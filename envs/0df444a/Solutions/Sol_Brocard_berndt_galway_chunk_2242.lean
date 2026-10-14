-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2242
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:06:06.630086+00:00
-- url     : https://prove2.me/submissions/d259428c-24b4-4772-9b6f-ac705f30eaab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 403057553 ≤ n < 403237410 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 403058803 1250 403057553 403057591
    0x705030f090f1f060302030619050f010e0402010819021b070b0301210606051c051c020705120c03010f061703040513090302010f0e061006020a2303070c06030c0e0603 73
    0x2800c42d000b5020311104085a441e51780d50109203003201c00d8070241ca03808190100e94068806510a055100c482c0c0618155075500d00120101125000341c0042e041040800c001400c4440d548400302040a500720119078031000310007a483c01d0758100086d031206000b03080c03000422405036403d981c1a1100c030860303200750075540c0440d10001041e0260882e002601e403403000555075542d4041d140d06a966244c0040308064070f00e0300340c0c01c01da0b58501c11404110000c107040b26a030390015002050303907001e40c0c806010000b104c5c1070701e103061074088850303500d5030030200c84690755409034002e08212842841102c01005072a08078544074041d50180f01d4010101240c04802c2413803641080d10003500030300000403904014a00392050b684008509202c42d0b100c0d106200031100ca40c1000b00c001d085900c060071220100341d440358184000042c1ca56041141c0c0192940061401d00840704100c0c0e0014202d08042e591fa00060081c18410394500041460000d4000035030801000b01c034841c440030a04a020254 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 403060053 1250 403058803 403058833
    0x105040e07030503030c1209210c0f0601081c2a0c0b18030f0d050d0917160b070e01050901120f091a0105060c0729030705030f090f 58
    0xa11540110140c4100d881c0007010a90901c0294003031540141d03140e58500031041038020000014041118551180200f000c104507104800d104a014030341804c0d980300c641e00741c034034a8112444040180c80c041c860002421100014103c1160413200c02102910205120240c810400c08441c0004400c8070800c403000142066031000c070403910a0202c9280c40340c03200e210000980050324884044041c091000520749010000c504402c84034000502c110041034500030301030300902c4106560139890b4a45030b81004801c1882d103c0d1820b5500a071600c40402030100c0400c01400c0f4020303202d452880c030124103200e200701024010528184c45840c035101c0c11800450b58110700c43c2c0c524002036074071401400c080505000348084203001c0c090b82144688969240c4c2c08013141a440b581c4920b07401c01c503003491003d0210b283c00c11102410203600740b00d5500141903c40350500c0380c6200521900208005000d0340000195000340030300142d0054558403c0d010315075801c0300e0501a80c40340e015078822080300c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 403061303 1250 403060053 403060061
    0x30c02030111190e040506060714030409020a02060f01061d0105070c05030105010b04030b09060f1b1e0304030305060d0302120903010f15150c0c09020304030509030d11070b070b010504 81
    0x648080d000040100102c0e03501103054001210107090315640400d4100d1507548100300c0965600210b40c01c1200b414000c000840501c02d00302c0c01001c05131803111144d8050401d06c01e1341e00506031a0400e42d0f98003003c010080d00c03088200e403419038900c43c080c0081015842000c0c02c0c4030744822000940900c1034500e0064403180c10080007228110058003001c102c540342801ba0300d0080c0000c00e8102e495030b055150008424400804648041d44040101321800d0070003225540c020820038251000b12000504046207841107803075100ba080c406405800c084030480c8000d40c8a070740281c2c0c0400076603c17804104103c50052010180c01a0301882c4118042c000010081a58540040c00001c2107440382c10400d055540d10780041800c110343d2802044004032144442c0100c2225240150403c599541c1c0c0729800c0c0142d00074116869804000101094040d00c03c60700046001001c4401d145064400200b0403601040c1d01d10a50051644c0010390600c40310590f40c45643c0900c3c3c40740310381c0c200350a00000b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 403062553 1250 403061303 403061327
    0x10021b0109030c062f0301080d05031003030c0f0f0c0906080619020903010b0a09390c03030207020616171c090c0b0304030302220612050415020c030403050c0603011203 74
    0x118110708002c1c00100c00311174007242549035a144c000d85a625101c501070406040700003500a0020410401242229005106051ba641402c01100055440c2000c4e03007a4440c8040044c0307009003158281d018000c04288030130494500c400300707120f21354442d00c140d0348030b90080d540d002043c20320f001c0703c041240e1590042c190221000e400011030900b80c10016102000c50b80c8030044c2e0b15511100e900d040d41100003c0300c10883c0d2030030700e0b001c5000480008084010305200341030803c0380d905246d80825109404440b101d580080490b6102d00c545440104003001e0040c1c02c1721171025000046420246100654811100041e42400c8207424411008090012490110750316040c210700403030340e160888007440c0610f00a940058450302001c48080c001c641c80803412000e5015900c0800240341d00045000211b011a180850aa1a03610b031000c08400e04043d0b00034104c0c0007040148500c030000000c2c0040302e00840c202e442c455040000e0084a100c01e001d008003950075510903a011030b008141c16055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 403063803 1250 403062553 403062581
    0x803060f06090a1721040905040501140c0c0d020105010b0714011b0c03110307020901180b0a060c06110415051809071706150a030b06040810021b0109030c06 69
    0x40c001003080003546000d09a00903510382281081d5210382034404201120020710003045a00e00100402041d401c0b031b00503441400c2d00141c0303c00001c2d0400800b9001a486030944c40040c4080e41810354180b600c0c0c0d04121072020b014803850142c80f4051b8414014036040350b4042d074115250001a072601d00d0030142e100040307142592640d40040d0034070301401d4400707140d06065442a000c440149001440e030504a00c00311413a40c02409240c025070f4481c2c048a045070341c0916080c1040441340c044102400040c0c58050b8840d0300c1c0305000801b5034000c00010b64540c40b4000800c0140343c0450205980c0c09280030314030154134001c03104030065004000800c180d0a0700da03804c01d80d030b1b005040040c801f51011541100000e039895204c0f294492070488040e0400304c112103403800e020103a8144c140d0350003a10303951020192651a4600e5030b40311a0116009490508266000c2040070780745040031398071a08100350000411481c150502c81c3c10b2150034002ca5040c0e5074003002001036105c80014103802c0c0c620002c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 403065053 1250 403063803 403063807
    0x3150b04050f060f071a090d020606121f020417070f0306020702030a140714040504030c02010f200106140d050705010305100e070906020d020a170309031309020403050c0406030803060f06 82
    0x3440d001c1d100040c20056100703140d031014030b806c0c072201194407440c0601018550b5004140710700c2c4440d0041030107984210241d41b25011039500b520018070342443d86560890754444800401c901000a0f00108107403095203100400b0f10350048210769851545100700c06000d56241e1b4180009031007034000746403c0c1e00081c121495500c1613140c060043c8065210755039603a201c2c21042001e02c900604500d1a0002107908014603d07254901421090041c0f03802810447c0d00c8604015a5005205040d0407114210700c0c0d809030079443ca58207000701241d009802c0e81c0d000d01072007042c59181454021508641c07002c00341032480d03d44001034018180162490007484440d02c4081241d502c0e8048481c030601c0700d0b586208540385041800790030f0449440c4014110b4001070100b2003c5180002018444141030203030507505e81e10381c41312074114000d8001403550440c410361700040100e4182c001e0300540b0b0140041c0c3e54104480030030801100c0440c4001450f8003010700000d50103180402d89210f5503500546018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 403066303 1250 403065053 403065067
    0x503031b0f03010b0712030501180c05040b0a0c0b101d0702071715071e05030604020d052e0f0618030b0a1413050601050d06090c06050301030303150b04050f06 70
    0x7180c1034100b600003005242000c1401814049055105c4000103000d0900f0401541801c2c02d07607841c5041401d490391025180c1c0c2d088140c07070344144100e600500c61109a203486034007880008082041075601622010018000b1a000010285040d03044410a60881c000e071212100d101c0069200100b019040d8041c200001504100410303001c0310b00c001d840098862140c0007240032040c908050610020026007000c00d2410300300505c00d10b004010a402e05030380b240d407103500140c003901c102c40c54061203609000c248421441c2c0450900501c50390000c07200c58011441c4101540040c0c2403246003480b1000100c00c0180e68014007a85040700902041d11035440d03281d03160700e4236454060b1030703041d8100e07554a00340414051490304140c10003604100d240484000f5181c040e6251418003400740704a120030091030800003541e01464000d9403084400045d60b0351a0400b5006400900c41680840e040c03030b925400301d030180b00d00c04054610401c0902e0819003480d09200070402e080000a4011104004c2c0d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 403067553 1250 403066303 403066327
    0x61d160818070308032508010302010f2a05070503061e071b020405070807180b070318031e06110705280507080a03030b030d050a0804060603060c0206040b07020a0503031b 75
    0x19441004854841c0e020b44030600700741c60709414011b0000040020060042c00146ea200c018030020001918004000000f503551461002905c04260310321034502c0782d0400200303c000304003481103e030300300e040e680c01d95035021a0a2007410140203c51080480b000007a4205020b088401c0031450b524001e0440d0701115030119080f01d9050b100380c0f01040041c020400010752106982510303402099811030030501c0c01d840c1c0c81132070081550040600242540c24032141d40c2d040700084c001c60f00f04030380e4140802505503100351090340c500c043d102c1c2070402146800740b005050403603216550000003850340000003036040704042c00d100d6041d5103c504418410010840070007415020b0081e01003d004c1c16030140c80d0190490b10282d130031b107001e03411040784c109a181c0c1000079904507071a54200080d0325519490040010f00c0e0981006101d249010f0520780354503400501d49204900c41c1c1c0c2c06030742c151948203082c1c0c1e90b0400008018155130081001401d81c0c0310341000b801600104040541c1001954000c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 403068803 1250 403067553 403067557
    0x1c0b011e0518010906061107030605090f120903070e04050c011112070606140301200306010309020a08010510080105150409020f040e030a140906040909050709061d160818070308 78
    0x410000030b21510062080c0352a034400c013402802903040c01e000000b6844c81301500c4811f03502c0007803c625a100000341244000780404900000e0700c100741c0c0c0c541d00c09080c809201c0c0d04180c010074000e00c00c41c0f0000c1000e125810704180510b4004000f0b01c401c01c04030004540307903146480460001d01688041e8501d007185180500040d5100e084042105810450310f40e0700d041c40d40a0171031081e03041084410035a510f011001c20714214100c4042d649545940059002d031201c07400003501b000400b0b0000400704010750205010b09042006160111355070202e00d42a17602c00e6540d0b00b0005541c072800c0d034503132901d94405103079644060071940f00420361f400000c0c100c420306d0581aa003034000064091110350b1100030b11842e07280d00e5200604040e42c05011540741c2c0140e0080e030a02c0e80c0c0d144004010300008008842c010202c60406002454071041010b00f000d158031810810010f42c13074041801500c900c43c0c407076500d18051b075a0000942d07400e10702409600744031440d994103008140c1c0220100d0380e00c0780 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 403070053 1250 403068803 403068829
    0x60e0115030f0908090d050705270714040603180c08011e0c1706240c0114060d030e061b24090601260307060b1c0b011e05 54
    0x8504100c03000099005070a50703201c0c002041c51545040ca40b0000594003009a510b455419107440a0981c0b051030304524201c460341007160700c500301103003403e9007003056200d00318110310241800303c1e15180d14505071101551403900c41388a00341444103002103440380d8000c40d114111204039614608048d00d620a482419401c1905244d444e00d10320500c0e1b48944040a9400303c0e407000402c41c9100d2401c008003800c50320300d042c000040810303000c1001542c0301e40780710ba89040043e60105141c240d10a400005600922404503075508187c0e040d9003000f00585114030550024005031003807105650200c0d1900c064051b100e0b80180c0a10a4800b0070380940c000d0212015040d0003401469100c6a90b11000c81c000000c070509540341d401048030114000c10322604555000a201d0002c12000603680e108918030b002d020041c1c440070401300b090040940100030121420344440c0b5038a1440b09035a06003031040500070b048031121070010040d02e0520310124043c803140402c032510054840b8006010b880c03e0340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 403071303 1250 403070053 403070069
    0x19120e01211d0f0d0c0b07030b01030f0f0506010801050d0b011701110301030b01050a14030a0209060a15051908070c11030109021c0c0602010606022508030304080304050d02010207170a0201060e01 86
    0x10580e46640b031040003221100f05132400c000000003600e03a42c0c030a08a000034034020400d61034650414287c0d01a4218058007084c00c1c500b07000700d0010b002a0320043c44100c2d41c56002482401c0001035074100000c1581c5101d40003041b61096078240080d101c1d1194dc00c1080e00b07c15980c9140001000c928000914080c521a0b03a03007150f50352500781000362944039038100441001094002c65a6a81c2c000307100d03041d01d80d06480369909907607030707500045400c400ca6200000e1044071510008a00b44e1010040c16020104243e144501d001c1000c112200182103900d64089024803100e100454020b04002000c50f000070008074009a031a408518210060021603400e88a01040d03d000c0200098071140600140c1c4001c1100c1490560003d50302c4a50030f0000400c0081c0c65051042e218034103614001415851003125660b003018500040d290740201c4040e0307401e01880240e4817010748180201e0702ca440d0000302100c040350f10808c3c0b0003a1540401102015503581305000215040d81001d0b00e4002d040c12 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 403072553 1250 403071303 403071313
    0x1b03030706092102100e0312040f020a08010203100303020105150f240412032c01110f011103042f0915040908130509100b03130519120e01211d 63
    0x801210700c2a40c546600101c00c2d47c109009036814200300700300c02d41d442500006032048140315400440c040091981041e080340d400001002592000c3d04010703000c483c40780e4020491039442c104e884d650860b000030055400200d06041140a02d42010080e148498400002504040034400550194040ea1041085070015a01030003815045422208810000b40e00a185a81b4580026822043d1054040d040c00340031880c548600c0010008402e0801c1c0305e0008112014503940e80e0000c541040b18207c07403101d81c410003140c284954641c800800407140c1800740030303200d14108009800720020000100c1a00b00030f41c1c10a40d036181d014600f80d2901443d01a552100c84042556048555800c0075001700c2224061102d41d8640d07001090486200e620340644948a0444440c00c1c05500e41c0c0140c041d100c1c3c0c100000120940070724071590503210309029010072404160680b8503030860442c4901040e00c4007c0c0e0900103004075a000c00c511b000100015102224075070265480d1a040800c504907440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 403073803 1250 403072553 403072573
    0x20406030516020615060c010b04090c140a1208070303140f0a150e0c0c210426060f09010b060c0f0c0a03050d050a0c231b03030706092102 61
    0x350190905030b500952014050901c3c0145003000b008005c0b03500340d03000b03036400507030544405420340c40211080001801031002206500748941801c6050181408030020b60380d000549242c03123140d40c1c040310804610410b800216484142c103581000b4400d400349a100c84400350300e00e005444e02440748200c0c290340402d50401d03070045012506070046c07080050a44502c00e00003060340ca80c001e0341c00010704820035a00c5642000d45400c101840b04060100e210b40942c002555043c40c010740103503800381000d0041c012078240c01c6030300c00742c8a5034104015086400440c02d55400100190ba22041b0340c0000324248001c28040b49895100d0340c4800f60744e40040d208000b03042801e1003100c1c1e0403101151b00c164103504684525883d000c610580c4024040c002516016080c003030108020343e1a0040d43e8000d1555244540e4040f5401c03110134407946000702c0003005901c01c038641401100b1a0050003d41c00c191180d40c500c0000c19040205462201c00c054407a607208000e56211013642800d80c0c0901403d0071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 403075053 1250 403073803 403073821
    0x914040b1f0801021e041202060c120309031c11090402210c070c050901060503191e0902030d170127050c19111216120e030c0d0c091e0204060305 64
    0x113104001140550406c01c010003004101404210b21250100c0d06180d44000710760502d460020021a4801741c81004810481c01e404040043d2241c08103801c14411710b14400d9030b460044520404660b00e052b002404241694200b0764080c00c0300300021519080e15102c015440321707208208480140e030388040003403d6001c01903000701140040130140c4000003154100343c8060710a0200030503104d602110004024100344190b00701780482c01d21281140421095407103c00054854064240e0083c8a00c07410781130100c0c800d804205810f1840e581c520142e03420070303444184000940909204500c90081d80b443d010140d44586c9018200250f45280e8030300064900400e11907031607003642d00780070f80c84040032060707000400d4901540300155240c1d5520b0b480c0c0081440300d058228809820b08a121100450300c541007649051070b0b5001b1400c60700e00c20030704410070610a40c8500028206100d52400300900d8009400c441d166012a0114424803500c0e102458100d8016030b0011000a80724014000d01a0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 403076303 1250 403075053 403075087
    0x161509080309030303070c02061213020901080c030a060b0307080712050f0307031704020a080f0a05060907120f020f0603040c030201080a140417040807080c03070914040b1f080102 79
    0x40d4030340103503007802c25940000c0d8507400024040000d112080701c3c010115070300c00d0304a811816080d0924481414902d241c116641e850800890080d207210300045484803000440315440f08006008240d59440350759208003030035100320019050f20800102180c2510288001401f420314200ca070f528891060a05a2034442413116508542e0420004100480d5000d034540c002d03040d0038040707480c080c0c9a45c404a069800a640084500d0003501aa041241c030049000c0c1a10341c083c80440d0303143d458401015807580400e10580207070100220100300021001d540031542a400180303901400d803654404a102a03101b00c1d0107c6108140c400c00303000b15030b0080c3d907040c0c208401d54800c00c004004854651600d00d805040a0645000030380d0160a995a45003120302074020391054507056513071286595501c80b4520301d01c0d403103800ba4010115143e00940300780300c001301c61b8100305903441c0ca568503825007800c40540145240d0751101800e6488100141c000801041d2420005030b48050a4180c10354803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 403077553 1250 403076303 403076309
    0x5271c09170102220803040e1009050c0c1006140126090709110a080a0209030a050f030a030501080307021012090c060804121403161e030509060c0c1e161509 69
    0x908020503062225172000001d81d0141c806401c0c41d034007191205050441c00444d241e0103030814070700b000b040060541030321001d0015845203000310350003000d404282e00c095420b42d001e1550305150312030300c03012175600c41c17070380344009682d0f0108509801c18001c0c1c1c0c0c0c0f80e5403002100c0c16829584038000400110703626124a128400100d0b19090800d207004800030101000988410307012900807941d050300d5078091080b032070703100d920000f100e8002503000009500c03a0448030740d260202e45080000150f803e008401c4402c801d038018020814000d03014419608044c1000508803e41ea584604100140202c40e130f502c09000c43d42ca80c03001c1807404d80340405011491441e48410071a002e540256440388250030340360841203000702201ca91003e0001224907900640004114000b016a5400c0700c0d9010382c801030084600b641602e280703075114007800c603a500c100c0490244c141c0c0044004810f516407681032500c100c1d440000d90b8244002d80002c003030007004036000f0041610302c4400001038660841c96000027 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 403078803 1250 403077553 403077607
    0x32301060f050111030d050a0b040b090105211504080712020102071a07050f0f13270b0d02130e0c010c08070b070504080706020105271c09170102 64
    0x144504004805035a60401e10445050003410300741a4100034090041e55261b0080b8a070030805c903d4580288005080c0c60201140180d16080c0700b00c94908008181c00c0c141c0b280030304000141906001e027021080078000c8500788900501d14446101222002000c0c022405001c04607243d11703050070000307180d400b0800000d055a1040040600240c580c0c08070340e248605400a101141c1d0754014251920302c528805c1189a0038001444105498040003402c0200c108100c2a403807651640550290700809142810368a5a807603141219111640c102d500d00b418041d0040101009540c081038100314010445460310352103050300048824100100031368a030007443e1064000c0380d103481d040034071711400c0e001034003030208000080d00040c00750044600401102d400c07a850160f9495001703008110540e040349900120181381c0d40103e510480340710301c0451102c0a000e20301d28110242a00882c40b80d02e5405001404078001280090042c1100b11031403241e0016941d034040c41c85070480c5c51104203098070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 403080053 1250 403078803 403078811
    0x30213022b0f0b090708090304050d05070e010501020d050f09010c0b090a0201020c01020c0a2108040608040b060405010b0a080604111b1204030519080705030a09140411090d0303020c07032301 84
    0xc0c540c2c4da800222500a8982d0800440c0d94840c80c2d4040d00314130441e000a07070000041c003410010040c0008004040b40d1030311001c401e499881d00012a10b401c4010740701da0001d10140300f01819003c07030034002c007103500c014100034001412958840d10509030480310761070b40ba044840b8100039560144a10b00c00c034003091001d843d040b582d910024209841501034203152070700c2c406622045141c0d1000b44140285c100d005940c0719a03886400824041c0c044508594011486001c14541e060071700440d416900090b1030141450120802140c038504000c10765940580c0301c0b000c46442c1d00c04000209590f81e0400c80740c41c40c6410019502d4549409840c40f4036004008201c20400301e040403131840254000c0018031030b40c803805030501002c1401080c201400a020010304989202c6d0015003103007c4550f0400080404034900c0c0400003122a4154191441c140400c4400070711f10707119803110f205d0f0b031080c107006040146401c0013518081c0c0039001141d098050f101e1a066000c2e5143c5208140d41a00707000788 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 403081303 1250 403080053 403080071
    0xf1b0809030a0e0d0507030f0309080a11090a090f05030c0705010c12111c0e010806060a0c060216080d061d040f03050a050d051014031204030213022b0f 67
    0xe5600d12610001000308031642000c01050390301d20300d02102081d006401c50703c0550322400d000324070114401080b800706c0d415050000381034401003010b403035164011441489040c0c0f60400e001c09210001d284120039039a13201c00900107400c200c00144943d025600454840000c8108185400a1904146d042c4102d0030a01c07000900b0900c3c2400c2221440c1c81c0c80c08a03d116080d003a4608868503580001c500624006c00e1078107a44480c003a480500240c0e500080c82d11490207102c0240310745800c0400244044102c01c01003200c9030020003d0707003501c0207000001141078440b4251600000b910350041da07240d00042001100644041100c00d5801c00b881d41c042c145071b0380d101c004000811005003444008180480d056020700290380d07954020940074040380ca4140100d50907001140240b01444031040d00d1603006003800207056140740500350030180740608540070002140d09225900d4080303a000c001d14031100c89800e00c02c0c140a00200d1044115400a212450a843c503000100d001185441c1001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 403082553 1250 403081303 403081321
    0x5191514040209030319080f10230111070902120a020c28060e01090327170f01060b0406110607090315060512030d1407050304021c02040f1b08 63
    0x40d00c4020011240180e4a21861011900314002d02403900640f0000284000e0029005a2014403804000c29103d40c541d580742c0054040541500441c1d503894240320040e030340c2a503445001600c0d003405040840e240900c0c0784084e840d001490300301d80c2c007003500407840e01e41107d182c2034960f0700000d400d40c0c2582000655000190385111034100c032082c0011651000917030311241502d507006183c00010a0100450f5003005038042d05100ca001c0300002c543c00518001603152100050202e42080062401d245c0b412068180d0024a001841621301402d038018001040c240319110040c480c688245803194501600070b40304e60f2203858001002c0d0481d804001840e81d20148402c29030340d000d2034804503050403420384c20040c80b02d500300503044400107402b0108181c00101501d207010402405004140c22400b0301d0244d02030a8440b80d0100e8018000f183c014a0402d284a1400508105131400d24001e41c0004050310408060303112101d9a84003100240141d55003c0032510400d41042c160a003004040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 403083803 1250 403082553 403082579
    0xb0117030915070f08031602010524030f01050a0b0108070f050a0503042307090c0c21050d0204090906060e13081308070e06040b0a0f06031e051915 65
    0x6502d120b01203042a000049090b00182d43c031664100c2c0107440da0070040d2800e454079900541c2e85040c045151409900d441e8414003480b441249400040c0c5c4407031041c5010800080e40b60200c0719890701418a00744403031202445800d125215115000c188202c04200240201d81c018100364208002402e6141038550000120f90080030701e890601d54035a95420f241110b1103014200e0b8078a03a0000e01000d00c90000059020f003500c41d078140030070042c00344000941e0646024a801080c10044250001d103141c03c55145883c800b100b402d08901d00003001001c41300703d80c841c1e0130003810250785900e08000e0010b1071207441d025207640c2003403407031508125040300a240ca02140089c18a031340011800c226984ea0341c0030500520390041110075880e19102c0545040700d044920714003903450820041401d152804601085818204001046506025049000d02084401d5440c82e1101c1c40c0d058400d98554441c440c8100303500650781150b00b0251003079000703450a000348007031281810007082c42150501c0352 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 403085053 1250 403083803 403083817
    0x100e060d05071a070f26070b0112110612190c05030a090309080d081b0901080a0f060f03030206091c050906090f0312190206040f02040903020a0203060a06030b011703 73
    0x400d045031010343c5000c1c5903107200b2000010403aa04102d82d40c41000410406031580c4140485100500d650094003202d082c011380d18003a103240c003800010004001605440c001e40f034051545101e07030344a148003107140c950140403030203124840041001a00c0107407030054449010003080601c40c0b00c5030084028524000604400d1a0b6a500c840d01d00c00c260041441c10004c140000070703a0490181040c2c0a0060081116084d00400e513803506000703082030fa501118150320050b1591003007512640000700041080210032064950f407140b010599404194283d002988030b94000d280520b0007850350390800a80f15442d01140c0c2190950b200d92503045000d90b8800d8130191000c0e500c48800702c001815a80c5103046407030b09409403526910700b52005000a003c91001c002c07180c0e0140100000485c3e03100412103015045c0c8178131202845c01450590800c07100c030342c041e1048512690307098001905094080d038a880314035036141c0003041001a01070391540101042c0340c001c1c8440c1030020109440e4846c01c070b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 403086303 1250 403085053 403085069
    0x506030d09030209330307050312070308070509130b041503030e221404170f07031d09190e0c0603070f090b03090106050112090c090e0a050105100e060d0507 69
    0xf0001d000701700c00f6000807070044c084108070310901c440206140480c08600881a01a0050510124060500041040821820036804c03450240d03951021280c142c009005801086020042c1c01d08170b41d21003a803507001406600001650700300000030482200c02000140d081c0041c0c0550030404603812403900c00c64403005941c002110641503140b50400c81303440150000184c0352009020082e522070000c1449a480b900204840c46113a1041c0706030f0b4000c4449451081c1420460322002910071746805240d0b650013200b44821451002c0000e11000085a10031908103040302c01c82041da105018074800384134030350b028040200051000c505ea03848001e004001b40911315151480551042c0035043c01040710b01030032622030408424842c06032415104240c0000d070750740d021740065181e5100c1d49509035071041c03003094000e250200407805032045141540300743c0508403190000c94020701465109034128005104514100040d2000ca00c80280072940207031072112010000900004041e0141d400320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 403087553 1250 403086303 403086319
    0x3020904021b011508030f03070e21010c08060a0503061302010e1009052704172710080f22020a06030e0106050f0d020904150509030d0506030d090302 66
    0x114011502030b2189078840c01c50b4103000c2208895240c0e06501c100080394020325401c01681e5610300702c6549001d080019201c2c20b1041021a480602034040c2d43c000304000b8010407078403d080d072580d1040d402c9a92101655035141d4121001c12984a00e00503802201125140d50071820240426030b180002000c90400b055000c150009580c02015040c007065802081c54070044600ba03001000d100702803058074011100c400c00a206841e04001a0083d100701403445007043d034850303c0300d01020001e044540701c4000200032030061100600c00058014000b5400e60744000e01100034011701e010701c44004810040c1040501510700011108990080042c144110380701021a800c581c900000660095002d01d84e6000002d01c0d5401d500200401d034107030f40003004155620020b1080506c40a2082540002c032130b036103200107103170a00c0c00070340183c044c05680e0218844000901c085820a513120b81a035030010418088941c03250080341c0e40f154095000d070070f0f1900c903d18003034980502e6010080c481c4d108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 403088803 1250 403087553 403087567
    0x50402071401060b0c0105060d0f032f0c120a020d02010c050f01020412030e0d081c0f02070609050706020c060d050a02070605040c060f0e10080c0c0a112e0302 70
    0x1c08414000070342800c0e0002c200c55961140480803690000d003105c90154280300c00035800c5d2400b8a68096002d4108140d02e8600c1c4035030303070207c85402d52018001660078225000d034a00c041d0709010304240e1080d19004005101860b410007864107070074240a61281c0c8040322490043e15000f41490100782d081c20200b01000b41c9141c203604009212566854540c4042030026448145000b4040218042e03216281c6059058041c40000006890060040c2d403042005510b00c0714254038404240110000004200e00302c040d094080c3d90299074281e03007142c0c8840880050040501222000301028001090b40c04038000c0426014001c294900c00b040b56242e000801d8486980c04031248258484c00412003071829280c50702d5a0002e13801000d001400e901082407200d80103100c811003d940040c14441c0104510104840014000703002d00f02c460700511015480e064100401505181b00b40342004107440c1407010f02c0507441001c21405200c00c980d510030040c1180340304204240c02d01c6413502681e1406 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 403090053 1250 403088803 403088813
    0x3170a0923010e0f012a0c0b0d1b0f0516080a1d01091404091a16030b060702011b0206160f05010c020a020109090c0c06020403050c0a170705040207 65
    0x10303840c1c0c0141119a14800000140e25a03515510384908090320303640c1c1d290ba0610140002c508042e80282e000c03410140c0040c0078000c41210100886140010000440c41e2030f41ea040c05441e0140e2042c4414080031481d40705264003030082c02d614020381c0e41c05841c498010100141040c030407105090a0000c0014003001028205460030703d599044214196607000c0720b400100301a0705594181c0194150100c0a042503100720344140484500a9043c880c2071781c49020000200000041200c04070403101c001c0442d1018010140d00c2a4003104240000520250014040da01007a40c0310b40302c5d2000704180d20051fa08482101c1600e115402c0716840344c0e01c2403000c989c00384265084a1014500c0c624101e0401070206100180144104d000703115482a80302c0c1aa170b5080041d0001380071a00d4117409016900f425030124110800c280303004984125242c98200880c0e0054005442581100c4200ca4485c18103158180090140c5200c0700103c8100f01c034200e4460155004084c03080f50002019400d00c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 403091303 1250 403090053 403090067
    0xd0609020309031306030209030307060e0a0b130b0604060b040905072c12030304020d080319020d0c17190c140d0b090708090d050a02030c0a06230103170a 68
    0x4108180110340c0ca0511440d0b0690381e800005448005560154010400520a00070f4504480010700114103004c01030742c0e01e8010702030301d4506240700d01c20f166800300410498121140a046030042c4081402c0c964103001080c0e9000a2403940107500303184040100000c090100c404444401c40c000445455641c400c40342c05400b003403070300000c80d00c02d100811000d03401240c820b10608221841c0400450304a021500c82c0400c40c0d01952050049050704080744201300199400102080740c11425a5443d00c100100e8100e0f1100402c902d82d42c007010700200d40c0100d40c601c085054211141c600c3d00d05400a10fa000c070381c408151102136203030401104214001c880071100d8050141c00c4e41c0c0c480081d100110020110130324254030940100d40802c004078061144580141c034120058844601c803941d058500b903004007144000c5101c10006100605014492403045c0c3d40309141c082407002c0341c210070110000c17001c4520740000b0280c00040000503450707038a1606100d14001b42948070701801c50191498 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 403092553 1250 403091303 403091309
    0x80601050c010c0503060a0816030f030909090f0204050c091509040b0603010e160504080307030c032d0906020c0a09090809030d021006060906050901181d2d0c0d06 72
    0x641c200f80310094159000f4000c2c0d031084400341c40d0a00e83c595591a956611810700c81074a002d2184110b060003c10310000d8480c03400707802400c240702202d070741f00000400c58000780c006590035203030030301c40c1011450180038040e0028181c07040750303042001c3c94001a900d020242e407040001701c0002104c00d85600c0d690080c2800d56030051140d6120741e51044a04810380007183e034607042d828855400811280600180e0301030b10302c030078003c500300390160f034096a0710b02020300705809100a9204d00850045104440c000060326880090442034640c000500082031541044080d50071180b6940c400b9144d031403c500454010040c04980704165041c400442d11407210b1140c0c06005800d0385c440e05680026000d0301d49040704a00304145551070310708442d07288040c01200d0004404001c00350042d8803031800710442040035079014420542d41ca20003c100e41042c900310b01003102c5503041010408181e05008481da61001c05801000141514a0a0040d008009040d40e4038081002460290580e0061003e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 403093803 1250 403092553 403092577
    0xc0b180f030d02030906060a0308041a040909060e0c2704060b09070206040b13030c060b030115081f1802060304110a17060603152805010914090109020d0308060105 72
    0x5030750300350b01c140c0d0041d600c101d410148910070000407860078244131103c00116508040c000741010b00380307807030007045003111040700c2c041803018000483e02e1003140c460811214885d400015008000b45a00c600f880b001805c00c603c10036020656003450b4002540c034183c004101600101c6d15916480d1010045c1620103241d604400346c2000c1250f043d400089440c0618052143c180c0d080d559104801000c0303061500040001c1c01c0e8504070704c0001e6907030300a1091614010004150944e03041703c031501000303290307000000a41c010701100c48680308a80c040b00c10301210080c280501041c0f403034061111030601703d0007400b640340000000c0900c10485400c4c5814100100800501952000000495a0f402c015405c142c000e46000c0b035080e1400040300700ea500200341d202c0c0b00a80c3c0c0c00c40b01c03c1c0394800c1115401b61507020144c10282c940200c0c42181e0180c96a08000107400a040d40c0510200b03c0007408164a6031400030050701607900c04408010156152411111b503a83d410012900c42c0140480040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 403095053 1250 403093803 403093807
    0xc01090b061905012c120706031a03120c0304030804080109030f03051501180306020f03090105070207080c090c0405060304030c2d0b070c0812070f0c0b180f03 70
    0x1082140c5011803a000d1181107500591080c14007242d03030002111449014003040e10401c1c1d0100b0343c0090705510003224801a481030b003059040b404030744020150404204a81c20451080c00016014410010346407076095403400c0e0702c0700000100360344800c0408101c03090800401c02c00c01e409030800454025507400030b409074440790303608030580c06080d502d401280030603103088a1001c0c652080c400c00384a0000c02440c15aa40c0007075005440e004542115091200c5181e08084007082103800100744401c0c2007440107940b442c0185c41d2508480c0c2c043e003100215000311804000085c80050f1000040f03900322041c050703d07280c01802c1700641c40b840e0b01c070a4200001004010600d5080048000301d980202c1c000b41e605480760403000c6031100007c00c041403e01c0c280c80018045a20240915404009820b10800440c0c154603001d045802c80501c0c1d40001040c44100039409038001034441041701141002d128a40c400e54804007822002400c101c030400c007250090010441c100655030020061030f007901c2d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 403096303 1250 403095053 403095071
    0x5040e0c0d030c03031121060a080102130f060206060307030303050c04121506060509130902040e070e16080f180c0402030702010207020a08030306150d020d0510080d030506011b0303020c01 83
    0x5400181000b6013580480c0c603291405840204103800c0320b02c0344861038034034100300c804032100c4566028007410440c2c102c0d60003140800c00c80401d00c003c0c411711030310220720307070409161030850002c4142642191085402480611860352400107204058940c5402c0c04103455441d07054071503003401103074800c0c916003111103004070a01c9910101850005207409082c001d4540b5500b096469201e10b280d600c1d0004080070003e0b41200160303124000c4544018000700706012000c2405142c2940da4100c40c10b0380b088a000d00030210020504405140c000d802c100e0380c10f00d003000070010b002e0f50042000e040c0386080c1034076034403a187c00e002c0262128001001151a0306040c08001d00070341040008900501e0b00120115040340b000080e240300d12001020810f290b6404201d462613034012042c135000a07502413054541041c054010303188143c004240c0307140320300d1030110554503107801000b991090618000c24071070b8590f84140440c299090300004565443e1003458110004d22841c03d480200c0e5282c511b540d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 403097553 1250 403096303 403096307
    0x405010912120c020f0309040c0201060515030115180303030b0619050c1204300606031511030609042a0b0405010905060406020604110604030605090f0f070f05040e0c0d03 75
    0x2980515800302c01080998034484059984200f03c18000ca2540d000b4841d50085207000e401500d518403d030310000c80c049580c2c002180d030032085003100c40341d01d50000c801448030308909020446068028074202c020a1000c2c1e5200c1000c1883d400041d04054440072141d80540b1624100d4450003010003070708007003484031600100250805040301c1c1c0300d070048121045280a00354241c800307640b5121f00c444548446403484811031490406112020b110f0541c814011504610400d40194040c1d607140000c4050070420f0000c50f04d0040030a02c90381414170902c0442c3c3c4030030302d40300d80c03150340800708205c05090800203410b14800c40124000c8441118030106480000d00c01500031944203894860b0b055072910104030740b90149014800059100d000050b0104460448003000300074050441c51606480c1e85070003003604c03002c0720324102943c0705012525810404201032082d18500c0005418218240160003040c00d0710791090501c81ca8550080e80c60140701844640d11001e8001d0480003104000d141c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 403098803 1250 403097553 403097567
    0x90e0406090b1f27020d0e1c0201050708091c1404030614100b0f071106041e0e0105010e01031508010513060c050405090c070302150703140612150405010912 69
    0x8680c031203070b041001440f0a09041d000c079403070303414260341030b84444d20342d03440002501300e2101040440d80f21081c07203c1c10b500603c280081a010039214100074081544040d0170741d03101502c0300c0100403103d8100442c1c51004503d03100721400a619124807018449003c56140f0f0705040b42195200000800004200701d640c09160784042049845141e951801544039400b81903225020b614070080050400403100a2300400307210f8850260880000c00030310114026030040d4200700120b000b00e02d5400c01040005d20408000c05aa0850250790760402c0c000034094004c0c03a800c3d0307042c1130301d54081c082c1054070100580c025180420080181e8a082c6003101c900c842010420b480e050729040c2c40d112160300c43c1e8222015942c01a00c6022075440711071900a9580c0401010380440c0244c541d910f01c0a001e0b601054004c64065a012881c180c0752260034a003a04040c044074420390625143e54042c000200303540095990480a004c8a030703890b0309203d0b000d000c00d282c004208000385900e03c900150400d00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 403100053 1250 403098803 403098841
    0xc0702100e300a0c03141603110102010e0723040905010e01020a260708061315050a050a030b04020108040203030c0102030705131d01030212010f050a090201081006090e0406090b 78
    0x80e8550a0702c00c858400c81d21110004006030800408800038804903040d4141c0c0701e001040001251010501e5203031010203480c454204440d642452a118410341d0390902411700c4d0b201500d800780110034a480003500e2051a01201848800100da81140255030356911864400740c010000340403906003060200d000750301401500b0301040e00310a81c1c084600500741c242010032190400a0a962500802a01c0201004100a0713020503c0d285213a5a060705000d04050100c10440c5248020b0a108c20003412300c000d03030000b038050340801c01c0410200b05421000340d041502170070305803059121400460709521031900004155130000050110f0b140e8410020180400c000c000e40003829240c3d02c1008004d082c6170400c8c0b600b249110300500c00b5181880d400d40040482d400006401c2c456646800150f0710100d4089100c19510f01948040d0750300141220b0b0307c030b040c43c032481441c3c50500d2006428244103000301c007100003020300010104121940140b14181d0003141c410b0244c9001e580501a1100442d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 403101303 1250 403100053 403100119
    0x200a05070303030c08090a150e0f0609070501050a0212030901060503031c0b100c060c03020d141b09091b1606021e0306060d3605070e0c0702100e 64
    0x15202078a44c0c1c3c801c0c0302c41070040911001400341c001503912a400c800340101a0602c2055450640c4034914404028080040f0500c002034400e81c42d20992072400e00c1201d0b8403131814400c04000c200c6500e036010a8100a030b001c000c0d4021380303949402440900401164104c99018800010072882d00503a42101c11001c1d08501d07410b0050300a9a014020811005c840e0f03038012954000030600029010780000e0100c01c240e14006041175948a58001907071032001041d11b0b0409490107202c2411914055a20000b08400d003031440c101c503e0010501c40c2030000c2080c420651480c1680410704184800c842c003081c1807001940070070a490a01d207009520108003a14480030400c8250080e19071442924890100100b8a0741041c15a02040c0040c01c2e481c00c8000f1511040c424000c090100a400c46001e481c07421181c0000201e2442c10302c3c41c1c0003c40d0008510030484808102c110541c81d4101c45415606035120703455048548015280c58120b056580e03805603084e540030170316080862241c5d0240c2c07505 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 403102553 1250 403101303 403101311
    0x150507021f1404020418060c09051c0302070b030903040317030117072319121208040f0201031a03060106120c0503010b0414010207150201090c05180403200a0507030303 74
    0x68002021a4429900c0400b402e00c090b000070b01600d00799001455040310751801c80a60031081d61184100e90640d442d01e03010400032503003070000741444000d440e070414076101c01c105401c202d924040d40d1009a40700300c1c1716120300000000d803000300074002d86d002541e1201844680e0881c000c044a0390307410074003c00041e0f4000750100d1030400400600c072000c84100b8031140d00003003202d01d9485d621484d0f0700300c4c59801007040390708800602e166034240001402c1d00c407080d00743d60007541740c03d0081008404240c4100301c56541400b010440c28510001e036035909080000300114158107070413807481460007045e45801184000148160403401d4450703400d10f241420802c203042c40c6400c0e10b6030b0100b8098045040303400c2c002804500418000102c0e1380c00140111690745644041e0608000040041400149d440f228030400300f1150009038000740c44212500c0300c1c101500d4001d01c0c0c003114018409000c00950760b0b4504a04401039442c1e02d058254101960410080e50616960b60003962204600203407070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 403103803 1250 403102553 403102603
    0x70c09050402010e060a1e0207180c030b18010e10050d0c060f03020a020a080c0106030b01090209030c0109080c01080402011103120103120903031b050309090109050a0f0b0a1215050702 81
    0x204074201c41004441d5150402041c803951681c01014541c031f50403c06500c035000e0b012600e03040580540952046282c00031800c01c1c03c3c40c500406964000903014003404580302420344003101c0f40e840c541511108448980c0035074131100b065542a40790341c4000d402082024896040c4108000c881c020303103449850302e20503562134840071402c92240e4004100140c00020400c80045c0c5120001c0440061840012444640725203801101c000280e0044020540c0080e121000382001d2100302c070458008d0074044000d40c60310b506e02c1d407a0001c0d0740c600340c10000c03890006421a030060010003030422041d02241e44a0100290411080c40b080c0000d56560a0310811103001d240f1a550070303419241d041e03840b0500a1440121134202e551158001ca81c0c6020030701820500c0d444101020b402403a50603004540f50a20198440442c0c1c1422a012182401c01c20b4221964543e4070310340046505170003d05000c1c83c81400e0240b04805040b1516403c681410103000c282a4001040c0c0710340d00b200c0c89070300c10f0700d40c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 403105053 1250 403103803 403103809
    0x20c0c0f01111b062803060501030b22141305010608122b0213182013080109050303060114030f0103080a032d150e13020105070c09050402010e 63
    0x2c41c10070804829032088114811a0364161198250f802004d8819820024142c00300b040c10803840651004560a400303140705141d91500030000205402e007030030040d04082d000403c1c500c1006466078401c2e803500009207001c1e00d03410ba0024011240d10202a0ba070b50410b06203040640c01c1e01142541c4940c04d11202080b0307040040f950564084001c00c00518084040c02c0d05204990440c034501c840e84c103070921461030303516140004d00302c02080d40d035142e45960420034260048540d20304a91700451400300428a80c013003a04080483c40e07180342c20962180303a01c401010641d2180e40117038103594241102202045800000745000d02000d898a07070b0046000600c041d10b17400308564210049200c8001040410100c00c003c0c07a501a1a18002c0780340d1485071103111030074404031090703c209809070743c940118032514401d042c65084a03122225500e031411099041011018100c0da2035044000c81c818110781c000c80c101c5000f0744d8425031391440940c1d1100042c008041c21101a4040359003200180150301e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 403106303 1250 403105053 403105067
    0x22111b01060e220b0c03250905060913020d09020319150c030b06070c0905070e01170604060509010801150b0a0206370204080c01050408030d1e020c0c0f01 68
    0x242c180c81282c9115916884400000c40c60921051180c403a1071100381d0219101140d0540b00320340c07842c05c132641c80c103040a00b0141503110041c3c3c0302110610540c116400c962100440003120f000322055601c0e4101c0381c0010701040702154414000a1002440c004041c0b0750343c100036080ca000f2000d40700141d044111021a00c1581c1d000204178002c52000e107021440241d205058003d880e10b000152641c100001c074019501c45942520441e02001080062030790038022141e0002c0c240c40c10100715003184001801c160128504031002a100000160381ca4030390350b0021004202c0281101c04070350351602032500905441800c0456179100147c00301d080f003080011589980890f40c000c15040d6074a1100c841811980842005041980c80e5a014241818020140078a1702240c006a4451408811600d00315511100c0d506014003480100708c9000044140c0e2809050380e80003090090f10064210003174003180340000d805e11710218610840110008400c0345548098030082d1100d01d000303005403006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 403107553 1250 403106303 403106309
    0x61525020f0306072309042a02010608070302010302030c09030106060f030b04050106120e0c090a02180f06070b07020109050d03020418140c09040207050102180307090e03030622111b0106 82
    0x3285d850010092072401c00001d140404100d540024241080c4c1d40000301503503182e42403c6c1c0c40684280e54840844120303450b071500c5c2d4689000030000c0307034a080b082d60b07200c81092001906040c0d021000a044030780c1901200c41e0640c0007802005441e0310380002900f1080c900b001d4000080c6001442d100c6410144207150594070345132104070303a40c01e1960b401d502401120b0348200305030180d060312000d80d0315100d4049005906182c0050303110700240c14420105000c0f0008680300d607285074403c10081d1542000c603050190004030400d1942c4e60340c86c081c1e004d040311880040140c40b80358080702d00c0c1c1341d0581c003420076203450150740c0d2807070000404a1420b44005000c000c03201c013013210103e03c241044030000d000c9a0405040540dd050403911903600b2600f021900c580fa20118118040a0b490180b010340090b00894a0422100c08000d4030241c1d00d0000900840c0207004000c1201c1c180d4a1032103103c0650f070701c0b1600500000d240100e00c0c0c01160001078150741014103407000c0c00c0c050b41060007907400b9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 403108803 1250 403107553 403107557
    0x30d151a0c0a11030a1502091005030610030203070c171b01020306100e010e0a14030613050709091707062a0e190509181b0306061525020f030607 64
    0x1801440341c4407039600100c18003d1030780c54841c01c00c1003000210444160210982c10840050316910800c00780f203400680343c880030781081000c1040003495079486039020792100407403500603166601c11600381c52000206d84007178105804210030218220b182c0e4000d20a01d84580c0781c185045102c0750100c0d00380d0000b030703170829488401010102013032407141080e0704421005142c8000d01e1002040450035010846d0080d40f8103200860500c4042e00b0b04100042d00030036000c0c940980380ba89138440d00d4403141140641c1c00d1850b1903000e210107001a0301d290744004400409600e80d41c0160f850984d0082564400b024801421400c00082d80c050500c3c504904013246d84800102d00620810000f105002011034440340002c40f4010441d40c1b00c41018920607000008034195040c2280401440e1034070604100c00f080b00d080d100010203880110303a043d000202a204c82003600708404082d0914040c8561000102c90040316107a000440c541182409a000795800c04103a010711060640700c150403944800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 403110053 1250 403108803 403108813
    0x1202030f1f06050d030f23070c0e0f01032f12030c0105010618031b120b0a060911250605090d180303050a0513030f0b0103030e0307050307050402070302030d151a0c 72
    0x35001d0b000d400e070b0210ba00304841401d48071840d501f55001d070541004900340c901003035140060015030000021540c10018a00c0d11004942c0b450b0b40f9a00d8001e19840e0b441588081001c202d0810402c0f1507540945000040c81c0c15444040c030b4084035075030b810000b85a0300b550700b40000010783c180590100f0099285200180c081c0c142903031100c410507101e115424112503800c0c04002081d4802116000803644910a01d202a00388484180140c82e01038000c024203034503042c282c0740f0366030f0f1090813514a0584045099990001805003140045007680c010b0049400e00c41001031000c07011915400510540c1c0b0341c2c0700312000606000c40103011901000340465410055800c5081c010000791070003000741d1604400860b20380e9a01a00d504060780221107030445000140101138010412444148091340141300c40342c40c0c00006a5186400c0c07060707d0042d5400108101414400e108441c021a00101b00784140e44a05600c085607207400e10a80030011852000f00a0000030030040302d081c4051403001304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 403111303 1250 403110053 403110077
    0x31504050d110c060301060201060314031317100603060605011403040b0a05040c120b1801090f030e040605061902010513030c0305030604022802160602071202030f1f06050d03 77
    0x195602e1125016000c943c4a1642d0180d821307034407400158003030440c40c0e002150355031562402107030031502c03002015684d070024007905101d251045640c0c0200ca0200c05000e203c201c90910a034180380c800100051514241500402448250313082507003110000e07a10310304050f00f004c01d150024007082e0b0307005103043c0340708000c07940f013a0709a0040780e0810302541c00c809580396200d00c82c0001e022400c3c422030b4801c1d058020402d450807454051441d0900f094024410102d59a607517500e40b0416000060902003404c1c1058081d445581c8140f01600d4094101940c6460340c5904404542207941030000560800e40068008030710700c04290006a0315480d4040703020802d6906a910b41c01c02010f1942050707080c0003000010140c0040e17092240ea21464010300b900354032900a0500084034076031040104840010403140342c2c00101002201d0410341d43d0600140a8070019007044100d0180c0d03000c600c103904c0d82e440c000c4814200700c800c006411504000c100e80c2e900c00d00500752604240039004ca00c22158074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 403112553 1250 403111303 403111307
    0x1506030b061927030c0b0403020d03121e090606090b090a0b0f0409060b0312131a040807030b0109180803010e0703090506070c0b0f101a0903060c09031504050d 70
    0xd038000d8800c2e030610701c5040b0a00704442c07200320b0701c04120307030001d0344008410414011005100009045203002c00c1d4980340c21a000301d042008041c2c0d0080400c46000e1030013031901840d50040094041f0b0444052024611042c05409045071240075140e00749042c2c00020b5006261081c4042c41c90050110101c554407410450010101440125004000080d20200030b68940c8100690a403007003600199140550083c1441c0204844d45100340c290104000108100d0044c02c010484600c2580c03c081582c04007211903840c041d41d40308849a01c104100030040014980c1c5150507207550200401803d004125040004003c012014000c3d003800c00c014080300301c0a003115a41710110f428041174030742d520340d160707440c1000482d008000075a100001c0c9040004000700c05070046120411034440381000c14102d5951202c6109045200c0c14807000d003010b01181030203680a0880040650f803040c586080b081c055507001c4071643d4030034026442440140d07003095136100d00441d0080014803220b5051441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 403113803 1250 403112553 403112587
    0x3020f0c011e03020702090406022703100b0102030d050106030506190509190b0d030e01030b010314060d02150c0307030905060a0818100905160f030b0c030a02090301020d1506030b06 80
    0xb010205502007203c1c0c409130700c45140d00e5000e20301c180c00040e644c200114021700c4080e180c60849074007000041e21114191780c00600002c212400f004006680c10740000142d05d0341c441c0c07001401001d03040c14000226180c055000c54880c450541702156245200310342e00c62605281d00803d03600c0540d00020079085540e20b5080c010000ba000800a00e2159070800105d800001c01d400300c00246168020b01c0955a141c002d46004c18802e003010701650300040f40c0349903000c400501c0340b805055241c0d075810940d600d66181042d61841e01300da45961311404580591070f6840b031802640442c85070701c40004c0505000040745c0070b0010541d2003026030380390f09405420b07074444912080740e035200c5c61010807400c0c4840c0c4100142180300c1c0e4010329564a0a800810300d0488a5000c503004447c545030810115000c684c3c400e40c4050203210841c1d59655080e00507009005003046550158030201e05080c21032806d1303120300015411119004d6440303a4803e4200d0545540300d80041d00a00c042c005070000615481c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 403115053 1250 403113803 403113857
    0x60609010305151506070f020a0f141201020f041401020c09011d0a020c01060b0301052b08070201090312020f0f01110414042714070605070b10030b010602070303020f0c01 75
    0x89546141a0380e80c0000e005ca41241209461840d40010040308510f000c0c0190390080124800d402241d92801581c03952a007040d00701ca42c000c840d0072141124101007941150000020300d96070540302c07900c500c2100c1d0411444500103025101c1c0c4610b4903803c1c135040658504070703070700381c071903501c8001140b0709000090742d024000316142d64080c841030701204800c0c00348001078035031085480e860398076103002c201c0003a84080016010000c010442d200150400035009841c80d04182e1050b907c0102c2d100403203100545030f201030201e054040f082220340ea030200340002c491000f00121285214450005802ca46610f80100030f1004100070403c203242c0c1c10350194038050002480028900c0d403002c05110150b02580c807110841c540c01c0071a400300201e800c40440c10420303650040c1b14a03820706a000c5c089205403200580118030f03100000d1014841c1c40503450181d5841001441103582d5040d020799035024074007044025010341480d41d00c0500f00040d81c0c0a480d82c050391010312201c40e611040c80850301c101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 403116303 1250 403115053 403115071
    0x150d020109170c0a050f01021c0c021f030c02010b031c03020418050711030c030912100c0f121517030f270f0901051302040801090804060206060901030515 68
    0x4001162000b05494014820441000d400314200c01000c000b4a00e4050300918031515600b54042880d980c0080d03076500c4400c10707031008200400c0c0804252200d17090b41500a52143d8060040e545500f580d49102c0c030569801d40b02842080b400407400d0b0b00780d5248500701354040d440b5020400c148820b01000001003210f034240185065100d1014200400d0340d040c101280759282d005104420340d2252484254040190245040100d2068403036280e00c41c4044152248143c4010001c0b5030000780101c04207086602420010415161400b80040401e403051030b010400108030860001d00300d014000e589100e202c0e0981d10107040440102904401d2445e01d03440d440144030f042c044000350b100500c1c50003403a08410314880402d01d099000003c1042e0800c0c014049050701c003289859400e032107070556108480001c01c404c04160310380001c1c0601c2d070000c040c640c280541107060000910003807017501c0150303082c0c820942d22407061001079070003807000504075802085404802d00c105000c6640000c0c1e50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 403117553 1250 403116303 403116317
    0x60402060a1205010e060307150206010e07110303070c150612020d08071b05040501090606021c02160905061009120816020d0303020a1205070f05250b01060e09150d0201 74
    0x1c982c00c40d00241c200a2140e81148140031451404000080081246030501042540d03001e50094030b507081807044600c06130048010511a60064584040403035486045039180e01c0c0c204802070440744201016070b0390503501007180315560994010b850075180300e0702011600c0461032b424001c071880d0810058411207018030541001132000c1031041400303415640b0b0500c1044c10181003101301c0e103060b40402d0306903280135000c11a543d0082580000c03608540d14150b400344014005030300b0807440b0001840d2070200000040781102040c0d0156004040603103c044903034820b44401e90f001c1c2403d014600c0314402c200c1b000e01c0040c032024000c0490450a8402400e021800e03070200e0316040d003c0310200c0210740c0106108044507400003032a00081c0c4030f84401c1c0618201a1400f07404401e41c607034440c0c2040000140c0d810000048106030190080b5600d040d04049240d0a009020346828001d000024154074501086c03441c0002919000303090442c0001100002201008401301c1c1c50b0304100d060142e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 403118803 1250 403117553 403117577
    0x20d0c03050604030f02010b2707170106050408163c09050a050f1506070816030203070b010824130f03020f010c02120a03050912040b070303110903060402060a 70
    0xd21489025a2103a121100e05d0072140303d010b400d440c20161041d0107000c1241650508031125200740c2d0450104141240483e280c1840071250b0050b06003006014001d4640002500c070b034407000400c112660300702540c080c0302601d410442385034a039101d900c4030400c40030607012140c44881416911034007205441c01c07005008403044041d4049030b503c0b020709031f50380301c0c208404036095001d0950320139421000c2c0e10291410408000c6c0072004414428004c54000c200c10040240d00d1044801c2960180c3c48030901c0f034a10f1800a50f0b07680682d8088400c0c0f05800c0001505201c001800341c1c1c401c604242c07030203c14050520840d5444401422002d0003080405e01c44045409210308400060003907002c0c10100c0d00a00031607094521180802d400c540c08582c482c000d0f101000240d03120f04000707180100c1c240d00c0f803044062138000e240514502c41040007400050408111005064180c400e44003881000b05803500c07a140360040c104007541580054000500602c2c02a0040045c070410f41402c400240c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 403120053 1250 403118803 403118813
    0x12011a06031f080a020108090c180601090503070f1511030f0a0309060c0c060b0105121303030608030a170a0e0d0e210102120f13330507110c01020a020d0c03 69
    0x25404103d150304810054030541d644482e80301e5000401000800344600e5000104083c000900c0035224544030441c08101c0680c41154136000504000303003100c500035290002880170110718891070b12000ca8242c81241c20500a281c9400510600b5001d141000e4844d080700030f2640c0080003182c20113a0318071070032000809600c00c200020040340c4c0d941ca01402035203002400c950700481c8041c1840b00a0000050403510041111b501c0705c1c94100083c1e42501c149030030343c0502000e03000100c07a0b000c04a5420341c1258050024226403400c05094006078942105883c11180045450142c6410a005481c103c1f4040d1911104400001c3c041c241403001c1d030a92254a003008180700d20a0765000611003a0145014100c2c40d041400585e00507068201000c270303580c6200c00002c00070074101c011003141c1801418581c5980094400150040200d80d00440a4004182c211400d0001c1824291902c01c036040c00203080705030b0075068004000041141d020420000174410049032400312013400440000c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 403121303 1250 403120053 403120111
    0xf0a1a07150e03070525030602090a0803030c070302061012120917010b090f0601090510020c033307050a05090a170c1e0a031104140f010512011a0603 66
    0x403200b90099901c6200910341241801e00801d402ea4810061001c104040c941c5141d80b01d00b2250300241c016030359044940408d0301c203489644210307501d0102108108581d0b070034000034019580701c0da00b602c5040d40c3e207045d5000840014022054150056480d040c00111903a104044603a80e43c1806241d0035610102c4440159020b4445002c42e515450341c05020304140000f00c0c0c204001c0b6074800c00904d0900002040d480042c41114450b0b001d02011190241c0203000304c8031881c0010741a01c1458804d00c800c1000405125480741480080c25404001e4403070884005010310903540d601d034600100440211416004000d1155000c401d0300e6001074007034003003000003107200000c43c043d000e10103500c010031a80740c01a6820802810030256668015a2283c040c402031300d90082e0050010a20200420014031030030502411144030407050100c0c00180c02c40b1141200c030209c44400014010340710707403400c2e112500d1803141c010701500224100c0d4501503000d580d10808144d1642d92031104119818600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 403122553 1250 403121303 403121321
    0x601080a0b15101101060603110f07020d0609030c12030509120901030b0303030406090506060109030f0b0a1410170a0206030f0c16060c02160b0a0806060c0d0302090f0a1a0715 77
    0x41444501c04c07851040c0300b03003e01001400743d03040400011007080c000010903c10b0018a8280c0c05002481c0030465131013110b52040d90346c2002041100c180b40d0303e4042d10000000500303440e4104134846000549100f03005161044220601a0850800c80e0150482c50f401c8460181c0c1031640702d0a101640d0344042010318480c41c05507101040c6044103051403410300d00302400f02070412200d02c00030304c003003186160a80517217644003084100554403243c20384001c000308012801c0f903448a80a102c1140a01b40090040d145010318407442d072103c10b510b240d910008408001e401c09818000500446807401805500200194403140342c2110400012454150f151040316055902c0603800c2c05d0315410810100b43c0302e01000c844003c103040c900000101c3c0a2000d140c020010110001a040d854500c192030f00b80000030112214015001c10141c040e4010842c4d0314000c5001c1c100041d11860404c80d481c0131a0740c0c0c10440c1c480c03c01030640924040d400901c054800c0b021000809131611818460712000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 403123803 1250 403122553 403122557
    0x12050c0f0a0b12042105030123100c02040e030a122f18090c030a0e160f060e06040b07120201021621020f060a24030606170601080a0b1510 61
    0x810b1a1602e005105141e0030034511110070300c2c031205d0300003050700102102c0c15a04460864a100d120324541800002d044030240340e0441a50303c0020110340d00100c030111003900c212030074000c50720602803190b980c4c041d5a202030000340581131700c2c0807024166070000466001c540c40c0306404520f0144014018000e03482c000d24140cc00003607200c82c5040c00414404a488100d80c03101d041d0403c0f01501d2190302000e820302041310741e00e030081d010351302c000c200c008052031000c1508207400703031f840c00d107600b284d14284600c1c40410b00c0351b048405240340900480b41502c00d0400d140d0b0409661b80c84174001c0c00c2c031200c0d0103001d5640c20400c06980715062510b0015651040e8040040e0680c5448002540d882c288683c509540c0902034000003070002182582d80165042000a0b0b4200c103a42031200040c0c402440e100000d21500000c814010b0a130800c03400eaa440713000442070000c1c2440030650701d44003440740603039039000383c9001070000c2c000e010010340004001d90b1021160366500009140d0083c070310a5240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 403125053 1250 403123803 403123837
    0x510022103010e0703050108030d0e01090f03120609060f03111804113f0304031b050a1509090f0f140105090a0c08010b0306010c05071e12050c0f0a0b 66
    0x82000e240c0e43d40d41c481e82900d0140019454081659681c3c00340643c0c1a80c095162640791b00340110035844094000c0d000038042c64806141c2c03c0c0940017070200c000d5006081d040410128103c00301380692800c0360183c1880001d06445d40d1140100e550b04034010b00d074040090720b00709000c90302d42e00a00340124014002d144548548008008203815258101c0349a98010300d8008499144000d410140300180c0c0380402d1052514404c0d98114030541c1c00042c980d00305c000c3c0e4001e0019a400c0c90b80c0946a09039407030701c00c454072000408000a0148403034070003d2240c01701401071b036559800c80000022a4103011034102070458500782580c40b0001c80c2e0402c00c07210300c010041e500d000400c06411030300c07805041102004890006040310b005024141c9810300c00000f10b500340c0d100e2035221120300e800405841320785454102d03117000030214060a09003030255140101c3c40c45982c00c140d0120f254403d0050075040a098140408401d4000c003640e80b242440c2c0b00080d1320400f04009120308403042d40080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 403126303 1250 403125053 403125059
    0x30212071209050a120f02040e03120f0c030402030d05090102010f0f05070807030227030c030703030c0b011508071d03030a02070603110301050918071a04060f1701051002210301 78
    0x10310460307090384124458404c1c81c40c2044401601d84181e99070700c1d001091454008104e002140103410400c1201355103210003e2845014001099480e02540040300046c1180e140e20000d60b00c00d00007034402075072680180444109235402003004044151040c000412843c0014050b00211882903026410700d544440c108142c0381d620020301a40841d15050850500c00000441801402c1d610340c4244518031f5000c43c0401a83d00b0086d12070307007403030060494407c0e645a00e030040c501810000304441440d04e04c00003003600b00703c50f1506c1002c180540e40d00c0180e071742c404c24101c1740a050000c40303400b85c01100d640d07036561341c0701030000302040301403078004001d036900d8503a004080310703011880d290b0340101c180018400c0d0355442941541254182401d00700e001c0c44e1411550501103950700c1204140f0f00483c0b038030600c000c000d021b0b01c1119103680f100c1c64001e0b030000c0c080d1550400000e0001c13402088500501413881c1100780b41e01e48080b644115240c03900082d8112080c46407a10008500d14000700c010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 403127553 1250 403126303 403126307
    0x114130303051b04140a03020618180402010e1e0d03110c040b1806120307061a011707230301090509010b1c0b1e0a09020109050103060305060609040302120712 70
    0x43e411541045080010000e28880700441d030003940541100207414007500360b0f0a41e0390324001e03000b642d001480660b484e030340c008a500b0010086558a80169148950200300480d8051414815901070f1605070000f42101c0c01c100b0710401940380041030301c0301c41140d00c40541f2003041c421a103911940762181c0c5110040003d920300040740c05140d1141e41041513030b0415491b510b500d05031801c01d0a4107540107480700c80008100000c500c3e0420124031000c41d04506024060300400b60b621807901000031030184030401154050804c1982d41c400c6ca4544011030240c0344621440e0b03c407465000c41c41c6d0000c1d406d01c10300c510b05034020f911840b80213442e182888481c80003031080395082401259a1060106850507402820184034130103010100700b0300000e4660203c0781442001d00300d00f01e0421189142c802588070007040d122034140d00080a2910104007540030b03228000640750014014030203a0355201c1005900300008000710118042c600010001c00c1c01030002d031035101c1c0306040d0940a29900000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 403128803 1250 403127553 403127561
    0x13090c090911041d13021302030717270c04021201050f06190509040f060e070e03010507020322090608030309060a15090e070e010b1314100f020114130303 68
    0x1882d0a04402040100007021114244601241c11140c20141565a2044c0c9003e0160712420282d0030040c501d0308034040d0302c000d50040d84a6030168885001d6012070b5100c054400700102c410345e00390468504100161030003003424451291400c011900c07554598804141603070040c080b41020710841400500ca0351030720b41044400b1200541c1e4160511703845d440854490440d9881c020b05001d0b000581408030f0b2141d420140311000359034400d000d03803942d4501c6001d021804403605000905810203a204504c0c060091901854440c3d0086003000d250b5800c59410040044241c0004140107600040c10511801203800521283e030246480c1c1c0b030114a5141884001040b00344542d1501c128a404201d00039241804c0e079890f01070000e58110042d090780d240280a81054103141c480800000d2802401802088000002148901c00d503580741e00d902c03803181030141c405a110420420804020f44201880054540144000304150300001c062051000c025510700107071b908034080483c141501070007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 403130053 1250 403128803 403128821
    0x905060901020c071512060f140a0f060509040207050a030320030405060705160501060e0108010c05090d0303051e16080105190302011202250201020c061201090213090c0909 76
    0x200a5280039601040251601000c3c09000507810240b40250750407032090140c116510401b0208110303154440c542006420580e102c0d128403003500c0d000042480c10f202081908441f2880c900311940b80c1054425601600f02010540c0c00503428860000407072000c105041826010340c400095424600351460301d01c2621234158403105004009000002d400010400e1b480845032500700e80314113061030903a07035070101420003400f25070070309002140b002c000007070f0f090403070f81880020087c0710000c810a41c0c0714080c2100c62640300844140c1c010200340039410066201420b01881c0000301c6000c4010f60150324280d80040700403c10386032200007190041d080350b0140c8030803a01c0c082c4088000714120203004040c00700030304201003004031104c042d4440d01a80c860352110070103000300d14010f850b81e5500c04030400701a4014810101c5c4c1c003499007088004c83c0c1003c103c80d0000c00309682021050380280d4404c90340412089120700001030b0080d00c80c1700f030b50102c1c801d5651f000c0f0b002e45403100180503034900c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 403131303 1250 403130053 403130071
    0x1090f2603090706120f020c0d02160806160c020a06090603060e060f01030905011d150a050606031503070b1c060602010c0c0f05070e09030a1e050403110301091401090506 75
    0x24030200e004000f030354030110340c4146085580c0e8110042e80d040640b1600b030844a1180c0041401c410161010a402118039907680c204c80d02030051429250348292144541469030304844081102d060b00c0c440c907070611040c02d0038a00500c3d40240e011400900f00d80c0c2c0000c002030303603002060041e01d03070500400004240086e040601070400c400010300c0c440c8aa420281459500c404510401101b03410140c12078040c015241d0181b024844800d88664009450b0b810962424001440c004111311030380d03026210162245095aa640c089000003492070000300741d05229200002559140100061504001c0c505c213104001c006c0708840410f80702207800103029a410810140c100c1070703000444061141d044032051807180c0d0329081040c1031580c644c00184054141004100d088030300000100b000c101e11790703a2044071810002c0c3c9011a04248010308001074020801000451460340c1c03013a01c1180300400001d40d4002c140d03282c10041d808850940c07280d94441c09030710f0500005101c01c039404a100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 403132553 1250 403131303 403131307
    0x30309060a080a060504150b1b0f0a0b06040203010f03081309050a060501020c090702060c160b0906070f030c0903030302210a0c12090c0e0403050d090302060a18020a0b03060301090f26 81
    0x41d152154662480d022300b848110380030582d00e42440d070b00e8000446140104040e03420210b140d01003240c03643c01c130394000d4410603e08801f295260030b00e84201c904860780c0d034a000d40746c1c900703558801002c4e0b800000410184005008046500503603442401d0040360700e101c000a02a00c0c02001a08042118a150b4803c20301003040060441d000b0a8140c0e004940d410581e40c0c4181d401083c3c2c030a0441c0020140180100000308914090f0004003030340102c000340c031481c01d03100000404071309644220690000003054040c0800000c0d0103500a010140c5030011144003003084801040e107000411118549400d455a50145603503402003401a16140385070000d10554110b03456185801006e8414134000c02c8805e00020b05041c8100180c580c1401d42d80e00521143c3e0707aa060096680105550007001d4929002c003507548252001c6141c41180c2d40602405201b0b890710748600e40a410003003030541c06548074110f0f84c000586903000281a41d1003a5000050201034105d2007200d103085a40004c40c0480c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 403133803 1250 403132553 403132571
    0x5061b150f0a0c0206150102031204150b120c0409020a03050a0c050112060b0403121b0308010f05120a0f05161e0f05010212030417040803030f060619030b030309060a080a060504 78
    0x4c08100306901c011040703040702e283c0007030100403403440c031441880301c1c80409040180810803c680254444401448900340301d6012030408001c440344015203820229449044000d0a50401c1d401840060380000c16100e2100d56a84400e404c001e54030b0012030744030721800740a00240da0085503410320038580107010081c0e24240a03d6034500c0c8a2030201800b94200c5441002049100e0b002454101039095000d900c001d1552402030030915081c059514016034461001c50903007081519540c0e50700041c5d00600841e0440d850b205401c15480009803070b280a0551040c0d080c544002c458401400f481c512100d20041e0316004244803802030b000714040740746902c010000c0e43c0e800034082a0140444400f80d960382c41e14079005002260b068108820342c18041000607441001001541c40398480500f40301060342c0300b100708402e0b81714104000e10f80075907041000440500c04e6105054078100981181c0c9020701c1800001c015800c0100c00c803000a00403000c004000095000307000041c201a1014001460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 403135053 1250 403133803 403133807
    0x21908060315060d0c0e010603060e0601171302030d0f0e0901030506010e071707120c0e2107031e0507060504081b061605030301140f0a05061b150f0a0c 67
    0x400341c039a044000c40a0205072a552500c0145402c0c40e4440c000d400d045c4d0b992080702ca10170009124000209160a40005001d50500311081c82761740d0503500c075100e01c55403018030107000d04050329010280103214003040047c1c8042002c808002c44940304c0d0f00345000080ca000b07140007803200a5a0044102c4401040000c900007841ca055480d0111144d050303540c0d5140c1180d01c20b450341006078910081e4801e101d0000e40205200e9941c2444807410300c00c2d41924801030b903003002403504581d005200a11000c005070640c800400800c1d011100751503140341d03252104c082103000705074a22044000c0320300841c00c100c0100540f4004241d941403203400d2a00d41030820303495600304542e002c491413003081c103001666501c40465260440503c03122144618604000d81e0382d8000740203006401350304070300303100c0385180c0301e01c2000d507060009010740885401c0c0400d1203e140c0118030344050b80e400010310040402c3d0180a016484442001800454509408045204880505103070406864100c9040f8016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 403136303 1250 403135053 403135063
    0x6070210030207080c0a0309060801150801060f0c05031b010c0207060f050a11061014010c0507050d02032103040309062105090f100e0609070e15060702130219080603 73
    0x14040e070800503140d203440d04183c5070394401d100c207100441c0600d1389200101a004024082510340517950111340e60303200d204200700c59000d411044081080003004000561107810014a0b0381310914100c4800682a0b48280c5190400340301c1c140c00312059495013a0f4850244100d0500d15030b1b0b880180001854803c018141508801c1600704000d000140c02e1003040c001d00840c1e080400c40300845100345006524035041d0481030141400160100e081c5203ca0343c843d01041c0c00f01d44d040400380429618000c2000f1003504c481400f2a0140225042841031020203030f00701007d6841c6441e4903680f8501442c0040c054240c076000042806203030a492442d00030035410252507500130450004494513101c20442c0340c14003040c640300c1b25200b031411118141c0016005070300280c403103008540540c0c85201c45a500e425543c081c0001007244880010140d500e101400404c801c00500300e1440d2064580228510107400c071015940b9680004140d1515041c4441d0500d401c0414076112000d0304100c00007945603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 403137553 1250 403136303 403136329
    0x81513112106061e040b04150908011b2303070203180105030f0f06120102030c0a090e07390b06131b0c0302030f04151b1208041410020301090b060702 66
    0x2002c4c442d01c80d19500800d003140c024205500c1043d84456441342c510300960074034401200050700f1054002120352050051000840c10840c001055440c030039412035592a860181c210b18400c461003880300c0e04840c0c0c004501444555010b59590b404454002c8001030201002c02d0401c24200100001c0c20b0314440d51581010501c901c034042e58803114006142d101260040b41c06035440002840310b50a80b2100030483c04410b5181c00e01e1640e613614050410a604560041c0400e000f070445030301c96896100001c0d45039031100188108203454407907026200d0082c000407030b5400c1c0f009050218514084461119500d03443d001031001e86130304a0301313540422000300f1440c24424581c48050805000f8403c0d210207000e40b1140e00e44131503803400483c0d400e03801c1d00100408070349922180c0703010f2904402c00001d8603811205204007048600c5e0102d4003050028030135503009402401c0090140c60520241004181c04e52000d0703225410003d401040310a840100c4c3d10950341002000010380b00d01c45c45407a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 403138803 1250 403137553 403137577
    0x40509090f0a020d050a1a0114091e07090b2b090201300e01020d050601022b0c0f030e031009050705060f0705031605011b08151311210606 61
    0x45075192411701d28025282200603d01040b0500c10002001c0c0c0141c007a0407100240003a940023803003407050100c03502058400600c01030242032012080f03001242c2c05a005039a524081010a07036172a0660041d0f00100803500a2090170203e900d00c2d07212000700b003c00089404010810740c41103030b0000c0e2024640080c0f240c0780e1030700d0382c05d9500700c00c984845d080036000301c80174140801c8a18280c864002d501031400a4403003450807010503c1c951000a6410107102240000450f138490040458550b4a0511481080003c4c1242c03074400120700004003601540b19803101c1104602d01d9041505040a03c80e00140003441e00c60120081400050500c0481e9000d0f5401544c4000c070010350704203881040406801840f000440c0501030450094001a80b405403008214025144150305203564030031141d0b400040a540200324205148004a1000329004109601d4090202c0300a4207441c400b40f40101c070841c0101300e0741124039071640401401191100140c11900d002000200c040c010b54181c644 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 403140053 1250 403138803 403138819
    0x60d02010c15060308091009060c24020c010c0e03160e0a02040512030304051002040e01060503070c120f080f090613080f0d09020f190510030f060b040509090f0a02 72
    0x7003806403660401d0401e42403000e052000607201d08284c0150b52205900da40907100f581d880e20001407140c0e5804050320490381d25004902c0240e1101d4810140d581101f034081c2ea001803204245205601c020b00d481c1002e0310001ca424030203c60087d000d22005d060b0140240c019500d903661400d5140a19400d880e004040d0320307051303201c040070f510007402a6005940c0000b55128807801040002000e50710952003042200c40030035140c010b00c0f00b83e01030392043c40d002c5130040c0014003010340070304042c5a04c244149802180880e00392607001d849580311061b0404980c46010700c42e29940d00103074290780011004401000d9007030524840c2c0d41d4080040c0125004102c2801d140d0400071018112001c401c0225011925a807a005210006003a9240100e201d00c00620059159090904020011092140b400d1110615260038084400d0400403203001309544c89216a82c41c500703a00c110b5000d0038402c60a40c1d211400c120070b214001402818036070740c0b68407400c0d808901100014081554a0303069540003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 403141303 1250 403140053 403140077
    0x17070e1e030c0607240204030b01091506031112011502010e0127050f030f030a06080c030d030506010309150903030b0303161101111c0e0409110f060f0d0e01060905060d0201 76
    0x34102e4505d80c0d852000582c010f00303c8501c480380c6078001c3c0c000d40f80503000c49071031039a84508501c1111001001c044070040c1060041080c240251b20079520440101e901901e04803030800104c1c0054001d030441200c4e40402d08410511540c24440e5018445241d402000142c40060900080000304c000141104240900d4401040700c1408102c0c1d110110030200c0c0e03104c00c0303480c06a0809410483d510103040c0c0c03070420009080540058440f03001680078001d00058a0302070012405403038000e007080d040c180c50384006000034040e1100313a4072002690100099040540c900241500c41c45020700e44203500c180448201071040c0c01c09104126030050803407425049000068880709410030180941d030044151900c05034010319807d040072480d036510071921100c07500070001100c011200291070350550781e02500d074504105000c08031410004010a0402c5503984c0c0f60150f90740862007a4030429210040f80d03107001401d00943d070141c84072a0003440036151040108924241c10a4084c2c10000500821 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 403142553 1250 403141303 403141313
    0x110916030c0e210102040816031109010b19050f0d020d06091b050313060606022d15060a03060504032105010e060d020a0512030a1805030d0f17070e1e030c0607 70
    0x1507004103c02c6013950304188280c07201c3d4823420400e110944a14000c4000a01c0c9031600c1c0b801241a0317070025401e1400c00e4500b0307075550f400301c042400180a1003401c00a0b005100c82c03480117000030144280c2c0140e40c0b0102d0700200c01c151001540400e54050905c249a43d900c8621a134a0002c0006450034603103994814800d40c01e200710f12038000d40160700e0460301103100c1c0c0e408242c10001100c8816604159418444040d91020727400102040507040b810b00d80b490304040402e815082100140700300303a030540760740f80ca40869070141c604034041180e4038210b0001942c5c011940010f0881c60104004561520441415084009101038468603c60301c0300411582d418000314003501015212400d04c00111f801d003035690f4042006400480d2024420800c0140708460000540780c0150141c1413030030302c000e0141c640c2c032840402c100c103010605021a82101e50400c40c14460551559041441c3e40c142c02070013402406c1d24007007200662005450b554649000514504210703080c0c8141da92004a0f041c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 403143803 1250 403142553 403142557
    0x12090f0d032a020f1002030a030c0203090310050919150209010507050106060801060e09060d030c050708011b030605010201020705060f060f15030f090601061b110916030c0e210102 79
    0x80c8980482414841984091500b2440318840f4420b5074400305952007442000ba0302c00510b0140c9005900810001709480c0c401d0300042900d6100b401107a003001460790010341030130300406481100941c3d80d01040302c100020050101c4040101044030415540ca454031040030542501610ae45600020100282e911036000c5130900764101000308101911124000c01003034007840b50200264810b40c2210003854050082c60140e0401012b5025490032a80c00342e031074012030781042c0e406e40650780c0c00140c0c5403000e0142d038101440d009400900740c5070f01d000180c12580c031900040e045a206100e001c0c00107900051603600601c11003180011943e94400080e08240100022500451800c0890107010801005103001d49608083c4c00456030b03a40b45555600c2c80d09101b03490001310b011118685609905040350003841c0100e0b0100d51100e11036012860b00d00c0706460180c0d0186039a480c107a20140d0501c81c201c03403a0050701d4410081c3c03041e003001664040c802c54141d180110540d2508129200c2541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 403145053 1250 403143803 403143827
    0x80106080c1c0e0a0203060c0f12040302030f0d0c200d0309080903030a030f0f0504020105030103110a090c05030406050a0b060d0b0406090606110601090209010c030324080d0212090f0d03 82
    0x82e081c48014010400c2507229100b052040340203120300d2022581d80b86c3e9000640e08074036615040142403580c004c09906140c075000d441541503000800000040700c01c0b100060a00c0d00800f2404510048224401424410001030110643d146000101019000802c8000b01d0800c949000b080300c002c20b05140e43c41f07101d2110050f030306110000700300c0000c0d03801d90001700502d141c014017084410704076440f04041d548100c1340280000c00420042c0000317507008210741d03107049002e8028a0b841d500c403001d417400c40350b003c10f01002085010042200700145401440d42c003083c950410f0020120741b4011804a001c0d102c80c4c000001e44500481c10180c440303030710080050134001d60500480da13032020058074900c03811903a19114040d80e0000300308514980200c40c0840c0741a5242010046591002c50080c0900010141001030040014075060940506071b4041c050190142040c07040303544000c1d1a00000a80c416240302081c01030310b81c95500c0301c4070500c5100044d502d448050700140350072100b5080602e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 403146303 1250 403145053 403145107
    0x5071b05040e0106060201180b0c0d0f0203010b030609060a14063006150901020712080d050703020c01140417070507090c0c1401140c09120a050c030d080106080c 71
    0x1024500e00c0b0030150030000c11135049030000c01087c0200c800c291454040f03050b020f490708140700b01160000c0d01900081001001c0850009011090912404184d07802a4000c103100e0b070012051012516115010030b400c028100c42541c0c618bc5030018422041c00c044094a12408012800b00301803615054641c003032646e000c010300700510070398a60300c520003801d07521140201068100500c18501e81070403940940d805800034112a40741840d90000b10781c11a9040301c0c031142c01e200b01c40040c00f59001d0180200d005031009a1103060700341615003120780902040c1048000c00c030074400401c60304070301c00c0012400000b840e80d54500070b00700b180c034000d07146d8412010246000c0050070501d5002085a81d42072242c00b03145201c91480300d00d9802d9a450014400355110404042148400d443d4000d001c0104090500a00ca1141d02c2065040c00c81c1030202340c40321b4100010a1310903140611665480010034141801e8035410f08000420040d401425100f03034181c0000c40501e8920040007018521800c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 403147553 1250 403146303 403146311
    0xc030b0306042607080d020a09150305150402041802090a0e040f06110a3204030b060f180f0a18050d033e070c08070303020c0f0105071b0504 62
    0x516050144035501002c019030383c40ea2403c03a40c2d082810a04076102d050f0003295603070400941109110003035000c440d001d01841a080c03800200b0246440356003072000059140047c96140020104030f40e80c2000070f100b441644104020f018400000c4144450390240c2400180c64004403c0460340b29441a0441950000180d04010801c444407540c181e681d4880e003402c1c040d84070307400f0b416083e0303004070b01503100450602030000c1e260b0101245282402c0102003a07042d44003104005610165004d82c0084d5581501d400800c401070400040007503400c842560820001c600c1100f014859810161402c0140c080401c04a418031002c0d13044101c0c40b42081009102e00400d43c0b0f4041e81d11002c0300180d0010a003411000d40400048400e0403440c441c0c0c02a050300b0f1131111103200a03442c114418084c003802c5080c0100000321700c2c440c03910300241c15510001c1040318198140a45003058030815035108054455100a069900400355000903501402d00740d808105e40c030400410341000c3d0042c607081460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 403148803 1250 403147553 403147561
    0x7180306050a0e0a050f0d030203040c050d0501060905011509240503090703290a0501180f0f0203091501230f040e2b02070305030a0503070207090e0c1e10030c030b0306 74
    0x10104030a204812880220347d0110715100b015016400300302e90291442103031007020052420040c901d2189144220300003d40c06482e41520421924281c0107426100203120380190f280e60842000c1c800790007032111040345104021106000321903028020403c002010011405a03102005100041d50f0f22100d0744e0404182000700340515840b0010100e11500007502140d911007651040d903050b04e00034005900701810241041024055010f80c0e0441c00b9604d0007504905607903840610b0084010b007010345168255400400c42c400d038107811000c12000310340c001420020017601d04100480090f5440345000c0d00c0100090010502e1544160f914010000c04200e483c8042c10407442143c01901c145c40c0301c00b10110100c0c1c0c2c4c0c400030300000f0101d60081000e0341d4480e00480c09940d001a0303520407515a107486070a400140c0e01d6031818021290700c4101c401d45d0500d020030459400350f1448185030a000c1c0000001081410690b13003d0040c555513140c0168100d20a4005400e03084002e070440f611400c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 403150053 1250 403148803 403148813
    0x5060109020304150b0d11031614012d031d03033102060906030a0b030307032d050a0c03021e0c041b08220c08060f07180306050a0e0a 59
    0x12080b141118164850044d03079104200c680305050040102030580a210700095440320b1491030051030441d8148036100f411b00754840c00b0454003002c1c2c508007400d610701d40040f10001d81820900321605005000a01c098402c5007002036004070b103040d040c9008680d06521072007402000745030300280c25650200008200b00b10010103104000d001c844500c3c0425a4040d5481904800e40088000d5021008002d0071840d0300c0c001c0c000d15049000008009681c68000e00001d02d503034080d2000303d0100e00c03005c00c1003d00024a94542200000400c244510f02ca60000001c2c1544503d82190b030500c9000350586060510800070b80355200c40d00c9641d10039404940500366502d1030401407051055003030140c8402501c0414041400c0c042068540d56416110041c140502e07030440c4403d4001518007454484c0810b80c82d4034880001e1030514003500c542d081c0684841c42c440c00c001c9c6201c040c0020480d030742c004c25901844090461303800040004040d15181d840d200900900c20303042c1d10340e10902091805001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 403151303 1250 403150053 403150057
    0x110f07120f02010302040b0f190806060d020306120307050a0311010b0109051002100501061d040c090b0d02090d0b01050906010e10030f091b05090a0b2b020406090b010f0503090d05090a030506010902 87
    0x408240c4844003403003443c00c27003240d4440084625517000035040c4220100303890540c0240da00b01030010b2041c040ea40c1944206d41c0b65421221082c3d4195106032400700525800920fa00010a222030080c0544440040040c20740c40d682d10842d809140d00442103010144288112110094070350818025035940e02d1000f0000117204904015101d030b664a944001d00c5c0600c99503528807115165480602d14004818020b6044054107038000d5400704491541c03940c0725840c0d85c440c0c500c00c070b80600d1a075041501380400f07108010300380b034140602480c0030881580c5044140c0c60003051480c02045c1000c264400001410f140400100407207414800350b02c180034040c40d404140c1348207a600c418650f8424a426069880140d94180c1015203000b00c4020504e000710808003490b00c0b072143c1d58000751070b640820111406035112490096807a0610400c544c0d000c0c170694080700480c50300364110300300380d8038207600d072144043c0c110300344100000c1500d0251283c2e20414007d50304402070340e01031341e03550059102039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 403152553 1250 403151303 403151317
    0x2111070902090a12150903030204143015040b0106080f04030c0f030527040f0908090d02030a170309120a080609061f110f07120f02010302040b0f 64
    0x1402002004a4400010700c203070350180d00300614112041d840c4c03408140400652102c16070310051041c0301d4003186403050149103001d030311995005946074075107484281c130020800a1144109544440300303280304280f1000c009000544004036020b0998400c01c50715001200039800080205401007100b8045035100d0503040720344a84032000310380d03210443c6030701440c0300b200e009010880388444100401c1d03800c0c40c4000310501c24207010f031410304090241c040305000080400303080c07450b002000d4241d003818000d0f400742109180043c4080b61650342c4036515401083c5c2607074012010311004005550f0b040050702c80141d00086188540d0440c1403110400d54801c89401c3c0d171510070041400c82c10a814011101c10361040e80e140141a01c1c1e00d402c118140c1070113402c0507130080304030050960040c15010b41813000b640320340303508240001a05520f801c0c030a0441000c8070303542002200300889664401c03500c00056109012503c840450320045c2c00900440d0414568001b001c05c40750a85502c0800070008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 403153803 1250 403152553 403152587
    0x606030f050703111e130b0a030b06041d090a02180106020106060207050a061b120207050f090c0a0f0c0c060e030c09070e0f0d1209050109081b0d21 65
    0x7195980740b5042d025a041603d2032455a103040003810a2034603001c1184103642030300d0051030f26080c11114620000c0c4125013280e24418000a0540303400d542610900d11920b00c190f862078105072501e650541c5070703405402e80c1c0c4499481d01d40054034442e018414440072036802008800078034511440700000307841c05d00482000d5841c0550109020f400015640d04583c00240440f89032420440708440e9500104120b124400508203500c0000e41d1520008001503281d600804209107808100803410320050f1400d4000ca00301c9090254020511003103400c010884d0418000402404c0b004a40c1c100c03800070007802150b00d00342e000c2002e40c1d02c4525050044011022210000d14010401c010bc92003580c0020109401c84115032841c140700a241c00b202400a00400c2d414602d6102c280400c7d100280c41030005a41a0b4240f0041d07812a088001803c9032400900480d025082504d10300b070281e140035442502c082100d0070801036880302c3c40c0d070401e483c8450010000b007070440140202e6684841524 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 403155053 1250 403153803 403153811
    0xd030204050a0801022505150405010222080304060807021915050123010e01050d0f020306040c021906021c14061011060606070221280327090606030f 66
    0x641d415050080d90081040000c2a80c50345c801c1b50040c104e00e43d0f0440c0704442c180241c2ca01c600700444203065051040b0b0042c0f002580c1d44400002c50600440d40f03410081144a207c2403d0042104c000242e40545044d42032810854070b48640a81c80c00010a41d100b200c00c0c5502e45140811940c0d040b5070b081680d01c07020900551741c0302c002c000007200d1143c0300c04403001d01e4034040081e40c1d8807030f00141d801c51030181020345c504400040750205584002520000d0150000309000e1581468401c0348036500d803620161460114002100e0042884140042c00007a0003040c4400260f40304000c480c4101d0790400f040080040026400e086800c00b102c120b44540e0310340c1c42c0304c40d2075405071114101c07061600c002f60110399158010442e082d004101c0598100c0303640c250101d9442411402080c0140c01c4000178094030005011031076085c84071681c1c4020240c080120000065005100608a6000c90020b403090b0550301d146000c2c07000055000403003490900c040058a41d4150340440381d0140058000c0c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 403156303 1250 403155053 403155059
    0x11a04050a03030f12110702130b030a210503040201021c0e040c0e180c2502030601030c0f06170708070e04051303030501050303030408070f05011b05030f160f0e0604080d030204050a 80
    0x17404590141101d103459031002c02c20000103140c402e0046034102285400003aa044812011914015070b202c0210380e55a011004114920310800360103080d640d8134a0b2003840c49c9801c1c0c0c0001d46981603000408140f020145407a0221030107461944800c0d003020b8010042070801000041807000000328507406181601401c2000700850072041d48110010b0001a180c40e100341100d0050080101c0c1c240800c4400c2c1c210703140160303010302c0340c940250700410780b038080305042071542031609901e9071019051080006030400750820001d80241d000009091100042e40d94000950750b05920840c1d4035801807400c402c00c66250310103805d001e40b06000f550300b04a281e88400a050b62031000342ea014044090034088140000c2030030b4001c0044a02c10703000030540007102010622000056910480842d45c08020003080080f41d844056104034510510010244240005080c00d1a0458200104100c204100300c0c0c40d200d440480d00200004000c50300c0070015044020000d400500550303120341c030026000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 403157553 1250 403156303 403156337
    0x3090b130804051c060204080a0c090c020c0f010c020301090507060e1c0b040c031e140109022101150e160c0309060302490e06011a04050a03030f 64
    0x50440c0c0d40094040e140c1420401080301c0c403c500003801200250002070080042c14074000b078401458030b00e000b010f018010703103010f4900310b5070f82d0010f1000a1812003000a100c0d03001601c441da076403064811440b1041c050340101c40c0c04103000c80c065055801c0800c1c2300200040041c44004403140c0342c1e1180c1385142c81404000c00c018910061342c084000d04104000032801401030701e5041f80c401e43c00824096500e9452801c0d804000f05031300054a10b4800304c4c1c0c1800b132608914135001400d840208081e20180c1d00048071102101a400850b403403242c00764205401c254020060245511007840c8a40e6a501c10004899401c4400440d08640b21003980240780c000c500c0c480095a16449550200b810100200c0007500410090711980c030440480c0022034440c600c806000c808202424070816514500c0081d01d00c01c030401489400c1d1034001c2286003107070b000c40c81074199410440c030110302001041900c07600340103075080244d1107861404000200f603041451181100c441351502d6170407001d51540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 403158803 1250 403157553 403157581
    0x2103030f1b1c0c020705030a050106030201090905060d030c021306090603141507050c01111c060b03070504030201050c0a0209070507050115120201030f0e0106060909051302030d050a020a0206030703090b 89
    0x242c588010244000d0001282d25a08040f03280c504510403242082d07920310010b031401c034803440e0a0700c542e55603503801d0082d960311028500c003400d1b02c0300301803103a8200b000100720124100400a01040350000b020700c1103541c3d901250b020f0300e0810b40c0911107281c84078440350080c82c85101c121042d8003900c541039001c441c0440d00d503000c0c1d242804079440c07da03500c0c2001d49440e403020410004039543c40402004880e034100150400c0c00d00500d81000320300645103d1030031981c041e040300c0340c3c1c1c2c6e40920420546c0c550202c00c507000c1e2642885c10307940358490448182d14014405000030f43c41040c5400f005411648031000c1d20303849014900901072410318815144503448240540030740c0889950811b0095402600301c003140d108410000204001808002c0782140d0381c5030030040c0040c01292003080385903014098a0b400241c02115542648400d0307000940c0c0c0e8402e10081d80c18040e0114920401c50300a2001c1e240c450340203807683d603992401c1076005008001600d400c69000c01c43c0341c08600f042c44107000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 403160053 1250 403158803 403158817
    0x409050112081e09060301170613200d0203100c140702011b032c040c05030c0901031503050601031b0819140705060c0c1f0804022103030f1b 62
    0x394041c50b2496103080c0445121a00c43e0707401c1e906a0410903440c0030744880004600a02e0110100c4030074205c2e48400c28106040502412035070161608600081012082079240803ca0040b5111580701c00c0c1c40030030520000144040d5150154042d503180070801c40d00000704500b81d6581d440c400003817140d85844c0b18081e420b13000c0c7c0052140950b40702034032050189413103240c0c003a06242c00f441d9a002c0c1d0065403602c083d022048450992001603c003800c00307015800030290b07141003a03411468490601d5816010380618a410141c0b11560b20007050045d580d0900a190072409940042d030716800c051590300001d60044051040740c0c40c0001d5640c03800314014034102044202b000d1004017a03118072280c0480004030340d14030700075400001919610540103120418000c03003d03000c171182c00420041c1d0481c0310790241107480201d12b170a034159036002102650040d4101c0b142054095401e903515100740001810002d0b62000009005d41c1481d010309561080f000440220f9450078049000c41300c50081c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 403161303 1250 403160053 403160063
    0x501061d1504090204090f050106030c231005130b09091303050306040c12140f070f0f11030708041706010b04180b2709070806220302070e0109020409050112 69
    0xe9848070302c0c40d10703400c003c1496000500c0407848042940395280184e10415084580e603541d201c00f0820000e03070900c020010117841902e81039035010094540009101c0b0307501944a500210320b194080303400348041d10251101d60710040b03826600c40b0154401c5521401d1307503520680e500c6000501428104400c0b240703c40c1d0569aa0781503413550410700016084401010060128001d0b0141585241e84918081411003c050f68030310708000b141704000410180549041000c0d01c0800304080c0d40100324100703440400c2c5806800d500103480c200d421401265030041001c3c0700060005802c005103030910001c00c4d40381040e10401c0c0d0740d031180c15050348aa4407074107020000c4041d80c6443d044580e444110b8025010340121909800e104061000c6d406201801c1100000d40b403d2003501a41013159a001c4d0001000500c0f06007480501400030303001070b50110140c1128504104105032007846440b00030501162107002c0c55866001542c065001401659103152401000103003100c03148d001d644415803c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 403162553 1250 403161303 403161331
    0xc09100302090a08100c12090b071809050703050910051506160c121a060102070b0c0c030703060c1b0b0a020a14070b070305060d0201021005061201090501061d 70
    0x5805401a4000c0841240c0c001100c5000241da02c40920014a02a100980004031003144141c0682a1868201c00d0740c1c0302440c0040850000b116500c01d55084071040c10003403808030b030100c44002e00440c540c110240e2141090240202c0a426400042c0a149401c00390f5404400d102500c4045400446a1800c5814111058010f0b4240480281071014040e5030340c034910003c0e030b20b60280350f440960052030300146410260052101412100c0b4002d441c1200703000c814140b100000796512194011030000c10740004503d0404c01007006400850b05d07029050300e440a0341e074108403009210150965010131030311403402440c1c20754050702c600040e82c0b000707100070162240242c103002500241400d10a2140c0400320008004412001d000b806224611441d000d2a01c841c0007400d0b00c0c0c4c0a01040d001d25190402440180e802180d07001c4030700c103e054002010356400000031404038001c90004401c3d4a084191800d00c44190400c0e8140c4400340d000000160350101d408141b80011201403100000b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 403163803 1250 403162553 403162579
    0xa030f05090609091302090c040e06040b0d0501050414010c020705060f0d0902030304030b090c0103050705270a060201021902061e090102070c1d01060203030c0702190b031e0c09 78
    0x14030054a03032400007501041c205129503001c6810329005560840780031200d4400801146802d120090340301c0700707807c4403074201071900f1000c95642c0c501520040c03040307840c1c03030055180d5280c0003550b1090f103030444001c4c8141d08050404074016603288041c0e01076542001301048109000082000071114041e0170940b421503400030300110b64010261440c01d09466420b0400540e070100b001e0405980580303440c0c821030401c5c0201380e00c1c08101c0c0c0c7e2810305150800b8100501141c0207000d44812101c1010810280a4000f40302c0e0f16052503000255400100c0000116810303078150b018103007003003901c401595440340740c840c140d0b540c1c84122100e80a01030740107024001400c2951041e500b00c9001400981465195501c074003105195800220032800641d01030030150361891407060040c00036002862031410007201e02403040c0305030080603010f01c0c0c5070240e9800c413180b4949414010140d050b0300c2c2d0b84908120102200703024641d02c20028200b411004615454030202c201d422804d0010004401848 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 403165053 1250 403163803 403163807
    0xf070f09051504080607020601090c1706040b03010f1a0a1e031401020904020412021014190903060504110315130321060801020310090902030d0e06071415090a030f 72
    0x1c41d41d0010b8604402e01000031420001c0140c0743c001c0c1d004d500074040940c188043e46c02210380e1100504200f00340d0014001c64401c50711b03031150b000031041d200814040e050304080b0340074002131004120b1580c5040700400c40c02e2255510f8007251041201d80d80d01840d513516010280d01408408503100e007600803800c10000d00c0f1000e0700d25240d0b200c18009810005510001400c982180d4842c004009101e190302c8114903040030706030b11000d42418002000c0c1c06961080783c0d640600410f072952000c881d110035031621301509003900115488801486589411320b0f201415186072103103140240305444510010303110110880b03100b901c22070f0010043c2003e0342c40c01c40310b404180000c0f192000c1c0212186c00504024040e05001e00050000907a49080401001c03030041891f50101075218580000c43c001a940421605141c40a900d01040660351000004015101e4440014001d2900a11010700346c5404030b008496002c10b15145000baa850107142ca4803250201c0000340001e00e02ca07408003200d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 403166303 1250 403165053 403165069
    0x17060f06010903061109041b02060403140705120403060b06160b06041103040507140a050a05090405010204210506010b0a020a0b1b070309050f15040b090121050f070f0905 75
    0x90310500d0450700650b50b9855601c129560000400c0d40132200090b02a01414180114490b4074240e1030060500000e665000791604c0010707000404115040d0071a0010516250940b00c0c00d82d00141034607502045c0c4c0d069002c41d9801440304464440c2400403034030175490410103540c048400d4050740040300d0f9003940c41d83c0c2d8507100105101d50050381d548244104400c188081c6100328850001000400e040105810046a400c10294850121018240500d03142d01f80101c0403070300c0c141d6091600da11646003250281c045c5800c240a03800c0c00d1884140d145102c1e00c402c0840c8c80c01a82030781d219036242c0042c1c481c14840c2110900c050380c0a031108000280d0021b43d0303e85d20028503003003401d405825803802c189517402030000350000f903400b0b0070512451920110842ca01d040498280045050329601040b940c0101e2003100d0302c5007008500030f03070b0a03406006000312500b40c00c4540e42510010b4200308005003002e580c01100e104440c00020040b5000d0f0100075204c045d0782c2c4514041c68504001c000f0f8075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 403167553 1250 403166303 403166311
    0x605090a05130605010626070509011409040e031804090309030b130b0a020a021b030a03110115060c120305010b030126070e070f020a0c05120f0f06070917060f 70
    0x7034100b448400010420500c1018060b14843d07907918030140b401c00f400414140d54140d41c20311140450240110550081f08403034020302c0a003005508203041c03890004003801810f00c3c4c107402c181481205004034402100429124450b80c00d01e8020910b0b642c1400101c4056950003000300c1d0840c2e200b44080341040060960025140c84a03e03a0810307150703502d07141002c0135107001303c00c07540100e242c0c11100d4062051405202e00008641903540c2820006a9600c800c51005007d1000b4445492210182900329480c400c590408408119aa513100100030000b0081c043e0340f0310199010400c9040e1103802018101e91942054030f0840c0d003002864440002d0021414104a807440c500c5404100300744482d000510300c2ca91044003610b403040001d000030811522410031504400d142c0d60015946100c1c0710150741c81550300102900b03540800714580110b5410302a142e126007540c0906400c00007a8080c440c020960350b940c10950740310720280a8000f03060020300c042d0001e00c001900710882c03424032a40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 403168803 1250 403167553 403167571
    0xf190e010e0106090e0c01030e1c090b070c0603050603031306110a140303010e45010912121104030f08040e0405060a15050306070809031c06180605090a05 68
    0x78800e585100c10b007100d96541c003448400f03458075244c41852800303001005840d4030a003000e00080046910f200c2d1107440044405001c21004041860b40c03078410070240c806030158901280d500e4926082c1420004850700c5070b5000203050070005180c90a02209440e11114800d002c00c1849040c203000795404402c100e9141c61912410700c448001c2840b0001000c07009100360080c595070350404c02d4441b800c00c0000d2800c83e60422404041480d013108003103036000c0c1e00d0440c01168280107c1441c0480b403030a4a155041d6a44c00c00fa01d81080c444803040d5916015a2a12401c168030901000c00713050340c8030740401c0c403a46e40040c8400c0001c90140031440803503500c1070103031502c0c0945454040140407401c1c0c509907080e50102c82044801c082621890011040c00245868114605070029a40300402002c4100304a008000b1404010040050382c0c034072000700b060300406080b84242d0100030030b454440c001c4c0750b2000800c034544510181c4202c1080e10009052280199144900100030385000fa001c101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 403170053 1250 403168803 403168811
    0x90705090301021308010b010203033306270102061003140a080c06040303150f26191104020c0d110703050d1d0901180902030a14150f190e01 62
    0x1645980030f00c014049048413180c5401c40303a003050361a5007160500030046055500400a02211103040b00000640081e12481800f20044202c000d01c2489005007600e60030040220b101014021003c10a84c0c5125042c03a0000000b01c14500490352110180c860011030181008140049140503840038500c040b0b0030215031045ca86aa83e03c85694000030600c0c0d125080070003803008065043c0507000080c07041e010442042401c0c136032101305014261182e004480d1801600c0034003001c2c065141c2841019520907030300f6400403c1103c00d0000b04102044074000380c900030f074404a16140c800c0d034182c10001d0380182030010320a5400c0d41c2c00d120703003040402c05100311900000028020001c643e825481a40d4480021903408110b03103165006107840b911422400340140403203c5040a120400544641e000c15100103600200f030500c0300c1c81c1e0024212622800040410440001e42c2c1c05140009840da00d01c1a5205952a0140c88003590070360b80c540c2407042c11558242960700106404001580005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 403171303 1250 403170053 403170067
    0x50c2d031908040602100908040b0d0920030f0604050a0b06150301060210060501050a0c02090703020f0c210711010c0303060b0a020a02030f07030803040f0618030c02130e0c090705 79
    0x41c1040ca81c112509580010300340549581802070740a00464000c0034899003140790740e55021070003140900710701000c01240002c2014950f42042c0c2d030041d0890002112040c0d502c1d4011101e04540d02110701078411401c072919401000101588603c2d04000a0010104240d841c01d8407800701424055100c8035503024804400751b120020750003000e01d078005292000d40186034900740c5400c1c0e0300c1141402014007856114030b400c07040c900341c482e504851400403a130701ea100c1038000340150520440c198401140b10ba640d400000340003c06000d0b600d00780c007460162101a10400d00c0740c0c50004014001d1840101820b502500c10b0a06003486800d0100305281c487d4440c00541c0c001c541d01c040181c2c400c48440083d030600b8070100e5100880d10303025180305410360703c500c4614400904002d024482c2d403403880f400d018440e031210304a00d0349604101d85000040c01d00a02240520906a2045407038a070a91414941403096403110f00c944005802c41000c1d41d002c11541e000014071602c140041000b0742 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 403172553 1250 403171303 403171333
    0x304020111060a0f0b01050c0a06050c040f0b0d2706020a0e100305040308010501020d14030a1116060e06070804110a2409150e0d0c12030804050c2d03 66
    0x101c1d03c110010700700007420681040b488000e5a801040c40b5041c07010800460301d0f03544010132464012030b0440e00104480c3c89804010360309108691105c4500342d5001c001007295114040100700401c2158000d200030102c01d0030010440c03003c559401c0b07241c40110703103140015540d43c000d010718110600f0410410307141d0101054064002da91420000f950380d1040104240d041044640903140030720043c1030410b0158006404d03018484401d800485000c4000b41c088040d54100c1803040310782c2e581054584900145031261222109001c80300300c2e0030701e110b8404030940018158400c0509a548041940b10b41c0c4480000e0000e9a000d5a001303103240030045290301ca010716003180050342203030000d640c070129503000b071007504a60040840c812901041240c940d500003802c01125004542d200da03889100d1034a800010704990040080000609900d402c7c950040301440c402c0d4044c0003600c03d01c0c000102001480041214418261502000003c2c0c0035240040e03c3d5400c0203020341203540391103200d00c82c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 403173803 1250 403172553 403172563
    0x111090321120f011502010c050306011103092e021203060d1a010b03011502070e041221060315050403080a0e0327011701031a070915030f0b06120c0304020111 70
    0x140000507900f0000400030a0f803401548140610703244020031005a07070810043c128031000e0308650410803d0442618291000c0c401c030361001000801c46c3c5605031440e004c0500c040d65060140d60710910901c10b4a00e079078004640172103401440c2c6402c620355581c1000700004010300d040180e58101c2c11591481d000c103141e46125002c0d000c0c40d0a0151690b140860400b0440320071410002190030402c07040000d00d4a200505800c0755220308945401c0a009400b203801801c10b6080c40081c280d4000b00da45081090740c806812f0344d01030b1464071600c1c0000240d40c2e094400545008000070f1030b00e80010b00c1c2c50021381c00468118800c105403403811002c0701c03108800701074a080803c40f070300c01e4010205140da0440e40901c8814800712400620750314680fa540c004e86010005641000d10920010740c0592148100034040e16404213105022461560000c00910201500241161419a050029180400c262100d00c40040942c21580e980e100302c1c00d044d504041d104a06200702c0ea4582c050701c1200f401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 403175053 1250 403173803 403173811
    0x60801120302030409020f1b070509130209011415031501080a0606020d03110c07060302131703030703180b07050c15090d0309060207020a0b03160c111e060a0c05011109032112 77
    0x40202801c9d130404c0300308810400c02402011045550f00749060050f01c8450b6002d0442e600040003c0c044c5090742b001c218035000c2c0f078a0024641c0e00c00420055801c8030b03260402074080003a03031003c415a03146c1046104845041c000e0001580c84884158a468030907040014041c2f04081307501c1c1001c10050074a880c002113a040400800e0300400c4000c41a0050740401f001070444140c00507840d03102c00c40361a21f910000d400354040540b01c23504000c064007080c00c070070000b03a404494134900b864040c0005180f60000080351246001e40844d81e00c00c107100b13000c05400350103003101810700740b8031050701030b4014030402c0c10449105400340301c0140941c0d51545004c0090242c0400c1030f42e24502041d012001319a070001c00b60601c580c2c5249030003c0380c8075003c10060820309590083c407010420075038502004107010b60b40d80c01440040c4d003500c0d2650040031055030070f200318020f0103d5031111122190314040e030f4020b142c2507070020218818440c43c80159030000d1000504091810640c803801003080c144c119 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 403176303 1250 403175053 403175107
    0x1903120e03030f1c0b10050a090f14041a010e211005011a030118020705010f061806080c030d031d0712020f0405103c060801120302030409020f 63
    0x219001220451100304c0d916080b81e02c07030080107803140c2000014400301e13603500309200f0440b000c2216282a070246035503d020304044000c03088165500c8202e20303481e86c070801405001d80d0400006901d254035581019400741710584609001901480512240d00111a113448002c001c200f400801c1201c140944100c00340c10641c0070440c0d41c10240341d600380200100c128481c10004000402c204003074021a81d0001b10303040405650348209041250140210114000c8214a0400006112000006111618416001c007440341c0d45c2e94940d03c503110031000782c1e40c03034240d04010051080c0798466440480308000c0001c0f043c1603503001104c5c13503103030900940001484041e00c240c54403c2d4500340c60311b0f0300d50440c1250b06100f94603114002400d842e0542c860072018844203090382088141807a0325030000c50344184089200250825900c081c040d0510492000ca20b41100100752180d012400a2950360160015072405151081441c001d510044002050480a00103102c2019180190000ac0042c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 403177553 1250 403176303 403176307
    0x260c010504050609070810050601170702010c120b01080a0207050708120901120506030a030c021201090c15090321030603081903050f010f0302010c05010609050408181903120e03030f 80
    0x3502e4800c1c42d09034080c2c8098100e03402610100800e80c40042d000358561440c240101c0c241d00d8140042e07420300440c4100c19403a000200421000a0b415170004880105903600c110104003a030308224110b602e1000c07902d001803100c100266650010307130001c28084c6c0c85001100e98044e80d400069044c1460442c4c1c04265070000603c4807119a0700804601100c1300c2c0307503410455070400e540020380d00c1c01c010300010188429145028107643d21000d06c85c0007089504020711410350380c0c0c580500c3c8181c1c2400340e0881e25103081d4800516500c200100c9050301d61208208090749441c80440a91340204c0a00c00205034588402000265120000c0c1c1110784041c41c0030514040d00e004d0142c1921030040640e1503010300c0b6030041000919600742c0c2001c882c1c080c205440c1440040c14002d024000c1500715900050030003003403000301700802d00103102c00032104500800441c000303000c026810a140107010b02076049d010003030010a05591980304410601d0400085109240f404203046400c9801005091100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 403178803 1250 403177553 403177561
    0xa2f0702030a030504140a0f0e0717010b0417060f040201081009020f0909070c03120e0709180b07020a0b060603090f0d02160f1503181a0106031d0703260c0105 70
    0x1801c06000c03400386c0c2101c204042c141402c0015202c12120b1003448108500e04020a01e5503016401180c0c80c03600d0600308031825a1182010101d662292150f8518040100002c66002800ac58024024080b22507451b419031101c1e001100c3e0488044c1c01080e402083d4a000035481080748010101d501d0310b0020542c84100385c0081040c1c20320010300407414404511115030000754400325030404c00860040003d0302d42c041c00f826525000d019003000d4611451301c02caa00549400c2914405c00c1841018000f800d503403490001c9072505a54840240600c1c856004500d5030b01e80704000e0350703000c1614812104910f554000703061926020414020250b0007100001c2c00141c601c0700290094000c00e401110b500340b4200306450040e5940e000042010380d10302454000b007440d409990491074001d03000c41402c40040c60035000b10b4000f0b1290002084c0343c04070110301044c085000c05d089040300740180400b00c1c41c54444409013035803010580f1003414100040c3c00d01449040180420300803080001070b05180c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 403180053 1250 403178803 403178819
    0x210f0f0506040525030608060c090a06090602060a0c140d0b09060f0f040513020307030803240d02010c06020405060c1c080f1b0904050103050d080a2f0702030a030504 73
    0x5400790801d070055007060108400d495002120b000c402203a550a00101c0010703c0e0300b10b0040045400040503809124184504c440400c00600006e00c02212551030f43c682d5010250340d8400b5910840000d41c00940010b09440180d42c01aa17543d0b0031420701c0301720520301c4000c4104a0f80203a014031030303041d6a0000b62010313040095441d90b12810950314115030701890000134890205940f0100d10650b2581c00040c203983c00d1441004100c0d9003c0c0444640c5a01c2e45440549508202d0724400c0d202c10302c0c1524031107085547c81c03000c040540644860109685038004480e65020340c0002d89895408001c0001c8986401d0010003203c1c451502400c403460900742a96155800e02c1140c104010070303201403016200d6a02003094000c644044107218030884040c4001c6203000f081801940549024000401d00002240010b03050503645e48403100b65840c01e0780324089410303075044035507103107910013149181e5080040c080d0004003010010754100045940003a160841596045001a07030102e001c0000781c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 403181303 1250 403180053 403180061
    0x30c010c03051b1605150a1a010804061d030a0f1805011e0c050102071a060904230708011503020a120b13020607060c0206091603080406210f0f 63
    0x41080ca018495420154045003000ba81c898580f075084030b00080c5000f4240c00d070700002450550200c281d480d21500806d400254201c03c0312654001400e000c04e0f0b1100c04503c407400048144140c5030907005446036250f001c02400c00c02c141402d040a041c007601c003c160100090700e805002d6503100d401551407000010840403001c0841a18015030600601c2640c1e002400001c250b000c4c5030803070002c1ca508a408850030b6160303010151841d4400a0b60070140000c032200410b44000c3d249031410396884a20a00c40d100070100d502070502910050b500311803000144460f400c0440d403501b00c964690700c4100b072900b121085c41059090a604140401c04c40c288194282d0040c50080300c40642c5140684540707001c0c0600a081d03048200c43e0030101011950340106039a80395030030030b400b000000c0a020010396a44415503103628944940c5c0d022072f84210744400c444055036405004c00341018a4204192007001c4089070700d000160150b1000c01c4c00360701d28411031000c848aa00302080321100c1d207080000711 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 403182553 1250 403181303 403181321
    0xa0b120d03060b040f0b09060415030504021f080a020a0921030f02070609031b03060f0b120309061b031204030e0f0a0503030a120204090906060911030402030a0f0c03080309030c01 79
    0x40c0c01e043c003017002001c01c000e5805044812107045030f50341d4540003002486610072a04006142d82032011400c40d119403607408688502e01c00d80381c0da03802444801d032080c60043c2c0e04a801e0002800c0000184c0c6c41c8a00c0c0c1c0241160303045c241841c0c8512612400c140e511011070000d500d84410449056a05140d4044040914a0020f0014188440c1410002451110a40005811141440350100b403d0205800d540004c0d03400880800500082c00d480f000a041e80440341445644c08600030907500030040100d03540c940d0014252854207a004484014600003816002d0440c0400d100490303907041a061031a00c01d920a03901d071000140c40d002000f182841c01c00c042070041d21140c01c01e1009480000032180801b42900300410b0340044030500070040e20640d001079044034240a5039000f00201c17074001d0f905031846520103000c036504142588800d40002c4501941c103500c544032050114208018611945014016804909499458001c0c1030b520941d044211644001295040c6d00002c1c49032008c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 403183803 1250 403182553 403182569
    0x1701060e0f040f11060309030a081b481c1d04060519051309020a120602070b07110c0a03081902031306080403081e010e0a0b120d0306 59
    0xc500701280407a8168900038002000e203400c01c080d140500200400301d58000c1001040c056483c07a10504440d220303000440101e0100d030b4550042840c00440c210014199016403040909001035003804490b034147c801a404d0744010a228000c1c420402128030900720188101000c45d01c1420400080c58158406010041203100c10340c404041c1e81c1c032505c0c2e06059041400800c800703001e1171001400819060340f00d180d002a00d0b0010341e004254800c000b00490f042100c0322840d4032001144982070303400d6100000d5101c51100e106015005003190070500701c0b401040010b06084041d81d1b0340880d40b105440c10000304410101401900004000d109812001a506058018655500c90f0f48a02454241025411402d024024098404c0081d200404070310492180c416650341c2c800b0b0010302d0309403410307000607031a00c000509090b180164003041d24006110381c20142c0c42d111620000f41e101828107002103407506502035165031080c0d840c220200104010707145000c1c1c170705400b40c116007040d403061760 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 403185053 1250 403183803 403183829
    0xa0e040c08101205030904090302011d070906121e0507181b020c0a03171317190302030a030518030c06060102010f0b0f060c150109020a1d061e040f170106 68
    0xb0021304040280c03000c2400a59020410207c03d16099000d0081c4204607401c0b0864100303040c0d81d1010004d0300710212020864200701c029220760003550b50b03403000c3c03002500142c140c88040101142611441c20354501650a4070340040d10341b011106059011480340c806035880384010f04410303000740100d003200b100d40d00041840d595510b000c100480c02c1448081d200340002c05803041c10b0485141100e09900e10080d6140c5010344500000b0b05513001c00c00c0f00340d41445090030000138000c8000200042c9500764004600303100402c1c2085020340001402d00000d0280c00c002665166410800380c0500074803840600304c84d240100009086428030080e981b000750904556411548500d040407403a04001c1d5840c56840d116502d20f94504280d540c20300603034000b51000010284c840340e015003d9001c05503a2064040e101c40780d101e1820030303822026030740000c04004d143c03903848103414440609908181020b00386640c3d40014000071480743c2c0f200002da446240c80600d007620a21407403003d0506402022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 403186303 1250 403185053 403185089
    0x27010618062c0402160614060907140c07030204090308060f1e0105180a0608090c0301050114090405100c170c0a050306090a0e0703240506090a020a0e040c0810 70
    0x403070030400c20032103100e11020480c400903079070322079404542003008104010305170010103141a80c01045000b549024620070400131800d0307803414503141c6004640310307139a40740303414044103900c403441d80821408082071003420000001a01c0e01d01a00e00709900079201c0c030a9a19202e070070301407492121050280300d8001c4114801040c0c181c818240700341142880d0150b29a048031105c4444404510121035003c403107642c000850304c1d4001a1a0710580c1a1030503114200d07032242c181426240c0c20b0003011002680280740f0a402d0030200382e650f900c0b81c021401c6400c41320544200c0d008892348000310f04001a150441c61580d142c0082681d90402c0f0240809450404a4640240b090002900f0781384181020070104004103001d4010f116070f041240d0990301d55a82d03030320f09007900c1c11030640182001004e4508005270744502d441b5492107035002400e8400903644914151b0025840f15058005028400f010560141c03910302c00c0401c15483d54865000b20304080c099440d4070141366100e000c4940380341c4480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 403187553 1250 403186303 403186337
    0x160e19060f0603020d020d110a02150c030105010c110907050a090b090a0504020306150319051e180321010f0b13031b0509040605040312090507052701061806 69
    0x803800b1a00c00d882c0050311043e00d40c030a42c01034820540040d19040c2000d400700c1c000501c0b04010b00140d507650302254141e00c0d80050422030b0b50710403981440f00c040180010012035001d010040d101921840b0724864110b1a01c0006200200a5401c0c030002200400c3d408156504070284002510f080c8030f106007450010000100d40e08a03500a241c090f5401001082d0743e030b2100c80d0b40d004d11070a6050030b1622850416460b101d004c429030404c161281c1400007260101c2812074000f81420000c40c1981c09039580c80100040d11040d15400221a100410958404003a11903082e44082c20201d00144503501d4401d03e034a1104103a0001c0d00c0d05082008244414541e04180400300c0f9072040f43c80401c0d103001c2d59903d00d2a0410b0303100c141c125042c0e00410003084010b40c09648180d10035215505a800001400c0040710f801140c01481c551000c00b040c003003440c0c44646112004148402100b94411f080819a82101d0030ba0051010074203281ca82000001905041800f4000c14541003040c91825196 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 403188803 1250 403187553 403187579
    0x503030301090e0a02060c0606090a020c1e0c0d060e060a0212010608090703060606030b130501080a230a0c0f090b0f041d071e150c0311160e1906 64
    0xe1042407983d0340c059418020044c4050400d043c0c0083c24540c81e1002d01512a413155012911a4031402d52400081d07a00b612620a40707184800c41e2008200e8100450050f401e81c8810150102c0c0510518908000951360300d040c003a001489504c0c0804c0d160051314100e85454009003512000700e0051004190210207003600c54112451403401c41202e480f10340c2501c0c2405140e0308060241d43c00c120000c906103405800c2855450030071b58000c0d10003220000c2e840d0883d0020301076420707140c007e5150035010500303418103402000c11030408140008035400d140707441c3c40440c2108440b08005207204000c05512001010001e01451009221100d1210f00150b010f154110002d0720440c0c4d46c5081101b940701050f940302a50304d10348200c900158840c0079800c00c0c004441c42c4049421510f101c04039010610941d4034240e0f40c565120a100c04215560554104404800b00c0880d4030411100b42100c4014415400c01001c1030b100031191801e214015490403d2041d002d11882410840100114130507485 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 403190053 1250 403188803 403188809
    0x30109060819032f010c030617070311040b0f0a0806010302030613030801060f120f0608010605011d090408070b04121205070c15062403180b040206030703180c06080702070503030301 80
    0x1065580d4004000450b5a10308426064130601d980380001800320b079605035000800b907030890400304405031081c203000b60341d034501c90100a0060300c800300043c426040503003040582180091200f1118440740c400b1600260595201000e1940420b004100350f05050158035042121a080d8501251082d00c0c0503110440621500e02000041c03880060082d1041120040c4100c4404040c460070b000712500001a03c8240201102c0b0352825800091942c0201d02061010780741c1580190b204d90400204080d02030010301c1594403120801000c80095500b2070014420b912601c0d0845040f009104010012042020300418040c50700b001d10511035003001d0140d00143c0e00241d030414090b0072010b454003410f1154003000000a40300001209040c0300c0c025103608414607501003100c0b450085540445455000c0d000d00030280000100700542405c0c8000c5920440c94140800c400c1c00c2581158288403044c081507624280b241814060a80d11022940d008040d0344003c11a29080600180c0c40e848184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 403191303 1250 403190053 403190087
    0xd1505131101050d020d0203160f02010204030506190e0d020d090b070305120a0b1005040306140112200d1103061b0a03200415020609060412080405100203010906081903 74
    0x100391000100945e80450707071035201881044d0b4072410494541400c08481105102c081440d04a01004052051080d24201c0742c00c200100301c10b03154507030350350445002401d0145445071280c1704c80c1e10003a4104880c2c0d0080205a00802c400c070f80340c2500400b200c04540007150522000c0002d0b00210703a0000c262450000322220441c92603c07000c082000506c815065150030181c1c0318040310f50940c000001d0f000b164040c00c824400c0e51050201124611001d00035024800441c4003820040303802200c4102091686a90003072180c64158001901900110021255849011400035841c10180540c41d042030103910b4000c0d04444900104a46001d40c00c1c8250070950f41d181b00b00b000b5803080d031340380c52014040000542d9036501c41c04811088850050070702c000d8031448000c20240c400003d54103200e40d801030503981100d80006021070748200040c00555980c49185c540b00341c400c10b184000c500070072080c00e0003c0c85614042c8030a007441c0e2900741b0191050b0310200d4010200b80c12440403050303c0004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 403192553 1250 403191303 403191307
    0x61401050318010507110c0406120b040503071a0a0f050603030904110904060b032706070f030f05011e080a0206070b07090e090606120d1e020c0d150513110105 70
    0x80111a00e402242c1030300081d2542c241824400142c0d0802c6c1e0480b0608042c3c02a104040140d0f801e0000b51070300343c850000380d8500309541078003085000f68003d0f081445078050740d19000480e120301441a4a0f800003000200b003140a002e0404024440c14400080c899001d00c482c1ca4500d000035200c5c05105155130045484424085800300c01400f20b800185005008025858a524188105070800c85004016283c42c003288620903e42c5c0510747c0305001480f008002e1030344d808404850201d0b0391070300c0d1424192a403400c01644d05050040d180a0a107000c1e804424460381281e07800b90045503841200e003900020f100d000547c40d10f4003183c11b10b5410110304c0b071031903d80700000c564a202c06e52160210701804c8041c0500440003060081c0035100403a2404400c0004605064442140c918000c2c00f00300da070104809840c580c0307a5151416107150058516020b00c0300042458042c0e07002c000c8481b254036101e0700d00012201d2084a40101a60490101f06401d40ea52011800307110f10050f8144880 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 403193803 1250 403192553 403192561
    0x70207051203070606030b0a1d070302060f0903010903081f050108011202220b130621060605060a1112030106020304121b1404050610020a0f290115030614010503 71
    0x8008807890f290b8008410810940d80e4144003605460640d103030a40241022040d80c00c0e02404040c0c10038000c06040903047c50b52443e420041e1a40c84007910440c102c40603c84199103980a01c80c1c200000c0c000c0e15011350070b140c41c0c0c217005424440011441201c014212090051340d134040d0600b4159502e800510f02c03007240c80d000094084803001411508079100b0403410b500f1007800e8002003100c0d14165404000ca942403081c90040e90f06a010750018400500a02c0244200e03801030603c80c10b00401000808544030340c041140c43d400141d044d0302048c000e1001598040c4100000d40c180c0b011013564038115410840000c0d140e2107240b1554940c409154504018001c14401188800303007222448240c07a9902e04000c002400d6826a40e40700d00c1ca4100003c500781080300944191030800d0303000d40b4461003503a54180010496940a4445101001a010714000d41446582c11100c000002101a601d403d40b0508540c8500e0060700816043c45000c00407501c1642e0040d1614009003800d6841e40c1e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 403195053 1250 403193803 403193839
    0x509250605030a111303031b020d060f1e1406370b041d07020a15090309032907020a150b010e10050a020d09080a080307021e160602010507020705 64
    0x14014903130040610001a45000411078240c2480072a44642c03a8a80c507459407141c00305101c4003003000a508a0f0b0405042c200241c3c5603030003e820b0307415816001401c9110300c0624031a00e502d5500307281e6465591501c0450400e8206081a4410b0f003c440d582c8140d62020b0200d2400340c0b0110703500030030484414070301c986154280a828041d14248443d941c8460b0b07100700c1d41285064011311220110b409001260485202203418996250000605129100485100f500034401d4160070340030030100b007002000043c0f20b052500899081244800e080c041c0751444200701000191400066500c03142810300054940d105038118200383c0c1800168542004005840460344181c010354800070b0142d20341d880c40e8018029012512140d4225002c035503070b200041c2c500c0d8506000b076006a90100c001e5200146801c00296401101c0f441666000300022081070b0f91040760034a80c58194001d0011500c40c42c6454983d10018045840240160300302480003035103c900700e0003002c0c012001c21100342c011103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 403196303 1250 403195053 403195061
    0x6010302060d09210c060e0102121f120803010e06101b060b0316260318220608010c0c210e1002031b07030c09050712020301090509250605030a 63
    0x80c41381c500480c200341003280040c001d669540e4212242441c0040c0c060003078205200395504003c003c2003c9402d80c6488000510403004504101036000740100d020501d0380307007440200d081510130060181c0765410608003140b5420010203680c0a901460100c102c40e59100c4031440540e4611540598035001d107007001c034042c1013002040f0790035101d1100c0c140c040c400c44850940468441c0318000c02103800c510850b04024502455a01c160741c018013102c00030008220000c442c241d07004210040d02d80490b035400d01c0000341c0c02070b041c80140ea41c80c41003050320400e0007a50f00340c6600c0c2c5072000000d102e580e51140d80300c3c3d42c100c0c00c24003448030806041e84203000306003017490074000408902100101e004001d50301d600c401c840d07800080c03c000282c0700002002411500350380c0d0104c051041e041c2411518001098024080ea08000030518101c5e81c0c0e101c188021030103000740c501c000c80e20b4a0045c03000e5107051001000c1d03c0b0040b4075203044d0440c40716580750400c240c45551403d40d54a0b02d87d0160600a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 403197553 1250 403196303 403196333
    0x20f040308090415031a01060206070f031508120a1e05070b0601020705040f0e010b060c070b030712090812061503060f031212010f120b060f061309020d0e06010302060d09 75
    0x1030300da1300c3d001c0f0620050120003030044031640141641c81e030b2034000407a1155001e0b100c0350040344541300b05001c4140a500552006034014030042100d0707a5411025241c0401c1038001e20700d03088001400b481c410391058031070702260101c1c07411090171028004000d19604c51003c000e40248584400701c3e9180e071080c0182402420010404e029400c1071103a10340081500c060a916650318115000c40c10341800307004e80303180940c10005000a1803503c0d0084080713a10040aa1003000744900b2000d05420440c4a040109405100410384070109440354030045140a40310360310880882d02001490701b50340c02143d030302c04010345102966045110219103000400e411a00643c50013003070a01e507805440260504030342046404803030441c0c0c0e650104049580103500070306405410070001d2410f00346094130340c21105002d800c040c6441c41c0490481502c509a400c039441c3c103500001ca41410303000358000ca001481c20400941403651541c0d000440030310900c0b5413403881c1901d8a8001050156160400d552 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 403198803 1250 403197553 403197581
    0xd05070303030219020708060703200f04030c210210170c0a0314070e01030c050706020a030e0d111b0a05090906040b0c160201110f16050310020f0403080904 69
    0x1596240d280180c041c2d0444100746a90304511110590000e100140110440310043c0180030745480d039175803c6014080100300218403104250103c1c84e80001d500c02002072000c81c1e00025129804d6141140b107240d031a600c00780814140381340d08980200c40007044104d542d0f04880c00c1418040d40603042d00c1c02d403155489004010168410807603105a2100100320b4140307556404c01c80c80d440c00450050803441035906500054015a184d013295000354000403980005080043c1131030b850343d45410590b40308010820000c2e8503513400d002c244c4400c0000c040c404c040f03801d101e0a281182007031156103034540302c2008084501200e889105455000400b8080c0c00040c002400510b05015002c0d500c503420b5508860019000c1c0014201c50744450584111044030b20991110303c007560011105c03d04c403460061180d018056094400181c1004200060350100311815000c0345850105800c01d400c01d0201040c0303500400801030805c12000803101501d030b014594a49510349100417900412207021451a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 403200053 1250 403198803 403198813
    0x30a090302072106051b04090203100e07030b1905060706050a020c01180302070f051f210b0a15050307050c0c04020d02120a06150c050a12050a110607020604110d05 72
    0x1900001d20340c48054020300a0034284061b48030481114564076500480c0c006c007100030b200030300c00300b401c6800442e0006000c400218566407078150084007042c083d41e0740c2d00030a0759004181e40c0d80c2403403580200e608111010041c0040c0c90035001c9a8140720f0b40314001c0070f042c1d03034500007515035145505032070389041d16100800c07403090b000941d1444c2289015082d000740c8110800041e0b4100781c41c00e075070305940019085211720340c1c10407030500c11343c51103801842c148028110080c0304060249100c06205a5005004c29104038900c14031540000035004805640d54140900b040741c0e82003401c82e03800103803c0c60000d0b070b40c00f0034403a580d0501301d510440503802400001c2500300e42d0721036006805410300c640081122519125007801c1100e6a5104203680d01c00c01e1b2008200349401000e100c1d06881c080c10a40340c1d031102640c1c0760040140524002c0010440102d440c1c451704e03a0044408565000b00310003000c880c00c089a000c1c1d6a0351005100070011004061003c01a0b1940002c0300725030380d440000c0312 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 403201303 1250 403200053 403200089
    0x105101b050304080f101104030f06091505010f05010302030402091602030f120106120b03070b1803030408010507110a0f02150c1009060e0d0512180d0309031b08030a09030207 77
    0x5880361740094080f034440c81a2a41004441c1d00f51095401c0c1c0580c0070310b200d14052441ea1040e0704285a90350560342955103100741004649002c4110100142c242000074442d0704209841509810580119040505c14001c010040c3c607180300850f084103080c48421744454414000300d2444c801c50f0700340071000311301140e001c4903440202102e5060341e01644400d042d80030920b141034110f0380b0040d58250725502c0024200402c0706560000e1030403010340c0c0e13074411100000704042031441e40243e11008544c2e65940420984940c40f607010650419014040c1a0401ca0b6440ea4191001f9034000a403207200c0100d101d0b4005c1020f201122084035104040d02e004100c1c10842c10003c0c01011000d4507902e0a185541c94100b20128100c4111309a41e241e043c00c1003031400c000e581020000b4003030f10030401400e02d1180303415030421204000e44a540c0e00400c0000c0075107402410605c62000d0003c850407000c501c0400240b00a040d02e50000b070383c2e180000c0e00b5030181012031602000d42d00843d05070640e90112 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 403202553 1250 403201303 403201319
    0x210c03021005031614270402040b041e0308030a27030e130501081f06050303220503010c0f050c010603060606020d2601150c12050301080c090105101b050304 69
    0x690710403203100d0450096034841c000117540702080000004c4042c1420070032031504143e40ca62880c1142c0d003000d00748a02c4800e000c04101240d100303401c0862000b1003c2000c0208800060980e450306031180e5010300600d00e155100c203118080139081c200c0103916840c40400d0b41103840d250b020800b5035a481815800454240a007604c54140555030080e1038403036404041c0340050049034100ca40841c0106150540c440084c1a15104a00e90500464403050005059a01000508240441e10800103a51a032942c0345907020b2003070354841c1340a81d0400d0355445220b60091204107000c00d160a1481c0e803210282d60b95801442d00746c00080c05075190110100300c0d0b50380010b2980d16140c6c1034649001a08a0003d410b0341e00490700d0705036240c08082001404030024034070380706000d02c0040c01d00c401d444019544030041c0ca0078101d4100f00040b0701000400c03044408020840c8606800e660402255050a009c900500a04044c00017402011081d04a9058907007105120b1240c0141c01e0f80c1d1070301e403107001c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 403203803 1250 403202553 403202557
    0x1f1b1509030206070305070509010e010c020406030501060608160807080a140108030c0c03150105010e0a030c090b272802030405010e0d0801080309040903050c030a021f06210c03021005 81
    0x3065006114150000701c000e4001d2142c0c5000c3d860030340340c4a050800c980d004417000e50324011603904000c044030450740140ca55000d02c1d4042e40c4550000f05005007003a03c028040f000041c41d5041582181e192040465000095035810961502d00030800780c4e510018040079118188400e440c0c0d004903c00047d40a0010001d021014568025640080c0001c1c00f0582c3e80d5403450240403056121500412070356020b81012041e80c0d0000c1e0001000c59940e07214165954002c0e4403150009440300c05c0c1078100d1521305d409180c000c00250340400090b42d5603901124000c0000c0c88404480f881b81880b04030720002c0d200e91500030310b10071025035aa1525142881c0a400741250008691186103190b42c882d6004a45003816030310054001d5041a02d21000c0202800c070700f24003a42480420060a219408180010700031866640c000701060280d01c0704128111210500642e181c0d4504481400007001a10900d6218078480d448014130510310300b086a00b0301a951b2000f5844010400c07500e80003a013001c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 403205053 1250 403203803 403203821
    0xb0d0f0501060f060e2b0507030f29130203011107110f0603090d0309020a0e040308040308070206070518030c091f0b0405130c030b03100e0c1f1b15 65
    0x1489680065850005440510750f048205030300c09a6102c1d2111b00400c4003080d0409040843c00300340f0030120342d4852505110054000383d030356203202c0d01340340c0030310081d80e00071140102850440d840d1528407050f95041d039013000d4503040c98500c407040c0844c150741e001d40040c807440d02e042c4d0985645402e1032606130341811035080300d24011032400302d09003040c0c6001004c0d203115034900744c0030380051500c0503011002410041d01c00ca900450903d4007051904050051902c224480e4480000906050030054200ba50047c45141194000345c10403d08550102c03d40e040000454041c0d0030f13030855040060300300343d4047e108940290b690410070010288490400044449040f601144075895100c62056403055001c2c80c0d800c031045500d000380c03402d03003640103411880d8640740000e0b10200041c00a8146031a050010005a03142e8400c0040c040060000c545040c1080300c151000402c11100c19144200e60a500c00030721809090351031440700040b102c81c451a520400765400c0340d2860040c2001450401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 403206303 1250 403205053 403205069
    0x1170a051906062703030c08070309090c050901172202060c1b1509030304061d09070206181b090c040f0f030303050105030c090a020f090301110703030b06030f0a0b0d0f050106 77
    0x404164800141004c1c1c500790398041d566407500181c0394907510b900c0d40c0901d6046003007020722100018529044d100b081d58000d001c1da43d00b95a03151440c001000214000c0203070721449032150900c05101610b48540b5502501c2c00c107000ca000c00d80d800000c40d00e00454404207800c0c0200138101c103a00c1816135480e2010301003254401020100500d500606006041c6c00c1e41d0907505c10001404800e000ea06450700765028a42c044409040d4031000c21850b2205941c040096880142440000b4243d022380038281b12083c0000d04134617101c101001402c01d910b1151b9801002018085030401c608401190f0140c40b40442c40c0840700d44c0e40815441c030583c188000d800080c64000042910304c0d001c68562402d8800074054652a120000600000d50007000c00e5150050200110700c403e45080c041d003043c1c4940080c5460b120081d80c02d000e010340344100822071041c041042003092511b9001c444a4200d00501000101da006020114040030522200035012030149a20a0100041504201c080d10705403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 403207553 1250 403206303 403206347
    0x50a0905031b1603080a030f0603050a051b040c0912020d140307021509130e16060512060402040602030a030e1509250510230f03100501170a05190606 66
    0x70f0f10442252403c2400002d0440c0010032128039900d02c660010b9002c1c0d0350300d10300020340580d00c2e554145046800d003001c55807508409080e5060000d821146c00705d9110544050080003154100240820303850b00400790005141382078482035480b800d2805610700d900c8405800c0b50001c0032090390b41ca8004010892090a000056448801d03c56080d942e4a8101910041c007641d15072020b80c0280c424a050780700d1910403c05030304990741403000c02e400202041d0721415074030001c6040d100a0140c0060105028034010001003180c1c9034004211120030768a4980000c13503405021456042103480044458140c44810500c9a92013000c034100070580d4a0320b6840000f400b00d48100c0305440281e00c80c072036014860303482c80382c052806844400018612044007611000f40c0b1417041c59250089080c4a40c0c5038408000c011a11442840340c501030582400e20f02600c000c0030400f011480b0005107208089030b12107000c141032040d0300c40d0300a401d10a4490600826407141307130040540d201c0b862007480720305078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 403208803 1250 403207553 403207573
    0x13080a0512070b16020a12090807090b0d0807061b0f0e0102010c08070c05030c06070c020a080102030c07060903030f1e0b060c071e120605060108010b031603050a0905031b 75
    0xc680441e010164840301d03004007659590f25208813000810300301d01c03c0d030150f04410300019808a00b80d00d070b6a0040d440c1c40c5602420310741a90702c0d0980640201074803614052129113550744049400c02915401410b032030303941e569031601c507016000142200310740503c02c503d41540d0356084580385c5400ca030203030780c1c1c1c4103082c07040001203080c3c40340b006100c80407484000111f10300c02e210b800c1c032079409070181c0222858400c4c101d0109190640884a16000800c0320310184114074040145900424900e002507007103040ca044003401500ca80030009020a40d43c41c01d400805000f500180001032920004104407240c11f00e00300d0344000c291010100c12841c040300300c0c0480c58100c0944a000d1503200003091035505004c8d84140142100e000c0c03070f215020b0440000341c42d02220101c251118400c41c004101c40c10024000f500442c01a00040564030301030013045080c0c3c581801d00c0100001c030380707008140b645560014600519800d08081c00e54040040c80308000365505030100840303100c81c0c0c110f9001c0c00e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 403210053 1250 403208803 403208833
    0xc15040314070e221401150b0c06090d2c311802060901230408070501090303050a0804060f0612050c01050f07110307121a0105100210090813080a05 65
    0x11000c5000e440c00300c0214070706000c252031512100417600c0c4c060001075140b072a40c50056800c40141e00c171482260380010201d907500c0062201e16040500700c0c004002031011540d0190001801d0a458034600e10310344100711240004480e5101809070240c810385124040102c9a910907800900d001c4d510021034815600043d510301c02c00c0700c549a01105503042d03c1c0d181d8200607840e4400c16880d410401d0100d200302c05902040c0704511041c0416007040d580e1803030082c0160900c55607503c40c9040c00140d0908101194100048070200301e014500f00c5200e035100e18154004020503c00e9099240c54030344080b41d00207034003105000450040c01241c0c116a2108011950782c03041c5000410140014085840010005010f1804103100141555100b58407116003100790031300d00c3c0d400d030b0f4103103484442540924050b024130350160070162195441030a00940123591091410600e0010a43d141c2d0f01409100038102507501001b11864140441d81d52400580d9880001c1e0405031201d004004400034006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 403211303 1250 403210053 403210081
    0x1c0203071103090f060702150a020a0b06040504080d09060608030d06052b12170c040306140f07050d06051f02060a020c10050603030d050709081e0c15040314070e 71
    0x101008207282d900c10028424017225403c10304040740c00c07260f07214800c1048581d031380180407000c0c4540d000340700121082c01d182d003405502804450103685003c041c0004078580360100c0f0403c0d0310005d008a282c2c062032410034000e1460b54080b840f140000300300300d0729140301070701302034110b03501186c04502c90315841d40c09000b42c409034008896090b80c803128030000185807041c1484101c200e41018045c180540161040140d070444155442400000c1d0610030002607100d100f80d201c0664001c556207182c0b85d0b6140b201c410340504244207106000c02e900000b00c1490300b14201618014242000c0601307015800c0700c07922124001040035001d914009807100c1c075544241c50407940080d0042c07620031102000f4000820740900f4454040c00100550040e45003203005540c06003180d69130b85150b852500394640d0070481413124400065600d0045198024000110304205c00800c0b02c4468442000c00644c41c400d1007640d200400711201005a0381090700049160022150190075180140c0e0390900441850 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 403212553 1250 403211303 403211317
    0x10c0203071e0815040321062402010e1b030a0f080301030302012004030f02061213031d2404050306070809011a011b021207090218010519050f1c0203071103 69
    0x4d100c6400260109111300c0003d0002c1c0c19018500c06000a402c8202c425500942c11040c404a0303e40600d0f0030121808031300015486003440200311410b07d000300b10b0f80701c032000c0c4160b0312300c000c905420341240d94003440004902a40504080d0080d540d40c0750400342508240301c00d4002d54602a0a09442920000324503000c0c4c058020740ba150504680e50034210900c070100c141d8100c0818007030640c03292000400b582c00f030000c49040080703040d80e030300e402840c0e150204001c24001030380400040072a107030441c48521041c8110035442c1d80c15500c000e44851030042e03500c01035062242e1800d2040603078000c0d402074000d5140740c009001c0c10000340d021070111ba90711074006000460340c0c0380055001951403440060b1602c0100580080f89903521160301d881d6250300300214403503000a8011440000d1788482c99091402c0c06c200381000c100c55500116141000780c9001071103c009a42c1a004413050200d410790480700498010a031003540c000e00003500100e0751080443c6411881000c05031002041e9190 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 403213803 1250 403212553 403212583
    0x301020c031209300f1b010902040f020a0e0906041407080f0708010302010503070e030a060204090c020c0909190609050d030c0e120618010e0703050a03080c0403080304020906010c0203071e08 84
    0x7032138800e95400030043d4044400f180c007442060084908040321440c082070390a0b01c24001090800319801000100d0355a405503000c4644100814059107030000001650aa0216a00180781c0d0b594004600907180180e00e02003011442010000401c0d00f001e052801241c0468100c600e50f5200d00302a56420b900307000c007a02041003800007a4010340301d4503407010341001c080c050f18850400d0765180b8082c0d800c1500482803040d169203c40c410140e0400c80e40c0e02c0c81500f255441d40c1130401e8524552601d0350041c924083c40741c40c44c10582800900d800c01450907078480c0848410b00e0f440e0384010300a000802c0c02c40c0c000b480d0300032510182c0ca441010b59610080440203451103480d58401d1000040b01e2915442c2d05548828488480e0b940501451000b1801130300a0206440706103402048118028105000c00c02c05004c01e001141084042e2a409607064450729a1070b140c100058503141541400250315200e03001003c64011808060003007800c1c0303da92051700c02501d42e46040d4640c03103031036034182c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 403215053 1250 403213803 403213873
    0x7080303071b1b06051801050711010c020303070c0e0105011413170a0503130806220b060f040c020706030c0f080f0c0f12010f090204030515060301020c031209 70
    0x54880080140001c0c00e44207407002001114400244109000c2a034030850119002044c400d4003201c9407004944181c60034601a231603c1e42e644d03207a43c0000020ae01d41c0d4100700600c404141151000c0089564050704043c41004683c0d40d540c0b0202c140d4002d010389c3d400205039441c106001da9544064440c1e0300c00540e1902403083c00d006507011310043c52580c020032407040c10350540100d80c050005000c50340d52010002c40283c2401c2d500c51401078040c14503803680d461250b0302031224900f0f040e4582601e034044188000e507221407001807400004683c0050784641b5060318900a190006540030494100d0348040c003030300d1060a0141c40c0700f201c3d038035135001140c04600010064010b40d0200c1c2da2045800079003030b061200d12440a403180d001001d030484108981c00c0184280d28680710701c00b00800c5c1c12041546020b08640c2c1d401c0d01da172805088166810101e5000c140655029019140851140c9049070348445007508a56501e1009a0320b00d00c0038000e1118160300e0701703080310300010f42c5054124921 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 403216303 1250 403215053 403215077
    0xd0c030501060603052e170a0c140306011401090b040e100e0c07230102220801021c050406061e0f15020319020f070312030f140606160602030a0203090708030307 71
    0x110980c0075010b00001b020444410100d6940e039100003952015204070010800f03011246042450a071046c0c00c8248071528082d94101c003980d00041050546000000c002030310070541006951a603c55007040d6400d010115001c101c50220b098098400c000301b036811880203944030f000707034104013098030502a400b2007004488080b07034601400100201d805807004c800d00340d600404508903000382550f0300d10201d80b40c90980c0b00300700000942e400f40c60400000c5281002400308800740203801c4240e00c203455183c1c0e00140134040d0a51240c001003240c00c1c03681c00400d002404503054510340d4018001e040000950101300b140c0003027003a0f204680140c00071031411028012550040c1980c5400c00c0441c0320303162906810032000d100100c019031141c4414902030304030490107070580300e0503070f051169545005d840710072102c8280480d54100764103032103070343d500c0d200b0b1020400009405800940074900000901c00340c5100b07503004503c0b9001103410340320f030303a5103071110b0726180e11080d122003000812030b010132 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 403217553 1250 403216303 403216351
    0x31b030b03120c120301030507060815031908090d0819050c060403030b150c0309040c180303051c021804150305030f09060910030c030605010e090a020c0c0d0c03050106060305 77
    0x1003982092090444d5103040c914214005142c1c000d0300200d1301900205420414070360482c11150f0025a0030000a0007031000d080481d60761058002da02d007080110300c100d001480724070011540740e400064000c25440e0054144011191310481c0441d10404003c081d6040e85131060301a50707407080c0c40d007020700010744035920100c020700309804070306901284c00d803244900404c2d820024082603600300701442d124a5500108000c031501c104001040c4003041c10004490500581d40600b40c1c1d070b15050241d00e414648443e100940c0d0a08105a01c080c40021850b45882c1c0c4007a04140d00401110244982001c4504090807054184001400c591040c001e030314030070314020041d010b4400f01400d07141c28007840304000b404400c000f407100404660303a0020f00303202c60f03070600a8002415081c00d00444591000002c030700c013000024030548000f6800b10b02c1d8400003006015001610301e00800258080525003003803030100c80180b200b103030a0740ca000000603490340a40141d520501075001005015440b00d012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 403218803 1250 403217553 403217557
    0xa0804060b040b0604030c060f1b03110f0a0c0323100209032107060b0405150d0501091b09050702121803250905060d050c01180e07031b030b0312 64
    0x102a07005403680d1200005481345005000150300030007030301c40407a240460162004004916500401c5010212070140c03502c0c040c1045c2403250b240c81c01440d440d44406109040c030203118051000e5015405041007400b481c1c1e04001c00f5170f40988099943c103529400d07a080d03803010180309480a504900d603100b01e200b40583c040c1002c2800641070f92070110510100c00d00b43c071100c03202c0300d070900e4010403d14180101841850b1459005403010000c50410740c541c0d02c50ba1000d42d0aa0344685000d440a2007003101c00e4001c541e0080e0701140482e95240d01c083d41c08a89003190144ca18240d10f8440010f18451002072031540c003071800c814440c03516001104001c000046290400d4141c4100b61304402921401084018590f01e2450101900717420031218005903000a03005910441c0c500b0080703c080f50b40410701d0392030700c202401c101074006c0c0034165824034000c4a0f40300d81c1038500c841e010000515010741101180090030b80c20300d0b40002070302100354200c031198131441e07806601040c051104040c4c0f000c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 403220053 1250 403218803 403218821
    0x100f091e05121902010506010201090b13020f04140106260c0a18150e0a0f050f21010b0103140f01060311090d110f01260a020910021506060a080406 65
    0x401d070703140305481c40302c0c040d00340c2e200860401250f041c0041900c011a4284941030b0000400d200030f102052440e16024041c0703102409100342d401000d42e50b83c0c115030324040c0c1100c0c6941d02030402e02c4003252152100c51416070034403c00c400700b010300f010b04410b59003203042100e000c00c00f0300d0820482e07194000003103981d404c51540c21b030a11115028a005c1620095015130003800d91020a600700c5082e22401000201ca00300e240e0700920f096201444070702e4185001000703032081034807240342400c0350b03100299512003128100c0315003144116840d0240c1c10190403031400400280c03810b100c402c024104120310342d0703003c8400180f11012000140540b034841c0d0001110058203045560504800070001040310401d104211007604ea950109010f9041c01ea1a850b440c40c82420103080c00c02c050401c00311010008801c41c80541b01403c006240041c03542c0c180e0b2035884001d85114041010501b01035940d81e002140d52a03a40c3d080d900080b4a840c08070200d502e41013076503841c0e40d4581c8070380d907810003e070030000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 403221303 1250 403220053 403220063
    0x70b0a1a09090c0f0612150a031a013b0723030a0f0c0203031303120609020909101a03040606030f12080105010503310212100f091e 58
    0x1410250301e039100d140907805100082d000d814450120000c00c21102c1d040340ca0540034510900085030b2821310010195440746455030140d01000a480004000c5806a0801008201011840442d07001e1090241d4103071800342c0c9506850703a242d2440c4034441c2041c500c6800843e0100c4000100ca242541c2526400007903500700401d62000340780110101290304c81404590180c0801040000c490703900801144070f81e010405c1191040c40ca000079124400200268401400742e50350108144c81b43e4501041981044410080c442e21a00510080d5005145492082c0015408503442e40c11440042e0211a030300317050100d42c060039040841d2503802c001e00136074036107075a030b40300001280c03e0030098012544202070098a4510944014140742d00680000e41008020b00070803c170a40802c00900304141a50203c07a00a603981911000500b00c940300290018070300008a549807400013041c0922201580c4144094016150b001e000c03034241d038502a042c00c003500c0c20004080524149102114055 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 403222553 1250 403221303 403221341
    0xa03060f0e030d0902180603120a090b030c0306032b0e030118030201020901020708071d0405100f0e0f0307080415050c030705060105091f0e071107030501020d0b06070b0a 75
    0x22080540c01c5401602c40082800c1e02c88024004524188840d81e8480e403900c1c0c14036119040080100c0e03929000310306c07491480d40c0c00007900c03c1000d015994030be00500c0d20380c1c1c10a43e00e16085801d0002d907081901d02501a2140c115980001b00040c08910080408040f17100c0c248019400121140c50314801040c2d019562817580da144441101c440041c154081d8001580c3c1d80c00c0000024130b80221030380b0401d12500150028004803108501c5403907010f2003502440601e0315681850350411010303040400c1c2603032820540713216540d081d4205a0b4260403140545400501040000b03440744600c6d00c00428200c0204414020040c108004403a80361551074803a0a060202011a00d51f13400b107039056032140e010800421a900c1d189070502d61001300c400c280e24034501c0100c1c5d0007500725440c0c0a00e2001003244400144041d1050300d400b11610261303021200c85681d80c0c100103000b5840b186503811030900340b00b405031141c18003208540e290f0f94000b1045c0b40c155285507440e00182201040480d05241c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 403223803 1250 403222553 403222571
    0x201090521120412110706050a05130e090a0201091a030615091e0a060c0f14010e03040603020712030b0307180f0219020105060f0f090415020705150c090a03060f 71
    0x10b1040c45244104400841150440c101400c0104529004510340c4d010345424000283d1200036560f000c0310a00704a51100d0710090b402001c07148e940c11032400568036000700710041d54006403044000c1e0003038892160301d0782ca80501d002042003100c904074071040100081000340c200b05a201207181d0042e0000781c1402c80c41c0e00060214894041c2c5c00078210398440c040e0f04175240400c200401800d40b800e02e01031601d01940d40b420000b10b030340c0b80030300882d2803a01c0c80045040290004036455030b008054955403901c82d03001070000c0d00003000507500d0380010710301041450f01a109540843c5401030045c0052440d10250582c034021a42c0c0030400107403035200300c2100c800280013070612280e1301d00c0300761440f40030b4443c0282100ca004105034811010340d03410995980f184d100503c43c01c4801ea4180b50780391380e2420120840c9105120a0000a10000f4640280140442c04910b2015807404480842e1241c03404032049000d0300640941c016016a8204000346070f9501c0880e40c400070300070104032490303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 403225053 1250 403223803 403223827
    0x105070903140a1e050c040902090117070308030c1b010608030f0a11072d06120902040e030f0301031704180203060f12070501023a1206031b060201090521 68
    0x1304450403940d007011004002d4100309060210004601090b20104144d41013a00000c0d407051040c45034480340c1003400e18002001307000f40301760700c083c40d0000c80c03440c1e0ba41482c42d80740d141540000516420454864408000d0703038010f01614040700c007454021030501d21101c410304501d500a402c08418000200501c4c03085000910403038004001e00c124481c0103804031050034003214848580003401d02d50541701485842c0d0008400300034811020000a404003803803020030001e0011039420351061001003002d00f02c10660380001d5040e1b0f4480c01504c8055a45c40d50301c100075029502400c1c04402c0c1e0180d061700b1400d9281d0240d50300100040c0384402d960240c8003c981418000c00d224003c54210308824001543c04001081c868000b150903000d0f5140e068041c0904120038440003060560b41c955900c46a5106000c0b910800d17004a008026060380d0380303801c4504d074030229001d4800c606a2034000a085006104e8224081e4102c0c0241072444403502129102501d01a9041204181400b11400e640 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 403226303 1250 403225053 403225073
    0x1406040918060636090c0e09010e06070f050a0c150608010e030a0210020c0c090115140c061810020a02060a06050a0f03120e040c0302030a0e0105070903140a 69
    0x1525030000504088071420548152079040e00102030444030300c00d00004c0714503d8002d045410b0031800c10310100740b03000d62148020340403800014050701c0c10600c0124050094107030a50184405000801c020b60702400003688500d02100e0340310104000d2802c0701481401000148000e04c1f1519140c40040900d03907865045525a06442c25203540d224400d102804003407081003002000c050003141404008040203603a506800c00c506069500881e12124424042160800407100200820301c550307100d2039a0b42e0b6a6841e04501c60025403c0d09800c400e45000e0001c07101111075810190425542d203121503940481c0c1c0440c009940e11820604595503481c0f440a0400d01d03941c0c0e03028141500780516003038240d0304030340c015601c68030b03010307404000c081c15020145007260360200d5506c8031619414403d0b1007030020320b18a150010708188070a51440c0d89640254840c414054007000a41c1940b401d941c2241e60880710700b000306000da001400800c421224a22441078400211100d10f24941d4559601c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 403227553 1250 403226303 403226321
    0x8060406050a180506031f0f0f110c0c0a051507150518150108031b03130902090405250c02030f030a02150c0703021507030b1f030605030a0203060114060409 69
    0x520350143e55002108070a024081d04030008a0003001000c6414900d0b50307a660035000441c0400795103420f01c004040c25078200220441c4640800c01c150130340840c1a81503070307000c1c407440300ca1402500e59452081c54a40012415a0000340600c85a54820005c1c40060780c41540259988a03620640b402d200605025131071007000d044040d184040390007032881d860051002c0302c81c5000c0842600510800d0f80c0082a00c001020440b15201c5000c500c186103825803066040400400351500c00101d01089540c00078046d460003901c0c2000140d96040c502103c2c50f4151070302c0c11402c2020400406414450386081c080c0600040650b1642a1461085440c0d1707880101c1c18005600441d034203001440e032021403da4065240c851070b5162010554000b0b44442e0000103c158880036103001c60320440c4294814105000c0103058000c0c451140c0c10000441ca285500031000070b420824086240d00340030400d40d030b905a0180003084980d090a401c80700800303441307030215009803041c80002941c100c180541190 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 403228803 1250 403227553 403227569
    0x307092009131508010606020316110a080d0207060e040e0d14121003031e08010303030c0c1a060a080d09090b04110d06051003180210030608071e0603150608060406050a 74
    0xc43c07403a149240d030940b02e0b543e101905642042c8229030003420100b0502d00480e51003103040c4024600c0328001041c03142c0b00e4205138102e2040038548048503400249003002d95401f61103002c0302d140203004010588420340440403498214800c03085c8880d00944000c0d601100c40d207911800e28075019124511400c086650310306100005e00700b0405c0c50b4120140380c2e409502510810081090584040c00f280300c103101c02003c0542c1e038607042490612520614440d540d02c83c00300c0803c0d91280b071080180c00070944032244513040d60000080d00381e000161500c00261070761503500600c1c0c58201e000c002040c807562415085030b182c0d02d94a081c410b20701c0040c0005c4c0e10001d4002090b500f413005100300303004460300c00000c2c54500420488a200c48407850351043d41d0458684111820220f4210082c080d40c0e0301441c100d10070030b031000c0f0b54541074022040414401c02d06280665588450840940b407070040c1d050140303030800c081400000d00c60003006500407030181000c501c041c1e540001c608152015401180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 403230053 1250 403228803 403228841
    0x409150e100e13020607080c03090a060504080a031103071b0303030c0e0916020a051c02061605092106040b0604140601020705061b0a0c0302030709200913 68
    0x105904611644540045454141400c22410701449100d6008003400c03c1c26400300e03500c00c483c00c41d51420125540180c0c80b1103980e0711508078200c413682e40d800001030148195803590011030405d1143c000e803800c646a032401807804d45010340b401d0307070801050301a401c814041002020003050340030585502c0d0412202c2141340707052840c180202210801d8007100c0400c0072a83c02134049540c0c05400981000e40040184900c600d00c0005a1510817400c80017445409241c8109900b81b8041c100c2d505800381310f80079a080341c1e9905002c050100c44191051000c120f05214040213030504161124008605400d81700001408255480c9080c008840840ea03920b10142084001d0501e030090201c0e1b0081c000b8541410300b80300300003075100d003141d0054902544d4041044a020080c001c4141c180c0c8460340280c50000c801d0303040c0005102c1190200342d001e480f440310001107155591142182c0c40050005140000800c092070b1030007580403951540e80048d043d240307000700030410b10401030062080c901d045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 403231303 1250 403230053 403230059
    0xc0c080d02102016020a03050607090602010b24040b0d060603061203120c0c020d0803010e1003173402010e060f0304020d0f15020706050f0105010f0c0503040915 71
    0x38509010600d078250540e0808051115040c401221580001030701d005481c4c94901c10707800d10395441c225000182d44801c01030400014800045a014000e1083e66a5451b10319100d1000342e007a10303c850700306500a2401701021340b03142c00f20036504240191508105183c0b5560301d4000d520b60b0841000f1010242e41e4250400800f9050b100340c00040410000c0d440210803180c5001d08140826855480c1940d29a00140c50051103282c180e440264000c1c20b6016881d0f180c1403005594100f405074090764005600458142000c17100d801301129803004c446140c02100303401c0c89036981c01c10011001900c0174030140c10301c0c0d141b9102c1e80721a0003031010740c403111a0340f20780001030000054103185401200200f05052900d00ca120407283c1c07243d01031714540040e080c10318250360036003c070250280c25403c1c813007600380d1004013540040024500503141482607413141510001045000e10030303e40030801c42041c0f03040b1103014242c6c0000241c010010360741410341c0e5210010a503200c0000c40c0e0400384600f4018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 403232553 1250 403231303 403231307
    0x10912050d0b0901030f0b0a0204080a06060e010f03081b03072f04020406050901030b0a0506120103030320030103061e050709030203060a050601080606071b0308030f0a0905120a0c0c080d 82
    0x42e05600c4401c40341c4001c95491510303801da8000c244a0054000841c21001a1711041140c04850041408800322500c803140d50900304010001c9009072184500d4007800054812081c40c400f0081d00c1d04054010306c1c111200c0d80358400368a443d08030060900081c4440ea0101c2c0031062000f03007541c0507070500c0300c8008030071020b032011810aa10061040b803040c40705004140d40f150564080920030300300060b00411510000f0329081700c1e075000507031103a40043c80f0340c40401d10803038450480f03203c1d0b2028400c0241614800300401e0244004078260b00081c8010004205c90fa0803180068840340684400e4018811203c8181c41c001c40d883e03004228903410800840c10100503c0c1d5201c010094100101c0c100400002c0001401402070385c46038102242200030b02c42d888a003480510000d95162103415501c0c070f08040d41c0c0d08116072104507100d00d42c000903000c0905000700240c3c25030182c0506002c5203a0501c1c1559504070000400c10014004030000010b1070006680001e40540002045e80c00a50100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 403233803 1250 403232553 403232561
    0x703140f03180616030c050403080d06080f0319050703030b120106061d030a0f03051902010f06060318021c0204020d0b03061003080d091a041406010b040f09050603010912050d 77
    0x2c0050700e600803020089000d00a051103102c5444034030300483d0003030042c00e088070b980c000c0b5040500800000101131403842c12903400601259840d40c2a40d8009c59243c03009507ca015618500c40802c0e0424075400c2014418030040c20f590f4400c3c14009603009201000c034025035808031400c5140c0c0e40d01c1a09020454112201880c1070200d4130b448005100c4c0b400c04a507d0701e85d840001401c00c000d400341401018094400c0c0d81d203103130418242ca054246041d02c000c1c081c0591b80515407900d0324094020510314400d0095482140800042500c220240e50a206a180000d40d001005800e01c00c00400183c0e01c600080601e0030081c403000c20000458000c0604240018004a400a1a203c801c2001421a00c10f44141550385200021945400d00703145604030b50001d1888203464070f500030001007145201503a0f82c502c082d002101d0382680c90303440a01c01441580903640c81825114010040b03071895802c80d59110602030000300b80d841da1a13031003c2142c032020804030045078008c00d100d007102080c0e2107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 403235053 1250 403233803 403233841
    0x60a090209030307080304060902090406150603051501080702210702040509030408061909020a12060c020601081009060f1508150402090604020702040b0a090c03050a020414060703140f03 82
    0x502186809402800030f5500d02c68514000e08480000c0300040034018690700c82d0400c1038000d0804009450241f4182d0020310301024407003454000b002012a00a00ca481941d210b21612501004501c01d500c0055500342e40c002d141d030b021403098001c105101c0c0c85100d080d0f02c240200c1c0d00e01300c0e242d00d035038410031056400090800e91541d000344420000b00b000021502d40210012021021268141c484d84010304500a0040d40101c0d000600090320044250f0030003505000310130410401c8240750080b43c5500003031240240690080c1d5021fa80c0c2080c90f400100814400d42c80014000603441140c0306450301452202e18041a0200070451300005021502860080c40c092000314a02940060401400608042d010f1a40451101c0445d1115881070b1144030000b800010120350311510700000d8103d050107240040c1c205804140052401d00a031000e4414034489400d00040000c203020158100030020342c1040f1001100c1c81490004c840201600c102c00e00f129517030b0b45800b40300c1803030910f6684 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 403236303 1250 403235053 403235069
    0x718140c16080a180e040b060f09011404060f0609030201200607030b1210020a181a030c0409060308040f06020a2001050d1b02160e0106030506010c050d08060a 70
    0x2000388440d0a01c42042a01180d0140010781c42d11604502100e240e42003070b01c2e662003440d4454010500002400c982c1d80f0441c0300b920b00174100c3c0c1e80c0105110310302c6810700c00303181c002da481001070040c449282074200b1500c101030f20001d403640d0380c0c2403001da020700c03564400c40c0030a0700c0e00010320541d640402248075001c0b41103088032001100d2041a0f40e540b40c028107030300400d40d4440b1b031040c1c0350341c88425403403a0107005411202102c080300c4903075000f58004010700000c82e66501e80c410b0500d240c0311404c4200c038100c0486034904503100c001e4081640c402001d07066402400c00000ca4605040d104a03805980611700c41741c0c659003000a54801000c550300400195071000c040c03480000c5105902242c11800c00040c52400300d80540141ca81d030045c1d5a0f07502105c1e0174019158914843c403003400c0c49140580d800c6900f404007640240c0b0015a00d40121600341c0e00d520300502c000c5000f900b2103070b0083c90615208454050030344509041071b40703603129440000d034210148000c51425203d10b40c0901104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 403237410 1107 403236303 403236307
    0x11090709210c03150c08130506060405060a0e0705030619240e03100905010b0f060d0b370902030603071205070902070c0906092702030718140c 63
    0x19035105c00040c900700000301656640306d00145507681100c00b500382d07901c0350b1003400050b010041400ea08401d039290001010034041503071610866966442a460342051070802402c041a035410045507101c4180510a5400c001009000120041590020481130210640b401300869411aa00d030003144d40821074107405030060130301184188020070000007503404003d0007203000381e20fa0760001c50512240045440035480f805403184014440c2c2c2c012000e82c0440c1c0c403007038100c00196031400c000740e07070441079400301180d018080c080b40d070070079130a6207080320109542d465540308000c11860300020010503c00c0510681029041c215801c0d503072982d41c1d060107120320500344030346541e940c6012400201c0c01c810b4400d0902c0c84031021000c0c851004460040021048144010f030703413500500f00c002840d030b6240004442c82000602c0c01017042980c12649600943d001081c1401940c02 = true := by decide +kernel

theorem cover : BRFrame.Cov 403057553 403237410 := by
  have h0 := BRFrame.cov_init 403057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 403057553 ≤ n) (h2 : n < 403237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
