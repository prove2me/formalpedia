-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4772
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:40:58.56+00:00
-- url     : https://prove2.me/submissions/a0726734-0ecb-4be5-bec6-89b78b204a31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 858093525 ≤ n < 858273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 858094775 1250 858093525 858093541
    0xf02010902010e3619050114010f05040513060e011a0d02030703090213020901030b01020706050d1109121c05180105031f14090108010509070b0d02091e1215 69
    0x101e0b01c0c980c43d802c13400740f03052001e0590381c1381c501c0042103c4a201c0130280340381102058a400e20342e18182c45185141030014405c4541410b1040c211003000e182030000300c020300600703442034400d90304071941c00802048182c182e44c1080d040036003a601d228044000e641da848008441044601e144510304200501c00603648111a0b4069a80610380380b03004280380c4d040d0380104050130782036000c050015800190042207960180926045401c0038401445000e1070070341c0c02405c0340140f952140708182c8800e9907460180d00308007503582000d401010780300d81d10200700c00103550328015052042406a1600b04081d018090800ea484c0b200311000c0010013111144011500c683c03000380a001c07044099200d041000c0c0f41c01c41c241000d8a1071050340c500d003210b050100702012005a0182c03007240e06000400903804000f0908008a03940030b102c070703504c410582e4032440107400341c494200c0c3c000120910402c027004020062400d44001698107441841c10580b08548540d03920391a01000048803010034200f07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 858096025 1250 858094775 858094789
    0x6010c02100212040306063210180b03010e0a060312050307120603050d022a041d0604080306040c02030a0e01120b04050c0304030e031902240c0d0f02010902010e 71
    0x5007403684180e402035140c4820260440d042500162161682d0310020300c42d981110300180b5000f400b481007046401c0250b0318a0039154206005940100440384244032402d028202050119002111030204183ca90661819a0b0400d10502c0600342c1b6280104e10a004984905400d4a82090300284495021300e0262410707403002e04070760b0802000d0717080c5885110540c8607105c0a540b085020307005002007904002e18000c6842c60042204801d2030294200809030035202c10301e0391b0161000304200c01f008030b40000d4840c28442040c020b000700c0017004100310103000110b104035000c440401049100324000c0f81c1d01c0c0510360344172001c100e515030702040e07941c040d1104024098444002250017040c1d0001304090743d4003a038900d20405000701c140001c168010b044400c500205800803c000340881c4501c6c24020390500c03020b40110300407220100d000030b0300b0604005d925007000b03a00e03030355403460400f15583c0c2c2d801d40c00c80000190300c0d4030580c030b0051060280d03030584c540507074840c00010f215401700441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 858097275 1250 858096025 858096049
    0x51c030e220c09052e1d040c0320030f0f06010f031116080702030c042315041a0907050316120204090501030305070b010906050904060b030709050c07051506010c02 72
    0x50081c2c41ca000a51507807030580d459141c1141c40c104840c0c80245c40c05040e5000c1c541000e10701031002c1c008241c0c42145c480c0c42c6014128908803008101850500700c190024500c0c104d0010300c1010521035060740220460056000e0014007440840698030103040c459418420382d100342c0007411440c007001c10340d0701c0303600079503500392034034800524118961445691101c02030030101d601c40303008202c003000d40c501880702c4000003405460500c01203400f03141c404010114181104464408a030106a00c0c2d00e5405541a10b01700c0900200030110402c406c00c071114111001c0103108140036000102c3c958441c4055900801d01241c00801c0180201c1044d190b035807405018144080e0300f4840011030720b2013401240d0003540a500c4141ea034051074140040d603070005812820107a81007032030801c003d44400f1100350303100385c0011000030611200030002c1d080c02400e40c00726620500b484180120009a040103000c4188654202e40c0403901c165040c805c03000b0102d8020f070128041c0a10f02c1c0141c00c1403080350b42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 858098525 1250 858097275 858097277
    0xc0f03090c03060118051014010c0c05220b03010b10111f0c0f0c0503090d060f060305101401290c0304090c1205061e0604051c030e220c 60
    0x40d414071a021901e058000d91000c2c0c000b95600003855000d81d15032042603040101080601d0501d41404268502e143c600d501050402072440c00040602c070036602440c01800c0028000d409611700e24001124040c1802e10760b55080f450000300c05101c0c0f40511500240302000344c001c41b41100481400c0d142042110090700c40340c01009400e95003103040340205040c4400096000aa00d01d040c140104800ca032a00c42c04d0030700084a150801264000042d00e8a0580407900a00001c01910b48640901071400040701c6840c1070090220402001150130404150a082c0c20030524451071282c000e0080c003849550100c00d0035245d500e030407821145001c070401c2c0d0510750407464080020902855a84141c2c0540001541c580f4040e090360740c0304620748100e1554100c14802c0f818030350001485080e903894048080701c0248601500c1d6251503003590000d0500a182c050f102c00c840880c5280c2a100c034404500241140e407800c0464907041c0c0040c650507a9810a580320402d96a0800c4028010165208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 858099775 1250 858098525 858098533
    0x321060112050a060303020706020f060a05130203031c0b18010515090904060b19140108060a0f08160905100b0f0d2406020106060210092d0b07020102030c0f0309 71
    0x74400380c00c54040c00d40100300d5410005202c901c0c6003002802d00c801c540084045421000082c0c140c03550001d10190002000c0c5400100341e2103015409449100408009400d4000810302540c0003102030b0015402d00440e200c01c4c400344802804000f000c0301c0210f081020003000718010b010383c1c2002d0f505003082030340c42c004543c64a4104070004499180850301142c0071601d074108080300d82400d000c0500201002c10342d4050003400c05000201c01540301410301e041085d40b0740040c4541e61028119801001c40d982d01951054641c8032091b00c4040d03240c02d001a140c0044070004014105204131446012040452040181005034003861980002d26407041c01d80140b1011080200c90300c00c017118041052195040094102800480d070b8890750301c24019645000c5003001141c0e000304400e03070005034404000030104540d1410304c2d50080550190040244007454082c0c00081a0314044004c5000b08948410340d95203503030880c00d038882140c035410001014820117403000034080c0a160441c214900381c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 858101025 1250 858099775 858099797
    0xc0207120f0206032d04030905190f06020706031109030601270c03020904150f15031e060521030a0c02060c060a02090f030703050a02010c05070e090a031103210601 72
    0x90090f4006a40b11060407080030203e84040c05d100208030052006004120382c145032a0f203014000605a126841c0125034148030b4610710f40810310b41c0c00c003801c1510141417440d51146c000943da03403202c4c0140d9011a24040004980000441c1a51507195000300180003c1e0308002c03110388100748010155180701c07550603018002015030f008401c40e00380f07030340c0d0f00688404142041005071007180d030b081c1640600c0e4181c28840e1501d440c00310010340380803030307a40e8909080e100303030480040600034054403048582c1300c960b10041030076411400440e10b00b2503070780e407202411014190030300800c45200d40e941d62041206000085c00755072400b018030300061400382440441003601d410944100c03113032024658000786815a5191440008000c1c1d202903004007022421690b48541c2e6603481b4501034103010058400d04100141000384d034010301200440d4241d00c2c1840061079940349940c0b00b007140411150005645401c1c400000c1c0d035400410003004004000a8068107041d084004c6c01080c104082c1c0148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 858102275 1250 858101025 858101029
    0x11032d07240501060e030a06050c161208060a0b03130213140f281814150c090f12010b031204090c05040e0406020903011e0504110102010c0207120f02 66
    0x700764625880201100081920890342085a0701604443c061114003000000c00307031000141085820390007080055642c4447d02c50116a000c0d0600b080c6484000b1103c0d041041400d6501d561341c48241e4613100307210b07141c02080010744503040c003807402600400c2c00000c030103030010020590002d00292030004030801900b1018243e40b182d00003511158280b0007803140c2401e90180075903100340680209012485a01d0f03814503620a000703050ba07a025280c09100b01400041c1d038111000d541d00415a9588010902119881d905200c510f440b40070310540000300c000c2c0001044135008200103014148442c00341c810404900083c00e000b01c03c566a840c9548266101042039031001d501003529a03443e14a00745000702610b0faa154001c08120041c1b00c100960700840e00f0706c4e070b04260700041c05621200e400000c0381c0105054060800840000c0750b070a1644020f81d4802c501a5001c1c004419401801c080160300b658450103548005900c12641086104c0c402c003415030201303210f504016031140700360300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 858103525 1250 858102275 858102293
    0x90f0602070602030f06060a020d05031f060f121b05070f060204060309110d05030405060c0c04050a020d0e011413050118050115210b1e090d11032d07 66
    0x421540b0560000c240b0203c103803e408401d6100070b003218228074003d64044000d403503585c0c0d11245018000c3c0400030450341105002c45084a1a10111250300a0354070003008044185020206010600309654404da2401a000e540d10020425490364000d0342501d604442a81c8280000d5031111004038401c0d00050050005100502495170045a1001203040003880d0340c3d08050b256100d0b41842c055140020301c0030094508641007101c0003030b22044512040b50818142c0c407ea80d80c440e16003020441c0451840d8040c01180310410f0f000c00064140103405400c80d04843c051402d01035080c000560409080c003030084105105400214000000a404003640d510300e201c100c8030750b5115550310151f061440c1408c0c004004207008803200401c0c03941c1c100a0b4090220014000740c00b4074000503036042c2c00c01040400b45510341c016108515007031110544a40d5807040c18000604603202c1c0c4281040b0000680740c0c002d403440c00401e450208403404100580105d40700c50103010090ac15240480d00d210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 858104775 1250 858103525 858103537
    0x3170a0b0603180a0f12200606060c120406081e040f29100801270303090807121d062a19030305010810050c090f1903050f100e10090f0602 61
    0x10042030202a6100140000a001d03660351070081547c038a40c4031a4800190b41500304800740c44c01e81d41c0f40c2515102c142440d0100c0403040396070b4000100091441d9001110911070324103a0090b40002c00c0d0700b41c5480359641c1c151806002002d007081c613500400e4403100744403166055087e50400001840404a51007101107c0780740110180080402007280c0c203000b5195800f248210350300d00b080c0c0c19040050f4140c1590341c0907040540c1c03602c807a010002e940089440c0c560700142030b1244034002d4039004002c0741c00c650320591a1841c0e16000800ea04120080e1101040c030300e07102e41008084180b01500c3c090020704e2100e01ca10a04030000d01041d0346148500700d00d07001e640c1c00310713040d0b0402c000a0301e07105c1e090340c041c03100e1490141000044040300040da0401b0300100e50444100c10000300080e04040c4403c0f00e40b40c131070100319001080240006006519000100c15500488a003010450403504004021640c0d0341103c10064505003480e4010100c0354452206030007170080716120340c000c0f078004c0303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 858106025 1250 858104775 858104783
    0x200a0909030c060e03040812161a040501060609080a140102040906030b070806012d170106020307050c030d05030105092d0a1406060d020c0a020d03170a0b0603180a0f 73
    0x868042c2806500e0081c002d4540c9040004c41c40c00d0b01e0107020030341d5896408080c040c80440422110352400002503601000d5410a121140a440709684c040c0410707401c0d00c1c112141d40c41c1c85000200503024009010840d604100a01842c03500740d12501945d0041e80b00c2c0f0300865508100c08100441588112005180140c000364850b00d00b0a0002d0403080c000740c507860602058000d20f400700092440c81090203c4611003c15542d40c1802c2c040e1a07103180d0491140c41031a0b50030020a1160f400405404082e01501c1102c0310800c01c1c0e0141610b558a03105064005002007005214500301405100d8110001500003901507100d85580042c10701a0340c0c8800e00c0e10501c4040c00100798035030041641c6102c070040203507018240400020b83c50310070030364400c201c280c000c2380ac4080c0310f406100d9040400d402502c2c000c2868994078004256504461080c0c001300c40010208456060707904c02c00306100c00181c0b10a01d940c4412188403011940108180b03a1481600c41c100000b848408001c4146881 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 858107275 1250 858106025 858106037
    0x5040b03070531050402150d0b0904051c03110f1308070b04030b060301050f0610110303090a2a090f060b1b010c03150e060a030812071803200a090903 66
    0x520100740b15060030880644110ba0400083c0000b51fa83c0c882041d80d49139808013175960b0b030b401524121015003c1a803000b6400100d0104205c2400b2010401000302840c5c0010800802002c42060301150781030402419608801c2c08601000c009620060200c10203402c0d1402006517a1205140b50480c1c0750809100781001280400410904001d0581c00c890110020b00140c40d2484c882d00c2c1230103004100324404e1171100390484209000f00c000450054860007602e07a01c1c506051034942d0751038203600c1210001c20400321091040b40c90440685000071140080d0392052811400394060900720b0300202003a542c2c0d80700003403056001e40050286010440c6510815030541080364211040c401305070303042c141444d0700f101c8840c15610480c0143c0d202a003201c0d1a80d15268003003050300019400c02481110009003104601041040c958441c1200350780d90002e040002201001000c41d600c8002c0c91000c0400700d40070043c3da02d0740700b05070006010709852440c83e640c01c080d8069541e0307000240c02180c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 858108525 1250 858107275 858107329
    0xc070b09030c04020301060807030504020a211a070c030c0302100207110a09020901050418180b010f080a17340611030f010506030a0e0a06060509060a0f05040b030705 73
    0x281400040d02c6640c0440e02141550704d0820050906a0018000410141d840e0002000c6546004200c00070740130081c10040ca01c1521060402c0350b816580f41a6500194100014008400c0016151003002e159450380c0c0351505550301030303c1520010f141241540544000840721134200c0c400780011034001d404d000c9401044500380180c40110f40c10180ba003034010403064030566003000c01c80d01210182242101d641d110880c107600280490501b00450000c505141c41c14030885044840c142d8252004022980381c2d5200800d40c2c40c0000c800c018500c2442044111400700500c000e806003a00b803583c10200d0003440740405c12020b048862285a00c06454014400d110325482514203840114207010b00e07609000c0401e0012102c140716081c4214000400201c104405802000c500d030200c1e422602000f1052624001400807401038500450141c000560640b48c0200c03002d088400014000700c2c0b00d42004107103c00350128409103074240c40b9071040000c43d03454000c011040801d284600380c1203a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 858109775 1250 858108525 858108529
    0x7030e151611030405060f0702030d0e03120405150c010b033412020f03070e010807090f021315090b280c030503060118090203070e030c041815020c070b09 68
    0x1070341506944042200c2c2a904055000c00002114160341040301d0168a40384521060003007442102c40094241c0242000103140641020480c402914118159107184029010032801d9008520904e5803204904e11954402690350000780702c02290b1400101e84210041c0c04a03141800d19550003a03140b40380094100001000024005490702108601c0d44452800d52643d840800000380a841200015100c09182e071b41000600010142c1462005d081c1da95140003944a8503244125a10f40b0700340045020500000d00c21103288070030b441001c940e51420a01c00c0403045089000750300600084500110b20403c001024012030001c0051070405201100100031510049180ca40c1c01d00103074030440e200182e00301c0181d0b0b920000a103042d81c0d403241d24000c056120b041c5030340223a01c52403000007403261039030707100c05040740b0301c031044d000c84090f144050140000c80b80c4141300c074081410f0103030482e4001000f000034070616009840c80513040204054440b400e104c041d074005465240001100500380c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 858111025 1250 858109775 858109801
    0xe01051312141c050f03091c0903061a220216080325170705070f0308040201090e0105030c090402030a050d32030711010906050709090513120807030e15 67
    0x12803010403c0d0b4016180d00c00180c03031401203002d802541c1201000260356507000f0800d245a481c100300403204917421502000c0d1070400316000c240c17171190401d80502d00054101202c0c058114021b411020b02101c00c4003c400082a1a80d490800702d80800c00d00101d52261185104210301500016a4031706000a000d1903e03040ca081c4001100e11000c01c01d41c0c42034120051050140d52a6512200c6542e00c40d0112850703c0348000040c00800c100f44500c1c14180d1010200384114400c0e01c070a01d48036203032020114180e0b801d00c5040c0d85031740400314144031400c0c1030000c44d0b001440034003154001410355440a0a02a48008403800102026480003222004448903605418a0310806880340f50820b00c01f201407000070991401c0c803045a00d005000b0f5025842a1802c2d5003006081050b41894800140600950b02c2105a85410100031079110010420a452031a0780030a001016421010f400e890400005122806041e610307440b141d44080c1c11700a40d02d003404410580c1d181c51030513080382a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 858112275 1250 858111025 858111043
    0x501020a11190528120f020c032b170a0b011407050601060c03050d060b04061d0303040303181715091b09060d2001020c030d0e0105131214 61
    0x20405489020801180c00424055900001000f262104d14611003494414461520000b050b079000800d08004086e8130110820340c0000366800c0d071781c01001c2001055550b0341d010800101c2c0c29400d01c44410368240f50070a210220a00d410040d40c50071200c41d940342c040508540d02854180c40e1860b40343d0541e84404001f4021a594240c02d0426445803242a035a5005000f61005c1c40701080c44c0e41300741406401541e0344046800c00901c4559156038501000c1d8009110380c0012402039100d80c1c11000c0340a80c1c1910740c0c0e034081d0081d03007820300d5034130129003510751800c5801781c80300120004910204802d00c1120060b000c04000c3c59060718000041503150340c000c02d034260540118041c034070405001c51050700402c100311114496901c9800c002080802200402010200c1c1b80d924502c2000384071203e0f00030000240c007541c201207210418941c0703501c04001c6000000700e800c17049802540c002c1001e44802011218000d070016120360300c054100004040a56242c8801040c0030281c0e10100f140b01c0b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 858113525 1250 858112275 858112303
    0x291c0c02030412020d060f051f1502060a050624040f170c01082d01030c06031e020a0516050a0c0f08100216061b02070914130507030501020a11 63
    0x102d01841d00c041194000b100000091007003100e4a68201407140603000b1480b40c030080c07501041107080c074804640c2c4c0311051103014140c8280280d4001504410060f0404103608290090609581c51010390300082c08010130f1258040a103401100d001000c9045105003420f05644540c0e07210308202010102540c6c603480f03d00018142c1344103009412004c42c44441082c000c0c20300b1040354460590304107504240c0820300a5201d01001e13000740300009500c40c3e0741202c1c00340d00801202a210a0304406940d40042d095400e403032520080b03c80030302240e00a01c0f254400349042402c0050680b412890040d1020341540c480e40030180381c03800c0c00b044143c00383c020405850212038040c03501c020305413078012540c004a00c9aa000ca9108000b4000000c11261194012410040c103819040e003003950003510701c0003600512070128042a841402c0c49503d2000c3d206540120480d84d5400c200c40408a2180302242da40c000c8a000000081007400170b81401130b0f082d101c80540002c01101c5070f1a001590611107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 858114775 1250 858113525 858113527
    0x109050717100b0f04050406091e1106030c0405310506040c17010519050603010e160c0b190f0c031a0406030803060f03073318291c0c0203 61
    0xf500d513030f00c5070516416240241d0b408281581c0d40c3c140300c0010030120101902088e018650a03c1d00d1014051803a003084c801e69541d000e00080c0002d10940b0b0004444d003180c1480104018070151a100480459400b441502c3e403013500d0b885c80540b440880310f02e00d0346040310b0703c1d2418810240b400c4c2c05010b406192600d094080220f00010b5074cc02944107110741802555000b0134000309406204003000034050261002e984c1f541d446c1c032603042c555000c8031065007094058010081407845034484048483d0410709100c0301c0e48a40a100c0d29017040302070808101c2e50f075549151240b800743e000700c8038a0100fa883c002580c0440d0301078503060342c038510b00d0540304a04d406400d200042200e41680d400c00d405540d9094112036410201e454040c19401403441001c41c20704004080341042d128480243c0d603190151039854031071400ba5055000f140d5048400e440703480046c44000e0303803040c41c0c4002c01c201c278450043d4002c0e86241001c0740c0c1e0116100340b4003140300341034000114203180a100d10401c80e1784015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 858116025 1250 858114775 858114791
    0x1f050703080c070302071802090409050601050306010512070303050a0507050115081c02060a090f1b0303030b060f160819120c02061915050402160c080c180603010905071710 76
    0x2e40703c441d903002d40c8145091f01180305601d048541c0c1900e41da0a0060020080120507003401552118240b03d11340c8680f24803c0041030508008050310b0304960384000030040c070342c01c580d020742d2660050843e2100f00441072040310041a800d0254040401c0c1c1c2c0710440380d115003070201031400c00d03481400780480c0d0030030249042c3c0c0e40d03540004c1544d440443c800c0d00248800880c607090343c1b0704407001d0001d0a080da01400251004031a80000c3c421640b00780c4040042440c0542440a5409102c1140d140d082c0c0621400c1041001d08065000e080d00c1103050b01d1500d200e0804200b00030904a10030000204004a12229140207202e51000444540010001c07890101d0700705180756401135481590a4441d2084820580710000800140c44010000c0d91591022100400142c440c090140c030f0f4002a03120024218002242419041714090507141d450540020045809036019284503010745d0780f1160341d8013282e0180210406800d01390f900413516030031154914a402c000585828410f0720701310270 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 858117275 1250 858116025 858116027
    0x60d0903050f031305210a081b1201230109031e061803080c121906030b010b09100e0f0d26090a150c060e0322090e03120c091f050703080c0703 63
    0x2622680c09891400c99178564427081190a60700b046000050202c5005c03c0e034580354461100130300d0603110301e0100131448034103103800001e021008500c03042c08180100802d00218004115101c0226425074880d1601c56296980400700c0d8003400d000f13202c040d0f0145082c0101680200e82d1500b2010780e968080c103000640741e603403c4000010f4184002c2803040740100e94081c1080e04000300860300141c582c0c03a04d60351001c40030503d0b8072041d1228031806000f4544030119002d0501d120110700c01404c0b0794a030100c101c0521000c444030100c1503415410f075000700d44032540d411003800788451206218985441281c400e100c4a4690f51f0002d005034511402c0070305c11207a12468403035506410581c0416a43e40e1414040d040d4130511440d107154002c03607419401c0b1150391204440c01c4401400d020083c2c500d9141c40543c0740d002d141a411130744020304001c40e1505604030081c03d0024070007042800c0840c56991030284c2d1014520303209000c54400b2441c001410f070403099039903122030116021032a1500c0c65078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 858118525 1250 858117275 858117277
    0x2030a090f15050c0a12030504110d11060c070302060d09031e0219030e041406090a110403080c070f030b0402031905030a3504050f010b060d0903050f03130521 70
    0xc50b100402c100412082c000c00790400021030041e4000490804141d0b039140002d0182c0412a0b0a50781001d01c845c8000700c50802e80c200749652078003c00b019407102d04020401c100c43e4072042e1540124401c43c400440980d503040001d10310f001c3e68040000b0802c0316850094a441c642c0201d0703d00b01180f80d0303821144540c0108183d820039108034161900e004070b0303140c1a50380421017491150028a41200c0b4980d0110310500e850281e0300071101c2154694940c181d280541300c1d01c1004600e81001403004000050719a0302030a81d200400050320600741d11580c41803044030b0305c2e030b005641c070511f403400780015410148004d40321240340c0316241040c08802c0c1c440640d00e220760011a002c2180040100c00070258a001151072248020b406070480c6542880c0070329180c0b41a00c0c20784290003035400d00000c0030014819080880c20203410700e800d007442c1c1006032000300f1802c501030382403080812410152846030030003103100e00d20404c81e0108100050429a140500c1c1d80e420b0200020708001081d14941400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 858119775 1250 858118525 858118559
    0x90105010e010207120f120206041506122402030f16020307110108040203210903010f0501050a180b0306180606040b131d030a031d06060a1404150602030a090f 70
    0x45c2e810801d004051801030200da00038003000c4c1c2046c03102c0c1c0320034200c80d0340403035600c1c02140125891010700d4203c100c0c50045139018800d840d03030b440d1410111030004545082c00d4404040c0c022035044030030702d960001002e07a401101d0880203420b01100300f000800850345820180d60f000e200440c108107059071803400c03001039601c060b4144803030800041d0440d9000c200c0002c482050300080401c8020041f8121400d800400341e05100303508142c1501501c1b10548074080c102c1f80010516240d442c075000002c0200a000c898040d82c860301c030901d04819880c00c0201074005c001480e404202c00309501511414000090404ca2207142012440921907031350007403206c1d00141d4100009004050158085254903500d00c1443c040d001c003040b1103040507056407109840b44105050360300303032901d40d1800a85408d41124119400b0041120030700100c09020821800c405000d00700003034010032000702070000100c81e84881d0041e0300000d035030030103e548003020500030910001100d2285044c4104400b60301415 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 858121025 1250 858119775 858119789
    0xc0807050c0c130623030a020d0305041208041503020a0804080a020109051b0306090708121305030312011401030b0612090316080c01061211300309090105010e010207 73
    0x1280c080c507007003414000e40c103850000a01d040d0340340c2200003882010b0900c5201d842c144040003a075860f5070001403c0091074001c001000b805540d0610f80c00c200c40d10b0f03c0701d041901005014030000c190602d91070240e0424074001e04110791101d280c650790303c00c0e0044000108040500602403011060782102c00282c2055002c000b07103803a1118070070202c2c010404803802030160b100d100310904982842d017400c800156002e5040c0c03140b07030359110161a40c2e4039440c0700c2c55176030341e10080051003100c41180c040d010800e01504003030500756a5100107451908102e501103a900d0100004009801513000b103d25000b100303003424002141e8a60010b103c5010f2140d0034028400c1000000300c00c01c4050044500003500b59800c890010240d08004800340c200010600c0290303e052404103003101040c5c030740e040841e030041203001c0b00d00000081c0441e4038500c1048001244c1c400401d40401038a544a250b0a06150801107440d040004100007071640182d02803030503c001c00403801c070b10781d0307010803084240c03201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 858122275 1250 858121025 858121027
    0x10e030a0201080901020d0606030f23190908070b0702010e120901180b0a0504090f15051e031f11070c061110020a030e010b0a180f020c030406031506030c080705 71
    0x40403085406885400c0c1b03c3c0358120314213030380454050341540c498408546840030821125900e2415125a0708070320f0322a490710441c500000cdc04500326040750359003c40202101291050369030380c071100c8036040750400703c42e00d4400348200b0411030750900c1001c600c408100e005156000301319000c11410300c030b105e0b4014104030034404030000c0c00f4004020701c4d0061009c0005e5903501c070303001c80707006103907030024061400d07801e0a0055607812402c4034001d0041d0a480f4499040b500c515200c1000304402d07004540000c0c241a161031071115079014014a150250f988065522112000c4042c400b140ca94400c4805040018444a00030901100c44d0806a0788a81400d0700b01c0c600d05070400b80740c25000310804503401d0000078110241a4190400800884038900900902009200704078040e981d80c0039500c0369400080940701340b908107401581820300020ba00620300451450102c1c01d40c4e215030041804030785c4a1030000c0b004541c81074184010700f03c9140c00c016031109a400101b01c000e0180c103800c00c0101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 858123525 1250 858122275 858122281
    0x40e0a081c090f0b010509070212091c050601090213060201140a090c1e0f0b03091b04020904021b0c1f031a0d050d1d0d0f06023006010e030a020108 65
    0x242540c001540c0030f40115104290b0641440d00b40b1031840300b40100c90144401c40042080c850002070b40c0c80d24098207c810f01e040040d900144120714007603205800d4808404000c40000c5141844024040d00c4402d901680d201c98112400580d00141c0d8005000c680c540b8000207541350344490035070382004010307070b003c200c448042c03c00b0324844110390001c001038460348980300003c00c00f6161000440c1d44a03400f10ba43c0e107658992105582c00200c1d2050709c50b8010006000004c4000e82c0089c8200c03900510040c01c116100020608a030404031601080d0003480c1e1340080c91807400c01c11000e401d40d045034901c2091082c9003203a000300114007510b40c141038485203001c201c1c4504070855030340c0700d0014142c83d01700295420400c0c1e9a036003104006010444101d2182e290803484800d03003043c01c00c064000c080844165a1f031415004800c0000c0e1040743c0e0034070042c01c4c40800806c04400c5c11a4492101c07202c00e64020368049007503c05041c80f41880000b42020a00740c4011680d40b0105809081051280e9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 858124775 1250 858123525 858123577
    0x2030426060c1801030b180705041a0405030c090403200c06300112030e0d14030a0201060e25030e0f0109030905030609070b0706140403050702040e0a08 67
    0x404000c8401458040c8108000500d61401d01818910058200c2070a0f109003960042d400c03206000070f2280c021169030304c401851700c3d070420001c1d00190103141103481d241d511840800f8110f10b41003540003c0c40002010040ca01c1c003084801140c60381103d84406900381690041d006040f408101004c82c2185aa245002d00b414402d001d410a405454a0b58880c0b1201d20390001d14101203c125014165005c10441ea0401b03074142d5060740c444e10510355a62095480c1915906c5000242d107600200342c41400002400102011407021445002581c071260410b002a096a120741c00034103203d00040c0410070600300c103140312520b10408400206007081ca020301280a40280ba035610004d2023504a44c540308001584040030b210700a44c1e9101c01d454a075800c041d21a0400c0d04d05a5896000040500910700000020b00c01c80740300f0007000800c3c24001c18914008202158140d000c034002040000550610b40200c0410b84d0036a405080d00904a0b130b07131082c05d802441180b003034103046441d46003421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 858126025 1250 858124775 858124829
    0x30e281104050708040219140f030708070326030405150702030d05010e070e15030106080c0d0f0c140a020601061b02040509011a03030a080705030618070206061c0201020304 76
    0x25102500510103440c00f07240c090325810040d078040303001d92000984a05002c150602c3c29003a40c1d4a403e0002c031081d5428100542d44542401e6541d0600405c0000950840c04021840c001c2d071240c007003911070207000c84809244149000c1901d450100400070003000660205900308803207030300c403c1c01405844803c0c0480c59401003680b4160420f103000004110b0641c44d1010074800e80c101e84e0b41002e084202d400784481c1c003203040c1801c9900502880140600c07030007826129031041240381c1e042c1c00c100d407030020350003512206202601e0040d51899034401c82ca0f8008403191030300e42148003080ca42100300f41d000f50b848a05102d082c0400640b040c0e004600007088210100c4150000c1041c491801c200000500070000540e10032800d8058600b18040e909011040e00c6032801c00d0f4555586564400724103850540c8010981d0b94400f03000106011003d0504a2103405403540b580105140d00e803102c20301c920b003543c2d030101c1c111032034541c800040181e030b0020841e003c0d50154103c464202602841310644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 858127275 1250 858126025 858126053
    0x4060c18060e060f0d230a06140d03030b0d0c0e06060301030206030403230a020f1908030109050a020708030426180103020f12040f11060f030c03040201020c0a080d030e28 75
    0x1194100b54245803200c49415803e40390481460003141c60b034842c0c1c0704840c100e81c001d200f41440e00729140d0803506242b800180c084000e0b4020705001c40c1e859698030006003803120903101150709510140040c4102c45986202c594012416a0b110386154150780008400d80001032004081142820321380500300c01c140c90118000b842180001d0302c40003c20f60207503d6901c80c40c4000320b5403003000c84040303421903d0380070390680a8221045525507428616030001030a002001503460907000c1012500240000008511481c001d83c0302d5195068660541e0042d129044801c816481040c06a200a00d00408595290a00074240103a4560210b50b007509140140002e03903080b40300140411003072045242102c0303185841808a1440303e600d080c2002964080d03803034840c1074050f0a01c0080e8039003480b0300003140c000d070050040f10001c1c5528000034030341c0c02c4030340c1049400d5000400c800401d150140251980103092001038410180701d10750700c60000c0e00420705460101034100a250500c1103906601c22 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 858128525 1250 858127275 858127297
    0x201031d0d0c200f06090d0c0f0e090d140f120a0203060f0306090601120c0803070c0e0117070627090b01020d0c021806010c050d05090a06050903060402090a0209060304060c18060e060f 81
    0x1202540c2c502450130b80e00c1d554412080da00d904030000800c0c007100802d41803030440cc943c42d01c9005107401304212000b504401440700c0369600030000301c00780b0120004000c2c406c001301080580d803440d100381807250f0380a01c801013502a41c028010300c07400707240200750b030f83c1500d5004c8070552300320340c00c2c0c2840821058203030301c582c1181c00000386200c00c2c05a030042030010b80f011500c0c0015a81da0350450341d0700109071081441001d0b08040741c14450984031b05000c0001043d2241e650111080700b601c0c601d00020b10f540030312983c658801580f40e0a5806210030000c5019074144a105080140c003c1070060b40002d910145030602100040c0740c90b8000c0142e080595041008c6840c4440750a40c00350443e0b10501d251072003840c8203100000c0e118403d1b41220031400d00034000d05503030303125a030034042c1000000d00164601e5400344001d2010f41c580d40041c2d4030440c051540406d401080c0b05020b8281a0011040702c0551460041030204642150500850701000d4030380990344c40d1801001c81e020700508640d08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 858129775 1250 858128525 858128543
    0x90a05061216030b18040507050d030c1502040504020a0c0506060406030203070e0606120a0608062d0415090501020913200c070306180201031103070c0201031d0d0c200f06090d 77
    0x4440700b080c070171481e88185d100c1c108a91b1304176210020801550001d103001000607098081200c00105000c05a142c000134003a40903041507150b0000a0690300f04075443c0000801050000b42440f004100a58004005540c1045500e0454002c42e4581e815401610001f0000b41c0100c4c56076100d05040714440200c01000c500340b41002d50719840608072911808109124100c0411070000e20400d6a1800c460709900d41c07181d0203080000d007241d40d40d000300141d607400c841c0c40102017000c40c14058404ea0900ca51b00060380c42d42d0750700c00c00c403420f1130508119280b00d00e442c1c402c49002c501141c90441581c01044810789a800314204a807a103009500300401d12410100d4241e905440b0038904103516200342c03000d020341c0f00501c1b031404c0e860004580940005034a0307d000c20155020703034400a102c0110503054182216108125850400c2e0600030078001001e141400e0140100d000b140c3c1809040754100e07100f81120f20740010394210308040a944980e8000507000c0895a07402d41628002e03601c02111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 858131025 1250 858129775 858129799
    0x150e010b0c07080303160813050609030901030510030308061e040f0507030c02060609070c03050c0613050d020105010e191e020a0306120206070311071802090a05061216030b 76
    0x400000c1d00940e003100040d1203002404500c041011082d42c5c03080040c90042000d90685a004584200c40a8072242499001154040100307001b41700051103005c5802c0203580e160b80d85000101250001056110444043c6106100103a80502000d070400c01c100c0f403040e610f031a2411420031b20811a584603500c00d00d80807521012080c00d410107031040d000354170100b04142d80c88400343c1c2c5504d41265480e9112001c04d001410003400b40800c900c8941c02450500d0420511039200d500d0001d0540e1001140d484400d404400c00c4400c00151109850920080c0001d5240800c1c0c2c01100c54060954188041da6511000300207001d9406040c90910300c242042c20b02142c07918441c0254809000040024104040403500a6012240700340c1e8643c05080b0034500402904c007102c1045041d0382d00c03c0e25024104000170101c1d900d505845001c0c030111401a610284d1004118031144554081c3d0b00030002442450703141500707989034592069a1080c1e45150a00003142140201651003640b0fa102c5016108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 858132275 1250 858131025 858131039
    0x503240103110a08190b0705031e090c0423010f0b031911031003020f0d080904020f092701060f0e0409080c0a06020c01060807150f031d0102180a05060d150e01 70
    0xf110305c030b500510112901f07840d407180484aa11013201c500121403400c0751505640a0400300003a8003c1250007502c05041085001078242c41000754080f0603840350ba100002514049009180149100210750940d00c0c5885504161800014410041c080b06840c14084449454003c1101a01c03c6c0b41456030b6454006ca0075050000140000c0e80a040135a8042401d810484903030041d0035041080f0301d041c00304074010072000c1e5210710740c48206404140701e40d0800d900e9203404100f001280f000c940c2101d8201565240c407409059016800300040400c004224540180e205580000f00b924046055500d80c24240c0b0389118015492020784500034948040c0702043d400b42c441100c0c040300a01c02c103540c03021056901ea6090240c8070543c10000d80500500703008003200088981541804a0080c0d28506c80391a030050498800d5010b940026282042e0900c2d030f1111000c01c07100301d84134808035080c030000c03c0e00b500880c40c19410b19961b8104400c005603808043c030004102000420300c480d80c440389 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 858133525 1250 858132275 858132313
    0x40525020c130c120b0a0308090d050d0f0305070f1403100308040b0d0608010c2708060f040209061e0d061d03073c03031b08010503240103110a08 64
    0x2076000040105130300c9440d20020740107601800300d00803c900300f0681161545105940b200798042d03405406182d852002030000d09c500111402c0d04c0c2c48402d2000404d1202500f5100c0040141c401c100c42d5a40d02e0b00010380004e04c1038122107003c01c0c8540c5a9482e0050311010f282c3c0d0307400250a51801043c00240c0d0b070080c03401400c2d880302000013400419a01d0407007030301343e507408210000440d800c100c0a01204610b1540b203d10f40da0501c4480a4541d503034a103450402400756404454190b542c0200415810321b680860781204003a0ba880240258550814188404501d402403080c03800a8055090000c41e070001d4090014003001c3c403400500904c0c50943d43c1d840414202c8002008400200400ba01068005414080c68804040400314030003004810081a4000c505060b40c0e03480010310904242d000350f02da1003040d21403e40550410f02090300e425003c0c0d000c294100c034a0080e4000c0442c13044030043c1103170750003181e56105c0c0c40075500059120303000b60064401d5100f201306507400041024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 858134775 1250 858133525 858133541
    0x3081b010e1b03070e131e08031519060810031b03050706020714010e0411270d050a12020c060d05010906120f240e0a02040b040525020c13 61
    0xd03682d0641101c800905882e06214441e584019030050002206000803424098501b8030070b0400360050307007038a15a44440c0300c1c10141516148000700800091050701c200c04040a002100c850066910720146100c0c000c216000d54401c1200c03c4012664041c0303a480080b019591110455850900a044484802d180c1e0301c002d581c00e103d040e800180341c500200d8040140c0b80850440c1e01c50b8000c1c3d40055451400156190350002d41e02d96941d0704442c4910003030840700148000160b45191040e000c984103407011034000d44600c0c4002c0e01e00c00024000280c003942c9942c402a10358000361090800e90034112054500c070f0300480001119134524403180d000c1030590f03c26103020000b464a45600807100403050000802c86002068000301040702e00041d000444c2d51042070343d02003081d0321105005c1da02c2070381d2419000d6004120760011032915000da0303840010261030801841c0b400d10510f590010b036152610125945103050400014801cac040d070f00c2c080b1005808144580c000aa0f54001080d0754 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 858136025 1250 858134775 858134803
    0x20607171b0307060f023f09010b1003020f0a080415140a0510060509061b0102040902090a15050306060703021c0507050c090609070513030c03050c2803081b010e 71
    0x109100442d0100d182c400e0321f60400c14040079800101c0320b07012030a6002c040340c2ca90050710208441071031a5036100d6182c0d41c0b0030080b80001085007800d00307042c004a140c0f0102c00d401858010f000c4a9005464002550f00c0320109180099260304c8500f0144030002c0700701003003014ac4c1d0070911020700f82000c1117001030141007044000c100030740d42d00c00010b1100e80f50740503540c0083c0040001c01c00764a440c001803c9039403d16200b40c0b0804081e071002c01e0880c0d2066114254030743d00410b180c4503034503100510750700500010304581d42d0003c41c88401084e1748001007105106040106000c0c051510802c01c201d401c0c0c001040d480301c240b034210400b8001d0b810100e0115114800c0034160351060420b409160701820010380140e8840c1c03100c000130b0300e440d0850812011108803005d400000300c0c00b0b0140380c030029070041024000c1da2002c601440280c20303626220b2001c003104030040e410a0801880741404070f1340c00a100a8485140783c0030b0b00503030140c20411446a42c2004444604417201085075850703a00a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 858137275 1250 858136025 858136031
    0x2070308130f030309020402090406060207050120030703030e19031d100815010c1707030e0a030c0510050f0712020606010c0b220b040803010501030501050409020607171b030706 78
    0x5401e4070080071001c0c038000400c0141c542c10aa00064001c1d006a81c10504c0100054200b20703e20001c80e0171200780764007090041c0d001010820841d6041002c0c107034514280100381903981d00c46140310f6641c0c812800000d00305665045003007030a25041c41800709641c3c00c440e501d2900580c2e030500402d0f42d030700519103508003001d00d40c42d83c06500d8a14624070380784005441d24010741c2d44164030403190038504071079103041c0400360608600041242450311031707214a0103075042c0c0303a11103410003c041c81ca052048078060600c0038002d05c085688180038074100c4901b200d868242ea1010034089031719004d61000d6130010b107000b01341d50040220b030029815445a142d401c507090380c1d4802004540c2400c41c00000f800340c42112004c20121001400400d102920400002031074a445656915041e8400c841c181c4034140c001c801404903603403500070940180021181030000c48d0b96030700000c942d40b00c0c201d4010001c1721030603400c14643c001a02520110301c007403013240c07010750540400691a9402088226a1549 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 858138525 1250 858137275 858137281
    0x810110301030f020d061b181403030409020a120c030b01020f061512030906070b0a06060c17031003060f06050405010509010305031c0207060f090308100b03062b050102070308 77
    0x900401981e040301d42003804103c061015070248031100904400540b801521160701c0303800115003040c411105010303a92030351080f940b1500000b025002030b401c402c0c4080c00301680e420442d80c0000c20344060b10341c034200041c0d5403910f008060f261401402003010741c4d182001107138403003070713801d40d014001182003a0243c0e07200c45d031a100c40544404080302c19083d0b00c01d059140f4a103038182501e42c0e1900305d0070b8204882c0707070850724000114075401c2410704a0701075141e2000c0010306105030050b900140034034240f06442c25620758400c0c407440e0855055858084000c00000d050b903140b100394034000d541020b020004901030b48040c001800b046d020b40f80c021424a40000341508190140300c0c1244d4110001e941400f1890581c220854020f8501c007020580078419100814454030070b0341e45000302da200c0003454850615010b4240007000b00040801c00320b40350100005800c08040340e80c0311400700c3e1703000c940d1500d07030700f00a0b00901d001c040e004a000c4010610420028154000c1007014040d8403001d44680d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 858139775 1250 858138525 858138551
    0xb04200414010602011b0f2016180507020307120c1505150604032307030b01080a0b0109140403180b0304080c0609070b0a05070f0b0a060e10030b010e0402190810 71
    0x1000454024000075801e1241121151040300f1603007250460800b00c070240d40d9081e911714505512002c40d0342401400381c9c4100602e51505100d0500c2c140480001c1c8154501a50069100c0c0504000580151280e11500200d98807480c0211080e65206801c3d110484a4040c2c00000300b80490700d164a5601150789100c1c81d00e07182c8162000c407648030100c24001d0340d4420810140d0121031000300078500c039099002c030024130310f944028007906130311000f000070a40c0380c240000c1000041c2d001c0c14180d0f180400402e8407400e03030810f01d03a01c079406040000c00c001c04001440141c1e005548507017661000170083c40200140c81000304048444a011102d494031500000c1c0e840f001d152280100d681c07005c0000b03c100600032009448064041c00c980075484129440e0425040703011a01c00315500e90740c0304140224540004000d80010343c00c6402285141513641e40e02003203a040c05200718500c2d5800c002404c6544181c10001e05840c0b480c1c503000d042d079035110242e6440d0b070703450142c240d0142000c0301e0600d42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 858141025 1250 858139775 858139811
    0x5190e010b03070512070506070503090108010e0415090311030a020c0a05010801050d1401091a09010f020918060d080a21020f19020705031902090c03040b0420041401060201 76
    0x709802409070680510b4402001442034403034104020030302440200040301ea41c1c1c0b001410180d4000c10146990b40c1c0600d000420780c03601600003200c08140d0780c040c0800708031080c4030f4904880f011200024034800314101a910070440d00e60322040d0348030000d151216241d0119a0305c030200c1c01902d002440b941c6401c01914200824041c031794102444d8a40c00d0007080d010b16110703082c3c0e02140000100a0300549a0401c0c41e00c0d01d218914200c503c220501c2042e9409101d12841071603400c100b1404c041503100002e10b000c003500102c0e10010344240118560b584e0700243c44201d40c1e40002940d0b961400c0c5d80014001340004006240280b40348244d0981c00201c900840b100c044c02040304034a40310608400c000c110032648865811480b0303006000c40d40c0d44040020814903c2d698105041903542d40c41044002c441c014401001410300b4014000011403924049411030340c840c0510780010f0450384802210790241c1d0616074000d00f4144200702c45444090243d058038001da0080c4032442c240921940a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 858142275 1250 858141025 858141041
    0x17060c030c070f0c05131e05151e040603050c0307060507031713020d0302031b011b140c06010303120f02120606090109080f06010f15020709090206040905190e01 71
    0x450034200b06040c000b4028400582c2080c0c0319400700c0c00225104c9021660500301c0403103d810442e036405044000b01c0b03d4841240711008000000d101a21b40a04441040d0180d006940c2c061040c0c4245440740070544035000604a5001c0c1c002c0001c0359480c10115514440121078600a000c0c0540c0412424803910869911a0301502c0d9008940183d480307800b03091a005200c8498074075101010f60059858250310030f1118043d80c020b40c1ca8840c8440380110740b15078850f0700280b5030b1401103040d480b440719035644003019001742013a10001403550050021071090708601540c0c2e004100c0044101a0040c40c2d800380c0081041e000c00c082d600d51010f250480c820005421100c082d5a8006041481d00380c0c0200508a01858074036142640d41e03002514105000088540c20b8001200511035207015106410003420070180100950100030320294a620950041642d07131a201d007004015529207604072402000045810031092503e15502018101c4c0390106240d6141000180c8089201c14026010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 858143525 1250 858142275 858142291
    0x418021807140f0d05040501061406040e0f061906050c01110418090503090436030f030905010605150a180506181309030207030b0f071e140417060c03 66
    0x60155070902d0403010f40c22581810b890b1000130050011100b51600070140910720586c00804d0042c00c00d0346062418070002c44041c040c240030f04c0100800701c86c1e141c00a070002d600300c0d0b501c03009451f0400442c07560481401000d10707007044c1031000211181e00800400780f0ba81e106000304030396002491740e4802c40c4154400d07000c1e020022000900f0843c000c0c2d0000c060244502c3c00c407458900a50082801e854005854680c0061400000441c608a0b42a108480e00c200001e140400c41d15a0f03018001c040b107070f00c0303c10802d0380d90404942000300c250702007009000300800d8450345107003040081a00368421426040064000c1c10340381c0070340460400340020351b440203010310704044111042c22190400351400940c01014029a28114a124461902414003d5000c3c8c2546411820f00c20103540b40076100d100082040c008111400d80e11050704101c0107075401ea0204840440304c0708850300b00e440084a400b007070000400081c040362000e0310400d0782c4280301c00d031002076a0710040340d6030601041307403010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 858144775 1250 858143525 858143537
    0x20a05040e011d030d050105060a231e0d0b0d0b07031a040f0b0306100510080c071a060a080312130804080102030f240102070b0d02090418021807 64
    0x8491494160000e4190040101c000203030b2514280e0701201d4140ca1030030b04000f6804c00900c040e40340200c3d001d803e01414043e10424500244c80c50010308000980680c1c1c0d980e500142b00851641e9480d004131448140a110094100403050510403010f80c44581201421450020740300454103240c0003070441d482d0400504c028aa5a09405401600ea0205400d240c840581d15102d1190340381d21980d1028110f92200240c442400c3c0180351807c0302c09004041d802e94843e0301003003aa42d03040d0b604c1c404040d20b858650310548403403206c000c250141d10b60007000c10780c0b0200065041c0c40300491042c492201214940d600a41e00c2e070960751644a21020681030000b410b00240082e40d440c900d61103024483d03031312203181a60f40c0402c50f00b21f0308184d800c02c4c00105e00703078144596180703021807144054031154005d00f00743c201c1c400041d58403a464410038070003590204400c0b4036112181d06840040902800a01c0b500d008051009080369040078120300c00c08c00303141c0e103045101941d4040391082e02c1c9074482c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 858146025 1250 858144775 858144779
    0x7031a0f060102060412050c120c030408010c0801140f0f03030a170106030614060a020708030412060b0a05030316020a090c0903060614221107031e0503060d080306030a02060f0301030b13020a 84
    0x112516400899423001510072003020300202e0040d00010305203a10308002842d01e8508101c545425180c40c0060641040408001484000c1c620344118014040440b20545821000700105a4080d51080c50340d905003c08103841d41542e4001e41d14400d1190703030301c0181440780c1e261078003541210924065035981c404d407500c043c0c055062000042000000b24011101d1882d90703040038a1031507005800105442985d14404420401e85000724445a5030843c0c0c60305a69042501081d900e02a140c95000101d1101079060190345920420001a081180d018050319440940250400a0501c0112401ca11f07042000400207821001012100401010162039051307600c84161607802200d44040d0255440402c0442c110707882c4000c2805500c01d0700c44082028090170a055a0300d2110904014024200100300e07072070b52113040b007000080e40150ad840e100c0e00d034500400c3c548140400d0003900508009200e80710003020501540c1201d20400c010035207660313110107900380900200e4000b5009418036400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 858147275 1250 858146025 858146027
    0x20706030c35040818010f0e0105030a110406110f062703221521110702100c15060602030301050603090102091534120207031a0f060102060412 63
    0x40200900b1220082074520190480d407004107040569040310f81c49000540000310034041c04100c00e91036000d0a14400107a102d00740505400c0101020700e0412500200080c840c030600c0d80a94050860500d486072950307103c54014000d0801c504c1d4009051041c5003444220450005074648140c42500501134040d55480628045049402c07540265002c18400003100d059900e0a1040300050441e134004910326107101d0441401d1800b1440081042c0c00000070014006010945031744c00d0700c1c0728000b4a40f003800180e0341141c080d508000350b00901302d84c04502408c0d8000d03d401c20007800f80c0242001c40c40030011a40865001d403150304d0140c0c00900c010045841c04002540e8000860400549042101030008801c07502c00780758944408804920007070f4050720011080300c0d05e0752403411454458185c101c2c0c409940300741c0000410b84480c11481041c818400d10140d0000c59100c503400d00303910911a00401094000c42d6844440351801000130919840003c03640e01035504035035180751001c01048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 858148525 1250 858147275 858147317
    0x4030812042915042a140d06090501150c1131050901020f0f090103060f060909051b180f060412060e011e09020a0b0403080901020706030c 61
    0xc195010302ca0aa4075410301448095000615507088120004510700460108019601807414501861400400029007111000382c455140c1449003182050001d294040310008440e03007400d0100ca1002c20101400343c129002801504c010312000c0c4a10381e00c0e031130328101640c0c040c5007000000300000a071a01051a061205001001c05050b80444004a24040404c4003001180010918600402200c608458031500c1c1d0052201e8009510f00500c0003c051814000c440540d144180001403846040c0c1c000d9014200500c898901000d600d07a860744050240d412500c00c0b8402c00e03041c04001030490034450641c84181c41d40b00d044504008a8071000707062044d00c035506c25042009803184400c41d0b039802c0702600040280c3c0c21040b006c183c5a10301007090301e00c468031442d41d0381e0405c0c400325170340340410001140007010b901000461040c0c1e800040c0160724a0341c8117100304240010040b0901108900600340c0340020780880d400305685090440440b020b02c410000010041141e82c14003040c000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 858149775 1250 858148525 858148531
    0x909031e0f0d0e0a050f0d020c1909151802030402100507060609020c0d02150402010804140c0919140c180a05120303040309060f1205191508010f0204030812 69
    0x214100d07003402e290241030300484a21091401469201c43d6400d020003008104028048800c8006000c01c00401c240196482040c114070910407103403401c8600041b40c804490030020180c5480a00c00c2c9050b40302494070030061805683d00c0c2c0d190501600c02024224000c40740200c0c3e0140051141050b144030440700c68007c054211070540c5c89600001c1c03400b646002900d0f014121101400209a000c60040d01e016210000c1100c807000741030800c0050b0307810003522130f44190054400c1000491725610700303080c44c900080c52a84a000c0c1c40a112a2020039130320030303003075041246081099904801c40b00707500010880b807030016090100a000341340704010342d100060101c09090740c00081c0d2150b00191180a00850350300d0140e0012042006055200d22504000d003920b04000c581400300c0d84004012003607032040c8204c080d03200d401080b150748401a410740a06602c00081180743c2803018014074a4a071442100c81540c00c020f00c4104021191007164112a0300840c0c4500d000300070440e1a08202c402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 858151025 1250 858149775 858149797
    0x40c1d06130e061611010603020609010810080118031106060919271a07170709080f010603030329090c040e15130e1e120d0b0909031e 59
    0x2480d54582c04500800070240145252a000a06400340300401030001008000260307641e8144141000940c03134142c21190007010a00c0c110310146c2d01c010a8041e5010b080d40000825131034403148800701e81100703868404941c4207994000c201c0e50b44000c2c4903034401054503100d0b0301030523080c086100303a10140030300c80c1d010324844c1c00070981c010980749007000d010a000c03013088040c0f0741071030402c10401e07402e00c8441c0c140d0000b42154140d08105100600c0101c484c0599180106000c000c2641d083c01358100301c005100d20780c104d40801c030003c000340703020b0081440105c0c08282045002035100360000070b80455500009143c040446c00d00303081207804540540000c0000c1c004010125080040b040254401c014040704132071801ca01c1000e000103c1032138188009a42d2500103030952441002c40c003841840d00c071202000380e010049841c5810400d4268010000e03000000318580900c586800c540408041202d10b42503d40d5013480c519200d02c41e20507003e0900c030220314240200001c48010308549015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 858152275 1250 858151025 858151031
    0x1002040603110c061f1e1e080d050319090f0201180b070215040b0313110d0818040b120a06150e1602010902040204030609050c1912060b031005040c1d0613 68
    0x1030765452600b110700d03610082c040440643c01c24041120084040302c20401e6040380300901f503191000d456100c0403206880e10030000000081031110308002c8000501e41e85200b020400a04a86498400c240418400300c1c0411075a00040c2400c2007004929012141d8804400789041c20307030303420440540c003100c1c040020548140070200d060107d01c2c0c05940b00ba20911100c40c0d07100170034100700c20b580c018040481c0c8640b689224140002d0f65041c19105c0190f000c42c8500c0e009840711002038003404030b101605400c501000c5040c101118001252000b40b80030b540100206c0340c160038103200e18171060140071804071001011038591804202241c4030340c2e41e0707480006250700040d070009080c0d92040d4010b036030702c6d0385030b01d01d000c14040305000705005454110b0300003045c8a8110f10b0003c0c4c9110601c03982550040b16990a4180311340c0d07404c000d030380b181c0080070356144160340e040c0c010081000b91829601520219408580381501001101d0383e1041c05000d03520540d034400801080c0404a40054030070750f1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 858153525 1250 858152275 858152279
    0x140604030b01152703120c060c091707050f0d02011701091b030e070315091a0a051602030301030b0402130903080612030a05160807051002040603110c061f 68
    0x81c04441c54082d0418400811294002410050020102d00d00d50492000080c0250b03181940c086200d0048962289614101038000c60041ea0901c81d0341d00b001c0c10703680c204502501081e40c01290442039a00c042d03d00d20708040362400d03c40d6505c0c4d007802411340203c803900a9480910700303100801c1080c0c1c41450301c903208005031040009200e000b03130b000601e596181e0580031080c850740815020b400c002c3c0c6c074040241c2c071000203100b0798078400ca12018291424801d4a080c060074141c0203010515000b034800c1e8403001e40820b440d1020301040782c100740000e10308404038060940c64406810070209a50003141142d085850310703d6036500240c003c83e0300c01060601c00350400c086008501c4582e0298071801036615000c01844403101d070580c500a140d070001c1100d0303810381d50402e003507031290003a01d04a0300036040c9901e030440c280d00c1065400341907486068070308403801c1c42070740061056070b5403540c1c24007007540e500c90240b0710340c060658685070542084001900c06020b00ca4684011805603000404040d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 858154775 1250 858153525 858153533
    0xe0304080a03120609090b071101020f07030e04050609060d171c0b0301061e030602090f041d0c18070807030902041821020c010804030c0501050109140f1014060403 72
    0x1801c000001c03804112a06090300003032516101e0301d0020b04602005000000d031640d9100d52400005000e4001d01400c03c039001b00d2250258161000d111408501c941c0da2441c07030801501d60300c4018681481070742070000065403410036888841c09a1400b0b043e003001c1e90400c1d940c00135000f03009a0860b0301440c1c14070144442001c40309480c4c4d4000e5a0b240000f501d090400e06050a403103d81c1c02200d450356032044d81d100c2d801603d0090004413604104016116a00100007603d0b65420200780c99102c2e0928500f00c080d03025119101e0b59a4100d0001c640e816140c00707060211450400c3c410421258602c00018a07450140b03200d1540415a480c000900e4174041d40001d0489410303980c8000f124180007400780401c03c00c200400c2045400a508003e003120300f1800a65038031211b160f50b4100700308100407900b05400303141c884806681c8070000b4841503031074070041d2000700900c0e806858410103800100d80308981d102c4450340503000b02078402030b15034100169031481d0907001e0b11a641008041000101103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 858156025 1250 858154775 858154783
    0x90b071110030b031b010f0c03030b060304081308011e0906090b09060105151207030b1503010b0d0f021903110706090b0f0c040e0f100905160f0302090a090e030408 72
    0x521050314001183c08001c000d26151a990000c0704144403003500048941e40c2e001285100e14040e6480c00901c11203851400320040c03c405403e05820400c0031042c40200300c075050185c4050050b03032000c411900d0742c4400690917074184580c4404005605c482c66650352a10750000c842441c052400401d804090b66149421440d00700c410000070380100d4018403a51a00c44008500004200d4042d070400c101450030008005019140500341640c07010170b580141c035100850640380c1c015940c003686969507032403aa80030350300082501c80c480e8078100150341d40032510301c20350700000c054040c18010070b101e00c0d0303050b40148210040c803900d0380000d20003100024224000d0040c00e40c840d0510410b2400d2003000a041040c000c3c04131100071400784000e0050000c00280f441c0d1110541171640711613256040c14a0390b16005411110f20a400c06c800c00518040300d9241c0780001c142e907951050008102001241203029000c1503a81c042c1d45030b0020445407010f9040340081d48116401d0380d181a03a1b8407041898 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 858157275 1250 858156025 858156049
    0x1515150201090b090c011d0324060102160e0f090708010c090f0e1605071b0608060a05010f020c06030a0b060a080703060b0406090501050c0a0203120c0609010c090b0711 74
    0x180e4440c60150704004030b80105a0304208410020101c5c42245000a80000c0c0c4c0c8003401c28285d030b1144405291650100402500994540410040400d0342c8007500e404000c200d9103c1d02500c0f07461008034041030450306110840300807050351003d035140c1c1000e58052280107443c030003040c07241100114901d5428807462500d900030b0b465002c0032519114000003818440c1d4400120701031140c0c10031901c000c0101d082c8040b005240340a41c2c2d039805034500b400b50781d0f41d500075038401c450074640c0115000d60400c08203401010101c500e85045980c0b5001100d843d06418084c0d40160800f00025046003000760240d6084065100003013003401c1d52030302140b6190412411400094491400c1c0050940c00d4407518000d040310f80c104605d002d0070f10501030040365441c03240c82c0c10040001510f800008003401800d007210750040680308004050315000c00c458106041c0e0207940e0050202040059005101d001d2280509031500509149042c030303201c29075000114282c0d0480075107494056a40c0d41c3d0001c100f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 858158525 1250 858157275 858157277
    0x315080102070b0a0b010903121403040f0b060405040203071205070302060a090f0f23010513060f1701030f0206030c0712020601091b0c080d090507090c020d020703151515 75
    0xa150310075030801100302e0b0340213891003000916201289030240d03440344501080c0e035000402d58100080f0000100c07a00b10015445244800000c402e02081192410151542c5806000350003000e0320761100700011a40c050380e00a50641c4059003c0107001241660311503110300a1042c1c80c0e01d00d0f80d03900494429401321401c0000190440d5051117455010806100984404a001186681003284070003014400e40c0b2602110807140805058981c41001200c00083c0e0b5401c010514070f55884000d44600e10f41401c50b00485c40503698440c0e02c0301c0c4507580d2412a500b0400070200c0e844180c081c0300c2540d0024210640b41c103402c018500110b440c4805d81e070030300c001a500a049a61610122030102c3d02c10703020b454a440304125010b0040d607409a001c4050301c1d04040000e6540c10b8001c011720081c90020f5004085d4022141c0003c0c100d10250710800c48510142c00351003206210001c103c0c1c40e41442d0000400078a8145a16410552181d00140b04160008003400445441d4582034002c0c007c0350304c40704 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 858159775 1250 858158525 858158527
    0x28141201021c0e060c1e1b07030224030a18140f0c10050a030f2009040b040b0d14010204031a181204030f02041407170915160315080102 60
    0xe082d40005120f403881c40811400a0b107031500b400d400d681c00ba07201d12900002a0841c98459002c454501c40c200c40404440c40c9142d1680c4003180081c941792082c510090317214051000f15101a4682c010b0000c0f2030200011800c0e00d183c1d10311107444000c0101a841900310f240c2603850900040101d1089551114000001c01007a00c8405000b441d2100e04580c0d1801180c02c189802c003082e4124080e00c1040025050116240100c0701061000313060308038210940311203054403244054620b200411005e40242e90910081541d60280015200040c0300f043c1c006a01c9060040450140351a2010301c0c80c01000251800da9280c80e04c10001915169030b503400900541030150700d141c041981d048403e5060041c0c60100601d0749244818015032001814040901116400310340d525800800408031082c2c1521311b83c2882d5000811804103040800284800000450410342e00003a00c2041d50342082c036070010b1aa10302499526094480b85608141511040b03008808003c0c10b980300054a0844001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 858161025 1250 858159775 858159817
    0x3060e0610060f0e040e2a030105131a1308070b0105030c0409020a05131104080705010f020a0f0204111e0c21030403140c07030606052814120102 64
    0xc19070414560010b003d01c000302e80f02c3c080c090b8010042005622040b00d0002c1c2c80581034031000d0901c5808082c420711b41400b0001c00b40d144044400200071108250020049a52200107842d8034285204000c0c1980c041901300e030f000521034900cac1c3c45e808940142074540300c440302d607500107054008000440d18100da45c030050195040400c588040e9140c2150b05204442c000d4001c508510f005024140c0201e501c0180d0390701c02da1840c0c001c2411240c1100d0002e80c1c0f035941c1c160340e50316035110b4007a490000300d2964140105e80d1001950300c900c1e98200842c80301c17150b51682048014101c4a030360213174514041c0424035002c11080020344001030200503ea039a41c3d4180c9405084c03444010301c118414103a44104030841040c1002d880d40325625050049003131529205e02c0c1814040c4681e42e001a2145c0080842040401d0b0840800c98100b916000c4035600090035280c00c00d580395408550742031018004012030100401420801000981440c80785000d240019003a680003411200118503200a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 858162275 1250 858161025 858161041
    0x1c0201050a0b0402070c090b031f0605010f0f02060f06041e0b09060303180f0d200306070e0d030f09050a0906140f030d0c020418063903090c03060e06 66
    0x400c002c10004507404c5280101544da1012142075074001c0c3d130440b80d60740c4203944440c0c800708030812407500051111076011040440039005030030140112400903004c03e207800780b014010f018400030f1681070703000f906840c3c0d81c0311340501d443d4070000c00d440e620646a0b00810102d1132142c07003a43d40e0325005031000c1464407900003400840900a09841d00961041100824407228014602278094040318090752205c002c0c00042d1040d058484050140c40b145410110120703d1308404c00448401030f4166a40c95844507425100980d1300c030100c80d0091858020440020f115a6800c0000040c508201440da83c440020545840f80c54000c01e006580c0d650f02070003a4030301002c640301c403c8821034280d5507822809000c0381c5c0300d4403e0340040e41480050481c400456a40703820101101e0030101c00340400c035400341016009440d820754050ad18601141ea4010700298194013840000c10100d1021452604200200d004000d0340400b9138200e503034038201000041841c010a1070001d04c04c00140024246142 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 858163525 1250 858162275 858162281
    0x30803060a06050910081f1d06040b01080f04060f0e0309030f0705060a210c200106080d05130803180a0801050f13051c052a0a0b091c0201050a 63
    0x1010003404814030040860f40e13505c400a0125214a00c1c000b81e0300e403100070740301080c03003240c41144070380201c0b0800c08200003441d201a103035011701103c201c2000b912098244401c2314004000a40010031002c00200a405da02c4020394019200c0c0100061540148603030100302d03581007040603c0c942002030030401a06e010444541420103190141440d071746404001009803142d6030807003050118424030820700c2c0000c4140b10805403a010020302541d000b814008001c1d036010000d0190010780060306600d00c0b501403049800382c9804400070417605034403200594080d00542141040070840c4880494112024006411380c4e402070082580010302c40c00410800d00389940000d501750789460b041026404005c07074a9070700111b0b500d48000340085039060190800741000201281142216881004154081c000b410002070204101241800c40002911022540e1208080b00d6000c00c00410114540340312164220038031800b00c030340410320310903098088500b074041000940d640300100810604640 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 858164775 1250 858163525 858163529
    0x8091f050714031e04031e0210050a0203040f060209060702030114071115010501180509040c0510050903251706100f03150b03100e0307061a060a1404030204020301030803060a 77
    0x1800c2e60707055280564010350400b0032214007089000c1a0404101032501905034850300008080d192000b5802d12400607556094451000c440742d458035000881c081c42c0384c420750f0301030350340070303002c4440f0302d0587d210316000c0e40140d1b0280c1c1d4803400401411700160f030300340306120810180c02401c14480ca003e8102901032080d90b4445041e035000440c1036150b1449054101c0e06465090a140b0600146083c0e40004030742c00b60407540d00403006500f84000c2c00031041221084030021640700080d1b190440c011541e0b0300030051015003540c0107050705103152003103244070244120280c460f401307115500c0b10340c1818440055488011500030200744041110130149040c098110090103448803851503450700e030394a03410220080b00301c0e81c48040715080c2d81c0600903c070880c20300c1c800600140521000c51500c0750321140040300c0c420b01d854441d1079405980e40240c618040b0061585051116150065075200b034440401804007808020200050751030b03101840c040e50003a080780c0c0d03ca01e8980c4c1801141707540ca07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 858166025 1250 858164775 858164807
    0xf08150f07080c071a0402151602120a2301050601020619200309010605040509010b0f100201061503020c010507080417090102030910030903090609140108091f0507 72
    0x540401018511401009410506514040b032841d0780740000c0b24014091204010401c14101d44503441981d14103011030b0155000f2a40d5015065000c07142c8100e91041440c1804141c0500000c903001d460301899a50288004030140d4500384070700e40d90384074401d41d006500c0c100c1541a440c1d00001c3d0109201e0745500003020b000900860401d03810742040480006a000340a540314498000c0d4908403a000260b490480b4402b20340b2818440c0610303020740700500646000740e00c2c00000450300b00c3c0501482030740141c094a48040503102c0c1043c01580f0820408510541d900d50600240c100c59020b4045c5a5003a41d80c2c0068503000b0148e4aa401d40700701411000400441400780004125030761028130b030590807920a00c1d5600a481c0050b030079030040c8510240d0100e0070ba0002c0e00c80c150140c1000404500c030f581d0349544161110001e4035246039501074000f8200020010840c00d5010346c181e280c11007031807001c035861000d60306074401e0552560090b1b00030240e12a814843c80c42c1d040000400034210b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 858167275 1250 858166025 858166063
    0xf0803040e0109060608010506030606070209040311010e0304051f02190f0209060301420308040305010b06040b0a03050a0b041505010f02010c0e1c171305040614010309110a0f08 78
    0xa0105d004105013410f000391880340c2400004a25a580c0750412228843c0d0301402c40f00a0b80303420304001e044000a14002e01d61942800f180349500540802181c007560802041d905401d50350307083c3d0014010f480ca070700c2000d40c460280e03070101c200564001900d442c2e1040c514500d1000e018410b1041101029083d80d010340e04000c240d910030300f07003551b0302c001409401841655141415174030400c0300181400040250711180ca0210910007200000c009981c001c100901805081c0030a2000501c42e40c8a20b170381c2e0340c005021030303603c20303110b03030084d5030064802507020903500b640b500060229807140c520060b00303940c46081000f003541c0220400c0410781c5a8002008404141040540304510480741c041c820550610121400c11082d40740d001340035084110050051000001000c0360360140e18040c0300455881000115450240a401c0a44a9821441d03400103051001900a082189811038060682003054109600d626040b80c00521114071aa960603144c40407071410702201413040c5407000b503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 858168525 1250 858167275 858167279
    0xe1518090a0b0402030111040303050310121505191a0102063105030717070308060904030c03030f1b0302090108011d0c0d1e0603230d11070f0803040e010906 69
    0xc0040351008015401005a41c000d43c1d40e440000e0041c000c5489041281c81c02240c08000d055018010318410041340340800132103510384440c1041030441540003400e480750588000400300142d0009504000101d2400c544603070300c4e101040075103020600c5141925075540240e2810760703040080036000400981802101c0f600018400c0c00124910501c03a200032038100d49000f041000c01c12140c5168101c84030001814001240c8606da501c0210f040d400554007502041c1346103014584c2500940e0b2503155641c2c01031142e42c050303000c0d080025110144603038417003a0171250480141c821214079850f68005907180d5030710001414080c2c068003d40514015030b2210300c010044000a02d4116526840198440380c1c00c00280014088100c10402080d42c8034400414215054125000b500d1203020b106581060300c00300807080b480900303440002c81d0701c5405442c001500400e0100c510701c0c04501aa00d040ba152501d03d181c588075030b031212199070300c0080c00f0494600c40034213845c05040310704800e100c10b0f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 858169775 1250 858168525 858168541
    0x40912261303020715080108150105010c060b03190606080d0203090a350114010806061014090a032003030f09060306010e0301090c05041817130e1518 66
    0xc400184080000d03580030041c60700341402040076100410700701221444140c4c85000041c050082885000f2072445011450003101e03141c4003004c0d040c0e50060f035500c20504000d86802c400360580615298260080210391080100c0c1c0d410102c0025000b1a804906c09107000e8040c0d03c1c11501240e82401c6400500000d8115640c82601c90202c1c0c8400403035408074054111920502e1102d0210030f01b00c041612140c010540040d0445050f944071681c0b041c28980c2e81d2510141c480c0c0044070341c50f511140d850400c205680c064160024811540c6154600340340300440403488410075504196a408054103a0303c801000c500a444840d0609030042c500f000008064600140100014248940c202000013007459120761924980d03088000e0007403140c1031071409c2003498860300b801a03d014a040c44580d1040901c2c500e0001016a0310100c14401c224540c1c640c0e901d030750491681e292440e50301c0e1400050400020071050b0249a0240180c1d1050340c0020030002c42e0b03a54060200850810f030003c100e0b81d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 858171025 1250 858169775 858169847
    0x151b040306050a06080613020a05010503060603131412190c0206030118110703030203040b151c2a080c0a0e0a02070f0605090703110d02090403050a0905040912 70
    0x225407208010407070307403504580c2401a06950704402c101d1703c41d5500b000b2251319800d4240c1c909a00a0325040d016a4894004491a03c0202d6031250041000c1000c101161160b11808010700d00034804107000d004c0041c045414541c03081c0240f08004008900d0b82076030b0700707002c2c00c001c4c142c65103040648900041da804640c840c00305100d94a50790660b080711082045007070300000302c00048819010341e9188075107405070094109540543d801c0841200040004082d1a450214081d008000030105000518840029805040200e42d034a4070020303000000720f41d40d2a02c19101d0360308415002c1304c5043c103500724508014200e04901c94151071500f007191566642881d81c2000011002580d101c101e41842c440c02030380440c000701204e2914041001903100440c845050702d00c00c01c2d010313480b040d0003801c00c16108030203080690b22001c0d00000c01d000900420007040c4100450900036951561400028103c2c0c500341c000395000a03c0250b400d0382d0650080040720281307140c81411100411544a03c856 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 858172275 1250 858171025 858171029
    0xa020a030804060e0d0f020d020a03390602070209090d05030105101b1b0801140106030902120a0c06030e2d031e37030b06070f05151b04 60
    0xc0c0070300d0784046000c1c072501e40c1000e40d00d00a2482118443c14980c2001032003c0e107100410b90050145240c0e82042c14404076455030003940680d1103800008640240d8040142d440001e054520f03850744c040d40d008205030500b602083d02600b00141c8a005500500400100040c4510320302c0d00205095a0b006422030142c9055547c181c81c4a070304920000029601406160362020816045512000c1003000d40e0000410100c82045003000081c0c1e07400c2c050307003a104444000a0314203030540c01802001e1081e80118800c500007045003681090080c0ca190030002207640649020b04180b4040c0000c6805020f9503061040340001000310107160035106e40002e85441c80502042c40c8100b0f484a00c22082080d600c0304070001e103014000c03010f1720300c0801392a8050342112001c044018090441200541c0022144542e00c4409604a00c03038034004030b00420403c1d003026030090040c040750b0b0120300800100cc610034440c50090499001c61640300443c00001000840c550003405110360351040c01100742c4003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 858173525 1250 858172275 858172277
    0x705090c1b0a1b240c1a0a0b030304051e0f1903050c01091d091c030b03150907270203070c0201081506070305070807050a05060109060603050f0103020d050a0221120a020a03 76
    0xf89144c50444910b8035400b405400c2c00e07a004600c1c43c88040d2a01d1150040780d007107100f0032240d000c06050649a01582c812558003075900343d0074101006584004000784000101942101b0004600055520a004200440f41c0100c00c0d018070801404002c0d5000c0c3d11000d0908141c0c40d0311b003251010031041410100c8010039448004950444810880d184048142c2c1e1903000c0301206c06c840c0100200003010782c45210781b00d8072404000c032549620005008a120300b0180c041c00c2c1c2004801d100041d824400796500c61081c0b411443c060b801ca1014600800c07550707a400c0369286850000401020026101c07030011110030648034000d540f00b40864000e0380c1d1508180e0784440c4923050490b407074061000040c10f42d000707400906041001c0843c10074161001d9000c00c10200f42c642030200d0441c1c4003126020820494030005001510b082210700b20500d210310119284698182d0109040704407070014004524214a484064400140f241e41d140b0020500b10a00b000d0080b40000d580e06c90180b4058 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 858174775 1250 858173525 858173579
    0x31306121d01020723060f040302030f0a08010510090605040909060e060c09031002090d1104290f01170604050c040e01030506060f040903020705090c1b0a1b 69
    0x280440c03140d070001c81d803003191009091200d18408410030302131340c014601240d090742005168146100020520a12601d0b600000d188540d261110701e142ca1001400070f6096100c00c4c002069158034000050569500d9a1740b001410351401d0207101c451160050500d051180c02441404000d80c880191411030f000040c0c08034022919081c12802081c40c0c01ca41c56080c082e11040040b1a1a00c13002000340e05030540468110f61070515144089000b40035401c1d50210003484001c000c0340a50104440c0c10b000100001a144007106648618048000d038080100c3c0d000c1182040601d081840d90390109030a003004030210010251820504800920452046a40c1d1001c02c00350601d1000381d802405405007410b4103540c42c0d003882075884100700d4030742d4400c00e914a1958001d01f0180906030390203034990002d048084c1401c00304088003c000b0aa511045e40921480321541c00c84580624425007400c0a0001c0c00380600385400d000c100c120900c1c1650014600070480030300341481c00f24620f00a21042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 858176025 1250 858174775 858174797
    0xa0f1a090f100914010302010e122109030d08060f060703170714030a050123010c0b060415030804030606080106060207090209060415080906070206060d020d02030111070c0e060102031306 82
    0x901e02c41119040b071128a454115034601070004521036034181c9000343c0380c00c008600c94a0800c0320444100340c06105a03005030409960b424000d80340034a1506400302e031503082c0360007400442c0c544600c11140c10009064141802482d081014074503803000b0301076071030515103880da84000c0c110490325001541c41c8070382c000009520910600c0c800f10b070150720304407440e5030741400c0c894100170703040030702880c180340e0001e140900c4010030381118040c4241042c0c40f451903980d180c0d10b40103143c0b10010300c001c0d0006d803581c1f0031421200c403036520000175510501d009505c84e411403c0245c05c440e01034002800a030b15001c0c0601456800041c2d000848000607409179031020700d0000b040682c0103503403100088840142c0725a081e80d412030003841c862803440c01101d490703548041c400c07640e030f440944250780c000380075428100c0036051000c0304180890000d40041591235801c80d024015a1040c0d1040d0303401110402c05000c03070030940719001d400c82d0003440111f09040c0d0b0801c4944000e40140f04034002c1c010207401d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 858177275 1250 858176025 858176041
    0xb010e060a1b02150301060e01021c0c110301063c0506070309081501083d180515010905060a0b031f080709060f0e180a05060a0f1a090f 60
    0x10b849169030b0244c54403001c0ca82d00c0403c1300b0144c2080c0038a030041115004c0b03201c815403002501110b826050034881030708580b90541903640c001e10741400c0d80d541d41d40c50b09a0b409501c003405000300070030a108103c91205581514005400301d0a40b40f003100c90b011042051002c02c2c0c886010040d11b60440d009561040383c0c3c503099510740c506500140a82c002e84000c64a548092174655049412010a0f20300d00e428040040041200000042c00b901c200c08503d01110320110341c9908101341011000240c00b410007100003000181c1400885255001e13141c6000c07001072000b0030070b0041107800c409014030f0410000040740311003c1d01a40c1ca0481c4080005407c0c2040c1a4081500b0103002035010038050701c03036002c00d8880c1c510b4024107601504203000042c1c04443c001074402114607010513070b2895100c01c80c0c1c4c0102940c100c44045107503c1440c400c0d1000c920140126401640c0810700010079001d48500c0c41c040d590f801d1080200032000480200194903050381c0c0d82d0303201580b0b4a1002c4640d440c000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 858178525 1250 858177275 858177317
    0x807170a210806010f02070e0c040b0c0604031b0f020f0f090f0907140f040c02070e10090501060504210c080d03020d0b04290f220b010e060a 62
    0x400741a040c10360400400114a040022a8800980d40c42e98816514800151500443c102034040107902032001000103140a1040a8000c0c00f070f100d40503d41a540d201422558020103030170025600010240000c26400454003400e003104055040c120f21415107030b0790703881244044080d004101c1c80c14444415130b56035035040c4020900a180c10500c0c101106518128041182c04001a1041000128032540802c4800000420050040348143d280d4401c0c031002c4d2007a0010b00003980708005002c1060300322656407034840d14101801c4995103140a542d0820b4a006030310102c01e01404002c14860744510001e240c030b00810b880038404400ea020b03c3d0030f00035204554810b103104d00071120200d918951580003800350000004003400420b0f172030400c01c02141c107403c000d500d14903800c0c50211865081101d500d00000360081c4442c800c0280c210100304c1101811a00603414503906040008080710351040305110070080c40c0400071940490041511403080445800c2848074200d074088000112923 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 858179775 1250 858178525 858178543
    0x3020d14010e060f0303161e0c150201180804050603040212030f090a1401090e18010f090b0a060303051c0204090e01090201080c0f03040b0c0c0d020c03010c09080717 73
    0x50035240250395409061541000a4070b0451040808420008191600100313980e03000c0482d05607141d04102c95900e00841d40e0800b108201140d05148207080030844080e112801420441300c0d200b0fa4414002000382141c459100b0110941410b8103910003142c9660141c4080d2141611515503130380302c900000b100c400d104e5030800c1c558400040c0c4a1054a011009031102030025104d81c0c502c2070329600340c1d44203003a9030b004443c0000c90200c41000050005401503030400d04107140030400c401100388142c01c6d102140c041c1110980c4501d1002e00b08012800c4099005008490401901d8210340d40140746104614600d0304020b5420001c914492007641160f0081c40e11715404c1061081042e0420301901452704183d000c100c1203800150115581030858000c0e04070001d0051840e526941c40c000803050290070110999014010860f01d4a000c11003841210126001443c41000304c100700b41c252030221140c4410854000c00800081c0000101a82551001040f03141e0001030100c01500c1c000102c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 858181025 1250 858179775 858179801
    0x4050d0504031a22120e1e0105070c0e0903120106050c0c1203040806190c080103080913060314010608010b010e1c02010309170405040606140d05070e0d06020d270303020d 75
    0x6115210100226502c0100e40ca80045e00d5005404031030108000603000310117131080703c00803001f0b00020990300c20001041403031310820380300004c1c03501c5e9103c0802c0000700303e80380341c07007030384000f039080000310320340c050140140243d00c3c10350700d80700c58412a29125074a00f19200c1c041c41c15020590740607401402658084c00241080391500d1802646203058200f819002e00900b81c81c094220380074a10506107181070361307044803a15190242c0303807003400f8603902d02c01c8224004039526040407001441c0402c8481c04030100300000300ea9141041d45042c21226000d29550512020002440365900c3e030350710070740d48540c0f00b00d803143c43c0b40c20301d00059001e4621070000400c101c0310903015404881005010300305035103050700d0801c002c51b1100000c1e9101d00c00981a490324003800d21801980c004039030001a806182d918110b03441058800110b110340340d28000807aa01d42d00443c2074403000301244140021191101c0c02004041004c0821112103103025502604241d00083e400b0701c00c0c00a0f400043c4141c0003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 858182275 1250 858181025 858181081
    0xf0302390306010806010e0603210c06091c0302031b04080718111b071809050606060301030c1e080a0b1e0f0c09130c0804050d0504031a 60
    0x61a066541004904058000d4803004000502990030001280c070b06a43e8240010202c50b401c0980803410040014000b56040c8140070281c0805802d5951065900116203240c41d12440d8144d4054148580204107000c02d078084c45104610304280300101c0c40d440c0300c5040040e42d90310f03003d00980000c0f50807007a0b4415284005800500c00c0e0b40022104126a0280e24008dc1c030040c03501039105580004040f500c000b80240034240201c9800c0800901040c0e40404460382917903144502c07801800030348000d1004950303914090007440740c00d00a03142e000c50b0488015245604545da00309460000d1f00400303182120000107024034a100c10f00981c040d12904084400f01d07400e0745021428000d0031940c9220003442111215800d03d184410b60740a080d48000020305036560302d03244013031034100c0788186500409000c81490151414070840300004166655801c491400f810454a482d025101c0386040144c100b0081010420440d01d0141e00d00c0416908900c50700c80c20348085c0c0c5501d140d0488448114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 858183525 1250 858182275 858182323
    0x507060e071410020f060103140f100b12010905060a0203040c0f03150c08100b030c130f0302010806090f0402042a020706030e010209010e13090516031704080a0f0302 73
    0x35500c15402000070110f6001e60204090f000403a143da14404041083e64413841c01800021042516100320314480d00445a51001c00500d0510381201d44010304030003036495000d00001e0810081148841c00504028400d480301e030383d1401da4901005240b0f80034a917000c800304041240c820900801810341c0c255023218a5141d0030207d001c2c1c1941c0255a1101d8a00b109078004940608103891203011004a407d00380c0d40ba0401d40640344d480100130000e801c3c01001440c84560070b804004014148040c4581007442c19840050084200139001e81e104a80e80001c0202c1300c1035510186500a606a41c0401d500c10200620890304230707840030f98070b6000c81802800c58440c1e0b00045403003ca4526607014071075038000410141c203c1c0704024003140019a0000900d40394100018640700111515900040d00651a2192401c1c1141c21500c4480d48075151810002d000c0b14a551140c070484aa03140c500d001d19240074580e40d0040d01c0401810003203441c0300c00c400c0c0350003401281f030140c6510000c0700c1c0c40781c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 858184775 1250 858183525 858183539
    0x8030a0c0206220b0c0d061217040f1e03060e0607020c06031b091203070f06050708062b0b0a0e120f090d0804150302180d11010507060e07 61
    0x1001456103200148210400903944403039012000d0b40d600c007488800d600c0704041e0307100c0c0700611340300401d481204401001070481980d41c511515004110079865500b07207480c03900c2c1c500825900021100500d1905002c2071103d946039845090403145480d28005002c29258080d0302c000040c0d43c03001e0541480d203800a05210f9011501a02c15540782e030942e07189020709020402207000546d4074290f6140c1c0c03e10b0721148047d100c40200090390b0b00501d01800c440c440c2412520395880b0900803100340c00c0c1d912804c410040716004464011049043c051854680315012503010444030032403581542d82c444100103403030010b845a0f040a900200f082d101460012840406445d4900c912025846025034004c440000d4006444c10b9804451440b40760004800801100d040719210030b4074109820480040c611007003000c0c41c4038810981d140580c8601c5000c50038000480010b128500400060b0360320030010b189808180c0000909080c4a41c482c0c85a003030401c003e03e0f0f4541c500c1914410601c01168103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 858186025 1250 858184775 858184781
    0x51831050630120c010c02070e060415380304032115080c0a0602030c030901080c0412030305180a030c0b0c070b04210c0515130819030e010b0f061608030a 68
    0x3413803110091003d203e40881c00c0f070742c0d2031462044c0c440d44860880400c9482c030f0179400010300c0c2800c25402a40e26038954400c900e0901440c0c0210074411301102101070801082e10740c652890070080500707429460107440251441e0480e000c2864100000422036203016215800350354010001d003400111580c44010b807a9440d0340804420740300d41d0440360b00051092002085480a201204c00385003010005001565080c0b4080d1268081540520001c24802003030030790506458000d0b600420315040c00000541102a92401c03a1401d41207a049000407a421004400c2201d5000388225141c0e500d2601e800b01600811900524020741e010030703c0244035082841040d24050581340500d20240c070907040d00e40b40141500144190040d40420400c0d552145000d40e00002800e41d0540380080d60f518084640e208007880910300c0c5620b0500e50a1641c103103c0d50a24083e0a402004410340c1080014092400e0820a034428080066513504000380c1203854128036500c80c1350243c4034141007641c903000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 858187275 1250 858186025 858186037
    0x16050d17071a0903090a0902180d110118051f090810090b180d0309020409080417060105010503070512060f1906140a090605183105063012 61
    0x90700e4418010908440e8040101d981c60030b002041510341b6072904650341d010750003180c40c440d003000f11103090040644034444c6034026140300b007000d1640b45940340b0014114024014812160000135001072101e07481c2c9010071250680c012a1180c510407440d14111900c1400e5001504903016041100001c11601c2c2c0101e03078941d12400481040b965078419003090043d2000704803440b40c0c8181c5402c0c91035400395016071030181c0082c001054151403034560781d10550065101d000c0d01c121039091003003000010f00141e405800240780c098a10b0400c068020054000d030400041702844210211740540d8441c20a0000064003502855910b2001c0d28450175204040c803c3e0004240d0140c0000f060010300d03c115200c400d20703511440d100b1402c10b41c00300c580c1c2c0c0225055100c225034066203000d00383d640104c01319808210f00441c0d400c0c05010341e03408240080c20201c0284e014208401c0c414141c0d00c40c007554100544140440901c40300901c4c141201b510400c610503042d02034001886d100a00280007421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 858188525 1250 858187275 858187313
    0xc07030c0821030601020718060302151206030129132c0d022a1e0102010e060435130311090f0402060d06052205070216050d1707 57
    0x400da10040c0300382c03294030080fa04140107800c041c0d81401034500c1140d800f42420614440051400c1d12036004c00c0586140040001030080085010280084450703c5a54081408c0c0d00034050950b4680c80f40d500301c0341c0a82d407198000c031540030340083e6031102903151141c05002c4105100059800d508140003070b0100c0b02c1242401e1124814030556a800502c9007002c02c065070062402c111903201201c2101c03a50301100d4040303184030441c010039980d440b4103000451001061002000c0001002908480e6552110b10b5076070440002c020110300d82140c0e52040120307281604251250001084021402510413025012004107000010030890103050007500e100b40604c41101903c00f0130442040000c803016102042c4040003d001803c265003d0f04031135503841b402044294a900000c4e0b22502580b285030010301c400c11035012241d4841c003882d0303044101c81c0080c0c10120504080c1d111280181e0042074090005007066008102c4002e40a00e080403da24205c1e4480c092445d08070304030392400032004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 858189775 1250 858188525 858188563
    0x30f0a0b061603050a030906090605100501031802090603031204060504020f0a0b0306010c0c05040207050604110f03120f070b15010906030c05090103090f0b070908060c16080c07030c08 81
    0xd10103041031812542c01400b82000360b0b121402030740d4111032691000541c0820180c4444071900002c0300e85c0a8400705910504d404141e40c0b62140c0e1100310054540d01182c101401c200c828001034900d4203210103a1034069901c1c0f01d0a0380d0355000720345148625000400301c014040200001c1c000f09a2100d802188212085d00e15a5081c80c20170004085d50300400701c0c2500100045140e66000d03040c0050390b944a207035a60704980d84c642c0018100e810804c400e5800e034012000b00b0040283c00d8100400f5a0317022900031880c4d41048021030ba984c4a11415a20540c0c1c0000d40c410202d04440c05550030030f43d01480071200e82c50006410301d01202c2c04100180482d41d0050b020500b14001c1c061002c500c2060b941c1d040c2010200d500440140080007020340316210401184400714118941c5244180e0035621141452446d0100d280e00d008801090580c034100f0502c0504844c0003480d0000000e00e400024480c0c8502a048999080c1040c1d94001007840100c0c003400140701c9404101d4100c1d801d40b8030032107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 858191025 1250 858189775 858189791
    0x405010b0102031c0507020c040507030b090c07050c01140c1009050105060103060819080f0a030606170705271f03060e010503150702070e130b281808030f0a 69
    0x5903601d00804c0842a1504c0c03286540a8100c5001c0d8020303940301d012031046a99000c510000320701225800e4401c07100103900c0e01e65110503420034600d1140c00c8420075015a24000d41074031a5500c6030856982070341046880d51044a4600a540c1524803448003002607030561410005240c004060216080712a0350800e00059560f6000e4415081241c80b844082c0c50303882d003d1640e0604456071140c0031a10000b003803000e8050041e4081c00380c03001b0b8016440015040b07007814800340984190b550081c000c2581141040040d650210a803010710951650800c800701100307907841d050b010010346054000b44000c20340306c014003806418100b1074040752820410f41e0344860081440580902070203400d5849010300032403c50b241342e02d9542c09034540c07041c2c428607926000340602d85034003a10202e01100406420500b400b08454020340c1002a2495040c1510020b0360084001000317510308050070b940da03000b400745403031008980910a9501c5151140d591420b103039000038014080d15040c002e030b0329103080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 858192275 1250 858191025 858191027
    0xc0b1305041404060b0613030c06081305030f1317010b0112020a05030103080f1b0d020d030506010e21030f0304260d0905010b0a15120606231b060405010b01 69
    0x26030312100c0c2c9100700d004290f6580d403503000181240c05401c0380c001c4402c00a00c80302d0813000c030840c00510b129821075003025180c0440105000c10141025a9405c0254040400103100004072288055244484d81d00d401c42d8455160340034110b0391100c6006017100e4400f202400c3c041d40011011002600d48401152840d14400102c0c040d481220001c200204014004960386402400e4401d01e81c1c0348440c50400c4040c2880d00c4c0100c52a5280800e601c40d042c00c5911039018420198142803030300e0100414500400000c25503444044400e000301080c0c0b074102c0840c019110780c1060810140103c0395a0529072000e045103034400c803015641900c4200e00180c0b000d10a9010004444a4030032a0f810042c102c8481001081c501c2c1c400c80760f56603079025036031030b40d120342600000405001c095002c80c000f02c0a000740258008036494a100361803e142400b044c0d4010404900e50300301072108044411980321b0750481762041200d0f01880e540c81400c0d0700c2400c80300190a61003144124024004803d203100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 858193525 1250 858192275 858192281
    0xc030d0507051303060522030801240c02010f1112130806010b070b1801090605060f0a06141804050a02130b070b04020906040917042603030a0e0a0c0b130504 69
    0x403440d241c3d9012441e04101040310b60300401d400009000c0341901900c550307440500f103074451110850104407103500400a031001028203a0308010001d40103d07800c080741400030600200d000000b4144410900d0f1211354500c1076895074801032410f01218000404800c03403610580182d51501142040b4030400b003a20f40d00070400302d04030781800701d550f030811703901d550307060810300004080d40103100c0741000824a4000c24002e48044a00828000030142080d9050210044000318100c0c0a11b030000404c12010754081440703810100705030070309034403000301d4500205e001070250601903006040c0b0307060149404bc44d600501d0b46842114030080f034240da40071207c40354000d59001030304500c0154005400350031f1840350103a010400900008d54001566149d841c07041c9030201d03040342c107e400f2a05002a05c00b220702d001061010860740d1141040741d40309240d803880f008000007113003900e0749002001c84004001c9012090f0b441190400c0054603800303c81990381050139001c01c4240080030008a07814144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 858194775 1250 858193525 858193537
    0xa020c09040c320f13110a03060905090709050621030406080906010b040303182c0a11030c0703030603050303010602161a090906011812020a06080c0a11120c030d050705 74
    0x603041d0b81a800360a0200640510000b80e42d54018000104801c204005c07071040003111403917000380503281c40220100034110313900341d00001c030704600d80014088201c1e400102c400485100100c04503440e80d5030004241480f0541d508045111052120b0850040d4003002400c144e0f80c0035038402d0840d070b41d140c030f103141d40300f5080c860302045040400c01400440d124244080d049500075503884445075a425102480c9185800e110a1000000007982105440c0d1125150000760080701844480c81c4841928110711010700072150300540050103004040c0aa00944011f54211007603d031250303510740029445004e000d044c0c09019100e0340340851440e0300011099408041030328440e0601c0d400d40c00780188000045e01050511010740100d001045001031988041c15010183c1d155862807407052106000603500200280000f210800c080c41100328162009c41c01075240c0207043c01041c402103401c2c100c0320b6400718015640090790304901c100001c01454501e0400008100c82c0e500d45000311b40c240520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 858196025 1250 858194775 858194849
    0x31d063007022109011403010605031e010501050d0914030301181b0c0305030a060803032701051302090a0908030a020406020f0706050f180d030c031704080a03020a020c09040c 77
    0x482d000002100e10240600003011303044c100a564131000c46242035030b5400036032203500003071000010840464032201424510109012008900e0b50400e0001303002401118810421299594601c4d401d001c2c0ba083c0000c00c00b1040c0044d203580c2d5031241c20005200c0e201400c5108010b040085003158050101010400c1c1c20304d41d83c030440c540c3c08a0354210780541c4094240e400c0b40e51148c40104802005000950141101e02d00202000c5854507540b10b81c1c2d004000002c0c15a40b40c00100200007000400600706103034115041051961410b490b41e00404d01480c01a02000b004010414542401c1d4020425681c994084600041c0c0c68115955a0411401450f0004100307100080d901c40ca04005401f2594540c140c980e003401c03184001c00e500c5000d0a50980000e14156405024190030800150494460b4a0400540d00d4103031038158580c49000744160400d40d0004001e80450300c24405001c1000000780040403a04042c20304a007484494020490090500000da50a842c0b01244c0884803c05d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 858197275 1250 858196025 858196063
    0x3060905010933060e03010b0907050c16050901050d141207200f011206170303070e0a03080a2613020f01020c01090e0405030913061e03031d06300702 66
    0xc104003160384603052100e4603010742d00c8d00c41004003030761800181c51140115542d416120000c10281a152a40f80c0894082d181038078031042c042c5440702403100b41036800c15a050a0001c4407803a1084100c0c4c5801e860070028010143c0ca400c2040c000c20040c24031b14051041000001540c20b103c002d9284040f4a4540c40340011740c1b07140965015400c18000d20180010002d1015565100d4503050008400001d265400c00420404d446801c403070044104041070f40c2501030127081d50b5900000f40701e01280e420505c100c00c912010102da821701034003030601152a154480381040b00900b8200382d00480c1c00ca12400b040300a50280354400900038000c4070b0140d4038030140301d00d000d40c031f040c43c2c0c200500103a0310340c0001c21034562030380c59042125000280d54900084c1141c50300795185168481c641440900a10580d000c0010a5210400030b0b02c4d00e24400550102e401c0300d0000071500c1c81041040307800042211183c40c02c3d10700b4210f2110300c88552599589041d41c503640200c0e2150f40071a010b960000d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 858198525 1250 858197275 858197279
    0x406110111090d031d030703053703110c1302120106080606220305030c0307030201150509040618290105180103032003030a06170a2103060905010933 66
    0x105c1400045440300702c00c070030f414280d410362010a0a0018641040e111948400d40e140b1103240034034104031110152000b004850301f441c903032010034108045c070301904200750811a0100918180010000341400414028105c50b07028190790281d048508800a1400060000258503001d24241c9100d0000103050791701d041001c0000d0381c113007544003441300007011140d0400b000007070f000c100134480c0f0700d0f5030002161a00c4141c0b40003400c0d075003800ca110102d03501c06682003000344c90344010650030940c801808108014520010007101da00740001900c407450101c82d000700e032466049104040c111011200156a1f00c13401030001d038901c8100c42d0745c403018400b801000402c3c1300e03c101e0310602640011000202c880c18034617a1031a003055429130620707641d13602d003000420030404031000c050944030081d09003012a602c0d000c07604240190301c500c020040c41d0310122268829030101c0e0103020340c92420071440d611420002c00810f20040d9041440b4000300e00c40307401543c1107026003203045155070700c030395118 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 858199775 1250 858198525 858198527
    0xc08010b0a0504080106031a13020303120402041404030908070b0301080c0409240501060f1e110f01061d0705040e011203090e07080423151b0406110111090d03 70
    0x1a209200ca40d0402c1024000411251000c0c01200c0040d0300501d80049600c40803d50011644e4010703048070000e07414131543c0b42c0183c6000c4142d500e118a4443d1440c000d03600d41c00810054021064000403e0307103008208010182c00121040965440c001220b01464072412122086d01c003e0281c91381079402804034221900d850b070403003001d551281515000b8020501c4a03003041161010302241c1c0a506c5c0c0c4014002c00d070788030b401c1088403951450451528201400131202d2000c211182d4010800344424110b105201040a401d01d21000360081142e2580d44003401c0c1244001c01e28101c24400b04000308402910510a03a400c1d02c8100300c0c51445c036481c1c800441d00c500512041201800241c9400040b07020000034070b03a100d14003d4440b0261454103141101607200c1c801d09108401d800041401c05500c40080d00d00111200c2c0703030704840b580d1074078400c50381001845214441e022000007004111503500194880b400070740d100080c0940c015415001e10540110044a6081001600c00c00080303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 858201025 1250 858199775 858199777
    0x60a0207050309030706030b19142103281701140301090c2702030c0d0e03070501020417060a050411010c030c05070b0715050603060414030415170a0c08010b 69
    0x186100703004a0703141c104041c0200c0d080013030b0741d4800d0300400c1d99a89030b5102c0e82070041c200703039541c0340ca010190902030604102c5032580c403030346442e00d02070416003144010a2038000e1074800325024640071292030b0400007840301c601c025a0b09100c43c88144400300b00310158054051032001c0030303150300c0c056501da0900c06650b2540041010083c1c1c1903407640725500c0800c0071410325002410b90420604408608811201c03800803c11884d203d29034410003c00540b40258015039510005c8410003082d681c2002541c01d1440c00340c00350141c025440020002120f80b940e640501c4c150790301c0001e4658596030b444904080301c030200c90203407034180030016182d110740c41143c410b180e1074801d040868146c1c07000c0d00ca992501030690004103906400040180c00e00c200c08102103200e0400318402e1082c0d144c100b0108c0e854401c0a0b200400c0e000d080806914540300a01c155000307031458503c541039a0398100e000030000c110b070b0381d00c10103104900d50100321000481e014011070120703a5160502182d107800700051a07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 858202275 1250 858201025 858201037
    0x12030f03091207232b05090a0b0910030e0c010e0102031b1e0f0c240f030612030304020a0315060306020d1a2d0a0305030c1617060a02 59
    0x1ca01841400620503071214024014450041da425001e001007500040c8000c50242600403507030381308166050210361842c00c2031100e45d40001c0e1101d0134044100d010358980c0254921107500c03039040d0a010800e503101c503010300f11340001107480444c200c9900d401030301100c100461b05401307600035451020140d40100002d002c140c8040c4101c82c501204001981e41c001c2e502614840d02ea0004402c0203014480c81c4d0304100c0081400e806080e500e402001781c0c40e540c140030382259006104e080c00c0d1210184c25222080c5507044400803030341e55000f0700d0f155030009601c2101c02034420600000802d003c0c4a00005803403140f903000c2d084014680c21510382e00b01a121080c0700040c601d0701c8542c084002240342c0003801d618603600c000442c1c401805031b480da81c15001071a034107001c0d080112050b40d440f84208510401d240080314805420002c080225866180741d4102034200e00c4009050880c5120000308056103001c030842c000340498031602d242444006000c100c1c40550721441c0850481c4c00c1319401015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 858203525 1250 858202275 858202291
    0x30204050c0f0d050711030408061f030c08060405072c091e15060d0b070e0303090603070807080a02040f03030e2e0801060813062301090603060b12030f03 68
    0x20030160042c0026400b0b03804502e01030141529802403040c026044800c01038990400d401560410782002c8965079140401800030b00941c8518251088500c008200d660186401080d0010391a0b00c42c55425a030704401d65040f81c041c441ca080c0040c0c0c1e1001254a81c1e85c2ca13015823038100e8284090401e5000700d10002e881c40c481406200399a80143c900e083c402c1c14220920009001c2c6d10000c66044080c4400050a587c040c454120000000910074100d1030303803017055070a2400e0606070510100c1d107580140d141e0240c11100000620807411740107200b04d482018295221161556000142e606134001d41c402c03015009210b4009000190103203c20551000003d840f90080b03003492211500905000300822409062219013001d40a90101002e805065075042c403042606000d00c00e43d407250218440034205681e41c10b0220340041210b401d401210ae07000034154000e5841740c0440c2c000300303998801110014030344011000d580c2890b813003640002803404051418189000c03240e540030350000700100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 858204775 1250 858203525 858203527
    0xf0a0e012c030606060f120405030d060308040905070e010210020f1c0b01020615011e12060f0602240f04080d0915050105090f06010f122919030204050c 67
    0x3001400c1c8084110701d80c0c00c440045014031000310428141002009880c040c0550760410001501d00c4902c807c9607040c1000040c0020940e4450400908501854080417480c9007441c00020601c8034070303000b60003070300c0d142c0400700015120366006950700740e030f00e650807400f41e000a141c0181c0040e00358060942c1814001c0b45614200c802c4400d09000c03c01c5200d612440703665003000c42180d5a0401440368440c440c3c02e545002c030030310180040e010901741c17420320502c003052802d415036040c460702101e0203542d40c0c81c0c001d00c00661107644650070002e443c0260030044c401c0204540c8184414403204802844c0314815079802c0c0c4a076000c21003010360060007038a0103c010402072a5101882c842c0741c4005000314103807140c2e6902c6041f60300503542c060340300b11710480020080c042c1d0541c100301040e1300300c2d1090074111142a911402500d001803400d0b11030b08a40e1600001c1144d02141100b642220b80c020400100e9174105a41084185030005800314010f61a410017880141090740c8160380100360310100c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 858206025 1250 858204775 858204797
    0xa090b01050c030f0a0e0a2405070b04260a0e09071103070b0f0a0603110f03070f06080a0c11100b2b0b060306090312220c03170f0a0e01 60
    0x1495503001d40190306900130000340c400d461aa10001070707030039031000300c0d03e031980305280c807032240781580041c181d40e045031004030311403d030f0103010f0012990070301c0e4094a8009540303030908001420681d5186080d48441c58034007818084020a42290464505522022040480e80d07050211140f4000c00106c01e1010780780b00503111030000c1000d0800e0074425420341c000c0c0e24254807e0000350f000948004460b40c20201b061000a80700e60342d180740e41c1303025250381e1110042100080c2c50002c40e5800800c03004081140460000e0344440708920541300c2d51418402008901411106101c01c3c098841c42900f0108400da4060b1054105050b9070350000c10741e1200900780501c0c4034142c121250080400d490b204650400c10040b201c286030b004000714040c01003460700e04403860300e0b40305072030301040041c0c50f000010728242980e41c4800010780b601500d880d114070f541d10b480c4099003028082569445541511850180703210740071104c01400b502c00306401c102811406948a10b90a84d00e079044c0303300700f990 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 858207275 1250 858206025 858206047
    0x20030c0609030c1213061b0209090a0209090a020a03020105160b07052d16060f051305070915170f0a150e03070b040b0714030702100c0804020a090b0105 67
    0x3540161441005140e44a414220070340c030782003081e610f039443d0110034000c40194120800c01d5504a0303d05061400244080d100303203041c0d0480c03651000f544400b002c000e00000f0304002880004c40c52080d5180d0301c0700c0c1c0300d040700c4e9070340c80c80e000c140254040c024807000d0005500c6803000c0e00510101240500300a20180d0381c0c9400c0580490780b0034006400851030922442d0401c482e1010424070b030b50105405100c8400f0207160384101d2900307d85405c05000c0c03017001c0002903444084c0104141c1420802c900b820010350f000c0c1c02e0604400d035014450f2840c082207000c680d1240c840c0c41088440614203452806801c5580c15400007014a028092164036082d0040103004041c52244200003680740c40c1030300e00c41501150a80b00c600c002e254400d0200c0400114811181030f0065000403554060b030f40c408400300c81d807440d00764000910010100c2841680c03034001812030648040d00405001ca14098071080301e0b0031104480c045d5000a20460420414a03103510441d0044010300d401458025803600e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 858208525 1250 858207275 858207283
    0x2706091a04031d0105030f010b250b06040e0313050409060603122001061a0714330702060411011e090f05040c1d190801020d05010902030720030c 64
    0x202600840d80001180a8050407903c000100c0d060074203100e4190308242e10250042d200501404200420000d040080e850004161074003880803003c00c0c8480c00380918182c8201d40c01940c4030b80c00f07181480740014032242c01105850700c1410701440301ca0318518101c200009070044100559405a0340c1001002190542c40b10b010083c956444407480003800c4044404142c80f41b0360a001030ba40f61440911407002c6603a48112041c418050b11a01ca12850411a4902d03011644211007071081038040a006245802e00181424a05480740709040404071003144020303048074403c0c016089500018001074001a0b2039240d68130601d80f00d503920341c0c039164052040d40110b14130170100e100740108000d40d040504400001d000c044d0f40500041c0004207028000d0b6411612909036110310170880c800c15154025025405149100803203004c0341c2d15130f107060003035100803000c4002904040010400078514001c5074000c2e00301d84e980b450720540d040b0440444842e103020340c10481c0401c1101312100b2400f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 858209775 1250 858208525 858208531
    0xf04020103090210020f100e0c0f130204060206040516060e240318010f09050619020c060a0617060403080610050f0a1814090a0c020c10050903012706091a 68
    0x180040009201c04c2c08200d1a0201d07800c0404516801c20341951003040c3d000c609d840d51003c0a036203840b10000e06500240803403803403003c0c1c1c0c2c99091000c180040d0307580d40080c469004a004400713483c955480c40c94080b0711211b00d4000c040120340034071240300441c10080d0000948818000c000e030f1042044040d84d0965038000c5d04c081e01e0503890000e6104001c4020b10460030220046002041820400d954184e1035040040c06585600c100c00450880815607030100c40142206c003007559218500381c00828014003060007104d2108001d9015070b0240980061b13810300032501520b91901b83d58460040240c00d01444203140704010007072141100304220758000d00b4460090307466003c156800307450b051039041103541c0440b010000f0188412001d88540c20559084509d400000c07405182007071042e807901140c580750340e400603001c07049460015031240150051400490090001282c181600d035803c0b41d942c43c0304245010345480303620000350715034032114a040c8901031010042d00000b1094a40b5031080f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 858211025 1250 858209775 858209777
    0x501180b0a06050a12060b01051210060f030212220c09060515040312030c03090f0b01060f020127060b0d050102071707082a070b090a1a030f04020103090210 69
    0x1020500450894902078030000c0d01c0143c0d072000130755140072280340c0701c1d07202c661003d840700e60703109010903d5034401d0045900c9013001c45480b01c102d0405200b621110324080c03144800080034611118000c42c0320b40225030141d00c0b0000e00704c546464100c1070b0009011900c1002c20040c104044501c001031015080000500140e038001500e0303403608051100940b0360210881d505034042005100250046020001210b03e5280c0002c104040b984d00b42c004140c051000b41500540036092800c102d58103400c903040c1c9001daa2546c0c008038072400c00368240d070307000e40c02074040500100400700e00188540c40300714424025480441c240301c0d441c01143c03802e0206541628140d40020b0310509206018228801c020f22842e049841c201840e1115030083c06a10301001141b05111405130f61100c490803440b0140030b000050381c0d0304690b900d192200c1a0b1003110700e6400380080c48400168440340c0c05855080f040070171002071550b5074a0007280c890200040040741810f0341c9010704409038641c1c0e00c3c440355160355 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 858212275 1250 858211025 858211043
    0xc02090c0d0e0c0a09020301030b040308060a0506030a0912032f090616061407140a02010e01020d0b21030f030a022a151504020d0b03010213050139050118 68
    0x140f401e02c0740ea00c2240d00134070841e500401c010400541070359001503011b0b030946001c0000c2e40742e40d400202d91981d99401540d0145003c0103111130340720030384d01c8181100e120f12254a40c2400803c000c0c0d0903260742078103424074469519120010b11107042a4074040224408500f171a11107100000350f41c0c1d40000c00006021b00740b6101d14820420f0707512031003215040e010100300039490016401054100c0b04001078586410110314102c1450003504001c0d4440b0161000759200c0f030f090201c001c0105a42000c40340301e07980c50780c10480e41020071170044005a103090041e41c40d0555490115840d94000380101c955158200035044980c180c141565074140f0003491030700d4400c1403001103c0d1038009015030902c0c42e41d6000084c802e404080c5032040203000700c240ea02584a40d0002076000040c41240030043d05540002141341682c1b101030080e00c00c0e28000d8076200d203d64403847c121780600c601c0f4005043c45000600742c41880b2100200f40b500040e00c540c0000c217041341c0504000003540e0108000f2540210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 858213525 1250 858212275 858212293
    0xf09150c150c04050111011e0e0d110c060901090803030405070f06300204091a270a18061407030b04140a0c0c0c0e0405060c0306010c02090c0d0e 64
    0x5000d125096041034040c00c5440c1c00d00300311116085511407441564103208101d000c00540010030340010300141000000b07540b8000c030300c51018020f03081207107030000715001d0344d905940e01d680924000680d06080da0001c2400c07002050602030164002654641071206289001852031810001140b10b140703e58007510320240f41280d0010f80b050341707801c0030f4144032180d100c440340700810000c0c9001c0f01d0308540c502d0721000f8000002d24024442da030440c081142c10300504200e049100030030601d500c0e209980f8421080c90780031b1005201075940380e100380c13815400d101084a000d5540c01c406110006800d80c0340c000c0304503650b02c200700c480008612a600801d00104503400e60113101d9280355032000d650a00282c0d0841c1c01000100c440186000030f200c0d9030318513108050b403160128078007082d440403641e40f03540d8039040401050343c402c0758125490f104540000c4c44804840003585d0003644107858030401000a076003006450503000b095101d1145090051241949450103040d02c1c60301c2a10203005c001f9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 858214775 1250 858213525 858213547
    0xa09061b02010c0e0a031109150a06030e06100b070f022205040605090f0d050f190c1203060f1401020f070f050315070509010503041118151002070501050f0915 70
    0x6130103580c4038401c0c0c100340020000305220448146030003200302c50a00341642c030410040c0d40d2188544150b5040000000d01080c2d607505940076401d6034201004903041540c1d0060f031030034040303818054081605000c1c032188002610030096600c0d043e1001b00001c0c0d41000821500020722091040161520307280c00a02c01400468411107400c00782440c00351500910400c91241e07244d00c2e0752000000c000c80041c0281d021540c80c401e5400d51000d200c80c0c03162445000000800142c5941020340c0e4089051307002c2100305000b031180e0030480c0d081c881c120b0400c070300e0500c8034207462414901840c15800342b206031018242c000d10500d406030072000314042910341032100740343c984030740341d03c061460404210501807030603001410307204146000d10b07105d55030b0368031460040b0b0008041c907156500841c540c4811000104160b00417881403000c1c08541165162540c2040b404e0003441c0310860240e00440c2081c003095224030020b0a901d044034400a00d80f00b41ca40101d4100d01c0000c0e441680c0b250301190410b10a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 858216025 1250 858214775 858214787
    0x60f030a0c020a0201021b1807050c070e090703240509010c02010b191401090e07020705120c0a18060e15010f020a170307111507090605040e0a09061b02010c 69
    0x3003001c61009050102203680080e40e00d01e100e0000000503120703107026046139541ca40381841d038204071011103012424104c102a100d40c10000486100e0700030303039001007140203200b41064030035007160000b0000c06e0701d1603d42c03071004000705040300c0b241c0e811002c2d00c6c0d10b0302820303020b9140140c5140c0c00000c2c880c1c11010b1300900311140f10742510302c1445003030141c00c207881c43c1d01d07221f1094490b41400704003601e1810b80140c4500701142c0c001c0b00c0b100300c0c410800161540100c0c041044500c103844940044801a4805071180405980380b0b501405555040c402ca101407030300e103c013030f10f9111000103049480d20b0007503440e810200d032001e02d081c11018540c1c5c419648480b41c0804100c49000070a240030140d40c0701c0142142410030000601c1c804000100401d116a511518118500040d165a0980c8207000600b1050446480e40414030b503a000044941c45281200e040303074011840c80c1041e07210007590714090210044242c07519900c62000c00c04020800c4030b030110071217103600006a0880c18140c06046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 858217275 1250 858216025 858216041
    0x31e070c02030c060a09030209070e2106010b04060f0e0f060c010f1a0303040b03190203040f050c01050c070b03040507030c0b03180a030e060a030608070803120f101211060f030a 78
    0xc0c902800340104007500410340a047e40c3c0e04440081035030350f81510803581d080011940c0355001202c40d468442e01080201d0440d900c1e40c0e10300554001d0ba8039071940c20300d5846280304403400103507402e10a2003680e00c181c928040c0400300804003292a00c2c800002103c98000d24117622017a5075030100004248164880c43c1e6640c0322800c1c1060b200070b81100040e403640514850041150700000c005030554481002d140075900311000d04640328101401c05100c25056040111a98814149003080704e43c000e005980101250384014502141000c4a81c041c6400c0071308102c50a04c83c001f0044000f5100f22240c03006088907075401500e03850828100c50742c4d0010820040940e40061140d40c001c0703079101c00d0690708410140c8250340d4503000708030210014466603101021501070408003003000c0038040b0050101e048049010311580d16a503041514600040e20103881c81030103c04104000c0c80c5004201c601d0300e006011103a2117411082c00310b444c590101840240c070440000c10440c5044003442081c2d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 858218525 1250 858217275 858217279
    0x1502070806070e12150c0301180b0f0d03020a151410030807030518131d010612030c02190902030601031b020705090c0c03040e0610180b031e070c02030c 67
    0x1141821900078000c110760789081d03401100f03130740800780360104104807060000b5603d01c05041d80c0d04e07003044071100c43d8100f8002c00e840702e5140341b02c2c061885441e00943c200444000c1580c042000048100540145881801c401350300618041601080d090004503026a00200011407050403912034400090340061412000071440308040c404220322005503a03120798941002c56a50448010281c903c0c84d14418040d40034854181c03c642c2c4081d160812188003e8601100a40e112182c0c0709a0a860b010f004510ba02628800c0c01c1020a106030008103800b400506010400f0b8200c2c8c441c0369011403507800c07008601da00041409160f59162140060030700d002000301c440c80441000081d12070105115042c8501d8000380428002181c2e07000b01c3d00304d078000a007241d680e1903883e0b0a203182050101c64441c80781c142000015041801070501062800031030628407591410b0400d8203a46800180250f4511030641018400c0010b408851a006104d40d0321000320321000c510406280c1000c0382e10441c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 858219775 1250 858218525 858218533
    0x15010305010b031315060503160f050d0206190339030207081e0f0c070302120102041d10030c0608061005130506070f02150705070501031b030506041515020708 70
    0x4090b4501c0d0307107134880041e4020000d1000391009083c0d00041d015a4000707581c14015a84400243c2107942429402c036405900400c219a58480801c09101070030030700a03421880c101b06220b1440002c1d100090808140e080c0000c00141c40480d1984004518080b05110207240c0710b0480aa08a6000b150b0081070b14034042d443d002803695103c009001c0d0440c0c0403c0901c83c80d4a00d080c4201981c261456044507411880e12419601d2100380e803040c2d01d100590195000d0300034030175041410700031101075030b464a08441c604440d417000319042d40340080c250030907214031080110008140b00c203e00010801ca0f81c0d030a810742052010403181d48000f200b40c10503c041003000d60175014030724211100301e40040300c205444070350030306103a0006e07241c0c010000e5110b00e0102074a00c1e1840140082e01d20b4074000d1044a070b1903a100c40040d004c984070061b06849080d58000070a01d0584030b608001c0d0702c0200548086240340d0000500b0042d21641c0d000a051001d10049044005a041041200405c0000010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 858221025 1250 858219775 858219781
    0x130f03050f1c120b0f03100b040f02040806070c0c05100e100e01020c0d05011d030712030c090e04081603113f0c030403080d0b03010b131d030315010305010b03 70
    0x151500c3c080d90b001031040c0741c480301c682c0c00701e940d02c0c10021004403001d0140c8054594900d0100020160b065440d840303145005d0141c04201c10318805c3c0c8040c0d0741c1e901c1c0200f002e078954031800e50305038010785011030742044a2040810141c54a40d400c465038816622501c2c04802d03103c04011003201c04603460002c102d100c060011a603030340061001c3e84080261001c03025808682082e60241032940d000c400050b41081d015080c860000008091082c000c01c54529070302c0500d0012426544240140300000724600028403a000a031903601d500b040c4035400f01c0b4078061503007003803180c900c2c401031058021805003003880c0070701901441070601d103418440d80e5480042c5203449075450360a8110b11259003103030356410034001c1c500c450101c4040002c1030b811692910740c0d0789009101036010440c1010001d003003980b0140503085c140600c60242d0002080b44407002c080364036090007000c4444010050701e003412000482d19400707000540c02502212014101d15114070009800d07110180d1000420b00e40030010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 858222275 1250 858221025 858221027
    0x4022b03050c030c1b030723060a050d0c0c150603020d0609030203040323070e071d030304150c0b0903030622060b04080d230f130f03050f1c 62
    0x101040140d0604105458451000c0354034554010070300442d03464481c106000080c001c624003400c40c03540044040300c15280d1030f0300c402d000d01070140b000000c8900184030015500d00c0c00e90081d02202a00c0c1c5041c1d0300300f051a031310800036130300040582c0700170801c0e001c8454203010103a845c54030b011404a005100310741c41d40c1c1c0483d00106032a40c000c3d0a0a40e510451000c06200b030040300c0086410080d070500000c00b12901c2d030900c00811909100030720035800d0024070740808224040c03040040d80c1b280d402d140c140c8464107117801d40301c554481c0d040c00200030100d003118050740d44a4401515603600322009501e45040031001303d0107045103c1c258001d200b00481542c84205a01b036207444002240d405560103000c505c050807481c1c006014460000c01c020a0740701d40043d0402c0201c007159543c0121a90403d803180710b02000302110803181d241001030b60307030302c02c00400185941d011204640601f10341d681c054808414054004a800c0e8104440b020741c004401c0003040d074411503840c18a5011b03807020038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 858223525 1250 858222275 858222349
    0x915050108010b030a03120605061216091512150b13080a050705011206030213090620190e1005090907030b130506030307150b04060b07020303040608180d05030402 72
    0x4042008280c20844905c1f5107800503402040090125030b2141a080100d030300880007100c038010045904103204502c103218405160844803010003040b0340398100c6404581d8181e944103c0c05500c0d46829941e82034090180e813602c02042200e114980340c0100d4410903040304130952202c0e6071a4407507400c1801241e404914942261404d082c03901e5000d087d040c102d00078103100d900c00303548a00a940801011000350300f10390200c521034003040000c60030f4608c215410349035031680701c01140410b214007164568003000c4122034080c40e003407200d1a007581da800540c02040c4003480b50000343d00030522074028181400c139982c01403102d080074002c404107840802d00341752094a0304e4040c5620307007010501e292801d004070341409400c907800e0050304000c0e117042c0020b4000d220026000b00d141c05800255280c0e01030944149590040185103400d252046c1203c65103009040d41000c105a00002403d00d0301c200000b0407045600d480f080d440e46490300401c040b52110800001200c0e0000c0c070300c0340c90700e02442 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 858224775 1250 858223525 858223543
    0x9050a080601060521070c230c060306010c06090507030b161e0c0f1a090c09040b0403031509050a0507090b121513062c0711100915050108010b03 64
    0x40307442c4e03403104000d180540e100b400040c01d125403480600d05004000d6413040c601d245c0d250150041e03d00f081a0004404842d01c100348070000e454002c6448a80300c1e00c0c08c03400442d04128149044184009942c03038005c1107030605102102c80d6030190004000300040041890f80c0610025501e0294040c10100a4202082c401e02c401c0e41c0b1302800c1c2107951050042002802181c0c00813260160021a450001307a81c03004c8104166010b0003200c0019410400000d10144451010380310348059196591184980c11020308100d0134951102d4241c2d4044a80d1100e0600611024101082608100000c5c804458015003d6030401030750b070100388101140c0000312800c1540441381200b151740c0f289403200c4010701e080c0400f980300c01448405006c0d8000d54000d1000d032141c43c142800c1c000d242c0541e020042000d007070149100e82000000401d044d01920000384042501400c0d100984242d02141c1c0407550103100880c0d20134091005040054040e2242c2805800d408008000340308080300000d642c0c0502ca = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 858226025 1250 858224775 858224777
    0x30105061c020312030703050a0f0507021005150919060f060f080a0e060108100609050621030910080115090608161806050309060f040b0a05040f021201050709050a08060106 76
    0x400110030840d101041124031820101307040d40d0710f07410070300d0005011300307026129031500d81d0405115040a0801d0f01c1424010101a0001c1c901112008082806040028040947c03505100b16030315643d1189040c00b4070a410741004161003084c00031040088030b4942d007104544902e82c2c8024402141c000030b80603130000850605044540d10201810003619504d4081c4945000d000000900c60b400041c0e4440520403112003804142e4a0303851130011290f0840310310342d02c1300c00c170203010581c52400c0313800e00b0304045602d0580307181c0b4400901090f81c07100b800d42140001b642c039030700401120050042c2040045640d04d440b20302c82c1c0c0780090042c100e0034007402032190640050540d00c038a41c0120515030032204078960280c19a640ca400c05800c4d82c1045a4004650040b4800a88402444101d0a2041ea88140340028903215006140d0003800014001c8804004020b00e040c050f82d1081415000b5200d44800490a45006c0000a2010020390f00c02c50051048243c1070203003000205980e0f05403452 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 858227275 1250 858226025 858226069
    0xe0a080109081c0f0912030c2307022b0204060506120c0c0a02211204060504031e0f0f05010605030c1e03191a28051b04140f03010506 59
    0x1048599100414404a40c6184c0c1480d0407503003c1040031452694500d585251410072079400c1c1607406403064408010f00c404150740f09040c0381c0c0b0f5044c003040a0f29910340041c0030071411043c0880c0142000e807000d40c03900740e10901c01c1c01c04002c41c80c15004e1000600801d8410034240902104008001e94000d0004441d00c4008161030354440340030011820495002020a800b6815068240102c1542060021054005c007820180030001005c215000c0301e6603070740c40e546058603548401da84101103103a0340f81100c400340c01d0100490100380900c18011700a841c20122402d09140050860b034180d400b580c000e8006c1c008101c1c070b640e030f45601c0c1042d41c941c40320240201080b1200003400c00c28000805541c0054034188030381400201c100402c00c034034001c180c070101034442e0300795062240d01850030307400c005110000d0551104e010f500041d402c8004c09520f0741c00700e20202d0f0f440c0300703a0700903410a210303034004030340321203880c0c60141e21a0003180720a400810990801d040805c10401c00141c042c2c0c22119 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 858228525 1250 858227275 858227317
    0xb03040303110d110306030601080106050102030318190302030a1d010e091b1c15182a0e031509030a0c1106030f07020609060f06041d010504030e0a08010908 69
    0x200c0d11080b0348841c000c410003041013420549100400703800543e0701500900c24900042002d00051140c03c0a45105030000e6055503500c0403030313038a8003500c00e08060450044c400102d035132011139016800d40c2480f0380c01458842041440080c0181e0b8075004030000c0c3c50b1a004070666598200711704080d1000141c4038210b2981d5007595040140311300000e403200380c21000800c491541001807200d504164009000d00c4030204c150341108103410540644034039003425500c1400c1420503544a09004e498000100c40002c541104010306807600a1141021421440401ca080d02d014405440800c0d19481414100e0800010fa00d5907402460007480034803050040300014400c04000c1800080d4004007403650328a8100701202160505442d02c2c0d000d48122404144400d0021407140e100f0050b400302e81182d55501c0040102030202c7c03940c0c0e050f40d40305005c011a01d006081c007645110b075010b604c4007410040214280142c03050540c0c4001066490003903030100140540c41190316140d912445502c4041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 858229775 1250 858228525 858228551
    0x15160c0203030f0d1d010203040b06010e01020f0601090516020a080f2110050f0132121e0903040e0c030a0b040c0c02030d030228091a040503010b0a0b03040303 70
    0x3125011410b400c030320001c101c606813500c464008145200c40c15400c07065001305002414240d01054030002d08146a40d00014001d5100d0f80003500000c40502c11101c59508100f100c40c01c0c400d0a03000301428546070f4040004520100c0690705800741030380b00500d164016912001094024120360b880d20041c00514018a59809840d4501d00050080d2000b000e0600d6090341501000c00c0c411a40200d00d03000c0510200e600a011822504c0483c810462403941d03c1548404401e8510089101101051081c5101e0b440454003280c4a01f54404604c005001800e1123070042c0c00700104405850742c000c00082c4401e000040c9056088114511119200e40364000010003614840508a40007458207202c00c4109038496010140c40e03000750155041d5500c0c05504405900c034180350801c2240308103020303203100d8485141480a0000f20705d403008072103440b0b403119280f0381103160359000d0307030200030500340924a02807050100c90340d011111891920300c5c20f91603000d903010052001d01410303514007040307480d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 858231025 1250 858229775 858229777
    0x1060c08090d03031b110d03090b180f12031014060f16061107020a050f0d020127080a0c061e0305090703051609060f08030910090f0b0c15160c020303 66
    0x9085c0681108483c0c4811080040c115240407007140414458810011aa44e00a2151010f03036a0400e50701d80f0749a5034518003a0505d81500c907403814074415420941d4895105100b10100043d802c0c28030365503030504a44400b80e48440742c0203070000e41503004501156030358040c00c030b415150007640001d440760104d030340412034120710150150000d0b0401724000024180d88008101d00c1e8401c540f0020b816850781d0510110420780309040e600610510074200242d80516024181c4d50311070300c0c03141950f8910000c46008000c280e44104a20340c05180040c082042c1c0c8000c050180c841443c0200010784016000c005007109000032405140ea141f012031020202441503030051501f00c41200c25000204482c0d00009069214014096140031008124445148811011100701c80000d50400144200b001a5420b000740c1943c1440540a00010340e070061507050002041c1c0b44003140d40703802656035400d081c6060300f1350800d09841001c0401610b03000083d2070345214005c918091700320489500c0842e1031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858232275 1250 858231025 858231041
    0x52509030c06120c020a020f0f0303250c170307110d061a0325060e01050418140f04170a030905030c010204060906050c0703260c0d0801060c08090d0303 67
    0x103201c40e80303a0007140d480c0d0440710703124250014039404c00940309a148100d80f10786140d0341c025030003520461001000c3c9004101d2689000303004055030320744201c800402452101d50395180c00b400c0c2c10701d0b035410180300400e151040103005618050300001c10004502d40c4a100d071101c01084c50741c04040001c000d07113861091051640e80b1440030040c240446208a1103801e0440b0b060b4424131170210482079480411a1200c0300030709000c010a04281000402d880c038840402003a4100002400001240c0302c11806000b41441c2210303000440305104160704000390303001491100c02000400034040003c03154030a10881e41c025855554503062041c00071005020220000b8003288008a00c90f1201134066004200301d0340c0c55220002c480395100015512400354000341d130000d4001450410120362000c00c1c40225130009030107030060000307910481006800c400d2071114103a11a034640400503401c0400c40c0d000d0003c6040501d1a5802659038195070311035080000c1c0124842841041014004e801481e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 858233525 1250 858232275 858232283
    0x906010308120a060b07060e07050111030f03062b030201050a0207020f0f0303090a0f1707180908040e04110f0f03101d010e060702060a0204050105040312090f0f081005250903 77
    0xd621001c1d0f05100c4007820400706101d0b524009d04000050545c00740c90703008041c0c0e43d21005141051110031204100350001424180c000e540e006281ca206000241035174440c8900f11642c40300b402c5d05040090031100010410021680f0401c061005a03480900c951001d07001290700349102401c50010034114000d030710003140c12060300f000c081100592100440261210102c0194091040c1e07030038199910401d1080d041100400c91001c9210f1829420280c27610780501c00f4545070558032504051700b080101e40a48150001700c42d00320080c601940001d068507022034000310030407080740c0041d803a61100c1c80c59036405651800303501d0b9185050040e82000c880c00c84001c018510f203141001e52290f0f002ca949000501411380003130060002413013990161041a9204c90520f8116900e40311001c2a01500720240100f080d4009002c4140000d10006000c0c1c100700d0304019450320310414504100340c0341130040c0609103400c004182c882852440e540c1c10383d83c00d000003510403d00041d1110109508064 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 858234775 1250 858233525 858233527
    0x607060b0901170f0a0201230408101d01060609150c020405070503010e16020d050d090b09010c0f2a020d0b01080105040c0e040f14190c0305060906010308120a060b 72
    0x60700c83d000081c00200c4840181c20b40d040440072a07000b0340c0f2401000300081c00718215003081007140020811095030310546083e8030380361503101c480349890010143e40003202c65482d6490880d5115480100c94070a5029000070311105040c89000760902686005070720081d21402c0702d100055104012907104140c0203081005a403c0007100101399510074011a840c9005c0c91020901c003214803190030000e004070f9405015112a56201250150300140b641401503131200c2c014808030750341048840c0144481d00c000294044400e801420100c080010030301480103083c80d100c40f0075150045401904911a10380b146007101380300040800b224403401628075400640085a40401548241e000350300a51442140551b100d410309207400301140c0041070581d00050010000b4015030600300340454001c156404c1000e818401c0780c0c81e0220b441d0580b0f40f070036040701c200309000c424840c154003c040b0f1307009070110b90b0440e1240c80b00b034841c2c0b03552141e580d0382c0c40c00000c12601356070340450301170725a00d0285 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 858236025 1250 858234775 858234779
    0x81504150605061c0507090b2a0d09050f04090c09090501060e0403020a060605150a12060923090f1f0b15091003020421050c150a120b0f0607060b0901 66
    0x21300d1684840c070500042091408000c01d00250092044900302c40d11014003034038141051100c0340c001c00c121690003010880548000b04d20003000e0041d40c0841c141551104e4503e480e04042001c3d5103120032442d0b000c1c0345440c0c908000b0919950f050030a5070200a00410300142e249000c1d401484150f100720070f1060811309000405d81d010544034900e601034803040c44040d403200104003c0071683d0b071582491705c03000c02154228034082c1420054440355484c0006082da038612800e01600c8419031301210303180c40000c80c410543c000c503100a07040a820070050420b203107641280c076a40c2c90f000038080342c5425001c0c1001005881500882d212210241111400004c0c244007030010750014071401b0b20580b200511405050321a2007034604a44c2d80a02000c400c0b03004040f060804142c3c180c3c00d403413170302030800240c1190b122414018903a40000040f42c4c0d5036034141000030482382d040d440f488038443c00c004401e1040d81c0c488805e4000594100e03422541c8188500d8028001c01c031201030141c116200d4800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 858237275 1250 858236025 858236047
    0xe060f06191a0405060c06092503030305130605100303080c0a08043309060c110c120c0402030c0903071a0a0305190614010f020303010521030c030c06070908150415060506 75
    0x40e16000350341a2003202d403411039403a49d9081c0492034100000000e88012000c00200b44243c010701c1d04810000c07401c410603107483d01e4035810b85000715030b0002603001d126010401c05501c01c981e60b034495000c060785e070700340071720204010311031540504050403100a40c0c0254440c0900d00d14602c103500d00101402c0c8015849210560262a0b01e900a1f41d000385040040e0300c05501401c1400001020035000d455071101040810000c103205d13002042c05442254019800c40d02c0d140300650103040700e000c070503882d1301800c8105841c0c61403580284520034170141524629110850a8402502c510308010a075039640c4d03885880b100825020341c4c034545040c1440003802c810300309183c284401007a6680c5003961800081079a4900c400e118107508030090380f42c40340d121900c80b480700242030702003010341c0c3c58011603d901d40d2440d04481c801d0455500318209100020340c0009101e8018050900640701c8011001079038409841c2c0100090003520009101d2079000d50568480800b62070004d206036159090844 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 858238525 1250 858237275 858237283
    0xb030f180f0706081f05100c0206030a020310050a081005150306040f02040f0b090613020415091511060604050a0605130609050c0316210e060f06191a0405060c 70
    0x41540045550113000c02e4000c85004041980000004000d44030b0510b420140b10080d62030000b81010001c070704001d880140d442d0030003103005582c10007000da20303420060004055201c2035400603205110301001080700c0d00380455503400e150090b440000d410f42d500344514400c6407007844001c0d410700402c801c1004100e14401002046030080d0b4081000005084604007240c0d1504201c5501c04c80c0c020005a80d0304c1d00c445500c010061102000d410030381e49400981d500c0c1107085000c0301142810000340050a4084965001c4040030b28000004c03066540c0c5a0345c46100141541c1c1c020350312580041c0e800e035241d4124200408001e40b090700d460360b56201c0f4000403c0ea40c001d1912450900c0080b4031003a038407000307490058070a44040841401d148005036000080b01c1c0040340040c081c000c540140f801a446003d201900d504007925441c07401c1c403503085904600030441c600c50a8080035104010800242c1441960303981b030440100b1070400140302c840d80c000c41d841b07564003400000d0b4030070403400082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 858239775 1250 858238525 858238529
    0x16060c1e0b09010f020414220c050a020c03030a05090103090219300305030606034606030b060418230f0c01081b0c250605040b030f180f07 61
    0x20b00204070b00d4807401c0f00001a40705501c1805000407400c0003a91480c40c080300620b0801d00c0b5005400210f41c1712864000540b52019941c10204001048240c0c840740c06220105038108100c02843c503210070084040c0c944d024481259041542e520064002c5480b08250001501e0243c40c000e070001d9a1845022030181541040580000d0006096040040d001c003140340d441b50305445550031507a03500d0038440c2c241c00c020455600716980300480d0507495806003526140400f40d0a810448440e11400882c0c00864070700103119151401c2c004001103011226103581001c011a0040342001010915078203004035440080d0901038507025031500c0e891505c0c03a12030f101e84000c06a5a40d0341d02d81c01150f8403403407a03182003030201c1c900c440001d801601403981005203c000c0919241020a80d00c0110328100d8900381c6414480e407040003100e0321a40302030f210f8000b4521b51502914090400030b80c108903000c040d14541c0381000d60404600b00b0032003d400304d00e0280d030b00401c41d01803415071304a141c8c3d102c00324 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 858241025 1250 858239775 858239791
    0x904060902131d04020108040c0314030301170c090103060c0909050c0405031c020a0b060109080a0b0a0506062803061d0a0f0e210d140603070816060c1e0b 68
    0xb0b0800190b0003d1805641c8031000d40d00e4410401540d9903001986d01c1c60000380200c032130311181c00d000700000340c1d4803e1100f07800f66504021a00c1c1d60402c40100c80c010080300000040c0e81c40881070450903a14820a50b047d00d0b8008008500c40d00c042d481a900f52075980c11010109e41441c08000c40009440c1c090000c4520480440d600b1604418105d41c3c520789071a054070050f0082003000c40442c046c1508031b0b4226406150002e8000c5d89c510265050010440c4111082c41c0040c1c103010b01f00901d401241d80004080b03c0c9549050b51004220480500340c9408113020030304413101011940c00b0750300200c014101c50741c00105c00032480445515100b000c41c2d42c030340741c00e103130040380140e88405100c1d014001c01403200408080b080c10b03401d030354010b08140206040100030007195880800074002c18600048600303250b030b26030608500301400d04403203400c2a8042da1008a054010448480c03000703040360801d04244101c4a014205901c0819031071191401e45d42030f5200480412000004642c8605d4207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 858242275 1250 858241025 858241057
    0x31b0904140f01142d0703110405120f01050a0b0d0b0a2a080a0506011b170d09020a0803030c041a070204150302040f05091011070507080105041401020a0f0c080904060902 75
    0x10064000f0017240c850041042e01d194140014000710300135070203040101b0380c4650842c00d081c0e0303540000d0709420680b0b5222013181c020704103900c2500e800340686600040000014031008540e000890034080c589200a041c28440c0030210329101401e501000800d0901914004c042d0b0381c0300e8444050810300411003002485040014200b400207104203400307082c059450501c090407000507a000d41100050a44149420b21155160020340fa00100280064103101041102076801008072004455003d0442900208104202070141c03e046130f0a0350714840703106000200c9400285c07064050080029007051a00ca4009102c05405c00340740b007203a20850f003d0140c0e0604a0000040c1e580c107032802280c80d07111800440c410080c0d81c01c8600d01d040c04103011411710f16142c80e850b1500e4038652107101640d54540c140818001c40007022038202c42d440c0003d51170140c1500f401402d00c0d56440d82c240c1004200d42c0000704020b0a03001301c51403840014030501419482e245180b000703501941d0300b8000000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 858243525 1250 858242275 858242311
    0x706080f06010801090f0b0307030308060411091305130f0515072d0c021c03030c1d010806150a020706090501020a051f020c070b0405031b0904140f0114 67
    0x80c003110340600c601d8060355455410303460090841e000d05402084d5000d01e940702c416030402502c0802141c40107601940c0d40440b03904101060004940c0021541e070030000d020010204075071500840c11187c601c041c10001140e5544840b1103060441604005080340e042204003000c5c0080040c4100844c6090f41410445841b41d00003919806064401c0101e940780101c2481961500a00300b201c00102c6410200001c191540c0012900c2809201401c6000e01c1a480d550030716525110b990702c410500e060038840c5041c01c00c000c00307185450801590400000c0e40000c1c2e0030b0b4482051102113a109405481c0d00c8813424000603450f1070740c41c0101c0700003a45c1c0400000d5550310004401e20101c0e0000b01900ca100114007100440e41c41a42038281003940800036072201700410001c40780280442c28400e91281d0804007050306004210030503480d5034041c5002c14001d6501c000759950880d9005600c1040030384a110b0590a0401112844034030b9481d04c144141c41c4a03810703c041e07100fa160318000d4a17107a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 858244775 1250 858243525 858243541
    0x4050f1b0414130201120605130e010c0c15090807080f0706050f1308180d0318090203060a0e040609020303040f080c1516050304031b060e0d03021c110a05070608 71
    0x408200e03032000e464003e00340f2080155014a90a202c0c5030040e2101107100c0d034407400454060505400c40582280d0b5609a0701c074025402e00c03604a441c1091300c0e200c1314015590301c50201041c4549012880165900c0c0c00f1030811074800c2c2111a6540d010312010b458144213100114a50046441901c1444c28000010560741c1d00e101414445e03070300c1c1c09803080050410346030844141c00211410414000c4680e01003180d94a900200e0034042c8603580b020b9640049048001c89220203503c20804140184144610f036603800320541c041e6014212551402d640d14140500581418040a50035000008001c40c1d10780b3320060141c181c42d01401256100c20f05c0d4010f100b0102d040103074072001c4001c00c0c80108032195401e00701d24070003800344040300c3c2400d40360f0f160f800c48840c0009005100300055101007040d02d8100e030892008502c1201e4030b2840050f280c40280d165640c10141c28000c984002c01031640500034a00101c3c07060617241240c006c0401d80c81e00c070f90340e11407600400001c55002c0307000424078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 858246025 1250 858244775 858244811
    0xc0607143a05042004140a1b031b080406020909010e06030706020a08070b100801050106050315060901020a020910080102070c061404210305040b19030b0604030f080304050f1b04 78
    0x100d92010b50360211940184031003030560741309845964016283d820f034802403411004c80c9070207a12507010005081c011021004110410031801c001418100030228070490303000c45540044191604144a0700e60700c038601540248030382404540d1180403400085007051000d8002c40c49480c0640c1100c05c07141d11030405980c0d50700182c1c0020b01d421020418880090301d41c3c1d50507034000003100000028031351100260303425903034241c201400207100803041113018a003100e40350141c4882a40e80c2d030314045000c00002e45071035141801900443c5201c000c6030001820000e40001481010000c5440f00080d1034900c82d4503482c0c0c801c0d20000707100c3d52130340c4d04551501d6088034210b5500150b207800203104120b00e85070751071220340c060b002c0c894203000010720049500700600c8440d4600c203000828000007076024085031002c00b00349004183c240810310000c4c0e040300c0b00d911250340000342280c40355201c3c98486c3c505000400b00c0c0141c0d00501c496100031205002103140541d100311802e10808408a00c031202d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 858247275 1250 858246025 858246031
    0x81905120405060403020607080f070f020312190e2b020a0b03060901031e0210020105040b0c0a0909090819021e0a20030a1b0504110c0607143a05 64
    0x480389013004100018589a80101000b6215003031190a09400004121054001c070800307a6941c01128800011441c050000c0c9480411180b0b20a0520084c0780d50309120300c403541201c2d070074040710640004081ea2405038a20300303000b0003c40d03016403c0b034001503807a4807540550120302856403640302040f02c0c0034190960744200b10162000515a1943d215542c070a000c0c1e6526041001368210303207901503103030b00c2e120901e1098640c00102c2c01d07050528000d060541d00403c0a03650030418040407802c650320155010072540840004035074483e50b410450418402c42c0d103035500b0a2580442c6110150f00400c81407941034482000350091a11503242c2a19119680300082542d0014201944550200c401d8120f4801d0090200d40c0b40d50310f1952050b0b0040c4036043c1c20522010140c0302040350345440d028411440880c00902410800c01e02c003001e640700c1000e843c4000380040c00304402c5500d0420307010b581c6503c41d03550000c5a0301d0b03150360b55211f11601441254040301480c843c0107405100901440d80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 858248525 1250 858247275 858247279
    0x71e0201052b140105100f05030a0b0a0b0427090c060c11030a0803061009030209010608072c01030e0c0102060c0f3001060f050a0302070309081905120405 68
    0x11400000b9908074070308140070a410614921492100c114501e02441407110441024403800c0c3c080d41480c082142c15000d072940041089410205007002503400000d585e000707904188007041512448000a46030b40d40c0380c0060510302008600001e112000307000183c5100c001c0b03020790741082e04042e0954156030007000042e02a09104404110300c2c1c1c4251048041c490140381e8100b074400035200040c0c14021040d00035141c2c40b0020042c000340d460481c0448034410624142846010310715404600280d4052060a060082000c00180510b014402941c0d0244020a07810a0700c458222185001075074651410b0000740740c80c1c4455040000024045050307503058004102540e90b80841102ca9441400d000118070428041440c0807404ac00e1070940c00d080200012480c0d8480b4400d000003950168019010040c038051850203440d0440704450b480d110380d290269a410041c10305581020090744144017901c900342031060801110400507542600c200155401c1042114801016000302d0013a19 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 858249775 1250 858248525 858248527
    0x20a06110a080f19080601092909010c02060a0815010507031e0201110a12050f010b0403030807020c0a06050d1b05160c0f03080c070503150f070e090c071e020105 71
    0xa400b086801c4041e10380c0b1100c5088007860400556000c903106000703030001c90007240c0640d041c000b40e5a00610110050b004120912032041c5d038410741e010340d822a0440c65106103400241020007a4071400303840f600d0b0f0b90042c101c1940c900c0c514900138841081101d520880303030b0400c1c0c201c0c1b03001c0d07108000b00e5080642543c0d4518508000c1e02c480c01100c40c546001505541d604d0304c05010744600709002e040220141e0b03c1d544451503224200e00b080d41d000800201702605000d0040c414117501c030b003e4070142ca41625010101e80d60380c0301c090b07150441c050301450784414103440000d44a648030009004a01100c4028088100d10030280c0c110030039130150080200b1018410442100f014070850307041ca6006045020300d40d5034070b404020030021a03400030fa0b102400000d4405410780308000e50001800160010304103070280009102450102801603400c00801d0b10105480d10302c50560aa0003c1d0001c21498160900c44074151003503200f46400c50300c4448031b8501720f000c0401000c03841403a64043c0c4840d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 858251025 1250 858249775 858249793
    0x20a08030f10090606120509030a051c0b0a0909030f08270319020a1a013c141c08040504150f0b0d0f020715050a0b0913020a0611 57
    0x7840440c0e0000c00720b1012000d0100c00181ca0a914003541e0014052612010241c1c070b20940d07001c0903034400400d16415548100245640b030381d4000111b40c004042c4406958060000c42c0e80c0380054151640030951003e84050040b0f0400d05c40c4c0d000d92480d91194403500316181072078000303a440c1d03c001c94000840030520702c0e4815203001d00e82300031290801c440c0e007500c0c07405140000900c0801d082d90000350040e407040c0340403030800005060f02502d110700b441c440c015a6240c100b00410445500e8500c102d041c04401940844040c0c00001c20155880c1e08880c1c080140c0700c80d100142150ba040c010343c4181d85816089180030002d581d8092070b540c001498515103410142888040d01c1415018040e8200f03030000040d0142a082148002d001031502d410754a003049034054058460034910400280d10400c03a820001e0900034648014045406010800e566003c0315032300200020001c058103d41030700c0821454a6800000080c154403c654440c030700e64440004903001c0d1034107000000698469048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 858252275 1250 858251025 858251041
    0x5010e130c0309020d11092a092d0415050d06020f0c1207150b030c0409080f0a08040506250804060b1323060102120306030a1a01060906020a0803 64
    0x80301c410940c4600b000b1030707a203034035034041000800800710030f172060b00c20f8141840091820300350460304210464400c0d064a01441c0c1001a04254507403001e1034414000341c14000c2d0349401112501302c00c0e4045601e0088001e82c4041041040c000384141e100d5440e258801c03580c13072000340b0f60f001510009009401140915070382d83c0025032020009145400d4240420b0180755010090138100c4c4480c4a2555102c00261801c10071100c2e0740c0b5001190300e402c18420500c00c0c2c034001a810003004003180c020811310f404e410184450311800307002180e40c41c030000d070b2103000a4000c080640124030960071180c0c070f46d540000c140c0c9100c041002100011010314425041580701c0c801482d0401d00480001886d58007010000b0f0092080003140d0803e01e840310388558489130000b00c0c280342100401604100ca03d00070340001d44848401c908510b0850010012903940d0f101005200c1d8050752000d14202044290320400f500223100744612000030703103810004603a4a1003c620300c0000c5a0203042d403415a114140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 858253525 1250 858252275 858252281
    0x2060610030e2817120a06060e0120010e01090203150f04020111030405100309110111060c130b0c0304081605061603020c030a080315090c030103061d01020705070f05010e13 76
    0x406030815503480f0000e007021925a035184961000b03401262940d0301301d02007044200100041258208034030b84442040695003010340c13500c940909180841858065840d500c4080c1e0400f1404851580b070a9100c0c00d55800550100c17460900803002c407541c07040c0342600c03600080c000320f8500b008400e850b0081001940039009084c40c600c54076003920300b0140c0b03d0f0003103101c101c3e03040013440029454002c03400506c0200075100c04150f40030300e0217102e400f0070382d2440c2d6654280a4140c203602d140009290b80300292610310440a010701c000e4080d990010f8000c1c16959411070b010341072043c01111804400035125003400b5080310300191401c2d082610314401030006010820094056005547d00c644440e98103004503650540b00e80a4070f82c032420803103004102c030300e22007210600a6200d941449006001001900d04480c3d0000010480700051024580103926901900001e580041001c0c01080303c045050001e0b80c41d900001440980d035a4011100100d0130326000c0d800c26040e00229041a00c0c0750 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 858254775 1250 858253525 858253573
    0x20c19060c02150a02010903090509040c140d0606030f1b060903061e051311240703020a0f12030b040b0d020f010e190e010515031503160602060610030e 67
    0x303080c0000c020040c3c00101207a48600c04490060b50b56880550805800020030b0000d84000c0d1821070051030036a858030f03004040d40c0200701c02200f017200408140c0e50740b44011202190311400c1170117021380d2890110301014007610100d07a9160b040940012542c00546110b00b1604159a084802859030f22040002d09111341040e1130300ca03510346187c3c4000d2060140a0068440c400001a6500c1c242801c040c43c0e9851030186103d03d0040c00e102d06082d50021038103000450540032240d031400c81f0b2170160718150710050018503504905d4002024800742d00152040070411751000d0040c81c5003d020082120b454215840d4040007080d011000350a0a81090340b0808060400801100e0381c3d100003040e4015000e09400014005181400215104026940100010784090185880041030760a640c0001000640d0078000440b0070551a41d0401001424020a42d68420b00d0358a031007009448031011a001405143c42d402a401072501c02c0c8110f5401070680c50103002c11400c00c6807091724112404c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 858256025 1250 858254775 858254779
    0x120503120a0b180606040905010e250f030e07030b13060f181202012d11030f0402100c1b0608130327050402160c12080d0b03030c071401020c19060c02 66
    0x10f2001103241f0b1040d110310340c080c040303091085070645000c408244130348a1149840412501074029200d4186c0c11007411000441a801d000c2112904034011a15001c06940080c041c520210207205480c50766600b444a560f00a80d814448180c0a401210940d0714507108802c02c44003450600c00030480314136409045083d6440045070f910700c480502100c9288192603103654208035000310300d60311158403a8034201d012003506a0704625140c20200f1103c50001c0000e0301803400c0c82075000c041d80c403541c2084455a031003030009401030b08040900211540c24041e40e030204180f0170214090208100c00c900300c01364940e8810350800f100c404040041e144100502c94182c84201c3e02050503038460003d0502d0400c0d402c0b50840316042c0e403c203102e80c4941036008183c410b4581040c0300202c2c1121084403c120508800422040c1b101000b280c80e511440d01890028060b0580c0400c6400c1000070340000c50809a08443c42000703158100208820320074291045400414030810985003e03002c90301c02c003400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 858257275 1250 858256025 858256027
    0x10b030408070204270b061206060f06090d060207060f0b0f1e01090e011502150106020304121a0a0e010b18040605040302030c03120105040501060504121b120503120a0b180606 77
    0x10b040c0250410650040843d0749a81c030320100901e0742000f4804508e00c0d04202c0c01458542404008142c0108160030b425000b440005504034a85c1c075008910326005c0d83c040c02c21580c4158909100d0001e0400d400064240750074089030105501c0c00c0c201071660000000c140002c0c40c11004010aa440c50718040740c0c2c1488403000b40081e0384c51356400f4290003014282046010468400c20080c20700c02140e40751202c003030540c40140041580082500c2c15995113440556104030f080c10700207440c03019120b814410590300700400001d56807581004400440741d1009000c0030410104009110800346240c1c4040000100080d000c04c01c1d0b46c10068105001c0d00550780b801e243d00c01050304580c0f01c0c00c9001014409480100325900301407161a00405e0b591070b107035040905284c80c4401a4203055000790101c20361074017401321f1002204080c0d00030300880d000f00801c12058030b026500d039008810341e51544c6124400050000c4018011301007410f0006040c0303181c130201401210344240c8050b10f05508940 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 858258525 1250 858257275 858257321
    0xc0c0d020418030309060e0f0a0b04060b090403120f110913021e0a1b020a03060f0e010213050405100806340e03061b040510020c03030708030f010b030408070204 71
    0x200080101e02c2d03500030360b0040391080c90341c103007001980c1007002c0e01d61150344034580c1d00030070303080114401c3e0400b03500074201c9a06803141d0505502800901500903030000d600010700c020150415020440c00b184043c3c00c3c08503420400840c8103c0c1d20742800031005e18410084403005203081e0403410300c0001800001400c0c05030700804c2100e124041c40c010009040f00040e252207081c2c004036145110180221300c000640100e6011804103061803000074981c0f0386540740e61a0b10a4a41c008070a0100501c1c001c40d1a0740e05c101c6458600a00d500ca400e005a140001052111000c00c0000e02a10541b900808190320303034200d60072031280c915070801c08441c2407001010401e01c10aa203041c00201940d03425004a00b1181010304104014201c0320f81300c402c16039440200c0000f9019607003140c508484801c0312058106003681408134442d0034a506001c0002d580c0c00304a04080a980648483e0500110580c3c030354000d0301c6c880c0304c151030282c51080b00788007801c0107140503000003840709a08407144110174 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 858259775 1250 858258525 858258551
    0x313020a0e0f090f060103030507020402091809031b0a1101051e0f04030204050f071d01050c121b070e060d030302090306071709010c0c14070312090503070504020c0c0d0204 76
    0x4101501c400408840b03540500c00030750020481885101c4505000d400c030f07549507030b5018185205d054802801560045104021a9107950300c0c0311240e44060a0807200d0702e0420015a240e40c0302100e0544030002480c1d800c0c50f24400000c000303640c2540451440c180c10011301c0107690ba5040360860003210400c04032110788104452028164201c105001d00d510b0320b044d071040105440e801441050000c134400104150a90301c034000c0065014817810810350003e655004079000e1141500e140280e100e603008d01d0380300603203040007040c1b004e0308500c0308025484182c001d86d03100d101c6440b800d2051f00800b0046611071802401220550703200e4200140380064050100341414000c889000100304418040da5086406100306a40002850001c2080c03c4000d071015201070a48140a407013075050309022880c407007003040000013564101c0b03c51260500c0440000b44907070010300400b0b010b401030b000c3c000303590304060080d2005d074000b4501900e844d5040f0804d110340103503000800c3e031b406038954068003141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 858261025 1250 858259775 858259799
    0x8040602130503070902040e01061d09040507050319050f03040501050d0510050d060b030d031107030e13020c07081005010320040b120c090105060310030b09160f05030105100503030313020a 83
    0x70410b85c0000758683d40b600c82c01c800000416485003040c05408010143c2220812800104201c41281c6c2c00c4983e44440c11b2462800382150080c2e0f806120304020840c50103003040c0d42088261140c4110b8680e441d62850312a12400342e4030903940864014070480540b4511a08120340c088400755401a1182e41c84000440c100d000791015264955a01d01505d2641024090000c0031aa1402e080c451002c0a469203602d600c00c0030000780c100940c2554200342581c440c11500c080f982c004e4025511081c05521f02078954440c0e21500442d0700ca4080003141158803800707001d040780e8000307041c0303401c400208101800251102660b01d0340507076913035980d0710300c0d0303850402c122441201c0713400900152403404184007036020181c0007180305240520070031150f803105000300300a40c0d6103e01d018182e03071615003d4521f05080511070311803049039000c020804c01c04d610300e06412500b045009000ca40c9448251050000035406415019003080000415240d5041c041003071507440071749103501c100d035a01111700c1c01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 858262275 1250 858261025 858261029
    0x150c110303030c0318011116030504050a030c0509090610060c08090306151e09070c020d06140f070516030e030f01020c100632220c021009030804060213050307 70
    0x9040c502000340417803038200880360301c0941c1c86100208480d16060090601501958071000703910f50840390441c0805101e0411ba800600000c2c000403511500d0380740038241c8460303034050b850080032108001610300340009913040c0234006403488841c0040c1495012108403c0490041c5c408a10802082c02c41da141048401e1240a105800410070305142e4200030f40241d941c008442d4505a0072400c800039034904104e240c2200709e9040400b150320080c40851003a400349100038021515150302c000c01c0c0850f01d0b00c03039442803425103451001c944d0350b28800c3c0e0b0503000301d030322469401040c0f41c01440002d0080707400b8402d04070010212080c641c3c4020041d426640408050569a00144d180d41c4a0711500d002e0900a0000e003940c40c4600602d100c501040e02e80c0145050918458511030150140c42d16404c0c81c1c48600355141c1c140040d0003601c845405019420001c60051044e502c2d15a45200f09120703c0038840d50540c3d402815441d55114003020b034001104071101216a148000b8003a81d0411180e40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 858263525 1250 858262275 858262291
    0x11070b01050913020303031f081002030f0a02120f1801180203120a020d050d020415020c0114040513050405030409090b190c050f1305060f0d15150c11030303 69
    0x140941c10320080c002188009488908291102c2d4810b800503a4044142c0c1da000071a00741032503402c4842080d0020790306c0c0d6907102100b140224210b0f036000d25401d4006522480c00c4105102d8580c031000c9840d402ca01c21f25418010721811400440c548100038013101da0007245200c00010540500c00c1c0c090700316070400e540c0215140304410721004504040c020b1410005032394a01038100f8002c42d502944a000400980c420408005841070029034658151409400210a10342d801d0060f0400a5603465071030000c00c0c04214810320007030410318001c0864054a0340a0035400305000380f42103030070190001520445c3e160000b4000400c0c41119881582002400b9071030010740c0c0e0031320855071020f4001d04044907200c2400c019001e000745401c0700846038607c030340d105400d80c0c4642c801981c0404c500d0310340101c0c0d400400090b601d14266441401b6112035250302c0420004e0078011200403498401c10711900200340103000c107103910103000301d46e5454031900490141c2461005800040c0c2980e00032031340c0d51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 858264775 1250 858263525 858263543
    0x40611040f090e0115170a051b010225090c1e090e09032703010912030204090c020115030b1801020301062a2609030a050a050c0a0b03040f03031107 65
    0x81581080d00464850860280080180601c2071000e0030505c0064000c081b1100e16502925074520f1040010049294200c0242c400c00000100d0720030084241c820f00703d005104050880040b140010b00018200040c0b03801c2d0b43c003880c50041c0c2c3c40c01400c0a240200c062000200980e0010502144a1071b20b000c1941c5c2c8906456090041181c003400001c2e115161950090011460b910b9004104041842501182210752803459001a015003102d80c401408a00c1e00c42c074034100a03800d50050301c10753300d65090500002800d190704908032130580300d034141c15040f015070404c00304030310003141504035140b0400341c419580498421401d9a00030f038440800102c20885100c40d41d10040700035048482c01e515942e02c10211525402c04804a07000d100180044601c40003920b040d07080100d031040b600144c16513910750158202281c070341d00c0c020010b070b550f405950001c038514a043e000e0302d0240c8069050950450b15241c54034040000308080c11010b2550720f04021900c07000c050090100188594540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 858266025 1250 858264775 858264779
    0xe031c0e03030c0105010603111c0f021908043e010302130b07020112052502010213180f0b03030d0b0112050f060f010306060212280801030c050a0f060503040611040f 73
    0x408035407400200324401c00c0304ac07001c1d200178503005032130380214000b440300810980702c489000d03002842000c00485030180200114000140c04c417031500e22480c02240c0114016001c41e00d440011485160900d0009140d01ca9120003545040441c400340c0d203040c5401800e201440c400c1c20031034180e03038202c0040084003150040466034003170503814140486584c244214141840c1304c1c0c2e40c0725018000d0441c100040009024090b00c00d41c1a1039884500c10f405800b107039035809040d20a00103000803644010300301590003034000c0b9280200815210081c00075403615000d88039102c010074030440228100081348a00000406050007880c1c040c11011400f1070541c00d01030100070104920340b4010781810b080c0881040303d036401040728885040c070700400030b80e00d9003903a2580c41c2d50741e10b20705c80d100ca405490410100d102d0717024608a051742e101d00c00c607481940c1c8400c2049001d200501c180c1c0f001801807102070000500c130f00042e640080c46507c01250018041103076034590741198201000ba10494181 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 858267275 1250 858266025 858266027
    0x6090c1903170d050c13120f060b040f020f0c250618030c090509100501050f040b0d08071218050a170c0907180603060e0402040e030d0e03090906010e031c0e03030c01050106 76
    0xdaa40106805407000c4a105c10990354230510b42100c4001030703e444c2d51406400e416441d1500142ca0360450703540300b195903405e2044030300041e0300600042d084c5071244040004000e103100140282444003504e00d005035514040303040b2406182d9065240c9944411180000060b05c402c0c2d8160107000c1012700070844e0f14000195501d01403c09100b01e16050030800100300c603490307a400e00c6c0c0e0225416140403800d00802c0e40415043c60b12294018a107000003e00034042c4040d00042e40505405030b0307609a049a01d03503844214400e00e070f00079a03500540c484401c00c190701200315000f44d44502202078540e41002400001d415103411a203038404190034a480802400d4030040c1c510280c031841c14200b14850400c10703020b080e0341c0c00500080c02255076101107810b00700c0c200141c86500089480034003650030340716456a1a034224169007402520b802020660940c01004034a00b40306000c1d004043d01c1c89aa030180054440c2d09d2590070034403414108019007070314140000c10011118038008250f551600ca0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 858268525 1250 858267275 858267307
    0x1c090303081e18150c0403060b0910140112090b160f021207020d020306010902280c0605100518040507050418030f1404030506090c1903170d050c 64
    0x2142116045080308100c045511a0640582202851206001d045035280da42468048081c91008030061308100300040388041000410560b440f03400103200b200140800d20000b6001615a4544000c05c0c0e802400029101c203a1130100700302c1490421000701d9285542c0c4111001c003481542c804000e101001044004001455842082440c0000c1c0c003150545e0000c3d1100d0b1a1680f285912a0004082d02507640e03024a40106580003002d0304c0e03c035652907542000a510440d00114950340c001e245550700c003519854002241110388070000e10f82d501d0781da075a0003440000c0c00c0241c03c01200e00c0c04640741c0c4498140400741039200180d04890304045c1060340c5841c5a6a02291107036043c00e80c40c020042d00685081c020660500744241c03075103c840020f58502291040360f1300b5141006c05e00200303228000801c40d00078026007059418050140c0c1c02c0c40074144001c4070143c03030140b01c031100304002401d280c91041b8500030b0440150500d00f0002001c0c003520001d54840110550204000101200f440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 858269775 1250 858268525 858268531
    0x409020d0b0f03120d09080f040f05010306030305180a08060c070615080c060307051204060b010f02010c050f070f0b04051e0d022805073c030210021c09030308 70
    0x25104502d05620000180c2d9541c1500941c4d001d82c00d012443c22100d80e26a04141c07100c903400000c15844240203464440d50b40c0052241c100c040380090000505135000348103000c2500c1d05641c6030b1b803800c104150101007004e10b26450350340004820342c00103032201c0240314090150004402c510350305c01c4c150810400391501030180602c0c840c01c0041c00c2103107220024404200f07490a4407016100e98a082003998103003d2144200440204c3d24100010012180c0c03202c50041c100f621218112082c200d4100d003207880c10a0303907601148042110300d180000d400054041c85204445000c55061195540100c0b0103058804071075540c4000c0c03082113400400c3c6182000400420000d020040595100031340d102c0d0001e0442c2024000700750064070380c03d06000e2454103540c004040f0340d48290750340b10101140d00f601c6000c110071aa5050303480d04000c101101710111310718145404001c0f46c00e640810035200003020401056104090180001e107217441c4034031a58580e00d8844500b07480c51814060401d401c02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 858271025 1250 858269775 858269779
    0x3060606120e1c0234140a050f04110f0301080d051809060a080616120b0604050f0105090a080a121e030903180b0301090b1815040b04020409020d0b 65
    0xa5508030403840b0000382002c20280c1c2d504078404880391044143d00740030100207031160007000ea01c3c0864446100e06440c00c4840c68010810486941c1d4101a00350350442900340d6502910791030003041207280603d20135501c910014800a418840116220700e298004201c2a14241005c070042200d52410310254a078030800303080161810841c140b4480904c40003400141c8200c000f000403615035104ca20b5040c0c0a4030b02001264003a09245a00e080e64204000c1c0f4a0001541400d101140f10114000e2409004001d8446401c242c01c050030071445501c100004c0c0c7c1007200a1100444551b9a60002001020548060090080107041090031010711a60072428401310b4400071012003103440704909040e410b858005000c21403403a0456500224501940c40100c0e201000700d0440251401541207400700704003007007880004014008100c03820100207d0b81c50300c180014089010254001c10424402400000d1540b0702c0b00000d0101c0e045078000001c8681d0200325a00c00d02d419104404e400201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 858272275 1250 858271025 858271031
    0x90b04020a14180d060209031e0a06092d15050403140306130c020c09100608070525240504080901030209040b27130b010603240306060612 61
    0x801c10040e290310055110300c02d00210003c2c00800d2822018102d026030301c0020071001ea03407025030805001030b41100004c01c2c4079004070350707044041b48201003011190401c060301404c10300c2c4d03054440d0030041c46000e10540395000ea006050302800502842001342080c10095581001d041e070816500b076a111341ca0304c0036564a454103000210313802200c0c1701c002048403810390740d49580d01004184c0650505049100803401c21001404a58020032140710301901075418480c40d80d03544a807045603080c288500d5000c182c80070003046040c4c2c8600020480d8000c504020b0740ea070048490001d500f0070000c0405d5941c00c030507080c01440d10034081c0040086884c228403d010380c0c1811f458809140c89403088040c103044c3d0008540000352510740055103102d000821303110001c2c594100e0368034031444c000704556284a481c00059400c28066268613000307078004e04564626030801c0341c26801441500300922850f103030360000d0501c048200c0400c00165110341c8001c00c141c0d01d0880f010b81492844042e02e41d003182 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 858273381 1106 858272275 858272287
    0x609030a170301091404020f040209180708160206070207150e12010510060513150c0204020304050106090f021c090614130308071b0f051204060801090b0402 69
    0xf0351000c085c040c07040d42c1c80c4103a086540845000b0b5118595a2072201241840e90141c4202c0d880604541c24556007520300305c80c05401110340f10001501101048511038400c85d0b066080001400205650b00340b00401031b40f99907190041d8044009102d032810b5070030344901440d070822007000d0403c071240d10007007903494080c1504454144241803000300004050384120120303401c42d4192092125600d04101c0c0c08603c840000c54440104991a100707580584d407503100940c0140e115000000c0c0780340c5040c101760300f03480c1240c013003100351032041c403400ca1a148280c40b0740c580d60742108000030310542c1d2840d02c44010103d031070111503c11960300400c0b000f051000c1c00c44102d64000c1d102c50040d035940d007400315554081300040f200d0859901e0020f00025000340d0321b4440d414032440c1616903c4c1480603410391150899440827001a01c0080104440c0016100d0315947c214162400e43c80c2c90 = true := by decide +kernel

theorem cover : BRFrame.Cov 858093525 858273381 := by
  have h0 := BRFrame.cov_init 858093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 858093525 ≤ n) (h2 : n < 858273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
