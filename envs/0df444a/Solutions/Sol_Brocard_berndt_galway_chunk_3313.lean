-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3313
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:18:03.383773+00:00
-- url     : https://prove2.me/submissions/f3554e88-29e0-433a-bd5c-a8193e05a632

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 595683453 ≤ n < 595863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 595684703 1250 595683453 595683469
    0x6020a0201170f0708040c080d09050418080a0c1e0506101212030906200405190f03080318030a080a0501050916030b131503020102010c0804050309060d090b090604050606 75
    0xb041e28550403e254032518000d0322110000307401155030280040700401ca03408104900000300100365a024811407070203040c041118012522010300d500700200c1040410003040480b424140c240c50006110012401c2c03503114819200e10310004d210f00700c8550307014003c000440354087d501241c01c14404940e105a6185000c41c0004000c1551a805070514102d500903031010b03c2c20b5000300004250b000c0450500e843e0014204000000198042814004c074102a9201c030710000340c4e6008215003600304800030f02c00c441c1502c0028015500000011050710212010988141819080325200c826000d005080c4c0d00d400c5071340856807840c0100018151601074926802810000c9041c039804000c01d0040703014000341c0c5070032900903800840c00c0c41c500c07001e4070039120035050380814803043c00c4c118400282074071007481200d070030880c150040c440030078004822078106413003c413a03042d075031003801c442c040c084c01880c00044c2246407000e0400043c0d140201c1c400b4441c0380305d2000c2d5009035980c502000081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 595685953 1250 595684703 595684711
    0xe0601060f080c0409150303021b01050306042004141806090406090201030b030f0f01110408070e101208192606060d0608030d05010f150e0f090106020a020117 70
    0xa03074401c80c100d1000d009030300994014450030700c1246000d49644480f0250742800452501040f50081d08105041d41402141003070a10350041d2440d1102c3e00000030000e00018207000d1140d590380348914101ea1201046400c209039050405850b1a500c4813081800007600703190700c1c050303200714035080b4094050f44020751040000a242081c0b1b0307225a100c490007400c0d8088100e05040d03940c902124a40e038100554841003010500030007020200b211580d0a481018000c003001c00c000780000d00001c0004a040c100ba80c907d1a0083c0c1c00d80e80d040d0b0a4460100d5a6000c0c6407a00c0f0300c0c003402018850000300070208464000385103491454402c1e011070340c0484610300840464a915540502006103080c01d54000300020407880c10304403411698401c84110303500074606540700040000f0207020074090300d80102403c0c0d4840301003e00c0c00d0003403550700c5425030747c0e40b040010300038901100e591401c8001c404500b015254019541c2c4655019581c0d20758150168081040d16001c1e10464819050982c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 595687203 1250 595685953 595685957
    0x219080609061801141503070905240307050a0e091203042a1a0c07030b0a060e0106090503060a020307050c010905030409111e07031101020d050f071106060f0402070818040e060106 79
    0x2a95a451b03070105680d8860f081c42d550f150040c03c0c00011600258003d0300c1c0a002800f02500140c810369158046d1642205802170207a00480c0c41040140d80300761984003140c00750215806e059480207081c904106c448840004e120101009100520040014218050507504008e1a01d01541d41003801c6461141c800c2126450308440149000c040e00e5001e001004204c00441d41902e4495030b40040c01e0700c040329200c041d5981da280400255000c0044a8014160703410880061800c0c2804a600c0d000000c0032100c0d1150008040b44082c1e11510840301304104202c020049540940b1b0035903105e0740716104070008103051180c1c4042c09207580c400c03540c0540701840116074013a8058541c1c1150341061a094091040c0c030909803106410a000826030005e10400c00510b0389003001654814550142c0303c0da0422002068102c044040056a1600024111403000c103040110300007901074440d101c401000290041004240104100003841e9800d804940a001e00c481003402c4c155118002d20810b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 595688453 1250 595687203 595687241
    0x209030d110109020a30080904090f081b0111250606050a120308010608061806130f0506240a0f1e0206041b0609030219080609061801 59
    0x4005402480c040d00384404800000c00d000d00343e9000610044065840000c200444072840c5811811100400030712085075500600011045e85070a0040d014200c08140100e0741c40800c80180301403d9162080030360b000c3c108580c0ca40100c030611202454002c904070f00366007009202e20403800d10800741c0d038a44800c0008081103246509284850448680c81547c0b0a9950340001c00e55031981c882c87c3c40601107481540000001b0703460020306044050b0300040400c204501441903035504c0403000038a166030008040016210200000c002003541c2d1081440c05141044440f54818203410041c0304503000c40d9400c20104401c954070a45c0275180c0a00d000ca642c0410400144c41c0c0154a4115500b41614203c1090a40e040c0c1403045075403084100f0015902c004208010405200940c1c0d095041d1001700114952420f50b01030310000741400002c0c45040d180100341581510350b8460340007071641100300c452509040707000c1a19603900761010150700c810483c440d0381a0030140100c0c40141c41e02d0311000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 595689703 1250 595688453 595688473
    0xa0f05010b1318240207050a140d08010909170a0207030c120f1b050a0e0412030e100902030a0c17100203070503070c0812092812052208150a020903 65
    0x1890900c3c1e1001000075051444901d03210502e04e8409000c17118407400c000c1000c0360060030070750895203400d00304080d81e501040280b501d00c0da001007414110b542c13000c0e02054502842c500340c0c01141c5c0700303a600d0b030400d400442c0c800c400365070018240c02200d002d40030104a9035210a17034100c85d0000c044018203101c55040d1101c0010310100e030071144034403020000343e0003180c07540d002030036040c00b40e481111222004414001402a403059451101c03100c1d050400490640e41500c544520b00c104401880d1039840804600f503480500100c0d403400d6002c080f800c3c0b40ca445405000540302c07070900d221000d00c5002d912500c45040d6100b1280130341100d0311801c1c01c0d40d80d481801c5903888001c0307008843c2da0209211400ca15090020410b0007a134900c0090803415020f9144072100e000a2244120070008800103c0007191054202042c6c0c0703034140c0b80c126900c91140f465004150020010301e42c0020b00b000c8000f80c501c0c800309111102c25540c240e852440d48070130720103805a0062042d19503160300724441071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 595690953 1250 595689703 595689713
    0x612060f0a1e03030e04020c0c06131205060109180b040618140c030c01030b130c05070c08030910031b0c17040902190504060c030509030a0f05010b1318 67
    0x25056494018140307161191034038110380d01e0740c803808031409801c403504105004041d0040326071400048155030450502c03020b150b4107599440300300f0309140141d20000e14402d02e04019032021024281c01e80d041039820015290007540ca8034240324032080c20345412404001c1440182440d0340194120f10310300e00c81d455644424000b01240046011a41c495001190015401e511940840b400741c81c050244003030715005240c00e10f804e041d500b40c10985882d460864581d00c0140c00c0d50002001a0300142941c040e0348296110302c03488101804440c0030030f00c0042e0181002000301704004050707070000e03540164a1000d9040d00e114610b503040d40516a001100980d03c03a4001040250041e44560075a40c1c15040303041c00795100e90040d104458000030058182c0780c80c030705402c0c6668502d2070034601e0b15160040060840100041c000c1c204080000d17444040da40c03c00c0100f14042d0490102d001ca4866403809600030810301d148540500c03510f1100452100e441d00c0340644402c59004100d032410307890350b24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 595692203 1250 595690953 595690969
    0xc03020f0321210915154905070504050c030a0915020a0306030201020708060c041703040801181e0c05060d0e0106030b061e06040302060a03020d11040f05061206 71
    0x1180e103071405480b08240302c04010031844c001d51003180906041d41d1150b8014181103030050455288070003050000e4510b46812070281c0b03034042c4070791107a002e00e0040c42e6100c802c004e000550004c04070111480503044224540000d850341d100d0002c40e51040e903158140407e9031402c4075190010728090002941c1001641c022100240c4500c80d160f54144224049a08070b0700b080340258002651070708244110350301044280003a1803d1300080c101d600e00071550342d0f86131086004822201d10749105400f44001e08100399000b43c1040b100a002c1c40070075501150b44485504400c0c1d40440b1401819440524841140e50303140e41c100510380c20b15410801800400d43c00f10000780100380d41d41003011000c042c284502d002452181d0000070040c1420020481c090030b00c030009180704005c0d00c1c20321465541d000f04842c00c07250705981d41901c8240e03184056000b8081d014071484242d0500d0380c1030b4000c5000c01d004000350340b00703454071442c8140c030fa4080c4900c0740140300041001800755000700c2c81d503182050f2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 595693453 1250 595692203 595692217
    0x30a0b06010e0a0905091218040b01140c03250201091e0e010e0402040b060a1e0504180516020d0207030f02061903020711040c0215040303180c03020f0321 68
    0x180508401a048049a0781ca82a5030003040b4095482c011b01c04090814081020030300740c0101d4080c1440b060380b00001c0c001c1c00080b850341c4036070780d10b184401841e40900f003070030409801c01e40126103c81420244039281d1388810f61200c1c0049803440d0903180740c44080c080c0802550107039555903c0e1403e01c01d0052401c0d8000c8988102c02c0b420120000342c4891160b0058081c20081d034242c180ba081503c180400e81d00c1d17103005548250001d010400c545d03948a2108070038841034032054032420f8000d800c291583d201c0c40d00f000c0342100c2201d100300341544032500070714082c12003ca00303046255070a440403070319888449044401a0050881007010070028019003203420300013000c4500d040d4107400c0608440403041c0780c2e50701080d008111001441600c1034150b41d10345088c2c8040c403480894150003900d80c0502c8800d400803568017001b003814940b00f94481034900745c0d000c0c035010040e0034500b0301452400c2144012072080b200b445e144a400c0c01e0103d102c40c1c100f50981c20100042c2900f2a90399002d0300308030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 595694703 1250 595693453 595693457
    0x6200706050711030d06080606061c1e0507230c100f02090d150e0d0801031b08071205070f05010f0c11060304030e03101a040c090f06020106170a02030a0b0601 70
    0x400d55004241d0f050000f40844081a54000b4403180740800890401c44000d102e140302e24018403045c1003003114440d50404019160100041c0c3c800002d4820355a071411250311002031385030004001c489038005441c140341e800d4444070981c07507010040301030b4407034030884401202c0d83c0c0204541c081c40074410381240600100210340542803d40301000300b508100088000d6602481e141003840804609108001c0b00000c0c0c200946040031400b007020744981c6041c840101091101002c600e082c1b203403d1203203c058144901950a0f42c3e544101983c603281c802da10640341d034011441e00281e4584600b0385081100c4041c0c4401444e10102001550b0300c22928130309a0700540e584034a281a642d402e4002c61041d886504c80f4000e4a10380c10038146899114500000300380d01c0d008010b244e080e541f0300e0700e00320b811048a01203010f0b5441201140c084000741e000349900c2c000504007098440d0103401442c2581d80c040000d44a4000b500c0b0001c0c1e561520708000b0713405410070508640400e008001c900c0e0b10880c18 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 595695953 1250 595694703 595694717
    0x20041203020c060d0c08011406030610030912030204050f010503090d0c030c0c060201061a0304030e0402030a0b0a0e0a0b030d0e01120e06040c03030801050604030b010b0304022b062007060507 84
    0x100045011135109458058200d0f40c0d54840e030314442c0e0041c5400703000d0a044000c81d070a404a40300460490700c0003924281c0702e030800020410005210f0381001440a900c105000800e685252001e001f07500b2030300039584500c2d45208000169413043d0f0990303100c0c1040c41c0041200400714501070f00d90000c8000240e0070032402c0d891540214842d441040010465540000f8401d803400080c1c100140841c00d100707600143c10410300c00441d601c0241c071000a00202c2d00180d032500c982c00524020480440c0300c40e002403041c0300010b040010600090b00c6154441000c0c0035107880d1404058507000e01010004c04500d04c0c2e0310340034940d403143c1134180a56401e01e400040944001c0101d41c5800300c00ca40844151a03594400e20405d40c0c0010028014441510024145030a40d41c034a510076005000303440d614400400042e0541d610114401d410390b10f00c0600300402a601e8003254224060b4070010b40340203041179840d5100c0314052105a01e40314a641c65542811703000e58601c400b422000d0304000412011f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 595697203 1250 595695953 595695973
    0x1a04030201091a161e08070e0a0e040b01091103130206072a06080c04060c11061b0c0a0302010804020f030a080408010c120603031b03021203192004120302 68
    0x4000c5030b000c1200c0311040302c40040c80c00c4c0345040386001414030360404114944000c2c10107041007440042e504401c030705104ea42592103400845210f01c0c0d501c610703a803018610744009240078040088a008500a08400c0e03196a03d4014641c2038034915082a001c0c40700030400208480008200c0d40d40e01c501c0140ba035894000680c4907800001001403803503540784050b00c0e80810b0b240d4480c02c0c4200802141c1440450740c43d044001a01c24012449244180080042c08504004488050316501b42c0c0c001e20180d1284c41000200c0f4070034004030303e0a009403244032502139081c50720044071400c41340e05a4612140d59035690034091141601840d081d01485203487d403c0018540745e0141020340742d00000000c541e81c5441d0010559140740c4000000245000b1003480881c0d1700c41e0140d900c44249107080584812145002c80c50a002400711441100002c03060102c0104440203443c16070488031014000300d80b055a03112001c040b680903403040360b8010001080710701c8440701c030041783c0d81c0640150303000e000f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 595698453 1250 595697203 595697213
    0x20d0210050c120309150103030e0f0103060b0c2d060705070807060c030b13050c03011a040909050c0103050619140307091107050715020a031b050d020a1203091a0403020109 76
    0x81042442c0f03941c030402000704910960708100c802e280d0f0003c26601d1000c0d501d0744c1c030040c01d00098580e8150050f1701c1001c4090299009800c104020f100040015903101c11305502e079500d44102c1800300c80c401c1c0c01c25071114181600d1060501c2105007180c017410894666000c01c6d12298003140045482d24400d109082c04640035100c2e0700c0340c0c0070bd2918007051810140b0308125a0105016058010520781814002c80c036191700305a83c19100603c4047c42812803901c0520b246005a9002c94080c0e07040c004a08100800414800084242030704c0601c01601c943d02004410002070a400308000030503402001a400580141c508402d0064151001c0607180c03589041602c05141002100c0000020a40d04025041029200805070143c5031290326404100094442400c03507005003c0062420b0a0002640040d0000009d5580002160044500d880003e034803942c20320400e5414200400810351102c4c00390048514940d405a1100002c105588440c0385044010303000b0340840d9603550f45034001030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 595699703 1250 595698453 595698463
    0xb010e0d0b062e120b03150f0702011805030c07141311130306061a09060a0503040516170609030903030d050405120f0304140c01051206030c03060c0c0613020d0210050c 74
    0x40c4180c4e0320f900b0319902c41201c880070f07038049605140c040c2e030055450703540080b41d000e401a0002c3c0401a11406a110f4030f40490140003007031039003180d000340c6201010400100100501603403003485c042e42c00c5290b403105840f0000940c54080f0b50070030b04c0d0b03070a51141f5404550010a5400002080a0a100c43e07080039000a618a80080b105507946030700c10f10040390b600c2e801c070103e4814125081d19100c0020040783c81409000210000c0c46008400328040040900c01030701c60b50b8009411034405a510701243c0a4014080c0542d4881c3c0181d5000c0b8500d03001c04000c0ba18480d00140007103150480803054880200001082520207001e0010b09042481c109402066107103003a120745a200d041c18140754505800000140000340d001000111441e40c003c429078004040b4407038226400c0d076454010a0074020326522a66060013207000700102c1082640c080c021041030a81121a5036a81c014100c0d00d004503160007039408000360307400400510b8030001802040b8080c6c40c2290801c840040e85e0343c904 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 595700953 1250 595699703 595699789
    0x341205010b0d0b09150d0c080a0303051806010303020303072d030b010908060601090e04020103091203020a110303061f110d080406050f13290a0b010e0d0b06 69
    0x210780002d11810201102e0240d900c01100031115241c25041000701d500c85c45480c04d02950281e0504003583e014003000402c1c813001098580e09a0301c08455034a0020014001180c01c001d4005214240d40c2a0034000502c05050303070381c990011851611615030aa50540d4205a4601c00740c030b88400081c032000903108031024102031038501054883c4140c00140c11a40c85410030f14031544120100310640c0ea00541410031100e03c0714268043e920389000480c0036200d00c0c01c028202090300388031024010f41c164010198404280c0d200d129496244800c141ca92105550309076000c13038607034190144180c3c1c0c135540d00021545410000c1100c505407180506103103042c2c0c0c00f40041a903080402044c0b000501030154000ca284050035120302d001c0000c0801ca9142640140607030916034012445910340c3c804c0b4000e80e48070284102d80c50f243c45500c0703602408801c03503003600040c00f000f4a52070300d0825560600300d0310f901811070300680c0ea6442c1400001005906040341c131031600d1440003d0041500500c0d026 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 595702203 1250 595700953 595700969
    0xa030b01050922080a031b20150c0c24010303140403081902071802030105040c08161b060c03020306031e0703031b0503040b0a0834120501 61
    0x4158505030802800749001064aa400c040c409100e00301c64408103044580c1c10382c05504545c0780e04952004500402012511201119000b10281316064204000e104c08007803214400344845c100c54007181e290712550604032001004200400d0482c422180034114003d0182d04a5034a901c664207010701b44041c000300441c820400c0320051003850b5026202d602d003c074404041034501490365862807814440c0660322000000d02c4103c103175206109001140050021003041402c2d0030185040e40020352080c46814440e9190000c5034908074020881140304004100e0003480101e0210403e907401e00c0000c200e4081815101250382c0002d5061107100c0b42684903a41c0103071a898810181454001494004d411540340410300c555a000002040c40660b41d152901d030243d41c403118800160002c4014000b00303a40030105001c181821004003400c2c50118135074880c103107920703410106403441d800304003805140108802d040c280360100288200941000e4070742140000c0000109004803a004e03044454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 595703453 1250 595702203 595702223
    0x40e040b07080411042a0306081c05040e09010b030d050301062d050a020109020d03020a02101b0b130b0405010501141801170304121a010801020924090a03 68
    0x10a1101400080340d00202500b0030300d0341da003801c0c1c80300380000911405107440f664644410350a088016032070780e90800711303000b4842905000a1406400b610f032030301401c4407500c9011203110325207411a0092010450b183c035241d20b490704040c0340500405005080c500030b5900c80560f24038030388080000d640040b88031340e946e030340325410448004c080080200c84850345040190b10301c0700c461107040c501e00789181c16017001d59903400044010713809000e288802075441400c584000c030900d80c003c07071403001c0c1610881e00d4088095400c102510a04800c084c401d440c8400035a01500044164106030381040c2001c0c203803401100319640d021105002100c0840325651601c00401109501c0d5178102c5658404440c06418211200459619101b0521174203030007188020340b101120509008840140245811100344c4c10340034100280c056800034008a884e01051300000b842e180180300761000990002c107000d1881ea041c03080030f400004000c0300701c03a044808015002c15a0784079880f8400852082c2c0c0744407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 595704703 1250 595703453 595703461
    0x5090604021b060f0f070c03020c04020d0902090a090506060a0308040e130b090706030e0109020105090d0c0302090103110f060903030d1e020c010501090b01031b1101141810061505030c0906040e 85
    0x1800682010302200103218041f8800f000003034000c201c0550400d01610016100e45e110301c071240c09003010300006900150100b00340258103c02d0307001208000e01a208680b0140ca5501c24816404c48a11010740500e0080c003041c0100c45160700b00380c3d00580c4481268110304001d03100c0e50000d0509030358507012a8010b900401a054060182c1600081d00c00700804c6446210303000a407040c4030742c0346864460107000901034100400300c2440ea02854000c1c00c42c0200e9a1a890000001c03400500c0c464031940c074022580195150000031a206131101402450401d0030f884501000380915804107980d2641d12030005686081c5407019108441c3e042002040a51410007500101c13500d0581c4181054200510380b000b04072049c500c00a03240007841c0004004000003071241c0142010301461a080300b0072801d100d072410803d032005035280c00036000d84c0c2800100400100450b032191182414072440c80b281c0815076030040000e554051009840c0c1071405001c440001c03016072040c3c024148443c2003030244 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 595705953 1250 595704703 595704721
    0x31213050913110625050f151b090d20060a0c1104140103020d2405071b12270b03190c0801120213050411011805090604021b060f 57
    0x2c20f00003030b01611401d01d0021402c000d12200c0004114400c00540702c40c1c096400c11808001010614600c01b044c1c5200031000e0920034940754013030f152000c044080401488040420b04200c0c0c3c1039000003400d80510103525500d410300c4201c6e81c0c4007807000341e0071540101d0994590760000d0200881c103580300c0c1c151300140c3c0303000740c00006119203085c0510320f040701070641000c000c445a81520f40448407482020300a2500d0181034225000100c420701c0c0780800c05410000c40d808c000d0107594581c0b076403808a40d404142c0815988296405422140c54000d141a02030041260400400c0b0742440c440701c9402c4922151060301c0310740c2c0310040d510b07400000c0003200a10f0316100c0742c9081110308244008060400c00a00c2e00b01e06004144070507002c1c0d510b0000310f50390b20078400303035585224805028620f06801e00240d914141c21040b808a003028003484030b295100282030056500c018600e80241e110b500a000085d00242120403018211340d555280c0284104080c610a02070400580d486290510314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 595707203 1250 595705953 595705973
    0x201140403120c021f0b210102030412050a020714010507050105090d03060f0602150a060e0f0106020c01030e070b0904110f0415050f03150a05180a05070e031213050913 74
    0x401c0d0464104034040113504d0030241c0c0c01c60503172011042c04a580c00c510000203803085609403c01c05050301d00700340302c2c1c00d0b81010b4001d544254000e4000740c424140d80d42003a2158400d10800a0041e00500000e10040c0c0907240392511a100614201c0d052400c1c40c0c2d243c90849030292200748483c1d000b0105081c19640c540242d1000e0641038981e85801072806401a40d03994a1603803c0b0110000c000004169481590003040141084420103006051080d03503105800303400e0117605c006000c0d1010280a40d4000e000e66403403d03220400400b40d2500c2e003a2a200b464014803181a44203803039036006006109130344080e100c03620102d80e40540d10752a100540c004d0200b0405000207110003400160000b45080094907407240742d54450021505442c00040d0300c4000c01e030010303030780304500541140410296100942c400c805a000820003600c0d581e20986054048820859240c0d10542c00d8034a10541c0300040d0010359000f119000358662600d00203409070310210340d4081c040021a55400034022400340c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 595708453 1250 595707203 595707221
    0xb0405091519292103070b15060a0206010806010509040c090209040e070b220833010e090d03060803030105211204031205030105061207020114040312 66
    0xc010920014070405600c1d0403031004080b80808607415070080301ca0b41550308084182442000540703142d6014180c3d02d68040038850450303004007142c465090100e80002510002c078240d00380203500f05206c554909030a41001407210011400c0a29250420780324030028164003805c0ba00609800d40c1001d4200d458010142d00c41c500c11030b15101400b0214130309140700c0d0180c07915102d0250341c803410340300450f02070510880841e002d8813508900050320010a030191100c541103002c0c44520a03c440101080445070740500c48103508546500c0700c1d987e03038114a00664210000440020410411291031040c5099005c0c0f8404840201080100a4148401d05c1c0d04400c5041c01c000030b90400008540c1c1b80014022140100e01c00f5a000d1024041c00b40c0c524100000481104c0d00ca031544100c01d800c42c1c10034401142c0c032205e4210030036100c40c02001540d042c2c442c0500780d00d090181c00118018064005041101503540c1d52004500310502c010207903104501070389680c80300005989505003140c003540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 595709703 1250 595708453 595708471
    0x2b0b04113a14060f060a1205030a2a0b04060518060402090604021e09011103040b1e0d09120f0c0b040609050309030a030c050607050301031509060204180b0405 70
    0x5040c50300e00e40e00c40608407070341c00407107500720858610a00c1e0102d41801c04982c504003610030042000008240144041c3c40365505840c0c10360800d650b80792501d6450642c0074020b040b80c2082c0201081d50f44241a662031218402c7c0792542d000760f50100324180d01c1455a01500c804080000304018040c003800b42c5900040d416441841c0702450180c0242c650201600091240c4001c0c40441d1240d41e4a405855602e5105403550044022032101c04a00e548270f01855804129640041110f00d030002c010313107044406500420b840c040f42e134a5200c444032081c080030a84003406000d0350700c94001500c02e01c5007041c890101c1c0342e616010107801a00e49100f01603168200660046408005210618010340180c0e003d2000328041c40103242440c2580140e9540300d8040c0310f810489024103601951150031b181c09401070364159210a0320440e407910090002401c141c090140320100d1141d1903020007442800380030010700b002d40b18021154802240c3d9a500103040c2c651080c0d428615140c45900d070045840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 595710953 1250 595709703 595709749
    0xa0206011401091511010f020408070815071209050a060513060b100c02010e1809101401050d0f02030a080d020d05151c03090e01030305040e0601020c2b0b0411 70
    0x4003d513407681240b004403070010014130201d02c0207902000d4010242c0011004802e42d02d5640340c6074100d13030314600e81c41940d109200d0f044555141c07000c020340907030144030b02d5034070381d51943c00c0c90001c48054401082c00f1541403140d00e9021002c40c107544030702d0f4014040e0b54075443c0e04407400e06118082d108102d90507489010a03602400304a60482400c0800960a09100e01c4a0728068001652500c2c0103109007200e40d200b0082050741500492032030000c82d0319000c200018881506645982e0200b40a1039030011389403109900481d40d80a02c050045100030212a0544c02540d01c40006403c400000e000b900c3d008181c00481c1e001d5809082c0c0e0103107540d07500100014a450000d01406840c2c048103100c5400d0380408000d051040c502d1700054401c1c107103007072240d5031b41e0324006000b5071141c4280e40840104002088156201148811307a004c0001d2880e28081d40e141c0711030000520350001a0302ca00c449102810005410f03c2d0f005110304d000701002508040d40f5030600c558101c081285030006005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 595712203 1250 595710953 595710959
    0x3050a0c09061b0209040c170a0c03023706020705010201140606031b030f22030c1b05091e01061404151715010f02190816080a020601140109 62
    0x4085031440c2102d249150030302c0881900480001101840c2001039041a45d04080000b0700142201803422a070741401261820074003040001d4030707400c1039480102600d01080041000d8030304074001c0ca4040e812420400c5040800c00e4400090f809400002404180c0c44901001003c0d0144000801040c0c04e000905c4100400b00c807041020000a081c14480d41010020491280b8001035540d00c07028129545035807400d04c2c03014254103d20403030380d5400200040302010780040f14800f641c404607506846010b46801c156071002929450300340e80c0c60020744410000222584e903104814000e5a255101060951000c1304003000458160440000d0200e40e5a1003103115000004403003c40b0b1003900141c80d4144a58801c803441c11103500d403002d82d05240380901c00c224100301180203050704240c03600d50b5410280300c01682c40e07030502850100300c010240c0501012900c410028009120f400b0701c900d058809a0342c900ca501c3d00065003800c016400480103202d04006000008207c403000d003040307039401c0c1c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 595713453 1250 595712203 595712207
    0xd02060a0236120109021512040237030501050106030c050a030b180c22180207020f06040b03010e06040b0d150b130e07090507050702120f0610050103050a0c 69
    0x120b06002603010440303071048842500c0c4100b4404510100205080681c044a612281c003810042c80c00368801c01c0d1620142c2d0710a1145402c44c1d0f45490040340750b5450303540b59020007020485581150144101c003505001c11700000160800c0c480786090300d05011242182843d40c02c40d20141c0080707041c145090742c40035034a40c10009803039030f040d0310345000b20b0700e044c00380081110106482d0860842e210700740c003031011034056040030f06440e00715008a158403801000c100102201684500c03040c40c01c0300c40484040640c0da4006285160002c0c022440e04100c1c040400c11541c402d42c408120220040010301651242d1000700e41c00640803074080c0a174100c0e6500049034401d00c2c0100078029003132003c14500307501c982e030030400d55030b4001841850018190030050015002610f000c40d034078000c088000c2060f0b0410b1240354011071581da41c07036003403003041e5080c009000b0000008158a1007840e000405054080000718843c07030032640c1d0380c4112442e1070f0024082d107a02624410079a400c8c000e21019040e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 595714703 1250 595713453 595713487
    0x1020715180f03141605010c08040c09020c070e070e09090a11120f0a0501060f060201050f012601020f0d0605010206310501090614010f0e06010c140f0d02060a02 71
    0x650840010b4103610524581a1020081010075a420041c0419a0580740481072a1003060501420003400300c1028150220b070000002c550007130104003580c4091202222a0b8054130340c400740c1004031503100c0c2c0c03108444507025070101c8401d8000307000c1040304181414020b5040da00001c004c0c00a106055550381d4900d44489007024103402000515801026400204500c11034044200700742d4418058a05015010b454580100500000700c948001006441407140c144622402e11120589908050307400c5040c03244805404c4044070583c0000308616003c0c8020405940300d00d9504e55103444881c0c0c0f10042d00c800e0b91140e41550005010841c07007083e0a00403521001156025105989403801e280010309400754000c1c0c0103618100c12482003000c140d0040800003208040c1c2980b40e03a94056000b0403892500590b02240580404145607502417011041c00620501540c0d504404601c4060328202d0120801c0d512385c1c0c401081c9000d5640c0511030a40c01940040d001d42ca00100401c00420380 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 595715953 1250 595714703 595714751
    0xe03120a15050405090c121902060c01060b041211041802091b161401050702070e060a23040506090601020a0b04150c05030702120901090e070e0306010801020715 71
    0x5484107540d2105019030000390001c0c15008204010320308100320441d603100c1703500c440140074081062507070148003000545902c2001146055540300da049a00784002d0390420342e440e10b115905c510000c108400300380040c2001d010030b4160070000e440c03507003000d81b030403411180d1090040385060b8031546500c14299184004a8041e222116551550782c0240a9001d840e207041d20080000701d44c01440c0c2c1c0d10700c000002e140b40501032903103000720095001803c854041e00d89501580c09210200030020881091541c0000f000301202010b5503242030101c5100001040c1e901d0020040781c2c144884d06e060f1051075040081955031407014580080042d50301c0d0b002d0140900700c42803d10008040020502d50807044510549060091039074084010f00203410941c1c002000d40647c179800140703e40c150040e9007034030074141e40c0c152640e803418130204d5021001515550810440382c0c440a0030380c4080185c18000e0000c1c0307000680c4c84400e0b0602502004021401823011800c044070b40c00c0c05425040b0200c14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 595717203 1250 595715953 595715971
    0x10507050a2c040213080f010b010e030c010504060807030b10210507090909020d05030d1515050d0b040b1e010314040f020f12070303090e0c0a0f030203070c050a0c090e0312 76
    0x2d140e04400b4445217042460b48551031610502c081c11710201d07070640001407890000e8072a02e5290607004101038441c0015051715000540600c000c000d00340c07044008039000441c6040029060185102091419601c004180c0c0414620031807141145c41985605c4941040440d04000074100520f000b4400d00c218840d080074992260324150075560756090b804a1980e00c0011a50381e150100440c030064202c8017040d03009140849400508071034500400c100f411980c0c0d070348a20301040720b21608010004c0d030f448039402079030711601c0c81072075150006003d610002c1078001140d00d00c2904001415903124540030015000504140000075241008811041e641100c0c11454a0569004540e10105e05d4800030140c0c4140180041031680000310502a41d140ca00b10104a0341d850361403c2c21440750107202c1d80090120340407500041d04c290301840d04801a46090b50340d103086502c0b508e28000340600203580c05000c06404001150540c0704000152707441034081d500b481208226000200701c001c14601c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 595718453 1250 595717203 595717207
    0x5060a0311040f05011403060c030106020a02060d09022d0f0310020c0102070f0803070801050d050d0305090f0a0501020909060307080619020417010519151e08010507050a2c0402 78
    0x1510b6440d50403030008100f1140e400c220b50341c4c1d01c00c031803400080101c00b03490090041c04082000c81108a044a050755207540051070300d004143d092000307a82c484032429800c01d980b140d1220040e5190035849a12420080a6049041148001f9580300c80c1c5210300901c1070510303080080c0d079500c0100b1001c03d10000c441c0010780300c0400c03d445138068810f0003001007980b030056040c1400c1100350800b86000720215079500c0e10a07a00c40045c8a80040b00003000740c0180e01044600c0c40700e5200b60030180d4040d006c2410f07035000d02400c114032031801118410483e8940d4021500c0300090030070600c01e0390310100071002007142c1841c114100f516024003a00d1205001205640302c0107418079601142e0081010741c5c4100c114040510106000b0a802d441504c1055800359a1009a07220b0b401040500301700080c503008001c1c5868807500070141e0140181c02441c1c00e00d480041c20030001c0c4620746c8201000e80702d2540d0f03180380b407400603c16003050404032a007a2109a02000311095400104886401510016 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 595719703 1250 595718453 595718483
    0x2301060c0206180a1d0604020301120f1a0a0b09060306010308221206060503010b0121240f1706190b060d0e03271507030c14030406090905060a03 64
    0x3c19400514629190803100705280010210080e4400f9990061401d8024075a61a140c041105030710080c403075001310b0003a15804201281558030211400c512484522003c004503920720344220b00116000c04080e6614620310010342403c0c060a603112404a0142c18550b0560340c6002150040b181c00c102d0202c881c82c45540e500001e24008000380c9048160080285620300c3c040e40a005940141402075013402142c00301c0f5401401c45030040303155074000e14941a400a94a002130078228504c1c0103401c0e83c0b007401c0c5440e480030385035407001d000741241803c0181d0400000c564007070041c4c01c0b546141d44c4100c5c200440030300d1aa00300c079429104a40c001c91940d0000c40005c080d40106208a6929441c20003038840c61f0314000300501044404660801e005084020359181b0b0000c4000e1254100c05415581c16889820000500e00d00b40302c2c4c1024100038106442c0d00020703825070901041c05030f000190500c81382d50880c074040001c007100b1006001900d0702d040072940901042c0f00041008603a0305000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 595720953 1250 595719703 595719727
    0x213051e130c05010c020d020f0a030f0602090a0e070815060f0d0c090b09090f072102040915080a0308090f160f050102030705120904020912012301060c0206 69
    0x10000d0000c6440340c900500309850412000c0c510310004440400750b803100041d0a5026401a10724250020b10711184040107409203c642030b4108805039000d00c0c40040480001c00165507001d40c2c81c0035a9006071540b0744c1209006102486404c00c40e00c0360a03481c1040303109a40004810750061200c02440401420f10300807481d107004202c01d2940440020568042e5422182d01528030543e213030390303800d400999036002c2c0c048501c50030b0304040d040500f40002800c400e2220505a1300028039107440481e035000005000a004410031202c00c68a030009005c1103156060302075010400c01c00c44a82c9642d600d403c800980c2c0e000c6100c1d0050510180c0300014400d94424003000b0b924240240c02c0d0740d01000340762807884482d0001d000307800440780e42540c040750a5200006030381206502400400d5070812441c9160196084801d83c035078059001c101c08011030315042c51201e680380002d0004280280e41ca005803c0c107500e950b07042616003114200420600391f211030985131984c0c0550f04140d035400c654400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 595722203 1250 595720953 595720981
    0x8040b0f0405060a0807090b1306110c03011e060608061309030c02030d09180e120c030f040315050901110910050d05100e0108010b01050a260f0910020403021305 71
    0xc1d0354041004642c02c4112070700117072500d01c12501a5500b01c102a282d040f229000d028115400000c1c0c480c103003050200078010501c1c1110340d24030104490720207000c500000d003540c001c0b080071220703800072a003181d003001070f9401048040d24560903d141c062500301e0100ba10701c200940344503c090b441e080e882061500400d655103203160050203440c40c100c00d003040039025150b03a1148145e280c040c03003403415598910780328046aa5503000d000c0d205452071000405c50582100c0c80860050108004811a4180c00001000214070500900c0030008200701e0710011501c0080000036240d042c508045807065481c002c03622071708000ca0310983c0b100b50201c804c40b41c9020f66007110b80b00354500820300c039810861a0320f0008441a040b03100b4156a03c42d46000d0076102107862090100c0e8040c4044040107008052942d00103540d014000910741411150b10603000080d5200c01e06c205548081c812031010621503a804452500b0055280524580c040341c0c41d0000203920888040c2d8400124000c0c80500702 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 595723453 1250 595722203 595722209
    0x80615060319091b0801090c09050c0d090303140a020c0a020603070c020a18050c131221080405010605010207060905040b03190812011a031b13080309100c08040b0f04 73
    0x8080118100320b207440115180900c80076240107a413144002009181406901c0c0029401454100c07941d2406501c0005008040c009400c0c01c501400026050101886420012400b940e00810800c00075190302c00305410140020f41064010000b03000100d500003600c0d060b0590680e00207070b0301d40d41c0f120216154109070790003d5010746191400585006c050f0301c110b00b4400e40010401443d1203070213155005105450005200e24000f0408010039103050a4140041d4010302da0b55402808000c0c4010b00b000d5142c6015002c13606a006200500c6000d1042501030305082c0000e0080e1400c100c03001d401c501442c4145486039466000c00000740e2404e00c4000d001c03004a08140560000300d16009080382c002c50b080031448071a075000000c2400c0d2042c41b0b000d4400450749003c0c1341d5180c080d0b1b14010146020200f00d114201003240c1541d801e440403501c4010500900510f88490340c030002c2140d1f4010800c820000c2040d005000c2011444207003c5504480510203103665450783c40b100b5650601075a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 595724703 1250 595723453 595723501
    0x2a0312060f091906080d051e13031e0204020309010903020c06031e06031005100317030c0a11070302090702071d16120912120f0606051602040b13020705070806150603 73
    0x82461011b16081070140109448070725002202150302403400084d03029411030301c0c0489030410070800126140030f8071200d40c5d560740d13101070603001c0942e00130406a07802941c040502e0783d59880040c00f072541c14400810060001c9039240c1c51800d0a5001030401c580c0b612400c0d501c46009800301c0d600d035030100701c43e9008281c119400d01c0a0301e00742e070400c00000d00601c0191142100e041041c6504040b201c1140c0c4103801e01031100f0301741490321500301c0710307030a840c05108403901c136160001c0050fa6664000300e100b00c0d03460340186550350074242600f5104d0f030714401c001d13020b182c0b42040c84000d418043d401e41e0510340714540211758110b401e540c1c50140203003440141c20106a51070065515602092022400da040e0805000111000c0c0a0310308442c058480d0740005002404416610400308042d5a900d500080c00410150806000250b4170b04125914119107640003907502c0401c1002d002c00d01c020300ca104060401d52408045000300202c1307036980c1c14442e60b40000003c2200040c000e2401c4681801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 595725953 1250 595724703 595724713
    0x10f1e1209030e10090605030a0515041505012007030201050c100501090902010e030a030206041b0e0c09030d21050403030e01021903060f1a2a0312060f09190608 71
    0x42c24003400b950410301590307001d403446103002c40d185070040c00102d003140d6903907940625544d41c3c210380d14001c00c0060a136480c0b041e02908030341341c80c1c0c2e140c0c003400100525442c16599898640300000d004400f00c9170f4922158440700800d0f20007807201103000702c12a602800c046d035032800c210091505000c10503954220013858070b80003240301900f07640441010b5200380c0341e030a002052780040640d2262074210040c0140d0144001400080d100f4030b4150b03400041c00c0d4a40b0341c040c2c54210f4a00c900c1001c03034a40718440f0011a2400c2c2c140740400880b500b0000f5410305040346542c0401801c6070030b15504000000d1a00c03900814109482607120510b80d0303410000840d22440e01809000c90042880c01c0303800042d0500c0404030310824050018411944640e0540320007604480c1100e032541c02018414072080490303984440714044ac182183c114594000c065030f0f8036102610300300d05401c40504481c2c0a810003d42020382c0e0342b15141c1458011228141e28407242501c18841400b511041e08003c0c02c0d4051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 595727203 1250 595725953 595725971
    0x30103060b090709031509021233010b0301090911151b0f0c01030e150717132d080f0c0106081908030a0f0227010f1e12 53
    0x2080e40038514010302100d00d22015101c500c1c08a13100c4000b0300002c0c0c400f100f03480b034410814000e540f041c0b02540c406800648106000d109103070400e840b040e40707116401248840c0d0070814011254102280d82900001d550030750605200320214001402144d00480e83c400515082c051840509000441d005041900b04a00500101d4054100241c0d0300850002c07040c02e40c141c101d0100755060700000c1c050040495101c50401100500f07000c0310101d003580a82c0c1c1c0c090f5003611100704510311601c1d83c1d40321008030402c07034403403c8404c00c00240448074000e8401e001c2000100140d42009030b03110785100404601c81c10b5075092007409203448000740b18510010b40292203e04070b00c00340c07980c3c03031080000b0440c0070342d60301c1d810741c4071015500031ba600c9240889142c400107809901031030704030010400000c1c10215041668040307922039040383d20840008648071051101c004580c80e400d000c00e10f8412000040e1001c09040365901e00009580820301c0d5000341303000c038402c1a00c013500c50741d400004d009201b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 595728453 1250 595727203 595727213
    0x1f03021309020906030615130e030f030106140a020a0f1a0403030507110106050901050103091a01080c040f200a031e0f0c021501060f03020405040f06090506010c080f0c03090303030103 81
    0x5400c5401c0703000f4460100060b40520b0701148852043c1e64000419800b070030f51208103c80c1c0170490f2100068a5903401e0500302c3d904040000d015081e0000b156680d60354100840507190241070012410b89081c20402011115404105090230350750040e903108211301e0b20301c0d05d81100e281145010304014040c4040006155040e000540104119100c0c44d506411000720103007651240d008142d003141a400c01009254400d900a403e0ae50145990718541511122050042202139000c80910b510440e80742e0040d02d0284961b080c646030500381000382c04400300050800444080040d40040404546655280e00980000c1507244031a041c4a0031203051044e400010503180000d000c00f245800d030810700890001490808440024465003400da107032020485404260b10352420805030207010008603501c80b4010f030610313040c1105000c0303034060400c90320400b04c3d030303008085504204240700608089035500d02120143d0722401e00d0786035119248842c0b2031031403054240c000d4140c0310010000040c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 595729703 1250 595728453 595728461
    0x507030b010801090209130318061206170a020f0105041a040905010e09030f07030318060c0f02121806042409120308060d03020f070f05120f061f030213 67
    0xc0c4501040300080e40c86404450890b0001c5400030f40100c140c9000c5101100f0b400b004005540c4245800380000101c0a10074081240c2a400840483e8001c8a03106078200325000700005880032101000301c0301030081c48290340c2c1c1c4100501038051103001034600140d034802c204035070160400c40c030404804000d80f00c0030201d07603105119981185162000220f0300007802e165990041064030300443c100300c440510007440d40c0c040f65088003490342d2807014000c03851003a0800540280100b20005038005c0c4840c0140424210395016070454000902e50718003c400c2c0800c0ea050084281100e4019403060004650381d44250340003904460242c00c01e10116601d402004001d00d40c065550030403141e55101d10390881c400922000780850740310030009151781411340f030044c90b6a00034411a80d00141507114681021000d8101c60b042941c00f02d0b0501140c00e062507d50355401140c0f0040500202034441c96448520241c4500e41c070381e000003d02d5101c100005070713038001b442d002810b40f80c80b480c811007a68010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 595730953 1250 595729703 595729709
    0x2190306050a080a03050d020d110309012f070611071209140603060f010201020d0905060105030115030506040b180d02030a030506060c0a0312020d0207060507080603030a0504060302030601090806040507 89
    0x281050008100340c10030390b500c4001c039098071008080305016a40c0030b5030146c001c680d01c01140780c2d083c80340824503c1503004543c102504030b40500d559092440f03006007568128003040f602920200161113901d09500200d4118464202c05c0701d466072158540382c030190001840c683e2104030003103490018032020b8980795800b803003582c440c505810340d42c00b4084d07107071f00400d210540d2050003800061040c1c02c103d5120140310308144001032910030010202021189005d4059a266001c0c60041c046424244200034811052502c040d601502d1a2f480c2130340c441000388010030484100010409001a501e851030703146543c10140c828000d408400290389400c499840b200203810a400f0030b00500340942181c0d11025008003601d40300546480c280c0d0309000303036188103800c2076080025062003d401e2001e04030311880b400c80800d5038100180c00918440b0f0261100340719420800ca13002c6407541060454046560030308000d80c40c0d507240f80061b54501c049601c82081d501690b400c0108016000c90b82d035041d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 595732203 1250 595730953 595730957
    0x6020a0914031b4507020d0824180a0c03020403051b010e0a0b0a020c011e030b0616050f010e160611030418240f03032a03110f0604170a120219 63
    0x7107550305c9008076510b854440841002c90b4500c0d0100e104500f400c20b0600484032204201103a90b454240031551921640c500c04480c80000018401300741c8c030300d009028132488503150641c1818119110709071191b407a8402907842039040140c055281c0d000303408d100700c01c00c801441049030395900c00d071501203640326044610040c000c610380e844082d80507071008010480080401641d01e8600401a40200302011400d60b00080c20b11000502c0c1b2076103500065101d12640c00b91002d00e410100760b03401d448001103001c5c01504040b07404006000c40090319403c5070110b280491600e105040c0305419841107402220000c0e1820a4042e40c9140e545c001445a00520b0002090084140300100016850780124801c1007030240d410400300307220300c0e5000050740071220003102c03010600740244544001361100310003203500900c440074070075001d2140014882003240540740600e0250394080d03180007840d0325021000c90106906018511600403030180c85240901159070f07a003080032101c21401c1031034076200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 595733453 1250 595732203 595732339
    0xb190b0307030f0912080a0e030a0306061d09040b130b0c0702030d090b0f0a030204051201140703051e180714121609020f0706020a0914031b 62
    0x8040381151041d42d800c250001791214503041031a400720303400c2c1d0000d056a508141c49808240030024148014141030455881c0003850702c4c680000907200344004581101d90112210b40740a55841c2d0198650740268400c0c00b00c6025540d06450307800c00101e103580640b9820002c0301b00f010b0b4526020040c20418021000c80e03100581c07217002100ca03503029000d0040964014400000c0005d010070103032011008604015040c44c0d15040410f020141004e003406060f91a10030503a4040340500d03440750021050b18003441280f070490101c2604480200000201d034006400050742c800c01c100d4007115103e4001c094944440d516003010080804401410f4424050038440c40301e8190006183d41c2013043c180c0714001d03c1458100440000c1d0082c4030300d10380e0000c00f00300b003000003103d900c000c0c03e00344140d4070b6190f186802c02020503c0d2a2000c0d5209010b17910113558040146086c00d8440307205c02046501400140e0740c104200001203880d1101c456002410020900d44d058a8100364102000505102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 595734703 1250 595733453 595733471
    0x9050f03010203090a020103020d1103041a18031608040b03090d02060601021f090f0f0305030108120703080a050402010306080a030908060c04030c0e06013014090c040b190b030703 79
    0x500b00e11040d500342038141d10200da2000154041d0700a40810840e8040000e607a80343d07024240d00561040711b045a01180e4144041000c456429005801000e0301456500c0040801401c5681348075241d0204c060b0050322403a401042018400c5802034900c0c90950764481c1060055642c0e600e002e641500090300600b00010b800e5440080d11090700764004081078544604500b00c10024078000d402914455802c408540c0070883d2001c560701c0e0f9a110341d0b2940c0e6030f90f00d42400b00c0e0500d8840100340b40007082c1004250301280d40b05a0184d0811140100001d6540f510b10058005054952200b40319000790010b0005042d00f045250701120342d9041661425510031007552050f101d50f000082003104901c4060204400b0f140c4c030300354410303010705040300a003200590b800600d000c5c41c0303005080112850403005503142c5500800d000900d41120543ca541042a0700308d880360b010840d03450040350346908540155130342e140e5000f8500f504000c0e401113641c883c200901147d008459a001190034a6000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 595735953 1250 595734703 595734709
    0x522110f03011a0d0507080f0601060207060c0f03050307020a0213140a05040f290f01081c0e040f060513060302092a030711061617010b03040809190609050f 69
    0x70340c0301e103c50605145814024181008101445103409031000d20034040c01044c8090200b00081000d070160000300019854040001c0c50200c164019904100138100880d00040600103ca4080c59060400030703129500c41c0e01c00c903c0c042d481c4501960001ca20b01c0002c802e5405684400400e50503803c0c8030003140e407090702101c00d513030056030020508001550180d001c68142e03618902000d0652a980b1030b01040c82e420381c40c0415050b01d11030120710080004000d000c601f08041010241500c052360729010440d6005048034000c03025950145407160722008500b1422384c0000040c1500a1a11280b481c061042d4402421030780401c9024004c40704c0461612031140b00e0702e00d080b403d00d892091462040040d408001d4202410b80c00500440000751105860244003052050120f001002a8400e89040040180003441840390700152008018002040c1441c1140e510940110300c840d074a10116011505a4080d850a0799900b0001300000c03549a90100c6403001311070b01254040464901c034020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 595737203 1250 595735953 595735961
    0x1b032703050d05070f0c090b0a140f10020304170606010207080a0c121104050a090510020702030a0b0916180c110a0b220602130e040c090522110f0301 66
    0x1001d41240d211214602203240719000400009104403c80a00d1003a60740d0381550313050b0103030003500c2c2194484009401c5401e10b41e01c680c0007070655050280d02c030940800071849009549150324010b4800c40d4450500c24000c1088400a2502220070840c81d213104200c1c0c0d88480701902c0c45401401041400a43c943c03002420904003500600146030036450038038035400040c0d1000e0b00f100c021400c000340c004640e4a5105003845002d20000204180104d85000c81c10580701e07180c00c10301d05205021030000340e14001485511194402c0c08140759840d002546450000a61040d074114426050301103030100c040c420200382c845210000340600490711f071003035900036000040c540300d81d4480b0700501c000c5189020443e8200f83d0000c1400750310700b466031481d10314800344c54003070310015000a03400c000c580302da01a00c00146000100c50301745041c41d40c0c510400304024401c041e41a9194400305124509211004448800f2030206030040121442d120103d04060440d0360700c00e000303140310b00d40d403400d040c02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 595738453 1250 595737203 595737209
    0x3061a01020d030507200c01080615070209040503161406090a030e01030515041107110904121d040501030c060305150906060c03311d04060209011b0327 67
    0x2d841c0b40c100340c400860040c040107000a04005103400590750701c01741c001c3d221010b6681040600381d000e0116002614418010700220702074414428482105003207402a108402c1e8110342612880d05c2d203003401d03851400359405181070b003290f8014400400454038103003d40304c0308000a444080c1e9410b030b0500d454040c1e40d100600426564400c86030107611035030016620010b604480081c1c02ca0b940e0129084550300c0030710509400c800030b17200f003c0c000020200d02c0e0f82d50302201c01030010301d0301e640c07006242c2050106038400d00488011032a140d607401000c0c02d1603120094000c00c565a52801d041c2d055441900c01c1c0c2c80841e240101183c042020800c0146201d071014094800b0f0380c03209002e010300c0b80d0141c0318240c0710340014410031240d40f036517581c205110401407001380c128800050110100b905603138072a04071600c1280181511498441035142d115821110040e100d5071070100580784d50007950010044510b41c01d01800c10184c1002c03082c8015014140e0700c0b448804400c0e0032511141d044c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595739703 1250 595738453 595738457
    0x11401150f1d040b1809010b0a080304350f100c020a1112010609020409061e06141c0203090604140705090406050408041a0d1401120b10050d05030403061a01 69
    0x61145400360903c1e402c02d10b007492001d400e003410390784c0c07500d1625003454040c0d8004106075104c903555181890005c0e030311800307050003801a40c6410300c1c0071854078820804100201480181c210a10020f440440c000120f25034000e09544c0344502c0481e043d0f840703087d00e510005030145011280345000344002003d05003a0741c0215031030070a0341203400f0401c050318804603900442d92108000b19105d8103038000f40004101100e00411014240703100a0200711015035118007200003031004000fa00e601104003241c0c2c1d02d5190200c1c0d07170f9001060f4000100660000a03200d824000010701c02000c1c0000340d11845075001d10f0580003402c2003004001e40b0340e41180304149d840404c0038081004250560301198000d032180c40c12500d0644c1d07409083e01c0e1050000704c0c603075010001140c1c0c0740c0d0020035409425282d1070441d90700f8220350704210a940804d01d270070300080c0046079100002138080c540d1403031000c0641b00040c6010f50315840d41c0f900a54a0307005020455205040c190346101c0c1d442074014100c2ca11381d050b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 595740953 1250 595739703 595739747
    0xf0d0f03090809091f03061a060a0909020c120304050312010f0f180914030c21030106030b030c060d15090203070f0f02190804060810050604060c05011401150f 70
    0xb0010051300d520064940d00b07003103c440c4800c80c00e07000c0c041d9502004503c110030200c0d403802405040030004491402c07441c0604020020200690b903c9180d40064900c03503800140c441c18914511454140c014245410404000003400140030000001e0080c040405403c44d00036038907502215500311f03a5220304001c11109903000c2c044002038a040f010113030740a4000290121164440c003085c07503021046010944c01c00585e030065454107002140a58820040d2100410612403c60f01c0c0e038401403090000309560b5034900921a0b805200301604404001c002c50b80f10380a4142d0107000b840124602e180401605400058071030a034025248514813a440f03902c0e0702d540684065950000919120046000705501040b0051035040c0412240e400b822001d6165410220080c0201d000604403060f2001590070800c0140e58840440f410b6500074070b011061034404d0301c3c000780500044100c07a61705102140000c9816912101e0104240b4256034131296000440003065413915041002d0907004881 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 595742203 1250 595740953 595740967
    0x1611030d18020a090e06160206040b090a0c180608010b061e0f03070c0606050913081c02070609030f050a1209080705011401090e031c0506030a02030f0d0f030908 71
    0x180354007070000c0c10a00103000d0015440c030750000f204501150004800169205c1d00b0f10100001044201da000444c000811040312461101964500c8c008000030140c2d00a03d002641404080c080c0a035520b610a0310340e06060745801c000b8000b100c2c2c3c81c1c10902e00700d20b410000180c03024140180586924050440fa107410745e401966444840d2407001c490502108000c01c0c40d8120116005510402c82c0b03540301c40501035945080e4003505d41e140e020504c80c051040c1800003040300e007403c0d0314126910061103a80c4406502d1030070b00d1a42d81c044004003051000c2540d1b404e0000c1600f02d0190036100f6035500205545804054465010b00104140050510702d150384c20030810341d200c00f8049018020709030502100b40e0b80d040c03c0d20707006188103040c14500c4c2e004001103400c40c0961491b140040300652f0030b090200700d040b80d64168184046804a4840021500949051100c2c000c0a41c016040d0b4000000207080d0302d40d01c030701c0209880005107001d40c2076600503100748500d19050b0740c04550340c2d1410310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 595743453 1250 595742203 595742227
    0x2090d030e0337020a0302030604081c090305120a0609090c090c030510120602090402030c07171e030a06030515010f0501080709140f09160206060402070c150909090b161103 76
    0x200c000402c0783c10000c2858040096a01084101e101e54800c52f102c40d0740f031008803550031403001304401c072588140c20705038544c0009402209480880c00810781300181d584d15060310b08043e160716406501050b1402c0d00721428050100c002c6c0c0305503010580284051601100224221071040b540c03464035610b406000d20000218001a4180900403d000340c100980c0310001822a4010b031504001440002022130030081207044070318802c48ac0e800b5079420301c07001c219071481d02243c05080718018880000003d01d0707080e459200d800a95080b808486c0f030402c0131000f940d4407010038040d141d1104085000011598800c0014274030520160792008034180c5007030342d42c113800c400f0080e00f6540108200c19080c40d41d1078420040e0320481e03c100f0543c600946407803029040c4100640054040c40c01003004c44045080d40700100300b1103941d1268002c540043c8902105c400c0e0350360b0010407446003058500c10600c0215401a401686c0031500c020015622a000381d480c0c80e01d80100314000d07001031181c180303241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 595744703 1250 595743453 595743553
    0xd270b0307140d0507020c04060b09010c1a01091415011704240b0f030106030c03021507050f030301031a0405100b22020c0c0121020d02090d030e03 65
    0xd0300703414000e102011200740d00303040d904641401c0030900c0da5041080011941000560104038040c0c804101840c03d014a05100b845807042503030600c1000d41141c0f0401003211080503092802c40005002961185243c0b0041d101c1d90380d00e1140d5500c5400030516140701e01803014140c010584400d184004540404499520024003c1d0340f000c501d0bc1500d541c80d10b5100c14441003000420300002c0201c1d21808020403240d2030f04215020fa03140c8201440003a80100d41c1400380c1e40c04072180c801400c48003032948154420303c40014120b02801c1680d185000001010718141d91040e800b8aa0721a24a0030001d51420304960180513540b03c6104107403102c01c60381c401e030711504000d031040c03550a040d5041e00c910500303851264243c01c0d500040440c41e801d000d00020300144024a82a9403c00308a200c2d091807003c0ca090202605600049030485418194101e900402018000221014a6080103001d20101000450190180d1206030b2008490904d05a201c01240814210072000a24102d1004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 595745953 1250 595744703 595744711
    0x20c0103051009050f0a05100503100b0a03080f040503060f3306040e040b010603020313110105070f1a09010b0a0603050402031e0607030e0304030213050402210d270b03 74
    0x4101e00c400c0070031414070f14052103109009050001800b400c100e2180070445400501c0c1d401c1c810b0030220188120f1360f011401008e0000c0780100860458800717000600b005120fa800203065520000364a0f8035102d8001c0500300701d92088080d030300c442d0360b8030401020114084494490301d01107441881d01c11126041030079a0212642d4100c59010041e00110f091079009030842d9007041c4e9800c081008000d20040128054240b5103420b43c1107040a4824074104114000c00404d00c0c40784031030115450744160266003802ea000000074405262608140440304042d401c4901000049400030303030080414002c0c14605a0050400c00c7c4503031800c1c1c0c00314010301c006407049a05000e81c0343d2284e0340f604285d1500c0b07039420100c00940881d080000340541142d1402e4200d43c51604288010009aa9140c10f00302e90007044000c0130a81e60349910014070840d0060010707510f0000c0c0d020703046500e90b02c00a6075045842e02512401c0d0110f103603500302120700c0c51012515814070b08005003446084050304c060741d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 595747203 1250 595745953 595745971
    0x61510050703050d1518051e061315151107060503150607170307020f0f03040918021503090c0409080901050c12070b040b07050a021b0303130b041410020c010305 71
    0x3142c4440da2003642c00d5242c0d4010010010303070070328083d06c0c2c090034810309800007401030819684800c0680c4580c90301200a0145114512090006941d0f102a8004503207103401003005261031901c13900c4200c1900b1016040c48002540f001039803030310302000038910b0150b6215441d0a8216954003441480e0601e0310310f0400c2e00300d14103201100000d2160040b005915080b151280d481c2c2c5803591009107040c840c100b1a5086500881100b10401c1e404404c41d01a15070104003c500081521079160b00030100f104002d4000340c00c411100703000440640510b004207030f010705a80203815100108000e6812854024249100810000c222580680b0007004940e03840c20a0740e89000c04100444401e070441001038a950415504000400490301e54071584508242001410f120f000003000f940c032100c108010740690703090b4002180581c0d0400984910412041000c002240c0340c046024454005100e21200c3e4000000203d100d840d04040003405643c4581c0204009101c01d001140074150242203410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 595748453 1250 595747203 595747211
    0x2b020f190305060711031e1813022520040e030705011509060303090e09070f0e06010e09150103111306030f1512080f0d020705060601120e0a14100509061510050703050d 74
    0xc3c0380d150400c09105440349c0a10060f11078541d0010050701c1ca5515030590007141859548000007420800390480611200003040d9880d2240c0000c10300030220072001108500c0007040040400005401110600741c10302c0900ea5039554402002040d10000d010050100740e070200d05015080078441450303408a0208100d40b04265150b66804c8000310f00e8101d290481d285204000c401c0d40c000c1c1895290400c1590440003603c1d00310740c80943c40a0900990303040588681c0c1310074049440070306a031000b0303101c0610f050031a03546400180082011000e08004641002544a80d480b020048141221345201091003803220030350300c0507141d42c0030f500200700090701440080d00d45810341c4050641c440c440c400034081070400000240100524080f8112000d08089403000c103640c3c04074105000035031001750340300d181c940c0c81000c500740801103042e0f1664078940020411412000030360705000340400300c0d075280c2044100c81801511010304440c480494401c001d004d0009100d41e000300140760300580002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 595749703 1250 595748453 595748497
    0x507030c0c1a040602011802011b03090503060903070204050c070c030803070c050a0303142a0702010c05060f0115030c050a0e010e0406060e2b020f190305060711031e 73
    0x200300014078000a18030401060911040d5024407d00380c101840c0c0c04403030002155039000a01d44401c0c540c60790f250a40049500c0200340c040c1c241c20f0042d20006068030198940840600d42e03a0300083c0d01030b407140f410680880c1c488664081114003d54201c044511a541180c486a6140e40080c0a1300304203c064190440401d109204c2346606074480d56000c03940e4a030f4080403214404010304981c03a84058416801c00180c4580508041c41021a210503107030081400140d5800c0a109400b074580e001d840c0800400e4001d10a0186c1030740c1c04d01030007c0c898a540347c000ca0445015950f1540441d1042104196150003000c55034480c40301490a40a01d020b11408141035403815844a40460f040b000740045034070f0440301d00355005500c0700d0500b03c00c10304444900103410050b10302038000e50300c5200358082d584400d03070425801c41025004c003002d50743d24a0540c1d41c450040301c90030002100c01e842108141404021100034000d51410180115580c80705c42c00e05500000001144442410b180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 595750953 1250 595749703 595749719
    0x1b03190203120c25031109060a090e160b090117070906180506181026100e28060324021b030c0d110a03080c0d0f0209010f0806010507030c0c 62
    0xf4450b00791009000e2040f1451440c03c01b2440c40c2e4000220306c52615901040f26076141c0c146144202c994004001c0741820004c20000d0501e910040c0242002a441501080b11600d040081150202c03e9076030315a00c554014a880d01408107030303130a00025604210403c0401d2185410411004c03500d0f1056100559402c005549684002000507090642034007140c00c5113800d5413000c10048003030910710303221880c11312120041ca541c0c12140d086616a800481c01c40706120085002604021449611a040403244104c82030340540a0103490a1090800d4802d01e0086c0100403c51303a00c01c0580b40413240c072100c403007003402843c00014a00c541c2400b80348011090900c40c41b07507440c4160081c43e40d4000300b145003402d043c007901400c4240920010de41c801d0820005400700741c50b4251625004a840e40c19000c0c2e554480e920344a404141030440c1c00c0c48452196000f8030407414241c0b11035126061902c020b8500e404207c030010301040c410320800022070301a035508004a8840d01d03130281c44c01d45800d58 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 595752203 1250 595750953 595750993
    0x60103020d0513030801060503070f12090c06050d05060a03020603283611011b0605040308150901060f0c110907020c0907021902211b03190203120c 65
    0x81106a070381683d000605041d004180540076150f685041d51852030714810181c80503054201d001d0070081d0840b00280c1841103588185c8001e0790062480386120340c1c4a000520340e03000016450600303031902c00072030300320310706446d01600310703503020708110304541e2210010810406c0e4100126102c81e002ea40c910103201c0c95202d540c181c51040030080101c0001d805e40c0d8500d40818005141c0c441c40303503d5107800450001c0b4040100b940342460081c1140c9040d214421402610250042200e410312040c0010950801c0401e44242914254411b60086850421685100c28031900010640040c01c258031240720f001c80000c494001d0441d04000390107203020460980d0110b03030510050304644020b940c1407415140c45508a01e081c402003001c000c80c0902c140614514080007407007848045c0131100787d140c15403400229485050140e500c0314918140d20458a248025400e00c41c2c007035505141c50f410718007041d10356a9500a80180709819031700003030385456880f15030099018070400800314600041441c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 595753453 1250 595752203 595752211
    0x509090108030315010203070213090201050d0f0606030513030905010e0f090426040806011806091b030b030d090e13020307060215010e07053117061501090e060103020d05 75
    0x1c001c0d0b540c0e20703011254200c420b54110340f00e8115001008003030056550018003401c1a81e01c1c550014102201d40300588040c85004400740c0c0c80307400c0c88a542030001c4d03954041c000f103d0003500d050190340d64440494004d41040c2c440140464a002810312155218140c9400c0400f00a084016540c0000c800618050000c6504a5100221030591684005006140054140c00910301030406040c910050f07114001401189040210005044040141d9030050130080044241c1000242c105c404103800b4015203100c0c40300400d050103900c600702c1c02c0002d88802d95013280e98a1050031030811804400101000c0c1c900c12821441180c03000c050f0340c09111210041c40c03203030004c2c56003079411003000c1300702c1d28140d100031001c020420070001c00e281c200781103881d0040034400d44e007003000d881e00c0248454950784400d2080110808400f1484c442240c400c3c4a410100e6005c0b540d25960b20080b546500308550b17002800503c116004002003480540d025802140504001d03060001040d4551300700d40c0212 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 595754703 1250 595753453 595753469
    0xd1115060402041e050a050a0518070c0f030c0b0f010b0d050c0c01020f0d051005060306090a091205130816050d030c0605190c0908120c1507180b03130602070305090901 74
    0x8017000b051809661000041100355101d460140c9044000ba0104044811240317501c0040c0e00000c00b00d82c890040140c085621420508039884641401441541c9030101120300080150200741401c0c841e08644d412142c003464603629120b450191030001c3c04016102400041080c40781d101c02031001e00261400c0344d0f46498680e1074000040d4000b00fa0380010707020511100b001c0c001070015880e205c0440741d00c41e074107880459482e29104140d1004020011000d0700001d4092207a0040c158040b004008803022400d040800b15141e0011984440001000d00c0071a05610400c00c141c1c00c00d01c180e0900280a800d160300700f02042c0d182e500a6960851300c0b48280010035607041c10140b4203100e00c0d49038440b40d00d841c990150401512954442c014034282d452000f011941001e4810204220a0416070b0016800c89500306050f0142c001c03007051024044031030327a03914045508803030901520302c109200d015a29010303541d13403a90f038000d502803102941001400c014101c2913484d07000e0014028101c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 595755953 1250 595754703 595754759
    0x160f2a050c130b010906090b04091d010c02010b03011a030d0807120c0203031806070807140f0c03030603010c020f03070b0c0c19050d03060f090e0c09040b07020d111506040204 77
    0x100f0004004071282e4000c84284454020244000301d403000542e000ea50700d4034000121300c40040c1080300c0760b044031100a40300c0d60800070000300996041d0810343d80b140090b0002d0000c5c00402020303200b10310184100c030382c03d5402410890500d500c0b4010041e000741042c02c141001203580d99800055420b00080300016900020a104000c0340b24005c0794000150386014000c181000da0000700480006408142007000b01010705200207410000c403000d0712450044c4039500c43c801a400b0751242c004540c502c2c0300b546481291624580003040d00d03250850910061440c101c0c950f620180002c10141c01042082c000344003012111104101c06031402003400f00c40348220311a494040e1501480b40c40751404c0600f4182c00704040d4034403004840c156441510045110803018110900d0b0043d0700b00300a501101312810b220504c031801421034042d80c21503094a16041c1100e0007510f158140c0028018254016a55825010030201d41e654114400400141c502640d445011025101c036041c1d0074206240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 595757203 1250 595755953 595755971
    0x50318010206070f020c01030c020709090f0204060f0513020a05131d011a0412170f0310060c08070213110406030204141207030b07030212160f2a050c13 67
    0x4200b40c5900c8981d030b18020394903d00c020002501c0c2c50b82c005c56281031503210850444c000d0f0080c00348401615080c40200521002c0703003008281c01d0b9002ca4181e00692800d0400b00303070640006548000c2d600e000d010315007c3c0e9809503001c0005d500c10048403041000c140604500ba8100c207002d80c0041094004041d000081144d00642101046e40020801161046000302c584204d905032011a00e0810442e009003180c0c2c14900654101ca00d440da60100f0002031201c0781c0044c0c00f01640c0648101e8102d1030341e4a454117410b85050307102e4030000d040c0c10750130300805005260000034040310b41d0000502051001e0b44008000807504a80c0100380800d4000c64140013441a29004040680c81250048801032804d040c50351580e1560001405218030040010740c1c241c0a50112406100c0d6510f4203282481c21060215001c1640d020103030000380b9904030b201915208411030383c0b044041540107040ca042c000c2999400e100c6842c0122014068044000040e07a5100718001c481400c2c5000403c82030300c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 595758453 1250 595757203 595757207
    0x1120609020402070605040303150f05011110111306090f090203090a06111c091203150b040306060e07170c210a0b03011404050304090c05091002010903090b120604050a0905031801 79
    0x43c01e2ba10359440c52800f10301004450a03400029040322402c3c2018080c2d050510b40060130000307045288180d040c00d10001e10010300d0030320002d01ba086607009611344034079190081104c50071200c0c45140140040400140901c880d10b60056030869414000c0b920810707902c0c0e4030101598044007900d8590a00070a4600440c5c079107041007100212020f404012151361999441408032108000600b0169907010180103440310518000180c8208122140c07104c0e640d2810b82d014000314020b10211107122004191210f0003000b40506002c9400c12100103030385c1d007a42070207051b00704000920502004210324601ca540400c0c000307000d02c0501c0c402091031000c1c0010715094500700c65004840708569010800032600110640d1705980744c4190125141d252141c08540601400340125441604401d407598190340561000c007030b0920a4071128542980d4095140c594001c80e42c0401000300254005036441c07034030f0f0384200e5000d502c4500001b030b106010345800349590070005032808550b009004028541da = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 595759703 1250 595758453 595758461
    0x1110615120c1302090402071e050d09261606051201050109050d0809010215070314090303060616060621060506030a03200c040e030a0e040b060301120609020402070605040303 77
    0x481d10002445141c10b800c011030001c010f0380f403030030000990128070130005940350b0301250b15454000e81d80841501c4030300242d4000c408404001c65043c410003958009980c05007440d04200c4001c110000d00c001800044050500001840c031803403809041444001041038a5510000d0300c91696a1510703040300721440d003141c8806800c164180090700004112036039803100d91214640e80700300c03540c1d10b9a100d18010b034900040580a68655811380c0304010391207505900c40703900140444080500364803603c2c0001d85a2205075940754010404014070703001145000c92842c0504c1c410400010f445588501501c3d8140703c0c1d00031142440e40c0340c3e10290038004140522070300218201e01030084001d20fa41d0140106840101e10091401e4840240055000a00885100e550090800c0c004050800034041c0ca81d0310160b60b09010503c0c40c2041c42141c2001d00ca18051400080c0041c0d1940c0d0801c2540a82c0003036007141264080e4a5a08150050300d81780082c03c6100d01c24038000c10642050710303000c2d06807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 595760953 1250 595759703 595759729
    0x10f030611070b010b1303020d030c1a0411010c050f030c210f031306090204110d06120c140d080a0201060303200a0b07020309210706050c03030f0601110615 69
    0x9a1002e00494000c80d1550014a04407040556095550721b40710019061b800032552001e5030048803a80020309040d042400c0b0090f0318860280c40c0d810149013118102401c2c419580a00b01c1900c007005024254058925040064000c0b411540545002c96120345154005207050070f031508000140d8200341e50010811440e00d0044030440d0a081e961b00c08252280802004080c007000381c103a4803002c3c02300690215028071340162041c483c1d2811440d8070007565200302c00c84020710340f13085170010b008682d00d0407120b4020b03880b503640040340e4582140712074012000b050703103580885c15612450003d04850010138444d01c00c1d40020030340c1c0b85181000b030607000d5000007134541d0b000001d81190070120081030344003003154004020b2129031a6180120318501883c030405820085c104010008101140402101c030403020040301c103040c0d29800d040301d170350280c80f62a6803598414030110740d602071070140c0c86074041010f141401080f03203894081f41c0b500f18152003141c881c0607104c0c8030b80b140f03080c0b40c2004800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 595762203 1250 595760953 595760981
    0x9060c16031407080604020409110d031e030c081602012c06070306030305161704090204050a14031e0c0a0308030a0501090b010203071e080f031e0f06190e010f0306 72
    0x5007900d4031644c40c0c0c88440041009220300d54032400c8404100401040c1d0300208000b400c081c80f41e03085450080e00b81070140142c0500d0b07004030a01c0c44940c601c03034080c17492081603031740c0c407080c15032101d200c00c1c0744070340062040c01c0a40d500c0b0101c059031a41c07524800d1101e90b81c1000e21008100b64030080d0750500001500c004101400c00d841480880c0c0c000044540e6007041504007151110340307040c20040c00e99003e91400c40c000c40000d000903031030354580240c4103455013103518010701a50303118800b051884112015416400240490f0600c4024425007240c4034030b810191a91180d1010002e000030009030805c603402e80c808014003181c2c200500c00c5c0e50141030b010008015211a07940044c0d564060a28014405490100150070141d0507105840300710768442038250720b0701d00c60281d0314065041164181c401c2007003842c40380b50811213007600034019811418205042d407210000d1003503e0900d411002d9402010110000311044403c15440c000c110fa040918101401e41ca401810380d0107100d80600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 595763453 1250 595762203 595762213
    0x903090f030a06020f0a0e030d0530011202090c131a0f0313050105070e150a02120703020109050d050403020d080c0c030607020c0a23091314010609050a0c0906030209060c160314 78
    0x540980003803c03101c125070202800141e54088442d1414404010317000b64101c0485180000340ca2035450304498dd55034401c407000d4503c2d035a541405401801410602e440300400c20404100888007019642010302640e50754034030340042c40700c07580303101c0c1e20613100e901141003003852100c05e01200303110302d64003c203c1c4e245c543c04007000d8100140d0040041c1c1c841702c14070b05c00010074100c100d00800540c0b808958076008203407155124100a03008128115040d1018000c03031240b01180c80c4901c08403025a50700901c140503051550305c5070355140d002004125421300c01c080401d152a0340c204070a910078400c81c5d004145204c07401040c0828004280c1c01140501c3e481040300c030b141c0c3d0843c590102a040191410300302d0340d880080000c1c500300c0c1d10501038001c80c001c000c00d61100d030041d000300c025948e10071000d00003600c409011130211040b0300446d4000074503100d814404603110390000d212045008103200d003001c00c0c042c0d006040403100d0040400790500401c08208111030003111940c40e15280010741 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 595764703 1250 595763453 595763473
    0xf09033301080c090408160c03060c390804030f050a020427060c050f0c0102180d050c240d020309240711070308030a0b0301140903090f030a06020f0a0e03 68
    0x7070b2244c600640020007001000c40e800c070080300d8503a5001c0c1d98907081301043c20010382d01e06140d8001c0503500a15800034104150004010b0b8160282c0c56038001ca0054a403000c0d100b90041000708421082c00700d655100401000010a284400d181c210900400c094810140c0e0361040000325044002c1c5000700343c0444a80480c00040b00f90a00072690308000085013010010b0380c201e03403d105410380200b0300c1001040d0100c50305030550261000c81310004220308500e03400c600300a000c40310b11000400303550000704042c41c1800c003140c0030030609103040c071026070114403a10011241c4c3c0050031002081907012041103803c1d2010003010240420004140000b8030308000d058584c250020203c80c14040703100c004a00482c0208081002550004240358580c10326a070418050072168100c0c3d0b11039820000341c054070b0710301031140c24091908000114a0000e04d01c0c10b010420407070f051000c1c2d02d07001d000e01881c04a41640000d0441100044035203549854001b00503000400c0ca5035854007a0344440b1810f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 595765953 1250 595764703 595764709
    0x1d0d02010531050a0803011a1207110a06060909030e0402070f02240301030308040203060901111614030c0102120c0307020d0c0809030106030507090608120f09033301080c 75
    0x222440650950b01208101080c0039110a24544010000c0c524032a480d40c1c00c00303022080307010f141600c0c0072100d801e01c40306084d0400003150144403102c00403024080041000300c0d000321521210300c800201655501c2c10b246d1140402c5461990129101d640c440c110301d401c05a202e1880c9081146c01c607011403d00c0101e454244207010001c80080c0107c0070314070858008101c80b0380007000c2405030112195a0368592a00806104003910100e000344146004554420018000c84407108030241c08541405503144040003554600c11050b1214110741c0b0280032030384c805100901c1107180c8100056500c60f035010003802000001004000c10003414424040025400704284507511541d1030070b07041c841110300b4070380c40b18440c60000c076602d513103401750000800801041e20b000325400f0380c0781089040e80c0c518030741da1070f0b0410601c2d01d04410000c003d2503a9903540035000e01662000a011204511980d4a0f2450b0015005044009015074403880e070011000380d013007540c09400e0560141c000b800c0281d002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 595767203 1250 595765953 595765981
    0x1f0b0405040c050f0112020309010b090702010506030a1209050927030705061306020c160513020901021504031403130c21061d01021803010f05010501050f0a050d1d0d020105 76
    0x580340c0b1030543d50089050581c0301b80c090312201216114219500d0a28220701d600800706043e11500410b503010004108034010700c01e1620400c0d01030060100307610166565034812280009038000d0005148000c078242d00c1c0c05620611400200c084400704214000171346040c04190141c0d090380798420003070000064404150b01c1d40020101407940c0805441d0310303101e40030380200154105980300705030700d100c2075035190200b01d0201c400a03608440c0c1d03200c2000f100010f0344170340079840d80540c3c00740d20481618920090540d07441802441c250003500200215440740e5442950540c101206521916040c05400b01444004114420001c20a00b0f500f0081c40d0381c5054a88000e80511760311844c0240c2079207008184210034407a5802155140b00204180c07c904141c648520302039844c0c88900509802244203c038144c80058407000c1c1404a00710b0705899036030006502500b0081d06010300c2c00054024010032070322400480f1041d0303030f010003010340c5841c0002403c107400840e81082e05000310040c000314 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 595768453 1250 595767203 595767209
    0xa0c030312060504020c100c1805131b020a0c090504031205100806070917030f0304020904030e1804030314010b0a030c02071d010f0b04061b060b031f0b0405040c 71
    0xc0201407004000d06410040042da03001c541c0050001900c40c0c081c1e8008144040340c14070001d4100041101658200c0703c20400030580b41031b01c480000140310a00d840d90b01000305140c50000454a010308403160b9000203000c017100b40c0540c8c800500f401c104001c0544c404050441c15904005a10341a1801041003c005003004001591940030440e422800f554280c05011001c0c201c60160400401c000c09110980c800c100300e5400400140d00030f00404403c846011405c0080241107844039000c02401540140c0f0807000e0000c00303510000f654450640b07441c03030781421020a0340c5904d41401d002c0c00b51130312000107003444013070400103005441c442e000351110b1801518002035510107500c030580c81d0100c2c2d5001802c1c0070610f001c0c83c0280d40f907523010440c103941c014607502c0d01d041da803104c501b0310303d0150b40030300f002196031469511140300d0554210044540100340118500034400d022a041c25110740c280741d1020841e11204001c40140c1c000c00c200c08100750340401403440c003601e5403c00c5d40a540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 595769703 1250 595768453 595768457
    0x312021005070c110f0a08160b0f07030f051204060603150506090408222603070f030302090607081603080912040e040c1802070515040305030a0c091a0c07080a0c0303 73
    0x13220341129205c2c01c00328501800040c00d90510b6680b40c0912a41d19518411500d44200103602c002c01c2030346990b026125031200000e00d083c203001c0380e5a01030b10044485944072040160507c0311440000003618411300850084200050203804d5040440e210401400704054030350034081440790035152107242c0703940309401c4040107440c1d45141c400d0b10286240407820301054034640303002203441031803c05074011018002d40354038030000704242099102d01514170003400b10502110040c003c64000e030003d10003010000d107620b182150756500c803d51074100d603505495071402800fa0134101500080741c9a00280c000c0d004018050003d4a502c0061041c0e0050500b10482500440c4c100a90703803400782c0241074480d01c00b21540e80d094940304000e41190344151041d04c10345000c601100603103140f450207140c241e954549103680c1c84c2100c20280001d45c0421041090700000018000c611003516404d200d240c415a940e19814607201c10310300039654200b421650041c501440004229401c00011a035240c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 595770953 1250 595769703 595769723
    0x1e060f090903190827100c0219030216090204230d0f0b090607210905100203010617010e0105030319030b060f040e070206090d03020d020904060312021005070c 70
    0x52079041c1c1107014802d05855103030440b82541d480582c000d0040f510961042205006415000c4101d80c0b9241c5100d94890f29600004403440c0074540381d801905481c00580125455002c0e10241c62200f02c008080a80c0160007941e0f12217000c01e42099030320005d002c04141941020304110469002c50804d05860541d000c0184024200b5106d164030070700c0c1260010b4503002d09440c20309002941104c21150020389005410004092074025040103000756030000a030811548142c10f414020450b02a05030340078840c07920810b00c1c00c3c00c90b00086018002aa5500510400880c2424204401031308070b05801d024590042c0f01c80c1c0c07400029641d4410b030b030440c4c1814429002d001a8000c040320169103801080020744c604003050340707800030411101003480009640e550800101c1e01d0b00c506441d607a4081d0400c1034400b061601c42e070040d0090f5100314400500d41010320000804480866104844150f992820700404980601c20008030840c1548141f004d854801c40003062440c061200404040203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 595772203 1250 595770953 595770961
    0xc15170604180c0311011107031a33030714150f0c0303010608061c2a0e010305100506010206250c0203100504020406080f03180d020a09051e060f09 65
    0x944101e07103482d035040b0150620007a03d82c1041e1401d000210500d501185c40e103695a403082d1400202e8404494111031540301c04a01002840f01202e4060031580d00b090510003203068407107950031000d90b1310070400a030500d01060301007403504161030780e84441d401411450990301e44d52544500b00b007010968040c1c0a50b03038001c600072903503140140d04e000700c041e20001c00003155094100e104913014030401c448d066141400412400e221b441035600042c1070040d540c2801000074401001e413030701400c072000d40140950300c402c1c61030a00d9009074002e940503840000c07143c03042c1415201342500514284040c110324030f00705040c4000039115482400ca1000001040ba1009124081018003268010152032020100032034100203014181d400340d21039440c1040014185400250554908000001035030510b0180c1d0805000c0102031840e40d41c01c40180205400144d8801c02d6020242000d8800001c031828050080f202c0400b0f0083c0e40c020749182807041c0041551514040718080204444200e81507031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 595773453 1250 595772203 595772231
    0x9010b01090b121611030d0c091a07020f01030204050d050c09070f09031e021305090609031908040501060302090108060a0c0e0109050603070903080301170609120406110307020603040c15170604 85
    0x1c1c5c2241080c0d140e000108100341c10071a59005141c070040c0c40d5440074001610b0b03000390a04403010620210365401704103d107400504040301c1c048902d6005050050030f06590b44003140000701200011111741c0c102c2988820f040c81e00400d038581090745490807007860030a0f10406070580c0142e000150003295800a0345208080310841004140d6010b803403a2000d09010004101904054408254a0090340001140c4210000640c4c0031000688401d40c444251038405584914000d042039909548030030010002da02e07100e51803070080c04104000c00d402d16012200302c00301c80b100d213203070300803c0f20325070800300c041e81d00400e604262a0300302c44295484d280d6540940340c0c1c00f240e40c4007c000c0070002c0000954100c14400310800010a0302c15580c0343d0307071454413064846c02c401d8101c520114042c0001e00c0b15070301c10041d4039402044003080303038a840e0003a000501e2030341007118203c03021443e0710001d0003158140302d006401210641840110319030b14458030f4183c4c0c203005040364021b036900c0c407070040601 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 595774703 1250 595773453 595773467
    0x1104032301022b0c0305100603150b0c0d0206010906050607150e060403120b0306130f0c080a05010b040b0f01140a090b0d0204090b0a231809010b01090b1216 69
    0xc8454894443c01c5407038103415180314405582d100c100d5a29088400360582c3c040d014080c0704500c0701040d62045420000c06500030900406c01c4075600e58008008984290381c1402032400c9400c2c44000d0101c1e6040c0c020080c0f0300030050304200c1e0b11604003d070404c01512004103030b40340740b41d011015130920300f10b4403501001455003400129180c4910820f0009240e041a061070070b03a025180c003800402003560501d9514a0159540c0c6407640c000701000340852045502003603071921903aa03c01100d03541314800e17460414610011b90380c1f0795440c0c0c02c8010521307243c441c030120300344183d03107000c401c61604001034251252184840044a80050103034541c070300c10149032000c0c1c2003c0c0403480e211241c01d540b020094000340a407031500c03860491880c42034034101c20450100d540541c001802000705160f90b03500c420311802125003000d180c1c0c003404584000424598443c1d40450000200d000c0c54034001411010f8131341c410641807404100c00312405a145443d00da01030000181c1c0030500d24001421a805 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 595775953 1250 595774703 595774717
    0x402090c0c060403080f0a02250206040506030a06081b01080f04030207050d051c0912150f020301030803040c05010e01050a03180507030b15010201020a170601110105011206110403230102 82
    0x1e80a401d04001c03c0580003540280144500b00b0b0102050391084144c2040744101e0300405070100405460800c413600b001403210f013141c40134141038186940d400c00706d46950030540f000c4039500d466807828405045d00f0032094840854040403107500340d0a510001c1e00e0003102520103000341511000080602d4020002000101805410400301c40424100b8a4480b80074203260b08201d00000c00000030f0758480e0300406c0643d4810f0312602c00750a1181d490400708020708001c2d1990781d807100c00d0500d1954a41c800346000f0350040d090143c1d01c0c503103441e01400b5100a9006a818049290100645640e000090305d20280d201c1c1000558118920070781c1036148607407900200130b0f01c00c04c0d901000300084080203d00030358606c021805616084070040e4240c1c02607641d24800100c0c1d80410144c0c0c20700d941d08060b0441d9043c10310303100d400e0352020f030642521800d0b00150581c003100701010080021600c00c280c04030a4550003141440d05660361029000c5000408001c4065680c5020b02203400a5046403c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 595777203 1250 595775953 595775977
    0x504061118030616020705130f050a0911030a11100318030302070308010609060807050f07060903050324030703021513030302070e01120c050111030c0a05060f1006080402090c 77
    0x31240c01219078159503455100480c02800ba2a0210f9459181d84565043c2d054180d00078109032410841803101e0080421a010429620795a044070f0302e91091050034007480441c04040342d40401d80c1820b0136128101040da074002d504c84846480451a041d501d020041001c0b10540001254007104401400c03111030003043d485c0c404610341c41050b8042d8002c122803803194995403a903aa890f034080d183e04505200748400700d41c03080001154140b00d00002c20600030001c1040782010314945903201100c00340407040700490301c00000d021342d0714511030300c01d500074070390314500315079881d0b8a0017081d00c0d510a888000d002d0320780080012030f14000b2000340ea00c3c180e102003601c58416683d082c029540d000350301c03c05000c42038003c00801c0c11102d11805104a0380c118014040d45480c0c200110f40030301c01c1d02284040c03408180034880e00180e013403007030709040e40c0948000d1889081c601191481640040c18175403010f401e80300100325030fa4000840b03039071041d01182c00c0c40c901d1790f50380c502e01c07107a104840107880 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 595778453 1250 595777203 595777207
    0x1b010908030d1a060703050a360e0105191701021b01060501140306090601180807060504151115040f0816112b02030106150504090c050307090905040611 67
    0x14a5107441c2e400111110000b0705a03010b540c90074418400f192186200c0076000403420400a00100c0c068201d13110340802e00310728207118907011170001d15000c51034526012070270000c540810084400086c414050541161940004403142003502003c038801d20a034940c0740b101c52140002d008003075050740d2815480302e11035140341140c10100b40c000d04150040b00c1c0800d05c41e00e04145035002a40589215041c00740c403620681d11610015282c200685d40d503001c50210b60b02e070214054000b4131000000381172030348895132a10305004004444500400100d410040c80003c40305010000203403990305240042c050000344d40760703414040784082202002170042e62001a221806c4c100d00340343d284185010324a0700340c00c00803500811000a80030244403945003104056422245958407240310107620003400010040e9840e0a802c1006001648101c08140086400c1016001d10b000c1c3c08a914886c2c035005145191652010301061043d001307801340241c1d2070002408002803548001c045c00d6035110666 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 595779703 1250 595778453 595778467
    0x2103130f0609060201090b040b0613240b0a02030a121b080a1805070501050c1e15070503010b041a090a09020a140301030b0106030e0a0c080307060c0e01021b01090803 73
    0x2508034400d20030440094400c00c0002503480c07042c403c09201039842040000c854465440780008014003508445d840f06811403441d030a6105481000b00d90002d4031106081284045503400124400c3c6d4040f41941404100b000078140d80403003254041911400c0c4040350880302c02100c401002c8680c1424007996070311080100e150740005002e4032461132014280300007030403001001c0300c040c51080001c145610a950a00c075035070141c8007a220b024a60011181002084d8800010703500c070104e1201d515404c01c0340c0801300b600c902e01c05c1d15440f07212801c04514551404800c100248507034416055032103810b0280215000c44881102c030907030401040c1c00021525840504000c0d0710410908001c142030040510500c000c84c0280c90481c2d402a40700c40e01a840c103141680544030306c7c00055054020082c1e040009030007843d120f009040c3c07410065071550441c1c54000100d40307400f201041402000514a10140ea0000d039403c1480b60031400070090941c41030040c1e0b2607030036a8000381c0c00ca000c042605 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 595780953 1250 595779703 595779719
    0xf140f04151208190221030c1c0209280603110705030a030e0c030a020d0803180d020114060a080604020d02061306021b0d08040e0c070f08090406090b210313 69
    0x29000c101d890004d09100c1e150389450690351032001d080e4640c14154000040340c00f201010000c1c540c01080c20a00903d44100950a0ba190202e02c190b040156a40864180c519082800c800042c0c1304500740180e91103d052814003c140890b8801e1004041c1c580381200e41c10500700b0150f481a55115045a4035404001005405401d054950003058411a19501c01500e00098a4401140c0142841e0600c008980324401a40d000601c01007050100780c94110b503180c010003018200900d9640009103a05503008070162244000d01494450740d80440c0c1032040d40b0020404940066040380c10a6280382e43d44045012401100d00c244071103002600f0001d04541c0220b00502c0c0c1c1003100316600b0392900d0800801803254075002014041110a1200b403107282c001c0078201c5c1e0005010120281410103650710a03104942d141411190700300007046030204c9007094001c0784080d05030003e080c0141401240411811500c070301c01e0800031660380082e80140c080500441d005510369833452005580c451030a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 595782203 1250 595780953 595780957
    0x1080f0f220f03030c0f0c08030603030c250504141501030f02041e0b07080a0f11160612050402030c011805030105010f05090c030603071802130303090f140f04151208 73
    0x81500030a080c0b49017400c40b244210482081c000302610b40800d0000143c0b510790880d0002408950544804c0040c100494403c02c0841d82c80800d03003220301040c00c0030441000c095543c079070049014a003051507075010b1800380980f0a511411003041480c50f08140700048000d400301e03450120180f880060081044244080707040802e600400d4480116640c408e20001c45104001019205420601c4007032030782440381441051510b072030310740307400340e00002041c240c2403110382000700703c184003101020800305821690120804c444000100806d140940100782c036001e1070990a410802482034a010103040010444080e0a001e802000190f0b105c03000c0000c1188180116485480307140000340c2c3e42c0c0203180c00c0b64403a80c000340207001250f2600c84480c10480c45544403040f4580c090001e48840c080c0b060b04500114001c4d40c80c908000d02d4030440c540d4007081908080c000040c000101201398039016010600d505050b2800624070303403954005001400301c0c0d0002014001ca003e8914107005070800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 595783453 1250 595782203 595782233
    0x606120a0506010e1503060906030a050d02060f070c050c040c121530030c020a080f0105011a040e040f0c031e02010e09090a0b04060b03010e01021801080f0f22 70
    0x2601400801084c0400141c0d40d070012110708100c404000044560421100d4507405c0400502101c40c1200325640f010300b0f20b401d00101d180160320150810940035898840d060300107a29041c1144410901d81ba8261581c900207140b81c06203889002e030b262407620036850320110f40d1500030100304140040c0c41c8280010340c54841c0c049429130900b801024a1041c4281e800a69450704001e4407058042c1d03016144280c061318181d81c0b00c9207205001a41c0c000920041034000340130000040c1d1907040080105408241940e0ba05002c00140014003070f40486042c2207801c02d4002c460a18a12402d2500b00c00103281ca400003000105407140280032160005002070301980300342ca903001010080e40030302801c00c0040341c085202c0d51040c1180404581340290040c1c22074001e4402041840310384003c41c0c00d60341e0074500e400b0980c0d4009980751952440920002c1d84980034a00790300349081205410034089005460030f81920200c4000c10b0110200907414002403c0200540080c2559810300d2805985215 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 595784703 1250 595783453 595783457
    0x30304150815010302190807052701021c050414031c1205090d1707110105011401090b03011202060f040312051207030e030f0c0c15030106022b080606120a050601 71
    0x120402c403980240240d03190103485017600d124440c910401202e19100c0508003205105081183c0760a02071003070300507600700d40c6100042c0e481c012203200081c41d12a400c81c11800f400c900130b07203808500b61310074101c40484900310382d8649040b1001d03000908042102000c0e00c18521010804110107401050304500f0303001c0c041c0c04005680d07840311860b881d54078520906c400a100c20b0840010414440e0800d900b0000d40e08e0300f84030000d4081d140908560080c5c005840b480080301c03035010b40d50f900c650a000501442461107080d0f51400c00701c100351403513910000b44030b00e40c04501c844080141c00c003954006c45e0031541d0415140d40c941405451980700c5859001c0b40c0c03100d100024145406030140700c041201050045203014441703074012401b50040d1480e0902e50180402060690351403210000000610180007070340e0f540b4141003c1e1801c01e400702084111280c0318503a07000c9618004044800400c11304082d121643e42d007000810900c15801003c417504a0303842400700711075890303220328444c7c4c0302a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 595785953 1250 595784703 595784731
    0x90e0c01140903150a0f1d010f090218060123070312021c020913140f0105010c080a080a0209090a0e010606020307150f060b0d0e01110406080f060303041508 69
    0x201e403008200b0320542003042c0d050383c0061011850074040d0f03150aa0700452000d8001032540b0340c41802c0084d14005508410065070385201c1100038942880343d4405501040420081002e80340e000c80c1408425880010200d44641c0004810380d000710034804402c00c40480701040800c00000000d5150800305090300015a10405201e03048014400c458400034101644200c56081e43d0340302000c2e6205090150304030400080341c080990484c01610740c00419a030704600a864400c54440c01d00005900060400c00002010b1000c01c10310402c9400e1071000e032074a5416651041c542002901c52031000c41d800c0940c205c00c115600003107503c14a10300500c2c03002407000c0e550f201c40c02c07039881c05001c8015248541540308405049615404102101c2101d100466203582e2844009007a401005083c1d1400741c8440c0030145541d8288103580c04510705041550409052074001000100010600320031b92100c000070945030380e07040050314010014030024149420710004002d00042c0152800c5100e1017075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 595787203 1250 595785953 595785977
    0x30f1203050702030d05270604110a0605030703020a0c0f0f1a011a1602031e10020f030610030b06030a020c01110301141009030c150f020a03081f090e0c01 68
    0xc41d01440740100b070181c0c015030a1440782903001e402454050420351002e010040e482512032004001e44007050400400b90100d482d00e410040700c05820603407020302c54200c02c80148140c13900842600c4d00021140340040e04c500c1c1f030f20790607600a00d03400009000700480640c68400c100000e001c04c28902c0c4038100b1070f504641814200d000c242e2080c0a4090100c3c0070b84403009640c840c000c084c10346504581000101d800523500403070b0400800e0408040c06084071203091301c4030001003101c20620000020214a04503c001281400c5d01001d80007510031030100803940075140c030a800442001d44000e010304da41c0d0804a4451000b0f50010805410f103508140203c15440303250300589040b10104424441c2280a40d410409600003664041d024014002004170214103c400c020019080180f40c0320a4002d00c614040e0182c204806110704541c04103040303500080d40030f5881c0d03800041280c203d60b05c00e0102010829070b856179404c01e401240c0707444038030321904c3c80c0014885140c813020f0b02c4030341d20041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 595788453 1250 595787203 595787207
    0x30b0f220e03040f180b010f050c0312130c08030306010e0f0f1e040b0114090405100b13030c12150506060c010213050a15080f1504020d0501061b0b0c180307030f12 72
    0x2803440c0380c03140841d50b6149101c010340d0159009014180c0b2b18000d07030f403502a060101102c0320f1010380c1c0500e21002080904010041c070352580340090071205006505610300131000030041d03500c546c42603000e01803d050100306925802016140984000c004070040031050449080400003500900d01c90350800b42d01d46003a50003004003c80701015001424a0480f459090201500c07000d007000100b02c099100008035640008054603011040441d22000a03165003060082a140b58102045200070400c810f400240030b0540c00d41d032a200c912000c6036990384c200c005441030003001c0020700f46500016040c40308146040301601620f008641c44a00703542c0721316004011840e0000740c200441c0411022401d8056024003607544041426841d41045584c1400320b02a03030051003080820a441d0030046c0020b9812045482180b01007485440c03d03080c003600e401410103c040c00d14600800001003902c220200c040071a41003401c042e0407107860b03617643e280c1b0313201d045d01c00f000c10303950820b00120f600700080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 595789703 1250 595788453 595788461
    0x10050f0d21080a0612080703050405090c0301090f0605010e01031a06070c050306010605030405060a0b0a0f08030d060603020c030711030a020a0806011502160501031821030b0f220e03040f18 83
    0x105c001d0414130a5901e103548090403580900011f405202083c40005040d941c1e1908007031161341e0501c000c0707480c0c0d49071642280680c3c1000d01100c60541c1007000a22559034440c42c1500a00402d10340070031030460400e036180a8080031460690860703000955001445490302202013191825412114560b0b0b80385001c0300c0d40e00040c1c5000f041074000201165020030660869201c140740140740301c0070966140280c942c10106680f00e5503541d0004242c0940ea03a80794400c02000305181d0609510307120b80c1102d4a074680c03240600c001c141140494020855440c03c001e140035496000e42000c80e01a203500c0f12682d58a001d1250703243c6802c0a85c0078491503840414240c42d84420040080c240600f00401500540b1382c8214000c0c1d0541c0c0c04102c03031f010130803040119403400705101580c803002c01c4010700201614540724099004e9802210300da0380310740f54240c9010300401c01c040840b10a45552494502600300d256544174144408200840d4030a1400d035040708441003245c01d0204030613004448001c2d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 595790953 1250 595789703 595789709
    0x6091410050a11150f160f0906031e0207031e0906080a020306030a061a18010f0b0903070f27050f0402040c0507150e06070810050f0d21080a06 63
    0x2034814480c0d1102c841c000c0c1c100350b0410105a0130384d211292441800e100081d0304030f4080060034104c0f01801017131413088605c5107040403989071010300c0d0007445401501504191140c0000c1658809028895a0311320002092160200314207558034503460030020305440c0042400c0c02409862000c14205500464092f000c81e83c0710703141c00350207503a03030b0141d40000e41008140c179815028541080000074003038414038103a684007042403450183d9003001c1c0014404900c030880c039201010070041c000140c20140403c11165016001c07552000c4100c0801e09000031079000c640c41c4080b1402c04124030004070402004040b00b03502c441000a881541c14041d1103054a450f00300c61400000700c0d003d41010307084008050601e003000d03442c01c8429501c50032070500c0f040e500305070329566104140303980f842401115003100b010b1800c10500d0078138002c074500070794107880f03494440c500b04044405e1030340394901010080780c2c0040c644941440d0340d030280380c492640515440c0c001904c060016a101107280324140c01d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 595792203 1250 595790953 595790957
    0xa050909031e18040b04180c0e1803030c2104033b040b0420030103050c030d270b0406030507022a15120910050a09121b060606091410 59
    0x40f14000800c1c44000d00400200741d070400d440d1100c0400300c11038580c6e80402a4481c20103044a2807516000110803800500006900102c15911000000c800030035a50442208070000da81c2e07210200c520100c0c2c2251900d601e18a6007030104000c141a001000848000c140c2c1c080c060981da01a03400700110125601c4103180c60f41c000000b500349040540c400e1501031005000000e41486000b00c4203000c0c1540b024500810a002005108106082c003131016000011350050440d645011000b07040d00b00030460141001080e80b91308114000244541d200400321203411564481d180c0710028094041101c4030000740c89107010f00b9485600500b0700b60100100510ac14220100d00003c20100042c10b400410b0b06002c180701c440f0b843c1c081082d000b401500c0c104010000c0c0ba0244a40030141d0302c008202d8502c261a20b042440800c040380200300c200c2d000e6142031345400405a0148244a00064025001600d8070002148260304a0510307426180340025030400100342c6800c000302e500e006444000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 595793453 1250 595792203 595792237
    0xe1e091603150b12030a030e030a051c060302060a03050601031503031e05070204060807030203070911090103020a0507200f1909180501050702160b0c060103030e0a050909031e 77
    0x110b07400e145480d042454040c40440c54001c0d0900040c0124a401c448454903080040c10b601225054405c0c0d801680100000d503040a035050f00c060001d000325919404d0300c10b1610403100d21003056a009001a5a004001d00c3c0c81d801c3d0f0300c0c0010000c0204480c41404640303000001e02c6100e40c600f22040440750305030360321441311118001e2300c00c3e4500c00342625028000244070480042c1e60754006e030009858013000800c41c1600e18010589400035a03440b03080c0f09840c0c070350410707c9090100100d031050142030901594404806030100c0ea035100b003440180002c0386210300000700301c2d11140c03000d20344c40c801ca0300410321490003001c0119552803811010b400700c01c014001c00c20000103410160340b541c110a55809107403d1178541ca42510411900ca00040e04444801c10b48040c050000b200984100302c4200d041404092034641d0703504040c0030150038800911202109950750300e1180340949005030100c20382c1e003041584aa525009800050007441c4040c1940c00c91244c480c0607920030f0207038210005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 595794703 1250 595793453 595793459
    0x1e130b07120603020612070e150a0305060f0d0609060b01030b06070209220c06020715171801020a0206060907020d08011403072d0b03010506180a0e1e0916 68
    0x260348079010404401110b0344400c070010150b59190090a40402d5168003045580f0700048001e0091a4403a80140b0403104098804111095003081d01d0f0781203414100000d05031218400201c1401d400481160702a0f03c20344064100141c50700b1034091076100b45018049a0b18103801036040d900401d40040d002101402204050b140281c3c50580060116444090b032444111aa0394034845500e030594072215803140800000340d0410140740100b07428030b5614040192007a0041140a603a0101030710310410801007800c10100c52081d5200b03c4844008554070101c250b4040c0d2111821240b0340e00c1124000009854940049070203012114150f9400869a007045a5482c80e54641202c2c070303405100d003600115065645c420f1070181681d05403600b40824039603030780c5041881d03407940244811201c1030004115070b4039217405540030041c81c2c40d490844080d074840071482e09a0503a0080710f891000c2d0301071040d0031b400c802140419030340204001000b541d85c521125964200340030b0802d03001c0e10480c0c1c20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 595795953 1250 595794703 595794707
    0x9030e01030b0d061a03030705071e0e0703051b13050a051c080315090112020f0d120f0e030703030c15110910020c0306040302072c0403110a0602031e130b07 69
    0x1c3d81000803101c035016221700e2460b0109155420291045600342c1c0080e00900a0000b42e940d0105140d00041d00100d0540c14980d030f05181c020050941400c1c180c0354000304101d8446c80601c1800214a045210b031903040c4240041290401c0f4803490340070300047c0c031300415242130481c49000d501005114007152900d20f96103502540e800189640c0414444060305602a540c00c44042d009041901000200c1c1409004010000e02070000b15841042c5561040c4000f500c440c1030300034030000c1ea0030700e05a001100030042d14100c4c00f4094256050107816408803c054102d03400d1140240070b0702c0e80420100d02c104007003003142c01c80700740f0041c4240c00303122481c0146030500d00c041021140741f069411054990300802d2900c5400e8800300d015811030003081c01010034880310703000c1140481d484000200d4003a5641442124054000380802250045440001208100c964425a489441107540740382142001915100c0341841900141920300450f03040000d031490001e0040e000015104c1a031160202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 595797203 1250 595795953 595795961
    0x1022508070f0c030b01090209010306170d0f090b07050102030a1506090909151814210a05040e0f0103030e010e01020c13061701140615040312030b060c0109030e01030b0d06 76
    0x1c2282c100f1080c41c4003100181d00008468000e1118400242e02d07038a00c08005819981144c00883c0518004440c1a2000e000011041d0511049040600c00e8090f40582101c01c0c5d100fa0300218000280080d03c2010070005500451040c8400e8104120020040900a8908529100c0c1000003040076100384180c40d1542c2c0a817022502c60040702c40c010710500440c505450710302410681420503242844140301c54032840c090b644011801500200000f09a248074481c200361040c3d01000021680084080c05001210301501400000d83c4d1a071030265585000300100740030481c001000c84010b041e0035401203080400b4050144c0150901404010511900c50412806130403c0c6845210000e4001d4500500744501d071801c0300080b82c40c070700006034400b245101800c6c0398011340102c9800042101c3d180155015640d1108101f071403c03c0c14101140038001c14040d095001d840001c8c11400d600d01548403c442a20a80325484074040000041d0112242c180b092034011503000c03004000032300c413544 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 595798453 1250 595797203 595797233
    0x90a0902030a1e0b090606030c0708160606270204060909090221010b12030301080703080c0c150d1505010503070f02071511100c0e0f210102250807 65
    0x100014003540080303100f0440c0b4010a084260465075100c00d101d65050a00b4074030341c462000c0d2203040c035508001500952900c950038014044103c003003801d619645420142c0c488403a08200e05201c01c40e00d0b82d440715100c0c940782e440d125180aa103940005200618001e03a421141c154480e4800c142c034242d0682d02034030280d401260f202c030741c1452134002c8202115500301c48804036000008c001c40540188921462031007281803071940280010400b01000003540710603a903010080300d0705c034801641041c2c0f90400760b01825601c580c1e80c000e02c0340c40f4021342000d0703c0044801c20b400c2c4444221807040744441e04541c080c0728001041000003441141c040e00c50603641070400c0c811114055900c0c0c0c1d00314502105450720000080c00c0740c0c0364034552242004018142c8200703070b41c20069044401d41c0541085220785055025000c043c00303505455503010240140691410381903d6000300d041d440318000e41c0080f9542014500da10084c840029000c3c03141540f6961050040703280c8421b54480c0f984440780a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 595799703 1250 595798453 595798471
    0x80a0c05100c020115050409080a0f141207120e07060809070e090102182d0f06070308090f0d09050d06061a0706060b07021804030516080c010c05090a090203 69
    0xc84001c002141d501c60400000c5080d400007460070084500040d11864a5211600c21410416203401107003440d021079500710711a042130303600140801c0040d1440c072000958a1400e00b00031800c0e441130341d803c04416108051560350100911081040d0004681d003500b299074103a03001c1c1c80140021806440c5032504405181c00f121541c07992042c40303607400c00c400c442402c0d00e650041781a42c000c0c00511418025042d003100e000c0321075500940044400d062030309200400d103007100c1001c6250384400201c2d50000c030f009010142c1e5004182406040c50b14180d5040289101303d07092640314000114400c2100291030390f030004a9450681000702400507445d0655003d41d44400c006403483c0f411003208a2460005202901c41c08503041040441c0c001d94006004000200728001c0180d0303402ca010a1842d122010141150325141022a950b00818a16844480c040d009032801d03c22440050445200010020710034100507010445950017000b04031a04400c0041c400d001804054028507884046a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 595800953 1250 595799703 595799713
    0x2011214060d150204120b060a031a06040207060f050f0a020301050105040b03060a2c01081b0d0f02090c0d150509131106030708160207051005070f0c0b04170109080a0c05 75
    0x2100c03c0c1c50032613001c0d0380907030a40803150950b1420010700742481603002c00116964840c1a20f540c44580406404240808031000010b00044032941c4c1d42e41035440050300518200500e00c80180c5000007008180c0b0f1500103903030000d0014a29817142d00841e0b0503501c0680d2441d003003500c0d2003121041508054030301c5a00030321030100852800f6428404080c2101d10b44142c00003110800781c0d1005048040c0c0003001c083d0014079005003d20564140f040b103810050703d854641026506001705100c20200c1c000354000410428440680d04400103003d03643d0000004000440000c018481c203803610b4071506070019090400940002c402c0c030310b1900e05170f0207110300e10f040da05040006903040c0d000b10381c0700300802d807034805012040090707081031710809010740004d01c109400d11000032904156940c0364010070400065010401649a5090303000d07a03400446000900c1e100c003800c0e1115001805942000840d04c4c9039000082814040c1d4040103801c840300502e0410081421a04100305000c1a9400d100f1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 595802203 1250 595800953 595800983
    0xf050a0c120b152d0405010c0809010c05160f0509011202040b03030c03070f0b090d020703170409050103080703111513080f1602090711030d150b070302060402011214060d 75
    0x120400a00d0b007007101034400c1e041061081d51103003a80c50070913544202d810042c030060007680d0b049002c0a40d200e401180064a404500780100d8280045c0ca04c020300c5c90040b41b650304d12508001310b5080a07110300f0a0305682450722201400550710382445060301950080c56050090304160780320504090002c3c0960f803a00801c80c070841c0c516401064116942c4119071460400c0c00550300c805d582003c0d803034014258103484090020b650350214000a005280d9a04001c84c6a03441e40d0304440041880d84130900240d80e403820720b6000ca800030601680812000c0d00000090640401c5520850000c500741c1d120585611441c06034010001004031104c40d000c00007924000c05072009880d50b54280d80c014012040c4607c10302c00c2d04013002c1e0810060081804014040e40b20100c160307122418035980026000307500d01c0254403112055030250005032000103800f07082c5540815128415030003a210280300300424001081142c40c0d41c0780d200d44450301540803d5003860840725219419000d0407a0000c4101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 595803453 1250 595802203 595802239
    0xf071d130606031b061205010e060111030c121b120a0e0a0b030f090c01030e0c06251208070207050105190e210708011824020d0f050a0c120b 62
    0x40c00c0504058048954078041280950014480c185101c4058051215500d480480d0ba00884041e060710b050008103080c486000c20f041050b1180c98401008a403003804a2020034042c5a112100c2051403114203410703411a0076000447851001c0c4a80c10a0030b00c1e20002c42800c69103c807685080b15403243e4080400500c010000000d507016aa0315046644035042c4141900d14020060001a05050802c0c040000442c0003145a89200d0300c1a1501d40c6c0e10444414440c5440d001081108011044600d8230828003800d0000311851070000c5e241e6114075164045d040e070b581c40d00d03171013003d000801c108a03158411300d0b012110202c0b8001d90a010015070721000c0091008814040700e4000c2107100048034a64040400101c0c00034034120000b0021010381c110300e004081003941d005481d25090260b0110700e1031074600110007418404108540b41c880400e516170103400310420300040a8104000b04080d40c081d84254228003140c1e0700d0f10803805000780e51040160080f615543e500038084101400210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 595804703 1250 595803453 595803473
    0x30f070e09210c0c0a230406081509070905010b040303050d021b0c1c02060714100f0203060414103c1d0408030f13140f071d13060603 59
    0x7090303102d081e11510310000403490720303101c4601d040c030a42c9002d40c20002c0498210000d003001205600b07480c9042609000300c0c001d00610b600110341703841620344405070300c251564510f0140014000380c60380345a0329501d800980fa400e0281a4400c0d80403c020400a80280b0081c88290fa030761001600f00402d03600112803251019806260980100e0308908091900740d01001140314102d001884c070030015000703c2c0c0280030b0a0b50041c9034100d5030450842c000710401a44110080080040c0070f0059510305603c0a90810382c2d030f4600503820000e001020114202210340f2071180c1c400300242080c0307000802c10034000c11500180c00141100c2c601410001500700b0f0740c0020031140d101815061070443c0c5002ca039240c1c0f0002c02d400c209201e041c03000240c0c5d8001204e80080c1d8184004003942c8901c2c2003c606a003210340002c0040c148803e402d40d800c0004100c261141c050301c2c0945046956818081c2031385e075103140011406407566400034070840290446690094043c01c0001210341d2a643d81c000c0d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 595805953 1250 595804703 595804753
    0x70e1c021806030106060914062503111c02191e080301081209060409021c090f0201090816060309081308030c010c140d1e02030c040303030b030f070e09 67
    0x481c803800c00c4501d0a090152078010105441e051003568a05241c01000d10444c0350440e104200c0007400707000800038402410b152058501819050314014134001d05a00040b0a5816440c080d001c3c03650955040b441c50030a520184d80c0290403284041000285402560300040758002003103145900d5000307000c4190130200e0303c600304c8603a895050404070362600c00e501542560f400b00402002c1115201e079802e40c1c1c1111664007015882c2d02d42d000648403001941940c1042041c0703002405424418015801020507000b80c0322440600e40f1031026544136001c0d143c400d00e46141c0342e48100001c43c442c2d40001602e42c050000941481100a0092440085544842d115510102e1400310040003803042c0403592030702d800e020640d40801c55500c10b140c010510030545450f603807400c0c121804c02c034000b000c040f4541440215a24900b80396560480e0700103020030b1b40082d00e0982000c4840c10001000e00b0664410801480014030301040f03280d0701180281800b0050081c000c20ba1151a4015801c41c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 595807203 1250 595805953 595805989
    0xc0914060f2a070815090606030a120201020c031318060b1905070501020a030212010b041508060301090f03020d02100e1b01021c090302010e04151715011e0509070e1c02 74
    0x1004038100c5d468921030003030898002034009000b03000540d80c0020703140744100d43c00a000741400c681014141d00a00581c0069030346804002910610b42046481400c2030303c5c445001c04658100000c0500115212405001c501410411004040c0044e00c85001c0f444120751030107a1400c14103035260360030f81e00080c41d601d02003a004112407058800c1c41124a0142c0100f416407403e01d8542901c8040340542106044140002603002c6202c0da20290000b0100306d82001c41c104925503203140c000d5032034031030040010060043e09000c864480960103100e403400c1842000b060070580441c1c00b10540b010404502d41580716540e003005c1e42268482c4801100300646d02d9109049155000150807258002c42e0a0b20072803400c00c903500c6441c2c0c21710305402680c0c451900783d140440d4030940280340a04094003043c00031904000003034401040c443d1030000b0149540010f00e0560348000784003286106460035008200b6851800030f0354101803131025884041d13003481114040d00c0d40c001c07070803c1e0362a0149400c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 595808453 1250 595807203 595807213
    0x60f1c0218011403061309050a030c0b0a0e0705040f0b0d0c0e0106110604030c050304180b041a0a180b0a0b0a0215062209060c0914060f2a0708 63
    0xa64840007034450502000c3c00e00c0b100b514100d01284040c0d00c03000307055505c42d51842e4080c041d0702d0b41c280d120368001588401101e24822250801915041100904450309290340c00060b44c01c02e01030003010590018003004044c180d0810040001501280785203258803a07a07050701200320340d82d8000e40071219004030991441141003012603154508141c20160a2080305a0703d40c0d0345c08c40c0010b6155100d601450030382c030140e01b20300c0e004c6c0c21440380b039104d200c0c038401c2e0303205042800e0800d070300990b0058411241084007403142d1010951401c4491401356015401030710030001a02035606040041403441000111001214001003a101071501b03c50005400420a4200d840e010000c07001c171641c000b80050b81c6d610b07104c40040c4116180c90780c5405680d0111348900010210342d04940c020700d50040060050000d025001851810036214280b9507500c0303134103c00400e00f06407044600741d91400850034500340c040c01081140078507401140b080c01515030010320481c2000d0200310060105200608 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 595809703 1250 595808453 595808467
    0x16120801050603040218040c0e160905030703020d12020c1c02040b0d021e010509030d032715021c1b0315081b0a0905040308041718060f1c02 62
    0x40414205030401ca0003041e0400612004d03030b0310310078280040510a03220304180d5686142800a01c00142d0180e6110b0403070100b07108203040c803024100104c51859854046940e80ca004041c2d882c40d8600c006900f1101082100012a407030100701a0400da880c01102d014410110101c0c10010074440e9100d00f00d01548010001c500d0725000b50301c10b07a00221120008003543d0340008001240ae040300c0000f2100c0e002005a543e4001d4007664040301c0014140c3e80b0641e50004060040c2060b80d5030b00302a1001c155841341c040c80e0400203010070300e8100c2180005502012000e400941c06145d20300d1000d06c00d001c00440720743c058007509850000c15002c200d55000c600c2d034090140c0b142030340e0740e0448403080d010a02100d0070008440d2464036601c184d203404444010301181d100700d51030300701e08500703410a010401071640112035107019a02c5200710140302e042c10303d290301c1d01c0d02600510000c0d20003441d058441c01c0c6060009030103014248441c0d945405c5440500b505c810510b07a04448545401150032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 595810953 1250 595809703 595809707
    0x618080408010519020c100507031104080d020708030f12040807061e0c020106051e01110d08040b06040501080a1101090b180f04020c37030513050102011e020706021612 74
    0x4d448600d5040c4030030740c1044400d00340b15440c0c400088000304ca056540d00050365040c820b401075030060040c40b500503039581d1200c1c100b5071608100f15031803025100301d44000400c801c001045821800c14100214100304030070f0610351039524040d0054411403424000c15021803903d1042200094031a081805243d94540503441580c49034450082964540501008180c0342c0d0304901070580e000324a144048811900181c40d03c3d144240040078a00c61072a41c01900d5412880301c600850240c848681140d68050820040e608240120707006a044034a00c0e0780010885043d8004500b0141406050f86840311000d110a40140001940d6407070358400c1004a420010400e19440da8160303010b51400c1c00504840c1d684800c204050740701821002008a19070507032082d180321000404211590044d070f24180240240c01089610f0000210410000b4042d03005101e4040700c41143c1030048404c00880103283c1c001c1d00103070816101039400b0010a05080c094204005400d48107800900c0c001c1c841a0b40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 595812203 1250 595810953 595810981
    0x403060e07050915193807050a06052214010e1014010503150c0a030605030d2105042a1d070f050f0906070609060c030b121906180804080105 62
    0x14082c0d410030792801c1c451449100e003200500743d0045003c0328180749104114491b0b13070911181502000001c19408200900030961401c9070340920303004c0c4104d8540b401c1c000b0701e120348101c601e1007007440c904500000400c419891030448600400014810445042d55810b01c012804147c68841c2d81c0d0010340780280040e00314502500c015002000d00c800c1c128151003c94402901d1680b0b150004244030201314800c1d0800e102a003000b41c2a18a000c00c0040c020344641c00446809842280c491550568a00240f003954170941d005160b001002c00780419900182c00c145841f40d44064485101050000321110301d000980c0d606c03100c01c40700f442e0000700108540008007101081020401604a00d4181d0109940c42031078101c0e42c543c0d41c5c0102c0d180c050010000700340c00501d200d0810781800d40c3d031601540444090601500c00e41c6d0b88904050780306454200c0032281400b181c0d001218800072400940c41003025100201e40c01001e80c0300c41c0c5490440b42c016503c415803903911902009441306c04204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 595813453 1250 595812203 595812229
    0x1030c090e010e0304030f020604350307030903080a0302071e020102011113031209170601140f15031e0a0506031903050a03050703150305031b0d050403060e07050915 73
    0x8020804038041c07000290302e170b1007184000740c2000590b400202c1556202d80480e0001d2206001222880d51140040c100100c0c80300600311120010460f060000c00e0040b04071140168195101c2c80d130035080d039445401ea50010301d10381c010947d0902510000890b0142c0d4020300a10324204001d840cac5107031000a00f907640d401803000300760a042c4207a408005a082518040d41e038041c1115020080700b0200b21003021442d03120b21b01e1088890f942d002c1540c0d010582c613041c0c0d14a4129910301c20385010500002c24481910590048101d01000d680c0a221a01440c3c105035443c1c00b182c2414003d001e2810010350617a07200100507601d41c10f0011a07d010403d0341e00503030a803242a00d01c082103890160490141e2030b6843c3c02d2540b200700260300e89209a020038401c2c1501d804210301e1303984070b0420903030301e410401914242c00384106c00d031009010b0010b080e1203203030a6565041d25250135030340c03a00d0260040704410074140c42480000f0410ba9101140d95214503000c1a0b010201115002004000c5690316 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 595814703 1250 595813453 595813481
    0x60f06060c0c1a1c09031106010602070605071505041a0a05060607060906062313110301050d1704091a0916030b0f060a0507050d034101030c09 63
    0x1820103000142840000d40880f4944152424036200940844445205442d2968401c800c00c840c80042c1d41425446422898000c1d990320801e0007d0005441d6521001c0c0509170159000740400c0040c148208000c0c14003034400c0800714a410724030b2155400b5601309640807950041c204103882d8202c25207140442d808a08400d00f8001800c20700c01040c15446904005001c0c15102e0b0305940505c0210b402030700003041d03841070a0119070b01d00300801da03210708000f0303140344100c0e6040c1350300e00841c03000d018448401c082c0180c15803a61b480c040400078814040c1800700d80c1004444c01d100740300702c01400608004c02540801141d0281082e40180460a00380425481034400c0d00900000720410400c3c111180d403242000100e40e4041c1c00044c4800c003616000325401500010b1440005602030060300c0000d105104903854110724843c1901030754010b812080804c0080c01c1d50f8425215074014030400d1b401595240e24038104009036400001c2026003003036400c0303031441e00c040003c1240c5204130b006c01d86c101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 595815953 1250 595814703 595814717
    0x80a050318010603030e06070f0b0103030206061329031c0503041e0f0201030f0f050a020a0207050904081e09030109110307060903020d12021e0706031803020303040308180307060f0606 81
    0x1645d0241c40341024107041401054049600010013001002014031150004030b0b101166079030345402580c90301c0440b031250040c00300140d04500c8030494001e021155000d81c001101c121400c0c2d000d503402091014a483d890b12405e00c900201c494032040e108240400c0c2c1c1c1c1d40703a1345c83c81d2074141381d07074100392448a840f182c26403040a4404508101c1d100680183d091a0104210b4002040c040c041d010402081021a01d042d041c800114416801454203107015020350319403564a03400c1104680c0105c6006d40442e00800024005480c0700c2c1c3c0c505484101c82c170301e8a04085145012908441c40c03804110b80f00b40035002c0b4440c06160800200d0000c2c440b620b0300482d100e05503404258486407091006005446412100c3d42c0980280503141c04a024101054000030300380d003403e641c561040c0310300e00202c3d1a2140400c82e41c104080940c2006400d900210f01e1070b00d4a5038110786042c0300605002c076640800d842000ca0b010240b00414035180514004650702c0d0306000040e003100c80d00c0d03200400344646 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 595817203 1250 595815953 595815959
    0x3090b0c0f030a09030306050616023f03070b1503010f0b100507080403050105040b150103050114090403110d05271c05030f030c04090513022b080a0503180106 70
    0x7000003182e5000c1c41c0401c0c04140c0700313080e10701a03001e030000b60000e90f8846e0011903032080302031850070300072240360003111812803404108188041030b4400c0103014518444c2d0280c49040812445d000c880004051401c0343c1c584045034603a41c0c583c120940e113030036040c410460313000800e2074240115450100d070024108030603035860b000908000600f02c0c0901c140030740070502205100d91107050300d00954014009201c07500d820f241c02d141c0050100c65120041d04c082401c00c8032540319100f00783c103036500015208500c036044403c00c41e02020080c0102c040105c100c400c80c001e92001d01c91001f6064443e241e068070b0700d00141c5000703213280f060903c218003001030242500c143d0307644810120031184d080a450646209a0900c04d0640c880c040b28800500d6000052149440810b4000c0080f1429148100501e44400f038880c00114030442e8041d600c0b51645131008801c1180141001302036048411051410302d4558410415400c5000c200307010030b401204024001d041c409042031149000402000a141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 595818453 1250 595817203 595817227
    0x70f06021c0b011d2704021008010506030a020f130b031614030c03100b0f040e0606090f100504030510020909060604060c060c26240d02040c05091003090b0c 69
    0x82c4102c0400b02c8611031341403060741d51111018810100b41555030002d90b0650000e00003c1c00c3d01c1503600321f0280b50200c0110f20709602c501c5842d8140d80005001d02d06d03584801c5ca006c80a9003210980c42064032040040d0400d64080d10902c80c0141a10001c2d640c60b49012483c0d401c801c4222800c1c101407110360081c0c000320441c45411603601c450a07004250307c80e1901d490400703a600094000680340315001440c5803003400400003400448040810070781565071180280503441c0501c00106e600415080c03039402c13103881e0100b1031400010851405601b001c0c0c0d00c0d1102d9240c00d40d1501c080040540c00a04101c0a06264002030703441102511601c0c601490315100501000310754034003030001c50780d8001c00c03001c072481b8290440c1c0082d82d03650f1021002d4000d0042d044421015202c078025070b8001d00903981f80b44140c40401114410041c050f41150a017602448064805040f01e40308000c02000501d55943d501102540e906203155400100f10050303181c08800d01c600039111820a50050002c910410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 595819703 1250 595818453 595818467
    0xb1804060b180f04060e0717070929030c1503040203010c03020406020d051809071206060906090306200304140d0e091602070510030f0605060903060714070f06021c0b01 74
    0x440b040d80f124040d0b03254201540104801035101c102d50041c3c00f00010003000c0102d0900b00c01d954070081d107095655500c5554102e60048240300d08003454818840c18036110b03c0c0c10070401d080060165011200860009010700c84245112a0842404030074401941000d2040340001a51403d00710f24241c00e200010755035034800220b9104008002500f2404010441200c0c514000302a040e41214100b005028180310b90850200340401d242c00350019209110346c40d00b8088035001d4480c002041d0550701c8040243ca603112102503180a259420940910288001c511560088140c42c0750200c1d03212405081c503006a02e56420030000032400d10241e940c1c81d6a064016001d006452450424030100760300b030130855070140307500840e81c81468190b00d425070003a91000014400420083d41c032031080201d030f8000c6500d026003580c171410028040b01c0c02102044240b10010240a08044032a9104020500c03001e908869458010811003da000d090399505501c90000000340641406200020024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 595820953 1250 595819703 595819711
    0x604030e09130807110423010b0a05040f1707080106061707030902030d02010c020c011107140d0507030309050109060e13051803042d030519060b1804060b18 69
    0x24403001001c9401644180c60b11410395a00c9203006443d03224030300701008982c0700b03845070074042c60400660105401c8a001c03840c0103201d800d01107040030390810041e1452034122142600600c54108008148444140030a20040c4007011039078030718402c1c000056040c2800b80c0d02102d011f0381019400c0c080ca50300b040348425100c0c89004100c0565555400c2200070341000320003c0d4150181042039240f0503419080b2004550090b021a07031780a1b9a41c00443e07082003e40003004554110181c01d00c4114000b40e00016150380040061240080c0340d100d007810b000f41507108602082c21481c2c01c001e00d5822030002d5008101c1428220040303a00c000101740001911111308a02581d640d0004191003200f2120300c612950038412651500e40341c0c80c1e00034800500800e00006048020f400c0800c1c2c103c040000400c0d260f101014000d8044088003998000101302c3c07007160050b8841d150012243c80d10708078a0b580250760100e580542c00c05041090844440c5500c640c011400c0824201c1510700c4100b100b504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 595822203 1250 595820953 595820959
    0x160f060c020a030b25090501050306120705101e030903170604060f0b1309020705070e150402030702030d05010b1801120204080703080703031107020a0b091f020708010e0604030e 78
    0x311000c0c0300040d400300d100d8000800015a075070134000c150082d0900007010790a4a2413110701080260001d54100d5a28424240081c008000180d9981450f8100b1641e00440404480d074003500c03200040c40712101c0d400800005030180d82040c4a031040e0401c1d02c481e5404505081040711300b251402009580c4000d100200c00c100203000c1507a540f5140c0c450740003010446010340f0110303201c2200c02a55030081150482c8c00201d40c0c0042003000f82442151881c5034000c0082c07204a1903c1c61400580344010550340c101e90b0244201c882646403030000b5440381a035a1302455036003604103d40c0f0201d50060300302e81304415040c8400f120700440300042012120090820032500c3c00c030305c0800b4019100e15005002c0b1400307280d070000100020840940407040c40f84e203042c043c11203160b040c00c07140c3c054111301a60000d03d680c410044030b10fa0030010301030014080e141030b144400060180642c0d41842041000691150344104446103080c4980b54000c0015405003000b400c2c1500d004005a0044e414584 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 595823453 1250 595822203 595822217
    0xd02091333033f0203070c0503060c04050d050a0203010c121b2c03011a18060f12010b120f120708040504180b0f180d1707020c040e0c03160f06 63
    0x22a00f454600b00100840c542c20b08030035111080340c020f48076000040111010071241402207058a0701050503842801450305941c03e29150a08121100c0c550303c3c0140e407280100c04075280503803020302646100e00015120309440c00c401c2e05c4450100e48601884141c08009050070306d89090384020000545001c401007040f81420718400b040c2038504000f0110341c13640c0303003480d01b1040b4807006014460b01a070446044655840ca551041d001080c11600d0720303400b140e600c0c040c2176545420411800d5481c01c180c000101c1042c03480105181e40c541e400a1115a0b11008030240180c1c41004000d0000d4100c840e00c1c0d0070800256141c015602444c0251482162260500180c85140c0000881030070b402c103641104c5e500f4200704680e0301c02e17000d589000d000c00d6941010034a2510018402d00c3e11021076548410041005410801e416000740c014400c5009410703404100390f845010f95a00c1c5403000d0090701485409400301032610503100302481004107040b40401100d114030041e0000c0340e269007002e0f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 595824703 1250 595823453 595823513
    0x61a04020712111e0a03030501121101080403030f150e070219020d240b01030c030b060d05060103110a030506040b04050f07320a020106080105010b0d0209133303 71
    0x20f0070500e131070030030509260f51022054041c13580050001c5419000c1e4038100500d980703c0e404800714031f07602040548101d2020184c0070072548540304180d881802480e0010320f0706d040f41c1140b015209000b03403803209100021003e1040000c0d004189803c10654001099196920b100b80c00c1c40d00115400030f40b140801c008030205100b5200d1001c84540080300340c0b20f140c40e03803400c4104c0080054200082c0000d00c2e1418043c400383c000d00c14404e40c0c010003008030b82811a2118004c0103030070b00811640c10142c43c1d5802c1c1c8040032410018088900e085c0d24007103010718284003408201c1c1c0c2d411105038811801c0000384100c0b81d1062081e160072558a1601210340724499160302c6d41003c824201e114182c2c4e084621950440390600500f92000d41a8024030400d03503a011541d00781c0ea0f003800b50301d0030381a003003220800e114060ba004011401026002c45052101c080c45c090480f00341000c0a840701c90802d2541500c0f801d11031354802006040300c03407000101c1c195103030a100c0c2c000f01d10a407111410704d041c1e50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 595825953 1250 595824703 595824737
    0x91401091a070f0c1508010e0c030a060315020d050f103012080603010501030b0c09010e09010b03100e0915041401052e05030307060c050f0403061a04020712 69
    0x2c0368815001615118200e070189400c0c8075895030762094078500d070b00c240d0880000380c4c40358003124102c0b9a14100e105032526004824045131740041d0902da0035541d10000040003c0001800101e40e1600300d000589032116000d00800340c1d04028074402401928604011002c07410207080300a4551200c0c03090311264030520b01c05400c8000c0017205200058106501040041e404030b02c40404032242c0e41d10758281c0b214030a150070307502e0a010050144051900240704c0c103a4510141c8400c10341450202007a0318018086401c018080c3c00a402c5040d000041084002d015582c000c01002c170940441ca003458000111516107d00e4443d50085207860404201809480d00340348803c00d51b01d00c020002c03818010103051501d104035021181c045d007291808500f800c13103c0c0468040f1940a000b81d03241c425180c2d600c10041090310040000d00c0400c0c40a0203240c0d10b4400034101541c8943d400080c031080b82c1c1c1d40e40c02c3e030140705840b80c1c0c480c9004004500000d030000d4035207010300402c1d0428007240d00105502c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 595827203 1250 595825953 595825957
    0x1e080a06080712110a170606211b0d0b010e01050301110f0f0f0706021911031201031205130906092007110a09090605060f0f090412022803091401091a 66
    0x3440c0d1040f0714601c46c503d400301c0d8550103644100c0c0c02d581e484018001c04c00001d2400c2c400301c0c54540003480400d028080c091469280c4213002480940b4110040d40c604182540c20f030080341c11454032030014407044c1800d103d1400c4541c0e0303c0c2099810501c00c2d14524016101303c2c008184107400115440301d44c0721025060300d20440c2d00c038200390341b181141d4011120040501140e800000c07600d4250503c1c858010040f01c600d040544080303c8940c3c2140c60b407891400d04c2200d51020410204001000340400c001c92101074080c91101040e0340d071030080d800056079824020710f110a40282e4400750250000c20445054550002c0001d000b00506000101c0d150140d030300c00707044c0da0309128217070302003210b182d00481c40f44008550a1201c6605d400c280080c00032143c402c03d810500e0000030802040902d11034031a02c1080384100c0e4807800c1e42c0b482d0400b400541007401c4803519031003a104020140c0120003c0702a0580426091035150400002400100c917485446411440e01507440c883d0540041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 595828453 1250 595827203 595827209
    0xc100e2101050609060103180609230a030905010801061b02030a140c0a090926041e05010809010b060409020a180e04051005040503030f06011e080a06080712110a 71
    0x4140c509400d09141414064141290721a100742d14040c0000c1d129806031051100d06129904c40d41a010980c2d900d60300103200865041d20041c003612241c04e151940a125480b4005903c3c014151103100c03490050030385802604581e05101381540103000303480c1d004510b900c2405171010903c1140e65580046401d029500102921114098181c41ea0604000540e440d00751030a841c040c00959549a6800c11207070051401000d26a4810202c1c01030101d40d0300030060102510200b614082d92040b00d448240117000d107801940300c240c0c1007040590703009400141e0043c3c40303400a102680c0300000041042c031490143c40c1109501042e500341c600d200c1d101c5001240030318250000466100c0e41c800814810489044038107204841c4641d1100046000e081d008030740c840001d60650719401070b4406131070303001081070b0304222a0109646050845054486522130070b40c40c0c001503820658031440540310144c0002d020759200c4507080050081c90541c0104843d00100703030303800040e04400001e000031441c2d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 595829703 1250 595828453 595828489
    0x1c020604030f18061e02070b0f090a0e01140f12070303050a12050f220c05060904182f03030f070c080708010c1e122a020309030105090c100e 62
    0x20000c00c03055008405080d150200303098941e1181c1c2c0041049940d841180070300e0b040d0520a100d007200e0309c84200080c048002c001842304d58013686800200e108a80241d0013040804e048000b5252241405509003060101c01e841e04420b4010b0a0452507076000d062200070104000060f1150000e845510300c045498101e0030280310900744903007400320003c010b44080c409040343e070b54556400700d0f082d426030701d446a10540c01e80721145450104245034211448071600151511803115034460078054039600203215040c0042d00c420754880004951b90030301ca06803048000316058421030b80d40002a15202d04c010040170350740e2106490011f80684082c2e22140c5688075403003020500c11010342008070034100316503418054440810081111111503003c040c08529248244000d00900d5000440c020602103029000d0b540c004902d03003400070b440f020980041e0404640c812032450f0038055290001441c2d4010304041c1510700000b200200e690303d540e018808805418000d64a03207141c100c50f240a16 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 595830953 1250 595829703 595829747
    0x303040905041a041505100509040f0314090d140c030607050a140a0c060b03070308210a020408033f01170105041707020604090e0f1c020604030f 64
    0x9050480040c05007500e048510344000701c0c81d943c030074000c0d5010a1045030481c0306038100d010b440040400a1002034180034200b0101c0001090907115103585038010f0b03108070384503014814141801000512542803110343d6000410031114243d542c075403807a4043c0e0f0044001500480c0701c1081d545003d5030030714245d41601851042003401a0890060040765890f52075040714007281e005c0f900c1080c4036150480340880c0300483d80c1004642181d000d2030a42c0006001c6800b03541c0c81c2d840d4176100360001e550751801a000f10890440450318500710a801503008803044d8100f40c06c1c210f0b01030f1a4041c017514007072a449244403c60441c05140141c070125002407000e40380f40700c0080600e20808130240136200b0741d10f840003415200b00343c051045501c92500407011071000499584d01c81c480d075210b114160303070241090202080010b4141303c0c00d4804ac007410700610190000c107100e241403584041048500f082c140641000703c0342c01040e031540c040d5051501040060501a0985000103d242980d4400c0301c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 595832203 1250 595830953 595830959
    0xc3f06090309011103040e041e0605010b03060f03060108120c0732010e09011502010f1d0706021504080a050403060507020a02031c170901180510060605030c07020f0609030304 77
    0x4402451020302c282c0e1071001500c2c1c035009042c1c1d20310a034811068070015070400200495404503001c15000100c240019030100c00b51544030039200c080e0000f201d0403500005000c02c52409400358041c1d242c0c2500603192940c900349031907840700c0d5065091580120009010340c41c020003400a00050319070000c110003c9002c4100c0401064031741c3e404401c200c000c03262200015801418060760748032006200c0d9210380c2c00c1c140b11940711a544140e00f029517480d0783c040c4020750030034012110b82c1c0b4925a180d031080042040c3c030398500784a40e84a40155042400850705d1000314180b0a80e10075005840269a1082c1c030400b1a520300c038950014058601d01030038040401e6002ca441d40c00a4022402c503084104079020405100005414440c0880c110201d032181f0b40c40132000ccd265019810400005214500703142081c992009040e08584907000b0843c50312412410f072203010040c0540b45001400c5181544816115114005020340b2480003200410700c40d41e108421a2031005001c2c0c166070b191a030b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 595833453 1250 595832203 595832221
    0x91e0e0f060a050609100e0102031b0f071508010b090f0a090902100306060e0904020312030103080a030c05040f0b0c0703150b0114090105091e060a080106020c3f06 72
    0x441555503070b10502ea000c40000e075514113681a903080035001001c00301d050302c1300403094a200d4075800815043d40418089800d150110340090149003002501500454002d03141450034502c40350000b80c86154000c070340140c40e9a10108541c15a508100c015a4980100d400980a0f6000a1aa03948040361403130225066900d50070a15100384280d88014820784220400d070261400c5c3e0044100183c4002a035100a10f00714503169003145c00907065910701000c0e0403071040550700903001912000320025550704030513418442d0510b80a520b180c801c1c00c0c14140080b6011001e072030311841c10074000c0450b450561640a02c103050080d0f9011440c140300c00d0100d14088050460025040d0125665401c2d52203084042c00494a001c4c905a4801d41740c540090100040c25443d102842d024240c5e40c50314240703a880e5071004280c8203403552561141589072100091500082011581c04bd4a00c0c140e05641c05100340a1011454140a8013a6807a5480850f0003962814203402410501c548030138061310b80707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 595834703 1250 595833453 595833481
    0x5070602192f0613020402070f03080709140d080315040c0306050109060c0218072c041107030804080d0f14010905010b04030b0708070e0306150f040606091e0e 70
    0x55020b140b4940e841d8103006000c070788040d1022150b030550f0042800038000c0c00d03941183c00c101c5031000744010b0070198291616100c1c3d40c19000105c02107141e8005000a043d040000d40004140031100050340101c420b002c0f03042c02048100c0282204801f2003c2403464840c9000d540c8030b405c025008100c2d03113031402030040180020b0711032a0302098070008081005c0c2d1040c80390924031038025040e074002d004461400c0b40b041000404801c00c000310201510722850804604050500c4403612504000d0300c4c0b01e00700001c890104200184410b01002180002908240d5059101c0c3d048200f0355207544e10380c1c0000700074003402c5001e25042d510304a04007210340c00c1090668141d40d080c20040065a880750120354491180b400701402c100803d0000843e81846080400d07403100306490f03c080744062402c0403034030b4010181c450359250711101c090301049044c150b1000703038112411076060200c540f6042c009800003001e80100402050141f02c4804000014840680244039640c070b919682d180c8428140c16070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 595835953 1250 595834703 595834727
    0x11190806010f0509030c060a030e030304080c1905060f04020a1802070b07030e0a140c090109020c010c02030a050702120a170c0111040f1401030b0901090e0c06040608070507060219 79
    0xc6101121040e50b840d11640a4920030345001c1d0003820800580000c01125400c100d600f4800c250f01c922a60400f2401400a50700642c400e400e8552200005c80703002c2c1c2070140c0340070a100203044c100802804070f00c0004409400c1506200da000340d607112400800d05060b6180c112070340c1454103140d103040464880d4000c0103c20b0240020041075120340c0d500303c00740c440e85249003c41d40c0c40b07c121a800325202481c442132981241044804807415035010981c425802d82c00200c0703065002c118040300c41d400307000c0c445555203640302651819000c51006403041c01a2480680580d544003584960ae140420209081d141c01041130b1802c9420f000300d883e81c5612015020350b081d400d01c90001000d9440300c0030380302943d4900300940c98540c242440c1140b1a10780c0c01c220f60405895400d005800d0b200c004521340600301c824400f0440701290340c1184d103004a081522801800d08020820409900540494012100c0e04d040d81e6500d03c142403a80181c0201e8aa0980c1c5a5a05102c2010103800001038140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 595837203 1250 595835953 595835957
    0x6060c0302011407080c0f090d030302070302061501080a15090f09031b03020303150f0d030513141305090a05061005010f030c090b130b0301080109020f0a06050d1119080601 76
    0x80c030320440fa0701180e5500588862022910b0b1401140310803003c0405080743c048500c1441e81002a00c00010f54950b584e01c200b5070200e6030002d035210606d81c0c10b00005038083e0390b2a401c03500d00e0204c400020b0a12500601003586540d9a4100700e81a036200782d0031200802809505001c1e08082040c608028000f600049010800b0818403c10740d00d107500910700707010f0b007680207036095a9421050712041d0000c403851540c0300092600120081d6038103502c1e03140c0715002ea6955a285c20300428607141e040c401c0d400072910469100300448482d070f181c05105813440816540821a0f0f11040740b101c0c64a00d80407401000303070240344100501c1e0740103407040c1c0040b80c909907655500e41894030300603012101c10034140c17800180100b41c2401900000381c0180f4101b1000500440a503503944030640702604207030002401c50b5140c00000d01907152400d08841c025108032915140c051070580090030303500c25031440301c0e9425100c41c000040c01003000306454101e0442d40f5581e145480720800102a0001103a003140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 595838453 1250 595837203 595837211
    0x702030615041401151d03100606080105011107032d1103060601030221040c08070b040801110c060115050702090c030a240b2212030207150c030e1306060c030201 71
    0x600c0d0103d0681242c003224488035045014071805c550b654500c08000c208606000034480d1142c0701003080c02c0c00910003110000d0f50608003c0018641c4106034041810000d89112042e40600003141c008200e0758440540b0072840064150f020480e0901c1e03403203510b1220340c980804184145001d0f20043d000040341134401e6a500c140054089000358980540003079500c1d185030044098151000303070450301500000c490181d9840440c1d182496076080307050012404101085030319407d0182c2c83c07103001d184105c2800c1c90303180c5c040c2c0755660b00148500c640040c914403903524501d0207071007205c440c2500500361080b40e01d803403691000c0b141c1c016070b440200f80e490007a1210804060a000b4100001c40802c40c07420329152003041c04054000005201008900702c150401503a00201d030400242604e01307644112410505020741841d43c1c5500502d18090700e040d481422a50000e10740302c400b071b45414031a5a031151400401c212200c01c2050f0340c850391074514041001c6030080408136183d44294004c0c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 595839703 1250 595838453 595838471
    0x70f050106050103090b010b0912010507020a02030f21030a180b060117042303120a060512060106120e01020c07081b060c03030106080c070b040b0a0e1c03020f070203061504 76
    0x44c1280d108281c050003842c0c5200050084100c0b910091403e400010420340b000c6048140e000d085130740a44020307004d648481c2460f030840c107050203542c0103d00d40002920b1020075000c511a5030659002d00c0c1e581a9000000154030400c1c940d1084407002512050708410040c03900e0300da8001542664103902090460620254034101000c03482c1c89654042c81030004071401c000d0304400d921001444940c42d0005004005509805103041e9100350f80e074a0010546038a01024803c0074041030321020766a4109400610070f60350000c0c03913505103a800071000100040000c3c00c040c02405002514030f041e004a000029144d030b8006546d40401340d001c80715521220042c004c00081c0d01c1079115041c009e820a1004008181c06041c03507030340c81800240598a000b8041d43c40c0c03034080204407002c43c0c86000800a20100c550b641c8150f07404541c0740340042c10242c41400d500ca000000d101d001c64100358001481d1307030900f00c101d01640c0344694003404581d1582054010b040b0442c6000c02098040d030302d000b0f400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 595840953 1250 595839703 595839707
    0x5040311010207030f03020a0507140c09090d0f0e060d0519050106030b01080109050601110f0a11120a02090c190e030c0a05011b02041407020607030c0938070f0501060501 75
    0x3c030f00907076142d00c503500c207603503d40d2064010750840c020481c10b2100038083c1e031010034070740d110343c0010428803c05003100c1c0810702c040002400300944482c409500000d10a40420b402503041009000a410600d002100480c00a17a0074800c0e603049110040c2040c080c81000d8040c403070040d00c408070003203003031009a0b210801241280e100c450b10b0350000d003220004000c2d0050756840b86400c0b401c1031400340b402c48041c440103460310040030501c01896000e1204107090000d50100c842c48007500b11011100780c141d200c1565a1008a090003900c503900c21004114081c1003207049030084032038014101403452824401a00f044111001c441c042c1c090b6540010342894a59404030980f401610341c9006040300200c82508c45c0c201120032600b09070380d03002c8514580243c5900500c1180158000e000c10700c0c05a0009064030b001c0480d01c0306106500009100c00c3e0310745100c07040700305028039041c0340d111303422654100200c11800d000d40305042c0c0015400c0a2150380442121000c2c010f034000e0291075034444c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 595842203 1250 595840953 595840957
    0x61406120d231918051813021f020705090403230906030c0301051c05030a0e18012c07090302011101020904060b130e0f04111210050403110102 63
    0xc000c1500100e03501c40078140104030303250910442c0d48141000c00303525698403515034001500d000802c1c164003000d03240303a03500401401002280001d40f038280742c903140c08206c514001649464140585034001207a4600d8070074074255454000b0a03d013024500d440800340511710150240c0010300132034202041d6410152101030040c1d03407603520507401044030b6400400c1400100000c07104241d0030010861166909005140645182814595203514060030406c200e02030402011100918140d00e90100b4404002e80d4180706060920f154000c801c0300028142514031180c403048514070100100e040d906e0002400700c1c2d00494000d903522440150000708614000b2901d5500042241c0d1052005501c1142e000000c410020005801c2400c071000140075544190040c9803525808902041d003c1007841143c1c00070312000403800b5203400c100203507545801c0c009101404032070b80803200c10195241c1066a501000c4651b05491004040044946c05003200351000c0d00011085007880d0107144040c82 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 595843453 1250 595842203 595842229
    0x4090228090e1c090b03010b030708091504110105041205010204090e030415201c180605032e030f0c060f0503072001151e050a0306050603010b0d061406 67
    0x8000d1100f50359004280240032100d40760410042031000910b200d404030146001c0c0c044161880d859107800304000380035020052045c48a075000d004082080c3c0340351080181c01c1908061409000818640142e850303200d558000883d40240807814403c0c004103602401c01d0312100201840596802c0c3d0000340e5900546c0107207400b0303e82001c005580580070b8201c54005c07010440030b4000307400507505040c0c180984407401c0c800c428070418501e418150f2200507103e000403601000584c95061100c020010b02008060400500c1100065407100300013102600b1035a240e0694048078a841e443d08218481c400c203c121102e03c042da03c042a02e42c002c02e403000103142c3d11380d42d076810b41d955050100c5607000280b81039a1102c080101c5003081034805e0240c5c0007a024034028080420345060090038040300c080400c808085002c11041c02a40c0d00c501c40c1c201103940105001c1465151b800003c0d00401966211650014014001404000b100e0300034001c0219000b82022155840006000300520702070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 595844703 1250 595843453 595843481
    0x180105031002040f0608040627050c01022a0303040807030302150c0f0f18091f08030c0601052106040c171b04020a03090506090114012106020304020409022809 70
    0xc1042c01410700c9286c0f01c0d40e019011b88808162520242222360400308034000140c04040c040850f2404c0c13007002c008900e0030300006c0c802020780034420042d40d05110541c1d034013108100e5180c0386d0074a40d50390410641e0082d01040d02035421041e41da140107503a84219180b4410404003070000a16502c6076502500c04690307400e0820361800c400c5510002c43e65100300803440641d60200103841c0103032609189284141c940d203001c69030102c120004c019155007a54002040c2d940200035230480440e0118215044030743c15990203501400c40c103044e913260040582221194800c1070300300420b01007404685012078000284100c9114800840191141500310f50344849110303d5103a00700b1400c0c0342e801446612035515001800298607551281000e80031744120125a455003007454802c803052011500516030511003002003c907401030040f040390380050107800390794080300103829074665802c1840c15030b41c010415001c880c03102034040212a01d0030721501c41403c1d40c079804100d9440a2064001c608020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 595845953 1250 595844703 595844729
    0x60f0a150312031d060106030b092505040b0a0c0303060527130c080c010305130b0109090c080d0906020105070e0604030b1b0c03090306161709010b18010503100204 72
    0x541c03109507100d81503418030410503a640748503441e0131090150140643c0ca546026040c0c951401c1e0300103003a44d0340351451510421400d014031004000340001100d6041c506002040d44115003081a00c1c1801a40c1c80710350a5540002c07100e41007a4070821500390035110351070030002c56031a6000e00055540003100d010b1201c4210a91507518101180c50f0f6034010340e80c001032540201c050f603e20042d10030703d40c40911180c0c0300c00c00300202d0f580c0501855900400035074291222500715140d0074041c540602c1541616941c031400350050001c02460310016010040460f018001241401400c1c0b1039140310f80340065190001040c95944580514849460000c3c0060300345411500d0355100c946000e00080e02403001007103a020446882800341403409100d001464a4a0451050500f031071001043c034100f243c10048600e0445070414242242c0840c51a0020020380c0c0d00340f40d05005041d10140281d000b0140394001025140c00c89645050318400d07800d4901c080302488411f0107074019801943c01440034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 595847203 1250 595845953 595845959
    0xb0a06081e0408040f06090509090109020a060e010909050103050a051c02030403170d110316090302091609030803100609210b220c0303030c11030915130602060f0a15 73
    0x40307045203641040c0035402580c6400e41d9003016040080107540300c0030100d0401d0380308020714502040c18030b0303110b800e4038024404c408a542c0060003c80030b500820b02880301401c40003d090344030f805c954000c1d0110310010840b40d61603041c16039484040c41400c07121440394404407003554160702c034111410b2129800850900d400c0d82c0d1800100030340e41007552011001440b01005088590042050206c4044031459883c240390a0450780100420003810520200c05d00c10401a01ca0080d81036000252035a0114500d0010324202c8a0300310036071014011400c04814824400d040c0074101040f5860764840e0640696125040344809864050030441e260310f4010b490081505400740c81d44c40700401201450040002d8008190b1041503034082d20502e103840b4040c010141c26124008042215003890214245c0b070300300c3c00c3e41d80e03ca0041c0c00da00562404152001e011040c00c1074441465520140c0c2c06174546811000350f0703420040300c0301b43d000505a00418405c400314800d038551f40b025203003220000e41c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 595848453 1250 595847203 595847251
    0x160609120302010e1005070210050c07060207020301020c100c021e0a0303050702101a1503040f060f06050603090c03061320011e08040201090603061206090f080408010b0a0608 77
    0x1034a004107030155521103840307222224060050441d502c000c00700c00684c40c00c1810f4000c2c905a9030795000e4100f01d10341001d100c07024204600b07840d40700754410805643c1d0010b41c03000c240039001d03e4040341414480c2420842c01d813841a0080740b5811000c2d0f00305c85a41c51a0403c02c4100d035040c0032036481c6130f0410510803011034401e8202c16840401401106c1480340103410f40c004895903808010505804440707644d045160032610405c00200c0b803242c860a500701a220010024803044c0000c0c0b40c0c90341d4a518218211558020100070540106141d4903840c042241d542c4544610790b04034400d024590005006400031340488042642000900300f1015141440204403504880000c0c18004003070a0289080c0b00300e510308003203860070f80d01d02505080078400504588030582000c4141820300500b8400e11340165144804a5009840460401c84606220710141c0001c05c0203084040b001501060b0b0b198150402c0c4c0c0602ca060707440001c05540d5000c112982442610328140021038250300a44040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 595849703 1250 595848453 595848479
    0xd02090408070819050309070b0327071805101d07030b01090f0602030d06360b06070b0103030906080705030f040c0803030a0b01021207170f13090e160609 68
    0x184107240d070324586660f0200e10b000c04110354144800085c3c0c008100a01400c06200000040014002031800c5052822520101c81e11244020360156140255040c800600704502402065140e0341d52104140440112000c1c000c1102e283c02d00000c200c0000030b400b5034001c131190071001d40e034038800740c107458092027100600841e00d28903041188500c00800c07684000381c04c9800801c080c5e00119070700c0507041c0006054600a0b44620001c0385075281c0341401a442c440710488111380800c0082040f26410303040300c000d120700180160005004244001004420b0f0880340c143e034001d0b1207038004951f81c3c00b0200c0303103002c1c02c9540000044040c00818400d500e82d49040740c10a04c03c0e0f4500c1d0740c0e15103840010b4030b03642041707400300c21030340c0c4801c2000c0c1d80e96010300c0f01500e4261004911803802a40e500e41c80b41c540300303c40b1003070344480d03000030305500d01d03d0300301c0c150f0b880d919034689036180055540003185d001d809062070a232150300500d006040014424504481202d41c42d071518407025140c0032062000d9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 595850953 1250 595849703 595849717
    0x3050d02070803070c02030d08070219050f0a0305042108070f0f02030a060b0a05032103130501090312060506030610050a051b0a11010f120914030d05150d02090408 72
    0x180c0c080c80800005030500d00910b00c10f0030981d40700802d074001d1b801014540000980f031201403101d80760510661550104110801001207000404407000903e011403800d260650140d20340d0140c15080c004060740f000040c41140c000710440c0f4075500078142c01e031050b801414402060303c07004016403c001008101c05c255841d01802503500d05e0a6075070003023800c0c202e0302c800465005980740e500c10440e1900c11400380c007030b05050300201210010300344440d051000010050030a50301c0400003c12841e1075010404806034083c0091001d0001c81c98054540c0003042e1841d10030740e082c8000882c1d2401c0c00300c1234921840f0000c04c080e080d40e00b591002d840c5940a640d0300c0c82006010448869298140c8822030003c05560004100009130350512520050750300301040c0c100103181846400780b6500120400110130078901c0050300c02801c0c40e001d10090000c445200f96800b01160030124034009600242c030401410101c0b0044141c51001c0000d0495010310081d845400507000c5030129041c08060040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 595852203 1250 595850953 595850977
    0x5010f0524090d0c0b032e1d090109140709050a020901050a0c05031303080d0c030e06012c0a02091f022808131806120809030a0803010803130f060207030305 69
    0x11a5111440000e155104480c0d02038410750304998130550049001c110f91740c20782401d02e0187c2d801d080294031500c105c0365120081140142e035000c2a8125001e40c003541240758044c940250450004980390f4481002d8410240360520f014000b9041c407809000b2144101030503901d0034642028500103850800401c001503690307100078084030701c00132405105a406540580d0701e080e25114802139204c01e68942d0707000c2e00c0c205402e103007c0a0242c5000030304c0701e040d101c41a5480040d0420142a840382d081199621900c1103942800d00070803007015801841040c07c242d481d400002d03213a03080212062240c100d00001a0701a07082c040000c1e00f07000d108000c0c61030030b46180d861203103551170f83c18464102640d84100c400514004002d030f406810200c0e00303058441390003072007451700d04840254407031000704000d00710a2000030109002d9070240f21009826900c468a66181e584540525a481c4c04c190480303540b07100da24102242e41484600504119280b40c1e006080242c219030741241c0f01c0d00010f9074030007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 595853453 1250 595852203 595852223
    0x14040605060d02062b022703010b010c15021224121b0a0b07060e060a06080a150e060108010e300a050705150a1a010e12070905010f0524090d 62
    0x1030901040c0004c0800556154100e422160001c0b8172907e0704150403100380c03090303142c1850450641d8102281c08681c5d904988500d420300885000600a4840c228a1035001100c1c14100501282b42030300000000d2424030342c03881d500d280b22003804150010004400385070b42c810058184010612001040304000280c00e0800995540c4015601038008802c03c560075500c03403d012245000401003284d103c050b403141070150350724000d29140c48020180340508041e80c064582c0d038080300d554010a05007840708044580541e911400d01e8001d00744010000c08a025121084e04208101400710392102800740c50f4040c0c5840898003aa01d071783c4040116010300a090003400c2c04504140441d84c040401441000c6040c50301e01680c0c000c44a295161107405501e4000b18006a607100c5030f0401d0b400e10a1f201e080c05018440d0079103103030509541c041008141050004600031030440010400c54505a4480a034912888000c008849008a041c80303482014089540c0724603040c002142600d006500c0a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 595854703 1250 595853453 595853527
    0xa0b0402041508120304030206070221091c0b0921040504090203071203120c030c17040c090c020a0b060102071d04020402040b042601050910021c14040605060d0206 72
    0x6410400e80825130007200c00040300300414983c0500800b0340c050002d1002e40b40400c3d40300e4041071b40c820f00140003520208081064045511b9101641f66194500c1914803c1e40741146402e08000b502100d589049014079091155201040c00c090801c2020000550f4203007801d20043c04001c0040410a990521540500066480f01c10105002041c001c0d92111414004084807906591000c50103400b014a402c0e4003081040d40803801134810748203a00101c0164807141400c05940b0038980200030744c1842d001c61042e140c0c4d00082d0803102d131440f41f80586d15582d91000166180d01d1984148600201086505810030100d1a0b5950384248020001810182c46011220183d08039800005e21001d03d040c05034208500e95050b001014541402401a4a8446011f5443e0141100c4103d01c0300d40118900c0c45403005400c4440340340029420420998a8113807a48503205810340b02900c00e5890305c0c01040c0f50b418110005540d658015050344c0c80d0088001e8800c4894079505410040d02271850421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 595855953 1250 595854703 595854719
    0xb0a0507170909041b05010807211512020f0f090f13060c210c05090103111603170f01030b2d0c030105120102180f030a0b010603050411030a0b04020415 67
    0x115001e01c0c002c444d4000d1454100c108a101c01803175801c2a414402d00c80c0801110903403210034040c0e4161500502321000f0201c09a41010700380320003004030003c265400210300d151031303c0582c034183c074003c594940c0204010010300a8150a04600d90f4100c0c24440018801903031002d0361513041400b9551030f00c1c0701e4840d40c0700d41007100d5040541c0000030360003200a1145014801102c00240f4942c1001c104088a104002d0014803580b0b0701c0c1c0341451388868a0076103180c0746100f0707034910000200e60005e42c00e20030309d001000c60301101481000740300c060000c502009d08950400341601d0340a5243c50094544280c07400c0c804150001040041e4030054540307068401714024a406600c070507468075265410202008403000b00801910701c240e1050115001d0144400f120310150f041c00d40c0c84000500e07035a80881d0800507c414054082d0f030b0110000104560b16510152259000da14131381c100710420410951185c1a01c1c801030300c0600403070082005454681d2100510b011040c1100c000d9954506c10303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 595857203 1250 595855953 595855969
    0x9021c0e031e030f070302030906060108180a1119061409060405040e0105241e01050417030307030b010503011401110c03100902030607090b1e04180f060b0a05071709 73
    0x1c00c4030b030801105104840000f000070980100290509509602e0040306280c2c2c0c4200051025041010120128448070422081c00d90b0f80c2c0ca40009a82078181c80e030500140c015600c040d054080d42824070582d1031f01c4c400000840603a461a0386880b1001d42031000c18209401c403400307042d4031031020800003c02e962940b00c0d42c0d14071000c0c00b001083d1840c1c140c0c0713200240a01508000d101c00c10010994250790f0b01d01c038407207029030000c0301c44078000307008800101c50394081d40d0040c40b96032240c1007458002c02c000101071842010705580c01d2103041d50080044480c0d0100b0b205e074039102c0043c1505880c1c07542c059403c0c481c951803414225501e103144400028989180780907811655941ca1070300405504042c0030403580149242445004036140a0500341c180c40340b8030409003805801c502e41d1044071282d604950007040d5000200e5200c0c00054407200003054103008850007507150030b100207010385400c001e542c0b921029445040c05c201c804e407603002209520291900d200c40081000001039903c004e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 595858453 1250 595857203 595857247
    0x1060f0e0702250e2214210409090302101503171806070807020a0605030a0e07050f010c06060308040303051201060c0b0a090f02030703060509010609021c0e03 70
    0xa408100d03810020720107420002946014035024a03da40a030b80b10b07060054000b001c0321010031201d10b06a955031442c03a4a4600c50400ca11000a95800001400684905110403003151000c2c0c0700c10810130054120390783d0303ca640604450780700380720070840c801896000f403602ea8040e0054503c00e0300180607203000ca40000d0800510224442c4081c4141300b807001c00c0e0000c00300d819002616160a003904004042c11124507035101d490002001d008209040050701c2000e940074000101140c1c4448020302160401c490743d182481c90300e0500039090500290210442c0c401400c5040000480c9004507400c454024007510920785074000000020407d03401000298020754441c3d03103548840d0b40f0f85200c5241070703000c030042180c201940c00c0072555500700513070464004003001410038658542540340c840d1810020790b1502981c0000001e000321508158400c203c804001c01a054465400700201d001d12030310100c01d611020710450b41e003241513202c5004441c090040740d081c4604000c40d4070f10301403010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 595859703 1250 595858453 595858469
    0x70303031107140d091403030339070b06010c030e01080705120c09010f0801080d05030a110307020127150509160f060e090f0a0510121412030910050901060f 69
    0x101c1130b4265000200b60040c0c504200c0c5a220400ea0300700007607607030001a000851101700c1e03c0f00120505001091600b46004030340d800680507400b503283e10910781004000b6101c3d241c00100150956210300f0201d161b41d035040c0c0306c031440e6250300700045580ba04014204c00611000708002c1641e600152045840b17111030140069913010410001800d80f583d5403180b2041c06240d80c01400703a0f000c08180000b01400c1c0349009900da50f20503403041c0c003400b001c003000d5028801c0041840710190741904a04042807492a50780d085ca0302120124000440c0c0900141600313107070340c006468032031064102c241c010300e00f08211162188030a050310240c4480740c0c804440c04130202002c1007080c0c0c000c4802102010304581801042c90500741d00145004014065242c0300e0740c80c400a00d8501d980d840040c040d041c0f01e4a072000c400e07060b2916900950300c0c4016002c0c0c0b4410350070410f240d2849070b01101e1069090001510454003143c0010003d083c0191114001e55211400801d500c220f072074084c1d00418001e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 595860953 1250 595859703 595859713
    0x403030e032d07030f081302041404060614010e0f040e0f0d030c03050c0414190b1803010203060f010804060b0607080d0c0c0206092403040804052107030303110714 72
    0x141801c0620801110640c294242d003d01100000c2a04001e01c0f0143c0075040c02c29081d25628003e002e10b040b211500001c0d405460950b000507813401081d0a644070300e104403130420030380e070706c3d000000e03030396101000c940740003503034501540310b8030308005c101842002030240c40490480038117141e0038240080c1e0018262154030408e1480071255150241d100380480d94201002035042c40040d46072148601d004080060106a088110741d0305c03104520044442c1c6120f042980c42c0c0c45003c14055540f0200c824500303110240417041642c981842224025200240522620400b00e4015a103070000208181c1c0d409a03070b10b100d0032032500c680c0e00408940f845090040e5031900c00c021142e044925210f084400c000b210002d0b1401070702c82200b20303510303100c0448001070007443d03000308144106040900c0e000c0080d400700134842000841c0c406070040d614129a00c3c00c0c03a0750b620014011400d00300080c114181e0083d042003000c40d020341c0c090001c4100b00305032540790801c16100c44200361800d9000512517801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 595862203 1250 595860953 595860997
    0x9180605040501200a080402010e0315180d110a1b0b0414090a0b090402150f0d0204030b07050703052502060304050607090b0705061501020c1c120503040209040b0403030e03 76
    0xc0c402c11584c800c1404c82c200d0403d02c080b50000d141510013800241400604000b400d03003964104059446c03050303410a1000c0300e01d00f60041000203400b06000f4402071017203103c11503009e801341c420049006010340041440042c9911810f594800414541035411541390010031400300600040020700b011400a00c20700341841c0500c101c0c03080040440422032b01d040d0f085980c0c0d98400100c0b942068048070050055000301c0b82400c81031062542c50340005800240056465915402030000c5034000c010200103695000410b40e1184a14140280014000c210080300c0760207008462490903441c9880e8002c2c401a0b60110318180c2c0b007510152495800794040002d050351095440c400f03082e4004200b400c09002c0d9035241e644900140411303c2da841020b500074082d9200308450b45102c2c5004106080b008400e46841d10003071800001034031240782c44054010124081e0302100e006990240807500c4507034840e280c3c0c003941d01c00500124105501c0700320360030300904100082d0203100212000125002a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 595863309 1106 595862203 595862231
    0x92809110f011b03091706010306060e0709030312060b0d1407140a050903120a1e0912080d14010b0d0605030610030b0c04031505061908030409180605040501 69
    0x4042c206d100c20031031000031014122401540c0411601c2d031240d1070351a1169040b94002c01142c101041080041d1052a0305100403850b0700c80040c50a07241ca00380a00c5510181d0b995010f88c0c3c039100711045065440031106c0e04540036050060080c4044d2940c011030303000d000b11090900c400891810307400c1c2c40a00410f500c3c06030000c0c400b591200c1041c000341c840d0840b15122140707000d80e2011580300c3e602441070902517841c0c1c102000c2005003c0d69031b40065a200030b018002081d2078080c054800441900d00a01818080304000c1e180c113280c1c03034050211100c80d40018800d520803170a221000003c003402400b5039400c01c0350041030365602c20100c5d10a2185910090400311001c1010f41c1d20591540641d0180004a4941c2100400b100c2401d003664254022024283c000704410403400c145079215841880034084905403851203501c0b0801200c400303c03025111651a0084450009 = true := by decide +kernel

theorem cover : BRFrame.Cov 595683453 595863309 := by
  have h0 := BRFrame.cov_init 595683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 595683453 ≤ n) (h2 : n < 595863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
