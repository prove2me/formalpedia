-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:40:19.31709+00:00
-- url     : https://prove2.me/submissions/74022c5b-1f56-40b8-8b27-674b4e52073e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 12050366 ≤ n < 12230222 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 12051616 1250 12050366 12050369
    0x5180a050108011a0c0610080f06090c01050c16030f1b050109060f0e04050106030c0f030501032303070812060f030f060714040f0902040807050a08030d0b04090206070f0b01060f09 79
    0x10b05106151300341444c400410b0048541c9503000f480f0384020801c151000c503c03803008552000701138507104125004006c0d01c6881c102e909246503400b00d508080254841c40091070a134800c401078804081400355a4902031001d0350007030711454595414881841500020407c8070045c12030307031512007460080080c0080e0641d101d4802842117000f441c038401c1d070107400c0f1601c0c16403005108204039a19410081c008140040802e40010400d42c191020b0500030302c140c0307041e00d4229841070038805e190400c0c649854409001080b060106110590014080402901c50740b2400320901065140c400c1c180041081c00341c42e600d12035803140004503410305c004960241c010007549895030030b620360030324480310512031580700d620a0540e0103000128580e241e400303030041d10340e90307015030300815a99802c11407084c0881c06405ca00c4c4d04204000c070044031035640301d8080c5030006400400c4070300958000611702d403c00d54054500d15403243d014000c02208807612809030156040548150900050003410001207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 12052866 1250 12051616 12051629
    0x20a030c0602070221060c091f091a03091b09130507050a0801020408010c0507020a0e060a05090a0b01020f19020f0d0212031902030702090f10051005180a05010801 72
    0x295544a001e00116404441070160042c09040025018030130038032500028003000e5501d03000305808a00140e400c0c07801c460402d0802404594210f5442c20101300c01c180140c040414002c1174807001030b140c5d84280c0c900e500c0da40900b01c090380700e28100c0c1d00c02d030429034115000008210421a51401c40d9112581250810102c4040c000c454810340f4000d45040701c135030496507006400d41d4000580c10390540060080d182020000d000300f850306e84050720319002c1c5610007907024440d904217100320915400c1003544080014a120401a51840440c9000e8025182008016120b120520481d41c04103c00030000c44000300511145100041e00c2c10480d143d800001d11400d600d10b11890103940f000b0010301000c1e0001d1103030201000c00500d040c0c0c0d03517000da086480700400f60052a00551300102c2681c0c065500a0483c030040c1e5103586446011810007003c0e45900d140844000c145030310349182c846c01600827900c440359149101002d2441080145030400d01c102d040c0502030069076032007081c140c1100e43d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 12054116 1250 12052866 12052877
    0x6060803180103020319020d0905190201030f0903020703080f0d05010603020a030b0d03090b070c150503011d100605030703180602030106021005010f06080c0708070b0f0601020303070e09060307170102040501170403020a03 97
    0xd9210b0180090100c06101a2941c0b261000c0f80c40034090704500100741c2f52003600d00b04084085c500e0a0415191202c1d4041c016800090301040400d50b5400180300303007203450115901d04000d0303850b88000c84000ba005600029404200a0b000d1a00347c07007100c40340001150070441d601210f50300100030024502a11030210400329242c010007e6900048018100c102c480d40c80e076245440c1c0c010f2443d04244a01001916404040140000706a924501441582f0010881c0c942090010760703203a030000c0c25040401d962003c2064003105514000c00e0050711440e809a80e82d450408000d103004414544d002c01207180000400ca0f0300210021002114010304188032242d480418071580c0707015040700942a20800649801040b40c0400807522524210b01c000f101511080300499a0340000c0b502c40c0c1c0030500d95220032800e46029880550721140081c2260750749905d940c081d40126507407950107283c83c0c0d008641808030750b030880c1c0a80c2d07904981058400781843c0ca40ca00030b54400c5075405c05003d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 12055366 1250 12054116 12054127
    0x50c07090f0204030c030602070512030c250503130e0703020f09041505060309060a061202030a02040b031c0503010806090c090a0c030605060c100506010206010f03080d02070606080318010302031902 87
    0x42d0182d500450f004080300310070031b031349003402d1000e0750291508982070301030195240200110101968040e08003075610301c0c00d0040300c0700c0311b0303080702c0451504402a4a17a0b00d00c00e030004008000401d8080d11081d50900854138241081c0124480035009500381401440164200155901a142110700440700401c060300c0c201203803010301c19181c00c86504400000104220001c000a0250044121420401c2000d581d040314034584030700c07602c000b903054010700e8503032016140c00d42011038041030003401d5600d5085284860006802d40c840b00c18081003000c001009202018041c4a600101483c05000c0411502c800504010030081c841100c00380d41e000005040f0b442544554050940500b0140d80e0700c40c8628080d65446107092240c0a0307a0500e40010f110354808181c10b4100d8180c8844943c80341d04541e5041c4154001d0600000140d90901040c400318000b402848014035209015558910803081d901705e0406c04280298103050040050062003400e8800303140d03240c40320050058851 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 12056616 1250 12055366 12055391
    0x50f0f040807030305040e06030a0f060213050907020a03031107030801030b0a0f02070c03050d030b09070c0305070804030c0806100602030d05070203090909010507090906051f0c0b090a02010906050c0709 89
    0x502864021420741e2003844804070400d604240144141c41a07030400c0012130b5202400c1644d501d494050003040c0340e26100114000070001e8024000c403a040054030114187c954000c00c2038284c045440c040180e1000c001c407018550544240b20600c40b03050000c41c6004550344011f400f488061000400c240111400510569036a920044907007900e114250354501e00b9080c001d40307003050350005582a00400400c0c00e0240d0083c03007603502c140700c060000144c540d100380b030555034010a5030b0140c0620504100410008100718010400b4600c03c402226059041c21200c40ca00b0310000c288110b064503880c01881110340001c143c0740c1071030702c8010205590344c0f8104200d0035805100702c5580c101d42c0c2001400b541038810341102e0312a80c2c0544d01d4481c2c0a80d280300c4901074403124810b5940202001c0d481001002c0d800c210180ba00002c0d007014010003d1581d02d0860f500780445124a01c5c1c4c002c080e0b0441150b81c400b640b50003c008901c1d03e9410005030441c2c9580300c00d294410b5101c496900c45000500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 12057866 1250 12056616 12056647
    0x10f02070b030109020a0e01020d0c260706090512031510120c0306060806010c020105070609081605030405010e0904030206130203010e100203010f0518040f060f0606030b090108060106050f 83
    0x1802540560540743e50313403008a0310103074002101c170001059072445124181d510004030107021401d566280742d01900700b0388500c4d030008088144030703507088044214000c1e50344560300201390135441242c1c001104102d5050240c00c0c600d0300030354950144003c00030b12000c102c035039250300700728801100c04040b112051182510852000d80743c00381c0d00b904205032005801e0f0036500c1003048070802e407603405040d903425004480400c252200207000c200140403e401003111544500700311403045a400d454008e644c004a035181038a08030440f0700340e20006044c8540c5d42d205054422020040d030750f081c210b003400d41e406900c0d0131000308040045400442038a09641e02504070342c0440400100b99500c0c4a01c51820340d01a62003406090503c1c424070400041a06010404201341d41e0b000d000700b80961241e503100d195000c1020360590705d50303403500550b00c1c86a505100d50707001025617440000e0040100028000e6500c1c0507030040d0007640040004004a64000c012602c500901c403c080399504622222040d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 12059116 1250 12057866 12057869
    0x4030b0604090b0702010507090807080a080f04050a03050f01060509010e010621061d060901080c0603070201060b121503010501030803061201090605010b0319020405030a060b01020a0203060709050f0f0f010f0207 93
    0x80c800f80d04050003441034041d031006004020f80e5491041e070549405050b50b0b00c0200f841003d40c01d0348018019004280750f0000703421030021a040507454285c0d54000070f040c0d446550400c2d240f80e04040c909800415091068200030300065403502d400750300d0003900c522080f03c14460b86081c0b10b483d1a49080c80e000f20b100300c03201603604420812500b62075107116006440545104401e00354000e001c200a481d201225504a50203500101291802e2000f44210707a04050010b1f4103540d00c4a01c0403c04520510142010951001000e80280b41802041000301e20b01c178280c9000b1b03490640180082002c05003220b900040541d0001022440c3c2e5094900424051101a1045262a0000c90000799050095000d42e00004400c40009200011a405c91007248100341e4103602c58003c060000d21030790440c0d02002c00c140145c2d0042c100e5270300401d043c284115404000a800b8003401d0000d40341c00141040781c0d034070a950201e480082640410300d1001c100341c1d56814442005150848240700704034510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 12060366 1250 12059116 12059123
    0x90510051b030405040b0402070b04020f0111010c02060a0f090b010501030203130204050108010e0d110c01081003120309140c090103060b04020705070602030310090c020d0c05030f0406020312150604030b060409 92
    0x104510706514078030707100c0c0c1240c01094451814141c0d8401c1c00d18240c020b4511058004a10180c0740d20742c0d9080180846000e0b90040c144440c2c0d011a0107500000e101c1c0e804400501d4003d8207241c681401c004048600c503000302c09205280c5425100891100c0d080030341555000e00313005079240c5802c44d940d000d00050311002540b040c182400460880c0c0d0640002c030600c0b01507001c64000040700f44c41942c480005042840199101c4103545103198456010680c000d0301410048848035165100c503c02444400100b0380441e44030428401002052003017a22250789440c043c22040850400141c038440d01844040d0109032a0201045140c0da1035040b01c4016a0020480310010341e1090080d4598100b02d82180e12911150000141107510780581c41001d800340d40980b8010203102c2040c1c401000d13008083ea01c83c84280700d060302000c07081c0d000b0800f512081d001142c481c00700000c004280c038030040071141d83d11022280303820745488030811395003560340c00307500d80d0003070742e503038000f1400426103404040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 12061616 1250 12060366 12060397
    0xb0901060503030a0507020f06030f0a05130819080106030507090e040203030c0f060a0e0606060301090903020f0706110f010b01090312050f0d020405040c020607080a0b010c0b01030501020a1b0309051005 89
    0x150400c0303805c0001080c18510036150741c12544408001c00c40540012076a140d0b01203148000140c40c1d4500358845680b2840c103102c003542c070030243c2e1200c0203250081c44000c0c54000e61072a20b00101600641707294014000d0380b4041c03201e031901d850300030000c502912550441450140124045650510a8500b65201481142c0798440c0c000640c55450031f042d5030900c450b41c513103919541005008038055200340740280c4454550307460002e06400514400c0002d0701140641e00c881e01c000c0c0014080400105038959038a001107040f035448500b13025640d183c241c8142e00d0502c4502c0c80703980061a8a007145d400499404d03641c0e010082c155864401c0803440b04202e40009a5060b00a46c43d070f001d0310030b5413810360701000b0031154008141d94500c015101440854030020010303492407a5504040080f6030107140038009403d49540b000f46410f000e820440713250350003095105c0c4107135200c05c52000120481000151701c0c0115200a015440240903040c01003000c0070300c3c0c1c22090f02600c1100c21825204144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12062866 1250 12061616 12061627
    0x3030a03020909010602031e0306011101060b0c010b0d0512070812011509060302030702070e0c0405061803060f070c0b180f100c030c05041401020705030d051306050a0c0b090106050303 81
    0x30001d600c041e0301d0710321900c005000400ea003840007050381d40b50910404810a8208071040820484d00018081c2c1d040025282040d94194020701600c0028943c2011003a11244405105825201560b803c030703001d81c20554200d0040390000403581c14040448203e039959580e9070500c0c02c0a846003140d03042d104854040002080c0e080c00f09120b07011480760362081845902c4501c21810382c4010384010740140c1c85900144001680918495001a0340790101c501d441c2c0c2d035801146241c0c1203040b154500c01c1c10050400c1b01820244003140c0c0c883c9800c4005040c61074000c0d80542040801000508000301c540c0004444ac04031080103803510b6180c204590046a030425042d988600410700b0000c45401e00303d01d000503d00074018085503200c1625624281350a0a681c900d510444900c513604501c00d150000503e41ca05200d00c0003140800d64405a80781c01c080502c40c003221880c1d000f0000c104041000b15481980404119680e030342c0290010000e0f21a9410640500300b2900440d0340350100040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 12064116 1250 12062866 12062887
    0xc050a08160c1202010210050f0636010302090105060a080a05040203150108030c0f01020a0c030309020f1017060604060f05030901060e10080606030703030906080901020f070c090f05040503041a0403020303 90
    0x101103c00e5200341e00326140b00c0040000c05090302c1c010b942c49000c01094001041040c0b508019000e0700c0c00301403480d107480d0110300b05030803411116418054080301c0301100500039814510409405090306542d000d1a1041d403440082815000500031a0040e41d0b40000c01c045503000d0007c1c03010441040c280e8582545c44d46040c0b6169400301d05880310034880c616805400b110180255100003116442c0d141d045d4000e51001d03005007426180481c0d010030303a0041c104003540d40c42400b4a80c001681c5d40d21048824030004140c000300054030443c0300d41c03818442008059031014080007204000c0c03500c030380c482d11182111030160107190840345d83d00b2002010000008251081c5004031901803084071050b450300001c0c0358a881e014040580041c52030f040a100c1c060241c040e42c0d4024003c03900051501300c44d0383d00251240c001d0b143c00c0740c01c2e030200202003004511078064041440564881006203080c035a40e0160f40e4444d07441120028080c090640010754440000e0303400440d0042c056903036a150003031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 12065366 1250 12064116 12064139
    0x5040507080f06090103020f1011030c03070201020f0c030a0f0501020705010c030b040f0b280b130501030609020306090f0702070302060d0501060201060807060914062107020c010c050a08160c 84
    0x65105041c21903040010303205142a10f0300504070b070b1f00a80304060144000f403d004440901440d2001440881a03c8808600b0200004c086036520800a0758895555100090030301c1490100a00c1c0741c0d0200244100d176640110722544900c0c5e10401340784d81941c9500c1d000340039024140d0f001c0d1655281c40b59070030030260940c0021451000841d01008048941183d0204a607074400d044c68001d10f0386043d83c07034414540240300015003615124a2012607665040b403c4503030003040b4400c0031727132050300041040396014003450300a0407040d14103506510307141c00800c007404d038000c0c80c0344200f039264004640350038024040c040140d0340140c2801c1e81c81d1089282c0501402c400cac071a0600561074584000350394a400710303511080d2015950f034800540d1820501101c10355005d1031896000b070040107000e8021401891080351000c4019901002d49080d400c00780c00c2240c01240203041c4010360710a80000f034400300340021034941c0b2251654841ca030300c0300b42c82d0028001241c002c0c51072001c0100417820f00c4114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 12066616 1250 12065366 12065371
    0x603020301020d0f1b050f03090c0a08030415050309030313020a0b0d09020307080607051207030b0d0f0314030115080408210907080a020d03031802041506090f0501080106180504050708 81
    0x3c4c0082c844098031024500b095030301107442c900081c130103225040d1244044402190010541c504603204009210005070440c14940c0c80b880755680006810450b03c01d00071341e4030394660198140541127241c4034905ca5100d200c01406009d2801c0844400f1085690340030061010304880d01400d515640d50607050002002980e60507803107440796500004050034006801c903c90354a80e960300c1d0506125044c00004483d02078544028035490358240c549540300c921903030300468050382b29540708245604010340500b810300c00c04003800908000502140410383c4e028102031410b450700e040666180c3c03c1800060240d00383c101005126120195402681c041429005841480648029a6595000564560386290025006000c4825190119010364048203244407912880c0e200b662a640c0041d0031200586821507aa207991a01405110361007543c44002d800300f0148541d146050400103000000b0501c140003c2007030043c07094080c0004040c1620081c03030050300078401401d10300d0b000b50542004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 12067866 1250 12066616 12066641
    0xa0e011d040c262508030712120f0c05030f0a14070c050102040504020c010606080702070608060913020d05010606110303090a11060f0706060303030b040b0d06020a02010207051b09010501180e04060603020301020d 93
    0x244c0001007190080482182c050700d50005001480c070110729019910b2002441104030880c1d582d450119007110799020700502034007190b45a03640c0b4500280c081c2048400039101c21030309803a1807510110626280000c50300308604d4101084258118504140a4402e540006e41c03c640007007500e1164a0341500b007402510101e446001c000d0f5075405080ba43c0303800901c501c000040b0f14802042003070500b006000e0700100303012641c083c0c000c141e40100c0c4100000345021101030b035444000304002c9a101c60500448801e89024524609200268035651049c030103000c0d15018079041a41610f80c5c86400300c130f584c00e0418074002e4442c100c13410103000520441c031003900400c0c01c0100d902d001d071506218501c81c086004100c015481805d403500130094205e941ca004c2907641c00c012070f80220764108242d40d0401c1001660803011790f2941c1c24005a04010fa00490500c0000e024070010440c2401080301070b40c01180d001e1036255168109240a8616903001941551000501388004002600a00b849001c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 12069116 1250 12067866 12067933
    0xc110a030512090a080f0a060209041b080a0f0c0e040b030c03060c0301090b01050702060d09020112090501022820070f03050f070b0c120304060204050a0e011d040c26 73
    0xc2c2c1d004c0d45900c40301c61186c15812a04642e28103400941d180c2d02420303082201410009528244c2c10a104004642000c240f011528000070807200e026280503140020903540014400c00c00c00c601e02912030104580c035180b141da11a03480c0b503050740301000201ca070303000020100d81c07260401c0d040300140ba601c01e0003424540d500b02400702e80254000c00407624240c0d4090415898041c2401200d001070102d04022410010950120719484405006004116000c3c0000580e40c512120404116005000e16490001012880c041c0c007160400091401d1407102c1e4281e644001950803024205403081d08000040b01200d40302005000700050b0040044640d80125814103444028400031802074401d0255243c0c4484501501000c98001464200342300302005802c260b150030019a006269410912106071242d0040140e0042d005204141070f2074000300c54101c0c1000e498200f201116401000c8850070740c40d0150003000480c0c501046000100c3c0150b07203a428040b840c0448000d14104203009508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 12070366 1250 12069116 12069119
    0x903050304051c0509060714010510050301050f0717100e1008060f0609010b0d0e0d0804030206010609050d060911330f0909040f06050c0403020103050a0c0c110a030512090a 76
    0x2c03d010000a140c40c402c0c1c481604003101c030020029a03a001d00c100b200c9204c60911320318581c1c0782c2401481e000b82060009122510f00781014942120801480c410311003000c0c0d01031207281508510389824229015402080582d20300b02841e0140096a110030411103c5004100010b400f00c202042500c041405460041c0c96600c6c3e1100c1d5140c0036207900d41d01c4141c000041003c1c40700b010040a0b070024020000c61003008100f15181005100b0380004003103000041000308165060100c64050010360a00700340160130100418104044000c0090416a0f6110450b0503c010030f0140340c090720000b40903000001da030707800703404859071501d5400310a600a080d4008080e24104240c0c0c06224030024024200040c0380100a980b00002c1c00130b84c1c0e10a04100c039400421144c2c0103491098520b4071803aa0784a1861000400300c6034001d10243c0713a02d1400a800148550100401c02141d801002852102c20403500080031460140d100070480d1050031981c00d071301d0b0900c801070b10140004844503180f46 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 12071616 1250 12070366 12070393
    0xc0503060610050a030e070b0309070b03071d060909040c030302070504020f090904030c050307050c0118030803040f0305160317090c030706050304060f05070e0a05040e0d030e0a06090305030405 85
    0x8100585107240d110002c07201028042d0310840140c0b0766001c40d0b00c0d000c10300c0501c2c865650308003041c1c0d401468041900008010714036200b0040140109030004c030139841c1d881c001e40000d04680b680b14800042c0350300c80c2c1300786a01d540c0b030005440da4a40020010b003040d0401c0d182c41e460140c00c031310040300036011f040390000d2945403d05c00e0311003146400160310f01d0940910101324170341c08024002c0b001d11a02c400c010003c200304001501096114400402c500000e00c1d0000d4402e110008010f540050444401d1000074850320681c0d40141c0c0c0040c42a41101e118507040d21540101400710030101080b107110018168082c500c1080110351440350003a581729540d0044c0c40e00e008107455034040e8055401000000c6c031a10046600c0345c010f0380c0020b08c401c201d15540094030b0007030350007000040344881080c1403071605030381c10b500404e0103c50411014091245007612210700f10060418166070b8010010520400e203c261500340d40700701d0403c211801450090500d42040e03c041e00e49108041c0f404445 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 12072866 1250 12071616 12071623
    0x2107050603012102030109050a0b040c0509010510030b1212180613060c03050904020a080906070201050f010501030207020f0301062903060303030a0b040207051b0111030f04050f060408070603090c0503 88
    0x69642054612041036246210443c000f400030600301c1e010340d61242c011011580900100e00788504c5007100c3e03031040c00c00b410300020001d459005548034900f25401007002d81d80b151409481948a420b0200d0301c2140c0c1000209001100b0041d11002d000f000300d100903056001000300600403a501c0710300c9907080c0350010702141d40180d140b440030305540e0400900c00705000c0d0300001d1100e88070380f4000e45050f100102280507030f0410b08103000443c000b4000d010312060184120baa000400b84001c0085280201d81e5404100040c826181415800030b042420754485c5540c68040c42e401900a00495903542c07031070b00d41c2402100c10b40c00d40c4800448a40c0e50b1105c9281205e0040b00010011411074456074000e00040808220841c0e00503820003210340010014000300c0360f0307807418640090140728940c1c0090301030400a41062030030341080213110405c000309016241550015207200114000c6000810098840d50b00441c202c0d02c281000041c40750b038140c11840f100b85c840c642c07051203180e40380149070f035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 12074116 1250 12072866 12072869
    0xa02100203190201060503030f03130606080106140906011218050601030c0e010b0703080a110702090a0b1201060e010b0307020106030803130c0605070201020307020d080f040303120e060c03010b03090c210705060301 94
    0x30703d60403c000803880b14801802032b5030840c4106504032000c4415a03201d8086641991200105d0394445c21704001038607007000c40100c3c030b02003600c41500c03610f80b5400013050340782407556404140d07940d000301c0030041100a600d10f114507481000c0b501d4030350712801c0c002c42c00c0b00c3c948a9512449203600c0089001e03183c010aa0340d40a5050b00c4241d090380702c030203001000d00580702c410258440e050280f440503a4070600715602450010100240c41070044c0305000020040184001c580d0f03041803020488980c80311b00f0030b811038081e000f15076101d4444e040c1c00c03405016558006010104003006120280617010400070542c0c0c42600c01400da16074a141c01e5959001d0241c000e809608240001009814036903001000c042c82062a149003c09000700400359070020b4009500050002d81550141180c922401118070f40c424000c01e0395242412840b03035188414060050368180c00b00c081141804201300c02c0d442d011000f000086158a6042c0f08c1401a140310b95982103486070440018850a22404890 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 12075366 1250 12074116 12074119
    0x50c0a1b080a0218150607060207060b04050105060702010c0501020c070e010e06030601180e0f07060504030204060801090c15020102040807060806100f020c010e0105070b0103030c15060b030601110a021002031902010605 96
    0x10145240c0d00a9544c944001d01c00409076040c1c105039842e6507a504002c000e01031143d0070060f02d032705650502c00200c0740d5592a080c081c41c5081e0041c0074961b41c0400f07071381c012942460f06003011a90ba1030254003900a402c00d2207840c0c42214000b107070407620245c500d41610310720300c850304a95032100105591040700780f00e501c0041484068040418a1a41020002d0344070302d01120b0013415200021880d00c10151301450000d88042424021443c2c5405620000d100480c000e006a04054071084103550048c0710700c504551900510001d014000c1d0156001080c52400b41c5442c40d540ba440078111040407207149104210081100b02040c3c0070759002c50801800760300401502c24405e0054441d021200781d490305002c400d2000c0400685002c0c5000d02071480f036501d071180c0403041c2c42c01000700718041e02a00c0809060003414071044040d00180c9030b00441c01d00e001401c01c3e084002c5503050181c41003001c2d4004450740701404005800100802c540c0c28007035042c180c0746500c828124200c0b2150302806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 12076616 1250 12075366 12075379
    0x7050d020a03091a070c06020c0103180b06061309090c0e07020102070506010311150d0c020d0503070c0b0a0f020d050f010501110606040f1b030e010510180903050c0a1b080a02 77
    0xa0020130a1805140e140c080c10f006400d15201c03890b15801c011000710360001006030700400c18001ca40d6494001e4003200864001113903140c2c00300faa9001d0891100800b40d50042c180499005841010801001c00900600074100001d44950030841c91118640c014100182d000ea00400c00c02803051003142d80b000e0308013000e4060340e42581d03289030ba4000b40b00300f001da006448011505c4680401c170010648070909020009005808050190070501403071618000c1c0103081c070412540070340037421461030350f40c41084800b4960b2401406070041c4030048a28140038808560380f00c212141c0e900240c00f41d0001c2c860501c060707071385038011a080c40c40c0c03110b24407203508003034042859410503802c1440d1020364000d000c1000400150415104083c0a444500080c1c54040c840e0300c01c0800e1190700d4001d007119101320045802d0905c1070501060540148040599072040170042c54801d5007601d0006140505a0f0007074109810600b104054081400b080e580e19407a001072001400660b850f081c55010303106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 12077866 1250 12076616 12076619
    0x50405030d031a040608070f0b0408061b040e0c031009050903040605090a030b07050715020a0503010302010e031507091a031b0d0b0d0602030702060a050105030c0607030302120c07050d020a0309 85
    0x3140904004441024484403007890442c455881d400341c0c5002d1b050203802808458035005a222400c14164850001448104003c1c407804c0d401240701580301d00e072041e81c01d1030b10303203841a05107a61260350301c83c40d0b0015244c0140411240940c0085001d02c003c1c074803030521301d9140ca045c10104c400a48000e400c0c0c2d841000b040000c14019005072242580040c51401d0140d41d03900c03640000c240444d640000500e000030759008000e030400b2450f980340c900d03000450600d10010800387c114401804083e051005119052405a03803c11151801070074a103001c2c005820300640182c40c030019401140c0104550342110111001d00c9400da074410502542c01240a00a1003002c5c00540d00c020007007503c1c03035103900611505480b609441040e83c1c0c8102001039407031400c070000038100100902014002810200100120303940000c1e100040030301103401e140e8840444c58260000e10409100c1c070b5480381680d040207240c03074840c4080e001c81405802561201261301e0b408a0300d0741c26000004000c503421410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 12079116 1250 12077866 12077893
    0x10f050a0309110d0f03120c0c0212010e1f060501080c040504020f0408071806120302060403030c0e04060801020a02190c0b03040807060207050a060b12031801020c0d05010b01030c05040503 83
    0xc11200e8502a620083c2c403190400040303084a84030316015601011003c000504140d4441d594280c0c2c8001c80b00c0400480f100c1000041210844100203407194912401030030345d101082d481440d88100f807404455030f0076981440c0c0301c100d112517000300141d580b425400051950088030035034800c1d0104540d0782d03e0607080c40200402500014000300e0040301c00c0c4008616241e04111400c054503446d61941c02c00b01180036080300303a41090700482408020030910200080e000900d280e00941d042c01c000c00c1c10042c107201101c040ca01c0c54a190351090526070005003007035040d401419602000d80c20b076200032a20b6900c1040960041000500c44101e81070f081042412074809140c00c10b2140210038500100c07a02e4000598011540c1650b01d0741044101004000f1203101301c0542c0c4806440c0f1203140b0320100102d584901800c01002986c074403101050206030b1007881640c0d601c3c00f008105032081c1d241810b2050007080c08110030384c0801d14010466520038000c000f62001c40d40000c005207542d0383c4191 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 12080366 1250 12079116 12079121
    0x90c05040b0304050307060b040c050d050a3902030901020a11030102070f1b06111906060f0605030906010e010b04050409050a060203090a0c0b03060a0302090912030412030506010f050a03 82
    0x14042080820321010860030745150040d4000c601a000441d11a98542041412140740740c0765240f06a1810030b039a2010707a088819a900340c080a40e000609941c2c6071021000303880d9036084031041c8030880b000c051100b000155040400034031540c104e40000792841d002e0307960348140d0794001d015a00447c40a80014901c10036005841005000542818142e582d03058500341024070803103542c0c00c0150500c104688881d101001000640b030801450300703900301c1680e10381e11240300c0710303c8900c5a40e1001d814030a003904103900400b40da40b40d800304203599503030081494000345c44140103401072a00011703c02e20001c003594140e92642d4400ba184c203140c207013004020201c605041b43c07c0d010f07440358030010030024409188030b0703d005400307055a0f241074036042070307211401e410107072460340d00b031091250a0700d0b11410101581e506580070350050300d450406a1500c1d607140200d8440d034000001704001c01c0558402c80540b018580c1b801e03c07050f00c0c0c0301c0040d1001c80d200c0d07009030b000440c1481080100c0b07110780c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 12081616 1250 12080366 12080381
    0x10e0a0507030b090f10020301030201020d08010b040513061706060a060e010806120f0106030c17060c030109020309030c0f1b06030f041115040b041508130308180a050c0a0f03050709 80
    0x8000301c600900266558a00b4580c03000000943d01f40c1c040010020341d43c040c440020040b8243c41c28001a41c10010444460700850041502800b00508182404529540036402508640e40440b400081080381355540b6481155080d00891420718005034480c0280081c41403110161904001a5210001c1c024848481c03842c9140314803d90341c8458400d01c081c803d40000d14025010003074054201b4490090301035028901035020fa010804000300804030340c0c00c2c4ea0650301c1442015a407a103440107020700c1c500608a202d0010300561006035603140000810f040d0031480d9440d0b51680551074420024280030480e038000102c1840c3e400980010b65284240960f240e0050031306007a480c0c81141c0e58429081608019520000001c0c2800300040d10051b9180480030382c40c1c101110325048403440049000c0b100000c060000b03007008525448003d1071041009135003182298406030035802c2c11640c610584480c030b8000c00c9078000c042040a040510402500e800c04001e080b010f1412a0301030041414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 12082866 1250 12081616 12081631
    0x30b010b070804150903020909120f0a02070503031b0c0f010203090103050a1806050a15061e050d050f04020a050102030306240f030106020d030b03070509040209060a05040e010905010e0a0507030b 86
    0xf0071000c1041c5005810081200099654041a0904600c1030122860300641040031940c030130040700000304c1028007103601d0000ca01109a48071012000140d160020b42c0d041107516020108000b0310002c0c01103000c10700002a00102d03054507080000340301c40740103108000ea005130002c009003010395010381c200ca03400c802800c1d000150603030f0355007401e4292040103008071182030b00c880c1844071600880c01141c0811556480c0c21410b240b070028050211140c1900316071640310348060301000c0e1402802030b07551024000e0400d000e1483e100201d42e01500003181c08038420003100030042641d51000055038030a000152289040030040419401e21606034241100c14a204010100c1c00044c02c4014500801c0140c0092001001d13801d0058141c541401c150390083d0b220102c104056526850741c0d9400580650300c01113981c5524011990302c14a603007206070418208944082258815070021030118000d0300200045400d416401c1e485019230b800142c41d07684001e4050010901c0301032026004401d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 12084116 1250 12082866 12082883
    0x50304020a030b0a0c02010509010e030910031503060b12010605060f0c070302030109080309060106050703050f0921280b010501030b031c0306060f020319110c040f0504110a030b010b07 81
    0xe40f0781d030309103c0020844041c404261920b840b0550700d074090040c25000403060000344480b90129131280d580b40600c2e2900c2d84035000061980403164041d50100c0ca6061491a0041c560740d182d05100d4003824212244600400e080d0b15a08c41002040c800e00e804d440d40140380515114a905107185903030400c900c81440d80c040c0b407800000680c0c0c00d00c0f46c41c648600c601e01507a01ca140010349070381044016030001060010401801000aa02108075210703111084e00c0251940402c0010801441040c1c403803210040c80c156004d04045000074814000e40a41e220284000c144903080c44092114805d0041510b00d0301ea0041c8a558025003000c4132148018044410000720309031074000d220036803401e05e030201c0d652b44000e00c02d0951100c2c442400040d58001185801c10030a0102080203009610108110124180780d034420420b00c03a4104807400240140400c00070041c46000038041501c04a0702d0100b054038030300703072400c0c64484681100d4124140307820326882c120340084c10740d111410440b01c221 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 12085366 1250 12084116 12084119
    0x70e060a1b0605090607051c0213031a0103230703060209031603110a050d0b070e010909060303031407020109051009080909070302031b09031e0f060c0a09060305070c03050304020a 79
    0x8014001c40285140a18400f00386800c080e07041c2c40c03c0c01d6000e044070b400c000c0200311a4021200141130130540404072000140d44000d8540800301d9181d45810040c8011989240d060303c02c2000c201c640d040c3c074050300e400144111150a4140c50418541030441681c020b01d208102082030fa90180844035405005d4503440f42c1001000d140c407440603003084408050150200b0140d0800b20102c034007400096400b4140c1881c40e40f129402040020400010420215100c5141d40d1003000f4107001040544003e0080e0707a12440c014000e4441e80941c5801900480d0001d0301c0c0520500a03001e00d2904070000c0d1951030550784080d07010380700400082e208040100100b0b800b41e203408042c50700c81c801070b03070f40180c0f2030030300007c1d20000603490554625540c006001d5041d45540104180b2500403e90911700d104148000ba003504028040e20091968025131007005003e280c600014403015040c0d44e1410f511130b48691060b01100e105456000010340f0480084001134040c1004680042c0001c1503220321a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 12086616 1250 12085366 12085397
    0x90f1e0806100f050f18060307031212111608030901020c0a0303060302030c0904050c0103021803030301260307050705010e030c030109120e06030103150b0612040b04020117070e060a 80
    0xc0742560001441c0282c20b00070000c01c8400c49603100a003400311401000480107100007080541c1c1c5405035080c0421007400b040681e41c1c1000507030001c0d030340041001480030401401401000e05044490040350a15a84c3c1501c14101c2e02110845403040002c030119004e41d0b1074070502a000100004410b43d407c003c0f040300b0720000c00503110705621a40d004107107035045105041c2402c074840c0d40b6600034100d04050100040b00492180d0841401380390060722100c2e80070302e1214040398080c15a401d070100000219070340b0040e000103030480c6810b0511101d1403050754a000d540c1c2c8285e040182031a007080c00144a590710511120b1039805004003142c91000444001908403a05c548084562400380071801050941041042c0300d60102220307814190743c91078440c404d00c0960030300b61801e030700d5030340031042d140c2d644150039602c11040c41045c007442854585801e090703c030003e82d82a40411014420b04000500d0b030000c00d40318420310b030b40c0c40504050034024040303203400069810040c85102031055004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 12087866 1250 12086616 12086623
    0x30b0a0b0f041701020901090b090307120f0303140c0d09140607020105060f04020901120f0908130302090a020306010f08040303021b030d0f0504020904080c03070209090102070302060601090f1e08 86
    0x7903101d6030240c140e4481c0340c803441280105860400c260385074010300c8520310707607a00089100219000880c41c1b41e40c2c1c080410000c1c2c1002081e8201c4202403805000d41e20900c52061980140f1900c641c1b810480d03220b07481051119502c046912160310b0408006191880e02960441c0c800d4610a020f01d650302055001a0f900381241240c1010040c0e5548041140307a1520f01040b103960341c01514210704e04074138580020440b05428007003001507a140c6008200111340da5001d6980d140e00441030f81e4880411140a2030800c005220030b034420171503c2e021038806601c91084078000d0070b05071240b2004201c01c0a0540312b0540040c401d8080c50340c01c0c0540f040d001c0c040c00300300c074841201101a40d40d8030020703880350382210401160040d489280108002c01600c410951640003030b00444200c1e11079520107e410b01e50302c615400207420916440500496400540280c2301c01c610a40950703001d0740d1a000111020602446215083c0c1c520010400040c0800203511404000c030340a521a025124040c4514 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 12089116 1250 12087866 12087877
    0x2150702010215070c0201020705220203100302030d050409050c031003020108070c05060106170a110a140f04030305070b060d05070614160305030609010602010b060706020a11070b09030706031b030b0a0b 89
    0x105c2c1d8840d07404021503906002c00806804103c8032104200c0c5001201d00120341240030b07036490260f000011481ca0b85840560748021503004007103520203408148001d1040c2c0246c424004401d041501040d60031050805482c0f10780541d03222039000b20b01d1a00119124400500b00380140000c4660101c0825005d010260203829661248019009450b2190701c44100082440ea80d0780d01d000f200546112000040b01c019983c1ca103010b403203599041c508001c4503c5014040000503000040001c10560004007030b004260080208203d60341c0c0c0c44090003214103610320020215000b5110520040d1700031405503068032038040c2098107042d00d0134044a45150510000e0b40803031404010400b480c41c04440d03450161000e0710080c400a4103080100e651406440002000d80d900410200c0c4802c0c4117803000400d01c0300c910110b0712060342c3c0c0c40d040c120300e620015000b4000d018000300810158001c5c000c42664210711140300035580c07801c5608070001c3c1881ca00081e40070701c1c11240042e4141030b2201810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 12090366 1250 12089116 12089131
    0x816060b210f01050907030209061c03080a0606030209030a150603081303020f06040e040b0403051207030c0f0203070308040b090102070503030c03060103060510020307150f0e070e0708010302150702010215 90
    0x1481e11954044461400c115030782544001d80c1003104001e4192008566030007101d41c1900ca01c0c0c8940c41d100005200040c031080032840301346a004d0804285507100003464000c21846204100e15070f2030701d078220300b80e00c00c02d848550513034884c00c000b1001031060014100c000d110b40500040b56078883c0c1d10b41200c2d0344182044200030103545010300a40c40c0030103c1c9044046c08480161401c0d1421a00c0d01149c840100098108000040050141405002121103481007805240319508c1c1100c0f001e030081036403107000e1000451503143c1c641d03a81e00000031100040d400d6201d100059503590f48805d98280000c2c83c020942d5001d100910002e6410000b5601038145a80401c0d280e00e000000103003100c14950001e407284100c0b540d402500c43d00441268070700c03500104816030000300d0840b000041c00720030a10728609c03450b11981c3c942c800c0c00030413408203071482500007105a0700e628104175100d000030301000c3e501c0b400d404221505d507210b40004041c5184180190342c00004101000520000119540e1307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 12091616 1250 12090366 12090409
    0x61308060f0106030615050a050f030a050f01080d090b031003061e05090106030b01030b04060e07060203070201090b03150d0302120f0c161802070204090c080703030801120816060b 79
    0x5007480800c0d152405402c082c40d040103101d103800c0c54950100b180800030024414009040c0304198850402c480501c0790307010707020303030790f4242250503a008200c11642c01400020780c00010683e4400422407403400149547ca00c03c162b401d2100b801496803000d04a421103405200740000020020300903400394801d103100381c0c442041c030012201c003500c0009100301c895900d09401400040d2443c2d181506580d00281e003207401d541d0710b280c01401000450041c40340d901c0388900c0020266400002020300074401e03a180114070341d65290007103035400706843d031005001d91118001207030f0504503450401d0b10300034030480f003603851407540074481a40154460516248000740d0b03142045010400c0300d2048a0600c070f488402460610600d141410364040114555000101e0a06540d91a00240070a540250800402c01d50791041a9502c010030700c0218045004c0000000302d2031140c103040560700d80c1000071940b030011142d50400c031440c2a02c8044440c0341d691000c0a106884603201201003a420700002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 12092866 1250 12091616 12091621
    0x4081006060207060e0a060e0d0f0b06033003040f08120403030b0303120105060c03090a14010806030a050303070302130e131b03030504031202120324010905061806130806 75
    0x38203240705030f0002401d12500040704c501c2500c58494070000c0320302c1f920b80388070541c05442c0000c5041710400f1015000600100d007c0d0b0a01ca00703410520f0040c80110115004010380cbd015448104001801401e4031513814a42020a40ca20000465105210714644580c90840d9503420203030b80c221440000046400408000805401d441620100d52080f0029810040c468454400200303050217000c0c0100310100b04131a14034000c1094070741d10b810003404034044d10344903280b04081e07503d01d0311110f0024213100007007445800c0110704160150713000b4003c2c610b0b6545214041d4017942c801c000007010044000b500040c07002a4444031801031890041c01604810309040142203ca1420611402c03248034000410010350020110f40c100d03640300d522a00c10104401044e802e00c1070b5898501c3e02403000104005050151401041480f0344141000c80030000c0480110b91400e02c40c02401c1c1c020200704094440e607103030003e03440341401d40144140d10b060f240311070042e00384040d039100f010075900090a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 12094116 1250 12092866 12092879
    0x70c0506011e051e0f03010605060d140f010f03120507020d050307050f060c09040b030102040302090408040f0e0f0f040611160b01050f010f0f090f030c05040c030905071a04081006 79
    0x840d90090404582c004d00c43c4105051a2000da544581221312a0b96054290078194400390000002048000d04194440700d10800e00c1c000340c4841c11620320700883c01400030303a550704c0c841c003110306a6a034640c02040807401c682d00c00f030451180d400040305014040c01a10010380da120a18102c651148c0042e5441d21518641180b42a0300c4e49044401da402003020420760f00541002d40c0c0d078480301114041000044180441c0c02840b90340c01c00b0b03400c9503c0008000500100f28010b10031640e4101c01a6141d44da10004001104401e45440356982206000b107046040e0004035507030841d01070100050000304042c20000f40394880d0252010341b40c424040101409041d20301c660041000317036031400340004001e0009040301800382102c010b00641c0075034060103034420b5007400c0207403c4000d180c0e00036541b80e003042c004407901441554861420403846e090814484e01401c1c2003261f201c0e00610352141400c828041f001c54030840440414024000010b101c04100f000c460290b02c04640003c40750304081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 12095366 1250 12094116 12094169
    0xd09030e090a06050306060f13020c0102090a14030d032705100f060305061609080601081005090a020f06161b0305010c0207060f0f05070602070317010f080303040b070c050601 77
    0xb442c0100d40d624201d070801480e240403940742d5008030308450f0000311110660004441c2d5a00c801c1c82039200703101217984144076005600600c42c1c011300f15140f0310095550304030780400c9455024229059040304490310031650080e08810800815921000c0b07640141d03c00300c01c0004424001130b18960300c07051918030328201c40d01c81c0169009440c0d0f824400702d81180c50307507a0340d08409021070900c03030b0019440da60440d2166001502401c125000e4071040d59494000a9a4050401c10701079494034141c04114903440000708040780382e5000d080d452071116410108500d80d04000b03175200c54010700c0380d16040050034102e680460345c880b0b0f0346445000790843c10300b1800c40d03503254942000d40d404a501408250740080c20311490800515046c003074000b200104503454003c0c0d03040207103a2400415004101500840d65014000d04e4a0b101c12540e80d07100620006403449104030040c9401c200040f4000c200381007103865011400d0700305045d035007849a40b0285019000d80c0121600c44060081c82e0031501d002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 12096616 1250 12095366 12095371
    0x30902030316200105070807030215040c05030610060f0c08160b0906010e071202090a030c030303020705060f070c0b041109010312030c0c0b06010c050a12050a0e0301020a0509090703020d09030e09 86
    0x3c0070b450000c640c0e0400600350744103a010240c040000495142c0c1054403c0001100b07082c45a00e15600c1c0d0b0601c0d01d0304018180c45070040700d10900900c0d000502e80020f4816000c1180c5042da29480140c103006801e6500a1610364240d6000c1010000c102101e03000030348007041e892284c1e460300d14516007036403098284a0183c1203424556001d6040c800d02590060300401141402301e0010b036544220800036403d0089540000c0106154090010178550958040c00c5224020026902c80c0d0351500c80350100007004444441c0071468014030300c00818a14064031341e002c0c1c40b801945c21030460000004000d190240c0c402c03291990b5030000b142d0110740c035002e40d141e000c00c581054260350201d039072190503502c00107241a04201b00c125680060000070019102a00d4001440103214480c010005205920020326900452108241c03100f250805100700c0e884c22580e569441d00b025003000400ca0140005041c0b142050780a00110f0b107028541d1085480c817034843e4030344041c0106900103020310b44000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 12097866 1250 12096616 12096653
    0x10050f040209060a110c0409151401030321060806130c09060501080f0402040b100e0301060e01050303030c030612010606090501140c061801021303050106050a0806100e0601030902030316 82
    0x40c0188040b5880300d005480c069200c90400303a000d0002480f400f0b24082e40300052940c860b0410201c4403e012003003030400c0802d061304e0424841115182c07404c20b0040c1c0d0038030000340042c40d0b0000807006105c10b01c09000910a191002245695445c14103601d0100c0a1b944051501c14500d044401c00c481400f40300028006c2920a1080f941380c800040d00d80380e40100760840002d60000080c08641d00c0b9480001795110040c000511142c00500042240303210080d12030082d0b18014001c10000e910090075030407900001e00a5140d80d6484007864425000588011741040302c40d02c100150301020f00a000141c2402c0d40d80d5490380c3e103814001003071169101c1c01d81105050030000d911903903074040b4480303900110322525400b0800700d6520f140e00910440b0001c14900003002e602004000040d00500120f035011247c0c5041d40389c0396041543c40e61826a152102121403480c100210703106640c0541c0d0040d414100081c90701115000b10b400c42d4040980c202c0c44e0300c00426078a04100080c0e1000404221 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 12099116 1250 12097866 12097871
    0x1302040618050916050f01030e010c030501180915020a030b030d0809070b030915040302031c061502010b0105030711070b0a0503070206010801020a21060801020417010c050a0f12110310050f04 84
    0xa007414004e1080b01a0086a000d10076800402d00f860340a608544114141980204400c00c910000280102002c0c010918082160224200801250700400b4a0140c11071040301c09440800c04000003075006c00795103801d040d00e81c024900075640c140640e103145401c94a4654540c903000c030300903050055503040525410001c1c02404038130840061540810040003001c00c8450325141004e0327256005600ea070754400714940c100809580459001202101d24911740a012051a910182c0c00e03241481031045c00154103100158a2030710070102c00c1185c000c0c4009a4030140c0d140e8100b0740580d480b100c040340100d600041440725083e81000b9080c01401c2da003008500704220f4502c0140030356812142140e80554000300041e200083d0340c0a800145010b5000315a41e6558201c1d040b020b16050b490a03416501c0c2004940070301d0b004038121604040107585881904001440039200d03042c038403c1c0e22103c0ca80d611583c82620804400450259113600003803118140341108200e01c4082e0703000150f01960 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 12100366 1250 12099116 12099133
    0x30f0f0a05040c03080a020f07060903020405060301020306180705040503031b0610050a0603020c0c0a0f0302130b09060108181005060a05011701120f060501030605060f040e060106030513020406180509 88
    0x3d099420b114240d81d0301015a950b1695070110403072074900e14100c0c1d2203150090f0a000151b00380c1040c0c89000302c034400d031000d0090790b5884003010700300e0000711044c680042890350f12000c4023001c0c222442d40880241405420b0684900101e881d54022141d203414550141442d007005890800401d42c2c1b2051003c081c020044c02c020205c0c2007989039100f82400c1c15008141c803901c07040705005081d22000050300d102c180c5641ca50610421210354402640034480c00d0070b01d503960000c03034020755140601c00b6010b1190b80d180d41004584e000c1000b8207006121f03a54403141104000184112012104502030204071800c00da41041024409580400d050000214010605009801c000da045601c809001c1419506905280b29500c8170713103d0048c05145400e001004025013035000c01e00540c400d588000c8c80c00900d0301404100d400106110b41c1c41d034001401000000e01c217420045d44520010410100e60065a010400391405904140e654161007182d40d03c00c22613900c50b441d48100000020403841 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 12101616 1250 12100366 12100373
    0x130c05060319020a141909080d0507120e0d0c051005180409030c0c0611100603050a020f0f040e01020306030d0302070b0408030601030212010b07030e150d02030603070b030f0f0a0504 80
    0x820b41c0100b480549074004c41e0075130490b40a107500d80d260454100d5520b40c0c032900d40c138184026107540703c492008a11040700128003034000181c901807010300c1e519010f2a040c03064a5005112018080c00e50800001c10901c0029803100700e0a8004a4801c080c4042100d0a001c00c21004881102c2003c041103024400c0100c00b103131b880304001b850300080da8001001101424110f0304480b40c0130000d0042d11540c000003822592044803c0c1c0b41c01242c4003600e0b558041601315000361601c034400900182e200f5045000540b400c00c41d410801c840041406042100d903c0105058484242092083c0e95001c001c100c124202404031410150700c619086117841d45640c0c1d01c011248001e0805015072100bc0b00040807640641d04440040f8080803030307212250781d9a0390f00702036941303d01c00c218002442c6000c00001406c0c20381c5802d690341e80c10441c0508010541140a000390002000b480e4144920040011101c52140c01540140c004001c1211303d4603044060300c9410780d002d023030075401074581020040031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 12102866 1250 12101616 12101641
    0x60b010f0c02040504060b090c03090f070e04030503091606030905060109050402060f0c0109061401140108040b011415030903120c0c070303082511010e0309030601030204020703050c06130c050603 86
    0x8050b812140018a83c596040000080c0461401650801604030600c580b41420202462003030710540f044035400313086001c9042e21070040d07110341c501c1e24080501290019008402650380302e04400111102e08800300001060032100c0d910002c0072981e1030314150103000c1d080c400d580c0034040b100414040c6003400d0f40454054811a0040c0e0924013020661001d221400c0d00900b1013590400414040b510348400c80001240c003c1c803550364070140c0f031160700030f465008040390340c422a000800740385540e181054610085031030b44070040c2d120321000c40188680e8062005140203a071084d00643d125000d5100355031039048080d0000190310001e02c130344030b000403002444c0000d580c1d043c6032907803640d140d000703156403036191407081e1000c64505182c0c0345140f55400080c40000c59a81002844042d806145164076445040c200c00e406803c0940184094280b6030001d004051103807800b245040c208919407030405030240c4071404000b1000e0304100a204006440700050700080b90001d145040071000c1050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 12104116 1250 12102866 12102887
    0x4060306050121050408070b04060b010f0201090f030e030705030102030109060602010e031306031109040905060601020610060804110102030708040b030702101a01030b030f0316050601060207080304060c110d0f060b010f 96
    0x464a4490340041c0801480c6c5003030751409607006c8007940346030810b440d01d0000b90004002e0140001c40301c0c44a00511307072050140044560300030060ba0a2120280c90407582480c0c1680080d8162080100020710741d00d0910045000740100f180014081b82400300003420741e01030f10001c0085034000c0c042040c6088030034014034110748160a00041c03403d25000300c015140a0010b4030350348076252169001c2400f10100d107681c1700740740c26429103c490f45d4030039100403048410700130207000401e000001030009034408034540031000140101c0b810301d505561a00c0055002e9040481404004000d00c8003298040008000000c5464018440b481c40758000c208011710340d459150405403620f0104a8540301070028210304884a402e03039a03540301c4001035604080ca9002e0854451061400000d8a1480440c140f0b041d0340d05040910701d41845d1a000b00d81d200301000301603800c80400b00424100356180c2030100100fa114101c144045a17050402e20304984141c0c91031410310014440354a112503005c0b10301203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 12105366 1250 12104116 12104177
    0xe0f0303010b030f06040b06070b1e090d0c0501090f03020f07050409110616140d08010b0301030f14070905010f150206060604170703020603040606050a08030403020f06070318060302040603060501 86
    0x50f9917032240004d02500c4a0420143c2145000450006001041c1c00243c8109600c102035503a2036008003d80480c2d200480da00c80c50383d040b0144002031648500c04800056001d0380c00480c80d8001511a206950b0700303800100c0240c0d00200600ca08003009100c040e00030b020442c0d00700540c910300d03181d540141000c0d9008512514000070000c880e01007569015800c0e60300440402c1e055402d40180659401c1034140c02000b06528500005000c00c0500449060f2588080825400c11865030346100718240c8810704005030080c10000704802d240742c41203600130000d002c204114113140950041074a00c0c4c2010307080454201ca003c219503a100e6904403411202c1a14440030301e0840f1045031400c01040e500b0080d84008000144000e118030740d00044150b42044400b00c5401d0343c0c0c0e06040c0c0c2e60b44140d220003504088030032a44541c5140803009032011a000b402c2a0805031007042c40b2001014031a0000c0c00841d901117828008583e02d0700c600341c060b090a0070081c1e2040d420020300c440199510f023405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 12106616 1250 12105366 12105391
    0x301050108130506010b03240d020603130605041109070314040201080901060b0f04080f07030c03020f1309030c05060601030b0105030c030c0405032b050f031305010b03100e0f0303010b03 82
    0x14110a0382d036a0034012160410240e400c60758450080640a500646034041e07900202c40c001d07604141d420500d150301c0b20f030040c860b08200c01181d00f401059040241a91417200c050300683c0085240d80c041c80e8800e40c0f1030111303004040e2640b01040380d0b00d1009040e075000c1600c0c0030107414003c103c440e0040d4000d602400c1c001e240b55280240c450160074141c20070007503004003040602c9500708500103401900c81e10750076208804480070849039601100e20002c1e11580e12240c0400150a11600300f002c5410301600d86403076414034030841800d40704400c10403400503990b44102401c2c00014403100350452805d1800b13010504030800000c1c00340c00080c02445040f200000807400e404c0c200400c40300100000b82c10396450f08064030802c080504440109214001002d81801c40c003032041045905010041c0d14450440e250100303100700c4010722110480b01c5640e030304034102450b6010005a408240c10170404036060044400413401c0c03e50514085000342d20500c01440079203494001e42e6840304141111 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 12107866 1250 12106616 12106621
    0x50603010b19030c050402190507020402090d03080f0108010c05040317040905070f020d031509020c0f010609020904060506040302010f08130b01031a090d050f070303060302270a0504080301050108 86
    0x9005120300041564840540202c1c00821244400040100ea000720f2540380425524014041070f03104420164504515003140243d0842c02103001d0700b0007a0001d0001070a00742c0601c0800e01c0551181e8041c4d003c038684108000c084124140103d0142002d84c00a01048440d004003401134026404024603501d28408411209602c0c0c000380c03001003510000600c00f40c1400000500640042d040e018014000c21305c940b10041c3c0240a200006070800300130038200d51600404500070f40041e821240c0e5800703000c0d0360840c8018240190310140040641c0184d480d040c080811048031a44d500442c080c0d00148030800140c0e0300705600320b0016480341000e901950302d0701968400c0740d41c0c241002384410051400401808009140c100d002291110060502d485410950b07549086502c00e640001c2c804000c28440501800d01401c030062007420003040654072030f40003d44000d9803215191042041c40b802d00c40c80c844041c549500007110800030011400c280e210603c86200500589051001c02c030003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 12109116 1250 12107866 12107869
    0x30405010516060c050306101706090703091403090307060e030d0507140304060509010306090b090a020c0f061905100e010302150f0c0a0506010510020a0b07050c030a050a090e01050906040506 84
    0x140102d81e036010404002c503858044003c0c049030000c0d02e005000714640d032120050340b4010240000800261036900400d9507c240400c01034110041103100dc16440741d101c103000a06840050312181480c030301450326406040b0516252205640c410010001703205448003507072302d011803c0d2841440034a011641c0d071b15036040c5000e003070202d00200c1c0b01c00d1200090016041c1d9004029124040090381e060200342c0d070b0f810200c815107203d4806161b101c00d0842c00f28210706000c0e030092080c1418401940c0c020301800144034100801101c4441d034210400c15030030f80d00c0685d48902544030b800c036001542080d00380039170741c0035050050000a005c0d40502e920013150020a006456011070900102c0d0781d160110300d01d80d9203440310300504075068403481c03001288a16000e41d4810340361240e03500514010a0980703604005c900d0160009050200c10806544e64080a00c01450002c2047e10f4a984d10040300e00c00a01c10003055201d42e80d1141e06000600c0595108100541c101c40202d170f010400352950300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 12110366 1250 12109116 12109147
    0x201020708070308041505010806060f1c0503030108061b07060209130603060e0607020d3c050301060801080a0c05040905120c070317030f06010c0c080a0303020d0507110304050105 79
    0xc40140255601040942c00c0661206a41c1e21891155400d010141500c42d03040d41030791420b0084207400d0300100006415810500c068000940000300710b503481060800400c4030100c0c41c01c0c0c4c190340306e41000005101c1f45004101103038012100c1c0d54800200030543d800c081840c040c0d604024001ca4000491a140d90380310703819175070b40c0510090704201465881c81c019004242c0c2ea800d12800303018290004000b103001050300c0003000c011b81c03508062815030f542180364449030340e14000c2d0705030140e200f104490203410b14141c00e907000300d03140e00c3e42d40e504040c00034000400c1640230b41300591010001d44005002100140c04030340081d00e001c076444000f480c101d8180340802c211007544641c04100d4480c4050001095402c0724043c60601c561588480b43d11030783d9210848010650394406004900030b5442004c81c042c030140a07101c00c0b9003080e01ca46800c2d06140d090b10b016400a034001c41c080340c118103244902030308084641400303003091156804454980c002d0303100c1c03641440008501c6105e00d44210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 12111616 1250 12110366 12110377
    0xb130201350c07120305060a14030102040b030a0b09090105070903150209120106051203030f01030f0201170408040302010305070c0c0603020f04210507050108100b09010507060e010519060b0f030403020102 90
    0x18030040721034030b0a69180d44075500301c000c0940d204011031300c0b0050024004d201d141d00941c400b6201c41421800c01c00002001e00c0c40044003a0550b41c01c000004052003010040c600441c074649010540188c2c0c8003c000d880200540340001c036926010074030180d0754108004200300d9034030460ba960036072100c2c2d4621000740628586541c0202c01421540c4017068103520942c02c0d10000c1f079038041400f082e51070301d60352400108c3d80c0006148049006102040b0b807081d4044c2010f00c145080c407200400030300e0101d1391601c1034030700300c400940c040f600b8000c40d80c141c01000d41c0100307280780a40517010980c888010401c0b00348540c03030505a000400a0385243c204046074040d0140c0058441109082c603050800d60394030141c01e0302c890042030b0700840c4661041d4101401880341c00d42c0c1c0c41903103080602c001010390003980107078140002000442d0018905024400c41041010300000c0e072844c01040044680c540110304600d00e41c5022800d11a07074298000b61603450480c040785980780d5846281c16070091060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 12112866 1250 12111616 12111707
    0x3040b07050403201302040e01120c0503070608040203100506090f1008030703020601031401060602070b0d0609051602010b101d0604090204030803011e030803010302010509010c0206030c04030b130201 88
    0x1160400c1d0100344458401e004c0140e001c1d40c21030542c510054454003280650b00580c0301482d03904004000c03102041c44c1c100152030007503881c0c6411a6440c1c0000340741c1106ca902c0a800b0074000400c0006500e0180a4000788400c5604244420700d003480000f903209e00010408000e080c99400460b803600c105640c000c1c00b0703066407802c503540c0300140c0c00e000e55550401d101c22228403541c1411080d80000601461045510603001041618100514541c0c00d81041d06900007603966003100164032241406a1802011550f11007802c600840800909442025020318011110114540039095000c00c1c80c00198503c4428141c10100920000d5481e110300d0f40291081030000c5004020f06c10030354000c0d0304a60042c1c11300007402d02d400c0750106d85020540b10141007140103000410255000e8401071840c2c3d4070504d0004c12144c2c6a0340060042d410035165442c24540200d000c2c010441c44800c1c00f500240c2e200c0600d0754031016540001c1211941014480b80c10401e401f06540716a840400101484ca0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 12114116 1250 12112866 12112883
    0x50c120a02010b09060f0105071202030c0d0309020102010e0a080412030207031b061d010206010b0906130305010b01020d050906040504020c0a05010903080f06010305040c060e010c050f0322060503040b07050403 92
    0x6100d50002d020b894403100303151058404501081d40c0346002d820543e080131043e100d5500b41569900c86507500010031009a00754001001005055803091010700c445150503100003031001150b0000a00b10350781505440c846074007100400b000702c0c50305020741d0221800300c11705c081d90744c6091a00306e00741800d9900041805021080c15280000c03814440000e41e03c890740c07403560407003004101080c410072150a15025801400c0107020050f100ba0051400c3c100c050600c03490840d8034021004460b0b8940d00c195096550340321380344000d41c1d051228550702903551900c6400c240031940010250b105030700c26a441a94001b4039440d200105001032404282c01c03200030003110410342000341c07030010125040c0300f5070b80d210320000301503602a11805000d141c02042d2981d45901b04801619044c03505001e403414000d03281c0304000019003c1012821050703044000e1030b1942d011295600441d032040c050340700e003000c50b01d43c01e1100560101c140da91040d00205010300940310840c040e6540d11454002910226 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 12115366 1250 12114116 12114127
    0xf04150b061204050c06070812040606030f0303060305101a04090515010b0702010e0907080403030c1e02010f0605011103070b13021f020609010506010f140d0507020706021203070f050c12 82
    0x5142d1034080c440da0052054440352050305040000510032800d0042241c9018413003907804040845145a000b80b04080c001005500c985560001c0d4004000490000791144018010010107003d40b002c4859500310500c10490045480100c8107151080280a02c0e901d04080c02442810060044101040350b003480711943c6400002c0391a9000d4030f41640410100c45810116042021220f845030026540d81500d50300c456504402a10f16815004100502c01c5103040080401140d0302c07075400555000015241742d0001c210003541c1440c1d01150511188204400c0c5c0e0b28400300480702040d40c4400700d28203503030700e442001001840100000c0d400600152901300606200b02c074000010600350212a015980c22000e01e00b0b9880481b20030707000651790100c41e90464000c140d1241d050340400c2040e8100300320041d507001116801ca410600503440004c007004900d40600059034400c0c40ea0050600d5454440c801a05c03408219080b41d00f048400240c3c182800b200740b0a041100030240c6c910703030350380707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 12116616 1250 12115366 12115387
    0x90408070501050606030606031302030a02090907050118030206030403210f05060f0409080d021b06150a08060702070b031512070f05120606040506030f01060803030403080705030f04150b06 83
    0x64004800481d80c640c6040041a03140c03500c00d0590780b00d0000185403500e1031303070b541d28041c0000b0040d00080341c0510400e6289030040e607449003858428000d6000520244d441d01c1c000500f0300086000040c40d0a80524091001d41c0303e031400c40f0b80c45a05401c001124440390071040c0040c000d441c8000c4400d9141244004000c1d5181c2c21040c0600c01c00c441d14014503590204110032150040d0004004007001c0120b914648042d401400c1c4100c102c4050301c1510000700d043c0c9080030301c1154142d19503042c0290302c6010345801d200c60000307807080d40c0c01042c05150054000c0d40e1080070380500c20b40304070302000040185030680c0900d044a4005890500100c035003c01c1c0310342da00c083c0c0c0218041c150021030046080c0c1084a2840e02c0c0c403040000400705a150ba0050200401d0050192a014040c0c20300c06a24100c0074041d000040815900540d500d02d070904006190440261406080280400500c0030016040c5403003900250000c026510092005500b030f07004040c0c03280120780200000c00c024660303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 12117866 1250 12116616 12116633
    0x2060901020715020a0605090303060102071703070206040f1a12010911070609060c02120a0504090902010e03120706321f08060a0b010302040302031b0402070609050105090f0f070501050f090904 85
    0x4140c03041b80b0900c1240c4480185540b24042101c40e41d0050780001401c0000e0864031103000314110229041d40d160a000d500400c1c11036006800c014501c4629541c1040040003035620060f142d8407011115003030030f40c0d245e04840c03000c4c0e062040485094032020440c04944480e42210a40340d4405c80401c92403085240500281502542c2c217030250084103180c20b42107480d60112240c422195841c1e92a150030070060500800c04000168100500d4040106075a1010080100b00c2c6c0503001c091500c840f52440d0040968a0000700350580e1000006000d4400d611000d80c50303c8025852000030040d601c2c1e401c04044200c107003903014603440812000180000d80440c0c241d00506245a01344100c1841c4401034050340b0840c40000e4140e8820420f4000164040946001040340100b0240c07400200b925503400356943e4500540350303a55114140034450344100601c0b0b413101401005043d010311402c1c011916105c1078415141807240005104885036100030484e82c4000000389104c0329030400381010f807503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 12119116 1250 12117866 12117883
    0xa0b0307170c25020f0109050109091a040e060f0a0212010603050403020f0607110c09040503040b030c0705030415030509060613090303061211030f030f0702060a02150103080c0705010903020303070206090102071502 94
    0xa410050850170b00354403e5180d4400c2e40c0d8180c49040025180030101d0001300f4107070682c001540c401c1440c100c1c46a546003d2007250804500c000e01082c00c01d00105801d840002d42012001481084007100c525100c00b40c490440e18a030030009040e5540b410245e08041401000b40350301d004940800442e01d030000c08900d10071441e5401c07501158005400d00c40700e0142030b100944903034402e00013048640841e000a6901600805840c2c0c01e101d1181c0c0d899280d90072540104000361103407078160703041d16854881c141c3c0c07103c0d441d0f00030501e81c18690040f07208a03030807000c505e540d152038058a506140c000d0300000c0c020300301c01d00008109401800d04081010303400c0400c61090144560f203001d540b80010a84004284c0f2386903007071500c4069420480300e0fa001c0b15101e13040d80036600d0000f0102c2c0b00280303a01e0081d8012031211b40e551078414002818084150046414410602000e20242e01d0020a40e680340d0f5060700c1c0650384a403044010b03071070505550311260024011724042248294045100304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 12120366 1250 12119116 12119119
    0xd06060801051812030412090815012c0103020103020306010e0904050c030f0a050c100c080c0607030b010309080306060d0b0d081305041b0f090b040b0403020a0b0307170c2502 77
    0x9002607800c0c3c040c81d881d6180f240f2443d802400500c040780114241c1c0c140310304101e0035800c10b4414a0b030b8540a0a06000400000007010790346e00700100708100c8800d0b84e00749825841c443c260200c0b040c0340c100300a50a0107010190406074080001032069018030721060301c0c41d03001090230281e0310300b80c07402c0e560310452886000e000e4000c11a00400078180014241581c580c0130b805031005003178000502c004d888000d4003c200300170810780c500b00440e00c081c00410b8214842d001400305480c00100c058140d07480082030504040ca4481c00d40085200d002c290ba805ca102120b5440da90090042c05102070017004040301ea011480b1003c0c0d40401c40c0244c000c000710214071210120301d5560f10104004c54a0f540000c00c0302c0604141d180d1100b42c40f072103048031050407d040683c07186450388030210264200b500320913814600001c09105500d002c0d00c1000c01044030030741680c51481c0500c00181803005c846c8080d0301c1d44130f0071340100b40c0520f542c0087d200401004400c02d10500320b5072044290b282e48001041e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 12121616 1250 12120366 12120391
    0x40b0d060f0612021003020307030f02040303030c020f0304060f030203060301090503120a1b050706090201030608011a0a0b0a09051c020d1a07020601060e0d0203010b090109060807120507030602090d0606080105 92
    0x20302181e050015443c500c0c0c0082c07101005020904058020b540f00a05107002c00d651403089007208000c070301c040e0001d54081c0e900022043c00581c0301030b190401c1c1c00460285175006010810085611038032100d0104124074016031240c0310f0714042400b400709508010028040030858010300102c407034000b48a11580901400141d080d10403103031070040e44003509000508104100c40220f003094000c039001520600d00010300d01d40e2000328a08480c02e08004042841001451500c10f00d400e004640203840c4c405c60321785c41d1600000002e80311307482a103e554087c50b0302040c13050342800300c03071000041c0d25005040105180304a280614400401c07090000b052084c010109503000d20000d0054180c1e100d5444031611504100c0812042480d181da041b0303415034880c05000d2960300c0340580140204a0b400b0b010503150304000143d03061883c3d980045547e140da0072a1000415000200c0d10100e941207400180d0f00d90000c00401c10007445440060314807810168002804401540858410a80321800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 12122866 1250 12121616 12121619
    0x12041b06050705060402012a200103020301080d11030403050d0504060f020c09060108060a170f070501080f010506071104090507030b0109060b0403080904021605011406060304030206070806040b0d060f06 89
    0x2501c0c64021402d01408a038031110020f0015402521031401c90088450140380d510451080c0303861001c01d980d02120441440000c008204115285420030f200c0242020b50031036051004803603660443d000703201d0400501450b01d1101d032905000b114013139a08030090340c400001c0c40c500641207a1181c440d100c00100074941c4030071300901c040b65001c40c518000303025038034a4560500444032100d01802c0740d64444142100059000b4615001c000c4d000b540b00040c0540c40c024844043c1450001e500090500c4074074000c1010311400c0000f0305064610440708517481c0c80d1941445840c800400c62841e80147c9000c0c1035106001c0300092860031a442400c04440c50303038841600f0f1086d0b5040c3c0c0700340d6003012001c4c8403d20015400b030010b0000d2190142c00141000400240d0500707540c102101074465954881480340703007444080d80c0c01d90100b02951090b2035800d00740e60081d56110020402e40811042c80089051541d0b2500308000032140106400306090b003d080210052000200301c1c0d840a03e000c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 12124116 1250 12122866 12122879
    0x3030207051002060a2a0903021906050a14160503030a0f0e0c01050f090901030311010e06070e21030301090c0908060702070b030c070b1603180c05010f020312041b 72
    0x4890300e203030882c0d0203020a521a540e6000c061b0076520004210540d5008070305680719200c01e0310048100443c0c0ea42c0e4845072450040c082e009a07103102110450400e0704c81409955001011503281081e1480e14680c52a0b082c4c0503101a4002d070344640d80302d00003104040c000d00c4000005540644003049007000356400e109003a00c00ca80c0344403003500c3c0c0d5400c4540e088107198060030141800107000d009031858602d000303000407800c0200343c00481c0070800007416020b42136003d01c1803800d000880f2004020394242000c010304058800e44d142ca01c0f800c0241034519082c1c070844651800078240c43d0450b0f0312547c45040000140a00e210398000150f030030800000d69003070010740b00d8080e0070140c0262a1450130040c8400182d88014045291048204104000a05419003da110700140744181c100c00050140090507a140703060044004000000003e0120701e4003011030044600034284112905081c0c442641980100098800501c000c40c040009202c0c28003514001c6200f01da03401c0010686518 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 12125366 1250 12124116 12124129
    0xc04050603070c0201021b0108010b0c0a080307030c0906030c05040e091504050d020118021302030c0c0304180501150806060903012304060b01050301080d031d1b040b060705120d140906010303020705 87
    0x1f4480d00258080004110050000000303044001181003661060042c03600d640b441d07948140c13694000207907100e40100c01294000051009000540750a00c03880140f82070050281c000c900812404140400100d50048820405d012540780d8100c1e510200c1d00e000c1c02d107283c070790b1401c0300100c02550a0010b000003ca26000c004072900f41e0051080c5d82890f175081041c002500014990550080e0410840c8a402000c0015000610346900780d03842d0524040b000707006403030042c2d01803074100c00031119114070b01d9000192194003500940d0015102c00305040000e02410110b643d810302890803034040b52106884194252107a07001300c6050007155050001191148024072071a0750ba50000070303900404610a80294031a504056000d19155402506450400307403107295010400b81040d2030240c06040a0140b2000b60f001101c1044c1030142644035203456081d86542c0808070500007074111691001c1c1d038003040c07092461009411051811890041d40e541003070100b500540304101c0300094515200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 12126616 1250 12125366 12125413
    0xe03040518070302070c0806060103060f060219020f0604260d0507030509040b06030702100f05010b0715060902120103030e0312040e041110030213050609030601030b0c04050603070c020102 83
    0x1d848804001500780240c41c1141c000307030218003015020042c003408950b01c505031001030141600a040305040c2080050202e814543c4002e0301800030b400100440c0d0340110301c04a601c2c07800c209281d401c0f11584002040082e0019059a000f03101180108207584099001c80040c40c24070b180c000400c035940348882d0380d240c0403812280040d008200c16400a48900e011b00850003010703202061200352100090030396001200d8040c010780c840e40103040f0b441c2c02401000e004045400c002c100950411114081510880381d000e0311110000e09400c040c4289a4040d90013004180c001715114901c03100c0040e0030300320a2200364000384180d00e0740030081c600865055003440c08800d040d0714061403d81500c031000d400030000d640301500d40c0d441c401562506a201c00045882d035400503600c01281d06102d02c0003260760009400b0b96414004c0200e142c8000402c1c0e410b51360018918282d6540e00d03c0c0b4a11103200f950805c030340040c0b002c010b11800a401030200302480e4400d80942c0e40303030480c01c02070f000040200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 12127866 1250 12126616 12126619
    0xc051b0c0306011a04030c0909060c0309050d0f09090911120c06070b040302031204060501050a0e090a03050c03130f090f02070c061101090501020304050c0109080601180f020403050d08010501030e030405 89
    0x3100400000c21104d2100c100700c44660401c07814103a17a602c60300f03091031041e400805541d8440c00c0c4481000784c144915809500395040810050440344c4440e40c1d68400926101c0c140704124070b4060107140542c01500040c02c4680051009030268600b200707181c02003441590142590780003840201501042c044060b1102500150070305099803203103025540041d00590550000b0894450501a516061403042d0700600f80071032554541000d0150b0719030030740d010306216848601404426800401c04070011901441e004e0f03114030003449524154840c040d441000c900101c5400a200780c00d100307001007107400e0354004001205c1c80c0c910801c26441203040c02071030107524240070f21820380140c800c001004520000003c0c3c6108503503071135089034000d03202600c80da800f00003814050740e4054008000381150314007504180d40b401c0c25200d800500b00600519064441400304030f013a03883c5d81a100110f800034110341d080907039500f02400d008020b0164600103070a10300aa84105800811101200d0f030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 12129116 1250 12127866 12127873
    0x80a0f140706090206040e0718050105090303030408091504090c1206080a0303050a060902040306020d1802010c03110a0605010303030c09051e040207020402040f0305100507021506100908010c051b0c03 88
    0x940c1e680300b10080c149858100d034403034028400801c0f2140c0c1721242e00d00c9001c0584801083d100d8803008030a040c1242d90180341040010040d507880b80c0c80c04400e50b5001075000c0c1501d1340301c254607000607043ea030b18100090160308011600003088843c0e50010b410454158850522502c815541d00741518064003420b12580c3c070680b0b0000003e4401d60011707510400c0310500182c079644650241007680d0003644141c0b6107076000308100003c40040d10601c1c44031291010390042c04031469001a00c00b030403184025080c4100304a1055034558180f2400c003030243c0c0701b2010895503071640f901078014800e07280014005090b5520224aa080159000e180c401403842c41c40c0c0c04040400411020b90b1140300c3c1280c0041e0280300c000740c5000050208406148594050424101841042c000f02d40004000c603045500090308102d40c10785c01d01d10283c12080c251814110384488000940303c07000d00d039010a0300c643c60507108150b4942c0c000064a00c2c00380031001400101200c00080350b4070f10008500310b90640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 12130366 1250 12129116 12129127
    0x6050702060310050a0f2d051903020303070c150206011a090f030a060b090f0610030c0302120115110610090b01020a1b060e121c020c0409080a0f14 65
    0x2500d280916403040400c40c000c4990f0b0307110400310385242c1071948200301004c5841c030107010000d0611440345d11400d02c01c5500880017480f064a0710001818820325020342c04000c44148080c0c4070042001c0510b4020b401c07603540380c1a92800b210040e603140f0580011922483c0c030050028804a010350480b44107044841c0ca41c0000090701c5c20740d510000c400b55010340c2c0340c000f010954405010400d00c01c1e02444c00022a020050240080c3c032000418030700080b45001c2c00c001065444200201e40101d0500c6d0015601c0c0c08039109078000d2040c1644141c090f800034000240d070740064070f0381e1848540c1c00d981350300f0343c00510440076503205400d58001011800440090110302520380c0883c500032814811902c00311030300d4840410300c4090340005e4107486610030042c030075181c2201000e4000142030355555011510002401d448894901981100481755032010300550303c200b102c0c0112600c01081084000e080b40303000c00107580216041004030703032148402c50005006800c020400141c06510070304d000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 12131616 1250 12130366 12130369
    0x20c060601031802030703050a03111204060c0206040b0d0903020c010513140307170705090105010f050904050421030b0906270901061d070909020306060708070609080f03040b0f0106050702 83
    0xc0c00306880f1001c0c1c07403268030100009690100041e000a43c003c1014108041d0641801050503500704141101ca40c4111020103540c0000d0741258101e40325858542440e0010380300061844c45940d00c004410071000c60410705c408650fa0118010500c26003c0300e010104100054550780140181c8188500000e071007044030548003a03003c0c80e503a0008099038031403511412000c244400401c014411540484170034803160602600b86405082c0900b8000c01d6469183c00080c020701c1580f81040c01a529840450100040c0c0809100703c24020010541c0491004400400a01420002600c192401d0000c1611801d04400750782e100c062a110708040458000e14880700701c240509000030540d40d900000907000505081c000c64021404808022802d0401005000440319046090718a2042040c4130155544408407400c41e075101c160b4030380301d180030305144004004154015244400c002001c070185a450070080d403003288550718281c107d40740c10200c21440c80c024051100411001c00924015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 12132866 1250 12131616 12131621
    0xc0909060301020c010c020f0c0604050a030303020d0605030304090c020c0f06030106050304150f050609060405010b0912032118030306030a03121805070f1e050105070c09061805060301020c06060103 87
    0x2400c0600050304e822140103000d070840c1c0060a410005801c031790100d02010800740001d031009070084810318182814a00000c00008581c44004d051690001d00850020381c0f07034000500408009003170f691296550203c45001d2319007039406a005009120240f0713201e140001c0c0e11103510902404072810740e800c2c40350075500c50344082c000b950f02048100780c829804449000b11381d40c200241d100071035a030805c10144191480054aaa4440c1e400c2000520110f411407040d1100540202d0b24400240217410081d070841c0314001f502000d511286044100415030502803030b00850464600500c07291044114079142d0100345d407030070790682003944400d01091180300d18901000342207000085c100f0b03d4111a644224000200701c4068128000400401120312111001843c09403502191000b99510705500b82d206400750382d040c04000726014040c002c52074024409004407442c01c00080c0d03100e07441c1e03802010705c1000054645042800207812818180250f5407251081c2c002003082c0e45810380150003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 12134116 1250 12132866 12132871
    0x204080a02010e1306120209070c02030c0411040b0c0c030c0105040602030904050a14040b0106020d0f020a02100507150506040c110606040902040e010c0c110a051c0302010f02030415060e0c0909 85
    0x91210515131105403010031032003200010720440b44203c07174041131441480b040a034020031503018411000031072405a00c0c042040710920008036400100f22a001200300c45c140515044000c050101003480741c0e0755800001d1460b001e0f64124200d0345204403074001190b0a1003240200d50040e082031161aa403400c1c0b0b50866070f0000d1010201042109402c3d81c4109644401c880959128056400412009070140050b41c020281d07841c00320b95000e6614000b030350740d10b01070341d00901580c2c4404284800341c0c4135a0541d003803260f10000c491751039540c6100440c064041907038040d20403858240c5a050440c056000080d02421701d4010b0400e0356036103c10040208135850007640c12985500c03e05502d1002032144001e10345980e00e50201096260515130f8503c103003221440c1c080e100314a414086a6902c2100010700c010b482414111000980350032405040442c201a4107907002005020400c84101070307444240001d14020002d041da90201c001c103140c8251005808440b082101d0f81550401d00c00055 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 12135366 1250 12134116 12134119
    0x9040f1709060c030702010f14070201110a0b04051f020304030905090a0b04020d06061206062001021608070506070215060d0609080307050304020901060e06030c0304020315040b01080f010204080a02010e 89
    0x40c108408003010a40c154803030f0340401c01030340002071001c0440da085904200054a913140c0841540c185802e91036aa03c569580030707060200b107100c0540d40c2002040148500f41e80f005198505040c10319000307560b56520362120200500a650100003441c0b5071081e6841543c0690b10710702c980b1b00d45424083c9500003c2e045540158542c2010300b01916580000c05c100c9000c41c0d40007800710f01e440c0b8010503600e42408400265802c1c95020040b50f58400c158041e818509810300d60b503102d038121a2402441107400300d900c180380f0b2030100c405009400b800740c013040e4040d10039108550f0f17421104030b89840c0c040d6007010313000710944040742c0f047c00c0c6400e2810600e407090900103a50f000fa07450300981e603002140c2c5900014000000c200c21414440d40c85401851f550802d09600505000010190701005042a81c0340710302000003020355404004206900c0c100e0100071001d03041c1818881140e444c24050f001c0c25109002d0017400d26001442203504480092001e0700c886070300d40d030044500082c01d52446 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 12136616 1250 12135366 12135413
    0x402030a0204090308070f020c030d0813050a030314090606031b0301140a050711060405060103020d0809060d0509071403100914070b0d0606210c02030d0f0b0301060509040f 76
    0x10001070b11184903020340c06000f500c401002d441c1c4580018913030310b00080001708640084820418030340703002981e0724007142c840c140000c0355a207816521001381d200071000b400b9031040c02d0380f080c00d054140e48480308801030300140c140d2a40c1d8589409076900010380b10990552b102c0c0c020303038020503940014148e072600c0c02800030a5150881c0c0744101f10a43c140c3d000c0300135907502d1040c4000b40740c12034141c42501d83e000019122603d0729071241741d10340c04144400b80c0a01850b6603140b0400185c00b0468801d003030000c22031600c0e200201004c0c1c00130076085601c0c00061050100204103242c0d0b21303a841a00001c020018a61002c0031003459014181c01c020440c0c9140031002050041002440b0040140400040b030548034a411245103041d01c070300f03500404c10f102e182c8400c071000e050f006001e0040301640420100d03444600060803861817040001c0c0c9000c0314644940405c160200d5002080402c00840003400269103500401c03401c04020303100100b000a5032042ca00000c1c2c440c0141032041041046036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 12137866 1250 12136616 12136633
    0x309030b060406081b130204030605060319051504050c040903030203040b01080303090c060904020405040e0303070f0518010302070309030206161a0105030d1808030721020604080412080417070e0106020105060a030308040203 98
    0x6d000580e0010b40084030a1a101c2c400c110f80e40c03c0c1003110060400606198203d005000e890307141d00c40c0710480001e15084803400000b01440410031074080170b480e0241c002c01c854a02400d00030000c1d041607404448440880300002200ca00c0041a01e004158580c040d0146080e40070402c102a800440069006502407000040c90b035543d12602006820030000303951740b03151822000708080441440b0205002040c4921400542000f140b100e90807c2800c0042c7d075065141426506d950f4268402584003c2c0082c2000e03019421443d4050058421200301010300d12145d130003c030228090040c035425502c40184d403910140318032015140d600e220b201104459031070b0f90080d411a480201c090382d101180d54009002d54a09188004a0014500c00b900b0f503420959a00c00700c030b2095220381024a100082d82100348040601110b00420300202c11030b98003185116000e03195030a0313200d41003c005035840005600390040c06268481c80d402172040d825a402c50b030b0107555003840500140c4c0c251180950 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 12139116 1250 12137866 12137899
    0x103020d0b0a031a090604030c020d030522090c03050103050d03090807050601030506060108090a020d060509010b06030a060e060a030f120306030807060b0307080f03030c0a02030c0a0309030b060406081b 89
    0xc202c05540610440d220003448a0303c0c004007020090020702d8903034002000c10001c40d1703109210300c0a40384c1c102e90841c51099641422500d80c01100c040610044400942c031000e07003ca0012202110380710758040c07109000250b001d0b0111030b030911018005400c4145c8090415200e5408001e186114401240c00c10256840302131402c0700c241c10460b42c5500040a0060707543e0466001503011800d0001013064061944c08200c1521090300000d1000e40c90300d001c103640314000c0d0440b06100f60042d111b42e0712841c0c201c0086d00500400d106150703101070b03040046022410141451002c0d00d8200b896101c8101e0300b41d4500101c502c85c0d0541c282007680d542c0c00880022003030b02c024183da5000c1c020108201340c00608041c00e05444c2d40c0010016030106410280c440b0021040d40e038411709040c0095200c5441403400d0b070940c8901200007005004800000c0d00705900900d650095034002c2c3c0400501d9130341c56060004840c0d1030b00070900c10340d010080c403030805800c010089410b510040d0402c10486050903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 12140366 1250 12139116 12139129
    0x1401090b2101051009020702060703030f1805060103060f050c04180609090f0b09010506010c08090f0306010807060306150504050906010207090518120f040e100b040609060e0109140103020d0b 84
    0x24084800d60b51200c040c41a500c5003c000b440c05041904c408614012448d800079603144503140c1c00806254680d03820184000c080d41c071200d150442d41e0380d04904000a4503006440d817000b4001110941e1400c41d074131610108134070541d1302c6003032500c64882c940340c2090034070800c503441e012056034000e031903000101c0c801c681401440e0141d03105000c000b9941c11075213001d4004420003004050107a15040030020b1701d82e030046001c00c420360803517591645c0d00c4000c0041820030a41c403040c543c041c40350400018150000050045c01c94400d40d40c01c01c580b0741c0b10380600c03040900565501002820521052040e840d02e4540b440d0070020500484922541d540003100c01d54808590044070905504183c0b8070400341070000c03000c1c140100d2401443c042440f4249141c1d40201c0c014080301e14070440014004001143d07009010748007940c4201e403941da981c84000c20a018030301400e0002000d07402910071550107920742400b9140e90302000500302070310900460003500603080728100a030300c4207101d0b100b603251034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 12141616 1250 12140366 12140419
    0xc01020f03011409070905190308030403020d020d03060501140c010e010905010e0705060f040312050d050c030402040606020a1505070302071b0e1305060a0b01111603020906041401090b 81
    0x1060355071a5803404106480c00c02e480169a4000c038a00c00030404440e42c0108010152407044844140c0340c0c1c90a0307000aa55401608010180304000090200f4140c00045407003800d00d99501311901c250754244120181c0340700788030b128081074031003441184d42e001c1003000e01505002c0308000108100352540d401d003944c04516041d55665941e211843c5070000a000c081e014000a8a6061501150b503200030010310807480060b08551031100500e0700c00340300c0c00803258a15441d81c0c0501aa003032011074290503a005a500700e101e24030b400e0000a141d80081940450030381c02c00001c201c3e0303448202052015000c0189a10b040580c01c10000c80010700c0d019010043c3c86596200c00070003400c2902142c480d500c0a008440c1c401c61035002400000e10009600d50700c6044884003042d0745c00c0100059030f03020380c0c00b0011032840c00340c03120041e120114646031100b05da00886241c000c60b182c0005000850381c0c14008000b68404110050015007419084400352544c0a003040c3c0200354071000d0200f840503003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 12142866 1250 12141616 12141637
    0xe1003141f0b090a03020d08070206040303030b0405060a05100305070201061806030506060102060c0a0315030b0c030601140f04050d05070b0a09090b010201020406050904050601030f0203070c020102100e060402060d020c0102 98
    0x81041c4400e00d07011409000340a0a107140a0524014a007000601c3d055590310009110b040565417020030000e03500706480310a5405042551100c0d281d190160140c50040501c2d4026458003001510318540842507504607000601200d90401c0080c80840c0034000041002c000e540d00c4020000f61300c8201c01003269510b082d0400003500e1411403a19904041015100c81e0440d4002401c0c042e0b031545440440313405404074140024903202100310401c003040c45500103004c1c1e81c2c0103010040241000e10045110318000da881c64120001d141249040d0b010b500441203007044140010b1285081100281c0c01d080c2c0074000300e88103644c0c4c45000c1060340c0d10020780c540018450444c1040000c149024401070b21909000a60500d03040a000401501074400c0f02031080d030702e440100d03240e6402a4401d54264803c200c00355500e140030403016010381d0922800308e006204440d103103001800346118105e00300b52060050301c0305071110340811119810014a0104c025420840311402c040e0034030040ca0310b281c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 12144116 1250 12142866 12142891
    0x90f090a09060f0e0606060706060f06120e060103111002030c01020c0102040302011803150f18080c070603060b0a0809120403030314070206100e090309030102040b0403140304060e100314 82
    0x20700d24144040e6815241c501d03208505140c00d16107002008203015a001000b81e504580300d105508041e00600700e59440300320b007101000004100782d94041002c4602980c641c0050000f11480001d6980d60707130092002500d512510388505020b490f124a21000000342841240c0c1071680c29901242245d01404131209141c0d40001c0c01c00c01c650b040350522448034035410403400250f01d1510f035107004040045000292540d10381c40d8525600b0b1581c4001d45070078001c00d0004405980b07241c0010168440c904080180c880c4000014000380304e40074000a44002c0404e4609000300c954040e9040c2e00060140c03015402001aa030000d0f00250b800b410096019590100b450107036080c20300310114000d000c280031074006c4020401c044020200c080d0444a419901d10000e86e280c00f150345c00c6000d02403c042c1d16500000b80010210b2001002e0030a0324020011601d5001c500d0046030b58901c902c0c42280f0104110390740242451400c2d2a04c080100411704002c90303100040204038500c07241c11170f0750200019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 12145366 1250 12144116 12144131
    0x80f04030c0f080c0103050a1404050a05011802030c06070507030f0b010e01120f020f0111030a0305060f0402040302011403040f0204020714010e010509190507090c08090c0d030507020105090f090a 86
    0x101103034494028104036140c2102c80d818005003e03101c0d518018024141a1120041802c00c1002d6020142e80340140d42c20a503642000d01d401380d140c0803440c9064400b907080070f005142c0214511109040c86600a000f0800e510441c0c05006c00d03500500b00c05e40303160241107400004290852901d010700c9c7d100c3c0c02482c0f41981803e135041c1d80710006030880e0f40c648040f4aa468000b5801c80c2c04a09423076011550b61031030500c41e10040301c0c210445803190815010108000340000d03010f401050042d60100c0e0203542c043c184a040c40201c1c0500d21001e030009407804e00003540f64450800840c2c00500030108034070f043c043d64001c242641c0c41701000302e03400c0b0380c590b1500307070641350a01c240c0014185c0a0000d01181c1013002c4034542d1000c244070a0040820034020303407410864100803820040188040c180200142c1c80001742c03102c03404070f8520f00c49005441c5684c14a1601d402d007800e1507941915021304000c42e603001142c06820400050360020058003036560540d5400503000c2c42000c14000215202 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 12146616 1250 12145366 12145373
    0x4050406150b040602150103020a0b031503100c020601080d020a08030705210a0525050a0e030106080f06160f03020a020a0203070e0a0b030703050604020d021f050409050c0c0604080a02030403080f0403 88
    0x81406e04940c240900807001800141e495003d0001154035102c00036449443c1c11604084500e80e45c81055410300c1aa10317540001040b039041480d105590b5000d0b52020381c0c6e210405030711201c0440b03998005030404550700001030fa240f8051a00502e15180c00760421500b5842e1620952a0250030b001100000c17080001901c400d00402d9408a5883c628403e04145400d1000321401d01482d048240440031464040c0680316a440c161400ea0080c0284081c07540c1d418115150b90f0030078085075080c09103000260030001040b00c515148030840d40d072803000e03500c1400120001d4001150743c030114003c0242a1026035420040c280150a0000007401c0a05026440c1d000315000c2562541c001d40245a040022039804503503554069015190241800340780d1001811b40c0080da0381820f051100000e050316100c2d40b00010700b090303035289a010485a11000141c0a4500990b05005110391001c400100014945400741c0b00d607120900440f0b0415449643d646c045405c131544e80240100c0119080050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 12147866 1250 12146616 12146623
    0x80d0203040e09030702010212090d020607060204050405011e05010c020a0302212103040b0406090f0506010315090f11040f11070203100203010806040611070b13020a061107030204050406150b040602 87
    0x2c44440000c510301704507580003035100e0781e1111200360801d002044010f420340710702d861550032641c01005595909450b142500080d0014020306004514120002c0390110001c041700c0d803001101c0b14041c01107490b15004458501d9021402ca8020000000c0040140c075401c1d0043c03d000440054503805480000107c2d14200c1c030b030352455202031128951800034010f404126500641c02030022051540c81d400c003080030740051407004080c202c1007100d20342070000c08118103068920510a4500c08511458503d0998545103c00f410201180103542e0001c0d21050301d02d064800068070119009942d410342504680d0036900e03002c02c1c1400080c00d00c0441c80c0c140f08440e0311060080381141194103080b000d41d514540100014031180d5a11040245140d0580a90702e049030b104034418014038254003608400c0b68410340c100d001d00a145400f01d800c074040c1c81c3c1c040704441c6400080c02400d00e0340c1c08020181001400980314180c4d0307030151700d00c06401204c122001d0402e100c42281e80c0c0d883d0810003840c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 12149116 1250 12147866 12147871
    0x501020705010b01020c0d080c07030b041511090a0e0a06030f0302030c060f0f06040f0b03010204060e03060c0c0705010c05010e03030c0d0e010903021c0e03060103081c020c070302061b0607030e070504020c03030705070c080d0203040e 102
    0x80900d81000780310703220361f103188011e02990030340c000320003a55a40a4240c00144069000542403940071141ca03c2010f034004000c00310a54044195603040d107803c03520a2100e2019508078101282c12000039281307052aa01c4428030010810020440481c11408a0b0032603105401003400a81c0440d1080001c0c10100b1505821280d40b0300c038545020405506d40e902c0ba9114015181000f83c1c2440e100217015003500310100e86a0400280d0340e0784d00b021880000142e11000a90301020700b420300d0850300080601c510b500d9642c0680103444007034071440e41c00c202c0d520103101309020312650710107000342a00c0c2000160302951007070b8100c5607640108100220b88040ca0302c0c1d02c5001c14010003200c0100e00c8042007490440c0e5041c0c0d0410745130700098140703205e40309801e0100166403041d03a040141266260b00050315001d00401a1001c0036207807c140805d9210702210010543c1c41040801c945a1040780103020726402454454101c2e900c82c0d110302c3c00c00c18500700e0703c0c0050307201007428454240c40d541d00c0354 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 12150366 1250 12149116 12149141
    0xd020a0f060b0d080409050f0105010c030f0f0302040e010905040b060603041a070c05030c0604060b0409020105040e04060902150a020c0a03030c06050702070504090501020705010b01020c0d080c07030b0415 90
    0x2a416a40e10002541a500c004140d551a6007007030b590364681000a5107096400340320903442d6a2203c90500082500b201ca03c481b5044c45d1000003195401030b03202d01d85064242c0d035211908841e1003401d4642c46440103003141015030070400000c0014400581602a024080011602c0e00f0306003000e90800347c02800d2940301e80c000300213200010b000e10303945050a59840c031152800755140c3c13009850909441d0006030850100081d240400b031004154903220b80e1151408100c05e1002e6402c0c0f008031024180001c2c00b1640411060242100000c2040c0c0c0c02403280802055185159000c51400518040031008404000c00c00701d004980520a0040d06041034903140e0b040d901d1914000c042c00c12032200503051965031000b24400c24402e111402c06810040d000f40465001450028003d40c0407084c10354903540390000e05440c070b6102040c0f030103d101d401448a4142c00e1103403594282ca5210250b10343d0302d032007042800070001b0400000c03d88218003401143e8080c20f500800c050540b2082214034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 12151616 1250 12150366 12150373
    0x4090b0111190f06050906060312041d04170408030a081506040b1612020f0105010f0b0304031409130501050f0a0b0313030c05100c0f020601050a031104140a05090d02 73
    0x200000403000a0890503030112031180019042c65040464680c641e6800140815013001d042201711840000c00c035024550550803503a24441e00d8007010388900540c0504017550310048003000c1c00351343c00980303103070070a0186c052505100c80d92840499282d05c1039220103040d410103d00aa070703e5030450103131a0301c0307064030400c0c4803802d509000003001840303203009071041e030640801d4888080c07004c442c000d41c01a62180e03801c14404117140001e1b50b183c220f41c000312030a608002c0089800441d03c42d1040481305160005400e42e2615035099800074415034908481c52024803100e40d4944c1c5017500c800303201c040b5100c00911541484141701c00c0c04140d941c4980203c01c0c42030708200f03c40c0300c14100e0b035002218040301d0101c460145022910510140310144c0b0130b125441c50711805000d1a032102d201c5a106031100d5036031400004041c2c0e1228824270615a20240030352003040440e1400740a0605445e0040001a49060b280c5d070022525809840040c1e042d0307510020804420000c0202c0d15090501d80000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 12152866 1250 12151616 12151637
    0x6020d030905071a070f20040603020a05010e060c010501122001020d030506130e010b03060609090303040210050c01021309050a0207020a0b0706110d050f070c0b0f0c040b0f04090b01 80
    0xb41c5690345082e11518080c1c50425440e0b280d91001d04003510728150740311045151180741800e0a000040c006900342c0c4030300c0310002030302800385030034411042201d038040c24180045203840019190006070801098005100300b0038900813190030b09c01c2c20301030000417203170200c1d20426040c080000008010004001644801c2064003070380c00207807450800e081851301013103a035200b001007107034880c80300300403006c00d0700349400d000c1c1d074650640210980c55007c1d0220780c03050307880c0320400c040c1503010f441c6800c4541080010501606260301a26242003480c18600d1500b00d0446c801030032680300c1003c2c1802c0704d11203002802019243c0c002c0716000014054254205403198001035101c8845101701a0940c50026003201044001d8000c0c05043c4109103445403500701585100b409081c048808048101c010342c00a051a4003404500810b190880c1c00a8601d0380c842944241510300035100008000c2d040c040003400c10903e5004004280e29204556182c4e231034400041e007550f40000c1c0722418807030003035103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 12154116 1250 12152866 12152873
    0x1050a0203031302030102090319060e0a020a0303030c02031614010c050301080c010c1104090b09060c0304030c03081b0c0106090e071a0d090213020703080a140a0b03150f0106020d0309 81
    0x90740e40108100b124002011000d10000c0d009104514015806001d2010ae01081c0200046044c0605014110500c0001e00070b25819841c3c070000e1300c00030741c050740198003800840c1c460f40c8482070600301401101d140c0388007000d4900c42806c8054040380c1c086402000d5116116003800780c0341018509003005421075050849158442040400341d07810024601d20400038400044401d05100703802810800a150041c1001140303050220b07a0b0904a1007400c01040c8601004422240701c0c50701552a01e10303403411a0340850701514080d00d0800310044800490800c0160100106408581c0d0390002921074584040407040e41e60f6240342d118180c000f44010012285520b520011088800e400d0365520320102202400405007258081d4101d0501100f054074100140e000b852094040c3e160b8403015a07907605070005403032100c1092100801c480001c144c1e41e00580e00a4108010000c043da18020740340d44d51100703511f0088a094246031414001000902d405004910585110389410311004840342c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 12155366 1250 12154116 12154123
    0x3070e090601080c1c060b0a17040506010b07150c0e03010e0106050303070303090510060801140a0c0903170405060f070c0f030f03080601050c03180a06090509040b090312070908060601050a02 84
    0x300b00c000308820005d00c3d5502401c5110b94602c110207410ba040145030340f9450b40303030003a030021140c800210b050b0b150b100d04140d030710080c554030603a444002808540e08003e69030010745c01c018030494901403400000807204603d80101c00300b28003503940703000d003041c045401c160075542035101503d40c0740d141020034421614040110340402d0707050300700030808000915003107141c02c84002120689910b40070b8045950001074000024100b008a00c1c4003c0e03072262818001100c4030100d08201041e0343d00c03820030020f002e031071045017000300710900241046c2d507600200781d40b5130002e40580380c007403030004d52081000b001490541c01740c0700d481d0705040a10708503514505107014003c07015050219290016946a1050048442d4003240700f0070791340c0b11042040c0886a103010a08040d00c0f4141d4a040401c115124a401c0c0d41296401020761802d502c46895600c000702c800380420b11540404c0064551942060191501459560b52808500ca02c1d2013011400c00030050141c50400104001181ca4182d002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 12156616 1250 12155366 12155371
    0x1d0c040f0e06130201020703050d080105010f0e1c0503040b040303090302130908030403050904060f03030309120206090a0201050706090206040305060906010605030705030a05070c17120c0f0301060f0905041103070e09060108 98
    0x40807844074000c3c40d0005030316014265000400c40d1040480700b01c407141e4004466412280b017a21000c101d00c1a0f81c0090303660003e8408480d4101e070801100c12040c103d06034130010030031301a0b0240c92a00ba1200910345c16903101350415008600003802c2001142070006414103078108200782001441416030700c1100e180b002805c080e040103004510030140b0340e0340c0d500c07940c004e29901c1c1000004a581c1d240c00740142040c2101a28003006001c0228030180c00824581e2081401e0380c080d115000b031650055030180c1160308283e50381603a0300e03503005c01a140c400090014601482c000e04952400080b00c83c81c1a00c140c12000c00c02c801072060008090b00101540d801080b00d18001c96556160081140c0840e0254005071012210f0002140040d8401004006003011031031582030366a03800c0300d440203920519208402c004410001088181c4c81024800c120204a00d8100182540c54000500360340110030140390045000003070007965a0002c00c009081c2500340c40c1c98405e45002c400107050740800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 12157866 1250 12156616 12156631
    0x906040501080a140106030902090604050702070b0a02030f0a09032a050f130c0f02070501020f0d05090a1701020301051e03070501050d092a1a031501031d0c040f0e06 73
    0x1070074045520310f401600f19000124031004104140d40c0d50b140d0003405403841480aa01508180c0d0200b01c00d41000d001c0c061044030690005c01c095890a00d0741500da61081051504600003032042200160104c1d0003000f4405040c0d07100c04020f400d50500b000130441da007100003426540010004030700161031409004980003241c2c222080d090260201c0d0702d240d01c2ca0b4003c207566180c0718100011a4101164403020801907084910060310f490042e079540c00003003e900180e501c120000c0002d10b100741d00901d40504060480c0502c0740e59804418220188010340701c203d03940101c018441c0741030185500c5600005000d00380d0b82c2c4141c2a01207529800340b401a203040010014a1401d030780c0c240d4100615440d07000925201a095002405049d1446442034000301c1450040c005905000750317080d00288081c0c0c110052858a490343d103401c485000d02c0101d414161600b60614152000c421000c3c2460505005024503580e080104422200394011080c049464045130040650000075040d902070780 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 12159116 1250 12157866 12157877
    0x1050d2f030919020f09041401060501210506040905071212030506060a03090c1a03011502010b060307031a090a020307080a0c020c04020708090a080312060301020301060f0c0309030b07050714030906040501 90
    0x5900200c0c0ca504103085c21560042030400038841044203000d04130103089040c4000f000505d0303e407001141c050164280040803107505080b40d000d5044507520181d04000002c0002440c410196112828034099071f020040b03040f43c003200340083c0b003070920000480040e503142c200207618060000030b1407401150040400c055035041c10a00b0020310b640320402500b07100c55003140c03041071621b40701e00720761003401803c003042e070015155949640140103d03100703640010582c60440c3e071062001c0b401444c241d0b000034107000c1d00b003006103444d484044080380500299040940d40e447d180001410f078a40103001c96200502e00619442c4d1503901003048a941c600480700560f07148242d041800e030710300444000907030000402c030b400103140d800000140403c0c1d8100c5908010b40c0d9501d0100b500700d000134449c1501054003040440700042c822064584914401d0401c41440f607100d494294005400b20350400200d6030000e004014464000e10034000790403090b000310718124046021801900a40c4240e43c180f20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 12160366 1250 12159116 12159163
    0x50f060d0b100803040902090a080a03080105060f040e040f06050f09060106120f0609020703020d091a0d0e011506121a06030606070b040501051902070201090308030601050d2f0309 79
    0xc05201c02c040040034201c00b125212520303004020000c3d480980901c0c881c071440e034400240001d021801140c2230380c041d12000030a0f8039110a01c85145d10000b0361021100d810040418040301061440340564041d8003c4510121075140c90b508648000d001390518506407802c204205600041040c155032680c42c1201c65241d0245822014100307403c0001003ca04091000c900f104c03459014044143c080c0d803c8502240441c0e1050f100b00281c1d0280d145612007001c40a40703c00f0301d031001000030350500803000692480700084035007110705031001c1041100c21100200a2181c0c000a21b82c0f90180070442080300751444185800081c60343c04059000c1c24010000078560341d40c1805595140c2d130051910807044c54949040350007818210758a800d0048180804054600c2da4400e507100c499041e15149c020b5411a00e41100c0c81e08014815410480b08104138070040e007407070007100c5038400b0501309080e0b4400ca0030f400380e86e4204003d0052550321403d004020070410001001c3e0110580000000c1908 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 12161616 1250 12160366 12160381
    0x30a060b030c0607050f010510030804030201050307210902040e010212130c030807060b01020717030306010804060609020a05070b130203070308030603010609020a05181f080901090f1203050f060d0b 87
    0x40020b203010355000c9800308001c0e00340f08000c0f0b80c0c13050f511240d030000c02c42d6170b441680c203030035a134424040070b420039009000900041d40505d00039904544141402403a02001c0401c0320700145000555552498440301c40508509180c086c042545c85000020750034060000036180f2000f00090483e0b2440b50f02409071000d10085c0c3c0b903110013031500041940c0d80c1e00402d00b4400090140c240c0f0040c018410114002036000d2803055030b20b0242d80c80380155145d0b4403850011554458003510a8030034070355035000040c402200c0e100034500b040b1583c0714540c9542c3c45050000b40c2c5180108200180f561648078100160307000308180d015a9404030b510303a160380340c1e40003003030051a0540100c0071951001425080359608400a0410100c04e03201945e14801000103106500a6844200c5908030f040e15a801d2010f001c3e00410307500203c04800010b08064507194868207a086c07031019242e0702c010210340c10205600d80102c507800108030f044001142000c80c0401d091410052001d49011460004500030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 12162866 1250 12161616 12161623
    0x60504110303030705040f12020607150b130b010e090c07080325030504050c040c1b030203120408040512010504050303060603070215010b19020606060405010e03100c031a01030b030a060b03 83
    0x14030401604498a03441c1007080034081307a10030b0080010500050301d00040f24981001d40c94100d603400f81a850400583e9030703503804281c0f0115040040b25446e40c141501540b60102e60f14900c250028000c191061000005404005100c0c01c2501811900080003446d86a036001c0323a004a61103815a5600d950301c901180d00c5010f0007070b0990400b02129406a02d1603807640086004502903015100c0000d00303501003104072130310f2018481c0403c02201980004620458412660901034016a8075080e820300103200c41d6032040701d088510074800301d42070103281002c070018141c04903042e000304603c0c18581c64550f03803400b0041105e031180e40e00200050300c04e482402024a00541c809608000e961500030f80281904004250400d0303140203841c000c41a88001021401640050180c515041c01c8c0001121040314418074a0340512078802c0c003000103040e500c10406411140d42c4c0c00244941c50301c00e4031030f030480c03000f0016041505060030402240d80220709041c505900450025000c450310000c00d05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 12164116 1250 12162866 12162893
    0x20c1504140915010f170c0a08010b090a030605072f0105010803130b09120105090114060301020406080c070230070506040b0307030f060f080102031911070f081c0b0301050a0612060504 81
    0x11b224030a001440518442440505000309081d201c00356140e0b00da80d21030b1500d000c0c0040740d503070100c0e0300602080070460a80c00b03c2d42001440c9481c094076200420007002ca00012022600341800071580003d5245080c03103401c0c00b42c20124080c61900d8820034940034400c4050050380c3d1000c200081481203540d42d484800209040c98000341b0240c43c008510b0790007844d503d900c64151040a0300050700c42d14041c8202c609480f110b441e015549e48904044070503a400803801280c00a8202003491303100010204076150008411011b00902c9003100c14a50074085150f0020303014920500c014040800c0c8071040ea540610140340000b03800c1648a8403c02500942d071000240c00b40b600d8022600031010f40085204594210b106090482510b55150865091840401d02e020042c4075840000744100c234480540360290480a00309042a8803024403400c1c810b569218481c1e071908010b080c1d040c203014443e48100001d40c1000740c40d290090500e1218104800102540e44d507000080400030003961221 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 12165366 1250 12164116 12164147
    0xa0309020a06020303040302010c03021c0b130e0d02160e010603090c090509070302090c03060901031b1e080f0c1f050408010603080301030506010f031203050403020c1504140915010f 80
    0x1141d541d69500c0a9100e5001b41d905500650034108400c80301d038082c0c0201d40c06c001c514006c402108510f2134000d0020108003a0300c6910181007003d4005100302400b401c0350060f40c1c00c01400d40000007207030107450800554000c101b81c42c0c54101c1001022203150b00981116044e0801040280c2c1624209802008941086d000180b40c4421700c45c00f40e00000c3e08c0310036a0b00c00c2d607601e00161035000c6000c017140001c0301c6c1d031075020f12500c0041c00000e010441c3c0d0000721401105004a0780d8680b03051b031221450003140066120b03c01d000401c1483c5080104002d81314004010f071554080070700201d00c440303030800019040c5555090002c0c086a110300100c070300034071000c070003000300079140c0c5410701e420f6000b88400d40e028441c10b00046481300389445502c088075030100203c2003001c2c1c401000d17009420018002d6040d401078661820407500c52941e82400c15010030069660780d400e1641d00c824000b1031800c05070142001d042000103a5915101403d0111001d082004030010111021a0354180940006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 12166616 1250 12165366 12165379
    0x60e0d0308071e0905100504080604060b060408010e030904050708040317060312030a0504020a21020f0604030f0f02030706020106030c090e121602090601080606030f0603030903012a0203090904080a030902 90
    0xd0003ca50000301d000030340d001142c45044a000d565421500f50049005600c0c4681024011400081095020001c1341001070a0705042c199100c00b204d0860b541e880b01d01d82070341c02c00101d00c619441c082c45000d51003a40382c14000114242030301e000340340000320072a8500465511000c82d509690800903026007500d01e025207a6603103850303203c2d0005003006613822400307002d010b1340c007152100c10b14044100c45c00c0c0b544000f819078051502008a120000b95219410030701c104400700c0890040341c0009105401440141038600807481418504504c55021790704591500070107100090712480745004a41d14004e001c40c0f04401d450510381030280d58600d0901c3c4200c002500001040c61184910509000b1142c00c2001d41d6030320300564030494103c4519511840420024a0074040e0404072500810054116030400300300030042421240c80078005600d00f9900350b0050241d0003003402c2070640fa405440a1414410380802180812a0251004008a00125101319242d110781d02c200d80c0c00b074004004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 12167866 1250 12166616 12166667
    0xa030c051603231c09060f05040803150a051008040203030903070e04030906050307050702060a022107050c040c0503041e080706020406030c02010605030705040b0d060e0105010e01060e0d030807 85
    0x1d000c0fa0b05807503902d10608900038070700361034010001c141c400000343c0a00c10030312124180c608800502c91050200c4409944440c3c00002048520809100c1c80c0324440e9940d07681461041c400306212480c10040c400e015030603061009454041041e08072403040d0038004442d4456200003400e5014140220340c0500c207000d00012007020313010040e40075600035121004010f07100c20088602d440304032501004034200700805001424460020b01c00860a40705071035114603941a0031607285108149030a0101003c40c103041800020701000e004a44112010001c4620105000d01107003c02072000d0050344c1d044c01c2c071000c03503540c88130f1429169511100c0345640b030540b454203100a405c1401381c0d000207880c0c903282203107c500501c1182c040c0da00040040001a127020100409800b940070629045101c4402100c00a0075602555041880c407400200e01c81d030400070141600f410580c00842000626424007580c0c1d01c0300c1140643d540e42528160919554191081c3d07001c00d01010300a040c080441e80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 12169116 1250 12167866 12167873
    0xa06020304150506012016060503091006080a0204050402060403080f1b21030a11030103060c0807080c03010b18060a02010507090812030c0a1e050703020606060304080a030c0516 78
    0x461040388908641c0b040c0d0080c0c0b40c2031604440b41195100d020841d2042111204080c51a000c0e0418446404465140109002d1140d41808592002020030303004001c0c0042680c00317020800c200440e4010400c8840d19001280e0354410b5511000ba0040381d480010800790346425044901440d00507620f907076101407605c1c00d100300d60b220050071103144541038844a004070020603102000c0b00c2206e000080343c06081822801644081e01d61107042e03075218003d44020f110100950300842c090200000c20b19480718004e400700030000c0c10001000080010444030340c0d90401660305441950030010b444491680c0040c0e032104c1c1d1072581c0e03984070001090ac0b110942d8150082c074030510440e030310001e140390751320342c900d90384d4548021030154030509000040715149050040c0046020914100040c801000303201481c280716070003034a0014000040000030305404100c00c54125000f510b40c1442d61605450ba40300901441c25148101501c1e8288452040c0c031800a0b01c1842107204250b6032800301c02d00c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 12170366 1250 12169116 12169121
    0xd020f13050118030b040303050603070504060305030903060709080a030507030302040909080c15130803062e0e030c1302030601030f021b0106080a020f0d0c0305010501030803070e040b220b030a06 86
    0x10501d4000759031040d99200102c500c1851a0450390f002d55440c580780c0721390340e0643c040c0100401c6a505449030348ad0014007656240180d0008501580186681d02c0b0354905050800c0c3d8028592800e010303014104001038600040d03546102c51f01450001e46404803031908402a21481c0e002440ca030382840910014072483c02c0081007508006030880e000c2003080c0d081c240d0f58400441d641d90405d8880301211002c144414015540040c000f000d201281c64483c180c103203800d0841006c072403080c2c15800a442d0345900b100300c07001801c5003200100005500d0380c1c0020320b482c10000c2100040d603008000301d40b290f4000e030400c01c245950301c04255121071140800440030030f9680c0008c21103600384a000500180c001c18100c1d02c1e242c02800fa800000440d00a10500b00341a510480340c0328125000040400c2080c81024082c0d481540c20681da41001c1d10028598084807660074031813450880d400d03071107554143d407604405001901041080c80120186e90003007401c0c1800503010b00829024404000640c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 12171616 1250 12170366 12170369
    0x3040807050106150e030115050114091203070c0e041104020c0309030703030e0a0905010f09110d09060605090c27030f0a060903031d100f0209120a0b0901110306060d020f13 76
    0x16550303400030020000405088e103000c40921841d82062150510940d440b882e489103100300d884840e1450a040341c4041070a03a641c1c00c05803003ca4201240081c02c012242c1903a034010024104041514100394880e85079103008c00c1c0490384241e6001a082844090900681341078000040a4540243c4e49040281044020015480c81400340c4100824031078900e11803d8180c440c2d0040d41c0040300d003400101c0c0024014560b50b4003919005128001006c034a50080c009424800c0340c0c042031082c5081c05000d020b12000d885507144000c1484404a02c00040c200502400400d00692208030ba511002c00c1c28099238201c00c02c060700800002105000241d0441400350744070356420070910704882009101d840c00c2c000300d00403c0c0c010110f0301041c01c07841e030400c5803114410720006141080040001d1a0031071091251b4069402980440b002e00100759021948550b0185c000d00003521034003804001448000c010030f00c10207001c40c0101c002c483d264183c600b8900d120b000e069aa0940301c0d00038108070360340d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 12172866 1250 12171616 12171659
    0x607020607030e010c0203090d020102010b030304090f06140108060f120d0302030117060108030d0e03090d050109110f030307030309080f03010f0f0803090108040807030c021c0201080c0705060c03040807050106 92
    0xf8214807250380003051041214070b210a9026505004814080080e0700856003410b80c1159212482400d071a0f5041c0000d00c010300364031100080359240c1b010070400381c0b2110f0740031806c035441d0341c21480d0450742c000c1030481d402501240c06401c501a0a00020f0a02c1315a6050001e54420b07507114941280d0194000c50580d00c202140c101f40200412500390382d03060034000c0d4a5990400c0c05038001924051700074000d1480c40405403070403c5030f40400702b041c0c4101520103a40d641c0d1102920030030701640b109030b400500010340c2e002c880c41909601083c1e6078819030400800b01541c4030317210700600213140103841d04001c1c1000070690300e50791044d00392407414071405841d03d00c20342424005a209400030890708841d6041e120160169039580b20030f01a0b03007040c01c0903000c0c012246945030041e500c00f0084140c20441c8060aa07200c1c490b40001084080c0040c00c08104d0441040b9050100368000f641c00d45c03080d524a20076580740e5907032424000e28021080c0082c1607600303081d4041200030440c050302c007902c0705 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 12174116 1250 12172866 12172871
    0x1090605160917010e060a0911040c1409010203040512010902180702070b09030a02040603060501060201060e01031110110d0201090212060709140109080f0d030b0d030906030906060305060702060703 87
    0x107840c580d08803110152100300d40856102c5a041000d84081080111041d1406000041d50b203070307038041c980c20010120744080e04156103145240822000c0d21461074040303820350381082410880e880140420a02031144005040f020075080d03502e038803c000702e071b01034135014201c00e10252003a030305c0320302030483d81301e040303110f41c4e007010001c0688015841c020344074148950003802c00031314228886000c1d51060322001d805015420000001d0785541c001e150003075204000004e4103614200c0020308540b802d0f081049038441036801000401c0c100c0404845141c4200c60010344801035142c01c0d10f61541c500700502d49170195a0000080380d4066100b0103280c0e0080c1d03107140c203a8149040c2103840f840c08844803804140e4285003070100704038a220007402a1010f040080965444400c0903203403c1481c1e044c10700fa13502101820790180c1d03040c055904040c0c8203071540c0700c1e9400c3c150f8024015800742e0180078109aa199041c5040c8520340e0049070096400c01d040e1819400c040341c0c003d446007000c603040701c0881e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 12175366 1250 12174116 12174121
    0x20c0717060708070e0607020a030b040b010e0903040302010203070602030a0617030415080402091302010e04020706150902071707030903021008060102061815090709060e011502010504080304030c0c0b030901090605 94
    0xb80035806444c403926442d591507205251a034104007040e040900f013a40c0103458403401000241a42c010180668000c5a101009600d08005040c14400007496085150000c0c4020001030360004180c4804da68001005030701d0341d803100319050040c5a554450328042c00c9880c00185414001700061040e501e07803107001084211040b0040e0b8141c01c064030001c2d045191100040e11040c00700a00d40465403051420307a02002200d000501660488002926115940e0a0300c0c8940081c01c40c0d91f00c000c040000c020f40c102940354407545001c10321461000d041e00e800050150825100722502000340d1f6005004030200b20340c4c1c9900401c1080203d4490313016203d13400100d41e03185110061404d0380030640c4002e010300400111492144800a001c000e40341c810b00402064042c03043c0038601c09496044100801907241c540d083e2008140801c0075019641f40809000104050b06c00b220703402070b058202024000464a00f0310b40300d07200f580c040207011401000b40041070b80103400400b6024068a4140314a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 12176616 1250 12175366 12175381
    0x906020d020a0c0e09011b0f020c0901050306040b0925090b120613050f01022d07080301150509100e0a090e07060e01020f070305070302010908010b010f0e04020c071706 74
    0x140c26100d4064a0010f040340b01304120310700c3c0411664440d22650005c0764a00e450a004241c00c1c07140200e100100e81c282c0d136003107106c590400084030b560004554841c5ca55150401103034540501610183c1000c05280004080130f00400c401d120a80100c041544942610b00400150084a00401702e0700c50804c610b5601a2421949000c2d64000a0004d0030b515128008050025800d0700003c903154020144200070b81d000030310140260301900030080000600500c07120b444c1c001448064003048109101080209010000784c0741542d006130261400107014860030f40d8580102034009074042018080c01071150f600003c400c400386015200c0700200d6480701081800d884940c074001c64554404042088441d1240510901040c0180103403694240c00c43c0c4214180042904140c902e0fa018000410841d40e00c1b0078814000c2007014001c01590028000080c54201d038001a20100300c000dc0c04240282e03900c0e8100c0b0b4185c4403240454040c6c60f96044592403081760942c401c8290f0040f0b00018001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 12177866 1250 12176616 12176623
    0x1f0c03051005060327010906110a080604050c0408030c010606090807060c02040902010c050f061609080613150e010510060504030209010605070f1e0c06090506040504091506060906020d02 82
    0xc5001d114440780c0e0303505000c28031056820007000101c4100403240030550f882e1821700c0d59161400c2010010490700102d0400d40c0139102c1401000000350340030001010010340c05011660070040490b000708190326400c88890b418091904244030380d002c001500c01a104055001404648564aa40d02565a590f844d103484034401d12441c40800c03001d60143d00103182950140001a105040c407800300034107910390510b050001c8040c42c0c4c403640b01d01c09101400103032140302d0380068558034000075080d00340350f00b4a4861034040c0658012060f401c20040c1000824100f89800207070320b08040000d8800040114040e000031b49060b80100c2d0700c1140410070b18803a80c110390503603801805040c04c80e46001c030210396aa1002006841c10288401c107100018030aa81d90740d4032010081541c00540c8281c145002c2e0b908c000c2e0300034007d201e911501004551182011b503811140e0880740000d488030641041c0001c00a10300c580d01010b81303410808190345070800b0301181510301030b0382103445003441071000344e070b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 12179116 1250 12177866 12177871
    0x60105040503030406030f0207050a05160e0402180a0b1e010e0607030f0c060209060307030c0314160c02040f060815090c210a0f061a0102060f060603070c051f0c0305 73
    0x20160402c120030700c8824001d8007d02d01078824544018039100c41519001e0802c0c000303843c21506501700c44031f00b00380c010500c1071410180400d102802140c2c10309900040d042400700c00910b17801514400001c2001049900482039001701820702550039081c412981041c48020292a000c81d0b0031170101501400c211060f00c03030055150300c0c0e04450342c04400b0150758003015090f044070f00310b408021101443d250500034600441c0a034401040055200310045d05440180482030202c03141c1c02c08004070810303d400e0100f1101e829080810400d041400440e002d00010a107528a0031300784800002c031081e00050032a103088802d00020b80585031644881c2d00d80e1100c070300ea141c0c06290b81d81c0c01d0008040719192034403540d8000c01150030b1400190b48000500140000c16160541c0d1000c2140300f00c0030520030403828003801d2001d000d1510b403a400c2c490603c0e50180545008500120000f15402d0050b900344202c16049412256103104c0c80500300203101c1c5281d99003400301c2c1000c650820041c024002d130350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 12180366 1250 12179116 12179119
    0xc151e050c0301090504080c100b0103060506070209190b03060f09010b100206061003090b0f01030606060203040302030615061e07050d0c031704052109040b011407060f0207020603130b0601050405 86
    0x10b15592030801107070080d000192090310114400c104104e0725420030000008103c80310940801c01002c001c0c00581140c1150380118000c99003008079a0040e641c0114240c1c0c0302002c03152400d03c12414000c003030014050f40790313240c0d050b218030000d00504070310254190740b01e04130010007808010326280501880454600c112401340c0c1c0044003184840c13420002c40410681c0700d00d000200d55042d41c4558101441c20b696504400c1e980340014001c0c00000c0c01040082d0101d4002907103024510303404259100d000401c2d00480b40d071072b0385560200356944011681000c95940100151004c6501c0180c4280d00c5064122440d20480008496980c01040311000c01901a25040c130b40c1540030140910a00004104072114025002c1d40114082c0024078070b5000b02c03402ca120760b200c1074081d051104590844600506001c90741110308905c0b42c480c011568055403040300410b907010001c281d00d0185c0111400258000c00200411540b9010900f00c03645a034040c4024145036250b803c01942e1760300c40c50007850f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 12181616 1250 12180366 12180391
    0xb0403030e01051201030f050d050c030406030504020d020d0c090605030d050a0f09030501050c0408060a1802060a11060c030a0b04090305160c080a05010c080a060f03030e010c151e05 80
    0x20004240649461a200039040c100706103014415140c12034005002d0f00110340c540c80301c04089050020030400e000d02c04505040c01480d1485180c0380316541d002c1c1e803240100305612000013404548409042c5042c1a5001d42401020020b40c42c1840322134500f801001c2040b0b1910100140700c1c80c00240702c17800020300307031074003450404032a4084901c18a401d081d1003d00038809030000001303109105182c45140d0501c0030b69211070401c0c00080c24070002400c104810342c1004101803504004025a210203581100d40b90303074422041300300741c80142c201032507509240114000c000c15040424000c522071140d242d81003240444400811086448075600540003a1051002480c0ca1102c0181641c40d9070003450342000141d81c0340821407a1400c0d002c000c942a035141c0015401d490303005064141c0002820701b050090f5420500200351002c0b07148000b13010010003070106102c5034001d1002c01ca48a801c08070106401003540c000c400605035004c2c0c1c081b024802a500442d440100d8442c039401040c1080380c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 12182866 1250 12181616 12181619
    0xb04060902010e1002010204050f0402030915090708070e0117011406040209031006090207020414010b071b050d0f1106070b040f08090303030a0501051503010501050703120b030115050405100b04 85
    0x144001440380c104220b0500c41502c0c0c8540c0e095480d10003902c42c200301580056a51400d010a01c0940070805103041d0040d8010700502403400c0003c82c0c290400000b4650f1280c281c0d50340c021061402c12070b80d10259840c010204c010030300c1050044102d0689490300410410700181c8424039080303886034591006548809030116000340f5040d001066030200081c00c40d04100100e1406004540e40c560182e4417442e40012401b0841c103180c021124940900c108500d034641c54031403400281c0c410820000e1086440c028041d002c031300a01141c00c00f400f800f0b00009e4021800c0d00e42104500e01861080e112004550200e00103440e002c003c45140320f030302500c540d482d503d03990f840320046041040b013115102014040d134800742c2c4040001d58825041500c000c00c16516060901855804a00362802032005c01c000501490341c00c10b00f00d0b440e9640c5883c0c22a00c100e4a806908000c1105440f0030b0384c194201810203103403015580072102540e43c122810455521699074801003020617225100310381e0002d000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 12184116 1250 12182866 12182873
    0x50a12030f0e0f04020f03061309020102030304080a030228140c0304050111030405030102031e010602010614011b020901090f05010f15120209041404110d031b020d0203030304080a08130b04 83
    0x440c0034030307254081d0546904a0101c0002002e9800c21b46421580c0740c404000c110061500c103409100301410b40ba4104007100d51500000d40b41d100061016002c0c0c940040c5c00f4407024443c1e0704852078a860644d0b07080c1043c05100018440f002401d40b49000036035040c1c0c2103000e0800944c2102c2d80c0585080041d441c09140c02d0055402c444010740d41002404140030001e080e403000c2c00114407174a406c640a440c1207181d10019100202c0c1a00000c0442e071421b01d003400b542d0410300804e2040202405c012000c480d20000d00e409550400c200250031600b904000650006540c008800c90000b03c4020700c41603803078010300562010a0320070744442800c00648180008c0c02818894414003000101500d08040400400c1c281c40c040798810080341c8164007004240008900581c414441c05c4a95955503402c54030010480d81100c040d460305038646c030030150115510f0802c044802617014054944924160400c81500c0c0c000d03c203100b012954402c001a0b040d800c005218070780c42d91080e80c42c1401c0e240c948 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 12185366 1250 12184116 12184127
    0x110c0109120204060f080703150509070302041802031b040c080903040603150b07050a12020c010c02060d020c0a0809030706090608010605030a060302040213050307060302160f03021507030501050a12030f 89
    0x10090f42c02c01d6642101140013844d40700c2d500094840140201041c07455403a020381400d10055050200c80e2408050118140000ca202030031a501143e0115a0041c021103001c2c0e8079484220007541031146031030041d04000b00e0000c680d02803104032070030401c00d0f8401500fa2440d001c00c0f120706449800400040c490203010354046046040c0b904200d1800503200c2c940e0030407a50000707900741c4042e44060060010840c00d40154a0b000030144054031100c400203001034a07000314010002d10034600440d05480746507981c0e040d240c0d0000702d501156400c489904004026a202c1c3c0101e5000380a4000007103a401c2c080d00d00c0308120303561a80c6040181e842d0000469041c0c00140c009003c0720b0301e940000000d80e40c1c40c00688202c81c915400c000c00355160100701460305213103a001805250050203a003944059280e4104242504003a0501c22a906803504904085450f01004006440341c1c05100c1c00c0c80d415030290b03068036802d40b4070b09040380c0c0710b200ca100c800e081454002d00080140c001c41c7c038032502c0741d0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 12186616 1250 12185366 12185399
    0x1406041802070209070c050115050303030402010c0302160603090203072903060406030b01060f030606020d0c03080a0b04050c0d0c020a110f030f0105011404110405010206041214030c0a110c0109 85
    0x1000142000340d03c2e80003c3c0c1c0b10b4401c1d240303100000da1030000007041c482c080c2704580e0f41000c1c0041415076186041d01013600c0b4000208040c0c14030407004598022b01d0b000b88080291003a41d00e07410303171807941c03144030150040c6101107069020307218085012954450b45074004806000c40d460868045001e426694056800107024580007619003c0000004000c6410316000e01150b07111701c001040b034400300030116803c550180003154000030342c0040c010b4204000c1401c803505131414000682d0b821040304050139500300c6040d0402d140070100200c51103454041c2507440201e000501000840314804c0341d031640000c070041c040d4260480103101e2132825013540c00701180050103581c00c25100d8241e00f801c49100341c0c401c085071320a01c3d40340c101c0d501d05841007008801d4031301c0c003040c1400d040000003941c0300c00040c03000300002120b5002c4110a40100140640c220340c4500c81c80d96450184040f5400390000303607802000c03400400d14203455010105076007030b1281e01a541d490015141006216610545 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 12187866 1250 12186616 12186659
    0x31a04240b03060106030c031406010906050a0306050d050309010f021209060702130f150509040c09020c030403050106081f021602010503130203030d09030e010203030103050601090903031103160801140604 90
    0x80c1c0d00c120101e600d091005600a01064070001418a140741026040c0e503044a0b400d908a07a4280030040c540c7e8000c001d58090b00c80714a0b1080d203a01031b0b980e06600030409070b000301d644440500f810b01c0400c20000000c0044d04c00a90b0f82c1805400e90784400d99031550f0141310450600b03010b00c038503103540c1040c0010709003040c00184040da040401000d60400c4540015a01e1945519420000c0200340200c180b40010201a1100302c820328060f01c50b04003c0001e402005101500058501ca84440400036200034607000802041815610840b055486140d4021030103038480107113800c0c0b200c18191080d81c2c0c5010703000d148040b0702d5200764011200b0340e0004011011005003540d07800050b07107042000d00a10144201d00007204021810050000e450801159045510402c01440000c80108116044032015400400c03c6407a03440e069015242e10360300350030905070100811294050794041100c4c141c071562100c3d41182d80b901a8071140d0304900e103445801120800c0308101118a040f54078485040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 12189116 1250 12187866 12187871
    0x62601090b150d06030501050c041805072003030411010801140d020109090603050c03011407020a0f0f15050a060503122508070309030b09071202010509030715030204031a0424 77
    0x8145041c20059000f42c111601c0141d51100103108010003403042540010b44981914201880d02320080c107584041c05103d9411601d840210748224003c815555140c007500c8640021640090422035503034204032403c4e00c0700480501026002e5000b0503101307041c0c598080340010720940342010320560100f1800701b01d0420105000000350700f41140300b14400b55210b80301a04961044408050a4880d18a0b8603200c001e40c6800344130503640c00181101d00b440e03000422040c0e401d103500b020591844681000f810303402c2c410700c01c418441d4442d44103500c1500b52039000c01071035480310249941c0307605445d80300a01c010200300e031072007500100e01605000c0001e0b0080a0ba0072417555181c0f420794018a40440100754020018010005510460b070360204c5104024800ba03480c0000c40c0030811003441010703050200c00a115003d40d10705000f02c102502040385100e61032224120002c0084d4040d12059620380dd18604900301e5280c2000a1401141c200000250b034002d00c98204020035440c00b006034410f903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 12190366 1250 12189116 12189139
    0xa0213050301050702010c0215010e061012020708040e070c0507060e0a03020a03030302120106050f04030b0c0c0f0d0f0804080d050601020a06090609060605220b0303130807062601090b 81
    0x250700340540c078440c00c0164000708107420180006403070f01100c242c1da8112403464100500041003110a21a8014021100070032400d0045906644504032038004844850000940c90280f04984004000b2502c5801020001d955050070848036142c49400051840d00004010024a40b24903c00ea07034660300249a45103180d40e81d40020030400380c503442200840d07004542e0980c806401140c4c10300605160030494075010707000403032503000e10860000925910010300410140c2c544082580c40a50741d0108490704448400452641e581c007040804001414440d0206d002c0c038810700c1303050701031903106419605040502142c04007511008002904506c80c011009000c103000340159100c55006d000d00103007034500b43c103000094441e00d4102500801d040d0a446400740100030807007401603201e1a0003d64415100002411841844140320000e05003100100c2d410001041d40c5085440f161103103500c0c84a8105010700301d4042081d8000411314030001080180c520fa00300c034002d404001c20240510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 12191616 1250 12190366 12190369
    0xc020a02040f1d010603051c0509090a06030213050f070e0109050f030a0203060a050709060e0102030d050a06050a0807090b0306040302070623040803130501020105190207060e0303010b0a030f0908030a021305 91
    0x20740c0c1e000c2c810f03601e0703445003020410700034180003060140d810300480044080039140042c04038803a0428040c054404000000c1501d12590300100c080d540c010300100f5240e14411001e0701801080d10301c1c40440e40700a021405076802808000e44068068484050040c0740504201c203c034071410360180c2500400300320900603038062110301d105103070040000a56041824000b08004030303a402c081700f4050f842e642c04604d40e800000340c0755040e00249010400780e464441d03410240412f44d1113103401558121001c1450ba04c0800c1700c0094070400b00c0100300444c080f00c101582c428040e40c02030056003043c1c10a0201d40d00c1498440140307003041682d1492401305400940c0903611503441500181c0010031441c1c484111405180c000b484244000d101c0760a14016200b0722000c0004000c07410790303000407803000700328854100324040406c0c04144ea4403580d4800c1030030261780c4030041c024006807400b85801c20300d0f1007501c81d00140d00c1e00500000c0c25036513244000d82c001d60101c21280c98500081100040a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 12192866 1250 12191616 12191651
    0xf020a08030a020a050c030c0901031e0c08030c01050f010e0f13020a060807020606040603051c1815080a02070b0604020c150106230f07021909050403050702130c020a02040f 76
    0x41c900580c01846034035445e08040e800c1c4040119020701c640c100100c3e00d11a0f42c4d40d652480c0c156500281c40c0c00c040c010240c0c20120340d44901d44001d20b114056140020012008806001005450070080c85999641400201c540a00340a10301400e8081e8010603422543d0240580d1302269084002d001c000003078000598480c8030780e100000003410f400412021690521000c0e411402c141c4050001078199925039442e030401002c1c0b01400918501c20050a610861501c4005020b41d0700d01091103489491280c410a81101d405011808080100d400c1009503c00c0301e142c203070400600003845d1101400c1201079401400240c140384078028010f0301d18010290850700030500360711401e0f03801c01400010b054154080041c510800d01c2842134100103000c0504a801c130350303811144000568180d4111860002460300580085460300f0204400c140d017080c010a802e9000700c03004110904010010401c2c2d415915894006030405245075006040c540c02c000c2095503001004a402d98131822218403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 12194116 1250 12192866 12192877
    0x31202120103020f100c030e03030d060f0918050a03181502010b0301150806040b06060408030406020d02010b120d0309050c060705010f0f05060a060503041a180c01030b0109030f020a0803 82
    0x60400064010011031410310145500c0000690f181d012170b0302c56882c05801c1603030b01100603040c42005601e00c3c1080e0303030900441d40035851482d01040030320f4688015815119050044080d6545020081d800c2c103240c1480d6007040c15440710090000c402107036800c403084140c4288800c01494203290101d001650280b0746c2c2103000c500d500010340501042d003050300756843d80401c001102108101030004144c0800c2c81c55019400c091400d1450f240c1e180807901e144100d901c0422180030204001c00d021398003280080040c0c110782d009202c1c0300c3c00b04082220200144910104941c030511000700101d003e0307000001e0880c0648180c45604030701c40c0c04980e1580c8036075001c581380c2c2d41d03035203a982d60f80280d403044424030240d16804110b01d2410402080c0e171040c050203000b06209020001800300541c6809440140038100c0700104a8107181142004200601642c92078a001e040040c80b032551003441285072b084416520071460505d07580301c900c01d214118009070703000b100005000ca07020108200406 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 12195366 1250 12194116 12194137
    0x8010509060f1003030309080903070f2405090d05010b06030109020406090e0903030105090405160e0a05180303061e0904030509030d020304031203020a020f070b031006020703080a0c031202 83
    0x101803400010103410721400400c00b03800c0c9681181070107800314801c40c01006a9505040024034a200350400c0101405084460303603040c81904c5001c9201201c40b14004c0448081d02218020f00800e955000301c840001c100303400c0000d0007846041085d1a168105034040b81c040c000000b034145030b10011480c2a4000d8100d26220307500010104103459000c180040200300000d564041c6003080310040361248018032400d40f25142c14004542406414000c140049202c40901201a035540c07020310100402214000300c000c1c039100014909408200b40204c0750001100914034660342c50302081800a202482514130310405082c00c2d000f9218440d82500890090300d403961200281d0302014680304250350544210b4200748800c1002030b04941c03542010a80a040146e2543d9031720034228601000c90b400c1d1425032054507800582c075440c40c1c00030b5015841c01065800c10680f219070a0313948140341d00c070081c110721003000480c44d000c1c4901c0d42ca21940c2c2c031070710f4070520300c088240b05602aa0400300102c3e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 12196616 1250 12195366 12195371
    0x1021c0e03010c09080c06070210180b03071d0306040b041e1403070c05190b0913090605090d210c051209030406030f060b1209010204050d08040302030c010e06030a0c050706060801 79
    0x34010090208103502c038401b002c8070070b41c0c03404445a020981c00d0400481810070700540045e0700308003d405211800c00344c414a00040d031a8074243d00010b1a50901e824040307c070544040f400701d820304012034503034803e13600459184801e80b81c0e0760f5000503807000c0c08a02510301611000040c0040c020303100303690210408100454035000e950420980c000300c42c0e0311003481032036041007409040b00706d10030807400c86044d4859140c44440c008040303044092980250008c0c0781c903280700081007020551005015144042c01c44218501d06c8505032224000603040f24101c1c0c144200300d8924402a0708200c0988a641c94000d0518055001d603410b00e003010b940c0e094a61304041010f101c21507051188141d810107410040c44101d1906000b04450b200e4001e01800c0c0080280003e4100c00c000d40448008040c00361020f8140750290070030070082e03006408101c3c420f01403656404015841480e04841040700100030b0380c5162a04800f803001040340c452a030b030130f200b024804900420b5107481490010118140007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 12197866 1250 12196616 12196619
    0x4080d0204030c0e0609240105070b1603050c030108120f0409050117010e070f140301140c070501060e0121050a0203100603030e0114041811071101020f0c01021c0e03010c09 76
    0x213101c0108001c0019005517200c0c0f08000c4804000701118074624691035044500302098801240c0703500c60782501820003103104051004542586521544040c0d06a07000c02181d00e80c1702c40d070529407000f0b00c10b50089070300c0502c3c81c104060380b5000400c0c11000500c821071903d552140e06034141c950036444071640350585800c101311100203010310100041d81002522500d4206040704081c0c1e5440d01401340300c034158441064698401f54044040ca45820616116a2411741000c402e41ea00c81c050403207007075003400300008407506071040c128162291b40700014600700e4501071045903114000c00654841c40317844c400b41c02588003482400800c8208480115005046040c0a8a500340c24441d1a04000e03800c88081d82490050003510151155000d0b80b40001440180c0e10b0064003042458646010b03000903a1010031014482c84083e4100c00c0e0292466460340c2c40319903448003540008030340540c200444e003003500c03141400d440440340514100740d032501e15410003007421194a0145034002c1074003240c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 12199116 1250 12197866 12197879
    0x100507120203070201080403080a140109060501020c01020705060403020111030706051e070c020901090e07050303040f050a0617040803040201030f02030f04020406050f061c02090d0f0204060b04030803060904080d0204030c 97
    0x2004055001280001c0d86000c030f860b40020203050b802400641003100c070101060f042d650316040720f803045e9012041c0a40b035507110b1034200000c107a14407401d40075101d4208194090350002c1240d5089400c0209158203007482e540055034194020302d94004203020402401e400030b013076403080f140580075a0040b000000c44030849100b041c0c0c2c001e049807003448a030240d43c10042e501e80403070b2070650300307107000c08901e080011528500c0d02c0895084503a040c080820b02107421480c00e605c40040300c0c003c0b00c4540459599a90584040400720441000c0100801c00030f40401e800c080116089841898000390248000142a040f03801c2a214010a2001001400113615290040d0030241c10229030203040c5186080009455104030901f400450505007030094400103542c1c1941c0d08100c3c0a0701001101e18540b40c800c040072140b42e0120b105900e000400704503640c407001980c05899004c071050f8910b80740c14040005510b002401158100e60810512030389240e1030016200940c4245a0f14a0703040c00d010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 12200366 1250 12199116 12199133
    0xe0303100e06040504050a03030e0c1e041104061b02030c090106030b09010602030901020a02090a0e0f0d09090c0e0d1113020702010206060303191b0515090105100302090703020d0605100507 83
    0x2c0401d4400c0d030512060001161000c6041100c031945400c0015213400080c05450400728454003c0741d1006412101c43c00c0c000d85166094a4074104840412281310320205220140c000d5014070000208100b00003d00d001c040300c1c8080d000c500090440301c040b170944002499540d0f00340c005500098a880045149003400c44101d40540300c2400954100003031003000039035691410340041e03c51140c010110321184403c1d400040751002c0e0398103440706040e02c1510680d0311128140a01c000550361000090403c0e02849000f41b208115554425890f06c61130400803216424842a6204500801c06604d6650349918491952003d0700c40541c541400307000180c00d110000380202d01a4004122614401c1c182040a007501200b505154507151625030300250103d110110007801441100c4805901c4801c58040307502c141c020b400240056039890071510800c11441c803002790000800c43c00308101c140203401610340000d00b80c000160050ba40d000040da89081c1d0504100840d90004050081c072240740f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 12201616 1250 12200366 12200371
    0x6080c04060303020d18030203010606051306140703050304060e0703060b120114040204150e09011a0d030207060e011407080a09050910050d020112020d0b0102061602061303030e0303100e 82
    0x1200e08000a5245480103511001c4040e01d09042200d0548901071101c0034008000217143c02600800465444043c05800c3d075002509802c000c8603507110008000e48034071481c0d810010301343c00f854201a05550241c50542000e00b0844401d6200c904d40c5070600002c0007110010b600038240421220440d8062191820b580c081c880e19507410000b00204c5816a000501c1e0440e82c1074400098540b20328104149000d8a80c10854241e000e82080c8819400c1c150000038800c0c0100450202080d4081e0402156183e282c40007800340c1c0103905e0820a850203002c5405001c0720604040c2003d00c003404003040300764444202128500004504100c0d41c9510501e40b001603d000d64140701c0038182401c406003000703442d1158910400c100b841c51411a48244090503010000078002d6444103030003041400900351640460b8014450030000840003030010818100982584d00508a1510380100d0384601c1c0d002c100c025400d16482d400b020400260420044d0311034941011b100102da400d2286845105201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 12202866 1250 12201616 12201619
    0x150303110c0102030928030c0906090b370b070506070e03150702010b0406080606040b0f01050d051005060a120606050406080f130b0a0b0f04090302120a09080d0306080c 74
    0x1148001ca4280d8000049841c04441140c4100d03050a03100349007240044031710404108004540c1000081000b54400c800541d007840c40203100140d00e55204108644a0100c1e0681c09036040440c5401d140c43e419004c0e00748450101050341510385844000ca0081e540d41c00408a0302000400c0010300c4814451103800c110940b40c80e20354405040c0000e55600700b0300350b206082c1c144110101d02c002d0f000750701403880100003034400e006c100e40e40c071002611040c0031940075008074101442c0b110726250400045d45240c505846c0c840c140210004240c00030722009100b5540151a0a400718041c4d031010301520f00b10340300d5035646110110b040c12400aa034a158044000c0c07120602091140c81e42044400c1d0340842e541c1d0780c0d06034541d80c8682aa42d00e40071100007810495101c0203004070586590810415010b003558484812901c0c40c2c140400c94109110190058011468801d000e84d403910040c491601245426882c603901c4170381c61804d01108034115404655103a030104800c182c14002e00020940 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 12204116 1250 12202866 12202873
    0xe010e0f030703030f05120a140601080402091501030e1006031b05010c03030c02031c1b09050f060306010c060e060709051807030c020a050a060218030304030503040905040c050415030311 82
    0x3444012a503156002c0c00010b040c007060050201e4428420001d40301c0c1818940401d801a08111b42400001c00c0301e0b4501e150220f0195002030010350049403500d00035940505440f0b280c0c0e6410211301c09081d100c20b40700d8101500c441c21280800e01c2042207109000034002c0000d5011b265182900301c1281084a94454003c416003c0015a820a160240c4180c050402003002d80040b5000ca00798424000340000706042d40701c040d00c0c00c3e2003c0c1d01110300e901180840000d2a0102542034402000a10400b540302d101083d0401003401d1038001b540d0031400c181022050800079030b407420151001c400707041c00c4961101041081084d0301002d024002e0000b5503a503256108150f035200300d8180300034014410b150300c032128843d809101300942c3c421540c11105807180d02d0814a0300c10702039403107607101030380a440002d09800c003442c010048504881d88100110b240919100e601400f4040041c4150b80c00c0c8129900010103803158003030321491500103415800d03c142035140150210303c880180306aa0750 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 12205366 1250 12204116 12204139
    0x150e0a08031819080304020d02030a03030501060210020913020a0c0212060604060e0420031002070b0f06010201110304060c030f060801050702010c0201020301080a031103040801110703120915050402030705030105070e010e 97
    0x443c0c009040f100f074000c2e203010344c2d84c1c0d618004108442d2058000941510804a0ad10149a45a4030450503240c0039801d43c2e00c0c1c2180c1c0500d50017030f0302481c1c0803180d10070604206005150805c2d070003401c41c60164100381031000142c1d00014030f004452100168603030065010045146024829030000d0280d881d180041800c0649482c2c0c0c0b40c2d202100745207100c4558012061969504219103803100b400480b05656070086498510902c000c01c0e40c05489080e294001b003440c560044c0a202100d00190401d0341c06c60342c0c0c2c0d40f40d41001d00301d03240c210018550354002100035000d007401120098881040082450b040c1f4180007801c450024600c0c5046902c10310051054030310100d02c814081d03805240980f002400754848904600c01d983c0081c210758030306251555446030800c00703001c0144c001d4030b9481c0071103060050001550390500c002022170385a00202480880d04c2e9000c9904240040c04413950691200080790071524161031040c00b042c0155445c6210b581d100720203240040c01a5032103426403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 12206616 1250 12205366 12205393
    0x1011031003120c120201020c12070b040b100f0909021e030606010e031501090c12140c0c0f01050705090a0f0302060a03021c150e0a0e0604150e0a080318 67
    0x151018000245035400c40103049120a01ca407403000c3c0d0b401e400c40300c4103001003040c0702c01900035881580165081d0081c46685009626000d0642e42d0580c0c0190001007969205d80c1d6141600500400788445034129280c00300e83c13154504900300260040b107c2c002000e42c42801040341c0e00f84a0700f450040000c0301c1030b82c00fa40e614041001a0040020300700150000301040001c0e003000b0b140114100c80c2c500324000099500c45907002900071907450b4513494002450400340a0640e6545480d1404c3c0c3c41000002c2102e01d050070005201e205845001d0310300b10b64030583c030a4251401915008006240030801c1c0701103140c6103000c200200048800005401d26640c0450401e020340005c034403e061340480c654041003070310409041d02c10840b41c81002940c100c00c8145c4003441083c050200010380d254006280c001c1503101d8050341a003484020101981c40e641d941510607a10694a4030854450200503ca18010000900d407070303101b61603d645a262402d140303180010076608020290744000c103c000710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 12207866 1250 12206616 12206641
    0x105041a01030f06030807050c0405090303070c030c020105041205070f0902071104020706061802070605070801140d03020102041a0315060901080103030302070219140109050405010b12090c030102070302101103 92
    0x2030000030b00b00854010740c903c0008004002e0359102403e0903800164000422501203034466000100310f50401140d00c40300d45540d030340e000498805000ca04951004408039000e40c4100340100d02c14504146004d403a450003003054242c1d420b081f150b961102c5014480040c48110100180001d00411418840162034050081801000c0c132401294009072000610055400203009003000c585048042900c0c0310544000754000401501c806103407001040700300b4444c80d2258101d80c0c461480c42019040441000020b40745401c00710f040d50b600300710020300780c1d5a0045091400003140d540c91303141d01d000b00a003d404607440000c40c1c4586020400403101c1da0b0001822410340e605441c005171160030074804035941c61501000010700700b1590313000140055041143c999058020383c0c030307440c08980d1603084c071060720001c4c001c9029000003407015480e00210410000e520110b00c81c2200c19000701032003c24226801220140e0040e0006c40c800340031580a40110313001c0440d50a801b9145141031a0510700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 12209116 1250 12207866 12207911
    0xd14030705120a0914060403030b040203010f0510030e01050106020703020a0909210c080f0d0b030105060f0f0307030204050f040308010e01060206070c0311120301080f0102030603060601030e071502070905010504 93
    0x38240905804560850025448115401c2e4031841c174480b1401c0c2402441c0d59403004850440000307061016404890416000b964101c904800215896905120820080301085040d2108050741d0b00d82501070710100f401040d009014a80140c4509801e60052001003010307608040306150038818107c0c00240000244101e0022100041d0b844406400003100d20800d6402c0181800001180d081c1503800d144004041042c2070b800101300d0120940f0515003070ba68111495075002d001410321108505108054044040d4002c0556140320b40340e500040807607400341c1c0c40c20703049507442c004c100405402524040c05407404410074203103076242003c004e544880041080007080483d5030000e0815000f510810803080480054a8001c4111180443c1582091040b09101c2c401d03a501881c0412040c82100d00915003d80a00300030790392140190702510100711000014860b070301000a19580e01020941c0350001e55004e01600340c80c200c01107040e43c0042c1c100c94811840c01081c0395512029002c080c0f03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 12210366 1250 12209116 12209137
    0x61e060c0203120a0203040e0603010903080412090306110301090b06070b0105060706110a030e010605100e061b100c021006081509010b040606030204031209050105030a1802120d14030705 82
    0x3209641901c0428104211140300300310a0300c02160b008841ca40200c0584256a03603082e11424540c4d039201018240d400f420006400f190001010401244450402c0c6035482035a007800800b07a035403540c0e404122420b01040c00180100840103002c1e5000314042d12400400441d4168144803c586039085400018841c0910070b0400007204401c00c0041d0f00801d2000110030801138590b42c844001401a1103005004c12465207440c070041074a2802908080da40c0c00e8a541d100b01811201c8107001d00c99218841c40802d03620940051089404c04004000b010b41150704d010a001801c0e0300040c1c6003008020036400c0c0c060402e40140044040068180310080030909411a10f495032004640140501c0d000e0540003400d184010450030b8141e00200110707072149048a42419a86000315072010369800b0300c500044d4104080340c00701c025600081e82165152420302c5454245500085a0321511040e20300766401485819140b25084407031840c5508592034410304d50b15003180010464410201c5e0b16 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 12211616 1250 12210366 12210377
    0x20c01060b040302061b0c0904050c09010803040b0d090602070506040302030a0e030601050904030c0c05090106020a0c08010212060d05010b061b010507020f10091106030f010f140a0506071e080a03061e06 89
    0x171000382001c2200c10342c000002340000403141802d0074142d0f2201c070040c4480380540840c81c00004c0f40d00e00001114112416813050ba4100232940c2000005010240700a403042c1d5020711824000c20428440f59015070722036001507540314034448001d0003044001442c24841c0c0c006800400403a151124010b0b801541854015001c0c522032030090002e2840350840c5070000c0101c0000f00b641174000070b40794a07240c0622821460b10342d0b01c1d10040c4c240d01c101c030003410155a40c038022448030705048014660b050302c034100100e000784104000c10007540214030040103101e501441542000c20030f11840b504400c06e8800f6250090107503141030764500d545040001d603155160300702d00521004070644200424010a05542c9080040b010910100280940030708030881c8140041c252040388440c08510707a014109981c2c02c0d180a00b0800707650812101a14403845598154817045104c082012001d44101075258032003501c41001022541c07140c12403400b103082944105481403409880030200c0d0110300c2e10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 12212866 1250 12211616 12211657
    0x60307030e01110901030e0c03070b0a110d0e0406050907020a080d06030503040b071208040302071512020307020706020105060301020a050702040b04141003030e01140703030b010e1003020c01060b04030206 90
    0xc03402840d16404000312546403003ea031203000c3c500001400c181d50300360380911091003d01d80c030a40f00d5150311000c80d41030740160760030002803191401030300c41c4030f506040c56000e40c00046102d50800091611400000341c2d400c0c0c0314112458580304010181c50151107200b000d00c4c0210b000795585503c018050030702d007030110301481e0030307141504544059a0b10205603a103032503a940125005400481c0100c4c1e0420410b100000c0080c890b40c02e0f03610403074040d401012607501d00080b44021034214100d0008100010783c041001c4001c0d80010340c003800d1143d0090002910b450780003821110302a0a01c0c0c0320fa40100100c1c0b5450780d001e410f469100d501150300042041c241310004005096111400a40075000b01c10007000c503000f0a0034008913070103901c5040308842c4000045924196070314082c2e16800c0240400c4011038440d6014400c034100604212080b5903c0a0010342c86d4010900d119000a800080f00b03603140200b070140d0001041440c10300f600b41411640002d01c1030140101c8008031a081035031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 12214116 1250 12212866 12212881
    0x80f1e06061e100206040c0e160804050a060903080901060803041404150305060709030b070203030f0703020306030c21011803090501110709050a0b01020c010f05090f01020a02060a02030309060a06030206090603 92
    0x780b070b2480010007481c10210800750007001c0d485002c125400c0e5042c4c0c0d512100021001c8a507001c03544100c0f00c0d109230f140702c403a619a0595441d43c000c0d00c250760304d104103d03800303000444500c286160203004c5c0e1622410b81c501404c40500755201c3e908504441d0f0010b000c200203006082c0301c004154601184d0204841c181003035401c0900c0c07183c0c0e102520b2803080c54184504140c005001605490003480b05000313030b1b600e011040c0c3e92403009880b400f49010b58800000c140c50b1080c0d000e1500500010140d42c0403102000000e01c2460a44026421140e480354070348030f1688013441404e100b83c8054420000707021444e00c0c0640021400d00c180c03810312117581c1956101c00800d021490180508103002c001c90304008031032400030003140500c9809403040030040580c0b50b004070300030340d1074490b15610720307142203001003d1182c803620502c0227505612844442da80180e440c1005000e00b2032660340195100c4c501410901c3c50b003807020702001c240e00c0c540402800980c0320380084039982401903a003190ba941fa80803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 12215366 1250 12214116 12214159
    0x19020c0a120204140703020a090602030a08010905060303090405040b07180311010305041e0309050f04050f04110f060c010504110d0f030503130206070c0302090c0405060702040b03010e07080f1e0606 87
    0x20307a0705103505103030010170100c1c94165018000801c1d095807034942440c0c07680c8042e607891080383c41400102d9058001000701c02201d03000580e0000025056034200301103403011400369402924121b8003c5a5402041a600d500403100c00302051a4040c0706d07070340c919646458120314080c0c03480e54101a20f0314000b5052051007041200c01111245045034041c5003401c00520b00e8030580509032081181420912403440c190048034040d110712180403c258031240d656003500c000c201401c41e00f10600f8800b84103540d4804010b406071b0281a07001107402d151515000c0300100780913440608c680d51f881c00e070502068000d5001c01100c0e41c5400e00640d6a1945622250010f4400500030750200001410ba4200040b41c031030b600840b407003030301c1040540e2100030200001340101e01400790040414480361001d4034194201c0804224042c0000426100080c0102d003428041d4000c181b40c4e50040b4815040c002c010070580306080e170200c3c5405242601d900c2425210000130302054401e901c042c01d85000e658072071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 12216616 1250 12215366 12215381
    0x61805090c0d05030909011401021b0102010608030406090512060108120a02070302060304060c030501080106051302210c04031101170a05070e09090f0609010c020a0b0a06030807060219020c0a120204 87
    0x30001c0e140c06841d860525980c0d804485c5490066511360300005004905c40c40004400c40141c01504450744110040311002e004803545904541d2680c500041c4003506000070405012540e0320626154204414084c8180c071814005069900c134800401407400045041c1c4c48c6440150f1000381da43d04040800c03440d100d1150006503004070004180410010950710200781c2c20303515241400704d40c3ea1210784500700c072424403803540c102106000025030a075280d4010507071755005008503000d111b4601d40c00450b500f001ca0310440c0b0004005018030500c00020300510800c5800d00e000c105580d8800c0d41d02c2c2c090103010345005199602c850206110303e000b08200c0340250800380c03000d52589040a00c03955500d41ca02201d54440c000c0c88085a074994041c060300026000035001000c451109542c2c10307404400082000c0c2c0b00503611400800000c90800061a0481c062200581c0310300f0301002004c4140c205259a43c150340c0901c07162041d40e21907240c5a0b00321342081e821117035a0702c2240085405031110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 12217866 1250 12216616 12216619
    0x60506030118050906010503120c1204060906080903040b04180b1005030106031d030712120f0614010302130501231201030c0501050f030c0a09030503070b07080a061805090c 76
    0x2000200d80445030781c2e8010100003001000b84000e44a0300c0201c0d0303e5003428040c464154210940c040e6440503150024001d0910102c115010328141d041c2d01c0301d032508190441c100007109418108034803130703004591036000003ca001031850145001000b003118402ca21410b40c04490a80c1401640015580403008521014100341c030210004203008290303600900501d0042482d00c0d20a0135070010210300f508112001500641c07811680e0f031144c604180102900e201001030303c0b0701d900c468500f54002c0d01c40c9020210070119003142030485440c002c4501c44100e604162040c80214940c0142c00c03418812500f0a080c80c0d6081f04400b0740104515117003d5005011b200c001620300d140c4030b400403400d4101c038050f0790310402554a40d401183d05219405100e2a031040c184040b5240c0340300900101440092400c1c080c220035900e0b0780e014295000010203a64020340c820030070000980000e03103a40e0106c2010340070421203060039a03004807029407125a90341d45680e00c0c0011041c0f1000c02959049000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 12219116 1250 12217866 12217879
    0x20c030d060e01060e06090402070606031203091a1303080a0f0216020a05010203030c1905090901170d1b0f020f1c03020c010309020d11030106090f090311030f0403020d060605 77
    0xe415812406400e40d40314580400011000006880c1e00c500700111251000410040c5894001000c02000c0c2d08004c405a50403980e5010000024903c00074042e00f0700c203503440110307000685040901e0006507800344541e403013000e1410441c102c1b40700c40346e00444c41d60508105410340c50758135400000708158003401c010a840055640100038100349503207446842264003034503803911500126128002543ea5001030342e13080c800a1280d280401d20b40740f016aa6181c164103181c002c80008640c5182070b0310041034240120000d0a9600d0180031035034100380c440c200341600380c608803212403440084441c05002200280e503003008540e9402903440d058480100390404d1070648803901ca03001c1c216000d084015124201540c0707099406806444a102e400510741211070041e504c50303541000c00a42420743c0755685039000714008100e8415a0191542c203440011100040d180c054032020003034505400d0380e80180300c460102211031040790f041d02d034140c4d410302099055160040160200b50083e99000301c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 12220366 1250 12219116 12219127
    0x307030e100e100c05030103080a0c05060c09090f16030e030c15060102060f15010c060f0504030e1009030b060d0312020301030506040201120903080106080c04050a0308091002032704020c03 83
    0xd8000b040a01521000d80310000d45203000402284c10a60465000c40c105000400101d501c100141035041c510b4100594044641e07a541707800e2078000c40e40c1e134400c24004220344e800c501345a2103032139100a4103240c07001c0a0a10311035501489260303141c19000c140c5c6403400d608481e0000c0c02a10328a150040440c0d0810803c480260340032402200c1e124014850900003a60f1030b000102094068051880016842d200c00070046a041c0d68048d800c1c0c4000380c031b5580820404510b0720a441c4500c0c06652002c401650001c1000401e250410741d070010400034090600c0816182668103130041da0840b030b98109070466160a0355100185038609211610100001060100125881d84550b201f42c0e039810b54007400a8168049445c1c007140a00001c5c00c050042c05100d025102c001e8100b5401441182826a110000ae4440f81581c1040343c9201000c1101c55140c10101601400300d800c90002d1030500c8040e000b0307410000e00c0f4040308646c0c460340c041ca5915a84550b411604417140010a4960f5203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 12221616 1250 12220366 12220393
    0xf0b1e04061d091908040b03040c0509090601030b0106020a031b050a050d020303060102011b05090108070905040c0306050907080906070c020d1a071202090d0204020306030309040e06090601050f1003020307030e 92
    0x542d04880b010380d58001c4802a180c401120034100700984c0c0c4c4108a20b08250808103140403681000300108d50f24010440013280c10340d25020030360300c00c40040c1d00a00c20f640c19881d080c461510180e100308103541c4101c3d0000d000039003006880001a81040202c0c0912801d030900620b8500106005491802403440b0f0b8003200762301100841c400c0800b81c00a22068801501e42400d1081d80c414960000340300307004031111903114410480e0468024905203100c0b50b1200006412101a406000d01107070383c0710010441801c0ca0000550700000d54140f1a21a15120480c0c40d01c0e0342008098101304502c101e014011540c0c1c00e0451001031741c000399410600600030003040000f21055481e4400300b00d007800054240100ca00860701041005400e002030301c10a64280400394102910380e0307505005c180130340314032030300c662007240c0800c519907005000034189000581c0c00c260041c3c100501801c0c00f20070301e582c0354480d043c0761447c64a9a280040c0d60350740d000c104400030911542d0f0f00350980905419109403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 12222866 1250 12221616 12221669
    0x102070615060305070203030402090703050901090203030c01020a030612050606010507030201021c0e0f070b090f060c0607080f1e0c0306041803111005011a0c030c0601060801090f0b1e0406 83
    0x5940454800304007170b865400c3e0683e508d010440d002940103100320005440d1511a801c4180c200140b0000400d0241c2c49500280c195009070445490a80d408141800000e6240c080d40c4018040010003d124611503101c41c1e807600d0004081c9410b20a00050174800c0520075811102006044003592a80c03114640004019002400d01c2034490b00c030390421200c220310049003042c101c0c0c04040440e8030705502070b01030210103901c291060340e12010510480f111910284003040c4640d079655980382c400e00d09a00c0c038910800c0c000c0d00e04420500340b11103940c40d1014030a80f079078200c46a50719050b00ea54401002401400c002c000000344119210100410140c00100c6000384a0400c0191181003040b071421204440c02481110000703a4040c2200d82d66041e1a00280391001e4034030192480c7c500180390380c2d40303085400c2e401540060401001001200030300c0c8101800100d940c8001c1c081c8003c1803001a58655010710200c0c02e15901c2222444e0030342e12507000000078411411441802d4681007151143c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 12224116 1250 12222866 12222869
    0xa0f030c06080a0b01020c0411041703030609130b0103030e0d05010f050108120705060402060a03090503030f090706050405060306092203020f01241e0f0b1306030b0a05060c0102070615 81
    0x301d40b104011612101941c05820900303c81a8002c00c1507048840403c0090310002200124402040001082c0e410480e022a43c018411300011907503820040c080c00360400d0014404035101d211041d03100006051304840f42e0440b5054600070301e401d03420300c0000d90035519200c0000c00c3c070762030159581c40d01070040e040782b03040301c0051050341e240000c10b680c135402d20f21581c400182a03030040c00001b00145444405070000d040146000a00c07524503641e25455580300307840c90030300ba014650410041e80c108002d008082c200d24500b6606141c40d001c082080c5002c0a010144507000840004441103411104160b00b10000c00c81c03031428441c2800c2c0651203403030544031580710b5402d00e015044403416100e8148450201c80103017402c45440e200034074240700140d40c03140202d1100c0b050000b60300c41529202a010704420001c65540c0c0c01c0d41840300c250a1800c0d44490241400c140010400361ba030000b404045400a64005550760703601d100c0346009125030700009213401c5c0382826011410454011860 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 12225366 1250 12224116 12224129
    0xe01110a1205071818020c01060303090f150509010e03011e060302150a09030f061404080405090f0709090b06070501020d02030f0a0207051e0c030d050a030b0108010b1204020a0f030c 80
    0x707543c8030418101c824004148103814108480c10082107400d054011200a224150100600f49450103251310700755031650b4410b80000703811000620250100300c041000400b0b030144032110404600c2c0b8040c01a001c2d1040700c506201e0740202c0e9000503102900808903007803190800100d00718003490710400a0506020982c014407811540724a580c280c0800c55000c0c1000791502420686180d40311451006010000ca8000380c590b128400c40706200024507001d6403091142c65110b5003000203110728000300400c0c44032003c4210052122540c0c00c20050f800392850100c011510000440101d100c0c1d22404e040205190710001d40650001c0c100d80c05580168010642030001e40c90700401d810583c01a04009403498001200d001c8011780c42151002141070408180d42201c010700300028148262002c00320040350000071019a1a503042c415032000080c2401c20a01a50400b4028102c0d4061011031603440c40710301380800c05641c1d4110706c0c40020010580c803e426a500d030b1412400d039070b01034410030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 12226616 1250 12225366 12225371
    0x906030b0409050606060f040b030106020a110105030f0601050306030304080312010302010f1e050d0b0603090a0b011a0403020907050c030c16050402030c09040b01090503010e011d0d120e01110a12 86
    0x1031089240c60701400004540050041089440d40410030031a03510201e03a0340c50001c810031001840015900280d030081011381c001c1c068520b035034145114001c1d0b0300500e5070704011003001002024a5070281250304050700f0703c0c0035a00daa0303c02000c640f940c46a030b04089040c3c8000710340f40c0208105020002e041c2c0b8401e0b41d5242e44098042c40994100740c440100652125510113810307001482100500580d50405502245036500800814941c0c2d009843c103800036041121010240054540e1650061290200d580b2100000340c000035001d00a0f800000d1280c2404030214440d584140161007980c1401e4094030b50704c21000c1c0400703a0b03402403040204a00740240800055502c0c2038801e4078850741003004120324022401c4c0400000f042c0d86068503050065000b8045040d4400741324590324118a0000024510903c14003071038030030031081c04c2900a5100c420403040640e44040700c0c09981c20400c41c00300300020910000ca01400103004040004080458039180f66a44171b01c0d101e960120f6003508 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 12227866 1250 12226616 12226631
    0x3050f0d0504060309020d06050a0f1b020c01030b0301020c0610030c09060515090d0507090902031002030402060a052b0203010e0a0b030d050c1e01090209010902090108160c0203010903090603 84
    0x55510340111400d44030100c0e1090004101d03035402034000c02c0341d0a10082112010340f000c0e954410450b2402c4d654034085540d10140021380340e009210740b091440030030b032461621911000e0025545d00400200724101501c40c0c68007903040e02c094054504c00480041565a50b240070914480c0030101c40c4800e98001a50100c0012603e02d144141400d4035000341070159060084051505964011307000c594001d0840600403011560234801600901846000811341e2441801018075241e00c6c11070310030001c0c2c810001e0200503038603e4116040d60441d818115129045440321200d42d5442a081250030340c1090100880a41c80c2e900440c10b8811550014070180c03103004a0301e04031254412210382542c818107004c400d00c2d02034400340011100e00c000311200d003071110016001e4030600100c0c070074560703443d00b68a07004c61429154807405442c9201c01141003070000d000013408074001034841c46000c1a000100444944121928489283c0180003400040f405240080c22403182d8860306000074600602c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 12229116 1250 12227866 12227893
    0x30c0d050c07030308040f05061f0608060a0501080907080607080609070c02010c140708030705010b0111060708040204050601050f13080106050a060909020a05160309030b0105090f04030c020f040f05010305 90
    0x15505000715000c028041c5030305542d02039440c1c0002510a85114007000e01d501d000031810002c884c07152840714404518115080791104030310003d45c104105101e201c0081100c02c0c3c641e82c044000700d46091800c18050b4844242c2e60b030801903190050380c040c2c0a03000800c41c603d500720000724044c10701651b000c85546c2d1003400407290300311700344d81c02030001d00207444503008200c00304035003c81103041e502500d64180e9100c442c41c1c03840d44401e008071400d94491040301c2c0c8940c1c000c40f100e10b03050012009450549402c210041c924180200024070035569103001c103005911881c251000b1040400c80c00760b80d05520300f034080360300120713102d024425802d00c1004910760a10f5680d600807518a603c50040150800018078065003003103400000b0440c060028a8006142c2000340d03d41b140261141b113111400d50400380c09604050300b0190141002000b44241c6401011a05521580615055120400d00d20001c0c1d0361500c04894558403038100804d0107130703a2302203a0159048034401e000310307282c1d64135014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 12230222 1106 12229116 12229127
    0x5033c060612060613020703030207020603130b0a11070305030402030f12040f09020301030c03020f0112050a06090b0d02030307031d03010903080702010e07030c0b0a140a02030c0d 79
    0x9051040d9420003002e6030384400401c0340606810b207011408516440134450610f80031590008400701410300c2907043c1e0314190381c0108030710f65900701014001142d640780c0b10242c46201c08600412600c40b83c40c17292468104084140398104a00f03a2429112500b0080060fa09409110108080218207100505440c40b0208006481c0c90a1041502c18114160400b07001e00c0d10400062000c603050050640c1102e03070480e803c820003030400c00101d800046407020812841e040009100d1940b005411003010364105900c00c016105085082006286e0f0001c00690190002c00c20f680c040392141d0a1030300307240045245214014201c2c1c000c00d00b11881c10b0416400a8481c400303010003240e0a01422821154110040050300d0450700c0340b02840c01c1c5442041000980041c00c1d001203401181000c10703401d01c03c8540c54a4041c0024003070740704d510242c0c0c0b05a040c0110074100c504203000c0c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 12050366 12230222 := by
  have h0 := BRFrame.cov_init 12050366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12050366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 12050366 ≤ n) (h2 : n < 12230222) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
