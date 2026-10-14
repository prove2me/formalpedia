-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2510
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:30.11398+00:00
-- url     : https://prove2.me/submissions/c8e1deb2-5a36-46f2-b04d-efca390ead8c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 451258992 ≤ n < 451438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 451260242 1250 451258992 451259023
    0xc0207030804230303031e062205010e070f1b080c03030406020c1605010c0201030c0318110414160c02011e0809010e06090705040e100603080a090807030305040e0702 73
    0x180e544a401c00c101c0040388903c50142401d00200d80d0005140020941e442039000002c1119801c1c20320240c400501c0001e0606500400fa000401e2461080d080c2c4507548a9440d003000225585000700c48000c4120240038407003480641c0540a0505901c102142c400040e458400c016400107840c120400d07102d45d1034640b5903400080140010428070fa001046181d01034012186c0400201106401031040d52040364007148030b13442850300650003038102e1161030072203050000c1c814030300e031050a20040c012542190107420700c54401146192511400d940f58900407840785440c50a1010b00f06400d004900ca030041c0070f034540342e00701160310076460a07100503501455490110740e03244d0050148070040d07030400525401c0c4048003075284000640d032842041d4810007840f0052803c0d017403000070311003114241980d0041c40c04ca41c900c0ea03403900540004512400300351b9514140801d0050214143c0d800100386500a2001080860740c09070031b55040d60b0394408450440d071940309040e4682020321081540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 451261492 1250 451260242 451260247
    0x1406130509040803040c0e010b0a0e0f040e010b011409090601120f0c110607020a2301020405040507020604260301050405130203010c0221030f010b090a0b040e0103060e03070f02040c02070308 84
    0x2081403c0d00a1800703184580c40721038401d80c5a01188450700c0c0240a0701e00307035040510401c81c24070320030384800b04040400f510403540103034440b0101e0140d40d40116440100d279100d040300751381c65030b01c0100d140036049224181c41c2404071850001c0c03000f51028040b0350421258480703904074040180e00244404400031410400d1003035460000c3d080881500340c65605005020010350030a002091200546500010110482070715009500581c0103040e0482e0440d0f600b40130204050f1110300c00c4500940c01034000f80701034901450304003004600b102c5001c05800c1070010b080248100d1a003036a041d0344003114049510b6881044006500c20000342c003030350643c01c09809018450f00422100d41081039181d010003004d211000d11640c0303110580e2a400c0305580100100140c80d508006170500e2800105020b1300281d40b01c0a0b1002e0b03800c5500000c10700254034004108000c8144561541e0303400302d1700910706103400f540300d07418424401c4401030f000e90748540c03215041c80e2091100b1005150f10590554 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 451262742 1250 451261492 451261501
    0x7020d08090a230a2c090a052401060c200607060c0305010306051501020a0b04060623100903020618041104081608010509060c0708040b0f07020a0b041406130509 71
    0x2103403100d00d08281c4c0c0542050480803c06002c10070000c0100300650421080407010720400604031000108134210a0181d00c0f0118000ba0007400310000c000541e5404c040070380a4003214003029141a4021011701c081c1502100c001500b40ca048034541c4000d50810000405400c00f1901c64030550300c0080190340380c85408e030351003501907020300d040e42d0080707104201c140da40812200b824409250218056405803001c0c0b40054040ea507009d83c058070481010a982d030381d030100485006901c01e00d06c007580304102d9030440c26061a146003013559409140000c003940c959008038100e4821103144d120350320b031001d0103400e00f901c85400c5906100c144075405c0340d4990351403404d05c0c0c072003540d450826011980c8540006802905000e0503000300200409490039854140c075505055010150071942401305110000701c0b4004e88002c0c01080d091243c2c5280d691000c0c1c4104031560319079401881c1c070040d0500046c07005d64584920900c1400003901e42c540c1c1e9480c2da050100000041e41e01c0141c1c4210101c0800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 451263992 1250 451262742 451262789
    0x3070c061206050103020f120405030903010c0c030e060403110d03031b090e01080a02090106080a0f05162601050112020412110a080f15130b04050d0f020307020d08090a 74
    0x80e0194074218404110081e01d42d001102070f072041c8541080c02120500942e4030408408010540040c4a00d040703c0c504420389022a0030743e12242c12920120301032110305028036420007045001018103d812519040c00c40d5502c2c07202ca20b15803450790080445000b8032041600951110302440384111208840815144c00100031003418020040c180e0500300001030f000380c0004941c03403160f6008117400310903828140116803040c002840401c1194584408200c07075140b510800d8080d20900c455820b0000c5e0300440035205002c03002ea005800940d0b20504103480103203030007a5055a80920b003085a0264541184c0044d01983c0c0050b23110a0344a071024007040280715420045032001d031000c0c00540d54944215460b400001c1034010a038220001c1c0c260480b01c01e001403a44507180c0940ba0307007030344659201c10030b102e00308840480c0e50340d0010007010310f010b40100c2c1500d6128050702c001c62a048159000c10200b0b440942c009154200100c0e1400c42e0380d503024220700240444c24100039403100c2d40c80d0703035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 451265242 1250 451263992 451264007
    0x2d031006090c020c03072106020c0615330705030f0304060c020304150e120607020f0105060406030f120314041b0b2104061b020c041b020a03030b0303070c06 69
    0x500303003464a88200c1c02c2002c1c0c0003040508020100a010342401d514105c500010b02c054403a08008440912507280001105403001d8902a02c0303250081040b450016801503012211328042445018803104c54410300101c5a0a40e054440d60308030b440307800b1041e014121460140300c000a0142c003020840034241c0c210700000d144600d0040100740158546080280d0300c0740301700c0c006c4601c04480d45002c0941d041c05802802d0101401030003400b6401a0401224100300090303601e0001600710002d8092104005d008a540029040b9010003000d861951031074407442103440c0040000e901c01d0710300302031035009504c9400260009075040e28140703000c1c500790799003200480d40c20041001d01c61002c00d0f8003020605035002106200c07001103030600781ca03564480c0785d000240221086511740141c50342d040442000444850940d40040402000364010041070302c8030000180c0c2000d4001c0c50900c0665030000e41c4203503658160074005503036145200441d06510030300101420101c0040d0300010b07401d5000d01e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 451266492 1250 451265242 451265249
    0xf0f10020c03060f01030305030f0c070b09030904050c2d070506010312020d030510061805040609090b01090504022d1017070c05030a0e041d061008010b2d031006 71
    0x260f400d030380c0d140d0140c40b160a8081c00003600142d030030310010700d21000d4015006d81028041c5000c0b4140216983c0d005120f0368105c58031003060700003040380982c90415001d6250402200ca01c1903082c032590b00c2c00b103030300b480d81034032800b11b01300c40440e20201402c00801211066600003050b141a50b031241418500c41c100410346078014401d00c2d941e26080c0b403007803081500a4200c128030b1000940341140444503007004801e05448001000b0b030000c1d0990f564800d41008018100000c01c900100c0d00300009124030503405100860300b00810040142e40d560714015104240f1814580c100241611a0004072007901d0f055400072525928003100345d0b0048405094013030f480411400c40e95507c801100c4024001800410f60780c0709124040d107190003905c08e19808640070304001540b010402c0e0341c0e0303104803030030030020120740003d001c0c4064100840300446c0508080f1009000c081800340106540c002c1c500040450b410725003c461220010180e925045020020212000782c014404a070009007980d10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 451267742 1250 451266492 451266499
    0xa022104061e02090a0b0d0212090c030c010305061c080d06060509130c0905011d040609060806010f030b010b030c12090d1d0a09020a09050a0602030406020d080408090f0f10020c 78
    0xc00820402c0c4241c02122010200540030b544020319000c0010400d40100c645203003003540074018031910f0b140c210300c20303481100040c1c018288000380105042c00e20a21500050400d4100000c105c016107070441c20140c0c02c10021030801018800d8200145d1500416801124840c1008000036807290f02c10017820081c201100d003801110900045c50040f15515405c280c08180c20040801c030320344c0503005d100d03a00c8806085144409000304000343c00c494050f00719004d0b00d41e60341c2c1c043c000c4d03800c02c202031030150510321143e014103421512111018101445281d070301e4000040051180c490800c156030038040c582c44c07030720601d040840b02c4644920041d441d032400500f081014010369000100840c46c42c000207800d1600041c2000040c0c0d010b58005100c080c01d001c08060001a5610351108007001448254003941d00c483c1000d00003814070403040c031a8820440a20240008948003200f00e0728104400c5030700c81c0a003440b02c4041851210b07464031f0264401a4813044044803600400c001d800d108044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 451268992 1250 451267742 451267781
    0x15060109050913211d0a050409050f010e0c030303181515151e0c011103010e100602010b0a140f1f020f0102160b0c04030b0a060602061302090a02210406 67
    0x255180303001000304040000080030407031000001082900305c907640c00000b80c00d005915869402040036508641002c840c50352186e2507188101f8020720559011405900182100201090010b0b903203000242105503200303625051a0007010040081c0c038900015040c0510b054503010900124160180654500072110000340d013a02c1d601c2a81150006c4010301c2141d01d0100d064101080030303802800040001e5980e4840034080d103802200518000d0415010b60110340c6800c19a40d482c01000e640b005041da070421454041c244d40b44221a403c0e40e80e500d011081028110000881e418400d505623500002403031041584101100c130b44101c150540d8086881c0680d03076001e014200c1c030521200d42603040d00d0091000000b48603510103030304890b0740300d040350403e6100d488540401105a030b03d0340090b175842c00104016901440390030f81c01700c0c101030642542c850580100d214948010300d603c40c10b80e03000803211400d140502040311000201c504a43d240d02c1c15242c00360040c01d8902041003d070180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 451270242 1250 451268992 451269023
    0x91305070906031b030b0703020f130e190e1e1015050301060f03020d080c1f05010f05103009080c190c0e0a140f1909030215060109050913 61
    0x41096201146d41c0080340d01515a03d09800314025003104000e002e404c542009000c1c44c10540301c2b02c1d80c0c060030f550f400302c002608240d43e8214000c0d0325a40842102c606049003101c01440c0410b030496a582e41c40710881d407007220200aa0b0900803c10f044101440c54402200c1d50100c680300001e060312021340081040b02d0304c950204066018512009600009000c03c2d800002c0c208000303050404901c001705c4140b02300b88400d0752680f00c0e44182c103001c0195560010131030340501c01d44c49401400c1c16201001801d0380c00d0401005040c002304443e20503e00301908480802c04600400010fa0040c4801c02c00a0000d01d081c200c90762107030307200c4100352051001d00a00c40c02da800d1a00e041c55070101603003e40c5854034070f0304100440014100011f00c1d0703480720100a20060301803014403400f906241f1207254504002035000181400b2030070200c05140c40103401c0069000504141e801d001c0010300112a61003900407500a08181c103c1e07908400028203000e2000800c60140103002d118402d402c03001e015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 451271492 1250 451270242 451270283
    0x4080d0e0307060e0a03120306150e1e100c020a050d061b030c020304090c050418050a0507080705070b04050f0a120f050a0804030c02040f05010602030406021207020d0209130507090603 81
    0x20013010160b218904c40780400c00181c40000e4032040000c90300740861038a03580d820a00c0b0215080c002c11020070090001c1c01700c10301c0d03d000c903c00b4008480098500c1034000030041000c0d50222040710050152641040c1c2c107542d070b5040314400500e0014000d1607007080514015010f000c20034544442242c2c031048090740e843c0a0b02802580303441075030085041524100e40c4402034083c00d6622424400d0400002c9003000c903100a0017580c1f10411800311702410703c0c0a90340b085400040c900401c115005003032010b101d81c044102e862194010752103604a80f51424081d00341304001d00e102045118005000d41003080d11a01c40c19011000e845500c001011210706441d0342c03051602d06000a6480000180003a0241c4a081d50050000e00005044403c03100480110340b403e8200300090791020804202c0319070b04012401c6042c460311041801d1454903130102d04000320440000340310300b103900002002e40c02c072040c05081050b04101211146552080034400400090106850303401e10401d03a03250240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 451272742 1250 451271492 451271507
    0x151e090b010807050a1b030c02030c0108010e270a120215040812190c0509100c122001060306090210020f1e0309090901060e1008030a0309020604080d0e030706 70
    0xc06846204035aa0384500485055025412a00500107041d603401c040089985002d42600d00c40d441da0b00d940705480c0105480c00315030740c4110341001700300700c01800000d4608800c290040304000402c5ca030300c00c03000c0601813545810500c2c1140ca200d003440050500c06444403410440030130703400752405401410300030307112048111000b400c07500703081103030403a4102c40000726a40042800d410490300b0801010550561315442c01c602c00140d8041342026480c681407601d21101c00031810100325010b03d9030313203019400360007120200910204803100c8400e034a080c82c411010700b4100d00200403454807480e1510080c2803100050380030303040d07040403544124000180c82c5c445840c003200604130080102500551075440b0224a6000c0c001440407810035103a00040e01d0240c540600003060781030403c4119454901c004003030320314014030001b0400640c58040110354402c07225250108a030491800800e42a124540c000002071080c150501d000641c0546041aa6030702241541e20703081d9905021544003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 451273992 1250 451272742 451272761
    0x11407081606360201260a0b01030e0a0209040503070f060c020105070536040c0201021902031e0901030603080a021c0e01140702030f030f2101030c0b0706151e09 71
    0x2d009409942070301c0c01c0d01d214065203484c0305141181c111030f900001108031000b1406510700303464200741400011040d901403040028401c2ca070800074400300c440c04598481030840081d0140c55018040360601805008a0394101c2d04203108048171a081d140c5100107204580900e4019443d040115002c00d101d0002c441001c1468201f4440001d51410021032104c0481d11111a5007500d0100c1010751f2158041c0100c0c5814075000107888210b2540380743c410b080c81407440c50464208100d003d0108800720a42410905040c992a03152400c510060307000300a1034002400b000c0c0b021400710310160340041c5c100b00710100d0116202440500001c00e0380d07800013003040c00340896481d02d845040002d955001d0500030740018100c950b42c10220441030b0640c1c1c450b0440201c40c250003d0050b64034049060300182c0c100c200000702c4541d62440d11002c060601501551104141c0005d00105014194000d040d0181011400601c0240e590000c01060400b070034400e04040d0200d040020390410b107216001c0b69 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 451275242 1250 451273992 451274051
    0x2808040b06040e0718090c05030c0907110f012d0b1c17030a090314030f18031201091e05060a050909100606050306090c18011407081606 60
    0x35403034181c00c2102401c90b001d200b15940c864880700040c1102131403540d64030566034540010b4034014070b0801048171003541c1c10080c001c1e80300d591003a6042d10b4010b8256030041301440d003c40c00581c0858007500b001140e84001e200d039230910941d855030049800c910b03011000101009181c4442d07580f4004156086c2014441c1d000e1907100d1641000c9958240f2184260b1107181c100d44442400c400c8000550410b6945c8035900f5a01c00280041680282c10600240d003105d400c03e054ac5001100380c00c03002d00040040c41d005540652003900307410300b0020348803070404040c1615107035078469100c00700038008082e50306030102010030100c0d081c00561141d107001d80005001c0d409990304050a0044080000d400e600c0c5911805405070700000c80d038800c5070044c00c1240c0e2060b41c3c0b410000100b020a40c8040c102241043c0c0400c0105071100503510741c15041102030810030f520fa0337114036140c28075010700c48c005841c040c000100c05100300e9040071142d206620a48041120350002d07041c0d811001070b26008841c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 451276492 1250 451275242 451275263
    0x5010f061205070b0d02040e16110303041e0f0f0b0702060c071a0705040803030f040302010b090919050f070807080f0d050f0c0106050409060507030e011b0302180402280804 76
    0x90b000280041000007811070000d4545913480250481140c805c883c90074020602034507511900ba40704460503425001a000bd47c00c50405803151095445291641800800c01c40f81e402e040110090760200040c1d003000510880740703c0d41c244940c400e00211041d40050049200103522003181c4001d031036034540c0010032461001c19113200d40c00095006050502801028000000d0b1164208010343c0319a107888048507041c10185806825078045220b803c0c40341c9100002c0200c2c5000c000740018410382170100c130401d500c11500345079081c59596240007445010391030001c0307803508000075400105e031002000c4509030341e211006152140d50a103030303e0000030000c1004c40e00340741c06640134241260b02c0c0400014541d40e034000003001c466850004031a0191182d00b0805d08503054400e40c2080e003448002070106100158502c5d8003050822a00000c0c10b0340401c0c0d0724244100c0030224880c2078800780045594509103c051440308000c0c140350704500181990f030319482841000a28015130b800310045e42e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 451277742 1250 451276492 451276499
    0x150f0305091c0503150402070c0602010b09011508150301180b0c04080304060f050408060103030309020f0907140c0a061515050a0206060114070f0303020c0c0108010e061c050a05010f06120507 84
    0x70b0f015070014101012002014204142a0b44c9520003010011311a03440712061929041c000790a43c0c40448245104000700c0e8010040d034101c3c520a001d4020741d61400103600c0ea204407110784158151450755406620303006c0b65040a903807500784000441d003d5105070341d1581e038005000001c0c0c4203e0003402c00a42003803008100c0540102010321244007242444e904154591492514044099001b44e00094070b501481080d0305008076001580c560640e0010168503000a0103840e031400707803041f800e40c500001500d512551090094043c0300740d0011080c00740c5048150745428000c031a00801c14608240411100c40b07500450803a4a0807195401605003996007030015181c0c0c04110782a06a01c88042001500050710301c0e006131003191080d01c005031580840401545821442c0c052181400b02020051019008401c0d00e240d006408603110840b903200540700d603210600b0400b00810074483c138094903080002c19007084804645514040000a83d135030008600720039a19409081504000720a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 451278992 1250 451277742 451277747
    0x2070519080c12030a0b030321180a0803010e060102150c0f0403060f09030216050105160f0209070c02181501111614040608030304021e0307150f0305091c 68
    0x81880c90064071000c0c20250b045001c03030705005003142c89142c0c4180000400c050034100c0d2040020f603001c00c2d0011b604044000748a40c00d10300e0400c0c0a0f0300c4120009001412005070300c11021120384120090b1090000303a4030b00041c1035002805001104081100080e8182d44000744610315141c8284c021000c5446410450900f68041c45001c0c0700c04900704404808581113006510590f0401e00b400100d20000e420000e00345820011640030a200003641000b00e40c0c2c0c44410b503031494603e0784809803075882c3c03840c18190300d8680d610000c2d00450f48408104110390050f044a12440c003d9034844280e0305104514841060102c40b170103600c40039911800065441181120a00841e00341107a140c14007642c02008440c05c1540150429440c00340d00254508090140400a1841c20025421400c280e030010f80c06003044110081d0158017030b00b2501041d0b5080017038000503e0b00c02c0d40e08000d5000300030010110100340009001007403e11001c20300324000000e00141c3c03c21990400c50b47c921401004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 451280242 1250 451278992 451279033
    0x209071b201216050103151703070c0e0a1104150e120f030d0e01022803061503050105120a0201050a0f0c0b0c0403050607050306030a020d060906060803090f04020705 73
    0x242280c00601881d2414582c80c1d03030146600311850203009041075007419041c5005001143c111a040500702440500f000076071110711ba0a40b9035001701600202e0700c084605181d400b89030b00c00f511784260810f000420518903103a060007070360b913220b0a010400c83e088070300400b0301c5a4418201d40c5180f111804504500c90b064400440e000240070341400d40716000c540c0e18000b40c0f402c5141c1240c000149281101c10340384a003034001050380e0000d5081c03807d124203200c40007488040e6034030f0080e080c03004081054400d900450181090140c910361011481d680100100b03004d001c0e50780610020412402c059100040004c99568141d540d2441c5c1717404180b0441d80d08072492038420134404104410b000080d00d0b401701511070300030079800c039441d0352541c20030301c2c0391010140007030051107403c0090164944011844512060b0103540c070f10380c955944e01d06080102000c090140015152070b20100300c1410120050a00c5842114070003880f48000c1e080000300e10440600420503030201d0bc0742414032500310308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 451281492 1250 451280242 451280273
    0xc020f0106080c09071209080318061003030e01020f01050708040201110109120e030304050d0f030e0d0503070f110405040c050102011b0c142506030c0e0105030f0a020d090305070209071b 82
    0x404004030346800031046d050307583d102e80407030301c190020040080e4001c9100c00781280356081001401d1170b0030901001a081c1d52070703020280070001c1181d1025610390007007000005c03c1084e54003c0181c0e2800b4800200200c0382517500300d0004031050303000006a0b0050049019068100b642c0004024003c0c401b43c904441c000d004607010f00040c000040e07241d44a44050304054090001802606640e1800a200a03481001584280283c2c0e4100010902c004261445564041412810442242814201d100500109541c041d0408040100308211410f000c403c4600a030000e01c01090141c00241c03054900c1c24045000440b142d4016010450301e0890300c4400318403070180d80081000f81900048034800541c0d2403c0000040e00800c0069403500c078540c51248140382518a0401c0f01d4002011403001034000702e080c06003180890340b16101c55040300d00240a080c410010083c070b9160180c10b64002da00700b68410174190000800160150322008038403103c00210408060495440c4221900c2049 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 451282742 1250 451281492 451281497
    0x20c0d200f0a140f060301150c0c0f080d080f060102100b0f190e0601030603020d03050c1e011505060301050612090c06030a090210110c0d170a030c020f0106080c0907 73
    0x1100100d032600d46100c1800906900f10104402d4058041071081c1070308000d00640c042c0b18204010000101c80c1044011000b0841c034080070724041506120b14290f0094000580e81c041d172403000529a10001000d100e0301c840c3d9168040580e56281c00c8bc0c0040c4800c42e00107025030018001d500095040780d01c03214560000600704105604048003151030441103600c0c1240301000000188010010702075802c1d0300040034030b420312401c0e0459001c6080c0403048980141440008209070003001c4050140303406031031002e50325a0020420403815406440342c2c0305041e040003803404003c9a135040040449058072405000301c3d1404850342c85040f103c1c0c9006103281000c0c002c0d040580d0301540c41c81c00543c020842c1032804117012003039004000c5101240b40b03034007050028208240c50070800209039050000e00464095508410900740307510f85224041c3c0750140d408000864001254261703000c1c3d00e9030000d6178216602d40c0c641480c401c1c22600280a0800300d0b600040c0680c003186002c0b0401a131054152 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 451283992 1250 451282742 451282759
    0xf050c071802030117070f140303091e0f04050f040323040311120d080408031302030a081b0a05071e320a0308040b070602121303020c0d20 61
    0x10111200d9200c40c440714440e41680020041110b038414103601600d0701c2080000e8160700c0d04d00090329500e40c03c00d204900f0b590b1605070030441e00e030f50309100780d86c00d891000e4200c07200c94103005181101d2040c5140014440c41c6540100b111900b01446424440c06000318540e0003610f507a141560700c0340d00080c3c0e240b00f8800c92039210b03062152407000b400095101e84064160703a904a030400c09034220303005403103900754070403030454950503070040e2516045600034100d16940e03280d0240c1111161207501000c2e425110790003c0d501005800300007000e01c0451016001c0c414801107250030b4030394000000141080d40000c60074403600c0048254280000e01141861200e07944d00d00442c4030780307a1126000c2060700c84210050224104803940c00301e407220200c3d00c44110301e081d6034880d0003c1c0943d0082c03030b400420114600e800c100c2c1c0355040b101c590b0740f010941c240514009101010800703d18130101c005005401c509446820000c40300c0d20000d81c002003950606071107a10312030088544421040c3d02203601e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 451285242 1250 451283992 451283999
    0xf03061502070f08033915070215090d141911070b03061f0e0907050d110405010c0f0f02040e1014070816020a1718030a08160606030c0e010510030c0f050c07 69
    0x1002600021130207d1400c0c01d5502e001003019042403405c0030351780d0800f0f4501040000c05500400c070414051242c2c02c00f15000c0c9020b5500812502a10441c683c1540000c800210400c0d04411895125002c0c40100c070246a00c6042c50007080c001654441d401c8540100900900c1c00504080c0360036920519182001c580000d000030740e6614140c90540126000046420800c6051f0040807900c45100b000c040ca41450710000070a00c41001c48041c040c0100f00301c0341c10070011480e4a1003074240e00113106000030301900c010a6100d028403c0e051480c02d16004454070514403c0e42e203140308a003a40c9404031580e8a608504013448200250301c0110300411050800080013500c11818003038103a150b03ea181c24a080c840c481c00d03105100054800d91100c06a10002595041200c069209880f01c80840c4210751400802030029500020491344000e080810140b2241c2c82035812141c046660411100c9a4030f000d40c101e507594503803c40064402c81304803c04500400050920341c0d5100d04540c2e500303a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 451286492 1250 451285242 451285357
    0x1170a0b040501060e040f06081c02030f04090204360c03091403030106030c020703080d0b0a150e0f010e09220803041b06020d020d0f03061502070f0803 67
    0x7400d030043d138041100d20500800380d041612401c03110104011040021a0906200c1940d030350b04070703c4001c11083d5881a68070f59510900039a00617915a1300050789464840e004c50001c0d4000b4061802c1d500c1060284501d00044410710740c8607c954200311b4080108941c4942d00644080681c04042c1500c441400002030701c44240d103601c604c1d01d0703c003039074507035050a1004090303c0260766040110345c00705d030013400411144412540401c1c00c5a400042072000c180115034050502c0d0300c0405894080d0b0b060b02d00031034101d019941080e10464541000303502c032400644400005020030b07500b007c103c200061120305e00c030000240c00000e010008031010303039030390315001158022602141c81c054688402d55040e070030003c1c00e40203415240081d00c0600b0b5051030003599a12070b01c0380f4208100000c1d500c80c8041c0e010764403071001f4200080b68422030072039029000e507a4090034440c01d04080c030342400014003804040203a50400b03240c480c6075982d04c4040e99141c0101a0a081e200301c200000c4040010f01d402d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 451287742 1250 451286492 451286501
    0xe04111516050609010902030c0423130c1203050703080403030b0402040b07200607030e010504050402030a150b0a0207121a0112030f09060e06031009020301080c030c0f01170a0b04 79
    0x18070000c03141050507164940a8180000a007000b030040c0e05000c1d45100507500407546165400090f1390001c0c0f01c110380c0301d400c0300d008448102d00e09040307100014482c10f2418a00c01d54081c50040c0c6a204020b950344c06103000c0c2031b900140141c0081c2c02400300d040002c6c850700c11a40c00c50f01034a804030303001c01200002000c82c0c0c8607038000304005000242d02800c0007140100c00682101c141103071022151395201084446c4600f02d001802c202101c00c080c03506a0049050714090880a0700031501c80c6440c0e0044030042c03015823000000050b4a242c00908920f450040310140206540501961441e14030340d2580d190307084400701c4810f000b52404583c926481d4030f14034002c040039841a07031850f804d4100505484140c112180030082c02c107005204240c2c005424501d0401309640700c60740c0350b403450760424402c000c40d0030800604d80004000a8940400502c840c841c400440c01d5a0301d82a1b8001004200c0a46600050220b102540c01c5820581d00701481c40c3d2000790302c480885c031031807500f00050445 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 451288992 1250 451287742 451287757
    0x150106030c140a1701080c060f07060e010c03051509190b040e0a060507180e070e01050c01091101020f06190216050f2803020a02060f0702090411010201050702070e041115 75
    0x19502e81c582c000480c3c0300d4004c4078010030840025120783c15501012451500c95117030024141070000a0850811803141d001c19820441c80000300310b03501c038400000f0098501031301d000c0201070a0540308143e6141840c0083e00a01c1c0044401000d2002ca08481005c0c00e65080c10b00e61040c2e8900010307429503001e022080700580b00e240c00003110b00c3e20507005444440a07400c04c4400c1c00b07007a401030000c0380e5001c3c04190862070605140069254050049545210300440b1442c4d43d4289200d001c03c1050004207041400e03000d0b002e483d035000452202954944d0112040c02c0d41d44011400c8080f40703031031940105141c01d41c800c262101d903140c584410749407021003404003070130307600141c880c0c1031407c0350704810500020003144c8916400d01c070340c500943e10303100101d0191082d0800140140350651850846068560140ca11101840c0170300705040c1c48250080614055400d10001815242c0b0201d00303081510000242c541d940c0d11251194400411481d41c40c540015800401c502a03151400140000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 451290242 1250 451288992 451288997
    0x90f06051f060f0311161406090102070503180312040f0f051503190615030e010e06090601060c0206040b12060301060519060e0d020a120b0603150106030c140a 70
    0x80c0c0c10000c140070141140d007440310700c491100200a000c1107a0050654003031078424503010901d069034860084492080701d1050620200f500c0e415010130050781c00c1014100c800200356170880d900c0403021401d03481866002001c40d0000c20241d07400c40c856035030003100060040e0440740b0701803030003899141c40da0164008000303000e40040100a406a2109000081c00007658070282012651689100500010381b04280c0b4003684040c020030304010303030301000041480226900206840c013002400621194408a043e5400c14420f1400b441e80003401034000c5100b04000c00d8940c1ca090003c5507048806c0706c00301d038060f50070800011105030003006819459080c1089130b503c0d041840c205400c540300c41c5e210501440100d1102d0079010241e4185000b01e80303050a0800d032520480c0300058a00300403c9000354059203440d004202017540c2100300290360310038143e108139510381d07000b0180c0d103002c03042007007408807140303001408007500c20f070445403540c8183c6c01e003070482d101092449619a0000701d400d000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 451291492 1250 451290242 451290251
    0xe07080109080c0f0c010c0639081b0a1412040b01061b030806060f0705101e050f04020d03020307060e03030714090609010c0c1a130b121504090f06 65
    0x442c00000d206080014500314000c3c46000c0660700003804281901f0005002c031a0b845c04103c5804000d0380350103100c1d155480c00c5501c4040c4039482d030781c45d848001102c0c1001409000025594100030303000c0c0442e101e00c0c42462800e24080c98400c941800c0d6048031440403200c01d1080140e1381c1003180d5114051351042010411039814070070300030b0240403143c020903605024000c060011030f40001005030400c0701682c044e6a00c400181521025106080c0c0c014198440e1580002c2c02e001c0c2a841080e40f0b07240010108000c4500b5030210099610541d01980b03c050210041801803801a240c98500c40c030038010f8a0a2010701d03154142110520031030a00150000000c103c00b155004c4000001d12a00000c80c1d8140740d092008140c55000e60704c581418800781284074001d01012480140041c094503902c0195204002000e0305903400c014922036911040440c0400c1119804042e20111207003501400c0d620340d41e041440c0359110b0120060350b00a69541c041e0408124a181c511079400c1c0600b00104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 451292742 1250 451291492 451291507
    0x4050a061503120e01080a0c09050909010c0201052a09010c050118020301050604061d10080708070f050612271002210103120f050906040801090b01050618040e0708010908 75
    0x40d65003d1104240c0801070090002c2c07401d6038008801517004044031100003a21100031070140e40808007a080994006d102504124252005401280c2000d85a41c02881185c40761420b440c42d10300d118030140c4099420340c02c4a2801a4200043c2002181c14540280e618a958580ca801c4a0928020201c1c036031040c03141c40700b51f040900509400040c299410040340d494041d107600c482910b400d0703c03c54264103901151003442c035a48104040c02400c000d5a8032196140302050340c0e413032607100320000800e02c090b00040c035142000c00e661803101508070f00100e036a0381400a007c201031090610211005140c100d0802d545c00700400d4800700544d090041ea1406001600d946c40a6004c540020701c400a030300600000e0f041401040400c0c9090901202c01c04440406980714000d91050680045010800052914054201a0f0040d000b1a46001c0390303604da000f400180d01c111980c000740e80f5141940d0f08258101a4080c80d103001075007007594000394994034100d007540c1102409459103680440e409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 451293992 1250 451292742 451292753
    0xc041e0f08060907050901080a0f021f0c12080103080322140304091401061413050d080d29011803020405012c130b040f0f030302032a040b0304050a061503 68
    0xc2020307041c200e560308070310348c58003810035503410b04404000e01c1414105154011134451b51a0003224640440d20040c7c1c807001d0074401455180280e1060302c6158000102c0700405008803a4541030380d41000d0414690307515040c9090042c5050180042c4908041040c00d000c101c070481010810f1074543d0107143d0b654648013030401a500c3d012038001c0005940ca004206040d000300d090890009104103541c0c45c0c0400c0c07106207409048a6001940011110354014100400407004210824400c4420408001c50350440b0411503451104001601d2200405449941c0203101e04d40c1203485040644070495101c0d40400c0c19500b0a038066280b00d01c030000c46c402c0341c451000b06610802440045000c56103880a045000040e0b210b401800c0e2407400b02c0850240207020410341d62503604000d4505042000c0c0c5001002541700315420b84440030340d00340d29282c0d1444413201488141300460385904282c185803208000350300c0a40205d605d8410316004400017466030040d4107500a100138500100c62850410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 451295242 1250 451293992 451294003
    0x2f070c0b03010906090221060d0609120f020d0e0f061b010203040c0602160504021b010e0c010917210408060106020102090906090601051206010e0301020706020318060c041e0f080609 80
    0x80d21700310b006012010390f2410944801480b02040c6100401a44464010810751580400003030455414500e1400c280045800c600d20b0b0001c0c01c1c0e81e00300300072000e100c080341c503131407010300d4540040c4010881e040e1a141070400e100f0800d00041840d80b03000105c4c60409030380111782c110341e1010794021040000703110100301d888000f0450703400034040e02d41c8480b0b405140c4541d54050301d40b0030b03580425403000c2c40c1b65441e0071506042480000f0450086960302980d580c1007808943d90000d50b1181d008560700d140d940200142d588404c00800030f8240c5403003886841c030b0f2000080414400709120004019000700b210a0080005400040c1c2c0c400c3ca40041c403121800003001c0307501410191041c4523050b64000e0842e200c031400391040d001183c0759040101c0d62000302c981c590354590b00210b80c01c414004194000c6024054010b039031a0319942010200f5210901220342d40c0d0b542102f0300080201c0c00450481c02c0304000310b2405a000192503c00d140c42c000b0305500100a1984401e04104904108000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 451296492 1250 451295242 451295249
    0x1110a03051006090e01120303090818091501021506030f1e0f0c09040201030b0a030c09140f010b0f0703021507090305010b030615041a0406030602030f0a2f070c0b03010906 76
    0x52440c402800c142017017a070080d042c481c00d4a010320140c0030005043c82640103011541d401002260f4840120703c410701c51000d80c80c2c10b10300c00c4030820003060801c0084c4240c86039003207040e00a89800e0490080030a10618010b0009405006804c51240c8011090002402203912000c0f44402c0e98001c1c60b0442c030305602d212104034a5408041e541d079031542e49506080d441903092a002c207001c0c0a45000c624106050b134030007482844d5850300400c04a500350881e4840305041003800c1020b507501d41c014001d103c000e02c540c10010394104041c00001d0065030041801501031700480300c1d1150b410803101004d5404030303080d900140c2d03212424010080c00b0701400011301800c400900d0642480500075a414005000d814401d5075034202418840760145603014540900030810807a01c0c0c0c0d00d041000c00b070750044036801c0d000138410b000a85541d020b1f104400c5200d1121102c10320043d00441da404504c40480b00102540f503042c40032170b0001d40201038030305c083c01d0001081504ca51400c1c0703804043d40c46580 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 451297742 1250 451296492 451296497
    0x6020601060f0c03080c0903100e010f180b2a0c0c180907180f02031602010b06162009040f120912060c030e0f0105070905040204080c100201110a03051006 68
    0x2441c490120780c0c441003ca030001b0804803141d60341c10507071002a24080076000e030008450b040941c1c07891a10f4065000d1310307880c03031021002c0c4001c049074031040405d03403102d00d0002c088030041d0f00420600800044254a030f00029030341c0c184140021200e071420fa03084400c2d00d500b154041605400c083c289485140d40c03801e14401c2c152a0390500b0748902c2d864044500881c2d040c2c8400b0009803582900340e400c000c2007000510011540c0c0c0c2000000b90705080b1001460740c3c0558280b04103c403072030620364225400c3e08450019031641954540d258000351800007145800e584c1042200e050941d601250203000398464803a000c0703001c060b4507011040350b102d400702c1e07401d00440c003108005015201240f0006140d0000001848204110081d00144412111080c0620442d0b840641c1c0420550049000b00c0d075079107408101c1c80d80ea0042006910541c003600000c1e800c0607206820741e0500c0d4a00c190140d41d14000818190100d403880f18854200b8000040001d458506100004149102c0306014004c2072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 451298992 1250 451297742 451297757
    0x605010e1512100909030509091e01091107020a0e090d09060c020d1e0f200607030e0301330504050402030d1407050a11190e010b0f0d0606020601060f 66
    0x4515071850040c0901d41d84107076a0003000070f1050000d8a00304014280c140020040034001d070400810700d4214001e0b4600a100000100c0c91a071040d1b50b44203410b609805c2c41115607802c24440030050701030100a5110020103120850040ea564407002c1c1c09002c00d19410281340ca080364846184c41c085204290a100180400344a52a440350384400601e07015240114022030a1900c009076074036038074a0518000014522400b000301c84042024090b02070809480c240b281c280a0050b808500740b195076200c4410000342c80000d0245034101c5420300e00a0000a52005003010076404038200e28100100c1c0c400148406030b82010001c061001d400c1c1900c0800440c54a540882da480395024580d00c20310075040e100b1540d8400480c102c0d1000b907032002c2070b03c240d0368084c07400504a200908486100e01d12050341d0700700341c00081510300c08031350443c804201287d2901c8074444280d4414034a0400e00c2c4010070005110031258003c40c0020440341c7c4c014051903241c0386000b030030120003020a01c1000b129 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 451300242 1250 451298992 451299019
    0x302010c080f180c030d020d080708010f051e04050403030209030d0201270f0807050a02010801050d200307052205011212030507200d0915140c1f0605010e 68
    0x3038918959002400070100002010b000c883d551910810540550f898420401d400c4001c0f980840c0b01d00c030003410307a111a9019110b40001b6101c0e60824000d100000e0b0117460100014605000d04903001604880300d136901d82201400315080c0c9400300c07400d07404a600003441c604a420b041040e00140901e61000b080711343c585400e2440403000303078081082a400c841140c1018083c1801c0c00060847c0c2c0040701d01e0351000545405a201c503281e00b8240d001c21856000003030036091039102c4c034011035406070040c1c0702c40d8003880035485050101e1000a13018803820710085265128040003242d070a49095801000040044010701910b83c1600320385200516017034500b0000c0d401c00f001c05910401c50030080344540d41e110080725000c058802c40b24800e00703c01c9109150f45000300300410354000d41e903501001c8548910120103c40462110b00b40041c030f007024122058540c19014108500c002030560388200c0d07141201c15025078440078011025a80c50804012542c0c00c0039940041140603135011a240b600c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 451301492 1250 451300242 451300261
    0x305060a020a08060d08041508010905011212112d0f120d05040206090d0f060608030c0705010309080909010b0a1206050916090b0d060e0f0f130606080d05070302010c08 74
    0x1405045c00340102400060801800c40180c0b80034000c032010071084510000c000a040358006c0c032420403180d00d082c0001c03411503000e608a1380c401d5000702130b66071a030014640848055014041079072990090001203403034148807000342124289d034400e0070110300f102d00f600103040102c02d101d403030025808800944903050991055922015801d00000f8580e600d50021400d80c2c070900707c0560f070043c017162500e82006403c0394650400f83c0921000c1040a444010055491041c00e0044101d980112010002036200750025101c4c5407040824500346800c10010801a003801c0e00031003144c50380401c210018a901c2400c03d031500100074000c3c05502c0c0741c071012440c180c20142440c0c403401140c42c8101241c034040c001c180024480106c015a840b100350504a000b8255801240c003102c00d078070301050200c515058406e00480390340c10303040300703d40740c840c1c1c1d0000880c84c205040341e00c0780c0c0369240003558400902c5640421001c9440da140d4510701440e000f401c45001c62400307000c0c061418181300b03041e035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 451302742 1250 451301492 451301507
    0xc1109090a0b1e070807050d020d0e16140402070804080a1101020f0607050315010509030a03030c030f140105040504053f07051005060d0503031303081303020307030503100504090308010305060a020a 87
    0x1150f08001611b512075541c11290b900c1406818007035103000140e1620004410352000f5880030220b02940e441b03005942c400c3c8da909041e84140e900d4030612203918009440c1c00d90003403034481c1c40368107400c0c6420350754054039040c64504802a241145122642601c658042c01500c40301c10062024003c90302d81031740003608030301000e08220365614115840c840103901841c00c94104450003000c48104403600c4c40d00401801d00103040200007400e244070030f240d08229000e00042d2644144a0000b10303802e14084c4002450018000e80c0d5502c6080d010030036440d045045075010003000c23012140c01200d29000c140036003500c00c6400c5080c04003080140c02084001c44d1446022160000c080b6194884400240044000d0200a88240400024462a1640382c2c3c1c254850754400d486120b45a0fa50b007009005403a06402c025000d1780041205030006840342c40203592002a45606c020144e850f00c0100d421929850411000300e010704005000780441081425800607a9075401d42ca0301071070141c0109900c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 451303992 1250 451302742 451302751
    0x50612061b0a031e1d2d030708030910050c03040b06010f0e03030c0c0f0f09070e01050f0427020a141b121c06150c1109090a0b1e 57
    0x226808191840802c0c80f907001a04401c0c09280011004540d00b01103100500061100410707852018441c02c0584c0c0340410a94542141070f0300c0ca01680c0c1c0c280384200c800d00710303a41c8900c080380410810380000854500142d03014407103140080c141c013072200e41223404450014000740c107141ca09004110028030000e0340d2540c828820f00c1e21105d08490300009560402d502540c4683c94000495501e11070b41d800680c0c4140740004a403084040380404060100304880070180ca07170400820310006032007038091085110108410315200386000b0401900712400d4203e6040002c44902e00802d216080700682c0113000801c180020840c906070b51800c003e44410441d42e43c010041001041921031020540d07450b608640c003040c00e841298031007000840c00b9a0000c07540595110300c0c4410350f0601007003440fa032000e5549240004000070080344094602c46d041940440b8900b88080c55040700b91920300300a80142d0821004000c0118a0b10307021054070001400c586102c5500ea03024000c0d02a20010316400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 451305242 1250 451303992 451304041
    0x20f04021303051906150503150c0706151d060f10020f0102280201110d0203060d0210030b0a271d0a0807200d080c010b04060905061206 60
    0x540480c00c1da0308580e0611544003400a00440e035411000c604005208080c04d44115410400c50b00c45170340e444075083c0d250143c00d40560110301000e046900c91700d00c5075003104402003800c0c00c4c030398295607801c169240e9031900114501c45000402c58900080002541142280044100c9141640c04102d00200802c0d48034441c5c0c07659040c61040c18000d11074008840701480003503603201d00f4088039031114968407400402000d080c20b04241a1841031240c56080c0e074001c034440e8900419004802c0c0a500042d00305c0354040344003400303840143c0e25030856a12001c17a0303442c0030448105400802c8541d00c8298458221801e602e204234508140a20703071010009402c540000b42070000d411207549140c241591f0780e52038491010100140202880a0244079202d0340c9841240380c13001e43c213004484c044070400d41c0c002151800a40000d0005800381404c0300f80c0b03100018642d40d02c7d4001a06585195100802c81036039142440302c1e60070701444101c01d00c14000018012405c00c1c00140c4540300542260160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 451306492 1250 451305242 451305247
    0x6010516060213120f0c08031306081e091006140603040209040606050d08090306070c050a03080403020f010f020403210f1214010602030c010506100203040b0f0408030a0c050f0604020f0402 83
    0x85081e40c03c0f0120b0080c00701c0d610850b6034a6130320b15000e031907118440300a640341c0c2860702000808400000440c0d9403100002000d8140310b107414000d440343e52001c0d1082c6a031b025048102c8143d103910800307182c4950002e50040c00300010300c1d0103a03000c40c0c50369008900607aa04020721801e5032201303c00caa4002d503042e030f501b040383c1d80e4504180e001440325800440d0710504440100c800c0c0100c0a014156061044050383c000d9129104181c4d0101c803030050003002074110b11410300109004d00d00e031139032040c007900540f070001c8000d03a0b05508407203001c90408422640803c0900c00c3c4001010881d01e00c001d605003807024500c882001a202c0520340790b02c03a0401010401c0030780528080d0b0491000c04180e034101007103d5031103101c041c2d1260041c2104403115807030500061020303e412007a80c80b00301e240780c0145140074180a40001d25030f01c034541000790801d041000180d01d00d82000284882c40d8141e8a01c0700c0c2c41024507059050005a1543c1c3c00150300001c14003000d030782c4508030f6503012241241c005a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 451307742 1250 451306492 451306507
    0x106050708091918060f2102042a020606030607080613090203060c040e0901050f06040b01030b12030705060106140d0b0d0b0117010f02070803040f0c08060a14060105160602 76
    0x4000d82840b000b8005040f4221070001004d007820080c03040228600342051202c15100c1c2d800549001c8240304903d44c800e0800342990013401502e80e1590282e00180010400340550981c07440c000940300111080807550000c2a040030368103110554101c2c40c118080c3c0520700344288001d09441024107914400c14081440c41d0021500b03500205040741d02a083c2c2d1280d18060781c9640903508684601c080340344500c40000c07100c20042c840e29200d51030020442c2d031203131944800c2c44000c08010400a052590360340c2181d00503034401d003c0c4041514100300840d41c40c003807842c01320b00b40141030344808144034821550204185480d01910010480c0150000301802420000380346102c0ba550090000030a007030000c110180c07500703811011900001d0082c00243c20043c090700807842013440261a5010278000724000800c16002c00700c1150042095100060302e031640c50381001400d80e405000c142d600c5480f4070714007d400b0f1400c0e901c1032090802c6405d1840401e4410b403541d404400091240380c3c0040c001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 451308992 1250 451307742 451307749
    0x604020f03031909060e010c030807030507030b1e1005030f04020910240f0f091707170a05010518031603030204080d02100605090601140310050907081608010605070809 74
    0x1a5a00080b003988000f400c80c4002001e002c29400c0c0c0100c0f00020002481038030301d540078040c11641c0c1ca5166996030b00030341e80c0a03821001081c02400711070030186c450f911603425641c1c580d2603074203008543c80a802c008540d0003c0207820b00010544c482841010300400c6000d03540d80c40d21a50040c0c05a420101e10703903850045006140c3c182d005680d540800c090302e01e6a6000e082151005c103100c540307130b0402c204030169040d00e10800300000c900024044010a002040c503000f034844010019004035900075440e481c0b0703181c020740122a03c0d4510ba102609010a104c0240034543e04000e0300b00e007481d0814001007000e600c9202e01046040c004900d185050101442903045500030072105050b140c020303501d450b0082d100e240000c40213440038181100072030380b0302c0e00b00105400781c1c905868012052440340c00d810000d0700002e20707d00d07490440c0000040c0c00c1d1603550800344542e049a440044616021209402c0c800825613084100b04511006000c0590403c007203c40c4180c10001c402d440310340a1000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 451310242 1250 451308992 451308997
    0x4060209061809060402040b04050402131d0709411203040302030106092a050d1409190b06120a02031002070b0a0c090b0c0109020a03050706200604020f0303 69
    0x355085180011090154010962400d00c0c0b00400c0310014119155003041109a015901446508000c01c00007004185801e40c000c0a44441d081e00c0c0c1500d0035520045201d040140c41c20100804255508000f182d960100081c000351003803844517040c1c244104011440702460070009000c1c81c9030076800300c140341700d4115030003d02e005c014400502c0303111420060341ca0340c2140c40100e010398240381000c600003082d80220300101c4040c10b851a0082070b0601c0d04e50f1752031101c15685082c86810450355460b100e80d4050b940310450a8042016a03041c51641c80e0320342410b04901400c48017601e0101c0c400074025101140e0003130000c03a10b440c2d4800014070725030b0410080e004000e42c10710a0b02c407411150012a0003078109140101c4214640d6a80d602101c402d130740500c0c50340f03c001032200c04240502066640540f1141344000f000244102e80380d80400e274401c00b50741040c1c070280d209070400c00005d07502648102c8c041d60070380c28110340f50400e00c51a41e540c41c1c001d4802031081d504034140c28043d40b400c005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 451311492 1250 451310242 451310257
    0x3031f0807090f0e0601080705040e0109020d02010509010c05010609050106110606090438040c082b030e2b03060302130506010203160309050108070e030d0806041104180c03090f0308040602 83
    0x2500c90b03d51f0740c1c01e50b681c2da848141c460700340541e0505807aa07101d010b041c400c0884084c0c01402100c200030706a8011500b642c080102c85050040c03003030003a00410400d200e141d000d030841c3d00c0c1c001323125414071402400f030f804911046803e6600c881c04200c800d031201415590440d038000700d9100031601100083c6500780c440c009603100c1c11902c40940d04400c05000300c85002e02e0080d1400900b594466401c0b58940d2082d065400300344d02d1031103071000151a07420720000c1c1d00c0e002e45400240c040c2030899442c05d0100c0042c1d019410003404021640c09050006c607000e1040260508100107861540400c19081100e0b5014070720540c0c410000308643d0081c030807070310907002c4c081c2240e5a4200f80c0c40d002e0011400c5018480c0010314031070000350390600440b158160364070014028000500c139040c041b60607590082a05801030f803184945aa2006070f4000781c0007514620010304034052445800c48102c03003003161060b08250400f580e07a0007007000c2c5449038038101d0701440c180108c0da80c0e6007001d00103881102c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 451312742 1250 451311492 451311521
    0x905030409090302010f0b10050f03090a0b040b070f0305010f0302010c02040608030715060501030c1706010e0a091d01061a07030c0f0b0402032e0b150301060203031f0807090f 77
    0x54802c001c056040d0711442c503401840b101040b4055059080c007411840300021100420010000a00e08030304401c00317580d0020030390044420030700302079413000c5000d0b070140d4048401c1c800d031030700f840b80e000e41014110700c20400034681009103600d01107203414030f4051440041d05002003481d00c1b009640700d0307821290140c50b5400807a0f5817078001c0c1c07500b040c1801c0140520394a803071038800c01003500d43c840e000b5680b0030032130340d90ba54080e0450300b281004440405092503044c4807150352807a80b5600c81c8540000100b005034000120000e0b5010b040407a00b1000d041900300340d00d0201c051103a840c020704065002201034040b603480e038a05140548224121240c09080080882c540e5030030451006140ca1040c2d10a030191001240e940b2aa9484158600f0881915509007031286040101c4ea50000031811001000c0e09210201d810044a05600c2a046000117800001c1000320186c6894240d080d00030940311800c401c0d42c84c00141c0303601c49090f4003503e00f14540b9071010040700b03130640d00090070074440e01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 451313992 1250 451312742 451312751
    0x30803010806042003070b0d1401090f0b03240405100513030f18230402030c041a041a0a030f0f05060301050606120f1e0103140618030d0905030409 65
    0x10411590b4824048400721004440680e0032400c88020613180640404098003d00d40e142c20012401e105400280c03610400582e40d18043c41d8102841103202e00810001c107001591282c2036040005a44110440302d00a501410034881000509542010880710180d00d0001a40340e42c6051401c10028000581d807081c1010300b80010728009504628686100b074842803410310342e100d41a80c547e21040203002588c014103504001e5186981c5401c100c2c0711444021803503c182e0b10300010120f800a8030302c40c082c014040740a000011a800744940620446400300b030416142c03001d00034207a5403c0c07400c80700307410001c80c2c0c1243d440e00076042040d03509008030b018400c50000340d411340005c0a046600038407070342c04c0402080b014140281229060f0401c0180c5130181e55950302111170501000e452200510360380d01190841e10600002c05029500c1420004041e0341c005966524060001d04803c000e20441240e0f544003520000441c3c49681d0f00100c0840c9110703442c203049040d401207912030324125050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 451315242 1250 451313992 451313999
    0x2130602060603010c090803031602070f0e0a0c020a02100309390608071d0f06040b04060801140d021908010507030c03050a0605060a14090604090b0f010e03120a020703080301 77
    0x100740c10384a01001e5008225a80c1004c900b04d605d1980c40c030070315959400c10008955844400024000154524011a001c030760381c419008080106580c400003104940c04240002c214050050801c0700392544010803000c0061340010f07a41104040b0300d0f006140e514a010b00400034100260751041e03030120428100c0c1c10589038609124041d00d0034859003051062000324907580034079081400b6822503503910500000315401030024070754035016503911135200b00d00584140c0d5807070000d00107400f481032034a480c3ca02e4880098191041078015018106ca440e01041e42030303c035070794043c44450701103449418080604009103a002420703005944603500b000200082c0e180c05402114070071038035a070104405e41c1c40d1101e480071282d641c041d29612840400040c0314462180d4889094070380c0d94802686840500c100050050f0b0255001e0400e01d07031114042480c510345004000c014090070309001c0702c006181d00000e9119940189059190301000c50340c1000a0b208020141c05558081c52030759603541c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 451316492 1250 451315242 451315247
    0x6052d040512070819110108040503090d06110c0d081005090a02030a0905010f0e25090b01050412061b0503090d051c060f1e030b130201140304060507030b270a021306 73
    0x3803650641d0080d1515140486d194032030003010340701d01e4004c000b441c189410a4100291007e0a400a90f484c5407070b92002400104a07400a04445055500908420081600c0980881c1d0300510b2010342003800e050400c43c0792200620b50344d0195010100503039907030b601e4810200a00c20000080c0913903291042644204200b94845c0c030749289241c040310740a4041c2040920100340410034004403d0010400b04001096a0001c0071581c5050601c941040d80b1582c406000750b00030081950901d03102e80300000d03201c0c8c2c041c9100013050342034900203181d46000c08400c2d07500e000200c0031004108002074405105102010324101f0000842c005216442c0d4824401101c00098020140c8000078411100c44804190301590308513544411401000d60f02c004030045000582d0700c0a0b4180b181806641d482250700b28020b500c11381c400c40001899041031007000b0b044800300001c150140b0700c640d0b86065000d11808151080c4820141d4010095464502e2140640101d0032400c403200c0c040d44001c192643c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 451317742 1250 451316492 451316533
    0x30f0c080a0e13290301110a0215010e150d020310090602030f0a02090a09050702070905090f06090d020712060906020703020307030806100903111906052d0405120708 73
    0x141c04460360201c08a00301c8604044996001c14511040c51884e441c4000034800e40000c00b40540003000020b402c40d0140d80c0d815590b000b114000d00681012041c0340c078100030301102c07502600d80d1681d800350720303c2c105640202c89407940d00d00030300c110001c80c84042195410802100682c043d0a420322040c4101e14141000e5081520080481880c010004001d070450b44286d8014010041407440303e14540301c0c40100030040900100110b0090b21404241e00c5a5801810301508001009040b10300c068090103061420140034280160040c1c0040010301d03a00244040a941d40e400c140c801e00901ca207400c7d00284038105000308100d001091110a041c0c000c00a0400103009483d50001e941d0345c501000024201940ca000c0441c49050062000c92100403030f155030041c000e4958080050081141e05d0900b2956000320000340000a81920351404401c00307510340740c0703ca2440202c0801080d5441c00700c1c000e5003d2039003d02d9030000c40a4500404100040c000d290035001c0c2c1d0040003c0c10410f006a2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 451318992 1250 451317742 451317767
    0x4080309010207150801180e0a031d0f0a0611070317030106120207020607060207050f160f06140a14071403070c05030309030705090907031407030308070516030f0c080a 74
    0x140550000011a5a100d2951381c1c103441c0544c1d2040364a03070a2041c0e00c61480c240b07850b2092035607550303032448170460000c00550586c20301a846658403004410000b4010809000e035040c025121040c00c00c410340c4440e161801a40c4103070804100564400a0a9107884401d620251144144503803c03807003680c4500086060301d03626070312180080c020590703050581c0700700c2c0c00094002908100040100714540c0c050400544550140c0c2d4116050303208051511090b05106070941c08850420401d141c1e24040d60402050142407515000b281c54080c40a0742c003480084070280f00c40d040c800380c20388a15000f07c980c00ca0b401003000c80c1000d000140140e80341c220030011150b1140303000c004112440e000040d1981448000c00504c001c0d82410144000307104003921544003842012070200003c0c1c3c0c586108003c9200841c0144100f91079428014100500a44000b0030b20500b040390782d4440c61410ba5610304aa0581071a0141d032854500445000940e68800313450004040303844540903034070481c0d55116 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 451320242 1250 451318992 451318997
    0xe12070c0303110d120902010e131b0c03270e01061206050a030f1101050c1207021c030801030809031c11150903090411070b0103080d0507030902060403081e0408030901 74
    0x1203d46044055507142d040500f0303200070031801d0405001e0b064040e000703200960301c1031400703040b140c1d010004031380d4800c00300b540c0554064035080c0c1071902940c004259090380f81546001c040312010ba4030007800c50180400d00b600720b84451000701d04071a802440c001c00600540c401d001d82c07036035608001010607881846000500d4144003000420380f90800d08002aa44c0202074a5240c51155441d150058298401d03d0f050100034460000800030030b1003920440c1080041055444d0103503c100f113061043c81e642ca0b001100d4410304007000c20b605c420245e0550f41d03c1034403130780d42e2018034001902d01021500c030320480d08841d949110132071354003a090102440b1800c045a0324901c000016409400044449000c0d6138002e010704542e80c0b800d81c122050a01c0f8202c0f04a290a1164680402c1d03003009800640f000000014005106080352245c20741c003603030070718081003010311960005605200c2d030701c03000e85202004500320004124040d19000004e02502c540d0f56502e0781c4d408055260340050010502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 451321492 1250 451320242 451320257
    0xc06060102070f06050307021002210105091303050a03180c0303020607080c0306040b010903020a030b0f0907060f08060f04050910270201030230040209060f01080601030e12070c0303 80
    0x5500020b900b809032580d26203150401402d0040c101c5a940000b082142140300351005100041100e100801e00700c002c2c6004408008a03a490f54444804180e10050148100408000c2160403000013040451381c503150456448441c0c100442c06410411442c0c0200b036556000d14041141c1008418100c0b44640c080c0e600540e1a601300740d0b0006c1c0c088070064041102040010894034260740811100b01050400d04a901e4580e00030401642e06904125040c000b1401400304140c11501c0c0380e907001e0f0001006181e00c44c1001ca0042000d0244d040d41c005002140c07000c40d0641e0780d03085890041241c0500100914a403206101f681c0701c048001c0003940724030b409200d60301d400000000e0124405289544440f001e201d50044000b94410600d2041415860035140c004000380c49106a8009048100a405046c01d0040118850380903100c18403400c0d40198125490b6040084c13140d0001003401c0024405400401207030030b0908075005400314240015014003081040c101d040180c2e4003d940740341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 451322742 1250 451321492 451321501
    0x40812360109080105100608060118081e0307051b040204030f060606031104050f1c080a020706140909070c080903030d02030a06050a0806160302091002030c100b22110309030c06 78
    0x113080b140c040d070745420300448800081c800503000b4000260400c00600d01440704440910707144012510a80004071160001e0417a21381c40588030139504107051010024524040095440302d41d40c00180786980e5000d250071046d0702640d56070754140d400560b0004110100b0034458035120000b000913002d1500402e160800300f10720a0100d07000e41d4260346010307044d21440741c000d400b0801540105810070742510300791181130001403120350140510140e60b8004040450400d00041c19021248c10b0607489401c0a00040c3d034117583d903196403604290b480c20042d900f04528100005144a195145501448001002090414a039000318810700c5044001c20600c0c3e221000c21640742110b01c1003141035800b07040400c0c0710101503094201100b03030604006103000ca640001c1a1024580e00c211009030b000400c03643d9a0032000e11001b440f0800c5003c0c108589550400055404680900c0c24130798010041005081e00c48640d02090000c001c201030a5181e20f002d103030b80d0740d50b603200050b082075a004440226 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 451323992 1250 451322742 451322759
    0x1090c08030d05100f050d06020906040618050402190807021c0f1202040501083408010320090a1805070b090307080d0203070308150a0e09010b06040812360109 70
    0xc030250b8171081038080000f490b02c410003521a0071400144d90f40c0707500700003441a03562120002d20040c8040d40302e0403955800300d8030000300c0303420541c00306006600400860140040b042d9800d0429a000e040c01c1d81c1a0302c4242040b0300c0c140c456008402c03c4007818003065502c80e0010740000f0325081c556529200303103544010803021381c0203d20610340851408400300300110003407121707041e14100610a0003180c400e00002c0c80d007021205040c40c404160010018028003204012440310806450f0408103d1424600441c95000d07004242802c0c49030b442d2000011000d5021404c071025030000201c580381a200c054200c541e9202401881c07003482041c500240b40c44000c503001c580482d0a8014604050880d20300350381d070003001002000f060107001d50b80c6059a8600c01c0b10710240807450030064141c0f4251821500319440c18104603c540820b001c01c004054000035500c80703d803400504261600310450b0f400c0d1600d21510790082d256080300c1420b05003401252503e80e5180d038241d8070070401d030381d561b0200b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 451325242 1250 451323992 451324021
    0x7140609030705010e01050c030a0804030305090321060d05060c0c010b0a080a060f060503060736030221030a0c030311032403100903020a060510050306040b0901090c08030d05 77
    0x403a0103400200b4104419070103140400440070041c1021441c01d80f0600d0a00d04540c0910301c400c0c082542c1740e040c041031582c10310859034426090300045180580481c004070124031401a000c040220340000210340d61151840c0f5903006620408850040c00c02140c11121030704082c0306004a5860070201008510344502c510045407055400f0f0039010005841d00009081c03503407100d14070f02d0380303804d07001038183c50411400f8860303a65130f0b440300401007240500e2108007041000c0084004d4040b800e800e40e0420000603102200e5040300c4200a42c0c0c544507291110201030396000045010124014640c0c6400840c10b01e4464801d5808010040002e180c0381e580d0700065400120012038100c0428464a01c1c441d0400fa07683c0007004c40304400c0e4001094001e40399220000c0340107800046440c4100300e80c6002c0c86400c82d410303003034000d510ba003030a01082d44c40000800190018400c01d001c80c0342250203600c2010740641068190b416030352584225540d80c0d00904140c0550b070700d048009010150820003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 451326492 1250 451325242 451325257
    0x50c0a0303120b03010908040b0a1101050702190609020411130e010b0d091103030d02091302030c12130c0e0f15150901050906072102190f030c05070602071406 70
    0x603062010300303003642c0c0c6400030842d12141c641c240d90784141c001c0225030890003030001044200d84070340e940c810801c402414004035654208032a8108000d01050340d8010030244026400d01001c4801680d0701d08001000c1c22143c1c101035007161504146848030020301005060440d2a000200140c1c6c3c0c0d207100c1510400f60910035001401010300c01c40c40c4c0d070703241030300814403423402000408840d1311000c0000b8150f522021940881641c00038227071005040012500c03040c11110b1800714154546620b0a907040e00c298140f0328000c640e404005560080000c104000b8240c0020034070032400c0d00c806c8950540c010030340f4910100e1010100103880550a108003146907040038282c8045030860380b205580e90b42021001d070b41071080500025110713484a03006815124000d000c1040041032109001c5103402e8108000400c542010030f595100d10080310a02081c070f41e0000e482e072800c40040c20102c81e11015000c001340700703014458000401903030000383c0c501901c4003100e2003041d41035210200451486130f01c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 451327742 1250 451326492 451326497
    0xf030f07080f0f0c160b07081008011a19080102070b07080906070e1509040509010c0f14070b06040b0603161409011202030711070902070b0a29060904021303050c0a0303 74
    0x40000c124104c000042c0c600ca103a0244001900e151a0351407004180044072050006640324017001059842c070302c2c0e00001030000c1d000801583c0681c0c000c130a41d1801c0703103a00340d004032044408000034486101c40740006140c103200854541800e850401110394040d01d05100050360b4002261150102080b5940540d071070340c0301c441400010f070061001e24551460341d084e10200a10000001741c85501449114800190000454000c1100c01130118880f41650104002c10b12104441d198032a008490b543c982100d04501c8a545810005014100b400da01c143c01070004018005008551002e800c00388003180c943c02c640d95508000c2104501808031413600250034003410907050307141540259040303a21481c044028028003000940b514245501c007000c0c00394002123101c14880d800707846035044580300c182448000c680b5658201401c10717905112051403071030030740720a21f0350307800c8116414020050015520340790280326000000d8194441a01c160003281c000344442e21380100c0d070406407607154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 451328992 1250 451327742 451327771
    0x100608180d0e010203130b21060105030a0e030f0703050d0b03190818060703440604061e030b0f0f2a04090218010e01020c01050f0f030f07080f 63
    0x8070300c100e4580e16080d039414194041001329a2025401c46c407008050040c03c00502e9a441000c0140126900c40094a8005070300308010301c03800d07a9010040320b401c00b004030030104808210080040c2148242110a400b51800080d02030816030014050f0100b460003880400021034042b05040d103851000c0c0d501a940702d449900e107000241c0032000750580c058000002c0c085103088101046003a407041c1c1c401c0d0041200c511075003032a18606441d494241700d011440242008408070f0b00460405140c038a0400312100c140000c0860300d80da48000010002021030200a5810341242e0500702e603640003d03240040346c000001c05484146043d14040ca0340d4001704d020b1980c6000c13032602c5140c020300d1500c48010941c1041104007101d07402030005000440d00040c0d903904000c20030312104124001b40360511110741d5040c82141e0700810a803041c80401c1c241a944c030f515401c2420030910a0001e90964410080b040c010500e2005c201107108900e00e80712481c654407480c000103c001c030102c8503c80491600b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 451330242 1250 451328992 451329013
    0xc02131103013515010f060507080f09030a08190c0b0408160812060117091c05070f06050a0b0904082a03031f05040614060c0309060310060818 63
    0x1802240f10742038900078010b003003000c041d0002c4010002c2940c110091507015852401c2d2207840340180798018118102100b20581c9041c50240980c0280000906031f02c20204081c4000e0f0080001c0b2203046030000c00307454200c6000c0c64201b0b030981040e03582c0c03900344c041e0a0881c060320303009008240c005500002010606d54441e5956141a4400160b0750080100c03080704a0000715085d010304440715449803446168034000000500000d056094240c18100c0742c3c0500200c40c0b000715040c4150b0407099001d50b010070000500751103900c0342103402447e6218069000c400d03c85694401409003003404414010940044208018a201910050200780f400c2000d1a0200c003601d00114403003071081000301a07485e558000b141150401c560244500707005503c0069036080700d0501101620040740c003000040c7c24071042982c5401c8682142e80140340000d41c0d0003040d1410401e49034422001030580365645000300304c1d429110507612403100400c0d000d1001c140e130002d0b003680d00007010503480010040202d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 451331492 1250 451330242 451330259
    0x91a0a0e151204030806041125020111030403030c05011b0504090b0109030609060e0d0f050909041110020d030b0d030807030f060506030a0c020f0304030302071a190c0213110301 78
    0x401440e03008031500304000d20400e81002c03010342da10983c040d440300b80e03d81c035202d000c2c001a00d00b07981428002403000c0000051031040038107a000f010000a0611808403414401651000248109050f40303200c08580042095030041164003507600c140000e003d078109040001080b4071841d1401d0020a1040c4014801072410354072120031210145081420349982e92903800c21106c0c0c12000341d80381911109100d01c440c00400c903032404248a403810410341140e44030000d006000b01841a4869600e07400841d00784910a1700c402e040110041c03080b10345068200d40696500542801317080440c0c00e051000109240c40b0b81480011601a25001c040d642e845404400a05044040c461110ba070744001280989804020394402c0702e4180c0300007116840d0300d101030300d012040701c003080803584200f1007807001982c08a09402110505120310700c1070110702140b9440d0740500070342c114103841d80681d0300d581c41c0c0d4800744050401e030003920719a05162802c450042038401c031005603010b07000c2c10001000300340c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 451332742 1250 451331492 451331509
    0x20114062d040f020403062913110a020106060206010b030405060a05191b140c12070830090f07150201090206270303031608060f030d091a0a0e 63
    0x80c03400180c080080c070100002c04a800c1006000c45266002c43e050040203a14030440051058620804002d5004084c0354000b4003142020207008810f20306098410401d40e402c500450705203a0382071601c90010b20390090091603a03110303240c0103206901c00003940007624001c40f4001ca4024003c2d1600d50b98040214001d0030b4058040c1d81d8090000190079020000b80c883c20301012044c502e045846101500000c21034121213007000c00c0010300300880030303e000e00051540703900f490b02c500c1c5a455000500340707060303030f03000d44a015030b80601030307004a04a14910741a0381c1d194540c140c0214141e074840714986036807245401219a00c680c00b05805012380701c1a500c8100285000344000f1030710b00e1541c5d000c10361541000001c00c244035148550000c205000560b121113186017603004500714a4118100020803c04559240903c0701520100d850340d184c4400048505c08040c0407a20346155546000701040440d200e458003521200b034288019800f410129006c5440a5980361003480f00d0104000c02d06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 451333992 1250 451332742 451332799
    0x30a0b01092d2d06090803070b0709030803010b0712080c0901082512060b12070e04090b04030e120309010c0b061912050c0a0f0b0d060305010203011502011406 70
    0x4606600020f011504200038a803000000c0c91082010882e642100941c0540390b041101800807440f810711080100000742ca408580004000c0d08945a5520030b0710188000e0f00013412a840020005c03d0b5110210000d00c4650321401d4003598443e00c0500850b02e48400755542d100c00b400030068010b0940c41590521f8000e4082189200c0d05402060055000d40384910450081384001c042005070750403904c00e6200414085c00d0701e030f00e0300d9840042602048001810081400003d403101800d98407070b54049202560320104243c400e06007424082c16000d0410b414a00c83d01002ea4005202007022041c1c502c803a1060b15030b6a0205507655031840040c9000b0910394204458424034114000c10103250002082500403104940e011410101e060503850f502030380c0a54540b0a0030000300500921344403c486050b8402a1035880e8058050b000c0d007210f034005001580003200206100f0403080e9401041d0501e03800030088280c0340c0020030003040d02291880c3e40040745e0f28012001d4030141c10002c2c01c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 451335242 1250 451333992 451334069
    0x301050405040c0806070c03021207051203090c0a0b0c0105071d01030b0301090c0914011a0307050906160b06010e09010f21060501081c0216090b03011e02030a0b0109 73
    0x3103901c59036450b2810170101c17034a000040380c04151405143d014031151081c2032603481d19030318044458680340d6807400c000b0302070344014130000001844210140b181c40880c5030002c0400e401c0d5a500d0030307000100c0c0c0166042d0180f9510b01400701d034085000e0f0f080d901441c5400000d0031741c0004954015030081c20f9801805415549803103218001482c03040031007000c2c0c2000800005c0d41c1c48079440c0300d0a4014160071507228040e4901490408661010503a50310649500d002582d07070842c58003140a901400402c5d080004002450b04100500d803135060740700d06003e0b079510207003c00383d00400c000c290082c4603200d1340e440004000d100e644003a6642c40b018050701c02038841200c000380d41705e0381200d809034005450750b00050190010710a40e44207049500700c0501c0100704002c41044c2000c2c40008270310901c5809a61038005000325242074004920301c56401c8a8104000b4910000b400a94011135064a60703528114088086601036500c05058414139901014140100e420f450800900300c00c0240300c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 451336492 1250 451335242 451335263
    0x315011101090f0c06021203040510150e161806210b030f0616050405100c0327081e0d08100b030103030e0f0301510807080102030c030105040504 64
    0x10482182c2c4208038944a406500c030034614061000342040c0201147c2211040c0800500c404500005821107003038401d80400140032a0110260b203070070800394032048404490808100c107185200754907420b59046911828600510341007040480d044d00d0041c4004200d1602c0f401c40425030445482e0102c030300ba8440000c1001d0114002440c1c80040c000c5210342d6805841001903949403030102e000404258188581098141000515149a107621600410201010741000d05203d207000300b81221018908800655403258001d82c8001a03000d000002e10907400707150a0f0000e04810f030980e107221000a00400390040404032280100500528200e0700030044c0031a181c500540214000c600c20b483d0700076001840021301000440e000655031080c1d25065041484c0b06003e500111071200c10403051846810088105524030b0a20000119480d0002102a40810044405c0c401e855441048420341540d8010f400e00341d03c001c070344020300c60a0600040142d07003480d0b0011500540700303a45052 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 451337742 1250 451336492 451336511
    0x6041a0702060c0a03020c0d080d0e150a150e1b03040f1b0905060a060207090b01030e0a0b091c1409010c05060403031d0a050604120c14010c11030315011101 69
    0x12510f8021100204164010003940070800d81c040017041c041c0d030350558010303610806030344170000e86012b03440305103010035280d10f01e500b805c9a041c4130b101c0700041d10300d041e1150b505026511400030310903a6401d01945000c2640455031010300d200b0715100b20790103d80007966905441c0201450b800281c0200c90352664140c158000034600d001008521014003100418589007925400980340d01800e1213014452204040c40019800314500064803200792002c1031540c1c04000403001010300000000c0d09004021610041122080b9a5800365003106c003140c0c0c508845e1a445c146c400c007503c56180204450b11208a89202d41201424040405040c0030f08400360700d48a060402c0400c96080780081e0381e40d07000e2600c24000c43c00d51009a10018010f002c14a0b840d40c8940d55100080c0001d411030b09640103c0050341d103e0034002c204541d01030f000b00c0300d08452441c1c5134041c090b403155940c0491500303000740c284010000160303485500c0200590503480d01c100019100e95108805080955485e00100e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 451338992 1250 451337742 451337749
    0xc0d02010212011401020712060b090a0c0207090b0a0e0a0504021f0e0135072010020d09080403030203070204060e040b0f180d0c061803050f0a051b0309030111040506041a0702 77
    0x2c00c1d40714020b0b01c0202b051000c2c1402c101129a00a01c0710402519060000040d07582c0095110181e5150b028006285140726002488000c41c543c01002080c60140070402141c0e0711740c0025006030720948010f940440c01050713404154040304a06000540e50240c0b2180135889041c0600741c5d80b90003109a413030403003c110030342d00e50345445c80e074484201c04880500254035800341c00180e034030303030401c1d07181c01401041d880780381c0c8a200084a40b0103503074000c2021103002e4565880701c080164000300c8a580c4940e01c0c64082d440e03400c440b500380c0c0325501d000d0002880000325044103204075405030b800ba01a98800410480036140513000c03001c4401c0c130400154050008100e041c107501065103501c41002a43d1800d0340540303402e00000003600c0300466283c40020b1700b02e02500c000d200c0d8180b509480e54076400d4200d51a00501d100918110052540c40e444600b01000a00c0002c600780c00a000c0b44400400c600960711940c800c0700e800c40340420080003000e00c4c1c045200101231108a1243c0303000e01c680c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 451340242 1250 451338992 451339019
    0xc0605040318050603090c090a060f03200405070c020409060906051f090e07060f020309040c050319050609070f030b03030a0306151d130209150c0d020102120114010207 74
    0x1240030a007190403000305a09410b5039400189011542d040ca549085002180c56210401c07206014445250100c1d1441c48035401c024060b10800300402c040a03a00d0802818200d00c045100001e07081001080c0024100703030243c184102d59546800e401c1030410b90a000c020030304c1080a40748203584e1150000042d0050003002e01401040308503001d451100c9103480c0441020b94411a8200d1406070b2041c00b1900114002007141d00c0b508110480986242c81030342140b2a01182e5a80549040e4000a400d500a006140105080c0ea01d6401c0e04c0210742d100c504482040d640694003505040c0021803a0b8030900000e00403d03861310f00880d501c0104d101192440e04010181000710ba102c140c10b00c14081c4a0003901031801a40ca000b0308000c0e5075814203040c501c00380040070302410001d1403d58080d1242d404450b1a280042c10307410112841220b03540c0301380c00550111486001e118031b102003c0b84140250340200301c0d01c084c0c1c0e08507646081c20b8010402d883d002014154004c4100010380344192180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 451341492 1250 451340242 451340251
    0x81924060603020903010e0f15191107060c0507020a1802160605091504080306010503041103030c01062306030a090c0312020f0115152a0303140a2a0c0605 68
    0x1000f580300d503a83c008160940b00442c52800304c1d6803044880c1006200e0000b403103000111054200201c40e118402601083c404601d20182d0060800b030903200c8000ca2007004080c02030141400300b01d05c1072511011030350f038450301c0d0020b0341c001070025050040c00d00e070052400d81c0e4a003400c40186003111200320980e0805400c0c0e4203450840d901c10410001d2a42408200c0012128a840c0031142c07806983d1034841e8080501098100100800040c0801041101e102c81d9030380018122911800400703181c0d4080c042d14040d8041000c481d0354410031110003030b11100a5400014105802e690764810408000c10048409588042c001000000414040030007840380d41c440e40d0152403e01e2440f10f009013910203003138600c0c2c00201a40401c218020344030300c003080340b6606880e00c4510a2410780d107950b008804840c5c000b042c0502c0350000010942c0cd90b01805c0c0c12054a0322503030b825a50244028215050301c802900110318900e51562125040c1d20341075510403480c1000742c58240d0546400013250011203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 451342742 1250 451341492 451341497
    0x807020c0310150e0f040803070203040f0e0402100212040b160c0303110106050a140423070c03031a0a18090807230a150b0a030204020a05040608010819240606 70
    0x64034803400511445030300004e800d161040c0f0126080484124010720030080c40038007044000310101c0c200b80e00c2801110018040554800da81a4840343c5104a41e80180d80c106c1c46100c00741c039403410881c004181184a180789815079400c0c40d10382901010b80754410340401d07a00c4803200c0840d0000600d68a51f00d00070318000e03a546080c00301001d062608560041e0806440780344442020021580c1780450501c00d444180c8000c2204445840c0c03c403912024000c0b03001c900781d905c030104040d07203a2100d20b2000b80f0b40280d60038032016483c11100c810b00c41040800c2904181c280f082404144071140f03451403150700100000078083c0c0b054454020381c0d000a0022219003213240703210703403d900d0350000401c880c1c08440081d256449003607071b1342465110000c4210071140c1d101d0311065250f82d12685c100c0d00031600608159600c041990000340300354090b0203000c0110702090000b240030840000c4c141c207800861088466802038a07202c043e05010101c000d126141c031900d1119207030880c40d0249800400b4a41c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 451343992 1250 451342742 451342751
    0x2106060f0a1815270f0e1b01030606090f0b030c040e1e0a0b0d02040b0a0b120117030f0304060b0d080c011b1107030210020309030f0a03020d0306080c010807020c0310 73
    0x62512180c007150307008015000d00090118059400c0e1220381000c03000110001607240c6a4207580e1001c0c01d81b0070340b01d8002d80124015041d404a51325008226200240c0c0c0400007180c407010143c0c0d68075114092801c0e00f40c0c80f12000c0c480703d9505c200640d00041c070108240e0501e030b0744d1680c001c805e000403102282d04a030030b812181d08c01e2142000c400d801100300c010620410f480600800c0c010050500040e01c2151030703420001290715091040b130007a21041003103a80d540c500d11002650540300384114002c08842c2c01108200640c080b055881000c0c4404000b032330342d107658441c0300180000940d461342c08068200d40d0400200b41d0700080075605954000440c070507089101c03030b45403001031040a1050086002c07140c10714010100d0742d1400e50341c3c111544043c211020400b20715502072507078405d806205042d0603030310000340003410111040c0301c5e0f0308850707515600341c808a0a4409520913503000780c0c40510405c2042d8010480c0d42d51002a5104583c000480345c00043c1c6003184031031010f651035988 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 451345242 1250 451343992 451344011
    0x21903050f0a0b07143124080906070804051606020d0206070219060f020f0c030714011407030c17101406070b0103021c0606030804052106060f0a18 65
    0x70302050780d00c0742c0c45040c80188040c0c3d0b03401c1142c00b8402c055040183c000c0301918200751071003448480b04c0c401c48001c1d40c4101551600501032603030044a07c2d071032041c0b0b820380040c0c0030548510000d902c102c1100b005440551503c900a032102c800c00f8008460901440078604459961080741d94010201039000705000c200605020781410805131400c02113400500d4124500301031402c4484403580c0c09800022454049041e000007805048007c7e070b000305001501d0304000c1c00000c05011414000d0801002100d42c101c180d5080740c91840d640ca150788851000a001c4901070381c0b000300c2003c5c0604040300055503804268800480803960b0007480c1c544002c060040d50b0030407011003190003041d0703a820304d41181034880c0da03000801480002d2098066220824401e000714500c1c40d55a81e000303400f88900c44e101d180c003190701d41041c0038580c02104d003000f01c1c101403013904142080f040302c4600940200e4076034805012201d60400c400c103400074800310b800200042d003003000503c1c070b100340400010302080e07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 451346492 1250 451345242 451345253
    0x141302040e072001140606070c05030304090207020a08011e05070302091207140d0b0f1f150f0e0a23092403060403020c0d030e040f06030b16050304021903050f0a 71
    0x4200800fa14668036010740c0114600002d042e0342d80044084070303500d4858000e8a40400d03810080e0708216014040070500040b6604a030b0040d0004070300c2110740300105034840b2002400c9807240644a1842c0030784101c400c40d000c1042d48041d4000c016440c2c094034040b01d0034089915003044080c10095030b40156001c0107800308204501041c0c003011102980c0403003094540e000d1043c03000e01010250462038000c1181c0d4030117148c0d4070b07a44e6039007400064205d0b81d4450791155401141c00d2944081980100c00050a910038651000d0707054004000d0009182003030000000407000c0728652004100741c01d2800c0c0e10350785120007075100ba06900154642c042d07050a0107405010782c00e114602a40c040d40070b1100103500031583d000c049070255825124200c4600b0308840d0f0001c802d48050b04581703002d40c0c016650340325030041400e0303d003e00e0f8034002944580322828090010f00d00e00e0700020b0b4041c0045001132905440384c0e07141040195031103c100c1d4032038440c41d042c65810310310b0184c4d551010060800300318 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 451347742 1250 451346492 451346537
    0x2040b010c0209190614090f07021603050f061821040b1605010b12190c0f0e0a0c0906050a0810170615030106210501060906080f1204141302040e07 65
    0x441c81406c0040c0d81803004106040d80244c800d4605903092000524003234405c0166005018040e50304074245c5030349041c0580c60f030381d840300c641502c0e004600020f141c80320001c0d02c480c034283c0171900074196188020410341040008000a1803000d8007007000151140f42d01018110740c1008000e620780e10a403503e840c03421602e002c1c9519000d440d403020708800850b000b0400c0481c0f031100d07030b603007c25914141c40c050700000070f40e4002110b0034410402c0401c49942440039980b0880c5011001c00600210030029501c019142c421140050010010411072a00ca481c6440d0499000300d0428040c0e9115410b0107020400b0040c0c2080d5a80404104000070201c3d40e64005107100940081102c60b0906d0014260345c002e10b0810620b408403a901e00040013000d600540042808280030042c4135220000c003910340b052655918240e21078180d004444140751030850342200c1c449a45070f81196000c9041c004124454400040b007240d081c040010b880080d800d030302e4865941d0741c2d2854038040d0b03120354001405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 451348992 1250 451347742 451347749
    0x15050d0b04020310180501030201050433080405190b010b0c0c1c150605030c0603130f03031b140a0305060a0806011e12150b0f03120309120c0a02040b010c02091906 72
    0x106c0c2000010000f60740c11408403000c1da412805039081440c11100501200724410003908000b01ca040c10240c0504c2d44041d80e40d01461280050b6102540038045242100c4402c03403001e4409c80450004001c0782060300010500517100c001680d0244035504005070b0002c0300400f20340504040346c0c1110701040300c100d400e0a00010440c800308845414000840d60700c1c3c061f01d04040c01480000085000c100c0c6801c0c0e201304595005405000d082c0192030700501802035503426941071201d800a4020f024010070003204c00105c007591450501c05421030440281102501040c0c00011020001c1165030b81409418043d1040d0490212801101c2000301d80070b04680d4004c0745042d944d45076040020300020603100c0304010707804000c1210200c070f6000a0b0550401c00141c0d605210719044025450101005188900c0004084e00c1c031700a80a600400c040c410481d920a0f9900851000c100519140d841460980818504200d540c00f01e540410f881c00c80581e40f20803810351011082c418a802401070b100034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 451350242 1250 451348992 451349039
    0x60c0a05040303140d020309010c0f0e090a051803040303020c09070e031507030209030709050103050609010902010206040b13060c030519020a09030b0405030c030f0d0b030715050d0b04020310 84
    0x1000914040105640214080102000300c1d0f00400d80741c0c074031510b003500c1e0810350b2000c0c110364030b06282036510b000b400400000d2000c5030b440c141d0403076401e014607c0480c00d20b01c041c0c072002c82c03543c0d014811801008000d080306070541d4842409094200108003400c050f6110b4ac0040c218002d000040144500c0000d000c0400c00c01106030301d0714903448c042107a1880d8011142c0c004030540f20448168043e004a0710900d4151041c0400010f0100064000300d0481e401751058440d40c1d1100f00b52642038407070020021340503a1091000c2800075520008656010544c40b00401d103c68059940701d044c1c540800b107003c0002c0e1a41c091200d15014070340200b541400042e02145020340116020340300840510001d030544441c0030000c1c0c1408420b1040704c034654002010f40c0c0c1d4401c05036580940d2508807980400c48507180070b449510702d06001501070f043d14440c040c0700c4071041e908641110b066020407035040c90552510030303500580c0c40c1c0c2d0000d1401480c4001181030706a0802d02c0500c14400c0c40c18420f01c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 451351492 1250 451350242 451350247
    0xa1e140f0a17010b030124092d140f040b180c060703051309091403090105040902030a0b100e010f031103060d031103040306050f070f0210020c0114010b0408060c 71
    0x959034031207940008403080840c1121054100350245401480781840310340c0c040d42400000c904042c82d03800c0150b00b103407807500400000b0340c4540224045880c8401125401d500304900b07061030110a483e1580000340d281000b10f05421307502c18503c0e441134141d41c1c40d158510800140010041d901c030000d60300c01003443c45220300517035a1002694488940c400319004403c001140b1003072621071070449035861208030f02142c1d81036850f2031003030007011503100c199100c600b001c120300b0000d034010080f1071120b601691803c2c149804c2100c154001e40c009803091032466079841e1117844070b464410305072200310001c1d180d5040d034020240014280b01d404444590416181140d0400000c07503070f50560f50441c00c10707108a6080c401c64501a140c02440d180100b10522022a00104104041d00300324821694082041c03a60707200d01106660703a23080186802c0140c3c2103e65507001c03414480c0c4c00b40c00f0322802c1d03d00110392940003d040400c0e9003002c9e040f01c0c118900001d000c0c000744600b0008103410035500500c40d072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 451352742 1250 451351492 451351519
    0x180204091407020c0906010c02040207200312031f080d03090203060a0204030f1b261506030a0b0408130e1005030a030f051c0204171006050612060a1e14 67
    0x4d444410105101d403185141c0c0003c03038a2a44620f404541c140d5003d4011507642042c0d0a03c0b20f001025440802003018220203410501e04020940030810285c0f0342c41d0f18150b8403011001100d5145c481c203a5222194082000102c96100300800b40e001c0300c0ba5100054003850900605040407401040345026034010001080000d150384040000710303130018004205402a01942c0c0c2040315285c1c0503400b034000c4461072a070a05c8040e40000070144036403084650627458481005044002100c5d61a81604a11020b8010821031030741c80ea40607109a44e100c0c5000c2c0200804401d000403600080d9455007103404101000354001320742e0015160890080c410307400130390740003000c624040300b48008110001c942903043d40c5c0c820070680100f4444203029500c0360303250494810100600c004401141c4154500f000f4038400d54404c1d04107844028000314581240c0454a00d00c3d14006000705801079900403001410180e0b032400d404800541c58004103203186000140d082000350304140a1203280c6030384c03005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 451353992 1250 451352742 451352747
    0x302030c0f1e220504090c260d090504060806060607021504030c1815080d050a0905090406061502010e0d110109050703120f1b0305070c180204091407 66
    0x100d41d0701c54080051680d81020310351064901c0220001c0c445042000b08644401415180c10328145521200001c0107007662401000213880007080c0140160ba105c1d0000e010030844201d140c01201e021400320003e107405101540c1c40d00100e4180c000000760342100900c203031318150164200410309139009007810304010b000949244990500244111140100d00e030140b10020161001035070002c01800410782d65121520540c50200d194002e0249030100d10010303e202150854203551503d001070401903002d0300140d03800d07803040302d80005019010f1000511035964842e079a20441c45404085421490191600858100b2040301e50540e4100390b4000808c42c0700081d03907400100760703280132030b54080b400d061903004158030480605280101e00e00070040c0140c1031075a260300c914580d24140300d201403c1c030031070b4003905050142e40c0b003460740c0401201183c42803020345806806022580302e0155551062501e0b011240b4040b5076464011400b0445030040303206201100f45c401011020500c0c048100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 451355242 1250 451353992 451353997
    0xe011805040207020a0e040501270c060e030f071503060f06020c0105071e051b030a020901030b070513031b0501050301052202040504230106020d020a060b040207060f0209040c0302030c 81
    0x1641e0046501003541c4082d581d580400100500340303440c0d000d04d2414107080a501900700c00d014821011034000e400d00f82002c8a13100c0e100b40302c0d0026030b00c41e9401d00b03000c02191425510b0046541c148104460242882d00601940707004161400701800f10520b44403010741030320360943c4881e501e03001504040002c207401042520305a602440d01950342d40740d510386041a2480c802d002c280440d03081140c60100107000844214620b41e1000427024030307038010300f01541d40e2f14070700c2c0007034020070003400410009888501c070302c1d00701d100750a000b401d2040c00d0302c614840010360351055600070700d003c020306240820140984054082860194603640c1040c0104001c0c140038000300e00c0081101c5036503070011a4946c15600070b01401002030022005448140c0c494090281300c0400c2c40d9000b40001403039600020380c410703140c0c0c035075005041455520740740d150081105d400f055400c19006c011840018440e07125200a489000d43e0050b00c80c042c0400703010031503140c1c86018040c94410414400360390000001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 451356492 1250 451355242 451355249
    0x30106021f200304020922080319150f08060106091203120606051803030c0a02010f0c21030b09040302071e0e0408040314011e1d060907060e0118 64
    0x10200070780000c0c1d0400030035184045000ba080078a031140002e10700500250300540c0200e55000107a21400700010989130078203010b0f6901c0000c50340c504002210300c0041c641c03001003132003d444009080b0400c1010b40ba0080446089c040203440f050100c00d071045a0300014005000c02000a507040440c0a001580140035180210907014011000c051080307041d2414400700407810f002440da034000180190b04400600699007244d003510140c141070020680f060b44250030000c00e014032050300103450b026041c0c050070081100366064100890000c00401d2080c0c0256041140740b542d4070680201100c0102d51900c2c8035140c04410b00020a41c0021210260f9070f0015802c080d900039041c070b01541c030456a006410302d10301e5070704110500101002a00c102c83c0200c3d01c100f54000c0349070103103003281e65048580c2c1c075020388440000c4144209034811b040d44005555107070240442e42c0b40061902004441ea644d455009000600c4110b0b40014001d4880c1c4003805e290440000c2000e2030030341c21100d0300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 451357742 1250 451356492 451356523
    0x1090f0308090a0507090204090c03090807140304090e06151c12030605091503060c0f0712050d0203090c011404181109061303030201050c12070e12031206030f0303010602 75
    0xc01060800c04103000502c0200c4c1e00c2411900356031751380e00100c0301a40052190030961440c0649000000b400790050030a001d500c0700c0510300c0c18416a4079841040c400001c10a040c5c4414400414421901c0c0304806460170140010f15003850180e003410301c0c0049240c80305000344d0205a1a005c4800d01c540d40f421001d0b0f10004910300d071402203174114010b210170f5102ca81d220400409224062080781100001d1200623402e80e44103640c0c20200850a1081c20a0904402c500f0800240407403220803500d44103555034a4010b1403c03503186a12000e0340c00c1651142000c0d080100980c80c00d41c3c01c450340c02003180a08106a00307062a2541044882c01501c0c04110310355180e0715151201180710713049425813079004000a07140c0020122440343c440603404101c0140d8038050200d4640402c050603a41d0000c0d001e181c00c0304131780d00d800044980c40c1030603c8040d045400803c00101660007030015003000143d41c800030210740303451401c02d4500b083d09503c042d0260010070062000350350102c0e0058083c01ca14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 451358992 1250 451357742 451357757
    0xa0b010206180115030b0f070e09071b060f0e1b0f0f0406080706020f0d020a23070306050108030a0201050609040b04170f2809050f04150302030a030c1401090f03 71
    0x10b003105405440350b03094041d41081100340220401c109291668090441c4a0140c100c60343d42c01e600351000b000440d040f550006030b03480080e000a201300074000e007085001130440455080c3d0303501d1105540340d0640290460b41c5074003207800700200801c45400e440a46040d9592a0030403503003c80c20000b604034030f55019186040e082d201a80355a00024018012101100c54584e0344420094540d01c1204c054075841c041c00000e014a0341c40017079412086500020707807442082c114413808500c00c4406041c1c0c0050300a2020010100b00a403003564002c0007a80065a43c404d00c8510007401c54034001c219922481540040c000400d00001249500540c450342070752840022800a6016000700d186980007903d00242c023228201c80c01e0380249240d280852602000d40e00744000303a030740840c05c0c0a190781148408500400602d40b40c1c01c000100640300880b2640e40c3e0301e07500070a00740400343744150301140504901f982085580d44000000d800b00d60001c215500c200d0350b809180d070140140160420600303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 451360242 1250 451358992 451359031
    0x11a1c020a0f03080c0f0c0f0402032a1b1515030f01020708040f151d0d080f031b0c07050609010e03060906010302092802030c12010801050402090a0b010206 69
    0x45145050141c042c010000c85280c1ea01c1ca0b01000c2d0350301007400031032103001d402418050f206000640008011700140070b4911150f5290a000003500020700b540841c00440c00c08401d00041070b0a10300303110003800d9845689100d10f0b039101046400d021331940c840d42c00f00b142c841210314000e079141e41000d0741d504c41c1c0e10280b00141c0040c0c0f0705401646481903175480001c0c10000c00140c00c0c000c00c11542c580307aa079070343e1554076003840c0b12001c120000900896205022440c03441c42040038462020001407500d60444820380f0f410380260042a0700c078000c0400081400035405a1000c070540c283d000c151003510708001e55400a0321400d60b031260b00e01400010401c0c02580c0e000d82d40c4006202009411129185442c00180ba5079034000c0c401640980c0030390303012849000f440e848104440701145414805800c1c03504c800c0000b076000401804800805005908000d108940403500a00450f000480c190502c0e0040094242000d024012840e00e0000926816600410050f40c0115510500800c4001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 451361492 1250 451360242 451360249
    0x3021905121519060e070e130207053d02040311030102090d140a08160620071403041e150521040c0e160e030c011403090a051509011a1c02 61
    0x50300040141c90176030042000b5941d020f0316a03059034000322030001d44107240c903003d40103d1051250240079508001c0d5a40b504405420300704040040b18800f4041d11070b48100b884a501c10721002d10100213400040400c00d1003401c0c0e40b45000c0280c03c038001c525005c448000154040503080c00144003801c0c03000d040b001030209015401510350441c5000f607a07440020741d24101901d83c17001c08c9941903e009101641c40d9a60080300c0081c210030301000d854014603448812904030307407100d120b0442c0310400c80070465a080803440c00c0c008103000f12420400b800c011890b05910252580710f03082000520000703a08440c5504c4188100c0c0b4051207141c21600e031820800030703115050308014480354440b002c1c01200d407a46840e486c4503414541d10707520038101201c01c00d61543c03446c4129600144461700c00c0c1040e84080303401590000d940b46d00f128244443d682e20b01d0304081166400e542c45940c06410844c520701c00380200314100111400051501c04d04500140c82e0790075102042801006015000c8210345 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 451362742 1250 451361492 451361501
    0x105090d0c0e13030f0c03230403080d0e0f0609030414060904060f080c09060f100c06093807051605070b0a0908060f0c0d0603021905121519 62
    0x3200d034045036058036150103d442c0100d488a01180010241001502200d21440400056070340c140c2d540d0080307541d01c116560105141c4070040c941124200000400205281d00900b1629403007100814841401d07441345082c8050100301c0c110f541c0002c0200f00c2201008070885007038030140c01160b05e1030f0f1010b1010034054002c041d0740341d40003031520030041504c1800500c2c0728116960f03102141c00d610800c2c0c1c180040400103654070303a080302142d002d1101506d098001d80c5060040c51410443c000d106460745400d5031740760a030030f5801481007810682d00c0d4072030240d42040820b0035095403041074140d000d6881d0804004040c10100180440c100b111684150703404d03110300c3d801804803400a0746403010040c107a40260000d03400700341c3c503a01c001502c00022500c40d119800e9111403400d95600d00d012003a01c3c1d405038603480c1106955010120050392000e406c04840c1d0310308000c8201c103a08080c18440c441c3c2e8800c10030891503210040300d14031914105503040d400710b1560700c0d01e1400305018501b02c1c042c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 451363992 1250 451362742 451362749
    0x20708120310030f140c0105071a04032d020c0405040201020a030e03030c0109080306120c0d030c02060d140f0a15180608030c0f070f0b03040b0402240a0e0f0105090d0c 74
    0x1061801c0b4483c05100300d01500c05c0300c03002c00c03209036981c40703130010010348079845041c5000f061084e4485914060495000702180d02c18000d04020207120b45690344040404800c604200d55a1a0302c0d00b2501c60300e604014407070409070117031810801d5085c5500080d649448801000b020407480480302000da44080c01510300c0d00c08114000c0c4400d05440c03404807151303082100c8031402140b4410245400540010b080c2944c07410250100c0c129a090341c50484e03003000c510310140d070040420004100f14524078032a2001003015600081c071181055041c4e07000f40384c0c0c0500300c0c074001810841451b580344030000d4090101c846118034450120340307001c0040060109030340501d00c075000120b610b40c2111008103001c2d81010450003511b04070741c0c030b405240740180c49030f018000c40c42d041400001e00054040c0310f1039800078001820003008074000183d03000454100c0c44486140c03078010401c07802c0c164001e4402c14030242c0840310058481c41510000301140181c03840316114481c84030f83c1d00e0078000152000e030090b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 451365242 1250 451363992 451364003
    0x40c0311010e10050720010f0809030c19020102010c0311031909020315100b07030f1b05070f0f08030c10150e070c03090b120a0b06130f030605010602070812031003 72
    0x1008026805130503038001d681c040d1000440c11b0446003030050070700020440325205844401ea40070000c2421606200001c1200709103100402804402000800110716002c1c444500848003540c01e1000a094a105c031041c2014103050028800040c503840098940c8500c608801c0315802441071a42c0020f005826400b85d01402070f042255641446880300394480c118141420403195a0f40018514a101d408000360004031641f000d0001c3ca40320300800c01c0381c200c0e481480b02902c0c8550700c4450900141c0d42c014103200b603000c03004101c60340c5841200802092080061030904c0c400e140c51589034082c07040c140081c19aa01600d20302c0d10300500d107040241c21886445000351810000180ca050401c000550124658110008044002d07100319401c90480c045481d03625110591040091f18607440c503282e100b4000e00c54050408115481c000080c144c510b80e1148552450034600c1c00c03100e060b0412003c5400c1003006204a031000111141c4035144400303010765035034900060071341e41e210340e8000900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 451366492 1250 451365242 451365259
    0x3050c0304180903110a050303060415091b020708010903050702040c112a09070c02121c020303152b020a09060b19020601050f01080a0b0405160305060108040c0311010e 74
    0xa0010143c2d0058450340d01c292100140700c075603034080641e900103c440007007480d402000002d1442c01c240d00b200444000001035500c4030f9841e0059101980d0350958a40800b0410080c02d041d22541080440300400c03421000300150001070b02d004059110310f0700080c0c001d54440d41030140e420706c90110f0440f004c801c20241c6000c443c180b000c0746411030701c1174100010f02d0341030820301e4202d161200006000b204261038402008683e50f0030700041c4070025004503154003c062444041c0031150040d416400056800741d81d4900c0c000e0348104107000451034441c0640c1200d040d0020b90b18070290003050200170141410754041342072002541c421000e40080405e0381c10300c0800541d072801103015006003038040d1044038099035000c0049035a02e0091185c82c1e40005c0d43d083d050050350007800030f04d81110700d80201144480354400481d081c0c440030f0300c0c850682000106a10100d59052240c42d410610910f01114282403545441008280601000e0044044075405030307150703070007039408013440b0201900101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 451367742 1250 451366492 451366529
    0xb0a030f030c0501150510110c0a1508010b0a0f0c05010b2d03010510151806020606090c0903060103083001090b04090b0a0c0c140102030415090f03050c0304 69
    0x801d100b2200380300716040e42c200303480c43e141c001d400e10f10700099038400303002811280b8840004889009030414500c200c1e004004401c16940c4415003190050b191a8116207a041400e40b1700810385c0d00142c2c8507507412081440700503a02d5038031542c60850741500c0e25103d44000d426003406801808074951982d40018503c5050700d51003159076485034038000d40c0c1110b0164040b50003e050130ba8004681040450907000d5092255410412201148042c2e91400c58000e43d4040302c0d00c01803900039044100980c0c0311030100403c61412000207a070002a825500e030800d003240700420b40d01c22040c0402032112401040c2101c101303884825003032100c02c14008000c59002d46050084c5545028051600164100110780d0305a00301790148100300c1e40d0010401c900c1c2c0e0b4400200d075005014209114041141245092020403098806d01c15124903010005a0300e007014640740240c201400d8206004c50704040ca184003051100700800c059a0300350030210b9441c1c1e10554a203085100c0c0385c00c1403050310401780801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 451368992 1250 451367742 451367747
    0x12120e0114070b180c090a18080304050601090e1606050a0c0503120907080706050d0e010b0315190515042f0c010c09031509030e0d03030b030607080907090b0a030f03 73
    0x1d03010798503441415086072001080191521307807000c4006c0e00310f460000810307801c1113a98001c11001c81c20300c07001406441c40303955500d4542d0040d1420f0351039601000c01444001440c0c400d205c2c501004400502c0244008203161050b1035180c4148000c0c01008114290300500921040c113510390306c5000d584d91031004002c0c050b0407103019a040c0712244900c800101d030700140040e50400303903a03003510b1302c03410444200a6000500804034065540e952103d1403401242c030100100a01c0b040320301c0c001d1340146849580c10301500e41d201d401c0b059141c20a82401a80014800d5003c0345007010348000c1021408407240c13800444111603903043c0120b0004501080c0e441003c054070030891128002d0050401a810841d00503504d0b010103410030031405261000e8518590100262038428201107508414036000681072881400f030540110f9180d0000b14510b00c1d080c024641d0161140c02c01a56908280d20140c0d6034928901641050554a142e040c0c0076a8131204410700841c1e04c9010441c4044051500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 451370242 1250 451368992 451369013
    0x90604080f0705120c09190606090303180303050a03051f0605040810020405061b1005070503040209280b0307050603040807150c020c01120221090712120e011407 71
    0x29200307140200600881c2c146005401c20403c8070800000f410394503880c104100c3d5080b070103003000c5107290803040c5031190400a40101401004281c542030002441e509000d0314071030000c13031120401005446c0900020b50400140c4400842c40d1034005800d55610108260300c00812010003004100320030005525580100108203641e010780960313400c040744030720b00c00c02c0c2d010b607000e4543d0010b01845944400b062903034600c0c8005c400b207001c880c0b100f10f21310f00440403548241c48210000d80f0000c200810750074049a00768211203158002c229101c4501d41040c01100b82d108031007030644d2181c407100c3c07081c1d41c2048004050500100342964a0030035241820036a4024801100c41310394455080c80702c403200748121084a201a00a00303012000400116804503200d649910a40c0d424460344944042c0e5414114020021705114040e604010f81050b280490641c0306140912020450303400280c1409031610a0b000142003241015540d140141c0c0c6e0307075500c0d4030000420724001c601d20341408024800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 451371492 1250 451370242 451370263
    0x4050309030f014206020a060b0108060a0614040f090905150f0705071403130302010806040b0a090c0e030a08030a0513230f03040311091003020a0b0f09060408 70
    0x444a03800c405030140d500365000304001c9811886548903202d1300302500c0784001104800504d51008407420703c07001121050b07254002c407005910030b983c0982040450310410907044001d086c601d03a28501040002c102c007049005020400007940510b91040e0f104d8016a0702401000440484168440c04200010030f1107601c107480ea40300c1d1440556800b407218282900607200441c200b4031540d04d49006031038551010108446858010918005000d818006070055282030028440348910798000144100405030020340300c2c900d0306001c0341d00740e81c600300044121008210701090b40c0d00e918009503001d00801c120030381c250081285810400502c07a00031840b60506401c1045107440d14a000c3d41c560400d010024909034410795080002c80c01d480d003a01da20210300040350f000c21031814025086420613801100c01c94880c0907030030481d1a2510f4001e50040413042c138002c030305185800082485070b0900ca201e10b030390300020300508501130510460351494006004241c0d521368a2044664030740c0c05c01e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 451372742 1250 451371492 451371499
    0x7030903120606270b1602010e040e0606030d0f020703020f0f04092603040201080a02031f0b0a14030c1617071a0915011a122502030405030d030c110604050309 70
    0x40f4428a003203c00740c81380300341c0b050b440c0c1d180c1c14401009042d60840000d01c0341a0705216202c010049103558600440c80c440b0408006001c040c200242450300d0040c0c492840014060004130007064981d00003400c200700e980456940e07503030802f150b0100740c41200454a00c1c0d003060804001409115482c00b022501c081c00c2c00c000d0700140c064081c2d0454500055500a00280105020074100c201c281c01540d080038211347d95000403030098003c1802c09409910501030824045400c0b00351a800c55511090143c000c9171151861901411404141c4640d050209a15400303810113001d000e0b000d0114031200c105501696030f1400c4c6410101f40e84d141c140c0c0b00380025110600010603003900400d500b038841d512183c00001c1079003449650715019000800c000e010f030100f48150700e02186c90000c820701a07440380004280400c608204038a140c58442158029540104410421501c0005600c00c014245103000030f07441420400894a00d42d504110390400d20a00b003e02080c0316020004003c03000044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 451373992 1250 451372742 451372787
    0x180e0601140405010801050409110a0e07110a120311040801060b1902012c030d02030a020403140a030801030809060c25050a05150c030906030406061d0f07030903120606 74
    0x7181101058031403405268001203220004200c20704054008a0013107101d50040a42144e158012800344c2c0c06961150f0704078001001840012900000840325503220100a0080f00450f030303c451a44845c6554102c0c00c01daa01c4910054018100701502d01400b08040207222041d0b40d2804c03446681c00c0140c000045401c0300040304902c50051007400c640e02d02c4112002c04510341c080d0103064465485001c1180d5000411403120450b03281d01c000c5100d840090340050b1110f046082c9142c0c80300f5141c0e419070381341e4011802240030a42102c20141142d03400440303150b41e65001d00124001c0d000b0141c00c09585c0c4503084101c220201034030400c8225456440c0e5900d05640d8401c02c11100c94001d21490303400000c500510161505c02d400142034007144401160714084000c00829441d510460b425101c107561410184a0141b07140360000b2104000c803070190b50f81c00c0408000f6400c100c09070811045c595280548000c00d4041e41060002407401481084095541e0720041e0100009242c0000b11601d076 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 451375242 1250 451373992 451374017
    0xf0a1508150108130627050106080106030b0c090f060309010c180501170408040509010810050109020a050307030507090308030703020a0806121203280204063c180e0601 74
    0x141c1d81507140c0c1105039241c1115807a41a03e5a101c1080f40c10155103158954401ca0003540015450000c0a040743c403901140c00c0c11401d2107421520941c0007484181d041c01801c002260703840083c40e40010a4007412a03036000c408000503400e600110302c59030440c04c00b00410841c01c406500070000706402d500d5102c124000e520780c0c205201800e015050100d602c19190f007900d060b12030000e662003031054001504e00b03502c48000820301b1038245e100c4601a0b1042e03100240302c210a0041c1030040c10310001c01c1d410444203520240c80317408020010300c06c044da10000a5001c6104040c210000c54006201582d01c0c00c141100130007950203140c8441c007040050000c1007031390070100490401d008052019041c041158112031a0b2a40094022070403a158850030031484030002141006004101ca00180d07078610f485005000c40d1b00001d1000c00e8801314070504e03078a159021444925000c0249401224603c004c0019100039102188000d8804840c40000c900350307082d2038070240105401d03280c0324404000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 451376492 1250 451375242 451375261
    0x15040c02030d0c030e0a081c02120402102f01201911011109100c0b16050f13140607080a0f0507020d05060402012007030807020f0a1508 60
    0x50800051005900801c2110700c0003503164803d140307000c010319020038813403034180c2e40f01e01e88400360030103461140c8006004c0308450130828000680032141d420940c28402c0e01049400d41c8030008001034082e813070017203080541900c04d01100755507820121650b20000000341c0c00e01c400c0980300030a0b0030a9807910042d404005601d01d0301200b06244442ca0301c1c0381c140d010031881080b01c44060f410040c084c109000b9200c81c6428002c1c03158040f034000c40300d502c03a101c0b00200b00c45d800402c1c41c0c1c4e001340b1800404c00c401160b9880941039000c400818024204c00300084210b6503446055000180030740046201c10400b4a850810402c5070b40700854245140b0080f02081218480c100c00100001c1040100c000c085000703601e00d42c00510700d030600c03d0500318690042111107601d003100f00c5581d04514104400c42d07800004010410f291040c2c580c09814100f25200d03034030300f0540402741c161000811200119a5040003e00b0300e0319018011640055880ea0701c07038203400b00080701e10085031082d800070b10342e0301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 451377742 1250 451376492 451376501
    0x11030111090d080702030a051e16030305091e0a0305010605090601020f03040608040c09050c0c060a020a02070905100f030c090c030207120f200d02070e010806040b0a180b1504 77
    0x1010303000e105003a40c0d10f140f410340c8040c40c100d03003601070000b0000c08500c0030f00201c3c4800407002041484000c3c1c0300069418001441300c0782c1c00414041d101800400d80c8001a6041101b068490317040311031408000445407144c400c42268001403016010041100640001c41221016540c40d2110340f1000010380c0c4405000001d03522581c02030004101c020304c00c0e4241d0381c1203030140800c1d04d0b0040c0c0301d082d25801c0d03420072181104610000500d03000002c00c10007401d07500802041c411401c1125881c0003e403107800900c1140c0102c0d0300c80020038080d42005011100a0000740e025a403801d660f481c4c490500541d43c89428405841d080700e54030307c58000d008583c40d050340216101c0251010200c01c1c0c0780740c13130021002c2041040c0b503031071224001e044540701019540388a0051003620158840245025010f4018450894040c3c0c0100020000024800e4126030b10508d02452945c1d0484690300802c40c0c0040e4503c0000d41c00c00503404d0120a030f00580c044c1c54403402001007000d8010034041501d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 451378992 1250 451377742 451377757
    0x60506180a1a1912050a02030106022401060f0e040c0e090703020f0913091211070914070c02030a051b0906030c1e06160c09050702120405010c14060411030111 70
    0x581d01000080000b8420f0783d908000c49100e8200709019425168042080364422a10741c203585a0000c0180006030301001349002526000200480008864144207102e51044c402d150510850980c4d11410a009500040c071203440034008205407a00150001c100e40020308030180542034410109203164442c1c000c654917100da16140c5031504100c2c00038411703018100070801e031155685800000c000742a0210b40c80d81c0350015a144104005091491414080c040c1c0c0911089440c002a80c82003141e0300b0b054030f80c004198105400500c907940040390915007040401480340c043e403107a1503185010b400c0f200f060310800365101062643c507801030650ba00400000f455010100198220034840b25144481c00714001a0006040c0402d0300001d818040c8581012121803070b06090600119105200d00c0398001440d100070417902c407401601a00610030b5000e66030401c010066820b0a1100042034100303d0b4503810101c0d20607140a00b025003403881d0513417903540b09500f494042c180e115004000e550b00d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 451380242 1250 451378992 451379039
    0x703031b0f020d06060320150a0c171b0f0105010906081b01030b13020c0f070302090f060a0b030702010e0c0f01051c14010e2505030415060506180a 65
    0x28050250200070f10403d00c0c150403590701d520780c0030200c0041c001080052000d404615801c0100f8901b501700110b0180920000501d40403d00281d104594007068100c0c40b10b8220f0b5090000c607035241c3e044841c0d881101d00c0920800c07890410000c8100e070019a1180c1401c541008100b5a600e48110074241e404601c914100340d40001d8507001f4030301070f45955080c406414140052451070440110300300700100200c0d0b810070380d408a900c0020740414801010981012405004040e003954001500f038000901304100c50150100058901e4807040c1c10000a4000c05a082c0e07201e1a1000d0f009020740780d00e080c1000a401948074107013490500240312014a5016164079050422030103c004541c403c8c00e030b5410119031151003540a0041589005001e0407406240e0412440e10115a4075002c420440040003160300d11060b4000d036901c501a45d40056001310b0382c0442640998110010342100c0e001140c1c0b00d5000186c103114202040d2000c0381e11241901c0d034049480d9194115001c00c030107100230030340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 451381492 1250 451380242 451380263
    0x10c0206010312030b0a0510050d060b070c0b030403020307020a09060513061a09040f090c031a040507051210060e16090f030813030c09020403020a14010c060e011d0703031b 76
    0xc3d4180290004110a4405846140c040c5e6030785c0c0004090007050020040490310003e1061401c3d201da01800c0041c1c8400490300703140c50780030340d03984500481500c0385444441011010808043c4240100c40416030010900942e003030b11038010400400c0144105841048041c0d50b044102605002d828211040080002080401c4d0450301c180782d485240c81a50280d0b4030340003151002140c0c82001c800728010202004c1d07490071850600b6070b030f42a00c15520090704800e000c2100180f0009440c2d8260307132055450200750340e03100d0788692421040c04540510741d42004004202019030315807561144600c0280107034000b091002c1035850b0b110b18018841146006002031010a06120003401ca041800c00740c11241c0e41ea940710b80c001c0c00da054005198141e000603080040d403400a50750009042e0314201c610031101e41c640042c1600004150040003a900c484250320030f80000e41c04015a00101698150901d11640c2820b4540e41d45000480c00705010302c15102010203c4098000042c0d80986a46c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 451382742 1250 451381492 451381523
    0x1e132c07030c0504120b06092208070f02040c020114070306030b0f090f19060c050c0604171e0d0c082e240206012c090f011d010c02060103 61
    0x20042d0202c56071540610508100000e00060100c11021002d402411500c18504205081010240c0701800961400c1201d2252490100140762030b21881d0398047c0b407690340ca203060302c0c10b691003991b4213001079802450f0100c015912070701900000d00c1c00c0101c400c548a5540c1d00720050302191072034040035204c00d420100003184a054071074002e030801050002c555101d00740760303021481c042d04406144501203130ba03240c5408010980c040d2082c000c00d1401c01d0f504240d05080019a1001c0040c00a00088080c021202e8800c81d248201c91800c940740c020112413001c80c00300381c9825400051644880b138945188000d04074800e103c0369005103000e094541a034248481d610485d841001c42c00301b01681348203030000f108246074018821108001c08035011400e0b00c00400380c00c0c520140d10251342c0e6030b0000103080705c810441012890034504406940019119255800e10340561802d40307803d20b601e4940c1503001c0b0200d8100301400040c001c40280001724544078126212682071000410540c61386008a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 451383992 1250 451382742 451382747
    0x120302130512030d0e0714040c1d01030b04050a02090922170c070f1d060f0618060f03040224030f070c021003020c011d070504021e132c07 61
    0x445070044030741228113049690f000681114003824041740300707a012550401030405d101708000d14a120880d0104220502c0d040302403c40b21740c691506100341441c0058000b42e83c041c1d801512160307c054020401c0d03181c6044600e00075480360015902c2441a00002154110801c0404003840041e03188102c0c000a02d03035038100b0301c0901c4078580307990050078090407580b034204000308001001010001d0141c24500499113055030a00302c441c0c403c000c003010400005455140b001c40405000350f0350303641c0c2d40100741d0355503004116160206601c0040094001004513140c2c01a5000301e000300d500705400403105000102d402041810520791131414030000c1c180b092080c482e9030f440512420b10f14800d400b41e40c0000d070b101c0d40380e21601011030350100b8800700808007442402081c0001900f40d00c2d801440801060b503800051103000c0c4516000903105200e0040415501d00c407807a00c0350303000e07200ca171210403131011114540036654041d0542d0700034200800b01c88424844004682810b0300d40d984440104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 451385242 1250 451383992 451384009
    0x4030308060d0803042108040c0621050a050402040b03030705190206090315070e0a0501080112030306051003020c10060e060f1c0b0402041506080c09030703080c06041203021305 78
    0x80c55004442c01c0340d10b404912400001c6204a02c60011041d0340d0010f85400000b0b0480d0207400d070f040101c84010840000c0c03000c213584007503034080c0c00c103040e041350070b10b054810401000160341000f40c14001030140700342c13950f008503018a1080b00c0a000101c040c00a040e41e80c003803010042c007564803609a0004207155a02040441e50000c0c0100b840c1040c0341c00424a0191495038000e2191040d2040110709644a110041d0100045420014003460000001d0048206000302106001068440010107010303500030b01c0205005410034030307210020b40c80500250042c0364080c2c124020250800142d8009200315402d503070081641031025142d80061019208020250320b402c60580c6401071242d2001031043c00c82c061154420f41c07032515161050005685082d805800c1c0e41812130003c2c02040e800c45181d5900c0744003000c4440d250110703103000924040311a44043d2a01b400041c0c0c0c1e0308441c00208446108901402000823a400380101c224120300ca00b0450000e0508015401d120354500b40e81d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 451386492 1250 451385242 451385251
    0x9060804030e1c030e09010b120a150305070303030e0303062b0c18060e0106020316050a080a0f02010e070302030319050d020c03070309171504030203070b0702060a060b07050304030308 81
    0x104a2100b42c03402c00400d440c1d261004224240300755540e050010180d100c00f030403003a804103843c0d16213a54542040b0061a00031144100d0040c406031000a0a0f0000d039030090085448051602c0c0e07110f9900d080c80d40d141c6155010950010f810900388a02007640041180d0040c5405000341c408843c498801e00601d03114620b10040401500094030003040a094611000d0840c0388050f103c000d550250345d10071213015a01807040c41c1400340041003216004020b94a4221080880f01c078900d0441c6003890030010303820b0b00102915808201540c04507800101c142d42130722240c000b0026510305030b4846540328140c1c0f1000354540c0c000c00081d21102010010a80d04d075465003002410304681c202c00c2c2003640c000706100314256101145003024141e00c040d1400c01452105105000c1c840c90b160f40c991190102c5040310100b461100100e070800d071080027224036298001554440f41d040921000b9191a000d941002c40079041500100b20044140e0864a441e58040020341c41c1070310b542d4056511020040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 451387742 1250 451386492 451386497
    0x12020904080706050a0c0f030b1e060409020403031805031b0103021c0f090506070512060607030c0204090b0702070b09181f03140105010b040e061521040507090c0906080403 76
    0x2d500012031a0142c203001d5203842401007589141e82000501502501400c001014100410203603e1380b034800003680014041d07048528604400008101c0500c256481050a90f100140000a059110b228150038800781040a00000c1e43e99080641e00c03c0c030940100e030318403441600c0c14210340c0a54001e0400014041180708040303040001d1808843e00000c070f88010030b40b50a4031108020040c0321996101e191800c156040060a4030506410440103210314022480001c103101454001d901005403240d0003481880211303141d00e0410201c000607145640503225a08005c20018408020382d10700290282a42c03800224142c01840c40c014050904014000b142844c4161190b00030079140141d4015441c5503564560212a242190f2050340039071100002448144420550700d03602c4c079006001201d42c01500f02104440e682c05120301781401078640c0308440649141e0140d10607117803069010301c0c10f55034030a540d09400d00a8410365006480018510a0240007003030150000da41c0150081c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 451388992 1250 451387742 451387747
    0xa0b130e0c1207030b0c0a0804080d0f090f2303180f030a0309150203130e27010b0112020a1707140f030a0f090c0504090f1208071202041202090408 65
    0xd0012845240c42d91245003540e4100e201c2c18000c1c081c03160a020b8108081c10040361030400c4684004108801c0a040144103c5001400b0344c0280004e0300006569528034100700321a0b0068544005003260900301110007a084403003901d46507241d26240c425006d440d001851502d40c0c6806000115004683c160780e103c0d080e05091409610104403400003580310b0f40394600c2c40c034184881aa030b600e6400e503c7c01c2c1150300801004c6010850b0001d600b0485012030b10684081d119000c100310000808c00c3c0461004005541101c0c103000705421184a003503081e241e0003151a12920044168881c3c41d0b0150081051645103940e080c080000e0705500c9a00c80c83c01104801c6e02c10410100c592028000b00e20300d40b000300500c15000603c2c46120807103403d03900c00b00700c801900e0f5580694904a403042070304c2980e54044060a1000700d0b201c6108407a400441c0c1880a000041d0241005406649000001d007560344818070403c102d1080b50b041e0fa480030044da048903070316400c000300c00300003c00c02c8820000a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 451390242 1250 451388992 451389013
    0x6070807050703120f090210020f190c0e070309050708010c020c04050919050304090b01030216020904030504120b01051008060d15021b011b09080a020f040209042903120f09010e060a02150a0b130e 86
    0x1c100c00c071806600ced40e55000c140800181000e0b40703000d0150f08002d401d42d140c4000c081c286030300012000380c001000c0c0c03404125075946103042401c00070320f82c900c03c60007030600c401c00040000100040c410f5403000c803000c0258119020045003240901c000d03420b03e0090507400c2e80013610301022030a901c07038441e1a14902c0c1c1901d95601280100200c038048901807210001481140340032145042526024035040b0110700d03040000841c800c00310400541310040f08140780c2001c048540490b00390005003c2c016001c10000e0840d42e00901841d0300e0300800b08007102442c00c0d1184254088030840d1400300041c000401e0a4003001101d118441c0751035400395003001010070b1a142d03406040c031800443d075003400c1002000c51850580d5002140c1041c0300341c11000308404020300c0c030015038008100344030b0456101d1203140d0043e02d250300c4045800e9070100000c103402e12a0740e800617203500c40e00024500c141880e03c4003040082503403030b001c0c0c400c3c1c6e00901200c1d01c40078000302030f131282c80103089100850344103800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 451391492 1250 451390242 451390259
    0x71412070311040f0e1905190c0f0506070c03080a051605010b010f0807050d0510171f0c05030105090415062606070807050703120f090210020f190c 65
    0x2a6104880c0d0000e0740c9407200c07007480d00f07100701d10075410504800c3c44050885d1500c5070321021046800e1401800450014007400400c000b0060090a59103051044070842d0600380001d00340c51091101d000c2003120f011405007001006c5d01c2c5810b91009402c2d152500b1035540030b21540003000c849041140520072946c46403d040328829030f460080c070001440c03242000004204895980311002402041c5062000d0154482e0807110044502d480020b010348940001020710004c070740c00705071082c0c00c152004164100c049a50190713200d100041c005021002048030042e107400e0007029010a6040c0f0040040d82030503031038603a00a04c11341c1640c1c80c4d2810035825a0072142e4680041d22030a03038414001c2d80740c00b180030142c110f20007618000c00541c90208001004d000004100e007040020201e02c40c0c1c00c241c0078007010466804887c100348030400c3c44800706e400030b1056102c103074400d454221040c0f01c0c50340040350400400d94450080d040452100d91880c690600c4080b040302c1e04030000000207070081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 451392742 1250 451391492 451391503
    0x14030903030a030204060807021f02070201202b0c08030601020f0a0602090f010905030a080901050c0d0807080c0c10021602041505010305010e010f030b040f020d0b070f030608071412 80
    0x84658030f005803160700f0b200e402020040010060001e543c8140340c0e24800054007512442404000b0001681d5201c0301d20048030902551000c0342035032100501008642c1d4000f240700f61410500c441d1448844014171030052004815200c04004100300c0111a00404c0c00d44006503409501801110014402d00303408c00d20f13180c02c00b6020349200341d021480942e41d103004e2151203140c1c031091a20704115810580042d480c4d03030b11844010980e0000295082d1542d01500640714603401c00ca05464401403001c0000d0312440301224801c002a905500090020765208252800310903008000c0c40c03a085c41902c500029401101402602c1c419a40101c1c0103944501440884481d000e80c100f0040346044000340c151801a00700250001e000d02c018001ea001038903810040f241c0082d41030314240c03a03506003000041c100c0003010750029106000319042c0950004298003889080d070320401011a80082202103c1c6c10703004141a076005400100f05088a400074004200d40062000c240c0040d000005c40c5441b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 451393992 1250 451392742 451392757
    0x60801110412032f2b050f07030c1b08010c030504050606010815031b040506030d0f2109061e02032214010e211309150509070309020f030f0a1403090303 67
    0xd6100405c0d800340415240c940140b600d4441c80d035104510000314014050b401860a070310004403012585109040c401c0e2201d07954240c00c0f1588081003d016000002c00321214003d519440d800c00c102064414400d11803a80720703507001400ba080316260321004548081c00a014011202c1e003003844010181e40a105000515404006000b00402840180025140010052446500400a81700444e5000700011404280a00e0440d00c480f09465400e0141c000c00c9131104415071615011100b00031b4151702c0301e882860720601441c41078050341c03062020b074801121035107c1c0d00703200c42d400703101b01c0b0540c298490030520078205007118000d81da6001e42112130540d500f8445902c254504801e10000c0843c001c4554800092a490b10006010394440d4206601c0703016001c40e030300e02d0100c0000003d0a400000703040002c0a0007100d00b41a03070014054000c400050344190000000141c062034001500704c0c2c000c40e680f014007141401a10b0b01350700450b03251481c0c0d00d5800104068040c5540510003000326 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 451395242 1250 451393992 451394087
    0x3010e0313090e0d050301150909140f0a0504020f01120b09160f030e03030f09010f0608160f050f0105090d1b0e0c0306030a0611070204020d06080111041203 69
    0xd1500e07074584143c55045042d40180c0c0c010782020008664440122415100c01ca0791400d03502d01c03041c0c8100c940d03483c2e81e84140c140c03624099820740200014000c1d140141140d440b4580c40b921010a84030841d00141c50096000100054500301540691040401c0411300e00c00042c10100e0840030690041c8221000f01007180540300b09422590010352030781803480d480c541008000b583c080340da81d60307210180556105070130b40c0c0005404034009401c0390f042c103e01701700144001690b03410b04071341e190b80007900c10144016003580415107041d120001c4044903030042002d1241c0c104a0015070396588120401e43d04000e107084c2e414081105441040042a1000c0006050a181058141c00600c0207414024441c8040080c441c039a070b030004903500125044000021011032901c4800c00520401000941260010071b1b4103088011a520a004032440200288414042e041d0040d45502c120b0285900030360a20200c100032921800700c82c1207100091030a0705040c2428418540241d0408034030000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 451396492 1250 451395242 451395277
    0x30b131e021002030c03040e060a0305010c110c061c0f06080303161b031d042d18150e012007063e0d061508010803030106050d0b03010e03 61
    0x8500701000e403440c402d0391510141d0f00344020b000c03e840d1280b2036803244c10009400e102c0415615540c400d080d4000f560700c00000c01880400000c05020f69010b61645d03841d6025041c3d03c4101801d000084074210300c04e0700c42e00c10030402d503d0340d00c1000b401c1c2c1200c2d062001c0d58135200800e10150810003180141a002c8000c1c01c882c042e520010050b054004040004441c1034040c1c500190704031009881c05400b25111180c038081c00c0c40418000c140c01c1e0890924010709580300c28680340810017a40503648a0081030112900c4011044000d0050190040c0107560310503070204c482107294000c11100c5030740f0001107a81020340301d08600704801c805407043c69480020b141d0742000000d104a0300e4084401d101411900d94408000400c040303507641c08075481c480d840030083c1c14214801141c60050941d88104601916901c45c501c07590300b1214008040f821650001c02d80020010580b4101c80c0195515881c3c292101d00c0180500440588690159220025030b01c00b4801400a0315042518244019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 451397742 1250 451396492 451396553
    0x61119030206011a040509040f020f030105070c1406010303021504060207170327030306060705010609051f060306050f100c0b190b0105071101110a0c090203040611090a030b13 77
    0xc022484184c031120a440c0c0801c0304111039210303031401070360140d0030031a046a00c24050000c100b8205a8600c403a0303042d407a0004001c4100d400c0440b044825000b800039103098511211460703a900028000a0050784c800d1041e940c104014200c00e40d0310a10406000d410403900f951241c03884404180e40768035514010080203421001c6007079004440340303c1600345022103591241d031916444054460760090000080c02c50620909410190081c078446e41c040005181c503940014100030400901110b5101e4040c0024016120707014120690301c00502902807560520100001e10302c00c8800701c0d05016a0720b070a6000f0a020a120768484c04000030401840318505040c84122601d0035101818060305201c4ad00104105009000700e56800382048001c2e164400607680c90414a4003008080074a10702c00410550f8443d0040d501483c400d0380148a03141c000a81826180141c08109800c60341000c010804142c4141ca15500214105c5100005601580325140c002100d4621036401c04e0300c003000c0c2c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 451398992 1250 451397742 451397759
    0x60d1205040e091b011805060c070918050c311a03030a050d0e0304030f060902010806040605010509012f0c030c180112170d05060f010807020706111903020601 70
    0x200e5004043d10701504034150f8031a05000d0102007907003064100030040030418442124443c84401412000703103a1501c1c0c29080d01c0180d500c4480780500c0800608000300169005070000300e07000d085a01a0242c2004058801480001450340002d01824000307241044030301c000090082c000f003c880000858a10740a07032080f0b20302c1da040c601c3e17540250301c2040f5003409075501c10300742d840102e203028010480c014000040751460045400c040c0c6090400d040f00e4040084c00da1100d040305200381c031030320381e5a0f40319002c100841e031603846581d0210303104018105456100c3d2075201842c101041d22a107081e40b40104040110441c4c01044c06a80e001e5540c500322442d00b00a4140b868904440c0d2403d48a5803880d0b020b0851010f00c141800c0c404010600002c000360703150142c4542c8007000e0210784030740c45220f4110140c44184d035128000d902042e894540c41d40704040d01442106180c0003030290500d04481180c2d007804410111005029400001c80245101040082094040c0d0300818695040c40c0307a8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 451400242 1250 451398992 451399019
    0x20a0b0705030108070e04060e060f07090509010f050405040c0305250e1003120311120f0f040b070f020f121c020403050703200a0b0c0f0303060904020405060d120504 73
    0x203024450140010040e1400000e0b8100076181c01200029054540d8544400541064038082444d0702480f005c00c921244001e000d64030649040c0d5510400650303420600c0320f030300000e001e2030010110042c0184182e00306902301c103400c81d105081081200341c2c1e94072102d0429140032000425029900340d090b4a008618501c04054074584000807040c0c1080380184240341110700c4014241d9a400181140d96030007035001080e62000c0d03e000720340d91003074014902c2038514102c6214040001788004100d51102c0b00b14502d124903030101800c2a0340d283e0807000d981d11403070380d184541184544030003801d8000d4140321000c00628005007807900c03007200216001e01c0f00c51800c48031040b80d1043c0010404550005107000890380c00401500c8810300358840030b480302e964880115009800b00200080b5996000c004200a17039800040c0c2e0905111444010b0312840140c45041e40400350b240850054985503002c25000640244440c0543d003942d41d92450841840b032009020400202e410800203101184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 451401492 1250 451400242 451400251
    0xd0210030501090b2d0105070b010f0f060c050a32151609090f02121303030b041505061605060f3c06060906180a0e0105090a0c1e020a0b 60
    0x1070601c18001500c45034160761007200d403103a000b000e00e440c031707640c0700d90040003194859504100614500d6845040c1c42c049281f4500c50100446000d01d130001d546c9105d202d00f40d202640c400090400007149884803403d80c140c4611411160182c0406600191032072540c0d50303119082c400262003440b443d41075040c62010010507208035450b900d0600b180c0c4c580c0c80044001525400031340010307030b07020340754405000380101060a00039125010901c2907107900348030000c410034840c3da03050014038290400e00007a05da1880c401c0c800b00ba81c1039414826031800c0c0d80034003405031002c90120101d01841d1905454280c0c10307038882803142005801d010368144400b002284480404030400c4403a620001c1d443c100700210505401c80e00c03c0704005c00e51a90320101240d40d010305c010120342d19200000c012040c810804e24442e03105a96070280001d24086048016040b1341d0000d0116245590300038001d0003401c401014082004180b01260404425074480100040d034940d0051240f404203103401c9001100c00341 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 451402742 1250 451401492 451401499
    0xa1b020a080109150501120c12051606180801060b0711030f0109080c06010b0301060e01030221070f080a05090703150b09150f030109080301060f0507050303042117040605060d0210030501090b 84
    0x381031f6004590803d803880203c504080040c14654111f041050074050702e0410410a03024851000803c16442080140c1c5000f52000018080e980d5205150885040d8071848002d04414806540498550407540e5580d030b13030190a4a00c0d90010086840c00c660401d0000c45800101203a11000c8203400c00100d4050f00114400034034650604101402c0814a101e801d410180c00284c000021811704950f0354080e88000b40c43c080908000b00040e00c07003120364201a000500c2c039400030f101c440040c05035034002d40c001c801815005041d615083d00d2032101c8443c051503140c0750080d9a409440d8500c0407032003110001d080d24590411703841000200707001808000c0c801da04180c0c3d094003040c8100112411951103050000001e00440b0301036405005405001e011800040100001d025071464180c411800c20b00d128602c003c5002000c0c0c0d0901d14074010480560880720000300007540139440f1980002d07000785200310340402c50b80003401c440a440b8a0300d0000782c40d64010004510240911a600b10045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 451403992 1250 451402742 451402769
    0x3050108030409020d021b0607030c1e140f0a0f0909090c0b0901120e0f06061c150b030a030c020307050f1c1704030f0b010b0a1b020a080109150501 65
    0x502581d92401540108590250f0000d64428101e035590704407011412030020410048424403103040d2121000ca50070300100c3d00340500001700c00c1c810003031200a0b203121101a12581d1140b44100e40c0a9914004514801c008001c158134040299014001440c0e00d9a41c1c0c400d85c4c4201013008207451240d512100c0c110307050011003000120034220200c00e64802d00001c4c1d41715040840100c2e00c18000200c0f01d1540c5282c440070b10820103000c501c064440d0304040c00c54046484000501c065200080184005070707802e07480850003e040c00c0c103c8540c160050390045204c5170b40000080c2003001111048011460140802c02141018010840140003c81d544540b00168001051034184010007143c0305c00741e1404c0074000c214000e950110b845040c0c0398140d07110f1341c0384d00d0601c40f004000308040d113201140c040009508172907081201c08800042d5942c283c2c0521840740324041101e00c0804980c8028401008140004240f240b00c0c0c041d809180d0301c0c101100d041c4110400c85506800c03900004044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 451405242 1250 451403992 451403999
    0x80a020315070c020d0203010609060e16140d021e0c061f0b09060313060e0d090b070201091202010c1401020901030e0c06030c07030c06090b01080105180d05090301060b030108060115030501 83
    0x541d4030500f40e40580342c1c0d640b4100701e0f2001031300521003504000300310f503d812004aa0381806040b5a481140394446488844a403144141c6511202c29482d5800c41e40800c49000d10716200d8000d00000ca03c020400e02c5540c100700d400c0e5000d500900300a040310782c8208200006903100940c403c1d007000c8942d2145c01040c2c18031a503420700307204601c01107000720780002c081050b80d07118240781d80f141c50f0426000c110360181c03414140c4d151b0340300741c1059001404030000803903075640c400225480103070b0585038800c00d2480c0109901c2e03c01c403145800d03414811549a031401040c0039080010107841401c0005039104003100001d000c0b950140381102c2d40b0350101113886205c0d1a00303000c41340c0082c0400141a11101d2500e4111680c0400800060101d800c0120600401c00d500c50114140c440210080c0300940d229200248480c0440030810465800a140d00c100c2e1400b410081c00080030103000820883c0e240c0e003c4042582c03080e03001c00c4055101000401c001354142c038a01240030f00e030b807600740b1080d4034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 451406492 1250 451405242 451405247
    0x80705060f01030201200c030a0f0c080d090311030a02030109050c120316060b2b0303060902030f0406020a05090a0e0601020f03120105400f0b090a0c09030b01080a02031507 76
    0x101700c00101d02c40d02028801501c03249040187c50a601801022545054201e01c3d25180d035a00007401202c0b60070203c040452040b80c0071402916140e4a40d440400d240d1440d03c6031034000080001395070301802013901d15809a2000c0c0584450b0034040c8005008100b071b040b05004032800310340c02000264109104041e201ca01390040c0400c06600400b011070350880060010b48800200401b0031004011091510344461070104030704200c0d03000b51010030200741d941c4a40010b91004803400325840c20342d03900140000382e069000d41048400c80c5021400c0c82da2410101c1c4000340300b50043c2c1c80014045c000c00200b03603810042103031810103140180d03040042c550201c100d601c0d0103004407417054001c0201500c6190000d01c00f200900d02e008100000c803108014030040d0500301c92500d800003428281601c2112442c2e0103600c07031500010300301031256610729406400800784451840d01f0400c01d100c00002242c1741c02c848034081c04101000c1c00e28608070f0702c1010f10307221842260742481e001e8281002100d54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 451407742 1250 451406492 451406507
    0x121a0324100812072901060f0e01050d0e070528050303070b0115021f0c0e010318080d060e1806150108011e081006030507090e030912100603080705060f01030201 71
    0x20000b15250312111103180010081d400317005c00c0c3c1480a100303a5803a1030b040404006074126000743e118040c034806405001c44500303d03480315050210300108824041e0543c50f5100003102d506407c2035481c0103172200b00003124803080301d40159180e007034021403511208807080c0b02c0004103811401586840c2d4290f54245015405100d0b90b0ba2010410304d030341010600a2011200702440baa0300313905030310015044040102178105000c0005207408040107681d501920134225003c4000700c103122a220300390b0751a94030b50b01074000345401548890300059299a8140b40a00800c007584501d40300c8a000440c10b440c14000600c0340513802003064600125907002544c2506507044841d00440d00b5407213079005601c0c0c41c241c2d4080140d078480d402c01a0b07070410440e402481628415425900c81c569503c91070300583d0310189079200c903904200544003203454059051442102c0351011754011030590000a021100c2035842954035400029041e420490b09000e41c0703510540c80c01c4108070075419500001e2201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 451408992 1250 451407742 451407763
    0x714070620010915050123130b01050717040e0705040e0a0902060c07030303050615030c04050f31050a020a09050402030a0f060b09120d121a03241008 66
    0x64000750400c01c1c40ca000390081032406400285004405105104c1000106002d20890164a980b010f140c3e003409250b4600280c6840c0080c502504000110202d4000b04942c1848a051200820031400010305651b402d07141007078005a000d44480c03a0513500100180000d01000c10003078208818130074086404007050300024202400501a4124404500c0324890f65a40002c40d20800e1000010564541c00c0a44a9007055030802001203842c1402c80741404150307413000c0381c40d005010074401810b046140d46040300004040030301e102c015010711000481c0021308050302401001e4114084c2c041c0b401040d0f001204680c4c210f01c0c00000140081086100e401114030403a000008140e00c407000d07400401014130702200803ca601c0d40e80c101c1c03000d00da0100c00d805010f11419118180c0e44007000c5504444c485260f00c07905908140402030000401d0301242c1d44100801009070114103131000c11800310600d0032040803100c4503810030102e010b42d100061146140f4001e11406000008011500b10f000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 451410242 1250 451408992 451409027
    0x408040605030433111305090402030309130b011b210e0a060c0204050c03040209070f02030d020a08090f210f041502150a0c0f1101060e070507140706 66
    0x80b501c991a040f4040000c0405114002d1083c15100c3c88840131280304001c0d449004c1c00800512403c182003420340d0103800d407070708000b042c103032000c0200d400c0c101c84840e03000c1e100406884c60052804002001366081c5c41103190080c0e44c03100c07076802550300280702c200f20f42e8a222000c161540c140e0b4443c1c0317580c200105016000609120310310380d118051032404021200c0101011007140e1100002480e8014441d01688140d090001180c0300d03080300b10032a402550082e040c980b107903552280642d90104011040c80451104001d900c401441c944040c006450080d52459101d0400900007450b007203d919985150342c0141c0c00030441e50100c0000ca003400c03119210000c0e12600b00760241d000900650740000e8103078071101c1903a81c08a0b40814040494800e004407203480c1d840380c544d844104d422003010b600106004005103a0000e010b042c10480d00300b0b01c2000425100d448102e2400c0001003038510f00d01240b0045191000c01036000c40c121074080c0b200c40105440c62500200802072002560007074507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 451411492 1250 451410242 451410247
    0x315100605032e170a0b01050904020303070201050a020c0d20040c0915030b040606030212100e04030e120f1006090b030c0103020c070e010605090a1d220c030501051e0408040605 78
    0x8410100f05022001850203a0342481c011440c065104c1d00c0b408020011034420482c41e00103c0c051070002161070155401a00031030030401d441c0e005403603e522403c021411340c42008880715555444c103401e41451407144c0201505002890240754440f0740d589009880b0364200b912203820301c0c0d40805004210b425000c60280c860707083da50280e0040528542d03180d0418240700011030125007640081c152078241000b6840705550f8085511984015402179100c6100d0070b03404580443d10454200405d850010044482212030aa0b00d40c5802541a5aa00541c20946070201c030500f540c402c0c0e000521422405000d110320850000b51a1801182c416042c950302003500e9034401070400180026003801a5201c000d541c551101071b0545d08440d130054410f051032000401c2c10712400e080401c80000061f00301400b900c03910701d092840c7d12509403d50903803000504c602e010410b0700e2807200045001d00000500c41c100751228800445d80490440d841c24402ca0501c400a5954000c0b2400c0364120303d84140c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 451412742 1250 451411492 451411561
    0x20604021c020a170712050a06050c0f0c01050403110d271a0304050d030b010c0204320a05070201050c04030f050106091a101b110a05031510060503 65
    0x500c40c00940000394101c1411200481c0c00907400300042071046000c400c4641495542c2106c5d00c402a40c1400103082d07801418071100001c0c6542c10444c0c000a01075074040c1442010710001e81c8a4202d8030b05440d1580d10745003400181030704082002171000010002c0c00008504007405006110922280410808000c00644407485078903514000f81c8400101c0325078a002290078140c181d04242c030140c500c0d0203041d10310701900d4061b210741082c0c0c41041e1142d150400c25034003048018200d81d046041c070b19400700d640e8401604036050039030341c1c3da00400e600442410401d6258040311002001a4156890042440404690072094404481e84802035140703141652034140d0140100e03a10a846180c2070160207000302900e010304145000c03050b5201c40103811100001c8943d4036030316a88800082248030b1520200b114180c2d1030702c001902030020131541d560b540c0072901d410290410080301c844400140714005004103030728401000b4600e481811030070010302c044030040302c51500344283d8803981d8519 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 451413992 1250 451412742 451412779
    0x6140f090712050a0b070c0b07300e060112110a0b120408040503070b0403060c0e150903030f070b011703070b070503040203010b030a0b1005060f0409152408090307020102060402 78
    0x4d90b82282e1216107003a081c00d100c03401404400b07152504076103404050780019030b1103110301e01c900d9107808034070b002c40a55140c9035207200d40c6000340300e480504140c540864400701541002258001d10944506400034070141c200004201c2554103c14807031741e00d0000c100840524941541c17040800640907140a880d1440d004015104c1d40c1e020310f03003502608000042c64031030301001d17108580c02907105000681c08039100700c504488a0001035408440081001829030034140904804107028003200d103804021043c1d0103154100240c00c07141c0c241c0b0040140001c00c40381a503c1d0103104202d00540c1003540583c0c4401c00d00710010200c1042100200c005001c0d95001d4105402c011400b500780c1d440481c450174206c4000b031040352648040e039201800011036040c44003c032440d078441f0a0030f66080c0781c140490f04024000101c2c280e01e0403501044082410f051f40320880309132010b40281542801041071010f0a000c50040c204001034006100c8a80541d070041903d42e400303681264410200d0803070380b100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 451415242 1250 451413992 451414003
    0x1111b070515131d061002010c08010e130606080a02010f090b030c091804060b04061a091003021e180103060b030406050a1805010b180408070308100b0706140f09071205 74
    0x503d1324a042849404089011000c00300d000d61000e82d01e2190b0b0080700c01080e4243c1d4000c186c2e020001d80e141004008900c00c06011641000c081001e4051004198643c00142c0308aa007100d5000e810082d495803c6680001124807083c505080c555103081c50440080c90302d002c0107203002c105a800144030340d510b944941e40440385c424080d5400720541020b043ca1380050814500741030089180c0311011400c040c40d01c000c000071400301010070b880c0510100520003900d0070a060803003856001c0c8400c019548a5840856491201402c910b032103004c2c0140329050514140103041c14103180581c00e01090110304100c0c0d6119404c101c001c190754807883c0044c00200320f01d0b00c058020035a86213a4500f0000117400c85c6805002c110380707091070721070715002101008030295001080c40f00f04200ca100001c0c050800c10741e01004c00901000f40c5c0b030740e51054207441e81c0100c100702c03003140c0d94182c000c10390016000c503940c025115484c60041c41c9040005180c0c0c80c0034500600c00140081a608402c02004006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 451416492 1250 451415242 451415249
    0x14280504080d1107060f0209101206050d1202120f0340023d030b180a1505011d190905010617060a0312020c0301111b07051513 56
    0x100400159007211540c1d03a0000030b0202c60310350500d95001d5000c0b1b02d074021345040b5500180580c0340c05983d01010b0301d8000c00132181c180b0042d1256400202381da41c840c403d022071801012503400840b41075034001d0400418080302440804140510080d07007012074180d9910500350200b5084031014403407521020081d110009400052285403d010b801d0380082c2d0f108541e10994440904501c000704240c45007080c02000317544e00c06880e0b100c3e10290944503081c5c256502501300050307103076559030206102590b680700c070b1241c3d682e0360018014a6a202d11807131642c1f8121250a641e034a051500007450b0b6003070411152541c214400013800d29540c1c49402900003030213460f01036200e580c6c0f0011900900000d02c50800400c2e032800d0701c0c40c00484210380c440e1050500038407008200e415503503120603510503240400300718490701c0e291041d00e071401d00c202600340e01680708030fa0310b031016160f01c0003524040031034100e89a040f4903410071103504c0e21080160701c030003560120794070341e01490266111481c5560 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 451417742 1250 451416492 451416517
    0x706141008122b0204170c030303070503041a011202010f02061510120f06030b06032e020d050703050108070b0c100b0d1211060a0605060a0e040213091428050408 71
    0x126403c10800722940244201c4d4030079552500740c40d014030380540d110210001a5505500100002500284141c008550140c800ea8080380c441107513158070614100241c00410080440c0c18025096680104031140c08420a1001f0710031440d280030034000c0d4040003200e0340d001e0055040301500d228000c4084d030016981091081101c0b00c1d0110451024100b54401590002c481c0008144141408500130013149108040012888805500e82284406906581e4220f990034488020301401d50300a181c0165050b0f0b802189a506008207941400c1c400d038001b50a007032080001c8425402c010542490080e0611000501e400d00e48000c5414429000801082c510784a030310030301c0c0310b50411507201c0007005a070101e8500350b80d6a90701d10100da50600445a0180c402e11903400308e24071648104503c50000382015061140d6564100d12190b295040000c0c51510390054061003c501000180c1c0665540400703406041c0c8142401d4050f0b240c8503045a0340c507200c00020b018030000c0c02c11a604a15982c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 451418992 1250 451417742 451417807
    0x20111010c1806030203060d080d0204051507062f0c07030506071206060e0d0f0204060e01080d0e03030306010c031d130204180b0303040504091502070614100812 71
    0x502004100c510402820200070340390720b00100f07007284a4800d0740d00c54403010b00310491f08922034540410b030b82c1202ea100210241c08001c0841c058585a0003450080d9a22624540300c02d2503151410a5030b07280e280003152452a40d108200604041f01c1603600b2002204515503955465030b0301c01d0a01000303410141070351043e501031210749a0f11408c5000d820022050402c0503075102c4104441440056080c103a014040340c0450000c034800329503502003103100030400181940d440c0e40103601030340244c1c0000119048400e041c54020b07003117610100a00c2084000d540346141500003e89512a14200501001203482c0c00c4508002d00300c0c9108400540200311854858200d00564042d6125000c1c04075151841d4095900341e42080c020042d40450040c061410a800c060910004100700c90043d43c04000039040340b04501c4051005100b4540142ca01003040b403a10391407100d610002903c1c02d065920002c408000309440410342190405070582e14641d40c0160410000b10010ba41c480310414001c075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 451420242 1250 451418992 451419011
    0x1805162001140402010216030c05280f050f09040213050c0f0c01050a0605010507170a120207110306072c060c0d0c0203071205060a090c0e1e0f04020d030c02011101 72
    0x20f101c0ca200b40e080701c03040702421070030310446156444000c0040c00044400c0c030a03032615101040040c1c6400000c501c01d24458041244134842c81c1c0d0000b48140118032082c003841c1080e41007ca0010000d5800d40002c1c10302d5400f144041c5030074140030610580d1003001c5100c0c21550b500f2501d003403c1076064541c4030101c042009008100079500c6160442c903014000903903502400176101c0c8241c011030300745e0141d61054a4080301d1341c06208100c0030010402e4031600c810080c3d01c0506902ca0207035aa000f071031801f010900d0301d002c5002d0401002c1c80f05846810340407106c601d00d50b201c01c180318100d071102220b081020461078064440b00c036115001d0110b030a200385034800c49045816000701c0c101c603070303456868124003903016000308040e0403038010f080014104c00c2e56402020b44c8034130a820809066548034020309020707000307903041107151902114082039911441c0e40541c1215092001a142c2d0904da030000310b001c205450000c2c03c0c40b000d1950f0a043da0b0040d4080c04100c031040e002070042503031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 451421492 1250 451420242 451420271
    0x409082209060608130308060f0a030318050102030c1b04020f0424080618060a0f030308070e01030c1b380c0a0206040b040602221805162001 62
    0x5070041c41c076094640b81d03000400601c2904c601340130300745034121000c0035105520700300c0d11030400606894121001c41e1909645484001c4120001c7d80a6655141614541900070540e042c03a54012411907006110400c40c040c3d012801200380c0ea0705803402c403c503031021070101b80a0301441d02004d440390ba0100380050f01031a900c1c0d0f1201c03245101ca0450703a07402e02a00080d5030004040d41c007075030040505040e001c4800724800740c441d04039030000c1441034035a54aa17400010340c2c0d0742360412000680001d0a0146a0750000c504c0e0f00001c1d82400d050007a00007a0030000e205804460100c0e413600c820442c010240301100c0103411550904004118554120040c00c1410f400410022240242000c00080b2040641c4080c2c40f0009000e071701400060300e0b16250342c840b806010703200341c4102d40e00b002500c0240c0468036240b0452808201903100c0f240c98195040d2240514603002c0d60010304100800540804600c1000c4405d11141000c0420180500381c0c5800c3e003502144c0b052481d860050740c104841c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 451422742 1250 451421492 451421557
    0x2706040c0e0a060b040b070609060e01020c12041206050c19021b01050f040e0c1b0a1104020c1005090c030f07090e0d09210b0708070201150f05040908 66
    0x18a10001c12180c0c0d19208a51021500580303d210a0001d082c003050043d4200c520041c840c490240c0070208503401c44c1d4450200310381c46054507c078540c0d40060041a1540f00740459003000380d80c105404c5c1018605091062034100e541d6009107541c0c5d83d2070000d84104020002d80d003c80540808558030300c084407401a65841c021000750501449440d68081950701c0b4a040355003082e05030784040e041a2920350203184840c8080e01c111300c0c3d54818000d49002d4105904007950080c076040c010490b80904d030800501040d0700501190103240108080b143e00d000020f50103599201503540026607079a85503081d07042070381c840603095060144c1e02541c040c0c00000120340301514640d00007001400c14204c9540e0742c4044480c400c20125010100405c0400e8120241c400d41c0f10300e2020700300441a880d981c0503040391040f03c55002003840e040031322001380c0d0f09104484082500b4091400c1960504d0240b540f6004503200380340c400c680b00c0440c4810400c801c01130301c0d4060355035140b0b21480941c40503080e8a00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 451423992 1250 451422742 451422749
    0x40501060801091e060209061201060306050607050c010e01090503070306050f06060403151a0d050a210207030206280503012102060307031d06010b0702130c082706040c 74
    0x150308204010070540c5041c4101c89070340e03a21080143c000d0000e040100c0c0c503510081e6090350f04a0307007070285055030345401c030040036074810814407000c06605240e80501140c645412140c01360360305000c0400012000152895280002d0038100c00a03100080120b0701c0c40b0700c580001c0e030180a194000400c004554021600940d980304101001c1d82e500401d01c002c6010751f00c0b001d01610101440d40311304c40560ba1060040004040e502c04d01d200610000c00e0030b000300081c0417110382e40a1801982845070304102c908030780b006550070482e000803142009684080a010191094034000f90801c105203076001440d078071918607000e02540340a42180034005070001d2180d00084004209450b41c4131350400140200b0507401800e1a0540c1c45810040b0001c1551503000ca55804607240c505984c10010004e29000382005c0e905541d4548040c81401601070510b00c2c500200f600780a581e04949810600d2160b100380800440103401400030f18a12124141094240c1180181020b00050003545031820382035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 451425242 1250 451423992 451424003
    0x110a05040906051903031107030203011103010e06040e0d0f0e100201091a1b16020306010806010f05030318090403021006060801030215270301060504390c03030518030307020604 78
    0x207941d403038052040d000e640302d40c100781e601300003041800041d015048800203e14182c0c01c9600c40703900ca6002c82c0c00c651156500151300c41c2c020004205100c20a0a1140c2c0544151000e100050300f0494a5070707100342100b003000520441e0b54203100894891424640c0c0894001c103c1c0c018102e006001034000c00ca48003064864041042d10401040c040603281d0380566640c0d80078410306ca9000007400e025800101002c44920b10800903500540e400300460350180013050058552035240222104c0c0540603a40044d010760000d11150582014001d80fa241111058076203503a507907254502242003580018004420514001d4081a610340c00f40010341641d200b66801c40b0040e0716285160003074024001056400051444511841c0342c0c05444005103500140000c41c0031610303240001d0555035005402446072080070317540c2c40c54112801c2c02c241da200040171800348562441c280204020f081030009000e040c0ca40c0d010900d801c01541a01c51540300c0a82601d849040c0703004001c0d04e0384403c0d10117840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 451426492 1250 451425242 451425251
    0x10308031b03041e14010203070216120f08030402120a062408060435180405070801061404030b01060c050f0f0c0d060212010f030b1e0a0f110a050409 66
    0xd1000d2904590146800c0480c500f030710031104001e450913121084007195240004c001c9814040d0007400518055002500501950b81e49001400f4200d0402e5000b20620240000c402000c42c1c0405403001c0038940203990b07190b4a039542e00108440d80d000469003005441000100418031050fa400303030f0f03014580c50f800b506044e11072000350920034050b400346082c2c54100c0c00201d00042e4440c5110003c942ca0705030641008a40c09820400707200480805800800300000e0207014080c42441541e986601183c00700801d080c0058003c000074014006d51041c04404000c000d04413076003c054900840e440440c3c1d9000750785890740204030900c5058221814491036016521480c0d000c10340158a06c0c181c001050910f4481c400c1140311a0713416015105603900304201d04080068202a0340603020b6404103490351171440c905444406402441003810140d90386869180e84181d03200250051582c03070740460000c00c440f408030000d03c2c4503000c2c6641c80c1c20008030000c1c0b9a81100280c411a09100300801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 451427742 1250 451426492 451426531
    0x10603050106090e071d03100e0c0d080a0c0f020d080a0315081908090d0b0603060a0203070203030a1a0a0f1a041404051314031305010e15091801030803 67
    0x140c0036010f078020b1000201103140003800c030071710035030288151115030000701c0700302d517002d1010a04041142061040e01500c5054180c0281c10801524545250503235480f10741e80ca5075265035940303018212204080000c54441c0e0070501401c038880b00d1006400900e03200d198112803401003410343c000c1c103d84010a00b00f8014024842c510410b0904036800c000140c11940c00f0000c44030020082170104585202c1d05001028a94541d440c10540d403d104054a1805003895400c040ca0305600420a13001e00d4010800c00c0300a983c040242d07500102c4105003c10072244014030300440801115003950443c001000004100c0000d04a0b00c0881d851101d000c0254074162445840c40d00c1a80240e0054a07a61603c0d4065030400794041a48000d107254140d004581c16a2450700c3d110b010350708a0403d910100314071800480d4012000c0c000c103c00d0802d01c0710064200c0214204d2014108028140207000c41e124900d502e403102e22244080f0341030a6a6099130712031600c02a00c0d0815200c0c18060801c401c82076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 451428992 1250 451427742 451427747
    0xd1a060a020a060f0204091e05090307050a1b0306140a06051203071e050a14150603151b1b07090504031d030114070c02182e0f0608010603050106 64
    0x2030310085a598003500900c1410f0300c0303280103000702031a00e4000d180d00700300000b25006607108802c103406011181040d0b0350401c021900c00c0c0c9002501c00d8000d07810822481000440008980700c02c258458111200145440345210005007103170700c0070b0a01420f007546060706448010000b0310030000701d03104001c0a9224020310080d180c03a00780c6c1e0105507100b00b00b5940841d155540658081360007502d480f40e001c00740c3d9280c6041510740030048903c3c400403518400360000030b002e651f0030008281400e0b26030f403800c0780000e82d0714282800e80098000c030b81c0b404210300100083d45a50014100d0354420703901c4d49868410442107071120039a002c180180103020035165110701900e4010b54055448511042c804804503411002194a83e58150341e246c4030b010308a030485040c58803501841c0c903450700e00c5202d0300500c400d441160540d0800200c02c2010800c4010400c8000c1140088a56940c00c1600b4900c86050201025402c100740c000c0c1888800101c15622496a80c1a101107540501059030b880b04103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 451430242 1250 451428992 451428997
    0x62406080114040905011805070e060d030503040b04020301090210090509180d0f0c020d030509030105090708032703030c0102190309080f0c010b04050f0a0e1203060d080706020d1a06 80
    0x310b9407044428441444070b407405400030500359003e03400001d1030690390309450ba000b0319007400c00c4499800810003003040b404040b03111640150148d4440009159a5a00601c07130302c03000b80000c041d002c400010500399102584403a4500354040c1150000d6001400050f02943c81441014030403412320002a15039800035096901d01c00072000100282d80303c4141c2681c400703484018210421160390211009a40d40c45040e21a8078083c1e01c0f074070b80c0d4107402c40a240c00c2d100010044030b01640000000c1181c00000811680740d520154100b03903400e094641040d500704580c88546034107220210740442c2c004810343c000c1a10401d0510120009000e80e5025805e8030300c1032902402ca0342050001c0d800c55880880104087e20400000007110451840080d003190001e8525220126000c03003041108800c42c440c48014840040082046440800030407819110042c9194080d00001c0402000c110341c10094412240d80110295200d21031507609000402c0700b42c50b942c0c91000581510ba010303040807004c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 451431492 1250 451430242 451430249
    0x703051c020f070b0702041a030c01031a060715060e070503191b02070503010609061802090604031712150634030c050705180415090624060801 63
    0x1510840000350000042002085801415801802d1180c50041c40038490300b0041d00004520b1a26540c441c0140310468a10044990f06004052050320040d43c1c005002403055900340303400304400302c400c030000142045050719160000b401240c2c0300b041029950b004003199003a244100300c800c1d0380310b141c2c004001056403050301241d0304001042440400e000d040010750103810003c1401030515101150b201840c0303100ba001600a018144003510302800b5900090124010501034181440b600d80e5545c80b030800b20504080d070024900c0303c1071711140c0564006507040380c0071071044100c026000c82c00381d0010000c07802c101070ba640081c002c1042d46c50030503140e4502a00207030900c450300c484160001e008031610292901c020700801044984000000031451080e555080e4030861458810301e0510603804c054402c068030306031001c40c0c80034000c900d0b50168100c0e4500a0070101044500d00800710543c01501c25400c1c03401400300c03844021420000c1559840e01105102d0b5240c108883c0d03131500b0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 451432742 1250 451431492 451431503
    0x1015050904030309060b0a0e180f1b040b03070e100e240a03050303090307110a08151902030112050616050d0b15040603140106051804020a0507050601260703 69
    0x10007040100e4440d600c03244046204200002d9811151400a1000743c510b41c400e06200760114204500d405a080181803e501450010000007200014454a03170141640c2c111601682c01c40d40302030f580d240d804c42070141001406507076a4586410f500c0c1c0c1c401400715031600d5402d2450b070700000d07000d0180c0402c03885102040301c00c4072405039010550b0002d2520781800c81e44103c2002d03020022034410300043d80074105143c010b541e86d00f003915010308a00d0a0102c090f04c1103002c070b5420015860003283c003551110104065440a84d200442040b00c0c0d0118860820000d101000225101c081c8001060100c0d000d041100c502e9078982c80c0f407a2420780000041d1000074010701c8942c13944e20054101200b001d03c010310920103914114100d895982040e0b00502c0000d48402d140441d03c00716210081c050203783c03800d01d05d0409100c1181090b811a001824000e030760006a5018a0b84241c080e900d00c10792000c152a0603585d207030740710b1511b1040c80300c0900d54030f000c140c100c07a034507000050318104603613105 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 451433992 1250 451432742 451432759
    0x12121701050112091401051909050a0209041b0305150a0b0a03120e030f370813050607030e01020d11070302241303170f19021e101505 59
    0x115a1070b41d03c4402c0c20f6000d512078801c900040c42444000c07840c8001c510002840740340c205144401e124108030280341051411010340b0202c0e00c04213141017a0390b0165900075035911175181541720064820100310b800c0081d00000b10400501180f0014021003005100c0342546aa9030141c1c01c640d000c241e0598403c004000810010f400f08002c0b1041c103e840c00c100f642c01c40140c02190916801918202e0a0382210b0301c4540d240d40034114032240310700040a80d1a03414440c50107008103903110741380079010000c0400c0843c003007900e1a11b00300242c00b020304525200e54035480c4c003900c1c0080c00c1141074058001e60000340d1100d4428a24107601c007417568010f040841c0343d6000d002c40c3c0301100c0308109100d009010b07a92036224840c1c005290856040074560407039881c40c00c1c845007074140c0c802d0034240c3c2c4100f003111501d000d0b2501d042d902007600c141c4d0180641c0315010010303454021046030b850b00101d039103040020221000701d91034070941c11040f420321140d001a03640c3c4802c0d1426000750369011600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 451435242 1250 451433992 451433999
    0x309040903050d1a04110703020a0609061b0206040317090a0213020f040e010317070b010e1003060e1605062508041d09100e0c12030f0412121701 64
    0x15400014495001c1c0c1403480c90549202c40b031400b9124000350318031078090710340d05400071410644508401152052080c07801c140155600075140c900c0b00c440030380b40c0c54441058509006036a40151034102d60681010508080f03d1806911b52808603800c3e00896901038001c3e150981e01001140316502c01405044070450b030b603081090044100340405441503084c0008041003101300c0c000c002400c14001c01c0c604540c550b251240103280104102c04c000d4130144080400105500f00c0c4605541c0e044110981343d90700d1031080e8101192660002e0801814050254180038001c1212208560040d01e890a1161101c06120551003604d244480c100141280b08581200c42e042d40107215120741e624070f161650380c00c00300c0d000e11a0300c4804c443d007012800600090b110708000c40c040440340c2d80b034280030351900b100005868460030300d02240164501c0d2001111032005100f150b440b541c1c100089500d4544681840352a211605001c60300380c0560381c0c50003507683c0291a071065065148819440903800d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 451436492 1250 451435242 451435249
    0x513120c15020c030d020c0a050706050405010c080d0b130203010510050403051e07090606170601030b1806030a051005071808100b0109090504150605190b0708190906021b01020309 79
    0xa1880f0424002806940c0100905000804130500031200402000e00c060804a040c0816a400b280c14410100420040f50341c215020a1641c1d40085000d9192402c2c15041e402414000700486d6018921079070710802960a5406181039070415190608002000041900d96223742d00000d000350b0b01c01c1c401541407580400d0303031960700341135142075414060303940c003115007669260f0300200081818048e04000082950a50941c452024030301804074240398004214031286100207520143c1901000a0391a18200701c001c0c819540300301164910a0b00c01205070007040252201c070002454000e42d02c05c164503054071401074518030302c050146100c2854251000384144802c3d5418001007603000070300c00c80107202d107030321407400307181c2d500c901c0c5e0705c0ca01c44c05084407071076002180b02c0e0581e0004040342040b00211141500c0300304225550b0752981d4100843d180c01844071032040807903817001301c51909503c41d0910041300c0c1290200d5030003505411170005014100d000d4030380181d0042c44000a40d14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 451437742 1250 451436492 451436497
    0x140a08160609080406030507030b011d01030506012a0c090525020a0c09021207050f0a0e0f03060118050a06230a090c0e010e06030105060921010513120c1502 69
    0x6210340710024a0302c04955031404580c02a5000d007002c02d940c0c41c10000c1d020341501801e04800424a00380b040001c140a0720402d50780d02180744d504045d0758200040c4030340d024000c4115452643c07005000d6140640350b2006081d881d4031411501441d041d000092484000c0c040d980c041d00e08445550407507000d401106551a1249958004521400c06450003150212200502616a40c3e1004da030b5507401d080c000781c0020010b03100c403080207005c0101007103503e4100c042d00c50324180c40c6010711210414800092002107403940c0c482d4580110000010f02e22b00700e482c18108281582028411a41c49065180488a00f0300c91500011480070210481d05000d01c0c5000d010030004059516003522038011004544508a001c4041106401c0d240845d40e003040c01d084e000344048998524560504000c00c08a004020740385000d90b07140344400070f090083c81000d009480004008111a2801d00c00380d0b8115000305205490001a45c42c4c4178003003c1c420940004025000703c0004890300301f18600354000e6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 451438848 1106 451437742 451437787
    0x91b0806070e01021e030c011d0607110d030e100501080c3a030c08070f0b0c03070c021c020a140316061d01050702180103140a08 57
    0x140c1e4001640540294605c66001c42010300b0903606165029469298055500b401c580c1189990b084000507101c940500c111441d6032a02e0f0000c0e075018641c59813128081e000039461130415070080c1c000c4104000c5500807039900e848804000c80c110eda080c2c025101a40001d4000316040c5812081b80d4800302c0c51540c19a074841000800c41c80b0f0700c00d81448401081462044401030600403080c907204103030009580b660318107540c5030038886840c81c80700480d1182c0c50000480c118009803410b80e0320413652611035803000780b1030340c0030031902d00041c0d420040a101403022600042e1108002400148681c0000c6000f0101c82c004050902895882e240341088440008014a0340d20114182120b510f03541e4920900440304012105481120030103900084800510b02400c009607500504a078040c007042c00500b05060309664075032100c400080c01030384c4140540510394465541c0321514 = true := by decide +kernel

theorem cover : BRFrame.Cov 451258992 451438848 := by
  have h0 := BRFrame.cov_init 451258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 451258992 ≤ n) (h2 : n < 451438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
