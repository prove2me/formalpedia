-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:55:16.881844+00:00
-- url     : https://prove2.me/submissions/f43c161b-b0bb-45d9-af1d-fb2942795d16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 20683459 ≤ n < 20863315 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 20684709 1250 20683459 20683471
    0x6010305160c0c030803010e0f0a0204050a050f030c060304050d11060c040e04030207050402040602030d0605030d1715040501060309060c08060109050d0501090501050702070317040e0402040f02070b010e0709120506 94
    0xb19148004100038030398001c64021034001502603241d50b11034003d0603588070241c1d46024010309100c045801d40d2403a02c00c03039044603802481130101c64a801c042c0b040c0c00c86020112940350044821110881c0c6407000118803480c030410161400b520f00780710150959070110050030072584071000304000101c1000c11201669007024000100d40d41368501285014403039000260480c0c000f25000908613000005000c41c0c00401c41c0a21085480b00c09140c0d0b142400d494080000e00004581440603c06d14043c1d5040180d41581c0c00520800f80c0106040d40c200b0f83c00440041d03500c0442c01e00340081845507c40d070500d42e10f000441c50629100080c440c0c102c034007075203104a0f100807006c81082400d6000b5040d59500c0030082c001da141080020b502d40c8000c1c842642d54800d0050b04540c1501c00e01d048805507400001e00100c2c9841d01d400740300081071a0203150f844a40e08011030008210201c070a54000c0c0864441810149040040140390420702e510000c4994605001c1000088000c078516500c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 20685959 1250 20684709 20684717
    0x809010b0d061a1206011706270a08070c030b010e0609010501030e03070f0c0e07020601030302030f0f22060e0609030309040f0603020a080c030610060503060f010915050405090601030516 82
    0x202e080c403c0c141c0c040c0030207283c0c0d800b00c1400c50780f61a00383c0c040740580c12291403216854011001e00e0460b40c4500048078072100d21143c00c6803907500c076180d02440004010400c421140740c22055518180507906c1548151041e9800c808100100b100c214205030140100c81280b40d09801c0140c0860030200042c026641416201e052460b0412400c0050381c0040d504803000c80c20b03802c25030404084000090050290410302000020328180c0001401e81c1201e0b4540d0003586060100d460321411908000c0317035040c074100100581e1345142000208400040002000301c584a0319012014002050064541d030040400303003c1c0e005295000301c2a655800c00542e00071031a19181f88140300201200c0c1c00096002c940d0010204001c0b40004036800000b01c243c0807176019455070101040d4000c441d11030000050750810014270301e41818074070043e2444040c140084087e413039030104021480d420380700c00700181d80810100140c1c54680080c0d07030840310038201003016041101d8040b140d03440c0040766100780 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 20687209 1250 20685959 20685971
    0x60501020a120203130905011503020f04061d0406060201020d050603010c021902040f090302070801050a1401030305070c030507082109090112050307050a060506090703140615120106030209010809010b0d06 90
    0x43d009208070b03202901c400c56860006a100c40c03107180101028055001804180809064098002d200b00c4031908450201da0f0704092a04004a07034040c3c00307032480c18038810140c401001c40d451381c1c01904c010348400d0700091f07142c0900c403040b4800c0b00c10003481d4600c03980c106071606030115000300300c1000b480d44102103100144e106002050240c00696041d0344061300d480c903590305040d8049041d0040d50b40e81c200030322554680c4249282a5100c1c1200b405000000600400001e4020001014a140302c0c882040029907213450351400c00c141540f010b00700f80c2000403060300d004e50031a55000c14030b000c01400c6080c4040d81c070114070310282c140910710704c3e6214030748004280801041618481580401194204811031510101800d01981c485014414150200e017180780030b80140c0484546c90002003c0c2d070b03900c1100700124441103040c4400c88000030400300145500d6079100501803c41500e000d6507624030880010300101d8010304025135a4500400c0c1710840d0340e111a040c81c1030750081070103c1c42e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 20688459 1250 20687209 20687243
    0x902190302061b0f2e060e07050702041506260405030a030e0f010203040804090615020d05091215040201020d050c03040510050c010203040c05030d0203040b0306090907080304030c09050a060501020a 87
    0x5480320480c401c1361203101304000300da0148024956514209000c9402040014000c0400c2d4141d400a0051140f40304507080041d6000e8851805040e940d070008001052482259089859028144d0412800540f0b000042a170821491200c041300a0000081c0150361500340c03100d503100c0c0140d03940c4204044d10b0f01400c1c8000784082081350840b445410085540303040c40d142460b40d0350720030300c07482380726074141040003910b102c00d40400404281c0741d801609048c3c0380c4100c00c960a500000495a000b03502111451000600304032011542d03100600941c8035003090b00001e45031007810038540301003041c2000541112032010042d1000c44000359414201c00d252841e0544007801221011013880d031010080100b4890903140e43e104036801581910800c0e000400100d89911481c002c802e0f030b0003401c00200b109420203243e003e40c0141d00c5002d41d40c1003a00c400d01c040c2958081c1d8016544498290403d102e5600c0501c507807500800351041c100308045c03400d00042d440e1924000041d02c0080c540d4182e0754 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 20689709 1250 20688459 20688463
    0xa05071b0302130204080601121e0201030e0102040602070e090303040309030f2103020a031a0a0e040204020d06120605060307060804030302131505210c030408030a0204050d03030902190302061b 85
    0x4080c0d0342c01464405901e120908090094005105409151107541e00000e1031000b104c079007641c0103400001c079600260030b046050780c41c0403110008038109a41d4600880d0080307405e10241010348140d601a104282c900302c10b882c0140701c09010780c196600200300344000280c000d5001b008580c1d11440804e5601e802d030902c0050003021400c000309204003a0440481d040e41a80200505240c0307450820584d04110703c001c407500c07011000142c026050070000e02152102044007540203100600152a01800c401d800065400580c41140030103c6003480c45d0400010340101680302800b0703001411001e14040c0000e10014001d440a0181075001508000d454170004908000e030501706107034800f140714140000e0403540070310420100900086007120b130780444645018000d2004848550850300c40340c03035004103035001800d20282150b00f00000551a204c1025001e6014060340700002c00042c00c0c018404250001d14200e94006e50300300c0b007840143e84040540d007901c0803105605001c50a504040c45c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 20690959 1250 20689709 20689763
    0x41d04050313060c031803080f0d020f12040201140313061a040c02030a0f02010612120504030f0c09050a02070210080601021603080a0e03030f0403031b020904050c0a0503030a0507 79
    0x884100701503107000c940b1680005108107a03602c40c0d61030305080c2c2d6410704a08a00c9001f8007000b815140c00f008001040c848050151005280e810b400502e84540d100000090f50b0102c042946464000c2080000307542c2c2080301295805501031005146107415130090329008202d82c0020240c655640d8045828048078101407142c182c081e004002c1841000400313552030b0458488280040e000300d1441c04051b03c1030040c201214500c0c2112078114000f0382da80307122060050b40d0041000380510002000c05e0b90005128682401030340e241c4081e9050018078401d03514014108031005004200000c01a12168400c81071452070317290880142e151000100c0c10800005104102001740010100600210000900000c0b072151140c40c034040494050503120301490500e42100b000900040010078010025800c50084550f421500d00030b00e80d0000780310b0ba030292026100c1368090b0700424800c0c142604400c0183c10300b10700440c100035100340020701c2840742e5040201078010a007040403410301d5443c608 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 20692209 1250 20690959 20690977
    0xa08040606030b0406050405060711060c090d0c0605040f05100e0409050c041d10050c0301030311030f041e06090506091210140a050601080105150a18060309020f0402041d040503 78
    0x103d0b0319820319060250250800340c030300f0fa80c14010000803883c000c3c081e00c2c11341c40507103039132019000359610415407410a400141c4101e410441d00020040010040d85034070010305019103803141c5079410140500d41e0300c40c450704101c0c080e200d4003a5182e00240c00640c0c50040b20030031580480d01c04014504281440d4081c00002d404c9424020760640702e40c07000c07904a10400b082c2044071202c203038481100303040d01d60540348182c04440c200010f00200e0f1040f0040e20b9280c100004692905810101135401a8000d510101d40180c1c1840b81c942e594110000000040401d458041ea2103400e002c000349e128400c141400307224540641980d000c0e103c0030302c00710700041120301080080403452014540208000c4410000441ca0600000c2056015048181c103840c400b03040881c003005465602c0c03190b540130850b12011303c041140c040031280348101d0b4100140c00d241d980800c2458162050082000881180501c11801030100780304543c0761100182e00c9040030280e452050300c0d00e040c0726007544030303401407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 20693459 1250 20692209 20692223
    0x201141512030412110405070804020d0303020705120306031006051f02010b0303041212210c0309020a06050c0705030109120807090b0721020109030903031d031605030c060406050a0804060603 84
    0x400139908500c3c94500d00468010b00d031058221300c0c00d20800049550490b10070000c614201c0115000d81048043c52700c2c45403003810b00601c0c1118907120946403840d95a010450b40000004105040c28280580c4500380aa5101408074030708202c0010b030a5000008444c080d08000789001ea0328034400d4116035640c00b0050305595070340303858404100040112060a540302c010310480900103a2140c0c042402403103540089440c036030a00b10320003001d4202c0042020400d40c98891040142e50b4204000c00148129161207a441002d100350f40d04100c142e034419486a4506140c1c0004504d00c40582a0102440d00c1c004280c2d03070b0349400c182d0b003541c05078100d9072072840040f4204040180c41c2c00400c0404c807107207102c01d040c140b030302c5401c909803a5a480300600040c0d4080301040001e00440b19a0003008141d20205005020017001c2031424030741e6031034011040c044800412160400b4013004100800c02d039112031500342801405419031080c9501c1c41300b0442914000f03410311403184e12880c003030365110803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 20694709 1250 20693459 20693467
    0xa09050906040203010c050c060609130204020307020c0109060e06090d0302031b0a0c050d02060d0f020408010f050f0709031a06060409020a020102070c230105071505040c0f06020114151203 83
    0x800c0554a03036044408902a6103080c102108441c0540161003e00c010b1500500300e60350755009108103980094084100c01420000c0c0b5001a619800514400c091a500510030041d40400060075005c46c0d52112040c80b484940700c03c081d4985504a03084000152206801100e407481d00301d1851203141d42001201c0501101100155000b196a00130705024500b00340d141030b1117034100669407040000080d0302c070604209410030640c0c0d90b040509140252500141070907a06c1350b0003800d40e04c0f90748241c04000c0c0e6030380400c0001d452045415411040038940050010305643c3c914a603949030540d00c01251210f100001d490b5560502102d01a2513400350540d2074842210000c1d000c0d41080034200c8003030740d4a00020601030302d000f411054101c01c0c224403401501c4084019076040c0c3c030012051310500c0000750f801c5550b00280c000d85000d00e21131242071504918145403108404040d4120a0859040101e80ba5640e1118801d207038020315807030440620030350300100081001071075001f80d64032400041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 20695959 1250 20694709 20694721
    0x9140a05030417010501060f0e030705130209091005060702060d1503080a110c031b01030f06030c050a060305090604020418050703030302030108100e0613021203120a110c12090a0905 80
    0x400500b00f19011082c202100e101154801c03801d03101c0900500700001e0b06100500c002511a07620b405503940301070f00b52420b25403140049200340d044084100d41c0b9a0f000144c403201410080210395001400c0302c140c2103010f007041c0000f00702c0e201d17142c03001e07100740404640300c00070481c40c0d403112000008044032941104d6603072400150a400901100c0041200035581c8402c03084d022902c0ca101004c010080d0804281032124240d603c0c0c0d012402604040e0758480902d28007105114940c00765025641c2c400e2940d190501300b084040f0160448010182084e05004800400092031900315504440104040309a9280b0800c58084800040d0940c85114000014190503030300031410f0320b511105860792605101455005d5a1100c421803101da400280003c620000c03a520400c651880100714448c10411001c1d09807550704070010200c000c2c0e0b04c001c20f04c0341210f100e10410440a01c03034001c403402c10030b4514129407611800160f610b075a51001858108139600c1000000c080d2481490400a6003021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 20697209 1250 20695959 20695963
    0x9030c061302100809060403030507030b03060a0902030601050102150f06010507081902060c040f3803100e090a02040519060602010902030c040212010b070c150f0e150405010309140a05 81
    0x9802030740124440f41d02810407602c20035a1a00c62491040107090b01d880f181d038110000d20000708802c04050355030800520542d410b0003594007401c00c600001c00c480c032240c0101410a20183c1c401810740d44040103251020300640030041c1d00000a003410205a81c940c001aa041d101e001001070001038009800d0504a602d40b180f0788d2006ca059003141c1c460754403813081b54032511503401046400840766608115001c87e54030740c006071054001c080c1c1c495888070f044a000310701981c074244011600100410882546e000f8610000300100300e4020b08030304003095856210b58030310201900550311200018100300b56070711440496050071208200d40d59691030000d000b81200001244079001d4801104503901c0e06001395001d0a25030030181511ba407804603c1060b42d400b0040c1161340c02c0300041c0001d00d101641c032070481060310036118490136601346907000340001d0f140c00140c0d1203800c1d6140881c2100001005603416a4400c0c00c00140c1e070141c50a000c80c009407102c01c03800b42449803040401c100600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 20698459 1250 20697209 20697241
    0x5060307050c1c05090d02040603050f060103060b010315060f0201090209090a020a080309011b0311030f0a0e01090b0a0c020415060302040e0a0b180c0c06090610050406030206070b09030c06 83
    0x2c80c100352048126409001c030b03a200001c4404000290040c0540c441e180382450341e9804151004100182d010344e030703a940900b03100031489000101e8000e20010018001d050041140c0b085091030108110341211125407030070803081c000e4504106040c148034404500035808011f11940041c00c0d41d50518115071240e41e508101c1e1002c9004440000000440c0e09002040e1080c1c0034050311500405840c0700231207410fa80020343c1c1541001010108654098400d2000304090752002c014240d840540c40c102421001c0300c104614100316070380d0810032a036602081950008075807807078403400d10540e600008010b41200c00b49241141c12005000800780e0701070b17005100312001c1c4040300c805035843c84682030454904018003500720200340850a48452240b8015070b00a00c200e603854106016044060320b001c2084420480075440b500501600c018066009402020211070a00c082e07400c50340401d10a00540000500c4108080003142c2c05400074410358510a04190441e001031500449512102203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 20699709 1250 20698459 20698477
    0x1140c0c030109141501030c0306020a020304030615060806010215040803130804140a170604081b0105040b010509060301090c0e1003020319020406051008070c020103020405100503010923041b0506030705 89
    0x1003841700e81680f400d0034511403412a504925648601c0e1b18580f5800041d50080340f0f5407007107000030403000c000548684500c4d8000b035403840c400c000303850070700300c1c050b00050740600100d065600800d1800c030100d0124100550081e4000301c2c082e2a0348a505c0d10142d4031468420062010340c1c040742c0805c074540d41d041d098103842001c8400513440f640c0c0e240005039403c40311100ca045504804001400318030070a00030103807166031241c80d400101d40412403d00b1100241d82c121120854203004104929090b50019008501180208440c080d0355850803111403191160300001210007000810289080c04404000c0d42c0280079290900580c00d403140344c6c1455904202c2c455850b0200115090030b0201c0240e50594103038450364490748851006882581c4102400c0b03040640070440030409031222200c2003d80400da889090b00c950401f0400825203204401000002c0c008c88042e4400daa05241d440350400d40200440386e607042c04008000f454089038210726000040001840301c040c3d8403d004140c1d4031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 20700959 1250 20699709 20699713
    0xa05030d0c020f03030d14060a151b080d0207050c0102120a110a0f14010e0a11060313060c03060501030b030303101205030c0102031311030a020102070504020d0906111b01060501140c0c03010914 85
    0x81c1d0748c0380801500341c0b0369028a4403041307000c2c041824124015011444503480f003074115190349007580d4a00e0800d07032190041e281031940118107001042000c000c0401036500900207040c5010038001b031101903000d4505444200322509103280e098100c24410780141c20b4214180c4800a0014200044240544410004150b1800c00006403640020440c00045a401302d40b4110700b00d01d5200300016900050030040040302e803040100d00055082c0f260707030342103116a00c020600da440e140024040b50b2602e41c03400d009420030000c01214600c80d4102005030340e184140c2561030700443c107240f40b442c00350705841d000c3d66100105008003e1807016035122098808d103400707580641908141038580c00280d00c02400369011390800d009502d4150040c1101c08a515400200d0000da6102c92054030403251080000d00030000f0040180d19040300302c1e044505401c1c0081c0105881c1200082c507080400026000c4201d0208082d45030010500c00c803401520000c00034081e81105062034400e01d42401c801183d18 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 20702209 1250 20700959 20700961
    0xc0903070f050907080a0e010603030201050a06050402070b0f0408190309020f010201090308010b030a0e0303010b090f09040f060906020c01050916080705010203030105040c1103040b040906050a05030d0c020f03030d14 95
    0x92050800307400c040e180042c00005058480303c80545503c840645130f503031013580fa14903003d09180c09100d80402180241c1c00480c103400c00ea0030401c01c80c1c3d19504418050350040145001081040b4901364100e035095444100b180e0313481c100742503d03001d61214aa1a680c0c08044c00425a60540044541c0d40c022548854248080d000583c02c0751a101402800305403583d0041010040c01c0303000c2c0d0790000040e480070030303840c00840145045500980104600840208413a00b170703400c20348031140d0303d0340d0281d90603d201d00b80390b2184400c1c084414001032032280c4074400d0310100650398050701e01d01c0c11400024015070402d4110303292281807008454420b03041a0b240011103800000d000000ca41040e0041c602d187d0130501031001802078003040c0c5050200c5006244104002003009000916440c0c080a03200c5051455900a58245501092144658000078801030340d01080320b031080d03065800e2100c801e907501e10100703260300d540e0703e0496030502012402c03401d0702c81560005021140042e00600722 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 20703459 1250 20702209 20702219
    0x30f05060114090f040201020c03010606050301090f020c060a1806050403030b181303081e0f07020f0c0603010603020c010e01020c0c01020601090c020304120c0b0703030605031005011a090d05060c090307 89
    0x1440d402e401986a10682840220346110901100c103070b081401032066a0146040c0d0b0042401c1d07444d580c0c420f00000d00b00000401102c9080c0c0300388002000807c0066140c13038610b4407000d82c2c13070304050010080790380d8940a543c041c503056881d001c0550342c410400c6c0403500d01410043c004000309a84a4080d10a43d0262600171a00e005480c1c400c10700b03800c4036030700030100b80c070221003202000303010029019038540c261a12a03011650b0340e20400003203c1d045c446e8601140003c3c24400404180303002580404500c03802a9070b0712050f24155120b0f80340058a032114400e031203024010764010100b8031f510018051100c00008161349a0074902a02203c403940d98407071501c42254813201c07103240107070406e10084c054640041003001580e40103011191440b52921350144a41d4490441200801c0d6903400410242c201405642e64400300c08004001c158904440c2e02107080c500300d0606036121002550320309079664418481c00064010003110382c107103051640c070b240650281122510a11550800042d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 20704709 1250 20703459 20703479
    0x510050711010306030818060c010905061006020303010f05060f070c230f0d110102030c060f18030313030f1403010b030105032107061d0a05010c1b1109060d0b01030f050601 76
    0x4c00c0326403140c242e503d8407044403100c1148546403282d640e4090710801160603003402c2400b688400314080c038080c208a00b065841d08809071074580c01141590001c0c8010020319400d8501e601c102d038805d8640366520ba246420050300c6104213400105824080c40000c0740c441071200c0102440010304800c4155400f5000c100541420102c444c1036110f240602181300003680701d40b044d0004a010700440c3e003040010389150342403a034111a4903000710780280070000300c004400c0000410076145809140383d8104555603d03c0c0c45180346010301408025101122610b00c1a8402800d4026202d8402d4603940c442d08408819402845458840d2141e81001e82c6e6103000f85510100c1c60400e281c2192514801c0c0d80d400001d0b180d508410a1a24080d00b03900100300c600740401d038400392040f000001c1c1c0000300c0c0c1c009001c5c550710804c0400c0d14000741d551038000441402900300251811100d2540c00d40c4c41e900018190360b50890001c01e04800c0c40c00000411050b240b044800038403500c1541e216a03280c21000b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 20705959 1250 20704709 20704721
    0x50f0613110906090a0503070b09090705071a090f0106090e120405010c0b0a090f06020a030c11070e04061d030a02010c050306060d05090c04020f0a0305060306040201020a14030405100507110103 85
    0x111030110204070303481843ca0b002004202030000505640c88403941c5800281c1014615844244404400074008603985002450f496020781641003460038030900d915000740c845070001c070340c140d82491000403c0125000704495109001e08100034400302d40c807280300c9400791002442c010454461000d41c0b90101b0012001d4405595040e5a42e12041c00a900d4003d80a0f43c040c110720f201030398441080e8045221002d030300311403500400d4050b179a66641a4001c085404210a4404220075601c2c820110030012681c00304032040b440c100c40d07030341c1c4403410b04200400910803541003200e0198521481c030000440981140200744d0000c000c00c25180d40290307580c0c84100e4005900c03000800c2040030b00c150319804541c000c1829030480700e007004224041803c03a8481600140c4c43c48020480ba04480c1d4940900c560000e410b40c042c1699007002d0b0700207991505000e800801c10300c1791030a00e0102003010000c0d6001010014007540c10702d81560006040c50340200c0e401c0d100c240ea800d0008030554041d021786 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 20707209 1250 20705959 20705981
    0x12030115050a0309080406080601080906010e0a0c091d0117010606050a1d0d030801090c0c0203060402011b170301090c030e07090f02070c090203010f15080a0519050f0613 75
    0x2800800001040845031035000c2103051090580c4d5000d100082105403020744050081602c2e03140850600c02c0000d802004010710300c2c407969101000600c000d4000310038142d080140b1241c0400c00301118041038413a4203030b90b0401026041a086070500c40b410741c1c030042d8101c030182c0c82a801001d0380e643c0d145090312a107009100114408019030103466108050302c1c141401c21040c02c0348407040030000200c407032507003404c2900021604001844030315414031074584442c1850134800e18450f81580841e846510041020341445241841e0040070381c0d1a90703241400550200200600c0d000c00020011540c1081c022803e010b8a4941001c4002d4001d10880d0508910301c40103082c40381c40d00c0c4034000a0001040f003c0c0034103400f8002c803000100403003200d601500388010b01588943c140074682e506a00281e20070b02c1c5003060310807252601d9410101464001d40d40300c80c085100d50729034902d4640616581c4e407080c946460032040040540c645006240620000c0f1000c3c401805201076290a40341446070b6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 20708459 1250 20707209 20707229
    0x40303020a031809021b0d05090a0e06030109021302120127050a020408030406020f0f030301050114030a0b120c01020606090c0406030b120d050c070504020301030f08070201030b04020c0c0102120301 87
    0x4001c0119005442000708000e4101d09503900ca900c4110150503604645000a1815181310f0388400e046024025039131100359524100d0304046440e000540c5a102c0e520a5852003e9101d000c030740c164a0030740019010640207002c5007004044540c50314003c0d40300d4521140b10b44d081100208410342400c10080c015680c180d00e48070109040301d482c0e0b00421010307005c440b01d944d080000040048050002c0d00007441660041c0403920710701640e00381050741100600d00b042d0020001488180e801000744001070f80f0b000c000d41c0c1c0320360702c1501810090403c0b6410541c03210082c5034801c00303408001280f102000e02030b402d0303885075243d035020300002c1d40e401c1d00e07003208210080c030081c84554825480b008811600030911300d0213000c03000a03203090018001403007000800004044085070300400c40c01e401060291400c600d15803540e1074582d03100c07044030380007030500100180c280150380c840c0d00511440880103008650b1080801813a41c0c0d519603104040307026001d44514502a82a00c00549040703803c0092 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 20709709 1250 20708459 20708473
    0x15030109050a0906060b070506010b040806070c0302010e010f05160c020f1201060b030423030310050d062301060215090606010809070e0705030a06120f200409050703140304030302 79
    0x140c5030024090082a02a51580d500c903030350082216401820000c111a2a8059a070821030070a02c0c1400310580011081d08400c0000b000b40001c000342040d40b00c0d00918103100320104a1400b24050f03c0800203070741741c560804030034400800c9a58040c50182e002076a4410000c034940d1030507107030b821091001039800390810707103045210300384101c0d03c0750751321030902c0002030254aa040d8585103401c180c03401d40e801d03544900c1803111a500380c00742c803842110b848000c1d403d501d040048191040042c0c003640d402600302291a60400803190401041c600d201c191001c0d4174002d1404092214009110310b10042c03082e82410450045607080160040c4003040c058051555400300540304a60b000e40070311514820311200044070303920102d006001d49801e540d100c0d034908040c4074080560b40c00b60450b0980d07800912075400050103036580f003001c00d83d11420b19020010141482280b10244d601d04681250030101701c2d20030070101003000b0013580c0c8500e04850028200e04401c03683c0b030095000040250740004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 20710959 1250 20709709 20709719
    0xd02010f03020f040f0803070209130c0b0706020f0703020109151505040c09081009060c0f120b010e03070b03090d030902090c03091c0c0308010501140a140d0203040308010e0105150301 81
    0xa0020543c0c64580c0d43e02a281558030110907104c0c0503d9400300100f0b030000300c0c0c42d0382149804454150002a07041201500018a80b82d0328540112441000012000010000104040303030301590800d90700b128500b504c0300c1c0c01d4207000c0d020b45075803c03040307940500150840c1d00c000d40310300c0b99034003259010741104c99031130515003440028143c41c040c800900614060020f010581001071881c0c010070003038041181c140c9898500d00741c91600c181e500c14005040c4543c40c0e05680109020710000143d03401245440308100140c0700d1012241d21203030180070f444000700348000d28000030b60003550b0080885203805c0c1010740481c1250320900c0000e5000c1a0200495140d81148002d0340d00001c001059410280409240b032582402024861000c9440c1200e080207140d04503415600400302800c00306004070307006d04203917500e200700e11b2014140803040759100040e00740103094a95801e1800421996810316090140445c80d0911620b12a081c0806c0041214288050030003021501050301c2e03400e5900302 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 20712209 1250 20710959 20710961
    0x305090d030b060c06040f0b010605040308091003110310080c040b030d08041e0c0608060405060603010504090503070501050c0c0717030301090209010c020d030807030c020303090c01050c07030c06050901030b0d02010f03 96
    0x71640143d8016001d00c0390302c0310b100041c01024016031042a05400c02c103841e03d0320140c0140141d00120030300c82c0a000030404510700d0404c64254031802c950414455205030400d50013055011401d100e462400700c10031020f1259110304905840742c1008441142000b0400c000c02c0d00c00340c074113282d01501b0060b0700c0062140a0f403401a0006d10030f014034141041904c1c0b402210030707d0a0380a50300028540e808005c0590007149a5420442c281c8050005140140100b41144010b2080c5c03800390b540c0e12a100180881403041d03405940c0e10000a20040c1455404550389402103002070a450041c0c81e000141c8250301c98000034072000040103141142c3c60641550002e41201103514103000e120311958006035191401c01588610a8554800d10b0600003c01421103240341c0c102c000703652082060108503030f00010755154441c0246091903680404142007802c3c59050ba1008003030b040c0b0702c1c00100e492900403000e80059282a0303400c0200304034050401c10101e055107400781c0855140b850340c011183c03003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 20713459 1250 20712209 20712221
    0x302010c1206141005120901020702180609010e090c0603040507080601050109030c030b060a08030c1c0e03060c0306031c03051501050414090c09060c01020d0b03010603020a06030e190506040b070305090d03 90
    0xc0f50078006d04000366051444010102241c044005950000e41801107142a04a088000300e001d10b02d1103d502c0c00c4000300301c070f41606009a03802036844400281640e1420040c031001144050301443d2241428501150349000358051115140500000800d0343c1d40b05d400d032502100d0300720203d02d0303200d032075500c0300107a42703401a00341a005921082e000ca06030804000824090030301200800c000381394405220f0b80f50b0940e04001c801c210b0440a2070416a40000c0d0103a08113880c0013900d42e89071101400680b034490800d00c01e08411400150490100b90140c0c001881142080480900c002c030130401124584214000c40e080e17182d04514075519410311100d0f05a03c00d0741d00340d0451910090100003016a00700c4181220560b4000a50241d00c2205020303001d400e40e401e6000744100d41c20341c2c1c001b03035110314540610020990394801402155108000d032407210500d0000c050220501da0816644070350084605540181c21080816a8648a44546403103089040301400d1542d14401c011006005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 20714709 1250 20713459 20713489
    0xc030a03060f080111030a0f0b0d03050d060501020309010e0405061c050304170303040209131b0f05130903050306091003061103060102010c021c1103070c0f1d1303080603030d090302010c120614 85
    0x5a00c035801c1409c1e4031010307044501c40b40692503880d260340c000700081c03040e1540c5801150441d00140003031085030340c00c681180c440703060444003c50300d981c400e4081540031907041070b20103c5641d03041101c01805400700080c4142e07190115040a1003600841050f501e11003030318006d401c505194001000310240442d0786403c6841240a0208881c1c0c440300c900400b801a04800020003d8003020051450502810703010080c000c0f00034045810191000b810310302000389683d009030807100004050a054441c00d1014581c031500070030042c0950702e84500700b0b4100720f9400307000d5807810f550501100d0000401e14510340b06410007581c0803030b000d2005c544844d0500c0d55544648402c0c404d40300010841039440c0040c040140c8143c005624160407002501d025192404019100030144070240c1c1c0014200c0c1c1c4400e07054101015592680d0700424518031038161550402e81c603003901c403002c160b8190000d0380110103607030b01c1ca021482c1140610040711907505c901000b40c0a0503040c580c04e81042c160002a146e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 20715959 1250 20714709 20714711
    0x20703021009050601170c090c0c100905030301030c050103091104020a050f0c0a1e031d060702180f01090b0f1c0b0c040801110c030a030905030c030a03060f080111030a0f 75
    0x10030345210010a9030642ea408403156041103005120505405800c29810038424004007003e640f0400440c80c841409004054608400524280b0f021004c021010150741001c004005990f000d007001d6840340c0003800f040b1a0f900c4a00030005d5030307601c2401000759164100d403500b1108100c0308200700003907000139060028014280880218000400040d15000643c00050210382c83c141c40c22085484c2c40615180b0200300c100c82c1031001c0390f80300388412103009411030b4480c5103140c644005035183c060120000c0d80046006a4505c6120b0703c140002d0052001c40c5003c0126601c4400440540e801144040d0b00000c4c00c61424071a03150041d224007141700c6040600890011035100e18400c100d04540301c01c00032030001004c00c800c0386c00b4072a024a10260308040c6051450007080f8a80f284200f406601c10141c4036400601800400c5c01181c06019620007107a5841c00500d00180103000710f44100b484654584000144074001130140e44d00c440220041d42e0b2035a03844907a0040103094203001e10b00c1e25 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 20717209 1250 20715959 20715973
    0xa06050a030602040503010506030a0f030809120406020114010501112a0a0602060115050301031106090a080609011d0c030c060d0603020901030f060b030a0507151707050403030912031202070302 85
    0x540c640d4100c000c0a54018000940e907181410281400e40300058007544c0a54000c010b2040418458010600c000340d0515200840b5110640c03207514000801c02481d002c404001800101d883e0158005440000c0b00f245c180302c941e0381c901c0195403034620042e01450303079001749195442d40c16089043c1203001c008c7d0b24071200c4000504c000f03c2c08110b0250402009680504014028202d2040303145080891f50b01d0072901d5581581d859101709200301022501a450110705d0401c0c56960901040243c2049000c85819141c9a40020301803d080d800c0e9142e4a00080042200140041802003140e900034004004a0340c3e0b90041c046190320400c2c4980000b640e640c00440103035503020003a4000d41c00340c42c0c881910040ca06281040381d02c0044000d20951112510703000180b00840e6400442c0d501480c0f02c105000018401d40351300a0742030a4904082040c01001100da40200181050b68000d5654240c45901c0d001580f41d00c0b100c00c20301402040f01030f00308a0084903580c004201c05c038807901c151400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 20718459 1250 20717209 20717219
    0x2040e0c1b1204150306080a060501030519080d0c030209090412090602030414010804030215070309020a08030a0c030e01020a020a03141c0507080706090f03030b10050f07020904020f030706053a050a06 88
    0x400002c040d0444400307440d43c0040041c003804100040036400e0f0b3b46050988000941c0e58181e140c880c1c540141c51440d200c21b802c000b09030107641a44c1c4a8100030301001001d143c5442c01204607451420b00310046508000040ba8061000003a0742c1915000030010400001600041d03078900c2c0000d1080f8218480e0300c0034040052410b110035405401551004141110141704116601a00360001c2400d5881441002c03815070b80010742c01e0040341c00d4208680f03000b855a0041b400c064501e68040c0d00080d0701000042001521210034803442001c000346c58580c04010051400e4091501e90312000070000d201340c9001c111400e004015a40c8945000500c0075100d907201040b10795008010b4010940c1c454505049040505e0f105401102c6850b11902d49103001e01d6015080c0075030741c001ba0242a084001808540390314003a100b441c0802822100c81c00d0381e98800034000e60000040c4071170b540340c1b030648004600d0001040f001201c40d50401c0c01c03480d0002204d01c401080300500013a0131949070400018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 20719709 1250 20718459 20718463
    0xc05030d021b040e0606040c0302040801060e0603060c0306090c0a030603060e01020a0f0315061202040b220f03030903060507021507030608070e0f06120102040e0c1b120415030608 79
    0x18004a10350040c000380310242c000c030015001d54100150045040002444031500080f50706680008100c600042121348108100d00070b001c2c0c2d40040000c0d6181c46c1c00450b002c0c0700d80c0c4126200300412011200b940c1e981507210ba2442c00b0654140d81c200702500302080605070844040c01c11101076280001341d09503030b0780300e50003910100c0000101913580028000001036100c01c0003000c8081609050156070041f86c0c00f48203521075440f40c81e040002e000c100c2014643c142e0112030040c500d580b111522109d1105070501100280042c20700410381c0844001070254a100c3c903041102c6e05508c450520a103503486034030140400812100c02c6008204001240d030304c041c0500c6000b90070950740001c009042180345071424050781c10000c903003d40002002400b0380c0c40281603622040070f072003200c815801c001030140640036171b8009180c580794280800c01010254005026054030561000c1030031000c0f03d0400d81c40f02004c41e0710851100d0108400c4c0680707948519a000f03030001e145000205180d17641c000c24 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 20720959 1250 20719709 20719723
    0x5010f0204030f03050c150a140603340902040305060601120e0a0b0601170103050303011e05060403031b080307030506130c08061c0b09030a020d09061704030311030424020f160c0503 80
    0x241919615285520b0b2707849103184c5254051400d40c0202840081c00000844c800e80c41d40007070800c0c0400a8100601c3ea2015861030020507809400b5034039203480b450700303988800d8200e85690000c0e049600150240a143c0211100000c10741c002e0300300b038901d03030300c42d06507842d001881607050156929201400311580c21803180210302807000345480754100212900304482c08000480403440d0150240202c5d070710300c000c4a00712507141c1840ca040d101c684080310b030002c0c1c0340c801c050039007000402000400382d055000f081c0f0400c012a0f40d401e009880c030a049084a0034041c04d100003481130000101c0e2400c00f8080c01000c442c5418000441510640c1d6248011200701c809254a030400309038400c03101d8040191b48144803072400c00941380340c01c2c00340c0117024200030854004a140040080340602d0f0095010020b0818143c802a40d0381c45c1c141083d41a07030144d040300191840d00f07038100c01512035041c03003903a10b100104c0e001d0b545481034a0000b035940307800c00402a1507004860400190766502003181c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 20722209 1250 20720959 20720971
    0x70314130504051503192108041101080705030402091b040603020c07060801030f17040906080f060609010609090b0310020307020a0c050904030804140717010905010f0204030f03050c15 81
    0x9649181030800348002d440002d42103031555131030508102030079540441d50803005200c617001050740400e9800c0c000c01c04e0084a4440c902039807100500c1c0b0206510000c12881640a000300d0046010488011660030004452070740014005002107001031500f041d80ca9081802040e800a80b01d850f2244400503034425405075010a034002404e105400d070500c034100060480d418400c61561541c3c94448154400203001400a0311041840d44a8410a03090350702902c02d1440801525450b03600e141e80d500f480b50b040071100c0c49004001a0305240c1850028140e03012681d45024003403030400d440c0094468420907580c1409103501c010381540040c0b000d548520000d074010840c0d0740150608000e009000d400c03950150260804004c0801d40211f00c80d40c2241c0c0c01104000942040b91500b428441d41d03412000481d1a0103070210595801504814401402940200801140300c24104101e10491000620840303a403810040400c0c0a2409416000b21000950358150022881c2c840d00c8002240c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 20723459 1250 20722209 20722237
    0x7080a02010806030105010326210105041d120c01020c0a080306120102040501020607080402120a050303100906290d060e010e07030b030c210102070606060807090f03030302070314 79
    0x110103540e40215242d80110007500204036075419601c41e070503a0304002141c03403030352007207010988000c0c4602c5003256220310304000030104450031070740300c002d00b514280308032403280f0300341402c01001c0720b61240010100e40703801004080030f0a4840200d08180c10042c205406550709010010001405100080c05c440c49640d106560b86058010086440c0e58182d0031002a8818001844682d8002411039001807807814072030303455035440c80050030489070910114400d02a2000c140d08002d0000050340c013030781140c481001d4940d2240034002c01c652061054413500251803420034007440700340d07001c004e609440030f0070300d8074003502c1428803015960550722422644c118030380100108032021b107000385c1110a901e414405850b0f500c1c0080c4d641c2e581100180d103d2280380101d0100f25007081c0328045a45047e074000c0d907e0300d01e11300b0302e007009100c02d10031600800d0145000a400030301c101c4c441020780d101801c0c1070740050308680f0124000e4101450840034080407405421120300c801010303080903005061 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 20724709 1250 20723459 20723473
    0x21f0204060f020703080a0810030510050a0c020a03050f0d0204051f0e01030908030a0b0103200315010e0108011e090f0b03070b03090a06090203010906020c06010f0605040e07050702010903050708 86
    0x1200401a10644030b520003190000d00c400e0001071181411111b40780c0051034a8201d90700c1c0c0440c1c0c12110002e6901c010314911600c4a81d0303194518a410180c4a40302c5d031081000441220b8600f41d132038002017200200010800c0001c000a10b800750040c0c03c0d16220141d005086c26118404100c880d100b02d100e10b901c0200d5850000030203540082035400000e400e18003404052060750b28043c03240005800c08506a03102c10084405c1d034800d602020001541c0d001e00340950f45c071f80108219990040e03c1e080081841000c192420317502031501d0010589c0107039211201e41e840c2c0211180070044500082d0001c540c204400074500b18640202c120f40b80b28000e002808400100070145441207651080b184541c0501c2007000b58000416400d44083d000b84011034403616134800030340107008444004264034408206003100c29800101c1e01d0594074500c01d084609a150841560036002c2d07441910002d4940e580000c0005105d003015204951041c1403132240a501c07582d80e0b0b420100182c001001d135600040d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 20725959 1250 20724709 20724719
    0x10210110912100f14010b071406010f080601080106080a0312060807151704020102030406030c0c0807060b010f02030c0c010323090c010224070c02011107080105011418070f021f0204 80
    0x1104007100e060785103108000c00d905c80d414501c00c0041c1481032081d000b402081c41402c2c0028aa0300c210030340042400c2d40e4042d0b03118050360500580500944016206030030003c40c044c00140300d0a410740b8554401014802c200e55011207050b900e1980d606800c2d5103400e40010404010400709018251501650a015123208d100030708800000302c0380c06172040484184000741c1d07008003c4130142c0d80039207400b10700d48545010540d900e6050002c001c00315600000e0300f006100c0c1e0355121750b9003501c00b6a10400307070b14a40e110499580c01065103201094004004c0940d240d800f0313602030707060060600c4440070749081060f5200b80a0008039402d001075000404008642e60381800303900b101c100d4502800101c44112502070b000400000d208506002000304032000790ba005090f596806070301403044803603050b01e070f501c074501801081c072400e03490350b1150344618818549910070021142010300200c107640d0301e10700200c03510142e00c2101e505602818003d18203c5400b85030003102941110000340c0d86920b09 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 20727209 1250 20725959 20725961
    0x106080d110d0f110708060c071a10090b011e0207030302010605030a05030d0e010e030a0504050108010b07020906040b01030f0213030b010e0405030d0b0102010209180403030b060901021011091210 86
    0x50071050055001094040072003030b082900c64070888820310341380420f208200c102034549182074000d8103141c45082d082241080c29500103060b03c5200300c9004001c4088010b140ca5122025554420151001941805040c080d40d010b240b565805250440315680c110b01d00040c02c000845030303000142c00c800824005c0c140c0900036a0000c210a40040041c0e4040f52144d42d10b078025413448100e580d8441d90f178080ca1840940090b00480c8810040d2952100f90403c098504e6001d0710071207021070594800000c205850005507000315402906001f45036940c103040100400c204e0000741c0c141551903400025442c1144041c00313403040d0840141190700e0550400c1c1e27245150580c0100e241940d0f040070400090008001d0b607240d00341058010452808a0006138068000c0c1e500d000d406c0100f0803040c41c80c882c0032040c640c0c041c42c0661001c0082d41ca56105002035403051358102805a40301d01c3c50301d90861410751002d100071440949060070005003200113240701c50003140d035034203c3d44015601c501c0303a901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 20728459 1250 20727209 20727227
    0x708060301060b04060c081818010305010b040606091403070306060803040602010e0c0a0522050c0d0b01231c0203040803040302150103031d04090501110301080c0603040209040f140106080d 83
    0x3d481e10300360401d4640b40c001000401c0180004241000202d96000f03000020610704841d502c000300205e0840c602484c04180c40c032400d10066400303600748982c41d211420944101c078140c803038558624070034500b08000c0c440071006090032a80c044c444c1040000c0441c44500ca9507029050183c09181d903a89000c1000382035541c045034011182d0031141d032801c5ca5075141719159040300c0c025600405003010214522404104902103041e0803401e201c10010107001c120003d00720000103040410010300440011203a043c0407200c840880c107019241940891040e070003920030450081c02c0700d070600c00d019214500340d0f042507404035102200401401308040e014454041003080c1c0601380340c00756140d0344000300305074441d030000c2c0380d20b0319140010780d100d03100c5400c00411399800400a20a48a164038440034550092160500b02e001d070041800d22413812204403401590000d2280106071550388410740c0c692150181111417901983c094039810b01d083c0640b200030940f00014090300c1c030038404083c103940e403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 20729709 1250 20728459 20728469
    0x90c020f010203012102030316030905040e0c1e060702030102040906051809070308031518040308010605120c0306030c03070e0103030810060f030c02010b0d0809041b02070b070201030b09070806030106 88
    0x10060005000e40404200d410110704900364803800113005c030b400460301314410302d102d410204000070900c500b810342124240085a02c00c1e2402c001d0380f000c1518464a44003da004682d10422401f10300d5508a9401081078038407030700034501858070b45594002422644282c2c040c241442d100d410400c9645080440f280b024003100031201c6191403c48100c60f201d10050000a101000110200e410f1f010600c9155140c0e8601a0451391f070840d00c2099484091f40c2100d0032000680110300200c0c00134490130a6410320f0311070300c0f80040d89485031011034525810040090307401d8494000514520364003009500010a400d0349422040d50460a00510300940105544020420407000300710103030740032101c20744803130300d6243c0060740ca2881c0340100d000d0201142526401148108050103110382e603002008602001c0701c08008a00360110002c2042c080e0307980ca00c0250304225402c11954408600800900d8814034000030100f040702d002440281040d10f03054000f0304403100308001403c00f4070139503020341 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 20730959 1250 20729709 20729711
    0x60403150506100c030c03090f080c090c09030730080a0801090902130515030607111e120304050703080f07031206050f0607080d090615060903030c0624090c020f01 72
    0xd0342861004d80301c000e41660003010410110f640e00705052051045a01030541340c81d40c1c81d0703415510054a5a101d510100035485022244d0110300d6800040d81201d000e290302801400c541403a001002690241d9121440b4181c0d01d018114440c100c03800004d030b00b005114160540c1c0b20201d08800900290051308407031b07021460415803001595490171919000d01e00711a01007551390350195040e444034000c10784640c1510458050000b69500001d4100900f44a00304955200207000c1c000c1c001c400d1598144400741c0c004c1100c40c0000701083c0c2c025540240110221040f5950320f5403802100c1d8081c1c03550341d10f030130404200300c420907500c840d503100c1d00728100905000d6503041100281c5000c070b280c00745510520b0000341100800c409001a210340d4085460100001d070035608002c0080c000c40101a503202d4504d28010440301d00510a80056036015994111051442e0351251300a040301c507500600c02c04200f20001505031315100380070142c4081003000c503100c00c491801914240c40008034400c00e03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 20732209 1250 20730959 20730979
    0x5090f06190509010b130e01180804030204180f061a03010e07050108070e09090607180803071b15020c03060106031406060901030905030703030515010c050a0201030c030b060403150506 81
    0x16020360074281c5060750704404001269103035070640d1801001c6141c10f5580040025000b00c1503643d03680c0c4040f00d50040c000080c06401e400248034a240c003000d003402050420180020700160a0a03484512082c8914190a82c10b46040e01d807000b0059405400b101c41c55204c41080343c0e20750381c251030304d101c508055000740304a00340203c1c5181c9808250064a0400440900003814203101d11b948503d905000b40c10389e2042e040c2060100d03211141110120046614000405641085507080300c0494403120061420302d0120f6550540340000c414000c2c01d0480c020101140600d000080b00345600b0741c80d001080560341100505080c000305034807403400c0c0351401202d0070000d80f00c800c15962240d01210f0f0b259a92030701070010b03001410111400f030405d21020800304101600f50780001d01802007200c0b55044050958011034200380e042d9001072080d0002d80d0640300550190700600c1450fa860b09001c40c020408201042c0203400a030300c01c7d95040c003a5a8051400801c0384680e903009502034401d1010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 20733459 1250 20732209 20732221
    0x3090904050706140307360b2701020a03030c031b020606030f031317120a090906050a0b07080304020301060b0a0c021f080403050a1b0609060f1505060901020705030f0105090f06 78
    0x15821551780320124030307800e800d5603d080061401448407c10080c101c404030498a81c1e40e040d41580100c0030080d070040403100d0151104060355881018210140d00400c1050741c05d0350200c0190082c00244401e0580b1040032032441a4406184511815254010001c929084007094500810386001c241503400030032040d500d21130307003a051105079001c10203c058400c03520010075145c0040424118032410b008115500710a51080b0120102c8121207403c3c00b041d52107030104203400070705200c0c0c030926400800442000550501c06150301c240000c0c00000d01c25990813606400354020050000081c010070007240842c60b1403049a041e90403001060044150090806050200e0241c00031302130000120300b0b014034038030641e1062034031003801c0c018080c0b14a480c03400d90080c2644040c02c592003810318445000c0740c240c0f44140841d01078004c00c4071461500d800180b02840d404032080c00e0441c09568004503882d1010008010800201e4000242c1445c000d01c00710300b07103074840403210510380210040c098 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 20734709 1250 20733459 20733467
    0xb13080906070201020f0106030c0305070e070905010c06090b0411010314060303070201050705070f0b0a080a0b09010902090607061d0705030303160807030b09040308040309050301060612050903090904050706140307 94
    0x14484001d44110740d480c0b03600c1c0010303883c1120340740141c4010740c20300e440481000b1090103440d003101c0c443e03c200c0d03480a0711046603581d50602102d103880042c6da0041d040069601c282c603880c807030314020b007400100c0c034000e0744a10000c1700b42164140d900d00c00c880b0882c034055a044c80745004004000b490304a0b24180440043c0e164171960201038100f04d0045107107400e006050011200800e8000304902d040e6070780c1c03510903c694001554000204003481d0029020b2200c03070051400e1040c00400f80c0b016607080c0844600250419002d4640040062212400003280d031f2084010100503003009402118808840c10b10b4503166810643c000e420501c01d10806421820103c43c0312141410022040c0c0d4610104500038402c186a580c1c0c42040142440309150b0040c0c0050302450080c0d0320000702c55150b030107244c04d9440130704c1ba0318006040d01d0320400150ba610303401030750010103c03c1074031f00e06030f170000005040010940c1c00f5104c80d04550010003216070469005400070000f42d0405081d0b2925080c060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 20735959 1250 20734709 20734717
    0x308010807061815050c03131406090d02010809010f020a0203040810020901050a0813080a0509120d0203040302040e2e05090a020f040e01060e07090306050606040806012105070e040b1308 82
    0x201e2000720803130114120602800548242610000c212a1a21441d100410418180344140c1074414000701440c200340c01c1030f9045a8058901500300e00303044038a54011507011000410344140f955070b45650007942c21032170000340348560f440c1d40219185d500340f90388241031500c120140e02c0c040380304003c2194681d0f086001d5440501c1c807800c240b901d9513583c428041000a41060080c0902c000290903001c1541150140460b400296500d4450203007004d1410b64503119682e966004d43c1c024042000103181a81200c0c0c042010001900c0022940142e9100e88045450304408107403009049211242d409204980e8400d4894004040b00299030700403900f03e00610000c64090744d140c001c1d03054200400d40083c8018040003083d682146011100100420500c1c0001ca41060600c0007049503890b040040d10159000440904060391820445a010b001c030000d900380c2c0c014141c41410041101440312038010241a845030f0007500d07007441c0c44201c0f070100070541a5050f40c003840400100304810300703413 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 20737209 1250 20735959 20735969
    0x40312330303020d0518030709050a05090705031c0203040e0f040506091f09050c09040b010807060c080901052101090f050a0c1409010507021c0303110304050307120e030a03080108070618 82
    0x203c2d503202c0000b883c0340e6440480786e400741d80511072004000f4691346a079004920509400a0070002c9448000c0c0803925078400d8072a441e410b0740000303018002c1c0d260310303100c88010210b0350040b01c0c42d055441c0402030802d4000c48100c0a100f0034003042105001c0140400c6502246082c043c2144180060500300300511071840c510101c1d0351072aa0701e041103010403104003c0702d401088244903103070030300d800c50200c0e00901403031706203014a02c4005041070003a20742c079a003981c0c00031101e400c04211500450365500141001c404544009140707040d030f40444c0a8060282c03004010100304d2010701c41c01d5a0596201420320b080701484e1154600069a11210300664400540b00c21b6684192440040325680104403010b036115080c541c00d010b000001d40384039034400e8400d4134184038410104040350300a00003140c010740541c00c200301100016175007404000015580c0e00b00107503201c80540200e8074000900d0b00440205260000512480b401044101c0041406140c1043c8002c40c3c1d814841a0682900c65 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 20738459 1250 20737209 20737217
    0x30d0903080a140d05040213090209010b07020d02090405100b1f0309061b030b03010e0102030103020105030c0306010c060c0503100f080a06020f0403051204060f0804020612040312330303020d 84
    0x929240c1e5109249400004a03c551616140c4002907814002003006640c00c0b44211108008612010313038500030224080d030005c06100e000d03031070040d850060340d004c4c1504a0303000d0401109039005035103030346001d0300860084008208030300078481030307200302d407020075080e442806113031144804141d2807946220620450b1030b000c1070030781036851b004014001ca8a0b003104854041842541d040e51706601207604100200c00034440501a05001401c0744002c0c04003074000340040000074140c100c0c10b001503400002c180341c03009803000c0c41c3d182c4a0885000d4880800003800000910408031403284100340980441c841190619142070526a5100d01442000b80659004100700010350305c0315007690000e503040000c4e10802c14210300c110f00154481d000341c5001c6480c0104200707055100307500e0309200e1580900020b2034005100c15150045000400450422401c01d500307184d0500b49008808e142c681d040c80000c010b8080018211403440b440740d04030407640c4040010004030380e0000b54a1001e41072400c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 20739709 1250 20738459 20738467
    0x3030306130f060504051501080c030601050f0a02030d02040b0325021e0f0a0b010e0f060f0103090f0204090c060f030908071b0905040308150d03080601030f020417030306030c030d090308 82
    0x40c2c1c42001d0001540505d90141c500002c020906000d1400050605000d0b41c605441d6910b00e0042103141c042516034a0000300d003400b40c40402d450100c01000001c07001c0c011a03060605904404041c0e900c6508000b003424400b00a10001061104a2500c1c00351403403820041100700100003507940003500351313820401c01d00010205c15041e040c88440d6501181c041540c542203528100f00c005114203101c0c1c020040100f100090748210142006401040c0c01884a002c50305018011000f8140342041520414840f0200c003005a4492050f910054492007502c9032151400c00081e107041000d003111001d05041c44d242d4400500c080040721a80d0f6400000b06002850480c1c024004030100e820a1403194175010600042c190000c1d4610300c40e4a580e00c903e13060030110028041c00c0382c80384000070041006400412455070091700481146a6607582c01070070140d440b141544465640f103d1a800b41c0c10000601c800c5017424080c1c610b5448054004040c40440c9490040c60307400c03135100c00380c02048049 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 20740959 1250 20739709 20739731
    0x103051504020c0d020c0d1104020f09060705010603140115050d1406090304030b0606040302010c06051b120103060c08060607120e0604030302150601021c03090f0506040507140303030613 82
    0x210541150301030141c0304640340c6541c41c030700300d603180446602140503202d441000150f07460140b012000c0711ba489280098000745003c240709c0a0b401c9031130420346044040c4100343c1d80351901c2d0090007455006070008a086451800e0900b01d0141d03c54034100140d040c0503040384146030380000d100880e442034440309003410450414807a580781c00c4c41141304074041c9a061103615840080500b0030399001d44005c00050301d5003000c1080c07a22840c48001d0118120200c1ca00c0440c031580d111a611182038540e40d620b49094150b100d4944e48005421f00044402400510a02c0164842c844440c0031504102c1c02e43c1c180940090302d28010000001c14100805c8400c0b500c0c28424801e000b4800300290285480725140c0c40c010b900c410078a04081051000d0100081c1c59620001c1e0118411040104005545074200000c0340600384411741074480c000000e400c1c5000580800855101d1801500900780c80360501c240710030740020054646200394428400e1040c2581d400301803518640081c2800a0008441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 20742209 1250 20740959 20740981
    0x90307030204060e15030109031205060123220b0405060c07050405040b0103052e0b03070509070f020d02010c170406090b09010507030b0d170f070c060513050904020f010305 76
    0x503000290480d003898400a848428004500c2c00750b0305c2948034031021000003003450300701d0f10a250003400244002900c00d65048903640015044035062400080004142c10041d03400c40111b01d031444c4002000920881422203040403060035002c8414041e0305e00d01d085055007683c011805002e102ea100002c4502d02404c0c1089060020503001c1e00a0015151034242038440c07090920068455000f003c9a95140c00222040318051381000300d9000c105812410043c00100704a48002d5054410000301054660b0b43e01120f0344151501d9031b40441e080c442180080c108841224854256070614100b00240c84d040b035440d01c4101d8400000c921b0998890804001070070454002901d10302c4403000f0300c05880019005a8440c0110307481c14050b0a10b190b0a0141d441801c0002501e01c016464580060055003002851145481c00215003072040d03544441c0c042d15019070000001c180001000203a1803a000008001040202c0d201e00051501e0f4001c5a0400180101507040580e510b000546070040c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 20743459 1250 20742209 20742223
    0x90b03071107080d09090b0102030a211e0c032703081504090f020405060a050904060c0c080307111903050a0c02030316030201090605010801020c030409090f0b070c1703011a0903 78
    0x10f82c0481e000004030b0380c07001d4440300c894050451814200310651500f54000003c54540034041c0e034400011b0105d1000c01c1c54207940e01c60820b8100c4d03880f1043c0c890f03031802e2005801483c0324000d0340000c1a00e40440c0203400c80c0d07880741ea1803410341d8195511403030180703a40070808480e50300342c101000c5d50313903404000961081c070360411241d01c80d28040c4403601b880102403103904000d1013603e00b00040e0b2210420450301100b10300c980da50004804c1c0004001800b107400c41d908406030707803e000420039a01d651344c00d0150400c80d62600003c42d1100c011880140c00c1001e0442d0700c800b00c0382d03202181c3c50764600400034851403a1000510400d6440307681151020022110403058600407100b69401a00d0000e019000000e0f003a1041c5003020004100c80e4030610031524940c0592008510341490124020041e001c500f006561040061500201140055001c84e100c0d01c4c1c141d6400c041015540b5000c00402d68041c505140c1810600050007000d00c02a1900300c0c0f8285000081c5c0c9840829001a1810311 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 20744709 1250 20743459 20743469
    0x30e1b031c0c0c060305040c0602010204290706020f0c0c0607020619110304090f1d031c0902040f06080115030c1802040312030203060310050c040e0405010f0507050c070501090b03071107 82
    0x3a00f000011410340c142d11190003180710b01c0c994044685c2e45d0800303c2c280d00450148a641007041c10361420b088102c120000103503800408010b0400705540c035188203d030030a030003142e4103e0340003c42545103002404078580128045034101e00301840707500403415501404500300714041581101e1800c0e5801011004240104a01141d40e9151a8070a080c007505680301114542e500f080203141400000380e10701800100074800039414205d09440b005410504200d918642980d10309103203002d40c485004128030030880c14404190390345400705d1282110301100040703c0c000303882241840010441c00b00241250411001c4014403803201d48134030028030076548014420b10030300030710704216500f40c1c000c4e501c14a0f0860a903800b151020072100c0581d8000c65142100e00030800003444007a04a81146c1d401900a0000080d440040c100c1c1004840c404d0310ba000c0840d034041640340300208204070142c0074010030301e046007011380390901d1000c1502020703140364140111081d103105403100400c0382d84c000705 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 20745959 1250 20744709 20744723
    0xa020304030c05011e0e06011211060409230c090a031401110c0d17010305030327011406040b0406030803010306050a150e01080601060302030603030a0f0905030d030e1b031c0c 77
    0x140d128059118915085c032010003c1604241d002c4148460200c0c00d00d0480c1c0c030740c12070320310003050301d40e1041020611041011f5100c1014031000c1498401845485940300e210719415556403c407151041303003048010800c03e9070f0403042006040580300c00c801d40b0100c03a40401640c03c6584080011030144c6000c81c00511044004903528000010001d1013700c1200c0301d072034100c07000f107000441800d400001d00001e000c9500401c041100c8100803c03840d280311174015084c181100c055040c00d030a40382010030034a42c19040d2018000700b4a094415941d007017100300c0d4204849803071035a070b0f580140414800500316507a503c000408581d210b410070302d00070010810b490001c54841c0c4c440f1001c6142809800000c1c8940380000c076040d4028400c036401400014003c1d801c18540c402c040b01d201c14101509010031207180d500040c80c0d1004c000c00c0285410070748012400030500842649002600255266005100c40c0417100700e0310042009004003450345841032034000ca4840a8882102d030b40f400074001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 20747209 1250 20745959 20745971
    0xd050c04020c01021206010305160804051518010b0301180f080409050103081c0203012304060e010f0503010b060307170a020c0304060818010501060e01030c020c03030f0a090602010c080a020304030c0501 89
    0x2902d07041d4010095080e10708142210782c0c070343c200110212402140d414101501c52085902031600820016600920881c110703081d43d9040034100d00009810381c1c81d600401c1c42051a0200c400c000c0c05405000c40080d4004c01405074045031140c03980105c2c003030140000860b17200c1e003010f015501045030007500502000340700d42d580d00e14148074154010081e03910f84003201e1070f040134030450340d008607412100031317900c01c002da461a150120000800f040b021980030b41d4810001400e080f00f68000780c020200c20801041080c5170806050070354001880080c4650303000c00c200001c440d0130103d054440c9a6141d0120b80b180e8cd050440402417040c14001c3c401031001250000d00e25a0202c41184214000b0340070680103060350120500303841c400e01401d4046082481400c036254400d40c0030402512443c4107c40ca50072400780481d04650040c0d80e0040e54200c00540e0054071a0020102c130014100c82c802005000c80c45e2100070108480508109102d0382c0020200b01803500c075015805403d038101c0020040c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 20748459 1250 20747209 20747227
    0x409030206040b1305100b180a0506030c03010608060f0c0d1107031115060f03070317040510050f04051c050303130b070f0c020409020301060b03040c1a030c07020d050c0402 76
    0x1551500b15412a25842c00c240001c4005401c0d05040003c5644800142071152908101c00c01400541d9002d942240500348451200d09a201205024004900d8005003506045e024103051141000e100c0c0d00a038105501003004010000f801070780b0580b10140b0040c29100c0d034103030600a02c2a400015440c41c00e0090032821800d80d10006c041c8103100f81c030f0388203202813105c3c00540c0320030390031091900450300c2000090f000e091122403500200350040540c3c56882d01c80d03540b50501c181005030041e14180100d410701c50f074202414940302898550a103541054a2640d4081c41031042e40191070145040402504c000301140c03a030800ca10b0303030120075240c692909000d400c040e0000301c441518542a08404640d12901524044107480b611703603594101445c0c80d409220191040e0038040341c066503103030400522800c00300013135070042c0d1240003084025403500040502c200c02c2c0d5940540710b00c034100140310070352030340200300d541c2554140c0304000740748100c2c240203091410640030356410500018441d24 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 20749709 1250 20748459 20748463
    0x105070203030d0c080a1107061d0a03030207120804051b0d06020c06040c0906080d14040b070f0302060601080c03040308100b030703020c06010906030f0206030c0403020409031e0c080a050c07030204090302 90
    0x4e0f94160380d95003036000d640c0c41ca14541581c03280a82d02609500410014021450315006460300c04c408121004038400084180e034500f110000d029000a60301190520420004074100c00080c03146140000c520304084d110107854800c0340b0190500c17410300c00702e080308a8480d40348104007903411007400c42d11030070700800e500d4035000e007100d0445141081007400b00d008003040c440e590a4680110040400c6c0c14100d40c00d0b03e41d80e0740c2c1811011512414840040c20134030030b10003421424414401030500440c80c0ca800f9141440203000581400705880c20064000150001e60b40c0c450341603d0401440d455840d800390203524203401ca0f40d55503000104000317505405400034030036035800a0450301103a0340d400c0c0110407102c0c1c9000007403980c2d900814070303009494000082e5030420035010380145096607a60004d8203c1c1d56441c0100c1c080b400b0b1080d83c0c0b206208040603421012410300f019041102c6541d54000240301d1581d0030014040045802c00240404000c441e0242d94081d00c100322101c1a410065 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 20750959 1250 20749709 20749721
    0x204050f06030d1e050702010e040606052109060c0a030e07060e011d03060105010309020105120709030204110703020c01050c010b030601030b0901060609150503070509040f090201030b1503150105070203030d 91
    0x580a4400d0b01144018113202d1a019080d00d1040c0c5800c0d101d8900958084031950b000000031390401c003016000010030b9443d031180d1801000d081d122030b60b40d4050302444a201205803140c0310100400c40042003881d840c00302e091940225145042a0f03200e10b068010b0300146041c40d1001c40702d10a140c0c01140d4150440d0300400c0d04182601d07181d004c400900c80c020130003442a0401da030560890401080300e9400784d0007081140d441410700c18202051852038603001c0f84111005800507812240420943c14a480b50400030503030454894907090960300c01070355403281502d00750b04208000698440030030003075200001d02c0000406994403940e41c0e00b42031140c0d44055805505552130100c1c000340b950b0044448004941c2c0008110880d80305207034050760941c10003040001032140400c010300c0d080d9680d200301c00c0140700c00c4800050045490000400720b4403020711450243c0300e0620301403595040e55041d04ea0240095103502c51701404000100d615000320351009426120110302c21603030800302d801c8a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 20752209 1250 20750959 20750971
    0xb0c06010618050d150905030c010504061103090a15020f04030503190323041a0405030705060a111209031b060f07020303250c021203040f0b0408070608070c0204050f 73
    0x18002c0c4190b20700d500d0074003680c148070f083e610945201018001419003581130441410220002922003659111039007168080a40d128150f591030b0100b00800c1401e1007a2409915544400c500303516014071070b0b0703035102d180d885c0140c04055484100e85159040c3d404940080786402c9030b290301c0b15924941190350350000705009680c0c6407520840d403d01c5100e44580d92010500040d00d40100c3d20110003280341d064007510550b02030b10395803000d040385546071102e580501c1c8110011990368134181171160030110050450074103942851000c20b00c42c4000c13802e9490380c6080290745030700c6071550795205207103100d500b41d5403586880e16054040030090105074a40b0070130241216605030f95a0140803030f1288800c5070200140c01d502c042e05000b15100c00000f082044482c00c2c00700d00c03a40380390001144140300c407401901603840007900313000030200320180b50010312110080328109400c0031303103594481a8038007454040004150024503854030440d0103030025500640204003d0402c2c40504540c2c200403102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 20753459 1250 20752209 20752217
    0x304140a05030c0603041e0204090b06010816021c020703020901141002031608090315090f0106060306120b060112020309030702090708040c03021504050402040803030f0105120a02060a05040b0c060106 88
    0x91604000c50003518543c00100034615550340d984d201103a10307000760320700144110b80086e20b4005813520303c56200490b0141800030014641000010064000108000c2c03001c00098a100c0050350001586480d444d030030503600e00c010250a004a150142d00d80c0042d5000d104c0030700000d0b8a40c803105902d00030301c000b13495500e020015106d00f039170307a8421501d1018400b8030244102d03021035828400341c840c0c94401400e54207028180021700c90080025a046180394200c1d001d0340c6107409003441240c0050129040510a40c1c0c50103200d480341d0042100301401ea40315000024250303138820b03e0068816607030528119200d040041e0117555a40140074202d020f0702c1414045500d69000b4400c0e1031140303078061401034425085a00f40302c04640f81c1c2030350415800051202040c29515400035001805030003000719202d113040062414000c0060344524080d030050412050750741004580c003090140c050319020342d55807500004541c280318941c0841c8200501150b24a150000841e92904a94655503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 20754709 1250 20753459 20753479
    0xd020a09050a08030301030f0204060803030405010b0108130c050402030417030403090503010f05010b160c17010b03010615140322080703030f02030610080a1103010e01081606080106120e030414 85
    0x424040350410b00d000e0345010354400d00c010000036110180c80715200e4409440400e200c0e0392065524a50b07001a5401c8850b651601c0301c00295591102c10b0030740c0005c0c8500001c0051040703880d041650310701409140c0c000c83d00000040c0500c4091401c0030006a40402c00c140da92405080040c004182e0740104c40c42035003442000000b0040b5401414165681e031a80c6074079000300c680340501110144041202c02c10800300c1d0000300c0c1405417040f0304003040601c0000c02c0c4441500105804c60b15a174008203c580d01c00c84c480d464866206540620f500e10603a031003507030380e02c99006a21116440000400003100e401004104100110010b4200103100703440034068543c034111b448069000c102e44541d042140c1c480ea07a03c00314410009160030086000000851648154541c201a80240c00203800c107102e4500411942ca410090a1850054500b80301582c60610000030310f206410300c1030104126007403a01c048000640c3d40034500040200f01102c1c2d555990b200600507410000c60103502c1000e401c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 20755959 1250 20754709 20754719
    0x106090e0f071e1202031503010f02030f040b0a0612080705010c0e0105160201050d020316170603032b0614010905040605030a020607030909020d0b090601030c020703030509010c080d020a09 83
    0x19203100e000303920640341c069030603c0002400c00030704602600c1404028001903091100d0b48503100842c0501001c0011480000d0358001703240c25214108200072200d8410400c000851092490306900164004031222158480001300d0000d81701d1074010300c070f007050400310303050801000788000c000c4580714800134820711600200030740e9040d401c800800d000c10000c010814000100c128a1030b00d80d841410818203012081c012501203800c201e80c0081003505091802108540200e22000d40203c43d210603106442c000740403c1c1c4a0043e03006001c2c40c10f6107603d08100e080c3e001e8505c43800104c0380060421000327595100000c0c10242c02421140891000302c4c0210b050704090041800741c0e10050b00038000810315509100583d800040103904101044402188000540c00100140300c018940803e410304070008109034124041c001a0605142030003c0c0700c0280c02003074030421280c142c00c120f6101c214440043c0c40785a8800c2c0c0082c0304031000210848030b502c16070701801c1046a40e6407107260407a215 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 20757209 1250 20755959 20755981
    0xa0e01021504020105031b030a0b0102060f04080409052706060f01020d1d010504210203010b0402041d06030c100903110102070303050d0216060903020a0b09070b040e060d05060106090e 81
    0x710304012450403440016000d540200001e682084040381000056003410214004a41081e100c2d038007220b84801c800134140d80d0410500d5007011071400c5220700c90410740e442425a20881c800c00b90b0f01e50f01c0324000344401c1d0029040d8001100390b4003810300a0362003048400e4039010111130280c0f0412500412805039440020030f00c4a8a40b1a01c0329a0840010300c102d0400b4440f00b204103040107010003011440d1030240b1450f680200006c14241103038680c6104060a40d030054446034004c51041c001041203d001d041b0790522031145414080454440501081c2801b8120799555080b0340895503004025a004292400700c0780618510503104100e807004a8460000c0c1c4400b80002d18107022810301c20b40d2603070003080304411801d984c4d020345503d0b9840e00103507440101c1c10390158101c854800113004000394035580c413285a0024088080c14505034122a00441c040c036581c9104c3d040000d401511440c2e940054540c0040882d580c2d917130345484c0109110b4550080001a40107100415913180e04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 20758459 1250 20757209 20757223
    0x6030609061419021b030a1107081b090403020705040e070906080a08120c070c0b120601021609110408030316020f010e06060621100501030c050309100b21030a0e0102 73
    0x3003a809503141c0f0700d08441c458045d40006a00c070f18201084809540c04a00c200020101550750f42c82e145020b0030341001d0030307051001551044105030007c0b1114840b140200c00303c0055000101d0b14040240c0f00c82c1822450f00801d60043c42e042407a04071003802a000c00207071081210f0101e0018048280c40700d001503115084100c0c0200340c103070140021694a121b0350640c96001c3e013003440043c2440c0c1152919000e00116038003401490704009030a10f40c0f00c07400b042c0180c0c492802e000409260f09014189a0b001e2018032034540c1640e42c90004105032801d82084400401c100c00803242c490a040304ad40c10f8103141041d03880c1c054441d06821407907426040c041c003c50307184440090501682c034001444032035480880080301b003002c2848000c1c80c80c405c00d01070600401c2ea81c01e90000007402c01c40050100c1e8104408401407101c01d000300f0070703003440026084070301110b0114081405000032010070300c2c40081d98001da00582d10710003046004640080940414801542e8401480d024440103a0b281d4403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 20759709 1250 20758459 20758471
    0x702030c0f0c06070b13080a0302070c050d02010c060f1514011b0803010e0a0e010f0b010206010b131419180f0204030201080a0507110a05060a0f0203070219020102030904060306090614 81
    0xe001d10581e404282140065070381b02c007484084000d880016980c00d080c40e4844040b2801203a030204049090000010800d8094001070782c00340ca00090035000070f00015a0f9510043c0f6058940300118000861354101c0140c2404400d4030840d801d86401d40301180142c4d60311741d1070004150110307001104011020907a500c40c1c02012152071a420155002003c50008041380314185d210312540c0075100c1d09105000c205090090001503083e01d14000905150041c1d0190720f00c41418080e90a000744018440c5084401c260001d01d44100000d0119080c40045002003c0e0072440f148000b813a24007400c22003000712070782e00b010400da40301d01030b5a1b401c0780254007010703001a00d07010009007050354503031166400c1002814050b0b82090840c440614140d40040201d9180d0082d41c01d010301c4a035680501d00b8803640c804019070440ca8001002903484480011103150302e44035a030310350213590080c800c4a0f076961015205102d0745489080c48805084911402c80d0418a8410343c880d41d1003140c0a101d00a02d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 20760959 1250 20759709 20759719
    0x30304080a05030603070b03011509060e0117060310020705151b04060c020a23040b090403140310030507090c18060206070302070516030605161809020307030e060702030c0f0c 77
    0x54840c0c0c00715030b55000100642e800d4402c911000c9120004600503500801e03031107001c0c048031700c0d1011000f007005d0746580c4103105011509400d000c03103a8104d1003450a18061505005d459075940c07000900d0034890b8030505c04007506c0040c8240a1040c0400c072000d5542c000c5c44c2c45030040d1a68542003c071845001070340c4c54452014041444076a2189001190303890004040141c5251a1405460807138003841444501d0450400000c01c01d0911b40100f08402d40708a13400646440c0984018006207401c021448401c0320003c0011842640d0144410145410a0445210316250340080f00100f030005a032a000c0750412036002c500c02d0500054109403290f1b5406400152a40d4106030302035041040c0480f000d02038503071008080c040c9030040c0301c000c60144c43c020a507800c00000e03803548005d031810b4000030010704400169582d840d401034001291600040181e60380d0310040c0c203c3c002c1c14400060201806601c040c0030b8416400800b81c10501000c1095600601c080f000f240d540c1c89840407415009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 20762209 1250 20760959 20760967
    0x8030304030f05090112060906051905030303070507050f0706030c080108010912030507050409020c0c0118030b0705090406050306040309030c09020405010206040f0809090a090c0b0f091e03030a05070b060303030408 94
    0x180c0c85000a4004c070401070411410350f1500122000c1500da55400181034699500000c20440c68002149a40848100500500c5904102c00f03e0340324440200b2000510100041500c02c20104010381d4034031881da801aa80d00a4441e04000d02030411341c941d50340064420000410003071018400c0c18100d5900080c000380002d8560303400d03806010f0041065051001c2484006a480e000c3d0000b04221415040a0300401c521103001400c8525600507546a49010360411310004444105242c0c212446041246d1124541d83c00100603012a4010381d825000e07507402d00041681040b40d160a4034841d210519016495022074000c81c042c5204140c011f80c88507001c60f001c10004c0e641c280c4d0746402000e103245050340d4003010846021050f204c20202c1540da590701c1c3e050056610064025281400c40d6500c0c1121103e07143c4560b004280b0f503035110380001010200035818008402001100150559883e00704245014045800401c0241d41d5101c1e950001051482c001c001c51b403045a20810f01414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 20763459 1250 20762209 20762237
    0x604051803191e0905210601030602090d020409030203090414160e0303040b040f1a19051c06090b040b03010603030903080717030a0608010e010504030509060d0204090c02060405070803030403 84
    0x10341c0c00b0406505040c007640b50001c01080b42c2c00d030504003100c02d1640307881300b03001c0ca4082404640700c042c000405d80c000c00340103202c0c0880c00c040341ca141100d810180240c0c440c4200300014000220740e900081d03105140c0380108040640202c050b0000240480703042100c0c03d2034240388030b00000c0031a070080040514880304408540a0b01024000e4003000e82202d080c16141c036a03211075540b01741c02c5848010010b000401c0199a00e80d00440030140e1441e01c14144120120310324a032200b40220700d014014041194411140881000502d00a0001c03041c000da81c0d442062000402056201900070b40c1040c07146502c81c181406031104482c2d00daa9403802c82031554499080d9a000100700f2900e2541015904c45529000d07400303135000d44524000050510b00d003900c51401c444002415800c0c6904107010071020070b40060030394802c0f045c10340d403190b601e84006841d0802485941c200d1107541e0300d084400080c0c10381c001409840745d071049007252000364441e200a580c85c001150000c00107400c3c00c0b540d120f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 20764709 1250 20763459 20763487
    0x504020312070f0b100e07050a02070b0a1e031a06031603021b060103050c01110d090303030e0304051804170304120315050315040302010f0204050a05091e0408030604051803 76
    0x4025400f0f01662240810280d80742e104410054030a0070700a03a8400042c090001103c010070f0b000403c6007002441e141c84154081e4440515100312401c41030007290840d181400b840d40e280c1102c010400303019114403020b00c00340050200301c090359407003840c1c484000d08508000d421070740203440c50041002000400c0804401030b60064420100c01007408034040e807000700c108503580c0a140b20308003604800d100d0000052546040f101c20f0365146e8404240f0558803504201448180d03601881c01041020b085800a46075206603440250800000a80100288a9500d255015a108055030172902031812a483d440d0302040d680a0602ca00c803030300031090140640d01514081c03103a00185020301c0c0c0da4200107400c2c8030002155201d410075020800c000c050782882440384240300160110304103400c02012504001c2940252401a600c0002145110500ca0303402034404403140c1d480c074075506c0c041c508480f0070780094a00b68002c1d4103001c0840c400e801c582d040c03488400e0303e10004600b080d058a540c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 20765959 1250 20764709 20764717
    0xe0f010908040b03070e0307080a0b07030902010c140102040803131a0405130b04090213020a0e0102011e0504060e0319030c03090f0602071103030d0c0e09060306040305030c040506040611010c030504020312 90
    0x801800f2403200e1b03901054900388451802080104c01419a050003800c141194440040440082602e081032100050303800182520300181c0010940008080b1101407a0081c400d5400c2075110b44008183c0003022821580a002512030041c00c0c05101240154a10068081e90040300c1c0e0104034140384000d8003215600c83c10708500c008001150844c015004640540c0390702d0740855000d6000500303005040c0e08140d210b40c0303040342880208403180e500e07607810314401809070240d92410344503400705090090640085400044400076241d580e40312030519803101500751080f0300801e0500017481d1b500d9000b485522049500000c00314115010b5944040095100020456a041d980c400072286a00c0420150180d000d02e81130006000480e00006050803c0b00c21986101b444903404110007a14040340c07468116a0600b05107803203440b01c001e03001d0140200d421860f040180494000740c0b844d80504a00c46000700c01000b0011360084c00c00c00c4080e544100c0d8044d4040d4880b840403059111840700038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 20767209 1250 20765959 20765971
    0x3100204081905030403020d030905010305061206060f1207060e010f0e03070308090d0b190f0504021c1e061506080403090b03060a0902030108150108060f041e05030304060e0f010908040b03 83
    0xb1301e01d082c3c0c0341c1d40090684540c0e9801a00010341440042c4030550f058880c01d40c004d40b084500c4000041d410401c0303642c1d1503004040700e000381c004554400d002c0d00c0340352168405894400c1a01c4040e501d5040061240414200b00741c0010401158102014040e0148150fa40000f41c042d004c00c80c11500c4080a0368030800100d03800c948600386c15004560f0140d101400351302c040021701c000720a041450425550000754240c01e2034941800d0000696030181404500501f07100440c2d80c5070041e040016803042580504181801c03000c01c69010056103a21202c03204062130400c1c03c0c6183c44040031940c10a0031180100811b50240042c041f80800c4000355034804002450a86516190404881a81c101380e0081c0e803107500000b541d0519a44040c001805405550001d1807031b440d1200d6007007403414000e48064614140d01405400c90304034110b000c007040c0d4015040b03030b50b2820030f031900e5401032109100030b101c1d038000c92010000c00c4c0810f00070780c1000c94004407028109410116a442d69a1002d424 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 20768459 1250 20767209 20767213
    0x11a030606071506030c080f07030615150e031009020310050a0605030106170c06090109090c050904050c0d060803030606070b0a0b04090c030605010605030c0a050c2a03100204081905 80
    0x812000510042c0c0c45000840c3c43c0c1402050641c034500d0601440f079a160400c1c1800e81000070700d61008240051000222a00450046080b01500d911a01c0641a0b50461068500c8062240d42800d800110b800c0c0c0450090f0122102c0400c150000340440f0045d840c000d41c0340d00907070542511480d40d0b401407034100f10940000101c0c03540e00c00002e070845180c0d511820500606101e10090400c06200800543e042510b402d49450180400284903e00d80d000c2e07141041da540b140001114421001d84051032405801080241000c00c00004c5030740002004156040c2010b07001700d0101004000d4901811001d006203040c96042d9070303074640c50b04009007004c00c60343ea120075011242d959030140014003401410090320440c1036081110a0341c2c1c0c140c1210003409010424072125282110440303100b0101442c090351110b144c0150f45052090303550350201e20750703d1605492103080480382c0d030315030000381242142c1c6002d009004074030a90082d4403035000c1c1908440c040716040072030022041d06007407090301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 20769709 1250 20768459 20768467
    0x10b0304110a1403160506030c0706020405040204060c11010201060302010815010201090503030a090b010e070c06092603010f06030e030a14070b0c04090b01030912032f090f0108011a030606 83
    0x80841c82c00840b0780d0000001c1101e46111242c10304052100071840061080c5810005040101182980c03001070300d0282c0141c2c0c0025148240507c44d4160360141030010825559240c0d03a2000904214401e032040d1a602c54607a05600958014494101100c1d41a120010301c0d41d14030f845040d0744044552550b043d5521034840340002041407004511825801ba0b0005486004d414400440081608100752030310b000c40500c221541c008820702129580188045503081d40f5181c07242c0c1158049024904815044070407180b008201e4003d14181c82c800c440300c050090f03684000700c1c10b80c1c0214007180e010390130400517428014030907401d1aa00003030080030a403401c41565111241e2010858129250700400320302401040f445c0d0180f0380329180246424480047d180d2607021400040b01a40d400340740ea40e090240a8005400081005c0004864441484141d8618880069002580b01845200e0714482040c0381d6020b071595a050b41ea4040312040c00d5030074100008450750000d400d0369403081d4180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 20770959 1250 20769709 20769743
    0x506040f0c08061c05150915070804080f0f030a060303080c0a09051203160309050f010e01020d12060504020a0207090f0204150c080706061e290d090b09060403110a0803010b0304 78
    0x1113810346c01c215100448400f482c01140e01401c207100c42c26230701d900c8058401403001040d403040006411603041202d00e5034968174030803407182c0d134425102240341504010040003045082e40d484071048038001d44a03403165507506896650ba81c1704500c221800f00d82c00301c00034007043c280182507014409001d41268600030800080441e0401d0640080b00002d161050502450400e40d0700d0540015080c03e06a020390032010001c0d440b00440f22101042014000d035080010f80c1c82c1d00a41c00900d40078008540d1000d944800a44400d500d0080b8086642040307449502a00180700721811121a04100c2032443c050480c21074207105000c0054440d0340040c0007120120303100d8070400008080c98010b003080310003c00055a4080b0b40c80c1d100918039a14240e6000e03041000e1104100e41c402c4203400b056a481c1a2510000104950341002d00b44602c1c0d80b00b0800540300c006000b9005500036211003040985483d401030b5680004000145002028001000030b04400b00145403c548203150840b00c2c0340c3d80b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 20772209 1250 20770959 20770963
    0x80a15090c030f120f1403060301060510020106090605030c01050a0c1719110d020d03090212030c01050603061014010806040e060f070e0603061c1704090506040f0c08061c05 76
    0x10b8000b592400700b20304000080010384249141412401e08059241c6100a0740c080c14504100d8500180c5180c00000a1034039502035000001802c1c00600030755802200c008024005c0107a8080c40070b00034030f420303400f0034180340000d1880c0c0f22407016540c0340d1502d143c0d42c1007155029801c040880e113030084400d21071400f640050180c8600038100081482c41511010000c10700141001541c3c0180c0043c17000d8450710303901080350381c2d041c100d90a001c034020b0306d94804207041c103c4601c0c0d0b036031590101041c3c0c50014001908100d004031412002c030b940d151207100b403480e8006028841c5980c02c00743c0c406c9850040d40031300c0c0143d5004000a00020303d10105094607418442e0444400703401e40d80c10400c1190044d000814010011410b8881074258580400450048010040141c02c8120728004080c1040f05800d440000181481e00450711613590710171500140100390b410911a5050244a40f1000c0c61b45c0324512040c3d500d42d031a211545c4400003800701400d100c3c1d014821004c65207001c500030809c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 20773459 1250 20772209 20772233
    0x703022803030c030e220c0e04050406020306010906050c0304060f03060308072f0d06050c09030312010303080604051501140d11030103060b03030f120601020a140a050106090204080a1509 82
    0x7610f4000d074082d80307458000c0030f40313421098083c860700c0200c480340c88007040104034208008001200041e5240740882c2543c3c4100d2198445900900b018100410050140c01550180384203880700412551919011790f90b0740141c60004295510038030041012a1240000da40245054100043c0a5840340c88007501c83d8041e40c0203440400c0d941c50301c07100802c030a480a58520f4038548094040d21001800a001c44000720340c040c0c0b180342c0b40c1d004107030300031280000c0f1051140004d00701c070b540385203d128401040700244030690100b07407201e0005545090900505108140c20203410610100c0c080041d506000e00007094441e48000b800098074230b0038035202d86240710104a00464580d859440d240c01520034024006002c0e400901c50489055404400e540034001b426107078074070950711000101d107007400144002e00500c1e03911000d0040104041203112419010b84001e00009860f69448400d910651040e105650b000c02c00320340c0440c40e140e07201e030b801002101c1c1c0491701041d561212958503035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 20774709 1250 20773459 20773463
    0x60f03070c0f170c0f07060903060905100501080a0302010b03030a05030a0915020c0f0f0106030807030807170f0105030f01060609050f040e010e012702150313020901080105070f09080703022803 85
    0xc000030741448141805c002c80015030303201c100105001400d2420091a5061620000705281e0320380800d2420014180301a01012000030b03030030051076a4030700e27800c1e5032005044416401340d440e00035881c01070b05000c002c48070140001d4450500e1a03e600c02584000c0204440075500d1502c500d00388883d504a5000070910b104a55004000a940f0110100c1c1880c2c410030034000e4581c50314a081001510781c20541340c0040d00340c14030880c1a40c41c42d90555010500b0501826201401400c004800c45209403203416940160700b15801644c11084a07800c94009004031f1000c43c01089007009149042112003500340000340c80030503a2040c034410b02c1d0030b440040301d5540659440e8000c1e603420902000c00e080d00310081480300c0c1140f0709150040703a038140e41a1090b4401000c0000010340305200c403880740b9005a07018043c40119030707441901c20700800c002e035004800282440581c0b0110340c072644521080d41c5001000d003444a11719401c000e90650180d03900d0160b00000481e132a00b500b07001d50060010341c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 20775959 1250 20774709 20774753
    0xd0302150f0108011401080d03150807060201020406030605010302120f090a0203031201030201081f050103090f1a01060914060d02030603011b020303090706080108060a1a040204060504050906060f03070c0f 90
    0x9410900d0340f070f003502c2c0c000350300d9442d0010a800402c03140c00d001402101e0106107080c0083e010390040e1a1051203146500024603501c00c4036030004405a0550082089800503130701009603548a00c01102a80b081c101d0844002c50a4004915040c90300d9520742c0d0040e040e50101c600c03010480e0301190a5400403180c80c16080c408500420655800811060b80095000851001c04500a140d00085c4000d4000c3e603040582c0d8003020010040202d41c05c9804036000202c18a0b4014420030500704a803003409150002500580300203072505407440d80c0e500d0310000400481c1450284d02d0075034000e410050030a0380c1903413258400c50510040c03d80308004106c460b800341da03032440c0000c0e00c9880c1c854180e00a10070402c0709401006101008a50740e90001407a040c00704a80c007000000142e50182503041030340c41403000a0010f001c0d030300003000b4412103809440503407043ea2203030308100d060b002e1405900c134402000c000144610b80f143c0d00b4401d240d84120005500583c12ba1240103079a044120380300c01c0d00b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 20777209 1250 20775959 20775961
    0x3090406090b09090321070903020a080d030b01050f040b18040501080304060e09010e0609091005010605040504060e010311090a0905011e0f0506010e040c0207050324070305010b0301050d0302150f 86
    0xe4108100441c0d4083d550800646c035040c2c0000000c81d1031012840c00a500071503045c081121280701d10000740084d60020000401c10703848110807070b15410b01c0110312000c24500f814000c2d0650240f800e89544020341540f250801d480d003044144158013150490008a201880a05d003982d42c900c69075001e8035070380c00103640740c50624001811410b4810702c1d0610038902e5a00401600c201414226445001640e00082e2703034039070001e44e0345080c80d4070100c1c4007041c1c10310b00080780940e07001024000f1154100c3c0c09100c05a0340d485894040749081c0406005007400c0c41c4820018101145103e4102c01030000008200c1c0180c3c0b10345084800458490b4030031140900e40e401c05204034050b40c40c040313100600801070b078200800040c6c14100500c1200d0702640c0c43d030004200700783c0240090310041c10301a013038400e41c1c0360440102c28804000e11000b6031410300d61000c10000c40c403910515040c0d130282d5555a1440e401d00d002c01100419440048046101d04c10751031959182280c4010f00500f5180303401100c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 20778459 1250 20777209 20777231
    0x30f020c03070c1d01060c0f060606020f15040c05010503060d0f061a040b0a060305090106051f140a050706020f0409020d051602010b01080604020c010603140708010506090402030c040e0309040609 86
    0x85001282c2c042c45242c044113019100741030354420b40c50b045440f80c1c1810b8806402c185032142d20300c80e52940c090680d0345401400143e01c2c0d000b060b850718500d100c4081c0c0d00d89901c94041b00700208000d880190903030b04691000d00403940200b00030b68000c1002458111000c5580e5214111907030a090100c54154540c110034188048203010700c4110841282c00748080b10b05000402c001010a1047c0010143c0b102c0114030100c03402c0d88001c0141001504500c002c1351095890303845004440700820008040225000d406050030003900e920804690f685417a09441341c44600c00394000045480364004d0420000640c0c268030700c000c0040041c8410003041900e0a502d503245000002040481503904120009a041e07921907150741d0700c0002100e0050f22084480e01c00ca00601650304004e2681c1c01108001e070f2040d000140f004c1c110341144000780a0780c0e48450034021248010b8030001c1d0158821001d0081601d05500b2441480e03403010204c82c1040d0038600043c0503143e442e8012000d139541c500320b00762 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 20779709 1250 20778459 20778473
    0x50a08010606020d2c13020a02061506040e0708071206060f0201060807061b050102090604180e0c010e010305091219020105130f0803070203040503010504080c190c09020a030f020c0307 81
    0x11603400300c2c28421200f50581591103002c0c540b440004d408001c0355925580c2d0391b5100c8510b9090580344003821903c0700304140c2c02a658079815917084d4440404960500c2541c5800701c01c03102511300d0390281c1c80e202e445021050300d91100c0030b08840c01344402c80750404002c5002e0300c5803a0042c0607a590b1010a1280c0f05c01c041d00312141904580800e4108140c14401e031707034100c215200e018408403107054000c600e0742007143c0213018920b211603001c580010001030562a071055080d40c011032200401c00040e10b036864954684000c0e0460f8003240310301d902c00341c140d802a880f15074000004025251482c006840032900c0307500c0f801240e258641251200d5205c0380c1d091240c958004807039801a0050200b588400c040c08000701c2c002811903c0001c00980a2071092060382c0041801078002c1c00182042e24101c051034104420460561242c135804484140b55800607180064201030081101401d047c10200a1340c041e411400600d51600008088852244000e01000e00305c0c501131900c0b022640340c822 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 20780959 1250 20779709 20779723
    0xa0b0907091503051b0903030c030a05090901080601140f01261009021204020d0f06090c140d170a090b0403050f010b030a110105070f0f12090b070302190c050a0801060602 75
    0x104240c0307010704100040380e8181417860911a220015603c512102d000130385544034107402c0d0350841c0000b00c0d142c02099000005040100700c11280004240e0f00d030a4001d0703455100340710361606210ac1d1682488a8184603c4104c0c032040103140c4031981d401c2803000e03900b0071440200c0300c000800b10f0741300b009040051014030101400e2012400c0d0310b0300e0071000001d400e0840180000e80303c0c0c0c0641c1d0041f03040224034220b01d020250302c04414048294542451000c859403407090030301010348080c044000d4a0032b44021244d05600c4510000e0169444019206a03084015040280200e01c80e020810716aa00050401036100d079008040141400810600791030018078818001e60041c140711000861703901140300107403003e103400340e101c42d40740c1015004c5081190000d051074040e0083c22080c800c1035441ea25000d81149c449003425561188c0c4414035104100d00640140c00084000884448032500c1030429805010024000c2d920342c070004021503216030004015079502c000822116406000300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 20782209 1250 20780959 20780999
    0xc050607020a020d02090c0705060a05040632150d060504020f09040f060e03041205030a110c010c02060c0c0405070c0302070b090604090c0309060608010209091008150a0b090709 78
    0x50b001c260403030781c003080c0000a1008028819004480000d48094480c420340e00341a802008442c0c050600800d41801000c0a450070f841c1e039030514400d01c14500d585118107003074942501c52005981070054003c1d400c41c001034901c030144140700c2d81840b05507840b942c4090482d4000c090003d00c07420144100009080c4a25009000d41800c1080201180ca43c7c8450a000d9030803074000324650125608075803c611854110079451100e0b15148414460000040c0c400704419489500090030310007542580c0d281504503584c00102088040390040c2001009001c1c5441400d00b220480c800306800101501d00490703030b00b00020005401003040c1581000482d00808030b00d1105e91401844a010030070502c01e502519101035214070704172008a11a41c80070a031a40c2000301042700c1034940070ba0031702035032001030681d1160001c02d01250358a4003640e440380844084000502584003c0c0c0003100700100d005104404541c8d64441251a40c0c4500c91000d201e11496540d91081c02d041554800d41402c1403602 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 20783459 1250 20782209 20782213
    0x1e0e0106050f150f0703020a0c180c0e091501050f180a060912020603060f0a150e0a0b070303050903070b0915091506040e0f070b041a0c030409050406020c06070c05060702 75
    0xc0c0700c0340f8103698080340c2ca12400c000f074260707031101c09050503440c00e01c9400c002800d4a88140c0700150142c614030000100301580d0070706000784c40341501e04403210400640c100e58402ca0600201d007100c08480d4188503803e00604216040c041c1d00d003050610382e003202007159040c4682c58050790903450034140c03103000351810742017403100d40e1b062100c0800a16a2100001d001d01e00000100303070150b81e0380c122003650480c01050182c1040c0c4550300103450b681004124070100381c4042c4031810520301000f080050700c0103102268144115500c003100a040090320b040440c1c00100301c14008601e44413051031090381242c009201a03045c07a444403034a018001c0076040f16401c150030b81036551018400b0700360455030850340840c910002e50b014500b8051070b1511b4003194440c000d8000f8070f100d06103001d04200c501c62480c43c000520808200780480c414400030003640e81003080705001100c0070340e01454010b800303103030018182021401d10514101041d20340c0d0022078150100f002c00c0003401c0007916842806440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 20784709 1250 20783459 20783479
    0x60313150c110601060206040605060a03080703020c03010b121504110303040902120705030c070b0901060803070b042112020a09030c03030201051b0414060708090301021603020f070b0a031e0e0106050f 88
    0x170007500c1360320142008140e55240d501042680c3c6e00c00c9444400b5641000a9594903015858041c0d99100400c610a0295003094101400c51402221000121501002810000f0301d0454103100102d0024812a15480050502d90940d102040071703102a00398000010303584c10303d601d100c128082d402441c840402c4010420400c441c1001003c1d18566580700074400c0b03240e103a0340d0a05c0d006d099640c0208219100100ea01014001d1b050718240c001d03805502d0903551141e85144152404661400c0344001c0390004040d0165502142e0081c41c4c0c4a5441c0345c2000800d40300d0307903007102d8070600c0e51069005079154020f004840904805900c5030a00e80380046152501e040c0d140490540542c0340d0a110340c0c0003103086428415094200e81d180344d8000e008654454071400800344901c90100c051740103218061841d05031042c00154042600c07041d440780d90804e0340700720007100034101450503425620101181150152202d0107228501e011400c0081203050820050144d6a40420318640c81a0381d182 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 20785959 1250 20784709 20784719
    0x309010e070609060c14011a1c030c14010902130501031103160909170408030415050a0c020906010507060e030a03110702090402090c04030c03032a0203060105060313150c110601 78
    0x401000700700d03101402c20313174064125400c0c90003021480c0f50f00d0074019400c00c0031480020320b036405039600030401101c1c11902c122104401c0058030074441c00083c01304224200b10008222410401c1e0105558000041034030412640440d0360030600341c03a480c5841e41c842006000700110146180385c0004190020100702e0402d803030b80362400c600b03842511f480070780c3e8508900a10110f03803201d6a000b109a01d442d90345981d10003a1581d00d07401441107810b80c02a80542c124041e100e20f0450b180c0d980f03960741d015950f8109808100d002c80e130180c06c040c1448000c10008000501130f018010b1200c4811014540301c0c0040c0300040c050710501c403142c08c643c1c0d40420409005039903520b0034a400940655103900b0951303c4402c805428441e41d0000b5103e10401c0c42e0000030594071030080780e284026692a00d0800d2160345005902d00426640250725801000040c4050300784180610b5108c04080111074a0000d6a11071012064400d00440c0966440c0c0ca620542c00d600702c6500c51580c130800f4000c1031198902 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 20787209 1250 20785959 20785967
    0x7051b030f0a080f04080304140906030304030b0a110c011506020610030305120601090302130609140108100c0516050c030606060f0409020706021308061008010b0a030206030a061a0309010e0706 85
    0x4004010101c181c0804d10042c00081e4006490141c60640d040301c0d5510b40b0f50003013142040310030240b14800c3c0d0b40c07000041d807142408002c6c0c03000c036603200070642459100c181601014010300c140e1402030030000e00180202c14024081d038681d400b6014a04190981072880c02810304500410003012450704043c200000b0f0740c407004884071900980402d8410380c0702d580c012a017041a55001a61000c0280c000307118607113607a403007502162040070040120007480c10004e070b44413400344120282500f03c2980c1d00e00c02c40682d0010741d2912000e2903c035240502c6a11807c61606400c4410344540e4000742d5800c809040800070503410490441e80213052101058800d4068804c1e4021146555000304814042107400c0c2c041c0c0b0b410051050703944207040d44922040d9a180000c59101c3c041034401e08000030f080710184507805900c1d0740580540380e458115024850954005001c101c00c02d41d484d03800241c0303901c25200740445c5c0c5a22070240d03941c03400c05507001404e55503016514501a0001c02c401c109080e00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 20788459 1250 20787209 20787223
    0xf071407080d1b0b010605030907091107030e150412230c010c0510050403030c020105100302010905010c1502040303030203061503090a151407020105070201060b13050409051207051b030f 82
    0x514038244200b40760010004900c80b4801c20f0040c07190f0020300020440e543c01102541c46a01c81c601100c0c0c00e16603441c440016507031403c04141c0241020004800801c0c403c8441404084020300f80d8540c0d00d0401011000d680d11581c030400251031580c90301d41c100801940552181000328400d0034200038841211070b103d5107001c4103a414050032801c070504210381400b01c1000e070560088100076030328150401130080c03d203c68560f0700551030480001c181400703050f03100381600e80680d07802c00c0c014200001510113107040003040c1d0f0783c0980041c24a003034001c21700007000550f00ca690007584030300f0440c007440982c03c000e444101058005004102c0c00400010700d4511041d000b1000302004421541820020120702c0b000c412032010030810091111303015040a809141d5588c002c000095a40928240a0003030a00c1e82d004402c0400c02040f0525042d041110f045020701d050329250407031440c002c00d01d80d215440448141d00322210b44d42050300704034070103501c42e40d00350080c004110b855211251035000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 20789709 1250 20788459 20788483
    0x6030f040201090b030408030103120206162001060305010204030b06010c0506130201031407020c13110301050907020102040503030a031406090103050d0f050408010c0504080105160507080c030d020f07140708 91
    0x116280025007076a1240d110400200303000426a940c1c0e0070203090128869000740800d50b050a46000042c0160303100240381440340c2c45c455515181c2c80c5468200303c07817103140f08102c240040c01c50f14000411040a20a110080d4864000144d41d0340c03039880c0640103800c00074065418000c00c0000324000c01e00c0070541d40d6001c280c6070314100b2030014510040e0020011078214002e80a0030004000840e50009940c2c9901a012103140481030b0000e400c4806861500017884036261090004018506014071010303001240c6000250900c0e1301c4002081c65904000d0380080080d840d011074105a084a83d100e94002c501940d0090081d030450b141c00741d0300c1043d110b044081080390341c48941040c2c4500151005032224a0003401200d941c0d400007000c68119005100e0103501e0305002c60146c14112507003145013074164445c40d040c0000350711010300340d800040c1e85201c2c6000402c100c0c80d882c81176100800d005050300c80e0464640c512401e0020380e0507484060149070750322000080c0140400081c210349010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 20790959 1250 20789709 20789731
    0x1061e020312010b03070201060902030601020a060504080706092301020405060304030f1e030903030b0904110d0309030503030a02071509050c120a0c080a032d03020711030a15060e04020603 83
    0x120418004078958420502092229518000041580f103980d034000c6000d021198024450320307803500000c0e0100c0c4801d42c0c0c3c041c050307400454050b000a1042d0040d030750150050408504094058903184e0a0300c0b1180710440704000c07520b5018008041920390340c0300710140031008509003170a1102040c5580b04c00782010b41070050074200c4600b0280300c0e000071000b214450700140481a0001030280240c15614000c41c08a801c103402c0701581d0400c036449a02c29500b001035040b0030846002840301180c851142038003009855140807000c80d00030001180541011040140e03175010038100b0007400700c0890081d640f403a040c00a140041503000441449101e400c43e0b6034a0701c010040d0b04070340342440383c0c80c008082c84030030600000d00034070104100e0001e500035165450140c21003216500c4411406407803c420018401c151401d480c4030b9406044518032403000401c5402d240f000080c5446007420742100e1301c01c90051000c507020012b00038200100070031b01d001515402c1950020f21180801041e02882d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 20792209 1250 20790959 20791007
    0x40305070312020702120c1c11010e0303070803071e02060f06090901150801020403020411040b03041b03050a05060712140115022409060709080309040b0f130203160201050106 77
    0x342e02c0e50448144a45c0108410b039601241038015480300c180120340c0d4480c6004c2c2048980f0505c80751011403905a103c00c08616100320040151610000121015010b220070321071040000c445600460290603d9298a540b52600e8104403441c4880c5402c03142c1150850800d0288180c907490442e5003100c012107036014199220040180100b000240308a001000c00c0000112840190f0003802500e00035a000d204541c0ca0310040380061007036204e06012b0650030000507000c285814050100e0388007401d0a140e07015525107031300d032415082203001e0740c881c0c201106021030580c000d014851000c0c03098500340280707601d14880d510031102c140705158900004865880d0f0312807082c803204100c9960625061521829503404200c0060100d4422203244629000b0400b00d902501c0034108580b4900001c40c03418000d0018071010b0b1601c01b44c0c45400400050480829540c0c1c5002890350400d080030041e220b1400c0340c6991a145071040b03145c01564034050050000f00d13444181402c145003813200000318 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 20793459 1250 20792209 20792237
    0x20a0b0405030c070617070c0503040303080402040906110306040c0206090a0206030a110a020a0c140d020402160c08010209010e040b090705072d0203010b040c0914060904090b0615030403050703 85
    0x794421070f82c861406004200e000703d2859080b55100b840541400e0882500e40c0c0c2c0c3d04410381e54202070641c09843e691040c482040040d00c40da650f0780d4440c0c400381010a401d249a5201016241c1e081c10200c1a036a02008115650801e88658802030308644000c02c0c0b5402d01040f442d440380701d0210041d0240c000000080c01c449c20a800c81c00046812017400d43e501e84500a00a440c0c001c414001c840090034030000142000c4401e0030b40e84445401451402111200c0d42040001c4d40403034481080807032383c64084400b05000084400040c2a40400560340c2c036600f4000402661109909500c42c61921005260740d840b071411056200e0b4850034080e07698451824040c2c1c3c5082020303400c59405001c8180081811111908165038610030360090080075410030402094500c103500b00b1000a02c41c074820800d801b0f049002c0001d2240140000f072400043c4c80c0802c0079508400002c0ea000c2c4900d50a0040c00e0410540812810803807065060940c2001e5900a2a9101c0e242000e002c0042e5407000c110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 20794709 1250 20793459 20793463
    0x40e0601260c180a0905010501091707051002010b09010b031b19030902010504030f0807030815010806040b0a0803031807080a030503240d0f03030510051302030702070b040b090916020a0b0405 84
    0x4103c1c0004100e03506840c0d0703c01028014010074090342d80007591030b8030700080d02c2c180403d003a00f8052104001d001001d00700000e1008001038000e251046648448508806480d100c0581d8085e002d8901c1003540e9161144076950070040c50794404a07404420006000c89100022007061403c400d0715002c40c005030640012980d41c0200e401c054489240220b000040201d008000d088040c0b1030b880f040c2d01503a600500d0000c18030f050781c3c403d02140581e40024010b1819a0210070b2501005100040d0180c907464803500e960000c03940c1101d0450440440601c1600c1001000000c10703850f001030075489a42c1d41c004050b800042c1143c11103040303401029000c0302580070200200200601001d00310760590500d8010a0080801507000c03d01d004081013a200c0802104401d441c00500205418001501c001e0000d50004051000f1806043d03004030b01403c040d0f00900080c1139040c0340e6507c44014004006011401400354181c1100003410f00c030803540c020865070030780c1e0340100d842c14003a076860071310718 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 20795959 1250 20794709 20794747
    0x3040609020a050a08010906140103050607080603030415050d0b060c070b0c07030b0c03070f03060f0e100e0106090e0a06050f090402030f010c0f08090d080f0703060b040e0601260c 79
    0x1c4c1d10030344104e4041410003055004c2c00c0c21500440d000c1c03103028060341c401d400801082c000540590040400100340c0340c02080840d801c03c01c042d00f26458a0b40d2043d03501003601d41e00c0c0c0502c00040c00050340c04001692401001d0500c0021a10503207444981c5040668441851044225800e40416120260071050050000941c2c2001c20440f10749004091443c41358412207046000c60304404940d12464840e1003100b0a03103032082880c1030703040d04049481c05000030007041644207035900c40021401840c21400c60380280710a840300400e40b420905605041e140040502210510f800010071050340c03810207890140c0700546020300c8646550020070b003410381c1c040c41c003c580e43c28842500e91041d880100050000c3c07060f507aa51450711a00501519584800c600e003001808550114a40d81c0600c089076411201c1404c0c001551961554081c0c11508283d019552800541c820402d4650704003d8000c0806c0c11160112101605076003d4107201c0740140c1040e8004a0110302e0b4503122505900f81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 20797209 1250 20795959 20795969
    0x601051f0807020307080301030602040504050a05011a0c0a1b06020706080f011a120114040c0e130b220c1106070918090804030602071412040306051033020a0803040609020a 76
    0x6c40d64941e120300309140650312901c02c40d401103140c0400110410652301c1900c1c140c0701f081111544240c4030500058254206414400c01400b80318031200020b81260064181c10541a2540f2380444c030342840a4103200d41a0301c1641800b0510040001c240c0c0c903100742a05480c01c9100007002c2076611202d03109103006407081c881c1064100381c00403800385c0101c44580c0c01a031045500b4051040308070300868689100545198000701e418007001900702c1a50005000c0388009044503498411058840e400c1580c11007004030029910120300d00015400b0621030072224811001300369505242400608030030392840360504940c00c6c901c0319482d1030300c2504914441e60704034081c280c883c0c1d12400c5c0031009600a200c21504c0114400400000610101d440d640e850070140b0114207007465612090040c2000500c0c900000800744804a0511080b10380c5002c46e0f4500c468004080d21b4205c1d0725a42c440c6048400340c25075214001510006410108899216030f000e540070840301118404140141015040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 20798459 1250 20797209 20797223
    0x312030e010507020f010c0e03121b1002030402030d0305010b091201020d1a090a06030305030c0703030609140402090105010203030105150d091406040b0f0c0301030f1a180601051f0807020307 84
    0x6000c3c4040d80018111040d004a000801120301e283e401602c02021707078200c2540503040030444140340108203000e4182c0307825540b06031202c00c40120900e410080c5241c4a1550b46078080b0a01c400d60504010440c1560500d007410003455050041074a910700034582c809100785d0410848205603035080d010349000c1c0031070040034008802c103150700070030701f003000104140604628000681c402d42c2901074482141d800d40c40c0d69103180c4505c8003008096000c503000f60107054542c032000558158074420160441000003040c151414588100200742c801030340000c1c110b40c0148010b00072980c03542407130340302d458803d800c060b616841c502d6840e02500328240c014040c002d084000c13445d41080400c602d0302c501d00c00d00f101006e84e0707038802240c200c41308140d844181c404001e02c01440000c0c88100424246c50080c001d0030300908081446901c21030044400e44408078000002c1a0301000422519001d0300d000c50301d400103c001d4081e141e00c1000c0308105d01d810800c95030013144005009104031980e0307a0704406 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 20799709 1250 20798459 20798461
    0x20a020301151d0c07020d1e03030905010507030c02030307050c0a08040609061101060f03020609010201020d0608010b0307060c020f040c17010303080615130e070509030609060108060903070c0312030e0105 90
    0x203590300c0e406030300d110b50004141d0b8840f0001d500c0e00d08007007291182d181d001010303052a0898003402482c1841c0c80e01240c8042c8100007210050802a00030103946109075404241c0035060720705a0b00351000a0714210515060000001090341c010017565440180c91070840c0d02e40c5017040701070385803035480d51000d0300110b400980841c5581d800024070041d6025505c601540410031b003521401c0350a80d210300781940d10071801c02d00040c41c0400092400d110140300150030000903480c00e1045541c660311402450b9501e40e042c0405003014000d802c010401401c01107150300a903000308120300400d5244c684501e5941884612843c01000000031900400e4094000e179030312844c0260041c0010b0301d9031841403092684291a00f940716045440f0b0920000251040c03500d4a80a00d007179410142c01503092002c1405580303150780701004010702c5460034074004c00c410352410342a01c0c01c00602070041c9210350010072801c808110b0344000b02045070761060707284407030b180b0248048001300400742c2d000d640b65003428 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 20800959 1250 20799709 20799731
    0x11407020607290c030406112203050601050a05010c060c0201110304050601030308010b03160e0307050607060603060507180e0901020904050106020105040302061807060c05030c030c0a0b010b0909060f01020a020301 94
    0x1245018010b1039800380b000b003422240c2e4214020b510844c0c030003601000c01c000203070000300660028800c00c400a00d1441c145807544100503c600c141c02e030103800d00c60315002c0c10805e000741006080d0061101b610b14450711410003000801e10010a000034200d61749401d84074881d0b0b80701b580301040c014200c240381901c034280b9103070080d2030f03500a100c15000105258004281c0f031803080102ca0041c0c001c00b0542050644540c81900e9078031103c059550305001c0d441000801e51030301401000700912130341c030010f00c1c20b0561802c0021680c01600342001c025910007081c5400345e07940c160b130f42500e8448100e0f00b483c5d03907035500442c0039208503040760b50058204000040d0050701500500e004030300c00d40a0b50f2081c0e54240c4001a40e2074200c0640700c241e80310b040108000ca012b074801201e0603000d0070a41e49800d502c02c06840c51a80301d10308900f0b59500a52204040c8405030040c1d6000d0700b0151203141c41c0402c0382000801d003641c098000d0384160803510f40590640c2c000c03c010720004e54050024000840d2079 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 20802209 1250 20800959 20800973
    0x20f04122102030306010c030c02030c130903081003020307120c05150304050c030d05030109110702060a0207061e0c0204020d0b030a0521251a0a02190503060906011407020607 77
    0x228181800988080d401e107105140040162440307441c040c0d403403150940003501c044508030132a1a090740c15020354050100039440701c910a800c00f0100c920301042c000482d2800130a4044010720900601c082840188012b82d40410103208070740b001c0c103da040c00c00d2581080d580848071940042d030300446407100c41c01c0c00428071001d50321130f9005405880d8180710013410b01d41c50351004100301e40061400c00041c005040c06502065000403600059810105607a02180b1654801145900541d110070020850560700082490755520031000c248020708201e00b000d4911000050300900c15600490000301603091a07101211603280201200c01169050070200c1c5c8030803541c0351469005441011503103520f50b5900407500c4070b9010580380c0c1080604010000c040c0303e00301004540c18001080070078a11001d050f0303900c7c01050b00e01001641c5003845d08100158600d09820581409020f02c10044181c1c0c902039010381c08513003801c0c11a40303400e005003641d485100d503c07002944a000458010f00f84000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 20803459 1250 20802209 20802233
    0x10503100504051c23090d2301020f040302100504080304030b06130c03140709030c09020708190908070f0b18061c02031f0302100e0f0a0605030a050a1b03020f0412 72
    0x1620403c2e4945e41c2c00c15a1020541c810a10520341050f1442e0101c00018400c000007400e101807507145440300d000b401409030990f4841c21011030424004141030040d840e00300d0141c00c0f04400d50800524052400061f55201c1c0103600c006440c0d20a010700040d50398651000f44503810320600000c2000000745000903006040d01504100c1e6071480500003420940035040d0303c82940e8118000c1d201c0c252034180c91038044d52100c027007240c0f8185c0c00e209040425142c110204022983c6072240f04c00c0c1c03410414910310b001c0d0700d940080c84042c8061820496511544101d414074106540260744110094000c00d103135220b00c040301e615407400398500d13031030344146a400785002d1a410701c1000030b41d04110b40d84141c40c051030b000c06035014900c903c41245060040240740500ea0024210520944c100e00002d0010840390b0f00403804548000200480d04a69101d00c65010003845e204006003c104003041800401c0c80c0e0310b840074158001920000781c80d040d0284c4000700302801c03400403407900a04e007040440350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 20804709 1250 20803459 20803487
    0x304030207090b03150a0914030d0b0312030f07091e051203310506070c060e03210d0204030b0106030c0f0801030206070206180a03120f08010503100504051c 69
    0x4511002c10075540601410302ca00742c00500624820802941300501c41c074001d8000101c2d5070352208940c001490202e58145010f100d40c025588400905640105907107450138018402c1e00140b2501d41140360841c10b50b60001410070007100e4554860909130f80e06510340d003118884c0d4881250854000c004448001c098410560ba038041c0164090880c0d5901e02503460103001c0500b00a0100541e0b4050007640c6001d20b420802c03401c1000d07514404105141d2004206603a004541340c2e0030305c491034201d0000c0c00031210543c010950469410413000700e15011034903110b005940040d50040101a03a01603c1c0950b402c4400b011442d60b40300400b1b0b0041090742e144202080156072000902401114207a04a94000e080c46181c035841d6800c01c61680d204808600b001c8405803104d8246458402d405e0001c2d51081d450f54800c00d00ca1280540a186082c86050401180a00601c069240070425448500b14040701003025150307490160b040101c45242e0b24081c0c004005603c1155600404c0c240f9118 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 20805959 1250 20804709 20804713
    0x91201060f12080a08091f020a080f040c15020a0501050f040203070506040303050301050402030a020408030a020a06060b04060e120c10170106030614010f030e07030602070209010501030504021005090a0312030203040302 96
    0x16601d424042c0c41d8000310001405607081408582d444d01e00900c80c0c9031340503010600343c4145151080b10b4106054004c01c582003441e50121342801000d0b040b4080e5500040c0c248851038042c5030540c1c0b003105076640c074000c600b6201c010060000d6100c5c02004a904440e03030100007070000d07182c03481d100c20b904a001c80301a446031141010000f03541c10024216026650140d586070f02d140c2c20b15081c080a54000742c00d07024019800c200008001406001030030229510394083c0614150906189094581c903400060041c4003c01c804c000e00c5e0780013401c04e0141c960507500041c000e10751882a40c104410741d000c043d040840007080701c0e0000d034070890740d107182e41415000d200283d803203510440458425010f0784600f405e03d024404401d40c0600540241180320386030100700d0758481c00c56241050a46e500444000b0f0300800d01508500e4a07001e000d01400003842d0410080c901030300040c1da030070005003100741440000034081d1410b445504200c40610781100488000074980a0300034001d5000b190260014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 20807209 1250 20805959 20805989
    0x70b040c0e040507031e020402041d091c140d020a090303080c040e04030e030f010c02010603140604030801050105180a03080a031a1f0306080607050405010206010e07050d050402040209120106 84
    0x740540d101d41c022604840204005821951140482010a6021000000036911000041c0d450b800140050003d01c10f08191008210a03101c1803840040e1641440b40c00c4006d20310380001e6665118406c3c03400a1408000a400d2035000341000c0c4508035000500e01d0000482000d881d030000c1c4060200c902c82d5613007a103d550f810405000c2400b07140141c00250303281901080c0401d210340818024400000c00750384003020306412282c00c45404484d482e0144c0d448000030424080007513a60b9001680c850081c01203031030144d50083c00e0807414050241840008101e2030b0f03441c103042c1540351a0040241280840b9926401d021030319400c158510030029040c80c2e0800c4901503149524040500f003c0c3c901000d0b5280040400d20003a1428180c80c00c140d03139003070000f03001e1004101440c05203c460311072170b0b50b460070100020709000c41600090030802610050012281c0d00000725034040b200c0341000a80b80c2c0b681d2001802910550f03812130ba000c00c03802078002059406601c10411100140c91403580 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 20808459 1250 20807209 20807219
    0x1080109060e01060f021c0206190203043f02010b041a030d050f0909040c030302010c020f03031302040207050a031d040c080604050403020f0a12021207050a020f04020d02070b040c 79
    0x341c6001c0e00030500e000450780d004103c41d601490010600f05000d00650f010380664103c0c1d002044100c804840059016500380f0120004284800e05903040300724055186207060b8481d207072209811802500200250342202c81e02c03507008044512610740d000e070208140f245144009000c0e25019100034844e500c0c10801403000fa100507a4510062400340c09403590ba0101d9200780c5a603000400e600007a1041040340710680e54450180c2c030b1107107204200c9441c1a50135410001c4c00c503500c1c0140e00c01550320014900c0014000041580da0180343c0c46c20034452802c0038070105000c1e0003000e0008016100d0690303241c1c109070300310b80000c0030142c0350a140b201071401d9004100c19640d41d61080720100e1100c8c804141c035030601d034102a92150003070040702c030003140c1c040709a8a03160309014180c03039403092141c40030303407060b81031004d0080b489901c001e190801c00161180350f15030f060301c1d60080c85420207134941c14040d00c8a4040c1d420b02030610740704540714060b90904c3e104281d03080798112014800442c2c0418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 20809709 1250 20808459 20808461
    0x9010e0a050f010c03030612050303041e03081305010207080a02011d0c0f010c050c0901030305030a0c0c0803011e170c0f0301050f060d0804090c0c050607140a0f0e06040f0501080109 80
    0x304a480040104040b0341c003400054650105010b01038003010744820b80807c0c040030b4040012002032051f802555285403a003810801c00c031440054021a051240b6450f0109505c000e5445e08003110303510000840a40d031401c0390092140710401071200320b01080c18a040d83d019881482483d600c0c408103010304044410054944c000a180c09a0249101c1704504040d4442c50000036114800c1048581c0f4407410130002d500b5950992044000890000401c454040d00340204580c070003043c1007101554541d039a8041c60707404140100c00c155071400c92025038080000e000394000b00b003054140c16122484d00400c0d602da0f1140e070709090285000e1800484070f81070511030103100e519039000302480ca449a004125440c20054401c0d5101c41c414400410607441701d220b1808201529141d90307404080c9454001c1c2440c0c002003181e8103004006a068500248181c101c41c240c0516180c07401e401101c940713003580d881015a902a801c90004103011400580c3c0350301c2c0100f0307140240c0304c1110760b0380d9501102c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 20810959 1250 20809709 20809729
    0x10b13050610032a050405030a060603021905030607140d0603030e12030301140409020a0812040f050321031806010806010618030317040f14010f0f09051c110a050309010e 75
    0xd11958420150640f12810340300c03080044c04000d01c1e00d81e10f882e0303503200000d1408160290550700310356503130170400861418a040d894000c441e15914400c50b407510002985882c00141108180200d0f12004001c84620f081183c4d051014107108000064481c00d005110036004c429503800340b5004c403101406840c002003a01d0403109204144c0d2480c4014806000241c03114200490700302d0954100890320b03100a00080382d5034100960b621ba2a81c0c40c1914035120080c065000f280640c00070000160b804070201c0c40400e10245401805940e5202c91489090080b24220410240d008001c00440c1001c0d0210740c180c100c46a0313580740824940b8074492643c0c8034016201c001c01044c80c01d0340010120280300c1c0308035402030088200014481c40c0c0e4482405103a200c0302d1050032659a900340c1ca41c0620580b0410010340c00d1200704022000443ea82c00d581c0d40494080c5811900262503016a6140b1500c01411082e5010091701e18900003468420b40c2ca4100040781030124900f10401400d6040001c141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 20812209 1250 20810959 20810981
    0x50706080c1b0c040c110a02060a02030408101a09040f030309150204080f0d02060606030103030305040303140c0715150b030a0f020a020f0601050105030601090e180d0903020108130807080309010b1305061003 91
    0x1801f01d069407a4204403081d4002d5224038154042400009505081484207488075555080c01281c0411f201405410b00610001080d114220050900c07001c20304002c084420184c0c11b080001e4001c2403401c141000346443c0c954084c1c164000a0041106100451f4250215210300c046500c070460a1506a8440004a90203500300800784010008030b0302c80d801964021307010b07060018013200c2082c149000000102c43c4000c102c0c000040c014104582c01d0b80b06000d25945210400404203100d0110145000c544200304107150302001068040e503466000442d460000710701156960110700c800707903c0c1e55001d07000707508900400c0c000150550080341240d1245005940e0000d40d94203140d0703c40c550f40c00190000b0340020303a0020062a1400c104403a0006007125100e0300000c91543c03000501000009160b407241c07404c0c0080a80000782c81c0f000340d40c01d0550190b00d00e500c2e5500c2081990041400a2049a001d200080401d5040300c055108500600342510131b0401d01040400580903a240c031104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 20813459 1250 20812209 20812213
    0x4020903030a1803170c06070201060b0a0f0315060e09010b070b040609050a0f05010510060e030a0b0415020d0207021e0904060b010c020d05010e19050706080c1b0c040c11 75
    0x3046149071140000c894007880d812501400e081d201c1d00c1703040510b5440004100b1035080098038184803a0f0401010341d010605100905c5410b050294070505401458204400e00c94001200f0207003500980207100f104405501043c2078a540d58402000c400c4200d10756030080b095040082080c8801c841241c1420740c01624000d01c40c8c5450792804021301034500141c0b07490042154200004ad080016030064601480c00407903282400144820b041c60194002d00911a240c014041035032400300340d40c82c54a40192425101d030b42d542c140613035041401d80c000d0110510018a00d10701c80c40650207040064000c0c0c0300f903401155124005c605100c044161154003c03c1c0400240018550b900709100065040c50816450700e200da011070038a034071003081104c01c0e07510b0b583c0c5007030b0102c02007060100d0400d907103060301464402c82d00c07007640b0741241c1c1c020541041100c200080c4002d210008859840c1019080b18555000c4582169102c0a078403010740d1059042c60344030015203105914881140c4100c0300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 20814709 1250 20813459 20813467
    0x105040b0114040e060a030605070f02010b0a05010903140c12030a030b060a1209020418060b040e03040b04060302030702010204031403030403020c041104140d0b0f040b0601020a0c170c060a021b0402090303 90
    0x4a64881341801000194060a8524080700103035040c040c1d03e000f64800c5d01c1d11894400e500c0d03400fa0030f540302c4150640c05038664401c1005030f613134404003800449070000300741176011810742709150030a2340b011912600494000200d00341e5000002c024500b665055508008528010041040d24403c4e05c0f00e00e00042c038801d41407181001c0f2940403200c0300e0b00c014000a0070708011802c55049041c0000140c8000d0f582c4d900450160820303020b80030381644910087c5160604042c441c1045014a004082c03c041d4040f000401e014004d504550285800c450f10300c030001c0c0c0b0049900d64a902c02c039812030040c052502050f480d42450301440c4901024003d64074101810301155640041030711180650050111104201144c2d428460364080d03003045007500c24515041c140803250550160205045500c4444102d0104a150b00c1080c1901c441080401c200c0d890460704900d00805846c0c100c2e8442d200050001d00c140d000200301c40485c1c81c1c50640c01c98214042c040104074000c01000ba601a00200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 20815959 1250 20814709 20814719
    0x6020619060e0105040e070e010f030b0c030c07030c110303040b03181606050901120e01020331020111030d0c121505030c04020906040308040602030406120b01020a030f0207031a0105040b011404 85
    0x50802d46007940c1140466400c3e030307612300c5865406c0a082c1d12403581c0c045515024001e0000140410350701420845280d80345051509030000c461040d510045c00704040b0503a46410840c003190200d0208400604481d01d070340c0c17504440e51407548207680044000d034210442d00c040303070000301f02c01075454901100050700900d4800181c134103503c41600141040a402c810301d030f2241e100e02c20004011402000145c82c1d260141c403180c0030940907140007100b01011410618214440060032034965820319205241180d16050103141d4051f0009040c92503003442c800c41211b80d40800982c0ca2448201070a200c0c0803108180641d10006c11f00920b5050303000040e01704610300302600140090700000d001949440d50300d49070344000d60040d400440041c3c00000d0100b20050748160003107002c8424030307802c000200c407030030003c2d640b001019002803c0c0024800054030340c5000380030030001103801084000d000d102d9030b0030075500d040003402002e02c220300c2d2070140d108d154400c409291801c1c00d05950149082e05103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 20817209 1250 20815959 20815961
    0xf06151e030604020427050309010807090b2a0f0d08150901030602030705041d060a051203030402010e0f060a02071a0c0d0806190306050a050105040c0e0603060a05040606020619060e010504 83
    0xe0a80791604040c02c110441c071b60004500d00c00503440c001e00c055a02c400c0c50100041079802c0107490301c1c1c20401d0201c0c0c21711020400404441720280d4504e000b60030380030b00c41190f0514600140c6c20468038001c0c070703061602018022420200c1c40d41030b61ba401c062036454003140801c0854105001d40c000807008010300004090783d0045400c83d6460800606047d941e40c4011208500b402d492440300ba5203a082c0000c03800c00706d1102d009890200c2d071410600c0c0f11101c3e62039680c08000e0019042208211180078141c0b92080312402030a40603000e245d580642480c041d40c5e0f501603118040d4240b0011124202540303c25050b1030401c00214068036146200b90001c507000d5802a04a940c0000801d03100440c249001e210380000b0361003120f0206441c58000128030031214141d2009000c2c1e424a00580e1070b055001c0340c840030841c01181da40c0d880343c5500020980900d400e4100707270b402034a401790204c0c4a03900010b10318030944503a0070401e044402800e218080e07a076640300e540c40301450741d40140401c0c540307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 20818459 1250 20817209 20817221
    0xf020a0f03020919030c03050105010501020a080a0305070903060f0e07090b0d200904060606030506030c030c010f110703030305190c09050d0602071203051008010510030204020c0f06151e0306040204 87
    0x10050000300c100b0b00402c4d295040102c030340d00440b004078440c2c2080003000b00c02e01440d40104424000350440c5030440c3c1356504113114602d6039604040e9601d000503495400b6540f184080c50700200c0c200300305602d90b5400700c000c04102d0fa0101c000c1c800d0440c0054404001c0c080d011070398a01902e07040107200140e444415a110001810900280da00b10030303092601ea0301c021910035401154041032551501c00041e04940340604407601079041310f078402c5880c1d20000b81a83c0c4660702841c198a03112650f00d42241d44164018250304107000700c1c0c4001003030542c50b410a80c0907504030880e2200c0b404100c07443d41c6c03c0f03c0c1d41c0d1840001146201604000e1460a41d02880f0317144e02441c8098507102140d40c0c0c9085071800741d00e490700801c0d956001d00c90303103a500d080c00401074801d4000800c01c5040c445450540d141842c88001c1c0304075000114041821000d12020034404c8540741111440d00708400c54191100c64410340300c1c01101c1d1b500d48080701d201c1003000707902c10101c060007034801521190203000c00303442 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 20819709 1250 20818459 20818477
    0x180603061e060c0d09030221151b070c0602010c0503040b042306040f140f0c0d030e03030a02030a080a14060f060423100503012d030b0a020d0f020a0f0302 68
    0xc1c2c24414005820820b0014100c001c04030741d1440381660952040102c05c06540030146000e610300382c0c0c651181e0b00001100d16a0055407070805545035213050344030341c04500000070040141e4011420340104001e920010040d50f46030b8000348000120341000311580d000440f006048103283c40003290119100030304201c0c03070074521400040044034819400f80351250564044a0343c0d08460a20340074803211071800748200400c02d0181c1304203503220380304c80d03582c0c0d0005604a224000014500301014000c000c4040c110720007900380ea44444280c400a17441ea0014100b02d4007140011001604480e00791062071105c8030500404100394856005000c251088003d4058011030204008100031a8030811a041c1100061030103040036220024412111b080c42c5408050042c28001885681e241c2c0102d40d040342000300041800341480ca405034800304103584050610009503090207041c514a0300140071500b0386040070701c1003e902c070441030201d00c0344c54070060014582e038500020303a40c07180d0018260ba00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 20820959 1250 20819709 20819719
    0x3030f05040f1401030f0b060a080603030d050c03011410050a0e0a030b0109090213050103030c02061303061a1008040507090209040603060c020105070f08070e0d060e0d05180603061e 80
    0x10b925003a40b002d012a00f50010741c0044030400c04400f103503a06004180303600c403e00c042800700304c54240200e0890700401030a101440442c07000102503460400650b42013441d8024107000d1810007142812855100307008180d424140b4514840460901502036446800186c1c1c0d43c501d01801140219009000c031400c043d0b01c03c102010020100f090043c4903406080400d400181c0c0401c584100486146103c421900d803600305001000031907082110440040e4041d212107a4a10380d960643c2400c0d181500001d149529001c00081080c040240401c624401990101201d211050b402e980052003110018040d601c06802800280c46503000b070804004050404221540c481d84c81c442a52404204c0d200181c3d90fa00400c01c4150740a40450034000903803c0100440c2400c000080545a9050525015040d0000341601b04070440c0d01209c044c89140341920f03000c8080190003040b5034440d001e40d09442042c0b00200600e86003280489009840040040b0b141e46095030010b4511108035640642c82 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 20822209 1250 20820959 20820967
    0x10b0f0d0603030e031506060304060207081209071401050c0c041a0d08030f01150903030509011e0e090106090f030f08070506010b09090f060d020409261201090507050403030f05 78
    0x1840c02402080041d502c030b0f03203030155464880420306291000b040403541002c502141031000e2900c9039400ca03504540c02900244c1c0c4c3d09101d04003500300384102d180c01c1c0200c01800040222242c00420440709a0305c002c0c0180c607102155600440352406980584d808903040350040500500d0558400b185854111000c1200c1203414000100070a40d480c0c401c1d0b405003000410011881101c9611602420302a601c0201c1d1488480b00104010080d010040c140040015080c1884c0e00900d18200b0440c80341d00c0380000d0400700040184184800503919000d04500e0001040e980d028040c100b007070b2286c054000c42d130710b49142c44170b07480d0134804d9805448800e0204000c101280c01480b4060103481b00e651150703580e0700400d0520804540041042c2028184101800303690741d54410840d00603038045070045164110340c10a940c07400707803503501e003651154203200206260060401810ba603814118a0500507a80c4000d240182d6504441c41030000e81c0410003400024000d015107d0300000502d082030130 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 20823459 1250 20822209 20822227
    0xc10030c021c021c0201020919060203030a020a09030c2301050301050f0d0c0f060203030106090e0103170304020f0405340807050705031c06030510060302130e030906070b09060903090603010b0f 85
    0x15007100340b5250b0060350000390788001409d200524000d0304019003107000c103003490020025260300010b0004290150005040c02c00c07244251000d0003e9a000a4180c201d9a13403820910602200d018154042001c076070301010040d030164003503904860001c0c03d18024030340440d0420448610703100007281d200100c20004104041d070101c1c000064140e903001140e40c0e504083c00540404c0399680f282d095082c8c000b00510001d45803101c0b500c0c07484443d003242912522240300083c40e40f10500c940582140c03608042046881c81c000d1100140404901d1007560745044040d41c400c000085101c41011440300d001241a85100e50700401110380100c050320704001207401c0b440c012a2450340d1a052140d212241030003404018820300e5440c1a094404200703103407459001c11510307079510444544003681e411443e0300c00e0030b00b84100d41201c00028030040e55120fa6151200350800290303800c4003d4401c1e00c000640c01c0c9400402c980350128020481400c50b86084c800304c80503803000c0c0c021900100e050000e960 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 20824709 1250 20823459 20823493
    0x5040903120e010b0901080109110d03020309090c09010e03030705031e04090e030304140c0f04020a0c0f0b0421050f090a0509070201060321050f03090109140c10030c021c02 76
    0x14030300400400100f02004000100045c03004180c01c4860241d141906000005410010800458105440301c2c0c02c06c00d03032030070160308500a001200e6000b4100404108178406020010032401d40c003621040e841058a40900d0b41d41e00548000a0655208001e044280d486c00482e02d455a10b01d48006860240c907041d041068600080385413400303505c080144001c102040c205400111442c1c402020141d845200040c01c9083c40751401d4002d0750300041c0843c000748100725009041e60080d0742d90074028014680960301c8070302106c1c00d4400006000414207011504101c41d903190314140e07985030500c070b05864403012036070064040540c003020003080060282c94002d402449090560000621203141d410044902e4030521100401c0501c0107442100403600042642e51059001781041d880c0d540b4035843d10300400c0c0954000e030419244181e90b490004000503030280d4504103130307800240301d004a14250150b1b10307002c8261b8090307082540036081002c60000b51310030048042c03049038602551000d8103a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 20825959 1250 20824709 20824721
    0x40603020303070c0602010f0b030c010c0201030f1107050705040c05030103060203060409020918060603011107060f0b04020316020d05070206091027030b0c030906010303080a0e030a090501081f0504090312 90
    0x1e0300c1c481c4c000410061541c0a105108800c403101d20f003408a4101c5600003900d4400200401d41401151000d01d001c6d64425031101000040202d000c108100079400c8846003a041031038111098031607160081001d0619000da050b0344106500c0799800e42e425980c9440294000034282a0800c4d81c0e5464003001d41c2d0340c00784403401002407612100414064034000d5003004402000a402030307040c03812140e0b0005041c412144c0440d00903000041c08000e90800902070410b07880400e030700a0020061060000c0040b101106452250302101c2e4011342d00002941d580c0990b040c06503121405200d0f47d2980c2c107141c6030f003410b01c4000c0d1414801d00c1c90403280c03510b03000c012501c2c1d551a0200340902401000700401000d6040b16034080e01c9420740c41c0034554240d40b0041400004c0400a200d4081261074121390002e0191044200a50740c445c0c00403000200a1042481401d000420440c0881e01c100031043c0d4100d5101104511808031f1418401440003511a80d17804904002d01c8000503c0b40d000340348981 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 20827209 1250 20825959 20825963
    0x1410030207050115091d03090d030306030f05150906060f040b1906032f0a0c0c08060f04030905060c0a060b060405060f03040b1e070315051002010c02010507020d0c0f0204060302030307 81
    0xc4d0032050600b05a202180e00c441104008010194a10310450400005a1301034050884d58402184a64981200586010b1f03000038080455a50948108075010800502c584840c040c1c002c0556180c3c0d1101c0d50f6000261400c13a003107000112880c0301c41c10140c00018100e9409000801e02034090b207410900403642c0c0d4040d800081c4c2d542c2d1114021103c20880160100460010580d40803140b8220314240c4546e030740360818072400d40302d0707241041200300c004c800900041060315101c0c501100f004592020481c0d0031800140340180110700d1b40380010a0358803c11b012001880200240d075504801050030040085d40840240b1001415980b980020400030b00a80342c07040d220306092421a01e501e80240030583d00389141840e130300d80d624103040e82c19840b040c2450041001c00040003141070319000f542100e50001c01c07002241e0380194054120800a041070b070300070050340d40c82c800100d0f100d01081d601840001c00510102d80443c08038001c01c100c1c01c0c0000d200203481d56583c2d00082c556888a41e00b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 20828459 1250 20827209 20827241
    0x30603020f0301060303081305070f0b030405060604061202011419020a020f060a051608120405030309070501020706050a05030907081903020705041b03050711030a03091b14100302070501 82
    0x5108505191000c0703140a030007078000303110311429a90040c18110000b00360703121484c1c20200b12000d01c002041540c00030b181110314140c2c202c0d290890100c05920840f01030b1581c0c428040400c0b00d90500d80710301012107480d1100340366607500039401150f09040848000742c10400500860300c0310720360004240c4e00410140c0040240d00d40910500c01d4200e0281d0071144200b02c14091054500c0d001001c50b00c19800070003c5444032103a40c40c01e54814000e8906020301401e02c030041000b0018000020350041c010348084407412030b901c100481c0c1e101258060740c00014010f0061092841c0a80040c581002000d0203071070300c03941c4074420985815501d07030110142c0c01d022621788042c55010302000e405048242c0e414080241007900000035800c0100c0c5035002c044d03588000400c4a44640b11003603031020101d003625950222140020050300440c034041d0385070340d1100704280d010b9145950000c00c441d00081350030401c0c0f5166081005078041000882c05068003005403a001a03c28400c419658142090b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 20829709 1250 20828459 20828471
    0x9240b0a0201201c0212070c050c030703052a10021608010605010203040e0601202802090708090f0303070906080c0c0a0b0601052106010201150617040201051903 71
    0x80c00e442108120902d52a400c01c00700b01c445000c80b00701e4203001040720b001d807610003121040138002e00c15403804203a902141c1c8140301100d980450710b1240e15000340d080316000100c03d0105912a40584001480380d4040100000040c2800381d07800341e8030341d5440713040201c42c0a500c0400c020911304c1d0100001a0411203a070511804034640d400701911000d4020080103041c040081d56a101703034080c0035400c050243c0021290385c401c03052080c01070f9078000c0040c0755072a80c50b181e0355945010b0428400c002886000003051343e0358840800381c1942c00600d0351405803907580068a0f4840047c01000050040824100b100303030f0100000c5000726225510051101d1414200a00101000e00f90000f6030104201181c820140000c507c00740d980c01c482c1c1240d840e00d851005a4031403003000010b0403030210b14500f0f0254200e185403450700c0b8440a800038841d428001086900228940c0640c8000c220034040000381032080c0c41c1c4440d403151060610703600d40100b07402494400303440d4411200019803600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 20830959 1250 20829709 20829727
    0x14011104030615060f0806090a020903031c0f14041101020c0603090c01090b04050915040209030106030b0402030c04050c0a03020a03150305060421050a0503040c030204060305160f06080109240b 85
    0x840b0702c00044c102071501c00801d02c00407400501c0c40c607010344079612520303a41c3c5c003083c4464aa98102d0380d01e4140181100c1e500e408081840452101c07200c407410b80c0030300e44500c00c842a07607540101800307850402c90b174803003594669a64080d50040801914114822030024648644130f00000b14052200c101c0103003c49001075000403c510600e40000c86844000c6c04100400d0301c600c904c00b41c1000b9161058a4400d58403070100d002400742c1c6000c2e590542c00c000c8008240010300750154043c0c2d00039800d40c0ca10150000078401510010380d0078070303c0c084007003200045081c46540548034a440600c1d02017000c1c07208009030424001b464205980b1500a0b50602041141c61006d0300701040c0300b0b00b184d0203043ca505101509c4c0707000740c0c9840d0083c45030000004003001840c82283c405150f00130010080203440f824620360302c0100c41c400700b0403254484408034188581d82c01340342c111081548c9180140e030030b004040010744a81450990a4003a030f20107072400909400741200502150203105484000b40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 20832209 1250 20830959 20830991
    0x1030c0f06020316060c030b09070c0b09010b0a05090405010b04060b03070215100501031d0601090e120c690c090601090f12030f0305060d140111040306 67
    0x194840829540f0820814040d64101540300725104d800030300015007500e18510681c084d2081a006661190246040007078150b00110104411802400d80880325926064402d080302d003882c01e040c0d170045501d5003c2100c2e1070590050f03a0b000344108000f14001c03904001060039a062a0000b0124080c044101b1100681c1049000001c050701ea004406034107154194000080090003060704040d01c500101c03049100d400f030440680c9809504030b550ba0746c1c0d261009402010780700503289050090350803000b01e100c10a000c1ea090b904000e40607020035080c02540b0601056030304590802a04800c1c00d01c0344032030007010100c210516880c41c02072690407d414424000c1268000e1286110521300d1540150b0400a4209031a89003941c0949494039001c0060310a014960f0054100d05003503000803c08042000c0301c1c0741118840e40b100302200c0b1074407605030705546003110b80036048a04024044041a40283c0c50f0f1551540301000041548000d880c1826035406500183d840a465440554802c001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 20833459 1250 20832209 20832239
    0x906030317040308041707140102070314030906160c06090302010902010e0d08070611120a0902131b1409060d090c0e070516051005070806031203010b09060f040b0301030c 75
    0xd600881e1050702c1c0c540da01801c20f90f40540064800f80319814007101448000084580d11600085c18010a51000e00c8c628045d5104030400c8000039030300c0300041440000c00007543e0080c2c280714040d050a94a400a4101c00a20078003080204400d070000040810494461810f00034065400031a0041c00c90001600c00784400c406a0700422650700014045092a41507610b540c0d80884045804d04400201c981ca42c018110030021000404083c003c80440513800440581d1081d55090703e807a0120601c0411503071a00c0251110046070f010400c0c201d031190900c100c3d40400380d0411401c0800c00780c04030358550000207480032b589941e03543c98001d1155408442006100400c04101c00b80b606081c01440c0c0d000c1c00060040e10780c5048440c03000c028040c4118151500050010045440d00160081880301c00f0b86103035001e8081c50003014881d03070705002120f044c0da02d0300154626010100c818000d40342d0020603603081801c0103220128460341c070907009500841c00360400182440c10030604002c0b51030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 20834709 1250 20833459 20833487
    0x130812160e010f03020306030304050a0e1509060603160924020124030f170703050d0c020109110d02040204080102040902090a06050418020c030702120f010605030105150907050d050109060303 84
    0x20400d00110740e50b03a206807410f030094201e150168407030301c51030003191030741c05150001c5510014400003c1810b0490720740940c0300d111401e00760569450f00c01d05014103d4010340303400e41c0148082000030701c0b10010702c072111074417030803440c1050043d5aa4818046d020f4050034a100722030603a0681d10349120703824040c10000490411030f00340311074102015a00b41840e148001461072030904050424480329030b04064410991220290351656645802401d55201c0340c0c0049400e4a0043c55136210b900c140300f06009c40da401646c20001d0301f000c1c010050780c000044c1c400c07a84190204008036040e5404c0c0041d1000301011580540c40e170b0002020024500a0354224100b01b020900041144658a104c1c40000c40109800182d9413918405e40174190b00c5000c9000c5d40000380c003154a10340758170004041b020580301d90000c000507900c0c0c100301400d85005950002d034a00140b0110281443c085603515000326150900e41c0c5020401178080301a210b099110b9444e0300d40d240f108206064010700445030741c030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 20835959 1250 20834709 20834717
    0xc051005040f0303030b01020f07060305010317070b01060e040905010204091508060c030106030b01030906150f0b1201051c0b010303050d0518100b0301021c060807060c020904060513081216 83
    0x2070030803400c0c2d44400880d101c060201902c03840e5400140e40207000e20620901e010702541c88181d2901e8020b0080c080070b220403251200d04040c0c01400c50800c0c4266480c880e448040030055910707004046070802d445a99144c2d20690b02d4100100181092002f00001c0c0001f03070022400c0740704901c5e000700200e045c0d40064680c0e003002d803c0200100ca4081142e06481e07050400041c89444075004070010b00a140d002072a5620700402191550401186a03080301c0c000070350b00e01c0300d0307444680c0e81400740244072903c000030b00300b400140194580b4072041c0320040604004100300c40050b072600c048050302a4402d5005c10000506c2107000c00d46801010352180c100416401100b8260541c50360341d008280b49034103007581c1d40800000596080d01103070b21300c0c0111032030100d04000100d800b4009028030700c900f803840d2084d076030000361030303800303092300d002042d40003482d003c0c4030756031a00d40a002d0903000703200c841d10131054210341c000140c0d1240a00154421030340140414603202c2820300c206841c0000180c144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 20837209 1250 20835959 20835967
    0xa05040b04060504030c0602040305010203060a090b010c020112020903071508070c240609020f0c011508060c0f0f0a05090103050a060803030705070303060b070f020907210203130506040c051005 85
    0x1190503040c8041c1c116500580002d183c2d5910705044400028455004046500008002041c001c0540286009070411554511143e5a41c0c90070412076880b0000c4601081590305050003660041c4010465680180c0000d45080d854500280c1803100319000340f110b01102c1964182e01300e0344500c28030307030010340707070504c469800c0080c1c513840284101b6a05040114110f085101c031082ca0305e4004500405092206644a541d150072500c020780203d44400b03569841e100c03c0c00e040d8946801aa81228209000b403c8161124030142c10103511145110700310038020084116010480001007200c901c0a9641540b81c0c09480300050030381d54003600b00d28909080180611000e440070040b81d0300103185007400c0f03944610624040d4094051940080c000d80c0c004070b0100244107aa56900d50054802c540c0c1e02e043d90390720103090b00c0c00c000051801f42e10345103a040d0000110159401103400080304260300030308004030356940303181c10f00c1110304480030038400d00f040000d414408041c001c44c056a061603420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 20838459 1250 20837209 20837213
    0x1509090b090105040f240612091203090201090305030a090302090109090201020c040f29041d060105011d130e0f0123070c0b010e0403090504060510030509030906130306050a0504 78
    0x30503818050107101e20360326507500026152552085909071102c040c400074101000000350f06d803800740d20461000c16400d1011917003519061044001c026401680d4048034251040110b00508221608a0610132181004004640c0070806820304451581d07a160390181144180002c05006a1080b191542002c16000040c0c1e00800c0417003103040199000104118481d02000244c40201901d09140e10640d01c0407031188492404c50100180c242c805220b217442043c040001c914400f040c0d0f03d000e410400c0103001c507611454082c07401800c002521024500141e00089541c9400c840c0d0900305a034660034555800b605018401c4c0002190000700400e05c031724036428417070000c125619195100d0300d1001940c00342c02462400c04898000361010040d42c2c4401420744090300c00c0e5010350200d107150900064901d09401100280d91005e003582c900000a1042a406800060104105070009106c2029142c4510000e0007078021020005aa424035608007042112400f4040c0309066081c0820040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 20839709 1250 20838459 20838469
    0x160c0201080403030c0e0a060507020f030309010c0f0204110a020604030e010504050f0105090315070f08060a061704050c130209090105180103080304050a05060c030f070906080a15050402041509090b 87
    0x940b10b90142070200f420005030108031015815500f0744c2da803205c0603000c08600305603c0405442000d2013030b10b028215040b0f6408040d601d002d546601e0303000074900381454002135641012201228405800403075408499201c0410a40000503d600164840350070030050581c800301c0c4060040c0d00b802c0913450141880c0c041014034111240d00e5060003000a0464105d072420003605083d8107042d4840741d540d08104100402c041e80400340390001a918078040780051400c07240c0311040340d030191102d00641040b45050710700d405004209803040d00800140b007509850300040d5000e4001000001030b0780300040700230062a1901a00554060410074510585020340510305d1410f40780c000f00007a46995079450858034107081d8040060190007148284401512a000a5405450480ea20204d00e0380c440c5001c40301c88502e13110b038400144024001c1150050140d03c000401901c1210501c00b0588074008034080c1d07446540003000301000405000f80d4544c0c003000c2d11010746001071f001c4c0414031403800056 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 20840959 1250 20839709 20839711
    0x130606050d090512071101180e16050c0f070603060801050105030307030507050709060f0f050402071a07020c030f1e03160303020a0c02090411010e040209010203040306050606130806160c020108 85
    0x641642d90360850442444020448450700c03204003401c0d250743c0d041300e180c03459424542c80078043c041032424254440307842d00d452584064610340707448032015a42c0d1040c0c54a91511007116501441001c01123400145414404000d0000e0b8420052924a180c91002400c0f607240c4d034080d4030140d16080040c0130b981e50100c00c54000640515040e511b910f036034108242030030303545d500c130b550080e107050400186c9044e60880c2000329000030b10720040442d43d400510060703100b40000140070030780401c0e8885a07034881806403500110944100c45c2c08040b0080440d00d031480184040519902114030f03102c2c40c60f029401000740c850340d0405581001c00807413004040c5200c0100c02401c0c55004105580800d20502d686c42e6020740060842b0700c1030070103090070105508514000e9000408a00c0c2c1c8001c42c1c1414004c0302d0145806074011481c00b880d6882d400d00a21000d0301311a4442c00802a20020355103448050000e0b00900380901424285400020700c3c2d4089000751405009251f0030040140c0c1c0c0000722a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 20842209 1250 20840959 20840977
    0x10f020c09060402040b03071116030308071103040801020c010e060106020f120c010b1c020406050105030118020f09031509150105090c030a0b04020a050702090105090c030121020a1413060605 84
    0x41d0703807500340008000e4056500000b00c0380070007000700301116a010380d02c03018411040095694500c40642c00501c26001c80c00081c1c0811080030101700c41c40d2150101500e000702100030b4900b004d45540805080e03078410346101003160f440e2b42c0d02c0002d01000303008070b44c01807242e400106082d05022410580310004616288480400070801a4074803e0a42245500c98002404110394108014900c01c0381082664103070700852800c0c20209640d4011021030381601c01710a03052100300308604041c0042d40c00764862100303065040c03203c05500c0e1010004c09500080390f031103101e01441d0228100f0715000d422401c2c240707190a4040104074a48400c200c0c0b40d00941c6428025503070340d40c1c020715500505901204103810910014020107081e40c018041c0807035a208884620b800d903601c908110310f414054803c4421042d0402c010008201121612241401d0644034901c40650540000e503240307540d580b10040c403030202c03070b241c031914508506900c3c02d4142c4c2c810104199400c110b4001c140703000c1d440c08 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 20843459 1250 20842209 20842219
    0x3060102061303020f0a03080108061b18010504080102120402030d080403120e011e0c02070e0105030d050a1b060207060605040207150c020304050d0507050a080f0606040c1209030914010f020c 84
    0x102d5000e0501c00e001d00c80c04080084100c1c1c243c80082c0c5002403042c00244100c5040b400b400001c580d0341303a00107400c418600c42101216062200a410b611044400115498144041000001040c12081c00603024071024408102480d01e0b042c01451309004142c1d0584080000000410000035005580800c11808c1075100241d00c000f06842180102072011010710031480c2c0c0030112041038074580020030807081660a407140a9030b00c04d49022280f0b402c1c003416505401a0440390341852062014240b41e0602d49800d0091802600f441060070080d4801541c665800198400900249004000040000f6542103103455076540b0381200b00e0a012a40c000c2403502c442c14240614400c00a0314042d00300180b40b0416550f040c90841d42d110100d00c19207005550382d032400602c4e19404983c001031440340304050200f0755155400c000041c661543c0080038000c020141d603520142500c5483c05241c0f080c2c65080201e03007003062042603611500c200c6070400200244081401c2d50201d107039084d102d001e4030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 20844709 1250 20843459 20843491
    0x306050402040f02031302030706020705010210020a0302090904050c010305010e040f11040605030f03070b0708010303020714030a06020406080a05060a05030a0308060409050102070c1d0411060307020c031b0103060b0306010206 99
    0x20018010f020543c641c104910300100502030030390a071100c42075200d442102200c003415030301d10040e82c03238118600c41d03580540c000c03089010424913641c00500102c4014030b40146060f0803400015104007055a050fa0183e2124821550658051040740d01400301000c004000c0d00d09a61071075a901f003489001044501c42c10340229041c0c846400034005050002d090f1481c0ca0715021011f5940e810003034054401201e19804204068003c0c5540d5042e03a8141e80a000ca0904003207601c005549d500201c60b42510610041d00f01050103403014001800c00d039941d108540c140764506005465002c1d0400c1e200380a00541003216640010304aa4416450f0404215903a103c0700050b0003040d0000c0b01400c154000190081002890780c40c640645260069009804103010032181008400322401090000303008a00030062800038051640061303944101c48501000c10f01080c10034409447c1341c400c0c0c0d0040d0210100c1d9603014010000902002801142103141210000b075039460302410300c41c0c2c2d83c0302440d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 20845959 1250 20844709 20844713
    0x30e0a05060c0702040b0d1a1e0705030411041a120307060501090506030d170411030319020318010507020d03030b13090812070c02010906051b060f07030e0609060103060504 76
    0x405219449a0020151001441d0021819106034401c5004900c21440d118480b103c82c41c08102c031051580e0042d084100318110a000b60f41c00c040c0152030002001c4001c0e0303e00580e130400260152195001b1b5984c0c60b101c4c142480d04101421202d14024401c030705080c0b50400f03007505a80310b0350710742c0ea0485801600c01c1c24400e00314203520801102030007441c00c00e400803a1003103080d0091405a8801d4040b80c1c846040d01a04481d020711801510280441c1140820041024000c4402d40780c6401020f036403800d03841006880d100d41c100e210f1240540c001040d0224150315082d1408000602804e0940c42c0c548503900058080d041104014245582c0740160740c1161501c0c03c0c82d903084001c1007400c000322000e5041c01300d400c0d0400c2c101c4002c0040030300c000415a80c17041410444541d81030b114041c915041c0300c4180d40c1da400c002d1010320200c503643c08011400c8020403202d07001c0c08103a4007142a0b414409001030a84011031311000c480d030300c200c0510005050010f26181129040100092161914 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 20847209 1250 20845959 20845963
    0x5060d021503071202030405070821030412050f0703020607031a090c0d020708070b010807060509030d080c132c010e0705070503121f0504110403020d0606030c06050307090b040b0406030e 82
    0xb0000e88400d413171000c8100010454001400b83c25254040708440300c00e040d0030040b56a03894548009244844140080340c0010500040c10604018a0400c107061010308811485aa0840b61060740107910040c20701460f1a05481604128400401e8480702c00100307a002c58403030305c03000e0b01860030302d02c000418810f034203665415141943d5009544660745ca14a0a1903941d080c001e00940c403080c018140c00050283c05001180c40c0984054060904c0c009943d50580b0345500090a100d12800300704a04c651085101d910340c005024890701c100c2503403684c100180b0542e004031020002400302c61005105009a1000d42540103200d0314181c0e81c0c80d1020b190850540c080c9040100ca0340301c134802441500e080b40c52100c9915040d0041c109500c80e6200104015955000303181241444c00704400d001600340f90024441c018092640840c055030b0b00c4d80c5000341004d041c0d1003c000244040b06014959a201c1114402002d1f104a07a03410b150400f503600c1e101d44100d21500040c10f40d20284c4410440c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 20848459 1250 20847209 20847227
    0x50106021b210f0601060507170310030602030a061a13050913020307060e0102010b040911010302090d14010c0807050a020c1201090c0906090e0f060f040c0801020a0309020405060d02150307 83
    0x4a40c0d214a0011a064075940c3c45140f40c4071001c0501401c4000b1034903500c918107a9403455000404060300c0e41d5124a0010726a201400752001c010032a08040080b4407135000441c014040e1000008600f840c004901c1a5404402d01d84400c0c0f00e401c006010710b0388002c00c003000503141c0c125100a0991a104002c507203604403110000d405003c1c4003030002d8556000300d00090704920030b030003e01508802d40100011140e11140050410280c072101c2e07080c03035210b6400703065000000380801103818900e403161080d0406d103050f1058076039142c14202481a031300c80c0c06942c100c559410041c2c01c01d5032030003010b9181d0301c082d41c840d03004158a10701d00c04440b809401c8882017640119800c0c5816490303014403009080240103407400f060a2010205607460006010500d81208170b0103459203031140d441d10b08100002074001e4030b41044040000c1240c16081c4000c1c00c17a412075850004000c2c2030703407050106884005006c0c51041034010505000740c0c840e04041d04809160b0b00c00603a582e9a03094069a969031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 20849709 1250 20848459 20848489
    0x209060603181002090108220605100503010603050303160801270216050d0f020706080a050604020f040806060901090e0a06090303021e0304021e030a0f05120a0305160201050106021b 80
    0x403c1c078401034000d041070f03030013400f07001020307030b81e0384141e9403690503607070a6070b91440001c9481400c44d1244004a801d0b640042d030000c1ca4010b00361501d0f991100043e0949149410a6405400020a1140050303c19504400410480c1468201c0d0362504a440d46c509240d2480d090b242e140940a250614403658102d90040c124a041002501c0541c00d0440e80e95a04070607003c0441c5101c080303002050700018582d001c44556584400060783c0303003c80d5402a04024000f80d82060302030004400b07000454028001900718000201146d14001003086401241a44000b446628103444a4041000840c0e000e10726904402c0101d00c05080b171404070300071301c10000100704a401d069614149600804002d60189000f2a81c0e10301e41e0407480c46131400c6409140030940e00d607208050700000103010400c6082224010016980c1218160380b41a0140e8130440070003001075620b904001c894030500300d1403c42d100b0b4034402005203604140c0040d41e214118461800a481708218140d100c0d074403800c4607a1406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 20850959 1250 20849709 20849713
    0x2d0e06070b0f0109050907030f0203070305010204061101050a0b0604060302090111030c010f0e010b010e01140c060a09031205091b130903020307020109060e09040305070305120103200d020906060318 87
    0x1040d0304003203440d110152980c1d400c06001c070000003000078440c040c03140105081c00c00740c09250724542e42c4509059042c0c000301e805006140000011503c20720140c4018039180d1a40e6240c00c054034105421035500070b1114156a01d00b803424102c544898050340c040e9042410010b030f03a190b88500503105006c039802c205c0a0340c48001146072582d0419003141e03c11503016a400c0c001d0301034501300b00303007a6503601d90b1140c00104120b201014940c0300e0ba4400d0075045a07254960b20300703408051090300f410b02c1101c3e181001030301c40c607100702010b51050f2001d81303203821178104201904005112644554203c041403210441c4000000f1055413242c00b0403c0e18180c05208101c000c50b10320740652079800510040e0b0104850210002d1194020b9820300c1e0341d00d0004100502c540c0c1c03155030940346500142c5043e0700b08281401842d044d0580c41d0601c9001c0c60013407801001c86800b001c3e1b2003448075200500d480c0201d0f00c0d12441d80060322064040c641100e4100c500c2d603102d41c1c4100140852540840c82c40f4518 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 20852209 1250 20850959 20850967
    0x30403030809011506050d0c0309050307020120100b010807050a080c210a05011a0307020303011203120e0c040e010e030304060911130f050a050103030203070f050133062d0e06 77
    0x2050308a0010b08154007130720781c24040081e50302016030450f84150808bc001d078100b0007090005620038091440c0aa905403041519102c0d0b102c1d44034a04007004140101c1650f940460024540e044030107590f01140301e20b803080c41c0c40c1188400400b01c0b04007511001180e040460102d00b180381c6010068030800780c0050f480724a1400e20001e0010340030038443c2001d01c500325000b9240310300419085903c6038041e6001985140d203801100790700401e02050940c06c0001c600410103800c0060700400003000002300c000c05040070032a003044102c0e00c20044a404036803508413807040054010090765445500241b0000300c040060811008010702854044e501c0490744040c0c10b501c4002d82d1081c44010b02c2080e040002d9035440d40310703004843c82804017a002d42e00500061000480800149981e648210000304521032a0108a2070054801803034031004600c1200e07542888420b15424001004a03160030545511410b1070018003070701102050007050003004603141c1e0300780904001a60404090b00d501c0e40c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 20853459 1250 20852209 20852219
    0x60609030a110a0801060608150a030c060e011103160b040206070b07020303041502030c070204200301090b0306060321030718060302040e06030a020906040e010f02030a020705070b0304050304030308090115 90
    0x3800b8148281c40c0b140158030000b00d001c4005115100c00d6800c01c0d140c081d4940c803004800c80341c60409081c020f60200712500d0100c0095420b82210009160039118610721044400000d03080b100c1082031440383e43d0080c402d40701e58441003880c50740e440d90011026010303a100c3d40003040d40d9218502024140703050b4001801039a13540040150311481c061044a0341d0f800820300c0c45d00503888156010001d40d60140260000b61a142d405084138600701d8008070700c5000c00c00d0400c01c1a810036441704c2d0490b6503411005215040038041d05501c408200c0c0a840302c0c002d217107514410200351800299019201000180e80c450140804020741c1c1800401554903550703610703006003c0e5225001f051030640208020503900d080000e19844030607801491103401d59504810302000345621140c4800d88d40d04d030b0b046c05058642d640700030b5024070700c0500050394580050138031501d030001c030b0f40c40700807002c2c0d0070010070001c601c1c00b01c107503030944e41c1c1843c0030a4217850300582c0038050000c64102901040c603031000011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 20854709 1250 20853459 20853473
    0x130203340e0702060709180c0e0405041b0b090901060e0613030809040609020307081506040e0109060305010e030a081909051006090e010902060d02131701050604060509070c020108060609030a 84
    0x100c10302c055800c4460580e00ca29007140d207003a56214070064288509510198045603820017100c0b000c0c9868402c0d40121580f002070b080c0c03041540d0503241c1d5031a080c84000c0d49483c82008d100905007007445e051400540402003180c559051013814100240a4a03904481e5100c00c01c4502640c8551440350b075035512410202c4031584460989031043c0d00d81100003a90b8803540c000c0d00c1c850f0519855a100a0b136174211500b110076040709101c0d50045040001082d650311003000340b4080c04402c200061242c3c21458074500315518180a41c1c016482840480c0c202980040c903d94482088403900e10103e40c403403078290250616001c004c0141c002c074a4908880049540300c00d00301c4504640505c4140314410358a0b00f00d4410300d4000c0e402107403c00c01c4103d07040c0c80d900101483c0310030b242b600c0c0c10b540d91201a07134034829a441c01644265101c0080c414145064040d010190108580095003403d2005000d004003d803e900233060040b014000340542e995001a1540c00d10007030700b0b443e689483d5140c908 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 20855959 1250 20854709 20854711
    0x10602010e0606090106020c0112150902040815060d030c0501090b090d09090501050d0f1703131709090105040504030327031d01080c0d0204080106030605010e130203340e 75
    0x807500c50750001581070701d0007001c0d440c122002500948440e0440100440b00c0e050040514000c0c96100c50050129008440047c40201255240141c585080c0341201e0704102c8a4580e201110f81001c043c002c080d982c0008010042d941820013071041450340c03602c00c0c090160403c000c0d054800a0b0100520a003022030501c1c00144181ea441001c9920b54000700215002030155541002c80300300e0060001d800040e501c418203004201c1c0d0302c20300321070020050860f030045074440b920b50401071040d03007081030034001200c400040728240b40c108401e041c041150910148100303880346480c0c4010030203046c000e80c0140c0c0d84440e298040c43c11700c8107407981704500d90303030070300040300014240900041844401c104821480c0c0050356001c04640704c6032500e004a03005008480c0d40c4550811000075903580c2445910001c2d4072901c00410036600d029100788130508020180c008680c022850400180c4d004030701e1901110050a031700408140c0da210b180c4841c0000607070b14102c00c1160501048501d0514559 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 20857209 1250 20855959 20855981
    0x4210f030e0604031b020607050a0c0609090506010e060d02130611150906060f190f1805190f020919030606060f1d12011419150e07030603080301060201 67
    0x284103410114003074a90302ca40494010340000c905690400201c2c0112402d0352120340000e00c0d05040110b603840341400e24a182100301c5009816100c02c10500d600500684000c200c150801c20203451703c0710019200035804202c55104035400900202c400c0500d0707058980000e0f08022b101c558940720b440151030405100001c041500c5401c019003503000700c12840d60700c0f400c0c1c1e00020300230039110750707091014513100201c1c0e1680c0002070100d80300b18441820103000050280b800a02210b900d000313101c0030070780748001d00210307114100b10402034071040c1d852042c40b09101c80f00002074000840280ea00081c0a441c10480d800f070100f82d440310f0000280c281c80d8040c3c0b07010341000c01000d9a258025202d090030b001c200c1c0b0114205299000381244140d00440e1040009020804420466094242110321110320003c00010b4078091000c06600d04e1040c640f50500e00400b0050030340c00704000c10f400801d5120b103844000c4c9100010302d0040c480c0d04010f0003168080f07a125101d503110b050280c06012110f0f00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 20858459 1250 20857209 20857211
    0x819020c07061206030809150408030a020a06050a110304020d030e04020a0302040f06020102030402090a020702030705090c0c071703180402130602100b0402090a030b07030e0714120307081204210f03 87
    0x701441d00f114410700d802c4039400300e5010315040e00041070240d07080a044414044100031b0100081440c824001031001070381660207000c03140c903680f409038202c4501414068942d0b16006181043c841910102c0ba00590111841285c0c9500340c5411901141c9120f815a0040c3c0081110213a940d01a0080e01c1600c105120701c1d94000d4680c80200d080f40000c48000e58800030840c0425841c400541c01002c1c101c1c00074040d1350b949512000400c0c0e0103c3c050b1100a0003120000300280d50007030510201d400382442e105125100c1c180b920300c4030780c0c1c2c0c0500441c10120050382900b601440d81c0f264110761320310581c8070040c06059519840603407550200080e0400060070154910113a01e080e00c2211890300e002000910803d0654907072848481c402080102850b03500d040004207800f0401c040f030010000c8000005a80720b913041404031550341100d010380da42d40f00340520380001e441030003603c011111100c010340e9250344034108540100c10495010030301d604002101810a9401000e41041c3c90080c0c030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 20859709 1250 20858459 20858477
    0x218340206010e060603010302060a0e030d0507061508060a020c07030b0a051e01080a110d0f0b090705030114011509150e01090506070b0106050d060509010b030402040507021504030819020c0706 85
    0x405503e00003021200645e100c1410070050005151030745c0502010420717460504c0710750f9a9480404c0c50a00c0e4050301c4c402041e40403c0306820080a8000c1041c0c00c0501801240c0903454a1000c565580b00541445102900464914161142001010300540e00811004041d06040000e00014503083e00c100d1080c1060000c0e9402c00310b05005c90f1030407941448001d208078000f9403204d44208051184107540144801060750120b6131820303590481e240909015441403c00d011090314024ad03642c4514007030390400b4051031510081182c201d0450313a007500c1c450040d0480c400c080344e0480d12074100117655020084001401035201d08601c0c01c482c001c1c0c90f4503040640381c004004031400764200c01402c8117030000044c0701080c8940040c2c203481e036000070041612070f00e840004074484426000074400310380c048100420343c549070140070740200050001c0d01240754401030503200204020310140c180300584000c50f41c14403a50300e4800385045103802c01c640300d20a00c3d44041d11000b00e44248000502c1d100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 20860959 1250 20859709 20859719
    0xd090602180109030f0f061805010c02010c0903150209010c080a02011401050d08030411010315030302010207020306070302070f030c03120501080604210f030e030d0207030c1e021834020601 83
    0x320054044c1c9400c440f1440001c45140d44044400000e03100844007161501e4141256a8140500c0301c1c071184103a00200b01c010340c60000900b107510389d28070a020803d00d51010004074004203051403904058001c007681e02d05864005903072490310110024801a00041d204000315410360220541c40c48018000250307980e1742d4100045584c10030406090101c041000c14000b851640d81441168810705000c154035400c84020720001c4620b42c0f0550150b50005204400c51400744000c590010090034210b01300902d5880300d00c401a01010010284940491103209043c02403400300850180c0074010b029568580c1031094594000b6201141c007140c00c68081e0800c2c01c2040e103001c511541b2a80e0f90b5050700211482100580f4102c1c1031180c281c001004503145d110064002801d00b940242c5071403482e0b021610700755202c600c040214400308000b01c040d00b80188d903044065203c6200800034000c080d1110325100034a060074120b0120302d88401c144040004a4265484604034120303020b440050b07a8038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 20862209 1250 20860959 20860967
    0x801060902030705090108060406030804080304090f02040311010f03020702041d0c030a020102060a1512050309030d050f04050906190602010c020c091006050f070503041412030c0705090603030d0906021801 90
    0x155010f6010480a005441075940b2891485034020030081021a03459a02d45440411f5070154005482c1c607000000d090180c8a0140590141107610310740c11454289181c8902c3c034070baa188013049042240c1c503164400b0720f0f0b00c240c0607034042a400500803c060200d1a4981d580708403e40607020a5004041100c01d04c0e00c0c0c0171505e03d02403038040e000b900c056074580a02c4402440c191600140070700c101b08020030030807045482038480d90700c203600840d13686081000b018074020b40ca68402040020400c9442044444030081e2003c0304c005032042040d40c0c980c4400036841c100c0300440010321184a15001644a074150407141c59040141c081e0785c1c2466058051241d00a02102d11114003040c4100030050248a03000502e04203c911102d07900f00481ca035a01c074115401941b00c2481d40c1c8118400c440076242407003d24110051842c0114a081d40c20094140c880d483c5103c0d00b03110707401100010300181c80a00441e44980321124003041403a281d0700c1c007903000b50444000d00f5130305020942800b03034035406 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 20863315 1106 20862209 20862211
    0x906050f0402010915090b0a05040b0705060402100e1507020f030a030206011d1e04050f01090303091403090105030a0b0f0405010312020f06010521070b030c04080106090203 76
    0x1c41d000041c200c0c40c0503002070981805041070342000d2070304180d0f840c04540902540c070382c03100c0d283c61094880740165405500d0000703001804008100c404114148664400c907400340101c038041000701c500c002c190500c40e03000b408071300d002201c552000001e403d001d40f000b4849544186510042400c00c52000d0048000d40d100400600c070603a1803210000200da4940541191442c10180320303109140020984401811110b0200e030030b01c0001c1c0f1881e00700844e01d800a0200d070486140041c000c00e950041038070340c2216488103407c00200401164a00b000581d00c46042d2703120b18903010010001c40441507844070508500c0030041e00d0320f0040c2c6000350700031180d41c21045d01a100290918244003824103003070300200c0c01401159681241000c1508104288110300c050180e405440d00703007180c001e142054408420040c5440300c0c18000d1040d650980024070406503150f40c4d08050b400 = true := by decide +kernel

theorem cover : BRFrame.Cov 20683459 20863315 := by
  have h0 := BRFrame.cov_init 20683459
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20683459 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 20683459 ≤ n) (h2 : n < 20863315) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
