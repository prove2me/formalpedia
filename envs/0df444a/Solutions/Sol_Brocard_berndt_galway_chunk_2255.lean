-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2255
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:08:24.980468+00:00
-- url     : https://prove2.me/submissions/15967a9d-94b4-4221-82ad-b19916c3f019

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 405395683 ≤ n < 405575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 405396933 1250 405395683 405395687
    0x80a020408060a1508010c180512030706050703270b01061b020d02040f090b0f090712120e060301080133061409040914060f04110f060405100203040f06140406 70
    0x200c54440088001592013000c15084004c0c0203a201c004426510780c5002c28000904400f601d02c9030740b205105e0454034010050b01c04011081d100281c0e0050300000ea10755074071500f03a014011000c400848181603003d800e04900c0303480035442d0180d010b000c0807166030ba202c01c3c0c01e80714202c401c0c4000381c189020811300c000610f0190041c0b001544043d00c0403805c600711a030144140c9510500844540c016102000b042c4520031850b035038042d10000062000a14202c9650342549540c00050060a5a0600c8040035405041c488000e01409007000e603a96940718600c500034240505c175001c8020003c1200c41c80ca941e1094009041d50301207505042c0740b8a05402503034200c02d00c20101c0c8500c001071003107104540ea00d104025000c0d02a5044840000c2e5000c01582811070040c054143d2400341d40a00c804103a10070083c8500d004c09a850818201f03040380002c04501880c0d0000e5400701828148040240d400700140c4120f40b02c004c03c64088a8135081c0a232200c0107600700d5400107203005e00c01005514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 405398183 1250 405396933 405396941
    0x103020f0d02010c1703180a150209061201080606040b090c030106030207230d08010e1513090b10050406052211220609050607020a090f0e030a020d080a020408060a 72
    0x1403050420700c02c91051035540380700940845d90340c580285000b008000c550059030b1101c1c884580060b000d8241c00ca8203940b0402c0c550081800404850743c04546203002d500d035841122064a4500c0c0a407240d507944014441d1780300804c07281c4034020f034206407800c8000d0618802070b03400b80850f14005d03400c580c206601140207400005003510051403217141c4070748e1304201ca1050541c0e00c00100140c482c010106801503d800410ba00412803841d1000c10880c22460390b0140000180301211254003401c4111003c4001d09103440d0040c103401c403280d00f0b000c40307406410b01040071508159000c1c4110b95031501003080031240c02251401c0000200301c0c84c048000b09500040101c038603201100d06040081c0d280c081115901d2440c2c0c030b0b51004164060040580040c286801030004442c01458080c0d940d011904042c01c81c800c486005441c0e80011501322100c1d00052401e07000c040449031601000c0310000d54418140040c140416800d502160101290b402118140e4103901c00501d000d403038840c031400080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 405399433 1250 405398183 405398209
    0x15020a02031605070905070807230c0706050c0111070b040f0f170318070617131b030b0603060c0405121204171e07030f03090305101b080103020f 64
    0x5000800c154a0102d442024034014103015000900f031460500d800072040700d402510000070701010382c0c104154281e1043d001380b880c81c070030070301000361006400c3c85041c640903000500c01c640c01140c1011402caa407241c050503020040c08000c0c0300c0b40703c03400c0400c245841071406c0a4040c08032440000e020803c82d1040342c0c038092003982c9244559440b51540180040d40b0300c0d00da41c903014000309000459407594624803201034004003402c509883c0c02ca004c0c4c01040800000c00f414115000007801d1040c80d289180d01040d009011104000c20148605648605500003120124669030124055060004402c0e10030200c01c641103180904180c01c0040201611007805994442e403020400703520484409040149100e0700711480c1d503016450040d04000d0000b803003514146520701858000a00010440112600306200455050b81030404031600300640e00042d186228a0044481c842901c1e40421a4140420050030341c01550f210b085495140130b1002075408003400b5002001403030b10130604207030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 405400683 1250 405399433 405399437
    0x5040b0f010c11181602070b0301050d0813030c030506090303131707021801050111060c030117122205060306031b01020f06090a11180f060f0d051f020715020a 70
    0x503d01800001408400e84408003030030500d8281c0c14000064200248035071141280c2c005040024240500e00015000511405110b1b4482e005040c007402041c03c100c51044840c0740351748800c15140d080081d10344e0341e10b00c411a050f04c9498000f8001c031102100340c030f002d6070300b1101d1510f13005503607100c48a100801541c0c040b0f41440411030040140e5a401844c00d0715980c00c003440c80c2035854800050000b40000019980c180c00680c1009449044070741203a041d9102c5001070000d441c120640c06241c0022111400c0c50a807000442041c1082844a1105c290b00c1d5030042c042519218403d102003030000343d0b101134041e80002401c0c0c610396007900b07054003408010b00c104c50b8100c40c1e071080180780032000e0320010000c0c1c01c5940d940041c402010f441e1000d08406807070b2a15030142d011070031404948010902240b401d044004240d60707a446500c456080d0100508020111401d801e105840d9890110310450036400c1201c1d841c14038005009503000603410414040f12040c030b000700700c000795200c0014902 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 405401933 1250 405400683 405400703
    0x182a010e010516230a1a04060603020a0e0f10060e330d0b100906260c0d0c020d0f0815060c0709050709030c030f0213110a020705040b0f010c 62
    0x10000e81203c10301440f031130151030300c651103102d00e40300c040c0ba50000345000081031300b00064090110b4140014030b40340c480c282c5200111691182040e800900c0f140e04002d6000201480008400a1000e00d41b4081c20400802c01440c0d2034070404000f940407140b0541001c244980c109110300e25002040e4140b0b40340c0c0840c1165140c1d4821080d01510341261542a807048000c03464014251003849806221602541c61300348000400801a162012900c10a4100049580c16560039035441140700c004101040000c005400d2104400d03446400c041d00462500d4549a181524203100241c8250340f0313921611401c120009a41007250301c070350b00501715034141440a0105c1d000d5121341e0003c10754048480050142503050000c110160345000d0726038010000c840300c1c00d1000c2408c00d420324040b641d121400301d010021a20102e40c3c05c0b9548004911280e00d0200d14220f0392040b0001003003502495401d5580c2e1a80701e004110494150286440c0c010a50104144083d409645000001401809011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 405403183 1250 405401933 405401947
    0xa0506010f05181f06050a180f180b03030d05010602010c0f051905091005090306100e060103020c0c130b100c08030f0c0d0e070608090607080705160506182a010e0105 73
    0x241c4131849a0380708500040c80040c0b4480003940c8250044a00900c0b40c140101903450034000055805040c050450011075816000c0c081070341c194052540380703402801340d03512040840c0204c40103040c240700e1280907509150758802418454089e100d1040304903290513080000d110121012888400400018070404104c00000b039525a5244105200260744041d600c4445c90f052505100f000b800070f60a41820180500120310340c0306038103511003003c1c03a006803070f17201c04001c8504e8444180540c2c4e030400101c40b010280c05015401441e00c81e2020b03a01c6413420155120211a0803070044000b03850404113101044031500b01000f00741d08002541c00d40303030030003820b0100c800440c1c034901d40d003501950050808000f100d4000d05001d0b40140040c0113811249842c02021b0f103d810024212410003100017821403a010542d0341581003a81c20202b202c0326841c00c82030301b100c07654492000140c644a40404265040c940300140b403060444019011100c00641c4010349000c0502d020701414030605001103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 405404433 1250 405403183 405403231
    0x906040216030e0a0b03010e0a0b10050901031128030506010e0a1a0f030901060e07140a0e040e0d0309050c030607090e250e1509030a020f060c0106080a0506010f0518 73
    0x3950203080954080188d5042c01c8001408840c0e07600d070000d024102440c01e0618003030f0840240c450b2100c0a08000c110138412094040a521905031185002e4403420108244541d0f5051030001e007002d0b43d01d0411081d00e4410055990034401d9426560040c000701c820701100080d80d452842d0818040500c074140940040c0c0c0f100c098000700c4054206da907480d801080051180e10260382c1050407400c2c004910410b2003051082403003401281401e01c400740b040c43c0e1641d1560362151181c100700c00291015200421030040240c20030040940d01d51140300314400c46840c02083c054094ac000d504c900c10218500309030b40035034181c01807104c241c03202d910924004000140138415400d00c15995501020810041041030400300c0b654003018000041c80154200d0f1030028003003c4442d011074915a96540d00710000e5224030440c03030585215400c04c2c0d80054a14000245c22a00c40d22035426200d1070f84c1c80e450b01408155403441945d9002517210749192406450f0f602d180e070800407028142c1d00300c100c00504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 405405683 1250 405404433 405404437
    0x3090209010f1a25050303100e0105060d0203090708030f0901021005090303070c030201090c060c03080907060921020a030c0303090b030f0726010608090d031e0b06070b04080403020906040216030e0a0b 88
    0x101791a036030400010002000c000a901c2c070040c041c2e00c1c010b0b80d2107504205c0490a68003841e0082d0400320760000c04102030003402c201e400c00400c120f4045958550071030b2101800c60b0050403000e4094840e125402c0d02001807402000d100b00c00242c0154295940e03c81d084030041c034888826030565580303500700004a1070010701840070301003548880325104024500248803507801441c80c842504a48000e0284642c0041d03d042228480e0344441000c1c02c045030b280301e40c5400306c3d02c0258807890140000040000f880e134200c0489019443c0c04940c140d8426a01c1054402112240c1c1911320001c00102040e010b0746002c882d105500744403501c0403241c005002e420440c20303080b49022600306000c00010490810440c0d0f1819064074081c0003218108042584a071006203100c0745c11521a401d0101948a0070705807550180c1020000031039082600300407025034014003041c2e0141e50450006456814103000302c450b030040e424004a52070413240c034121402910616019030050501c10000740070101e00340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 405406933 1250 405405683 405405757
    0x90312020d0228080f0711010608010c03060b1206010309150e010b0906240a11060703050a0c08070f1404180b0f0a030210050c1c03090209010f1a 64
    0x40c0c2d1200c0f031200d0b0241c059001030140361030105844401c29143d521010140e08500d42a009082507102c1c2c032000d5403508403001e400d000329882c00c107000843d9141508004008400340d1030420405071250001592442180c1801d6035003501c45010800c1c1d54400e90010201c0f5000e04078407824404101544001c1c0e900544c490360072691100000c501516080315201e410a00494200700c92107104040c8188203d00a0f920000c03001c4042002040d240c050f0504051a8510b481540d62600d02060050003c10741521200036049c07a2600010340302d402031926038040d04240c0c4941145a4440030700300c0304143c00ba0032180b0798880500001680c00c1c500c0020181c2c05d40c0000000c241010082e060002000c60200420311607050180200096107410205001c0c0d0040c41c80d1056071801408445842c00f0080c0b0460419030309805a04650142d00d0760000918501c00c482555007a680c511402d0700c4240c0c03a0207400702031b0020a01124002e0701e200c00501c00c851440160280101c000c040070100505048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 405408183 1250 405406933 405406957
    0x140d020412150c0801051507080904020c07061103070b010e04060b100518060909040209040618031707090e070f1817070902070302190201030912050406090b03010302100309031202 79
    0x1410001141c55070f4011418918110301c2e00080740d41c54400043c81002414005100258000644a09001b403d00841d1001000600155030f03a001010095070b4030209881080c1c00140c003002015000350000c001c8622045d08070040420690804145460700c42020304204d070105d64402541119868010480e514501507459a94030307280c6600c070201c0b81400200d4094822030040000c0348807a0340317481c0b040f40c0150f015034240500d950380c0d103440c1004000b6240d217400700381c0210300584e00300f42e80040800001340d952503c00303c4a45450400707851414040c05051044003000c400540c115100d07006050085800d4a0318a41100180c100b2810921203500100840c2020b40030702d010740c01c000c010002c010542e111046103000d000762002034071580304032a20b01c040a120f0002405581c42034100c5034003160025001c0840c03002e0508003070300641c820b105540104001460000c3d00320b400000f640d0480740c01030324001e030307829041000f00d00070b00c5030f000d048051142e40f02c04100c55081520140070025810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 405409433 1250 405408183 405408203
    0x206180d050d05041806031a07170f0a1103090d142a120f1213050607030506010809010903050d05070311180406050a060e090405030c240f0601140d020412 68
    0x711860b409042c3c45c11a840c0034641c201841040015545614a4030a41c41441003007542d45503884111094080110220041c928600603c411254202105402001c44c10010480302801c0211100f081c04103c0701102c0c66082007404156082c003c0b0007040c00d40d00c4000c00d061800c00d960b442c090b00d805c0c8032404031056600340f075000201e0341010001004103205c000801c60074804681086604c522503c84143e01021041c000324030001d00d502c400104103075011090f540e644c0f40148008004080441d0f115001810210229030300580600c04c402d016501a81c4040c9810303000081003002d00f0002c1c03c007200709941c0740304000e45c00403800c000c4e080011040c00b6643c540400c3c503040205031011038000b0780c4510350040d03040012036040303124a01006070a0b03030001034503561410060b00714041c001403403511b0300130300c004082c1441c074003091001003d000d00c1c106403898075000c2c07000d8000c3c04211280c50100f02250342c003031940c00f46807001e07080102c811003002d8502510358003c007980d26000c4004460352094 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 405410683 1250 405409433 405409439
    0x3030305041115041403030d050103030c06051f03060203040f05060c071514060d050f160906090207050d0c050f070306020d0b041505240c0d09060201090206180d050d0504 75
    0x21140b02031851a008680c0ba00140c3c40041c00303214188254480e6548110f600f03012400301e901c080c410f8481203d01803104020941c7c1d81d04020303040380c8a00104840281c6454001080c02e201e070a62440031a4203206480c10031815641d50070000c0d40050000da03001c3d50702071290300c0015401c00c01c5520400c500c41000c1e88500607440c000c02c001d01c2ca503240d4065181008200c200c58034440070101c1d80310f00c04903640003032011981040c6040c4138601d00350424a0040551506502c00c18590304000c55036100c1082061030f0b40c8171000412070180100050550b00803403102c07500305201c0c0000c16102030003141642d48004030030807404c0c98207520707600850b102c0b1340126008803154100d103d85440c10340240e40c01d2042c2c1c1590000c0071030101032400b81921490640c61315401c95440e81d414403801001100d02c055441d00c0c03002d00c46590751240744d400c0380011401200030035054411b0251040d40c0b0341c0a0b00741803c10b030003800380f10021740292040a80101030400a000810010008941c5000c01622450f0b03503141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 405411933 1250 405410683 405410693
    0x504140f0601050906100507150501050a0806060d06150b0a0f0905010c030801060810210606051509130219030e060601050c060126030d0c02060106141b1002040303030504 75
    0x640400e60080c80d801030001089280c0b82e018016078001e60855240018000d001005c0d102c80c014800c003d809030745050310003850b002050348018141da10850700b8080555545050903610715040b900d40390003480c00003c40c80000e141e9002540c0c0d00700c0036443d007440c0329120171030091140c00c001845c1000898910716480500d410030400c0d0090103003071030b04124400fa81d071000b034070700c10042c8102810000c1000004007440d5500d8141070152000540703400500380034406030030754090901c4d003c0d1880c510340080010b0038030740b0b450305c1c140b41d002114009040424980400c10000104141c81c40000d4007000140410421000000032071700d042c0c0c80009481c0303411407640b403402400410003810310800b0000b81d44008000142a07045036881e14000c1d40c0b41c00305482d41004240f40d981b078802188008552103c41401e43d0300107600060042c1e003110b816030790340c04003140c5d001c2c400c2075001c40c513000030440c2c4100090300502410b0400702000480d07159040c583c0c4107904170381c4968815800641d5803014041081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 405413183 1250 405411933 405411943
    0x31b210201050a0b0d39060e03060f09060c0711100c050d03060b0d05150a030302101b0c031b08030a0f06051203221e060e10140a0909050414 62
    0x28000e6038005c2c401d032800c0e80c4d5400310303003003103107580728102c40e0526107140c81c542e040d01e40013161142c403440f020196a5108050540d400750307040948240103010000d0f1244048403a5240700c0c01c861390081c041600d078001070309015400708074207446240603262401c2d00754445c031520030100c1401d95540c1084107000c2c10305a0400c5103c00c890010141888800c11110280c802502d403500c5505c032000a45440e07c40f954074100c1d240c45180b0b1f801000f0030034000141900428560b014100c0403905002c0c0e0403015100c0c0d105880030784240307004581a40c60200100384158003103c0c1e8003040c44a1449104e496407030300401e50b002102c00b114003030380f00c0383c074040c915802d0300683c00248030a0b5251006071410741d020a0301d902032550924610386503003070003202c0c803a1408500402890114a078a103035080b15410005014503074010b18010448516980fa041c0c24402134400b09100c00b07942d48208025940c4400e143c2d40e0019602c1400c20454400105942c0c4c0d00780314950180b407007000045444520143ca00b8205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 405414433 1250 405413183 405413201
    0x8060f060325090f1514090109060f030303020a02190606051c1106030601120c05070b01050613090209030c030709050106020d0c080d02030618071d0d031b210201050a 73
    0x3146400c5001a01c40e214241d1501500e44001d0080340b074a54440c10706004010140c2c5030100c2e804c070040b0006580c03c8591134900d440405907104402689c988075280180c80d418400c050513007a90745030400220340f003903001c2d0200e105280b040e03502441d5003000c00d54030005020350958020380c1d2030404202c01d103441801d2071600b0074401c0703030412283c2c0039449140c4145160300945004e4540040040d0141e8860300283c2c40c0c0900609017001600c010300e07002007094100803800c896442240d00045902e18094007503440320402068504a070a003029044000ba40000c40c050b03070503201d410305600c0c15550500c2a82c004e8200d03800c0c00140c40d85070000003803419643c0a00c501c144042c0e00c0b040c80204a42004846d2907040950025a40b902e822011411f682a803081c04490b800300c01044c00110b0741d00280c9000310b06500f145500e40f05000c0c80400c4408101118024082020138160250032744000b01c10025190240410400c0038406459106c1c0000031085e088005035512020010100b100c0c0c440d80c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 405415683 1250 405414433 405414463
    0x10914100b0303030c2d03010305010c0c051b01180321030606050423041b0905040c020a03110a30020705060a08100306020f0915030601020a0f0c08060f0603 69
    0x5500340700004241c5a10010f0101070403a600010058001050601c2c000300e2040c00c3c9580000f420480c3c507024169820a01080b40c8550900c1c107545507692203600281001c0750000e000d040481c1c4520ba0103012400300b4414a41486120461143c6030482e05160f9401940503035194162803802c004c0e40d98230010010f001c1c0c1d0915281031014482c580d070090554083e14107884901c1d455032100700d040942c000582c0c811035840360a2842d039400303207050f0822041d030341d404586810101b240c030b482c03c12003500d2540c981100140d01110184010034130501220001d00b07254030075510000d080b6210300f41c219507a0203001000c1e0b084c101c0959030359000c1446003000709041c1e10241107001d082c0b20002c0c1242c4261300b64401040780800120300e44202100c0180000e5a111604641d02d4000003101601a0807182c0c010340b089980810340d21040010710122842680168094544009542e54044101100d447c003900e8400c006400030a0741c0c0710800000340120482c00c002c0c00585001d100300740c03902c03c3c42e0700d029070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 405416933 1250 405415683 405415691
    0x1c1101050f011e09050115020c01020c360c03070f0809030a11010f091407060c050a02040507140304050c120115060e0f06121b03040804140f0301091410 67
    0x41800050342590b41910210074004100200310182e080c49158160012110075152200000d64810843c0d55521032080b160291b568803e070704401642c40304202c039299a0450f140c4070014640f00e00d00306c2103003a2174112005076050480d458011300391011045904255052000062102c186e070040e07100d00c2d0884040c942404686000111030780c0f82c1c0602402d60040c0240c03404150036404082d040b55182c03021798a03007003105001c5802c0040b000d500000d0606c88038003c4c01d901007540c9205401801490307820000410f1902800d50a2000401000304180708201105105407070411851009502481c0039030300500c4c220481c0c1c41045104212103032203a046a14014070844e09034100c030940c20494040d414a50004d00350040804c0003070a458a21903481103000a0800c045030258000b1801350003460b0142d800e054581103007601d20721056a000d0301c000410301003040b080d130400c10502018440686620091810b18010034295200940104c6800003014889074407640d04005803e100003000c20280 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 405418183 1250 405416933 405416941
    0x5030f041a0a050a03090c1e0303090503030a020c120a0f080c0105280e070503030a030e0c0d020a03060b04140406090b0a022704090c0b03040303060f06091e081c110105 74
    0xb030030a2144c038402c9001c0c59141c40b0000c043c03240c50007804004102c1c04040148000c804541c9150301e02c42c600049004c1800800041500e003800030070b481c1c0490182d00107040100f031041c104564101150f8100c11284247c00380703600062400084108030b584550030041c0c6a9880710065400c1d07071001071840076814003680446481d6030250980c2083c1c10110307000000c0360010240d0446c01d11100d40c2046e0303014440014040c01055242d44401000c0e583c11054524081e40d2108006181c01e0405002c2d43c001c0c2d180c0b10500101382140c2c414800764400400000e8010304c2d950a12044000c1214191880fa1385c4030b44180031b1001034100700b940002c0f0400c08600e06503608103180648007000072500d0b100c0841c1c1a400d20170b9110b65002119450300804040440c60b40c03071400a84540c42114200c0010b410600002440d01c1c810022000f51152610741c0604281070448180d0340002010466500c0107000c000018041818000c10503c4810120510a606040300e00a88030f0084031103452060303031501c0208 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 405419433 1250 405418183 405418187
    0x70605130c03060213031209080f0303060a150201020705011b080703090b070f05090319030f03060602070621060902131a190908010c08070f11070b0a030905030f041a0a 74
    0x9000ba20b5200c100182c40c1c030f100c12000c0080724441d820050850018804011034150030199103001c80e0b04400880d07503e50300e009030700d079120702040d91665080002103105202003580394090600c886410310005007880965107416007035461301d440303d45c195944407010002c41039000400680c4010703142020302030b609881d511000491401031020080042003036504031024403800840e10b00220007012940e04611060406c0c21103550402c0c11004560110103161140c3c0c064003402003141c070307241c0103032401c41d02e0511f0984552140c9904106c3c3c0b6059000c8560030388116105038000742100381d10040e01c0710540c0083c0098480e10ba0880403034002d942000400c00c0004a0840c0d06d03203848440f4030801c1c0391002d0300a81c0d17100710350340110115500b004016624a980203400d80c0c40780140703036148441c60b481c1040c15a5031402c0b089034a511500200020b001d0403460500a141c0c420603480c00140c9220681ca80b04d0964001034800720088100090030440c0b05880e481340c031000e0340c0e0500701d01c0c5080008400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 405420683 1250 405419433 405419453
    0x50a0605010c030e01030507020a0b01030c06020606030d08150d02060d0506030d02030405060d0c050c0609151003120f090801020d0911061215040605090906101a0703050c0c040e0307060513 83
    0x5904147d21440050b00329442803200b9550300790300c41200001561240780c0700711070503803d000c5c1070010710400700040c03214030b800a103806d6010f541c1d803104003240d01e440b443d0442600f146903c00d504180d0701c0e0840d0005850f03000040445031105540040c203410000101400c124285411804649c4103210a106990300c000480d08403104201001600403e012015680c5002c0c400c00c5442c1400f501080080701c64000c24a00160340518840d01c1c1c0c699210a905200301402d03010103051045500a8180c4950003401d40701195186810a030b15055583d140d21801d903030001103500c10345600d520149080142084040d44446412180503007015180030004c1034040c402420b000c0d03840c180c1c0340d002403152a60b62010020307243c007400818561070303c1498582d8400042ea50500161031400d03000034002440d4a26003036030b5010030801c030328107003e030345040710709030440c07000d25990380075a10820754140c3d524415504085555005991a8a4103040420890740c0040c84010041c00310b1079a0000194407941f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 405421933 1250 405420683 405420707
    0x180c1e01081b040b1c0905031903180609050f030a0906080610080c0d020903121c0606120b011205011511060108060117160e0604060b070f0204051b0409050a0605010c03 74
    0x200c4d00e40c0307a4504002c1220302240c1075030780e0f040d06441c1103d034005004c00440100001d5001d0104492140c215580440803291603401c800010081d054041c0005412500101c070320a000342c040398180140051b0700c0341154001500400450a800c800f04075164101c140141c0c05042183c4590740004040340107400f1840080c01c01c400c0b81400916074420f44480d85c181e400c0c545018044440400d1400354000d0240e004486204c1302448012451b80318410303a00808040e903582e59114150103480da100d19019003004800307581400713131200101040c84100c1c45000c0c002d03c0300f026900c100d0071840c44080c043d900103080e0300c51070b03800940040c8000000041c0403811280303242c503a525144a1030b05451304100e80300182d003080208a03e400101008140e910900541c002c41d410071040d075480722071200b03602c13404200800d0402c80e51903007800751030a07030f00042d8008040d45498a5000340c00c14410960f0b80142c010f0062190303104280607203036400b4400c5a0240400b0700300311a91410300c1c0c42c094000c00d0006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 405423183 1250 405421933 405421949
    0x1107020a141c0b10090e1b04060317031509010807120305070b091e0304060c02210304030615091a0d11130906050a020a0503180c1e01081b04 62
    0x400d0001c0d00d0300c41004207600000b1200341400100301c98a040d18120307500361403c1d5040c04569202044074022441601c0c4802450740003440f80314a0103103406107045c00040c129511030344e600700003c003040c03a6440c000ca207000795183c15a070301c2ca41100b40340820090669060b00a084050050010701400540c903015a031b02d604451129059522b0300b2a840c0c86451401003016490606000e00b500000625082130101038035049001040740b140301c0d540e801544100300015803142e1300d82d809801e0010b402c008038400c0d031801d0180458044203062842d40180d1080f40c01980da84510606440c0300b8500c81c000d1712485005002d030701c207410100f5032051001c22466108101070f903844403c00910700302e071801042001c0c000c0940260400d24a5000340507111040d9116820140001d44070182031007242c0c91883c46840352030850300e134407441c190f00d5100400250160300c180c00d10100d1a40d2440340c8a000726003228032102032890070600050011300d014061001802e02e0802040100e4124000e03a01620740700c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 405424433 1250 405423183 405423209
    0x405180f04032d020a0515150111070305010e0706140403020105090f0406050a062f060106051c090606180b0907110109140102071b03120318140705041107020a 70
    0x81540b243c41c0c403030103060b01ca40590400e9802a5098010600708503960140055418040891800c8412106c1c111980c1090801042d0038000c15030160300b40300c8803500fa030000c44030003a071039580b01400c40341100f09008240d0300007101080001e034003040c1070b14802c5110800d2810940b8542c0043c02d14090302800f00e101c0c03c2d0b5400e014903962243d0740801c0041c640240500106607907141c0180500c2e90010303000702240e074122010f8140504503481d8a410300901002000d04d0380c0380003000c40c1d00d6040064040b4213180907040c0b2030141525400f60a640c0d03401508001981071034400d00c03039110030280100a010508001d6060010b5a41c0e44490303034080680e050849081c501006418014141d05074020103801500d41c1d0455040740540c00750246134400c100500d0190003550640f111120684030041045407002001c1041ca8401d4001c03001a006030400c082941400340c0c4c074008203103991440031306640e004007000c000615040c081e07400c4e2150758a400c6450499560042040c03803020b402205080009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 405425683 1250 405424433 405424457
    0x18030a0912020609040903030203190227030f011a040c02010b03070603232d0f071428020c0f0612040c170303040203010501050a08060403030b03010f060b0405180f0403 74
    0xa440c2c00c0b44c10444004000b006070721554500a002500240d40c4031800c500058140d18040c1e085100702c41c0311490703022a030240300600340c90094080c46189800c0d50540038000848001ca02d09025542003825011507410440c07124100748030031141d00411840440e8100450160342e51804140da0003566040d1401003521221141c00c03030745482c2c01a480605850b161810042c0c074000281910100d81d09075410300301d040030540140c803410b1070181c40c40d40c50089410003044900e800344020b018680e5a880016042c441040307000481030b6010900c103031514583c45000c0c403404d40d0500030f0f500404400c494402c0c403680d514022a005005445048035880024030216050010314040013000b018031000c101c6c001c42d28800190b032a9001610200d00940c00c180005c102481d0901a21040c2c030654401003240396102c0e203044014000c400182c41d095581c0d20720311507146600d0f02445001d050126000c80e40c030780c0f900d010721005036034084104149101c4003090102004d601c1c48884c2c3c1142c0c043c80c10401442c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 405426933 1250 405425683 405425689
    0xc02010e030403030905040e06090601140a0312020d0909050c07081e0f04080106120201080c0706060806010617010b07030c020d15090605070f0c120309140106090518030a091202 78
    0x21180e09604800c1c8404a800030405501400c0e040941e08141c038240540c4401c058000d0343c0b8a003c0d100c4000b140c010800510022071a4100c092850000501d4000600d503070f030300c80c1c400f0800c440503020010b8014410300440d41c1d42011980300107010301c0c182001b00e40382412200c4480e0081c540001c08a0304006100b840c000d52082e01504009110030309107541d5103c1d03011800542d8041d00c6a140594241400000c5d80130741c05100782e1030b4070707010303126009903a0f0b0340c8140d061154030101c42115103594560340419140403c01840c0d029203941e80303408590081901840024400580c40800f115004110ba000002c3d840003044d220b01c1d5041c0c0fa00805c00101d458a01450150014a2960180341c180d1080500c045600000d00136801615202c000285004086800c803001e800041c1982c5485c441100180f0301c41e41c4a500c83c1d074001d000000e044400c1d8030f80c01d420740d406075202240c0c41d5203510501c0841103aa411040c4148980340c01140391082c02080070304022103500c40c100c0680c00300c000090030b41d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 405428183 1250 405426933 405426941
    0x5040e0112120c0c181e0e101407081312030f2a03021308010c050409230408130302091305010506270c070f0f0c14093124140a0c0201 59
    0xa600042c01b2034402400c0f0083c2001460141340e20000c2d807107010780700d80c0003444a03c0341e0031200d441001d00c00465a106c810555440c10050080882740d80b9030f00c94035000c6220310051740c01d40441d07035030045140360380c00d000d400c241d0b5952986428110034225204001389155403941c11100c8140c140561900c041e91440301d0801c445034802c070980d50a064000050580c040d0080c41a02c10456003008200e501d040280c8410001c0d260040000c1104400318010841c00d0019007800c29819890f00a036030b0b01c5e0307404206401e10076951000b11900c0d21350040200308007030281c1d641c042001e0783c8071402c4458940005811061041d109030107915000041441e0006c0130007261221a0810170303240c50581a490300c2080221025400d8407040c0c98200c010075246d03985107282510480c000c20074041ca4803144008079603c0b4070700311840d68045007561b0f20b01141c00202510b4407070501810601c00c216100442e101c68915110080c01c4805182903a161407005121003d55000300f10414005400107890700268010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 405429433 1250 405428183 405428201
    0x402040e0117030c16080706030203130303270b04110d020d150603082701051e09030313081b010206070c0615051e1306030f02060a05040e0112120c0c18 67
    0x185c01016074855825598500d24011240204100c07110580d0b80c4504404900007039541190400c43d01d48542c0c00300c1c0c400d4102c0b00300c01c0e524214086860740314500e2042c40020b0390324211414481d045c20032041c4103800e089440c28001c00e6070303d00c801c200c483d400600100e41c2200c0080070103540000c0101050f640d540720002655020000c0c40c1c1e922a0502c2558a4dd021004100c902048050401c1100d510a4055400c25001d07012030a50f0900d104007222030503042000030a401d071205000d00b030440300e148400400148100c074050208125403000c0405040c162a0075181550310450601103810340c8022080500d540110001404808089030f000080100d540107686c0513030b510742c0380510b001090101010003041100c03004100c104008d02e0006841e41c52001809609411032100090f0510000800c0303411140d20300715161584404140848402c00c1e042850322440c0443e0120821203041c507a210020000c1c1001e03240d0303d80c6640e55014240d428090303440105e4070a140c0740d84c0701484d5000300c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 405430683 1250 405429433 405429457
    0x1b030405030114091b0901090207110301050c0910030c0c0b0a0f0e101d060f0c0409140403090902071211010b121507140a08061201020304060b0108060402040e011703 73
    0x80004460383d0490581016625401c06003e101001000321240c8401143d4421004e00440c400ea8a00080040250000d40056460200c4071080d40d845550a101e120320402d452504642c81d0081c002c1404800720549c448a01454503004502c0c22281e00500e0040031a540240b0702e1209688100e8001d01503c50303101c0e5520854240007690b030400c2008100e0100c04545c003542009001c0222884034040100e0103000b8003150010008203160284640259900004000591f071038240d41e1108113084030380340c1004010103040780c0e05010405a006003010020000311400790308242c07407600d0700001c0400031401802403064003218180001400c0d000b02810f081e005011040c0104034462803a25021048040f0912404c501c0020700c05074019411420194004400a42803e002000986444001078480307503020b410602c0d1b1000c0b4035000d0000391700c158850000401c41d40c034080000344c10520050b002d240b00380c2c0103100c1803100b0005104410304407401d400081001c4002c81200a045225030b00c12010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 405431933 1250 405430683 405430691
    0x801120818180a0b01020d0c02040507031103040615050405070f0f091d060f040509030a0c08070606080d08090d02190c0909140c0303040e01060509150406030e0c090108031b0304050301 81
    0x2002c4030404025114080340302041c00003020410049844003158136410f00469404803641c0c0241c241075108035030001840c10b000030303254107541e0590040c0e04112000c607055030b2502042d00d480340300740b0141c0c1c004000588051099040128010700044d860078403170020880d00043c594901841070314210018401100c0800f20603a80341d294818004044500e940107103948484581c2030300b0903114081c4202c4000f400340d0306241151200312a50b80180c4001d44000b90140300e503102050b61849448000d1880500402803800361000242a104004005006580002c009084001d401207405005220f07146554071403800c0760b2918515440d1a500402d0b100c6140140550811640a051060311407030001203031a0712083c207082690721310440c014240c0c001c081c080100402401000030302042440108440700ca4407038601e0124198125a101d8170019407104618400e40d9802c1c0200b5070309200a5400e02c1d295810540c4869480c82403000e40500b40c1d0340c0c2c40744810300200c01c0c016038015040040080c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 405433183 1250 405431933 405431959
    0xc0f030f1113090b06090f060708120a020304030806010903020604091d12040503150105060f0304020f121c2c012a020a0506070201090905091914010c0801120818 71
    0xb402c0400107019a98015141041050980c5080000e84903a541c00034130a40c81c9024181c00e105440d008044225102c10080c019003562510614240d403158401c400016124500b905000340b45c880302171300c01814001032180910268549070122000d642ca0088040341c4106103090040036421070382c2050748a40513181c04654400900c50003482121000c5003120205243c64640d184844000c1c8038055008404010742441c00c0f0041e40a940c3c0640010f1032901c1641c4d024000c11041351400300120074540008208007032000c2d003030503c100d20081d0391406185c51241d284501001407040034107840c20210f0306400482580c4121100481400221756603c01c55a40050580c0030b940c030280224841c000840020a40f030510800703480b0700780c2d0144d6902e61054a000c90304401040d0280980c121406000d90400c2703100d0100888444103032040400c1d800c1c0107424214035003143c9503810210100407480780100203070ba40c0d0b042801c490036008614555540c00b2210b28030b41582680e2441c50f041010652a2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 405434433 1250 405433183 405433207
    0xb0906040b01140f03180d120906090602180405070315120f050703050601090c0e011b020a051206041a01030314030a2003090706090f091a03030f07060f0c0f030f11 72
    0x1450003050800c600741b034903030340d9881c41d0341d210030b00300301c1050005070010400d003240503ca070002c0c004c290080200049801142e1a0002030383e2280d000c4901d07a1009102c1e46540b414a40b1030240d10016074a0f0400201c00000710042c0700441500c20000c0403a5050b5040c014004201e11002c00c007030307100e002c41d21019928a031283d00c3e85400d104501d05145061400d0270524041d4041c413504080c140d46a04032402c81c1004049141d24107041641c1160140e031001c60300d600c440c241c290080700c41900810061600d8641f1490182081024a0b00b1004000041000a42000e030000000152032820754170ba0380c1d44c0b02c821008000e01480301c2e20340d00c9024000306454040c100198003a0101e00260f440a548035041550a036400d4860b801036111400740c10070105500741d100c81d101d54142101d1508a90000d0002455504074990030503080e1400070b102d408000945c4140b10394252009002d001c8042c0d05c02014116245481151050607204e090100d41404e5a0b80688009100c8044094481c50403601c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 405435683 1250 405434433 405434437
    0xf0203190e0c1807021c02070509060d0507030206161a04050f0109081c0e0a081b1504060911040c05190203030c0d0905030d05070e130b0906040b01140f 67
    0x19600e002854034903109120380020402da00c0a04014040c464050b40003041d1452020300141510110b00a010100e101c54035080104446d1380410350041110900b0401000001903000e40b400f80306024502c440340002d00d022926030204ca4040340d016488030b90510301000101c0015078010109190010981101045201c9540c0142e0041c400c032a840e20118654a0803502d02c5071026080c1c01040c40684915030f031800080c80080000e58010414101080e4110700d40203151108403401c42c00400c1d038100300cc1440c884104604680760003008448158081d110340d086000d4005800d1135140c00319a402c1c0028410042c00707140020340108145441e00e03100400d40e40081401e90900d41681e505240741a10020031790707025401401000d0b2910080c01c0090000300219002200e00c2d01051124440103142c81c402c0610410107a20381070740945110341000002901c90400d030300701a141c90030250007503e400c4100c650042c016603001580180c031500507034805d000c0c503100c6012146d00150002a10440c840 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 405436933 1250 405435683 405435721
    0x50307180312080a0905210702030102030a061e06080c090103021c0606020d0f17070201110307020c0f061801080c0d0603030c05240a020d1104120b01051504090506040f0203 76
    0x10f00e0058903122003000c40c040e00c051000140182c0d22014400c0c14040140180c0030803201070203441441c144803540403e080e80c008803001c0035141d5403031104003c40d065034924108a903180d11880101f09040200280805001514400c1c4100e4003042058080c0d000e5412140324011000c00410103460000701e18015020b280602001409001140d003d480d024550748812070f151610761044103400c110320390381c0078000180300c0e00071503480f920b0107074450803103200460088804e0b9029040d002c2d00b072030500c225000013501180c0510400c0200584840e080844880c0c03008091070014903540f5003961504050203100c0300c16445502d03140e4000b08140d001001080d04a01c51416074500400c4039441a00103d111800504040000d400203115207038254001c2400c0100c2c0c0b00c00051480c00b504010115800641106840c24007206152051242d201941d90052504076002c9101a000750b0800050340030303610071480c20300d40741c802181c80c50781c60b074110310803001c1c1d0301c0d00031522441c1c04540340c0c0100803292 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 405438183 1250 405436933 405436937
    0x403080a0b041d0c13021801050c24041b0f090518011a040f0501030c060810031a010e1005010207170f0a080702120303060105031617070207140405010312050307180312 74
    0x1080d0701014205c50080e5005c292500409032440c44000c401074030140c0c08151209030034000c0242040b1450301c7d880c0c0680c0b0301c0e1100c0080004030f02c0d0a1401c0c0044860007814000c000c41008402c002002e25840b0010a94464090118150315607a081c0044100402c1c420080c5500746070100d85548540d09034007020002c00c44061041c402c42c9410407086600138040508100e00d844424050ba5020342d812580120303241d0180001550340341c40700f100e803040c0c00c5400d02868800b10010802001640419030304406440c90354000c40b132400300040d545003524402d8041804c0c00e140400200d460a00040c0a401b46070001d41e09905500c1c903240c1d0182d03201c08812840b03505412004800d103000003051340e104504c103841e07440c956220100e03150040e031400055101040500c85504964100741c10206005141c55001003558604190b441e50154043e5039280b401146460010000300341c034400105441021402c0030741d603948501c1c50071901a04641d40c0040807145549001040040c41c4100120180d465 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 405439433 1250 405438183 405438199
    0x9040303150b0c120a1806050703140c1c090f0803030a23060405061318020a080a020a0b0703020309030307051005163c030204050f090403080a0b041d0c 67
    0x1a0b001e400c080c000c072a0342e084141e00040d03600b618440600c000b000d1502d81d501b0800d40141540302100502d0030300e9040f10300010008a0b080c02010f41007042000c0483d414800c490600988000c2140d540c0d042e003410f000f20561400700c0300c000b24041d0020780e0182c11040760694286e900c5a80c40342d500d51080d0344550109283c243d64a00d01c0c0d042407030a0420203400003c028858680c08200805003c0c09021245d01c015080c6400c2485030203803048803000648884207145600c4035004106200b01141d100307881d80d030441c908002c01030b512203081030207503480d0141722030307d0f14003605080b441c6000d5030b4503441d0148000284101070080002d403c0d010f0707a440400134002d541e81e080b049802d6841c9014444003007602c81718203010400311100c03400070100d1034080c1e503210354050341604c8190503000c4002d400842e81c00101884913083c40c85007021002c0c000c1d145c05516040c0780c0e800400c5c160703004065061240d40e80940003016611608941e0307800400c5103000b51021644000c43e0f4440d214562850722813107007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 405440683 1250 405439433 405439439
    0xc0d1103030a08090d111504032015012c042310060b0a09060e0310020d0e06090d0203070f0303090f060e06060a140402070303180804081b03030d1a0904030315 70
    0x114006d001c03d2441c152014040514080001081c030800283c01203080c406440d2040c1185c4003080007806204411500420303c41074003040da2a10711038180c0014118000c080f00074000d940002801c40007400c502701c10341c00d040d6140d0a012030240400c4440c0441c80c441c400c400a03010200013035800f01300659071001c112680e641e4080510501c640c84098010074254034003000705c54010400c0d01d00743c003000b80c10b50b400c54a22802c08412640015005610156101d0804801070000c0020760361240f5034000900c140001910060f5072030140400050444940244a0341010b22039042130082d1035001008050301865454050007420142c50310745a5072003098005402d41c0ba2041450741120a1407c10800c400c0240080c40082d501ca04015402d154552a18141e8900894081d0ba403040c0146074094039903082c041041d090244030030011240f1201d06000d00003130794020046486089502800017852504d1000f0158034410203941c0c2c170380c050581c0c0d08100500d500754002025442c2c030702900f50100b6071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405441933 1250 405440683 405440687
    0xf0b09070513050f060d0509010c030b0409020904110312030403020309010f0314010b130b070c09110a0806090a141e2a03100b040303050d050f090c0d1103030a08090d 73
    0x303400703104115042c40341c2d010009420860303002203e40c000544400d01d02900c3d40c0c00041500c00c20745640506070b64401701849810303450300c101c18a0110844007400320040326000186070440140c8060204012080885a180e80800030a030b62403480441c0d90791203203464107020303440f5003141c03150030702050042101010031403082c801d92150300c90344e01045000f0790a00c5035a0410ba08008511440502c903e40c004c05c800000d00042d14546100b241c1d994505800c110102041d9800c4055480d5000000d01c15000c4058100302a6548000c003034a0040b40d568031891603201410320070100320b0184040e6014851603021201521580c4118101581c2154403074440140d102e4403628001110300003907660b00905c1d521854010364004500404440146850b000c0300e68039a80981d00c1100400c20008143c0100c01c01409042e900101c1c0700c1d0740c0d8081e484c05441c40d50703c5601302082540f0a01e0401c18400421084480580f4840c1c00902169222981c0c0709015081600c1034400c0010751040b5007085e040c0324 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 405443183 1250 405441933 405441937
    0x80403060f050609041704080708070503100507020d0c020f0d060b0f15070f02030c031c020c0306060a03020d031710090b0301020f04050d08160b01060f0306030506280f0b090705 78
    0xa00000007a60352500c07400402c0346c0b000750058102d4420040000c0c00e0000b0011800604200800342540918020416180c8085000c031016001c0c14801005803003500401c000f51022094140003604014034400101700c400109101940a1144091201400115400455040c50654070341101d441e0030f8040048000d03030391a001c00054401c0023010001360701114081029840032b0101c4026031138031000641414000d10201010812940303003a00e1407a03040011480c1d03c1d4007540600a80d051013404200125100c1c04040e004001c041d1140d810980300b10358048418a900308880d80b1404c4c461030307200041e1054400c000e00681080902131b2145018821581030011200381e80b4a03051615051107d0f03d016924245ca401c2e00522a06850020910b4501005071243e00c020745950f04000010307011111401c1a641018508081800003810024010b038002e8a91107405600c4003010a20161030100f0312444e02a190602001c15a4034025802c5802c06a20417108101c1d980e40d914000c41d554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 405444433 1250 405443183 405443191
    0xa0e01080903030c1803010207060b130b0a151e0f2c040e19050a0b0106020f0a08090604030203030d02131d06010e011e021f11090603180a080403060f05 67
    0x142d0003c001140810007020b005095a1000b4101401c8188032040003074220707080280241c5105031214201466807610242c09120130303500c000100400d42049000c100710148900511424480141c9120b180340d004480c403000c040c1ea021111407084d4909500240a075190b00c204c003010501e1a5000070391354059294072072411089048048001d004001004041e0140c02220560f43c06514984c4098410f6124030340070541c00780d8010800b80105240c0b2030441501684084219000000103c07003241022400c201e11b1900081d0180d120030b04040000d0b258481c0b544025810700c00069000c038401c425402421103c2c105556041c0740750740c0d9581d540036150310752401d4108102d2030400034a06602400802007134000601d005040b19840d5112442c0780441c41c2c0728600564030445a0440740502c840c1250040206120140251000035981d903206000d1101840d205110110005046030030003060b11510306002c40c1203d0004c03d040c1840551548640801d96007079050480400d00112640203003402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 405445683 1250 405444433 405444451
    0x31104060804020402070201110a0f0b070305010608190b0604170106060e100f0c1403030411040c121d060c0c0624090402010c081801110604021c06061503020a0e0108 73
    0x706030303195400c000095201e001c3c00c80c103100302c56910500f40101044264100c41c8036082003419a070f06401c1030b1240000051403e800c02d41031100510003580e03c40e8485402164580040d94039078203050b0150003804c0c5a8084d43e40104003c140010501d041c8100b4078040d410b004020040301e5111101150f1181101041a0708406500743c1402c54512910a00c0308130303030f21803038512644141940c0b0031855586007040140c159002000303000a104404d050303604040001c032020420000110310180c0041c0000082000c2c80c5d543d0103001e0419000304c6c0305041c2c0c80c46440c00380c0e029403810342c1c102038141d00800c0700f80c1140d22640700002c0d201078003801c030f945042d900e0f542000c01d0204684200700b21200000c0c07040b41000640040c140004180034068540c00c10112420342d003a120030000100030301102c0440c805d09a00172814070001da1540030141a115482c100c0404103032034907082c42400703411541e010004100d02080000041e991590140c15505450703900e5450b03050716007004580f0507009407501d000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 405446933 1250 405445683 405445697
    0x6030a0c12110d0c0602010f062105030405032d03090901031401022205010210020f0a300c11030c0714010c060f020306091614030a0f09110103110406 66
    0x21110214001a6200d01e11602c1e40506801940c808120030080c191021a204200c0d45402c1c003000f80c082c000d560121443d00410000d1900c0c3c080d44014403644140d62018110340d0300c1c2c1590500c1820b00032107000c1d00026003103030300c614904109948141401c80300741e0300c0d001c180c0c02003200002c408011199080300c01404130303c1c2a42980c444201a104991680c080303076500700720003250710601c0190300c40f00110486941e01c826250500180c2406184586298a40d10411103e041e011107107040d25144440b514001080b00540140da248000c0300316082e80740b50681c240b41900c04c041a8000c030800c015207542c0c48400d0b28042c03c40e20ba0f6400751544110444e00b1080050040c14030301c2e00d540002590516100e1010b1006440d103c0840304d0122034050361903000020407082d8109644510707000702180019880540c030348500205070500c3c802614044010000102c0c528801c00e070081c3c010031951390703000c001c401041e151031075207081c5d82e42e0450b000c0307800d080a0380300c07410a440a17a012100240c941103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 405448183 1250 405446933 405446939
    0x8030a082203020a0b090304050102030d0b0609120303071e05031f0f14042007110f13050601140405011b0602040807170c03030a0c02040e0709020d1406030a0c 70
    0x345004a005103480700e8058030310041107032070360460118000207000b5006031854842a0408540300300700182941107981c0204820003507640d00000300ca5641480c0c410001c1c00203000400203003d807091800f00c0c3c0c2d001402e4070007550f91440100085000c0c01c880d484400c80d40405000358002150350042180100e4024000110707464084940c540c60020060001c240603601c03038410a841000580200b17a07d40352142c460611390900e442038851a10300e04640b5590781070007803c01c00203840b8070640107107642d1641d0000c0e420380c5c84144922100010080c4203400704102c2c4034015008000441e60103000400b1042c45d041840846400c07a010760310185d4406416954090103180b04402420b02220483d83c20800020880c2060042c04041d20060b4040d400c0000301d012070524010f141080d00d407107500104505000d507508400410000380e8107407008101d0890001d00e00d402c01e03449030301c018510780c00094540345040329544417041c5d6003040341c0610016140c900c24940d030345041c40c3c0e004204100801c014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 405449433 1250 405448183 405448187
    0x1a090d08040b0a09060e0d030b150703140c0d0f081503120f271201020c0606040518010c08060a091e0b0613080a0c0918110301090206030c090a0b0408030a 68
    0x40d81c010041000840d00406594524045414541440516421107810385600d030307506000b01d64841c5001c4907280b2b0345d0140c80000901c11320460100409006413150312100d000c2034400bc0c1c41c1d40d00490b0b019100180480b6070040e10004103000d40070005114040020384050202194401381d52000d402840c01c030a20321400841988000220500d142041c48500c8600740c0b00703c05880d1081c0b021924a4448d8456000c0c05001c2003a0124014244d00610a02d900801c00084080d03105204031004107150b1110014501248000400c42c81503509000c000403009801140540c080c003016034481ca8031690384d0b00703003c044038100c40e0515805c018005218803441c607140c2140e4820fa600600017807030008031600c18000014941d020500d0b40e0030452401c01440040d807429402003030302c4401030010b10200800306084500d00d400080c644408003040c00c070700c2d440940c400710506502500e802d41e24201720310003004e02c0d0419080a8484e0f0003200000c585540daa03400d41d4106c03203480c401141032494015003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 405450683 1250 405449433 405449453
    0x109020a0f080709090f020702010e0d0b0a0911040219090b0c0a081e0a0201140f1501080702030f040e01140102030f1602030c04050f040302010c0906092309041a090d0804 75
    0x1556003085513044011801506602c40c0f4440d1420020700142e9a104900c00942002003140d03801e8413641c2d0541406000c11b1504800a0703200c1007803000096244d48500d40f8610000b1102c510766002032001c14000003090011b251115010ba0f540c440401d40c503901c40000c0f00602c0342218082071a00039002e00743c00103a481000e07101a00908050560083c0c5000e1880095003240c203028006039125201003410700801c50241340c03c54000e0b62642d8551401d0b00303086541d035a00107960717410000e0036000590498428425294803d1b946039101d0b0b9501d5461141c03038080c1e41c013800382c1e5042c07154a441c220708960000040f100081007000400d03042c17606009960f41d40d4001144166058021050207010666941c46814031482441010b20520304181c10000d08442501c0224000d2155900041c0141900f1a4000003100c400e0200b4601d140d544411001e0b00c1201c8031a00c5410281800c03e100420440c00c44014584480d40d45030611643c907010300d01c1c0c1e600e1030301580e400489c4569002c02c01040718522 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 405451933 1250 405450683 405450691
    0x11090a03031809020c030a03151512091218050901140907140f180405010b0f0c010e060f0103053a180e191a0f0d0b0a020d050109020a0f08 61
    0x101c1140943d0303030700c0360a050768441c01c1000d034540c00002d01140044d4061043c0b0118481040e04c00d0585d50030f04078150079507403055404800f48100240d003201d010150f5000b07958040d40c882015041046200405408103004005504038070030180004030351390070420420340c1201d0a5280e24080e04607020107109140c1c401421582c100206003c10703404041d0910000c141c2d403411030324016074540029806200c0c54a1103a1050700c0349040c05c004125100900d400d40c0c480000007941d0301c1d41e17030000c4007035240104120f0207403070b87c01c1c0142d6003005101d04a40d0364003030480703000e00c068881c010143d07c0030392840800f243c2c0c4d5880030b25003800c1d03c40c2e40c185412202100d2014504046240b50803a40d1848d000301c11a501009141036000c003040a661460303048064000181c0c0801d001e1440060f5000d003c4a00e501c080600602e00380140690954a180c000c0c48116008400c40056051920ba0740d4007070b40c410034a00d071030142482c000055001c071500c2104d2607141c00b0342e00c49055541441044503d0413005d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 405453183 1250 405451933 405451967
    0x60409030c080304030e120a0c05011b0203151501020703050d05030c1b0a0303200313060b0a06030b040c110c1005041809020913020d0602090414041511090a0303 71
    0x381d6200009a507000041d805140030b80c648400c01010101001a2895002850011341d0071000081000a800b540000103446003402c01002d0005d0400c0358900c00043c04102941c91b104442c0c0008910301e842001d14000d0900c80680d01180e807a02300166035400302c51100816543c080f094510203503104401940d000806001c0603450b0081101c1400283d0300504009022500b0004460b4105500b6100d90340c1281c3d078444244940307104e1107642c01e401d0301006020b01c0203040601e059030100b004690081c01c64540c014000c0d03403403a071a860020300401d48091303c4c90155180c660403803400d130b008401900c8c0c903403110300007410201c8400c030a0222440811420b601401000c0c40003280c1c0f003038013441172610050303000d0001500c0041c60041001c4a44050805c0c02222100220200580c64100d501d144250708140702513510480000464000c014601c01140c2210880040c041009160300c0c805541d42201d000c01d02903850711040d000a20300c19020441d6205912400810010b40101c545a140b90511 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 405454433 1250 405453183 405453197
    0x606070f0206090901081b330405091009060f0510030e070807080a03120c0807050a0207030b0a0b0907080601050a0f020f060408040f0e0121051e0d090803090906040903 74
    0x503011a42070139003038100b07003516005402130482900c2c002c100100d800308100d507903144600420712405810021013100c0c41410301450f42800400007090125002400040c0c07002d0007601c0d00148031359012915006d0502d8850620100103440d1621084090680e200101401103000d016203050340201000e882e05a4140141030002501c1c1405005120041880d40060004085c1600d0018031000a12050080303007441c10400e411425801031a1a1344443c85003803103680d40c40c072068142d00e006c0e51070f40b004004000c21000c101010003140c00600f03d01c4015603a13400f16071a0554113561301c0f0400c480c880c0c0003520602184008500c511810340550303ca0f401900ca07405030503910f640c1005000c880950b100c42c40080d04201030400721201c14020300482d2045011541000c0800e03031944540703c105d04400c0d220110340340034010240321100410071101102018447e1905103242c441131068940f0300450306043e00081c070004080304071400d03900c0c004c02080303540d0744180421004040d80300040d0208a11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 405455683 1250 405454433 405454447
    0xa0209041503080915040807050d03090e0910060b031509190504051b0306040b1306060506070c06141c0509030f03070c021011060a0509100906150e0606070f0206 71
    0x2403403003141c1c00381d4092411180d4440382d2078203102c2c0e0482c0c0d11038401290f00c0100f1007040004004550b1909a079421a0031004201da00d050440c0c0b038a41c540c1217004043c08050510690020018010000031500a4180034290780c4801c10040ae010440710000720301c07181c04840c075551500c1d41000741e10051641c612840f404100080c2e40c12140d003110100c41c5c3d540032120840b01c00080c50b81c2600b203c6001c80003040c0e40c0c5007a03503810040b044054001000e990203080007500f000030350707003110000d088041c107080c1e1a402d0320300b007900b070410052141d80081040d09005034800c0100b40222045441c001208200b155050700e0088000d002c0205001e440d404280401200b81c001700c0003d5003e1545030b034541410019a0040180324440908010180b080c607107803201944201042a82e4400c10800000403150b907400d58003410008c0311610041e0f845e142000d001c4c200400c540c81303200c901401c01c208080d4503403502c45000310110140d8143c2c0d0f2002e01400b0802c00a06500355031142c161000c3c06950a100c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 405456933 1250 405455683 405455711
    0x4030207120602040302190f06050c1507021020160503090a0b03041502040608070c1b0801060e06090705070b100b0d06030506130b07031805060a020c0d0e06030a020904 74
    0x34907008a4071a80c000030200150300e41010022002005004030100b0645810745540c0b40744001d1141e0030502c1404503541c1c00710070050000303001c1c0301100c84c07200046141142c00207444507440da2910394885d20700f00d440d01944000c00400c60501c00740158031403811140c8545a0050251040e003103845120410810b402601e0b20440000180700b903c4020340c40303040502d0211080e880c4a40141a407610504c0300300400d562203141d0b55088003041c00c1242c2941d29604241017986160340d41d10068000305000040c0c0c1d40c0055019000b110400b035004207083d00d50600700321114030203036207030030000c5d20900c0618086105d4504c6241c00010103242c0d0540e81c0da4400791030a95410074440382420b69650007040080c45424014a5405403a4019000000c800d607a2040003000002d004074081680d0307020b14011f998024001c400e81550040100c0b841d40c0740c00c01a4602a46c020661200a400b415503001c3d98140501ca0812400c0c0e001004107095030f89407041e200007904144420b030361040e112401c580d0184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 405458183 1250 405456933 405456959
    0x9060921041a0a0f0203190e033a030603080a140d050405010c030c051c020903070317041703040806070302030c071416170304030f08070b1608070305070e010804030207 74
    0x6010306441c0b500d582508030042c14100d29101d84130150742040041c03070803000b0303040251300c030151450411843e145000f5000c02d141088100100014084c42031000e42c2c00d1401030f8480314055041c0c1c0c81d203c9003440c00d06c030031000c0d03400c2c0e0321009100c0101400215042d80c008d201101d4440100c210b03150800c4000790103001035031400d840c103541596580c030001c90b0b902c4c3e250055100c041c590341840e17403400c11081444a02c41c001c09a030030710241d82c0450006075580e403c3c403481c4020368110004844220200c0e040d20400d612520400a031b1288036000381204200101c10b4074229814200901121754403030000750043e60000389407114020040241100041011400720010b082e40001441c3c070807020b01034000440002e4010100e14a4040c0f0500c100c103200000700c40507070f64800742005111459242281c801d0080b03c00090004d03018408018041484010070003d08020f50755201050316820016811148180c8003000090350002d134400d0701c0d500a0240a80192091044070b8100380d90b14082440c00d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 405459433 1250 405458183 405458219
    0x3080309151303090f0806060f1f210b1809011107060e060907050d15060e010e1005010c0b01030b04020f0907030e100c02031c0f021206090906092104 66
    0xa50020b0008103043d4805008000b402d0b81c41070840c1140e0400780c00d29039031100144654801ca00e81c400104050b06e4048441c414000b02d40e110070001a40074001038034080362600c8030b1007075a4594069001000721400385e603401e4807001c2d1000448032500600303218403210007030000300315640342c0c2074508010b6050720040c82c04e24050384000640e001c0d030703e02c6941000400780900d10f00d680071107401d20040c3e480300e02c00d00d1030700c2e400b40c40c614000c0300840900c00a02582da002d40108070a020000901012201d11141300b48499400c0d408084c0c0c46600548000e1039080c8003512a070003d900510001c1c4464410640007400140111040c1c0103a0001500305c8030300b10b0f02140000c2e110410000924004c12410b13000b000604001c0c400a05d0380e800081d5240a18030720302e0030060081c10151080c0d00107a00449080c04400307020355548401c42500d922003401501c18074040c514110001d00300020120303085000c2d038426130180c4002042d80144540740f01c14003442c60803000e01000000396403405028a1250 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 405460683 1250 405459433 405459451
    0x70503100b0306060d23100c0c1403030114100c170904111606020a1107150f03180b060105130806010303020c01020601030302150c0409020d240501090308030915 71
    0x1590070600345030034048003800f40390040f04021240c00015010400849000308600b203091320681c0c2c01c0c0c070211b140c8002c2045017442c1324a4141d0300500c071540001c0d030f5096240100022940e0304024100030b641c0344001d2103000c4c6405e0407070a503c1d4a505d440d001012120740c851520707091900903620340500f000c0001c00d0105020f00001603030010f0f42464051340d080210341d4400030317050180741c014402780903801c01001404107a000074000303901070244402a010888000449841585580d1072018520310820390602282641764003015280c07003030103081c00c081120b104034800395071903a03101e440d2010050441d038148a000e100c41031005000703000711401088110003d1086501d182006420318100781e10590464201e00c005001103a000200d0786400c407020752018031190368055a100c054022900316200e150700012312030300d4482154014040c9d4100c404401e41c1e80c42040e4004109209003440703414045286000308101040b9803001550340018100b094603c0380d0385280300580840411148019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 405461933 1250 405460683 405460691
    0x306021204050f071d2205030d050a02091c0623040c05030307050318060d0f020903011a130b040f05100614030709030b041718011101090809011107050310 68
    0x402e00404104800c80200070310058418035052040400503100e410036031070741594110011841504403900000150b00e8220382d8802c2c1c03801c051070140d40301d5120300c007a01003540c00d02020940c0c08040c0e2003201c0711010700503d03502c03c2c0b07a40c25074408103030105c0744420b40301a990740c2010300d12184270706200340c200d40e8001c4801000e480c152170f0014032502d82d40c0116020354000d01c0100000f884c000304071240050101802e0007400c000c500021030610842040484550502c101400560b4040c0c0203442120000c400a00c00c540000c49007440f10300001c540c09510807295050407040001c0b580c000141c030a4050320216603031100050400c2561410f5421030324290080f0800c00c109580325180e05d41144ea6031000a01e181000c00c03005020030340b1400f02900384e10403180828100071480c0244035087c0c0180c20780e1604e503601c0745040e5284018166043c2c0c04248041d600814205041c03064015240e0f129071014100742e103890045036154215006100144144000031469640070000700c1580790540700041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 405463183 1250 405461933 405461941
    0x1a0403050601080c01050301050918030d2304150b03010f0c05090306070302031003110619090612050f0112021c06090309050d0203100b0d14060109060b04080d1803060212 75
    0x919080050b4814202900718207600300300760386d206044a0460f2011210f03008180c440b40500035481c01e070b07005e07162803a00c07000030865845641c1c1e4000d4490704485000114004041c0741810a60610071100204920031041054000c1300c1c9a0784020680c00b0701800024038141003e0402d000c64051480300341c04202d000c265a691413030100102a8042220b00d01582541484c624410402c51180002008207441d40d9022546031244400c2d10400001101b282001c480d0200020f0315141050007101c000444c04282a12380492a006880c0546140d81d07901505a03e446c1000210800c4410102d0b40540e040c03089d140072844848440400a006100004200503070340fa0240a20030700c0d50189005241c0d142c00d100141c0e9022815440c0d181c04c64400ac82e014007103c000940711031482c20002d102c40018100000e5540740026218180e07164000200506500c0d6a00207640340034a200c0c0c0340c074683c8140c0350071103603603c103442c0c2800301d85403204101c010a8481e9108401da030401c100203980114600104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 405464433 1250 405463183 405463193
    0x51308040305010e0601150e150702091f05030a0218070e0a030c05010f110d0c0305090307060206011d040b16030f0219020c01090b1803190b0403020c150409151a0403 73
    0xc1350041040c60b240112880c0c7c84540981242066404030384500d1f092404201e4102009040383c083c07a9009201280c0c0740341c0728407494144880c08a008120022491011030b280c203000441c00d007501c0c0c0007050301c58200c00c40c0c445000c500100030a20420082800c5100c580c2d600e0f0380380100051842411042080d5041100045c900340d641e202400030003240c00100c0c0200f100101c0c2000001c9103500d801c00700214141020f4481d441079890194061050410002d1401d50104025041c0c843d107507554030f00c0e802c101c1c10200f1612011b5402900554220000c03d900b45410280000c071b05041c1d09003c0381c0705801e08040c1c41203030090a00d105040d800d00010f440e2151b414813440180d8042400c080c28000d05140220300d00b4004d405070340d6401d40040070301e021540e4007009030424880c50b4098408070010703503145c01c248150b000d440480c00740c49165010800c518002118140706110020356600300344c0340403080d802034007000c508146400c2c0c011034081928040c04841882c152644460a03039920300c1c43c030380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 405465683 1250 405464433 405464443
    0x507060b0a050a0b030a09050d050406020c0609151803070f0512060115110102070c120b10030206070b041115041d16140f031003020a060f12051308040305010e 70
    0x110a2094001c25400d014507502c0000e04820740c1d61140341c403522a0f5881c000030b402402091006000c030301c88d0252046c0b516501c88000c200303541003070742603a420b40c8802091001c9401a41d116a500840c2230ba225010702900c6400f074240c0d1103502610b40d0503022034402003414062160412910f105a9840c01c0c040c81c18590302d84d400e00740002004284941c074002c00c0c822104901e101200400c40b02400d445d103440800d4040c1c407002c07030b0424501902a82d803441c811120340c1440404482ea900345c800000d01e484040005841144d0300540803901e80039280c0c0d21566410b0b40100101d8901c03902c80210b4096464004400d0410a100200c0581d1103081c01007900c09911041c0c1c0c2c00342e1400401d0b040206014461024090f031904078242000056110710711507049000c0c03001c19410750a40801000030911800d40c068040ba0b0027a00c4c0140342c0c83d1601d000300c408281403688000840c0307040003928507040c504c1d070140798402142141c1c0d0980140130b035100c00669106500c01c0c0c0305691a1700b81448106000c0c85 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 405466933 1250 405465683 405465701
    0xf080a0f0203030907031115040e0a050903041a130b0304060903080604181205040e0a050604060905070c11040608010f0e1c08040803090c04050a0e07270b0a03050607050706 76
    0x10b41c01c620b0518131a990381c0b051804010074480b00c48805502d15100c80c1402003150000517245910b4645441c040030058008492000305c1508140200f00624808421034080c2e0310645a00f4400c0300b02d080420842d030b03200c41084401390030208000034540c0b8003500a14040c62068101003441012800e00800d10200a03064602c1603180000d612440c030b400b80d0000c0c8030550720070030340141d1000c022025101c60050b0303444110800ca40c5010001100c0e41580041d10420040760304120f46600d42c05500100e60080b0740c082d01141e102445800030849040a5140803d0000c0000c104c054441d030840c1d094403100c55200700c01607101c03898408600c80c18442c6c1c0240540c142ca0486032928140c43c002e08589000c0d102a00e4a100000480c1c104003091007400d004001c01342007840941000c104580c010072248500c51014000c80b03c0214582030106819100f03c40d5460102031282c0c0c50f20f001c13078024400d65204c1c5e948004c03071b04400400208203202c40751040d02c0c66140c240e1115014103008081d0b5003440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 405468183 1250 405466933 405466937
    0x806010507020a030302100f111e1312031e1d191d1302150a0302040801141e0f061309050d05090901090506090c03220507061101110403110d0f080a0f 66
    0x62041c60082030b42809a441c0d43e145442b65403c11084c1d070045e0070292080c1140d4054941c429040070174100f0481480c41d140b68443e40d540501c06040d40d11030b020708a50803e42000040500c0c0c00c039040c14078408082a0740074030040400d101510003200e044c0e000256940142149101d1448002e460078480c0401584a00c10701001e9043d00a503a0000700e50780f003e8412502005008121550010300c00d80c1503030054501e00000700201c000004141860440459a000e000385a40700e030030329400241e0318003e00a00e604201d0036080d450300800c20281c1c060301c03107117000c805603294410404501c003004460300f0361003a42c44442c0e403185c600040c4101c0d8581608031402080c104014085141c03222410b1950107921520340e2912034881c1038071150782c5810804220100c45064580d4800d011000c00d9640c05c030741141d1910030079100051121400c0e01c051000d501e41c04001400100301103103050300e07220304047e0000e09110440505554008084814000c1a103000c240424900c1081da040018202090200c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 405469433 1250 405468183 405468191
    0x1c080f041e0516080a1104050c07051915020922020c010501120212071d1509041a1b1b280b06010c02090406200c061b07120806010507020a030302100f 66
    0x46c0c84031244c0e8052100107a000d60b036140c002401d028660320580e41c42640c800c00340e815050f40304600e002d41c000309000035600d2401828070101110154407c5640501024100c484107408810100340d11000401c90034002503000c022404400c6000e00c03d40d030182929084900708503120340140051280410301421041e03205d000f05020218442d03840c541c40f0b00402041c402580e40e585040515188030100007600081c04806000412070300c4401c0a45010804402940e550b03034140706e00c0e005c8160742400016101e4104844065085015440342c0004055801c491f04901800c00c0c07400700c001340222a14642149100b00810089049a003e421460034a4107459140c00b0380c0000b510481d01400080407159101214514048055500c1d607100030391031131a030f03101e0580405051303c8000c100c404a034280184141420b01c0500203050369405600810603107000020340400740c1d8a4100038046134180602071080000603910400304002440c800d50103800840d0320600e40509803180805c00038405410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 405470683 1250 405469433 405469453
    0x60201020f0d0504020109150e0f0405130201030e030910020d0201050a020a091512061202031c051218190b180c0f040227031c080f041e051608 63
    0x81c4005540c1804030b1004005250303100c42c40140d4003a1034a070700c404003c0360104c2d001c100880d007061943c5900318040e22881c104450b1402040f00300e82c000c4a040b22054000c0c4441000f6520a03803142c4280c510a2003268900300210002404400c0604070110050f481008500369059080c020f8503040800301c00198201541410003606950b03503801640d40099591f801e0507562807040911201c0c800d40e042e020020315449007101c0c0002141e03104181d00911400d1010500f41e9116002c020003403180c2c2c0c1d030301404d05032482420001c1c0000a00b003d440e9440d03001c03140741000018081c03000d05d1410300039642400e034840d2800c00140d43e0002e141110035211802080e0041c40003165111085600702c03040d850f40b030303495030008009004034015012a8620107141980c0ca04000800328070001d021000c80358510050300340f0b22461210350b481000010442800b0070107a0501c04403058001e4412500d48040300b10050300100b18006a500c10b4036241e015100a4515001c01111100a0001003000d4004010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 405471933 1250 405470683 405470707
    0x28051c02030a0807080d06061e090e0a200d0c03061502120309010e01050a09021906050f0d060e10050a0602070518070c1403030105090105040902090708060418030801080706020102 79
    0x42d900079010300d400040d1390081005110803100800002d080c2044903030f4a0307110080c690456200c500c044080d20000d80c20209000f128520300301c600c8920358040c2d0b507031000c61510140c0540c04d004420181403a1200520003218009410051a01000010b02d2942d200c0010103845007640309203401400b0182c2d01d03200765408107500460621195040b550380c6c582c0b04400d4014100c0000781c240380e500e0602800000380c0107400000184dc001c843c001e2140404000540100c9094410600443c40c10030041407800d40a2020307100551300c010b8001007074ad96440e0a40c020410464102ea1080c40301d01051145141594468024080c20b1005000c4c0c00c1c1008089820120a6003424080158580004020b10320400c1c4a559082d03100382418004028001e145550790028000c1078030490000001040605091055100168004040e80030039101c0901c16142e640c005080d0740d822544a81002d03244401c010280c282052280c0c0d203100c299803400400301e0620301070f508090116401007000040005d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 405473183 1250 405471933 405471943
    0xa031a010e01060e0d050f01140402120c01080a09060908040e041202061e090703080c0a050c01030902060f0304060b0a080d110307080306190504140a05090f03041428051c0203 77
    0x8103090341c3d0500d1084260070214075000a48003042d803690300341501c0b0343d010207940110f270b030050740f0039528800106d030004041502d540041e10100d000070501000035420a0b20740c0c0012020324061080080d50080c1b9490303650940d4015080000300150050901c4204092001c40e07111115a5102410050801e8181c2242c10341000350707060002c500d00030225010a006000e2403008551000103550303607001e42514591660307030641c4e0030f4030a40540b0036221415402802900e40b0590300606039840c1201c131a190540c42c1d00f000c0c00903238540c0e0ba140260300060301d8000298014001c110010071021001c2c4a00800341d805400740301005030010701092000649500a0704c0d00924106d409001c400744010050811030296441560700c2801c00110001a512000c0031600410380818103000580c0d8581d5480d5698840c040c466403035500800c020800703002080c154040e401e400900d071542c0e000740614003403407070b4040740c0b9111000d17980010704100301e10346003001d0b50f080c051070509101c1c00d000300c0d000241c82d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 405474433 1250 405473183 405473207
    0x27010c08061e0a0b07021309030e030f010504080403030807050d0f20040308030f06150f0d0605010f09090b030708071d01061b0201080403030902030a1406060612010b13050a031a010e0106 82
    0x41d91010540c0000c669403000d002c2800b100c0004204640545d9042c000c0c2b000204030135150007401031405404848006002d440d11641e000130200e40741c41c1c03540c0d50864034508014400000c00001b400401c18407415401980c1c541c0402d101d003c90004000700031001051840003410300344940c1044100000341c401410f6070750151010104020300d69856020030080700f41e0805540040200080d21450300c009003020700507003401414100000c648840c0190f40c1710b0000066003021840140307040001c4074054100400c4502c0c090190341c0141e80d240c40d260b02d000469003002000c48200840c001c010245d045955006140500d000020710b00c0000500d05440c110410180c10042c141001405150013a0001e000140d4003071b00721500001e583c100203080c03e080e9249102540107075000f04030720745082c20a4546a081c039070400340060741781c4215003480e64003030408240030340e0080d82c0001d903ea84650701180114040c401c106d84580d41504400c064402c160849039100f160840107100d01c40c0e0202d020303591 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 405475683 1250 405474433 405474449
    0x90f0420010e0f030a0f080c010609270201020c06161709060703030e1e0c09010602010522020a0902040f0905060a030f1b080106061d030c030627010c08061e0a 70
    0x82c464a8008a8103003a8200405046c802400c2c00a008000b2084010907042001030000c00400381c944c508801074603001000201070045101e0702440035001101c0c00c21010b4414011030304500c1202012680075000680036001603032207103a4040c2131100e02d030780c451025072a03c02e200340751562100005000f80185140a010145c3d62181c6481c0c40008100c8012400000c0748942c105200c00419195605005240e030341c040c4030003500009049005010b030314090105890340240610065100491801140c1d04c10303070744209081400100300d5480c0c402800074049009080c080141440395080c10380e9006041c19010324903c10041011139680310703002c00d400381d1094442c904c6169004a0002c041c0c0a82c000d1541c5500e460740008980350042000c295003108001010102402c0108168540c0c0321141c441d030305500a000041d445900b000c0000380c0968040c00341e2080702c90118019400c690016171458082280c00c0244202480c0604030b400d00c650440003030101c4101d401000c10f81c140b0b05446400383c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 405476933 1250 405475683 405475699
    0x50105121207110604260c0a050d030309080d1b1b11010e0406090b0a05011806111510181a01050a050c1006060809060103240209090f0420010e 63
    0x4108052020300c0c06442c40c00400c259140c6443d030b0a20403c406e088141100c842ca102105150440d40c04a150124208001c010880051a00e404d100c1c54070000d201c11010980c0c0c5031000800503007404060440340203c040002000e051a8081071824402400c0203c144081d80c2259041c807040b1403540d52100358004601088600300b203006070790151100d030440c0d40c028105400030813107040c0381d030110003141012542d1075101e9503650019503010f96021003085050345140806d00c4400d0092050740820907103182194065001d02003410b04001082c0ca1003188a801d081c02003021116a000580018036441000c01481c50300d21105aa048541d0310342d24107104020400080d090b02034001d81c0c6008082c50b00b43c5985001244800001300000d010b2240414014030200e00802000540740381a294040f40a900034040468100b27600018500888000b5800300840d81194a84c00d82003400366841c842004800c0c18107140c01000c48620241c21080900f02104c40d440580c0d00001c841c00c04401079484003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 405478183 1250 405476933 405476947
    0x105030a1502090f1002010c02160f0b07050703200a09020a120c021e010e011b0c0f1b06031b020c0d030e0402040f060504030309121a270c040501051212 67
    0x90214404c0071a0260320100060741099555019001014601095801d46050038a41c0452201c142140d001e078110301c0c00c0070390040c00340b01420002040141e0242080318422640c0c1c0d5110400c001d4904005400b81d003000c0312041aa080030580c000182040304801d60601540c800020308d94030302000400707101d80c0c03240d44040c8018000d01000c04c0f01d11124000d016100c4999010602821400d00c0c1e1000a40c41c1c100100f100109180d10070b0300000017541c4141ea01ea6280d15699114000780b03100f5035030700000828000003031044500e40b00041040d5100802d100700540100b1000740354584408042d5006100366031415620b146e4900c0c0469403508000e0100006200803130004e00841d0844800300403010004103419030803c1c060411280700b41d8800001c10b8448401c071a913010040002401400702c001501c00458002e00c4050340800b100f10100b00b86e03075049a0445440145980c950051f170000c0c681301007107003024040c03140505011f9070408402500040c1c0d90761b40344503002075034030007482c041089 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 405479433 1250 405478183 405478189
    0xe01061a1608031e0c12010e0a0623010e0103060f05060a020109020a03110907030e060106050a020c091f08060603070909030207240305010e060102101109090a02070b0105030a150209 80
    0x1100c40c281c0040c6110f40702e10340044648010221204903000c800420030026141584000c105e03100c03030080c00346641c80d80c0d103443c1100d6030001c1c002d0700100710715407602c4012561109003000c49210b2a0400c0003000155100c400141c40c1d003030300f4910541003500701282031003101c2010940b2401c540341a100c1d2030f507900d0b5102040307004207450740c00294410140040001404480141500000d50440e01d2180c280ca6848060703003203541d00f500b2270302c5070780042c801044800d0041d070281004484500542e00f000b05000e0016600380070490340001c03840054100c82e80407025031094100500b5050008214034101100000c4c0c2c0c4109902c0340354511615110202d007010310902203100140702c00c070300d16040d2040814018000d1001c025546000038602400040c4c50841d04420301d00511040e00070b0490010220444406024018540c4200325000c0000c42030a444640c0c0107403240d4020303400185c035082107281600b034403074040e0700992103a4401034a502c0801c60035000182c04151a40c0010b035155002c4004c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 405480683 1250 405479433 405479467
    0x309050d110105090d02060408030301081504030228080a030f060b130b070606050909010b0319030c3003061505070503031801091202030c0d0206091002031b1603030e01061a 76
    0x82d01f0240110b400101000b00002860503241c3c500d00380c0d00c90f00601c2d104d4030b100302d2007201c2c003400507440000b64072020214062110b40d14200b068241030140e83d581c507041303076640c031401c50100040d5950079001d90304111489042c015003804a502c902d0306112802920b01c8420038042c8041c0041c1c0065450200051940440c1c02000d010b051040300b4940686598000c00004004500a02510156491068070011504e00f180c1d403540310714908200743d44550381c055403210211001800307000301c400c2c1d020110326190f03520300d4916a000314071981011442090054503610581c10712000380803080c0050000f206880d8092255200d02080108a00005014210340e48000d802140c4044041d1041580071000f40a441e410404941c468581c4000482e075646044031544a00d8010552200d20182030303400a40d0403250803d940481c4442c0e80340c00007411b078400e07580340c4486844060814201605802042c52481c2808000c0002a02d8003984142007204403e0010f54110001a0614800b0f05051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 405481933 1250 405480683 405480709
    0x50f03090a03202e0e1c03020a02040608010c140a080106080405030715050f090d08130206040305010e07180209030705010309061407121503050a1e140a0309050d11010509 75
    0x100800584d500c480d448004030701c00c55808801841510b040a900807103401c0444c0101402e402146041c00c1e005d01142c0c00c2d0300c0c0c4204c086001d52480310015a40e14026003000d00007d41c00011a90480800508403010116001a41035428049158050f4021112604440c60383c01e1004042d40c0b60301c0c2450071032094810080c070002c004607003034020502903400b0074410080f11000c41c0f4203496490307400d41d49143d82034081d000901344030001105001714100c0440e0481c4040d0034107041c943c980c1e5440b82511440a05925143e00180f02005010714034000c800913401c905600f10318245008002c41c1e11511607000c2d140c14941c80b5800041000801d41c054003064142080b07040c00f83c10b000302c00a04038000441c0c0300700d807907041c83ea08194909050755881c0480380e101000b407000c1801a41c0d040381216030103280c4040ca0706580c0940f404203142c071803062154481c08014021090765840c0203131013090103400c0b142c02006400c2110f00014210707106049004000d0a0807522064000001a510750300a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 405483183 1250 405481933 405481939
    0xa0b0105041e17010905100f110d02030702061e06150f12010303020c0f031911090c0d1b120911100e04050c0901080c0f040308070f050f03090a0320 65
    0x1d080302c451081d40004105441928801c22140300349102a5400c2e5402c0040c0070700a500564090f0280c110141c1c014500d604460707402280c10003a845215895407ca800c4d081e05580d000804c00c4a01070b414048594400b103044446007035542025400300751400014002030140400601d02d01d5002c1400080d1010380c03500c8410b15907039440c445c43d002e40000c02807100f00c0241c0300f6030166884034546681c001c02c20400c0600240052001d2182440c071400720301005850500c1404036403455619525421840b440c0c46040d5140d03555a403400003c01c44e50040c08250308902c00d80b1380d00038440d9100080c0c90549000000c00b180c400303c40e042001c1c080100108240d4444130760980444003a411808d2101c4140040b541008296a45503444180c4c1c802c095509000805181c000b03a0000f207440f026010300c00315004c5945c102501da07583c20107164030002c8262088600105410304000040000301c170762200d80390185003000c3d40701021800c000041d02009041d5041d90700514440c4a0410300c11184010003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 405484433 1250 405483183 405483209
    0x16050d0203270106150c0606030605010f0e0a061d060f041a120c0325030503030708240105030a180506010f331b2001090e0c030a0b010504 61
    0x100c802e4400c01201100015000a07480e0040396044c4181021150f41c003610f43e04281440c1e6080380c052505e403800302c600b03aa03a008084049125440342501808250a142d01d5190820b2684c40c2951401041216010b0401506100d00d6008560500c20b00c0c1601c1c00868464403040d000419841500e089a60410b25020a80f0b40307074a42c0850308403188205851802007035856001190b00d4031244480b00f41c0643c80501d42c9119603600364400106075445210200c24542c51f039a03024119882038030b8000018981400f0301a07280352007041c55994030300490070401e84140c0d00c800a0304500005004070030b565514641c9960a0f40c58140c5200c0203603104c0241c0d0800c1d0384800c030719007003400e403400350001c001002c205031007164600c001c0070250090380a499124072005140100e0341d078000544c0300f00c202c0410050b554005041001c0d2200c0d583d01e00010034505c000301c42c0004213480341039441104400d01010500c41d0710601c0100f1290846110303080400e00500d0140161400d12031907201004030106 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 405485683 1250 405484433 405484441
    0x10903030506120307020a03030e011101150609120302061503010f053d030209150d031205131110170702010204060e120628020406050d0f0e030316050d0203 69
    0x85035000760310681d811107030350500c02844181581e81e07029200c0b0080d0400303018042030001c00e02450302c88240d59030500d051a948043c0100b068207540340c40c070901a074a50b4181e4184070042e04a003081014205030340401d0130086480e1002550707880041c00b468030f80d0040b240000070310703102074005650017030307201400b1302083c2020300f92070160303031415400c90255000c000c0440c3c8220318181c0704140311020403810803122509540800092440140801034004000142c400440e16080e20202c0114000d840d18480030010030443c4c42500d00040c6028842c0c4101a42c160000301110030704291100c06075420a29040104010b9504503a13170084044418204401c000806a054000b0015919030ba0317101c408802096082c08003101c102c1c41003603100d4001d13100241038a00e6034403131801207040c00031135185542009483c11089a001e0740102000450000e9901c1d01d101c00382c0141d480b0540d07540c000700f00d51082014400d889001c0a00340003400343da02e10074030311001d104806413900b20f10301c0e0004550b0f07410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 405486933 1250 405485683 405485687
    0xc050d0e070801021210050d0201020a080904091e030807020303010602032a031b0c0d0b041104061a1b0c06190509090a0603050f0d0519170108010608120c07090203040f0203010903 79
    0x160441c6c410001036141500826181052124802095410380081844041c3e503520010150000c0380b1f0117400c290f441d2943c01c0420f00101c214007141c885920749501d003160078200240720308030050811095520800042003000da0010849401250b5081911201828020350101d41c0407641c1ea07001c0a0b10022540a256442c52441400a8543d076801c903400c40810009010150b01940c8000e08000b4030030700010040b4080c0310318403c10301c00c0100009503164a4501480c00c0d50802001d40d4125203000c110840301c07084503054071b44000c29030001014000800ca0010703400b8402d060110640891100c1c1d9400210300590a5910622005140c4800d41c074000858030020a0184011b42c0c09102e00034961001c1d01c0040782d007042040c0079982d20751425111501200240402c5003004080211a1010f46a801018480c00303020380152800454140d2905a10b1440d085010342080003010b810403540039a28000a9400102c1f10149805a00c950303440c00d00c0001e045090101a416500348401801019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 405488183 1250 405486933 405486967
    0x906060801021c0905150603030c0105070806030c03070305030706150f030312050c160b070212070501020c0d0513060e121b04050a1a0f120703030906020d030c050d0e07080102 77
    0x414082d143c4003030300410060003020703a485001e0281a03900b22103c4205004c415100340c5034010070140442e40741044003209a403c5540448214001030482c80078000030b880d05101016001700200d0090800d00e080da01c40640320300c501c0400a2200790b0301c1704240380c042a06403100c0b008240c2c0d804171441c515039a0501500700a10881c03070400c10741c5400c001661a454420503034098500100e402401600305a4980d130000002070000400c1d40b2501c0001d00301c0c0302d1030400030f0101a21030713400541c44621001085140540e40d00c1e00801703005040c04401ca0301d0442e00e40440c11206d0600d09504000141e1000c6000304820000ca4055030140103400d41062198950742d030f200f8030059404016540d81e1138001d10869044032030001c095415a02c1a11091601029059002200519020210086104542c6419000c0d0b10403030114541c4041008100d4060083c040a01e580f800c040c4101404200d00905612a86c11071804c0141da5006003000c803d0304200280207448203900856440343c070440d41140c0c01c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 405489433 1250 405488183 405488197
    0x60f070230061b030a2708120c030402060a080a1503080a0809060118050429010303090e0f040210090302131d071a030712050103080408010f141306090606080102 71
    0x140c401d01012803c1100c81c62600c01c043d40c481caa965003103440340303082d543c06098215400c8140d141c0d019851000014181040140d0900c40c0b0301055880c3e941c14912020801c00074200e904014041c010040580c40c0c1200301d0308221024545440c50f6541c3d06103010080074080310280e40d150600f4004800c000c42100180038401c3c150712195402e5035040403a581e03406090040001c0c0941620184940050b550410ba0f081481f031816007900130040c5900e0402041060004142909910010424103800803442400707842580403030b04091600400c840c103000c001510003070140072804484403801e8491000000a194003c21001c0007200410244021785800e0003848400d50041c10750f584c95140000d040b4040768007142548000020540c80380b00075130801803021050101b40701c5180302d011260721505010b184510b007101d4549080c521a2800c41c0d1050b025048968500f071200f03507200590b01645075211141c00c210700c003480414036000c00641031070f91000f01801d06201c0c000c00e07428030640180c030301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 405490683 1250 405489433 405489529
    0x40806010b071b0605041203050c0105040528030824090411010906050705060a020f040b0f030a0f0e0c150c010906090b100b0d050402011e022a060f0702 67
    0x31101030f0b81e800383d141c01c224402c1001080d03080108200051099000c2c862242c0241052030030304502c4074000d03080d01d1007101d003100c41c0c1d00403078981ca642007420154000e452903002440100217040356000742c01e40f00080c120724010b01190095140b0703581c0e400490449014050f01e4403c05041a280c0140c003150601a103901240c828040456107030f20440039154184d42010041c4400d442f441b500b000298007250001550701000c100214115259600401091142c010340039602c0c078152102e031045415008291100504010742d03040c0d142e800042042c10028100d070100d440446850a00041d071059a203d15440e5082200300000d00405601c000021802204866041c1c5da400603408840b900b0380c0914040440c0901c41f039440f040e040da1020fa806031040c141102884a240325004110a0900000c00141c0c4840c40346040800a440203031900f1409400442400340503100141d280d004004031402210030220350041599100081c0404400c000c0341c172140c0010881c403079011283d40b5030020540b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 405491933 1250 405490683 405490703
    0x100504020301200904020d1112070315081c21020315090601092c0f1005041a0108040609080a170f010e130201030f0e0d0908160317040806010b07 64
    0x1190304201a1103e40c140c040c3e03190302e40300c09241017000035041906200000784c0d495040250003100c04008205080451703a02190030720300800c00400350b5140c0f04c1a0241c603494620100299003000a851004c0101d10398585034502d0102c408441c0149240c081c4d800101650418902c0407440d40d0046024440b81e101004a16a420050114540042d62039500090320944200640c003041105c180104258010090082ca0350f80700700a07607458182e0b100040d101d41c103410700c1007140540101c5c000821b42601c05204518042c030720460160a040843e9040c0b004100c0011708001c3c5642c4032110f0190711010980d241e4942c0c2e2001070210741d16455540d1300c0c0401d40c000c21304c04603222040343c3c101da03034102c01c42c0403541e0740c0350078a121410705e410101c0c10f06071140007502c1c0c484418041d83c0e1400203581c00404694104080050155965900c44e01d02074112003140c61200059410103800c3d02d400465200703142d00945c2600c1a14450781d48441c9203401907100200d03482100c54002d00d8140e000d214256 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 405493183 1250 405491933 405491951
    0x5150a060312050c0c061306110606061c0e030a030606030c020606030d0f09080d0e03070e060303070f08090a0806101d070302030408190309020111011503110d1b05030106080f07031e05100504020301 87
    0x142d0394070415a860ce031b0016051142005c0c47c08618107500c40144030500c0460401c2c0104101480c540200022202007a104c00003800640d40c903120315510804140300814050414001203030322610f5940150f001c00c40b5450204100c1e50003086c20030024005d0004031034401141c544014041c800c000303d154424000d912000550000311101c1d1405004014041d515100c03095681486440400200301c50b40c200c140140180d0f6502c5540903002080c0000140c4424a001c0205a0462609801c41d6200c0d0906280c22103444010041c1e05a1204035400c0041c0d9039203072030408801034083c501c0010203403c011004170031801d134140c100c00b282500c00e80b11107045220720442942030710725100107075070807015480c81000400c4e0200102c00c213022026014502e50b840c41c0d00d61481124007001c00030000d81040004000328202407054400030203110000d80386044604078070503145c400a101c060320842c201d0f0301c07c04820303c0200b070f040d18035503010b002c80e201c0c0110882040c0c00382c4000c550692082d480c2000e80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 405494433 1250 405493183 405493217
    0xc080c0a24060b03100b0a1704050a140307030806101707050c12040b090108060411070606140f091503031c20041202130204030f05150a060312050c0c061306 69
    0xf80340217280c24a111071425042c0b0007000080c0c4c00000c2000100030303020035200d01c50586030703003518000c50160011b82545005403c08540c520071000c14030600d50f008001003000310f43e203da501da401035421204481e41d06900541210f40c41840044150110000d10902c850650044010940c4031702010550f0404020300c0707011525801390b4455589210740402100c2c1a0350f124600311f0b54010707001440043d00c59001e62502d403144d00000b100321003042c0d80b01303000d010006113000d0344560b8580844204180440100c04500c2e0f9900c0501540c1c0d052120051a26031694288143c99454071000314040c42c002d00003e61501401c840000214900780c0d03000300d100410503e03030448054807864460702d42c8481c0d0960a0003c01c0a03424050301c3c603940e0903c400b000060160000e00c81c240d0042e00204800b10b0121548031650101a04001c21a494040100b00180b00482e41e002c0043c2c403030501684514026411074240b6560710749440e480900012600c00304400041c02800751100d550b101c0120555040310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 405495683 1250 405494433 405494437
    0x307021504152303061f0e0415080706050d0912030605130e07260102070302030a1803020a05090a020c070b2a0703060c0908010c0e10050a0c080c0a24060b 68
    0x100b07562410840f128222051a400700854002402900c40d2405000b04184080e18150403101040040c0742c6810002d600c2c5060301070100041d0041d1004103001c0d250880c00c642e103030b0b841d100da18180800420442a0024030f82c0c460500e068100c600c4c80135014258a00400600f581d01071548544080e03e4203240080461041c400051407800003052110f082241d110801c5451401d200144a101a00c1600d041820700240010b10300c26002561035001c00c05010f0004000c540380340102491180b0208090303601c0c0058030b81114002e640301d0002e0f4440d1000705019206262440280d440381c240d00241000d560301c000e002c0126100e4200401c0341030b601940864101c07a0104044540c0864414004906990300504820119040c002a0655586186825079403c03005500100d003401900003040c3c1805d009940c034144143c502180b500c080008040c050310145100900340310b00104010003128002c01a00350b40c1500b09a0044420704005500c28540b60b400700380200c450f0505500040d05a80001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 405496933 1250 405495683 405495707
    0x2090a0909050d1107080f01020c0d02030f030c070f02090f0a0c020f0619020717070203010605041b0c151a03190c0e0702120309010b1905150c030702150415 69
    0x2000d031040b003c0e40801280c15240100962649003d128000580c812042004030041c0ca20300d0b001580301c1c0c0003c24118284070410441b00199002007282980d1000d205084070b034000260300300107441d4031444c1030400341985141700080d00048903400380000000f030b000389644207120f4454140f01d44440c40d20103d032a00b880d4a0b540310a43d01c810085600190f402035001c1000b43c0c01440142056150f0701c070070603090300b080701d0f54000c2c2e81b0005010066040c20700594002d841c0c1940c5c207100540002c078454080d82c10085034682080a50b1900004100054040c4d0503c0c885a031028007003400041800b07240300c5540424a1b1281c482c003002014000d040310321103d0000d800803900c141c114908a015151013100400003400c5001d419001d03040b000d255406540550f60405c00001c0d08010b03002849a0300031113050000320540c402908000c40e44c0c2e0080321900c0d149940c50802e0300c80245807409032850060300c2e0001d6001744415040054489281c001d8422a0b081a11541c041c0450160543d071000b900d00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 405498183 1250 405496933 405496943
    0x222060e0f0d020f030a0b0403090e151306031b0f15080f0a090f03120c020606100c0f170702130b01051b0a0b0703150e01050a051005070602030a02090a0909 69
    0xd03031004454503118860030b118a0000d81498243d03111140007030709080c00640215024515041480306041e40001c5400241c0081c000300081803c00006002185480d211160301c10320004101c510642156001103008580c042c0c428402518084207090084590b8003074101101030a02002441224080400b00d480c1e042e038a840066842e03484406d25001001800c450389076440307a4500001802d51800880228025034844034108226404842aa403240c0410002c40d84068140010740d030b504505041c3c030005500b444880640949450050381400303c1002e0700c84a510015406440c800303100030b004c0c2074801c4802e540c1007101c145054085030441031589001410500140d0124600b048682c2c0320000e2080441c0c6a0b19072070b94590150500c1114070200003030300d6400e41b180755921001e0420240a40e10341e8000d4640c14403011030040c00d113030300c03e2034861910f035456900e503036001c0c1c0708452615801610955032440d260000102039844007840e0741c000c2d4400361000a480c0c0c000e11510500503408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 405499433 1250 405498183 405498199
    0x1e060301050d170c030301051018061116081b0102030307050405090a0617010b030714030a080a031104030804030b100303120e0c10020703061d0607050a020309040222060e 75
    0x101d000e10088200c214012146214048511190340c0401d034050104031050038025542e030741c14823040c8202140c003030038054103110005880700610b61945aa144c240c030400d1030100b00780e071020403e90b032030240400400e028108078540013280d00f24012811080100c6a0003210560780b0720000120f0343c0b84400ca40800004405100900c25850401c070786d290407040d44800030409a40361b00d0154260095440d19003030b6a035450343e6518160a003408450010703c0031002103e902d04000300401e40314190218014405c0350700044503101e0034000d40c004182e842500d8003503a00d4075183d1520602550060205842d80c840c404001030501b07800600c603500383d960613a1506041c0c0030ba00340b08030240001d0b8808041502a0002c89003170f640f5a1103180207102c001e540200030117851810010b00700c4221910714810700a458002042c000c1c4006680b640001d07141c50310361754030b40000c10100d00314011101140d40c06400003c150f1007910081d0091300d410512511820f02d070300c0d0344180541700348942081e100d80140c09 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 405500683 1250 405499433 405499439
    0x110f031c0f0207170d05060405091002030406021612030608010516050c07080d03151401050f0a090302090703090b070305040c12020303090a2c060108011412100204051e060301 77
    0x840c0c118000c1840786150260030b000c02c5680f00c1940b0414030030107041ca110049405c4003900c500d40541d6811000c1554104002c3c1401d0340419103541c008038a0410854000021400f08185170b8101e4071072400842c0c07110844076503482c118440c01085261700b00004d0070410089608241841407902070100030305510b400c13240c1c0d03c40945040d0001a0280d80034099860b00040c0c004042c03044c036845a4255900080d039a502510800b20b0b0340098101e0f42c4005041c1d903c006460740c00c0004c0303a2000d910f01601c240c4880101070211901c0d0703001d4200a4114540b03900340700c1e5440c0c264201401c4144138114540035a038800c03608034100c41e41100e0152160000c85410032405010202c61384907640040e050324500b100890100e941324a0983c01010035000700490640d00000b901c0c070b410b000018540d2004401d040240000f05014810b0248201c41da6602d284000d00d0340e1000c07030300e121084030072080d58218240c0ba54580c0c002c0d0007034803d00e40105561134611111010948558500c910010711050450b42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 405501933 1250 405500683 405500737
    0x1080d090806060d02030f070902030a0c030e03160f0c08030702130b090f070306120f14030a080606031003020316060305010b270402070515060f09060d03031119110f03 74
    0x4d420324241d03054000c180c08800e1101c000e110220151058010140e40d80c2040e0700d81d00f040b10f2070103100c8010103180c60f413803442080010044424603996441c14811080b0141080640308040460040c02118a09000101c240740030000c0c0c403110740204c0da0b50f40c0340724a000150040e00d0600d107007942e12190105c000346c204050720508a40012043c900000c8040c1c840b00d041040107400c080540781480d4154803007040100b14250f40d503001d90f0704006182001460480601860b80180c4454400c1e0008400954500702e09210680216001422900c8414180b0012440c9101a002f0b07071000904003030000c40d401a032001110b400311030800d00b1044008003000d1182a10a401200543c031a408210980c04900200818400a103c40301c2070f031120b00b13001c2c3c2000118469002c440780120b01c030004103e603990340d540c64003255542505011442e203030740c89101ca0062042c1703241c0398144c00500d00d201160300d5118440d0f01e02c0c84070b0f800442c0c00004c154500c2c282d82e4029141c4200301301e041b000e160a1114 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 405503183 1250 405501933 405501949
    0x60414011409191a270c0a120204090f0501150e1c020901030803070e04060303090905151507020f0d0b27010906021c0b01021207141501080d09080606 66
    0x244010403841c0e0142a02280c40f400c0c0d4407106050314800e03e409070240c03e0361600801d184070b19001100b0f042c50100382c91313001d116504402042100c0081d400b1030041d505600a04603182c08000700078085581d50303110b241d250018510b010520003018640030020800c1540f4040c2901300302001c0d107442d83c4401c601b0b401c2003da99503120811403034041041403100107072a2803e00a010f54451114207882c1d241480c4000c202b00b10107800c07284121b0502c2d4040020a801107410000d03500317466070109846d43d0300d508030840c00000d0150a50041d000441d41c52030070f441038000e4503e05200322000e0840030620341c10800c141d640001e02508101000700071038010030004010074142c0318070b000e140010a00e03c000301400c565000005880c465000204201290b2180503850640540c070b010400c0340900c2800000c3d603c0901c2c42048142100004015040c82494403604840e04034940c1102c02c030010307a45013800e00d01c1086c8154a403d01c2035841c2c1d0034440d40100e002e042502c17400c5000317005a6440c9000c00a0074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 405504433 1250 405503183 405503191
    0x50303030c070f12031d01060303170a18050309030d0507020f0405060d1202010c200a0b0a0b03030705070f0e1303030b0d02030109110f042c1c0305060414011409 71
    0x1a4012100c00000c4c0011545240c0099030b030b100040c1403004004424180c002c01340c18605543d00d459024000660040004201800d050080c030541e599184e103050014108100c000024040c0261503100304007000006042f421001c1e001e5500c0c0b4504c800c02a162402005402580011459164946420140d001d96072224000b0a10003540c141503c40c1131034401c2c05140c40c030050751100d00d0400d2580e04510007445031061040801c0c1c03101d5805003401e88400e00124002c040740030100201b00d8010581d080011400e000405503980c4400519050390b035042d151051105a0036031400014010004015240c4120b4001c0e0051350301d4a00c40c5c0c2d048004100c035081c00c0ea40459071090100c0562001d100742007043c3d100b03c0c1954900840d8000f08a042c02c080c1d251075100c0c50401441100702d203c56818541c9180e40b0394440b0341161012040c250071f003030300c1e035114022110718a200c0589013981604001c0c010003007510104101e1254141c4c0302541602400740840000b1000c41d0080b032401d0130300c8000d41c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 405505683 1250 405504433 405504443
    0x50109091a0a090e01060b0306090f09010e030d02030916050a0303051312110109090c0c020904110603040b070f020312010b0318060709080f0a0f0308071701121209050303030c07 78
    0x1407640d11500207142e0b15020741003640c010350f4904032900764490910560780940001800e01e4214600000003408141c070050030f400409004801046c2940c00940006984c0940d00d07099130346491b00c103d4550004c1d0421104000c0511440b280c021407010311f0341c241e8054072005040c4500443c2140c1f0240c80b80e6102d0300040d58215482c81c00040d151645110700d144803072280400c40d400d07000f02c3c000100019100e81008030014030b481d42284040303070410b004900c10395042c0e500100c140c1e614108142590204000145c010310004108400c01891001c0d09200e1600c0b911111b001100c01c2c0703001c0707a50340181180b1082030310048006003d0406c00b0741c05075070700030520020100101d0b02d814140382001d1040c0c03051070100d4000d44040c000c036141400b4620555003110001d014003d2140c0302c0107a171481800019007070190700030100300154071170103170250b02d00d01c2203103001d240d969264503050b181c440700141030700c0084141b0040c0040e9845200c5000456000400950841d101d2142158056110060072070f1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 405506933 1250 405505683 405505721
    0x50304231509121906061d190b01020a020613031b0501081503030702030a03021b0402031311120d080601080601050304050c04020d09140d4112090f1605010909 70
    0x141550290130090b140e5489a8008500140740040340c0080710b56032800e0000b000d1606c420882d17442041c48291014074644803000c103920880e02c00603400d15005600c080c1d081480081c0303d000c10b50001c0e200d501241c0c85034403201070b05582d12001c0c1c4115030b0382c0d02030580003412201c0400d03041d80c030b1544e580c0e910b03e40c01001c0e649001d5050780001d2820704001c0e0b003180542c10a60002d00c00d451002c409171101075043d5800d40ca5490500410307400c180680c44010203903403c4a400203419100d01c030208005040003002c030740c40e078400080e0240c03d0705411200e590028001200050655110b001500c0c01503900c031005104041500d0308010203500861120091640d440c07410340c011501d0305507050865020354000d44500c910f580d50050580c0580464000c5016041d0110f880408640c0200400010040b0b02802c0e1000c4004d22000390303120300d40041c045030b9204820300c442d6000104204c0c0000081c1400c036141ca0649800a08580c1c00521504d4003140000c0801c20912045410a0007500d002c022072403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 405508183 1250 405506933 405506953
    0x605030402101413030b0106020d0c0213060302061605010f11070b0403020316060510120c1e270f05011d0a090b0f07020106090504080a030b03070305030423150912 72
    0x182494200041480c410740c04501300b0000d00526480b1a0b01500d594400303001d00540c1d00602030081d542c142c2c00240503810030085402c85114640c010005554014143d590f02c0d64500318004001c030801205451035441d000419150408901c1039a0500e01c044070200d041404507210580d001e10024026003e40c0030810030108005d50030380003040b10354403d4100142d1400c01040d0803075203562541240321099080100400401c0220700e80008a0300460a00c4012540301c15a800700810154044840001006080b1a83c007181c00c42041e9140c05032442048803103052000710702514005e00c1000780c0301103d4181d0310480700c0c1c1440b005512035011040850004200e68501240e50f5080b108021044054803d11640c2c0d9828010b0b003000300700a24042c030560910f43c84521191150041e01c07803e1541e60303420040740d6102070100000954114007038035100c680d0340040e001a01e0324050044c844007040070501160b8504981d45645042c40d001d806810701001a0a100980145120351a031500c1a5081c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 405509433 1250 405508183 405508217
    0x40c090e0709060801050d030507240c2a0206030a090311030c0706110111340312060504090b04080306060d0507090f06030e0d27030b010f0e01060503040210 69
    0x26010740c10580d60150440e02d071034802415800180c00243c801c0130014151008650300c0026251807607000071100b58100118021807081120074540480d000d4148498a0701d229045a013503500180d0312904004643c0300742c1001440041c9244000758050420700100b0100c91540d8000140540b29050144a400e4034041441c51030b088429150b101d0380c00b0310f10601441d607028680210f510304a60080c01000544110760000e8012050b06101840081800410101800c540e03141d510142501c004040700c4039040041ca04866031956113803ca0030701900098a08023803240b150090740080004a00ba145d079651010964005040365900a02c10700940c1c3c0341d01154401c16008403026103c1e454100e24110340c03011541800e0b40a40c09251401c01c04e880b50590116101c00780c81414501518400810310000c01900110f58501c1d985d49050361010081080500c54a8162420030702c50101403955030010103131a620900520000070404d0010400504101e0a1411a00c50500b0481081d202000c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 405510683 1250 405509433 405509459
    0x80606041a070203010c0f2c06130501031a03100b01030e100504030e061204240216060e010c0203040b03090a060e010507031b14030405012a02010b180402040c09 71
    0x500c075506000070804114503091090300401e05442c1852622860081d10142c014554134a4242c6c001910950640340a40e0324240c0908031840103241c151144c4442c02c001254449500406010a20702820020200400300d04140c86410090042805601c0040344201500d8941c004606141d00c410307019149040503c1203103a401400d0750300081c1840c1606004000b07003034400d101406140c040042000d0320301a805d065600903002030303000c00201000700c0035400080410040c00080d910108002050062030300031790045030300a074014000000c45540700740c02c0380c42140030440564400c1004104054050000d907038083c0268040c0c4410445c00c0d180e03581603030101c201001c11a503403603040211481c0c0610a007890320f01081c0224036004140c00004d0140e405030f0502091004000c00001e013080b1094000e8040e80483c41903142c0c0602054034042c144140c101070b02d00142d401c05807424810700b402c05880215402c00f840001040d1290380a0200070000003100b1030400c903040c00d02181f6880756202c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 405511933 1250 405510683 405510719
    0x905011d07180e071706070302091309110303040f1e060203160503040905013b0112050709110408060106032007060e0d050c160b19020703050708100b01020a0309030308060604 77
    0x515009001ca8142e40b800c0c200b001f842d60041c11703c10701c086c46103903e07103a0380d0b40308180c080f02000400b4100d40c1041c040040190407180d6146c4030001e0080f940c140145010411214044030800801c041c0b000a80d0682c40103004940040e0700030b0225101042003030520885903402802a80c5c41c3c84c0c0c4401194007070b14400d0308120000d14805922800c54075824505101c80395465503c0340107001c144490781107410040c408d520103065145000800d001e414001c8000a18402d2000c0212511181aa0420350400d20400341c407405002d0001039079038007174051136290110300601040d410ba6400300b00034039900114002d581c0550355198543c507201c02003120020580003038071113680f07034100280c4852070700c508440005121441c05400300601900841074650710b54488160310061404181d00700d14114081c0d1003c0d00901c80c8100000f20400013003410711a4859001d41031048548060042e42d440580c9180240002c05182d000c0020074400c0300c0507608510f00810941ca0282d40e103003101c902140356a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 405513183 1250 405511933 405511949
    0x30c03030509010906030207020f040c030213030501090b100305060402060f0f03150f010c05071404020f0d0509150c030f0919150c090b120c07060f0905011d07180e07 73
    0xb030142040e60700201e20328024140c80c80c06500d030804a6020640241c8181c80d410301468403200a154034a000c0d07010364107040100161200019030707070b04145002e03202c40f980c2a0780030608080416614280144081c00b5030307420000802082c1c0b1540e0070701c082c0c0e43c0100c0d00c492240105220f041000c14070100218040d03a100035880601c280c48004020264a2242c1e245060144d904110301c001500803d2100440f000117242c03010ba81103120111713010b8442e10310007407a607a40000e01d140c2c41803001e500c841d019241400448040100c941d8220072410785c25648141c4c00d20007840090800c04a031410f490780800542c00341c40341c40d20741400990015501030302c11280d086103e015403e4240c110700c202c89038461145481144603207456441c180710711881000348040141c1100162081c070382c4000715040c00d07a010100304038400d00d80c4400d40060400c01401c54035542400742c018808a0440340f400d07045500d035000341843e1864421944810b840d456100c42c07a5a07200c2e4920075034040184140c900901c0d0003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 405514433 1250 405513183 405513187
    0x408120a090b0c1c020d0e0a03120f180609020112060b0409050c04150c080c070b04050f0a0312031a13050708090105010b0702010e190b0408120f031f030c030305 71
    0x524020700e042c1002445083d005034240840d1034007440c40030002840a401c42c0f00141d603410074400c0c24011301a1850b40c03030700720b01c9240748a40070940e0194000c03160180410042044003110101c82e4195003203440c0704c14070640060b4159000c210250300039000544141803050100c01c010381842c094940d680c0c803c0e41ca189010030204808030890042d40c4e405100c20203010b1609003058004054030300300020400c10000b84007420410005890129180c5404120072125016540e001c40640c9074807e02480d4002c0d4480c890410345820172441880603664040305003034103992020021802800c00c4034105400c90b28000c84001d03183c40e81c41c0050026038010901180c4c0b8501010043c00304000600304801e039070301d00001001080034000030b42e400ca550918202a401c2401000140908841c480c0225000c03103186000501110340c000030002c4582c6541524004003c100000303031140a001c400b03032001401040092602c100d0345c000032820349800319070b54003041e840c0d031034520010709c51b500210040382d40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 405515683 1250 405514433 405514451
    0x612040308071106010503120a021005010e1806060d0809040603020402030a090201230901030c110118030806101704051c080a11071a0703020c011503060f0b1005030408120a 76
    0x2208660010040029004100035490b00c00844c0d030304c9290303080b031510340ba48c007044140c250341c070038020780c03450070100b030000d0140e56169a4034500d841400e4845850014502c68038404010f00440c1ea40d20803e8001e1059400402584800d032541e808901e940380d01585c3c0b01004001666544003450081c1281200010341d0701251001411001c65200324000d500c0403d41d00c1c141082c0c215046824000c001c0c60b02040f83e808a003025905000c0f5000d850619508224408240803001c00340c00e403425010b41c0da1001c66440b01c5007400107450290303403018002030141081d400d404030b46c0450382ea00644140100e51000340c084c0700c005405070000c445000000c003180b00f4060003031218090324602002c000031091600949540c0c49407450340c58240c1c80400701501000900c918000d5060f10741e64030300c420081c0f08410741140e5040e5a0003103804220380c8039140c114045a00003080c03244040104000c0e10401d00468400d50075112908024001c1301e03a142d00b003040c20001428081400d01849102c2008544d200c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 405516933 1250 405515683 405515687
    0x305162609090a050112062f030415020f0d020c1c0908060106030c080403030504030c120201090c0b03070c0b040c03020612010503100506030d1b0803011401080903120411061204030807 81
    0x50250203080c1c0c4074201130043c040091060f90303010407194460000034500b820b115942100c03130b2003461f040d685194000034003801c061144009510482c450308002000c0341c40140004224000e01c86c1c4400410b0080c003108079403000990040085001031002c4808081c00751980c41031581603a000c103800520404001c01c1114010005039000d010941410300021104070780c01002803200420103070405854101003020f06008804a5512030740294680100c03000044019020b0004503000703c2e5462070001d00013807000c04120940f4050075480c3c2c0c548810000f507840c7c0d8010007070090001d6851214180c4004011380d41c8030000c1c1214101e1a0380d001c002c0d17240c0380c10103040c2a0400d1038194002d06000810101d558003003040700221405003415080d228000520040049020710300401100d00080040784c480810005488100c1d0300b640e40c45805c0c0d5408100640701d000701c9201e20460542e500110300054119410301411042c05020a4142507140340c40000380c0ba0306490a0300440c0f424010322176019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 405518183 1250 405516933 405516949
    0x30c0d0f020c01051e0c0d02160801053601150e1530060a05100501020304150e1309120e0a0e0105040522110f0109030305162609 57
    0x40310780060600c0070468000609a031141c0d001000801c00940a4120201c4420f0195040007956004603030360703900450f00203503940c80d13008040003c880c0041d10000f640c03074050040303500c900000c0d03a100308100c4c00c45054402c012013102100480c0200f001403003051400900c41c2ea2046205880740100e668901105114003103c0508102007900c00130705030300303401c0c0c440d403901c41c94501d40d0362140c804429135841c240441c441540501b0b0040d005000c18410340030104d8202c50302400c800b91130300c0542a030f2400107995900c070f81e01c950201c480d00c411451000310b01506200c0040c213030140021120300094010302d000c1742d080740011180e170303899151040340d226440240506a000142c490894007800c1008080c001ca2052045a20a68689000502c00005220464003030b6422545580da801140d2034510b525410074982c85000e8014441103014561017006440100e03a00740e1100c2e490031900d110030320501d0040703a0301681c4010073380703d50805e9045e044d40c4d950303101d104000b00b164a03007031030703c2c1004401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 405519433 1250 405518183 405518207
    0x409171e1206100e0d061b030209150c070f03080a120b0d08030406020f0f120a02030f06100e060d0c1209120f0905030d031a0a03050d0e0301020408030c0d 68
    0x6410305000c000e1514526115460300007804541d800100501e00d542210a50769020425400015090508041165981064041c0702d48a000b80e8020490228118200d001d0641141c1d0f00101804210044000810040006260360130548039060307102c425010510340c6641c0101c1300181c00142c405483c1c0c0d400040d880c54003040f002d060001048078400500c070808005000f628840c00000413500b08075440d4100d42c1c1046031540704c03544a41c5001301c041d54a4000300b40a07101207611b0030001d1300c22900d501c21284140c0c02d404c2c4c150099150802480303580c180304480c1d4018004089241d110030390f210806094040020000807070019201c0c03100410305d40f00e00d110b1070f030f640d8100710f07015000031108041c140030082d50340b52504500c000c21404075580c0645510003034240c00343d9803c0c00c3c20164950001da00b140905d845201814091000780300d0208110f2002500c1e80c0c000c020206805031040080c03002c1e4040007400982030a4803014413a01b185e00440c00780480ea40b050101d0202d06030820003200d88 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 405520683 1250 405519433 405519487
    0xf12020f0d050c040e10050a02041706010b0708071509080406030b2d060403080708070b06091620010204230a030c060503060a080607230403031d040917 67
    0x241c0500d540d856030710040320429910490b1122410400c2140c1045000119202103000b0301aa0800d03982110080d8030500a504121040100c8810412000540c1e18100d43d140e80c4524601a219254415a0b8000341c030103c62007210300001e400021030b6030042960780da000c1c510450350b40b49040ca001e01214052900d490207140700880402d00900508200c1d069480c0305d902c240b070b00c440303400002a4603100e150001003602e0008185802485540c401802c1002c0c814100c1040540b580030401240348400c50300d1401c000b16207101d131310085114031590b9610000000082c184030307444508145c20b98126410640600202680507040000c50111034050070f042640c80c170703411b6030442d25030554414450241c0340034420008040f41d00f9850f01102440200000010350b407150901c048014208908446c0340313500c1122001419081205680444044079455103494800d07000c0708800200b1501d1a411541d0b20075038449000b008514101150352070800ca00c01ca50355240040c0c0e8203146060006100040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 405521933 1250 405520683 405520699
    0x9010b030a02040b01111f06090b03030d0f2d05070302031e060a0b07060209030c12070e0411090403090321090611011104090902010e04020712180f12020f 68
    0x151585010985520060301a20f01241c881c0c2d070f0b01c0c0181c0310085640c190110610410702c100d001c06502d040304280304141d0030b0041c845607688a084005581c840c0e20950fa05801c20005403558510316480704514400d124808203480d2003004048905003040603200349080c80d0b055403040c3c0300c001841083c1d4099000e0808504606020540554120003403030121258605d5001113030701507035540c80350741c01010f421914079070380c0b0b01c0c40c07406901a400c24510503009200b8110f003141d0600c0d0a001c01b0050701c000b0001005d8440c9410301c400d2141c3e0001d4829074119107203881c2c0703000b50344541418621450180d1104143c4500d18130702001c0200004402c1c008020b2040740701a0076642c4084040c0450b00f4614003010104500702c0600d0040003504545428210700203400a8500c80d9030f002015054000d0b2940c10859407520309002c02d03032007121750041490280e0720000b8541c1e0700417540300c403002d4021007000305155240e01a4044241158102c0200d8140508090046152100740110110780c1035404103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 405523183 1250 405521933 405521951
    0x1807140a03450c1a0706050f04150c1e03020c100204030506180f0105041b061e030c0c0501090c051f020c040209180c040617190b040e0d03140901 64
    0xd40c010105501c035950b0060b5190203000b800141d0502c00f01404680e401c2c29a003d404102c03c24860b8003907041120454104000107805401c40740e07a0382d200b980c03c50f080d802c420704950300140003058404800c40070f02c003182c070500000c10b01212928a000c10759460040c0d40b0009250301e0391810180c5030142c0c0445004000910008402050650b000066012015400740141c041075080c80610101d0106135032810040005012200480401c0754420410700c0c400e10392202d03012510710f00e03401c02c440114200404100445403180d8840e6080125501d0407009081207642c4450035142041801c4d203a080002c4d10500c21031415a403a1018009180c0741501c80c80701400000e5124080103a41602c01d0f030740454034001903100c614105842402000801203c0d1510818a4a0a8001d4094080081c410b070b5460b00d160b0f1403858001c2d0291b290786038400f515501d0720f107844002d002c0d40110340750071a40740d582c01c007181c21b030400040c5106000c6441c0420404600c403000f00003118014148a0b03540c0c1482061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 405524433 1250 405523183 405523271
    0x109050c0d03050d15120c0905060d080301050f010203041211030c01050a0c0b06061b0708060c0702010c0b0702030f1611101706030307080a05180406051807140a03 72
    0x140c011301d0402002244c0c58920150511619032194041c0076081d40095501c03081121042983c2c05980c00020100102d441d00414411500c01c1d6078030050001c8400c0006004601e40001c500c8231148051045034a002d40b09e44690b0408404c040342158140e00364542c0c1403281c030781484103145c0b05c0000c2c6025400c2015101c0020300c000c00285018140801680125005803034500c00c444c0c1d1980b980282d640d0802284000d2a45c07608288121011405180301051501e00c1e000f017160a2a42c050303450b83d0006843e52507180d5040c1c000342941007540702c01c015505030b050101010b40340c0780742103202c41d00c0304580301c1c280501d20087e0046010721130500c51070000d4580340c005c40c0103011001c4805e1a071140c0e0352900e020a10f10301c80d5002c090f012850110300400310b1940000240850000c441400e80d82c525200c080c007013038036041e0042c2540008a40340200111036143c8a40303a01c52240d14201c4800f111020741050107034005207d010000ba02c69013a8140c080c1003046850010280610000348401c00c2402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 405525683 1250 405524433 405524437
    0x103061a0108220215090102010b0a030803010e0903070b0a061412060106120605030f070f140904020d022403270c0105071a0a0621021003050a110c0109050c0d0305 72
    0x203400c044241c04003410a01d40f20200c050800c0d903019181d038407040014034101915030800741c0e41600541c28403001c400b260a002644000310703030b4030800c440d06503424810003600004008110032041e200c10b01c034640c00715210245440c0940d0500e40c00065003800c104200b05080082d0864070f0150110406100c54024002001411180c42d0f291060400c00c90754140409082d0715440b65515208030825038072100c0e40480da80045501444668041960710b050300401c1080c54161580e02480301000a00507007042000c040407544002c100b038401900041c101b94211440c031412031107040010040020b41c1c81c8400c2d2031400d4500724010841c84030804410540d45003c224421410000042241d0040002c1c00c14401e6034803000e00080e00f09450030303604100051030244140110040c44046179000f0782c0c00814108640d0b90060049000701e140384805030050080034101110096648564002e1300c07e01002800182c500d5030004140703030043c0e04003645003400d0500c9841c40f0310304003100400065000303c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 405526933 1250 405525683 405525691
    0x70309020a050f010e030102180a0602070e01050d0f060c0e0f03012721020307020415150315090207050303060306070e0102031624020a03050106032d020702180103061a0108 76
    0x24915050080b81d4004036540c540b05c0c0d03002905580082613010151022405180740e18100743d4950105907502d42c800c17a600c42c024400d4100d4000782030018003a9040800300a90014042d00400c042401c11b030390b8600885a0321105000091150000c805d014942810350304548401140240f00d42c560200702c0440c0d440004500c805c0003425145100200001c10310f100101c08610010f07004900500400a0340300d034000305049105074501185010050b4080300302400b0341c0c00780c0d44071540400384200700b5801094904029801014140c0001510007080c0c0014a4240d1007180910384134144507040c140741c200b010305500705000021500d100300340d0b0300005980081080345940c580100d0f041c00c080402e00c60044041c081e14049110054124080e500100b03a044041c0d41c04001581c1d9038982182114505030324031510150120b08100746a80d100c0400305400107204005207413801550014a1030303c1076482282c40050340c00d0040062204030b2007507001c240c0c0d08805800303401400e800024050b0000074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 405528183 1250 405526933 405526939
    0xd021e0705121e0d15030308100801020304110103200a0c1e0f12050405030a0c0e0906060303040b0d020906031f06030218090a1803020601140d051e0a08030408090405070309020a05 79
    0x8101d03410510b4540d00030004400e1000c05241c1780c42c1d20382c01c000b00f032100111610304000034044000202c408051003140d11a5400900b1040034407001c20044018052101850706201190108600c4040107980104103044860b01e0320f44822100d480c1c203090f6118014505036820350070595060106107100794600c00d041d4030003680b155010b900002030fa5907000c2e1b80c2203203815208000f000c008006c905e1440b001510203204400e81c3d40c1c6d680503001075440c0c00c00c451030342c0c25410038030080001418110142c09400300101000d42088120804911241c10864502c0000c201e441c1e05041c9004a0394030300005000039150640ca0308003040d25140c40c00c90f01c0a0003e000c0c0f0f110790001030306402c4d0b590003254022402c0107810344507861030030020340e220020b0284501c85030310071502081e81e04d01012401c0e8804d6001015050385412507003002e581d00044046c8a0f180d010f100d10708000505204025840340b403080740942d48034032044061000b250f40003003a517424035107016008405a9200b1100d0700c02c4950031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 405529433 1250 405528183 405528187
    0x204111c060e15120304060903030e0618130e030d02070606060801080304030b062b021e030a06240807030506071b0609030e1003050406051501140d021e0705121e 71
    0x104004c14049003011811414600010402050441d4060072160480340a503a071071704228141d02c20408248524440b04a000c41e20010100d40e41c2090a92481c0700d14140c0d20000e242041202d489096a100040c10101c1940c001402d1080000d14414807000d441d140c9054203c0d9810418140e0781d9103c0e9001c0900500c9140300020601c0e17807803207007260707949401001c40041e0381260071a0b2110003200540882c03007490003202c620020b0b042010f0f5150311240003070080026a026031204d50040040300b000d866400445c041500d24010b614275031000500e147c4005041b210702d141001c9040c0b410107000801006202112058629102c1460780e442d40e41281c0c00140704201450196142005090203036000400400e12405281c2c042e0300c4644114081c540c180305a588801c00c8000c0b01d0300b000002d40c0411092511900001c9040b0083c0000c85104900140f6041041300c010485540307990115400c0100081e0150070003c0500c0700e929403c1c0c1a0205c036003440c5213288920020b1440c102c14440300c0380c2c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 405530683 1250 405529433 405529471
    0x80f06040b070509060403081c060b030c0f0903100c02070602010e0606010503011401020c21060604090f08130b030115020f010506030706121103010314070812030f06030a0204111c060e 81
    0x9400115001980d02c242c0300c07580c07185541c0300c03100c01c082d1001240c01c1c902e241040020b100c280be141100e1241c0402c008440c6071800041d0040c3c5a90080c00406400d88146842c0507520022071140d400c03210308540050500e1854080020b081d80d40c1910150032a0b04410140801a43c02c50b0a590560b185480f0b40122a0031000c0102d10b0400142d08080e0301840412040d0302088101100c00f40c00d03043e0100761580c66582c0c2d014030055420780e0f00f008161510a40c80c5c070010400c00400b400d04825580c110141181d81c61607450382541003070304005145c040e40551f8000f040d40400c007420400c0050f200a0040d482d1040c0041d89510461045209004101110031203044060b80700b400c01c8207030454499100d503140d09110360700002c0360a10100e244600070003c1062040040c011035200d503e64480c03881d41e41d030004507000c55400940025018031482003180010b030f8540c01500c1d5803401100c4881e4a811910b0000d00d0b00c4400813014084242c41c0c81c4041c440a8600e200072070b800b5810000e0ba40450b55 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 405531933 1250 405530683 405530689
    0xc09050f2d06120706030614010203040509060405091501090c1d0f040213050303040308090a27021303050a110102010b0d02010207140325050103060b0c0c13020c070906080f06040b070509 82
    0x507403001c240840c4c1c0076100010030300d140c061707200f201034600c142d442103c000c2990005a90344d01c5640242e50f8040021800140c2c1c92409030481d40d8045031440c1500d01c8a0040c0300c5000840e10282c109004203074654024075a015482252030703101404c8004014185030700748000c03483e01821000603030f018070f4001a80e101382d00800e1b0301c52001018050121f80e600e942e41c0c10516110381101c241c0714841d0442c98000160685d644150064481c070410b07e11491002042a410080d03108442d51102d030031540c040000451018045105050b0082d898180d11190760800207003165454086584141c6040010030f0250342c1c00522007056400e140517004464050398006850301c1d065020a4000c0c41850f00b542040d203103032448203012104282c1f001c0c045243c41e0b03d504070b1140038a003410b180390750140d103054281d454a69402c8c0d0ba82e1000c00001031500b1441403501d802c001690300050f8126403200003c100d00070f0100080d801c1c1040600c094101c41c1000d64072030a00410103000702d000c201d0f001c1a618880d503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 405533183 1250 405531933 405531949
    0x21507030f110115080c0a0b040b2727061522210c060309110402070f060510050108180d0f020c0d0b070806030a05070605070606030c09050f2d06 64
    0x41c03211350000184554946038159201100d01095019054502c00024074500403002d850a4840d024001c90401c03211100050520807580c04c0d100030801c440340303071142c5500d401c0c07000d6101c3e06039601d14042a40812a4101030f00380040c005c207015920420b007041e401896541034805043c030341c00c030000491882c0c02e00700307500c208550841c4450014480b01c4031010312903842030341c4e9a00d1140c00030505055590100782d0440d0f98154002e00182c4030407108420320320f070681c01010501d03c201c070011801140d03070b1108400c64104079200400310318003040500103581c00140032980503040130301c01c00824040d0384242e903d0b10458905842403001155000190382c1c02400004801032021b01591002c100a0510360401d0406454850119508001248241c00c020680c00210b54100c0c0050010b145801d07000c803042d520440003a150f55079110380100004000000f42c50040040ca4404190f0341407444070007900c40e0004d405801000100c1045000b01d04c2002c5440f80441c440e2400c6051507500d00002c21020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 405534433 1250 405533183 405533201
    0xb01090b03220b0703140a05010f0312030e010603140c0603130204021e0d020a1e02060106050306040608030403050c030115030b0610030f0c030e0d050f03010909031b0b04021507030f1101 82
    0x10007400c3c200011150715500407080381c91040340b89405622212004d41c11504203000d600701d0400f03000c50900116500c501b0604040e11503150000e03856035045803036821245e003500f04841e0b00b4101c50301c3d401034100401640c4c0c5a15801c031341030b0b89103080103448030ec0c3c80c0102e000300a0041d40c01003200c084a0b045100d0395440e40f0060306103160b5802c1c3c0400240000e6000b45082c1002c50042e602e07420f42c41c4c420f800540406840c2e500109404e90a094007518581c2000345234660054a8000200d4103210501c081c0000318400d0b0300411000409408041c00d4a803005003041c07a0784a40d5408001003160700f85003580101f02901c2050070a030f442c1a00320050500e0440c480742490a052040903001c7d072680c8840504030541c0c05403407250600c0074040303c1d1842400c01038940740e0420302c0140030781d4806174408580144a811301d2900340e0103c05ca0bc03030000c0100c1c00159a041e0b034540c2004150304101c0482d1101d00714090030603150034815980604030360124a4410200a5001e8042240d90002d41c851070303003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 405535683 1250 405534433 405534443
    0xb09040618150609150b09041d030f07050705030f0703060207320606060a2a05160905061503370209040b090f04030c08130b040503010b01090b0322 65
    0x5910a002008000e4506445402c2c10310340b80c178401d11504586a4040c0e826124100d03c1246051940c808005c003030b280780100c08264171104640507c42e00d100304002c00034a610f0b2400c50b511203040e800c0803406d060069022a01a030448018951182c0d408190001520780c0003000503150303030041c10f10880c9c0c50030f03a0403200d00500785e072000c030303100600900040c40c151092001243c01a542d01c0c000c3c09014096101210045401680e00302d0450740110031503900d0024104c096503c0100d241c4940b440c1480c40d2542c0d459080399107074240840c903420300076160b204100342e0b4603016005001e44408074a200017415a0044095a110711401c0701c02103051141c1a6807a44120589580f400c881200961048800c81d200f1481c1c81000e00b01303400d00b140c072180729195401c001881580c1d1903d041d5042402c44400b02e445290030042207000309080034211000e0500c10a41548030b034101818103084808210b100c60600c034050070104040f140c141c04aa0344201001030100c8a010204040c3d0b000030342854000340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 405536933 1250 405535683 405535703
    0x608040303022b0f061a0d090203030d02070c06020613140a0c08160e0906070309020d1505010e0c2a030405060c0109210914010509030613020102010c02010b09040618 73
    0x180e500240c441100342c0802d0380104012440c103240704002185c11502c05c0310401410f1905408906146802500c1a140b400d04049084e28107980040d046034040c0083c880c80950101b01c44060016140c20103000d06030600040801c1e04004400030005046a800200f01c49900c490b1182550000d003c1c0820561f840390703400f0b0f14030762500b40c07071600c1340542141a990318202210000c0c041e81003500701400b07480d03001c01411968032840d404801074554040d0598015125264000026100e00350416040130580d10010701075040098000c00c030400503008000c071800a01080005403018003074400b001c1c8140c00d00b50010a09003031000e0841c0120303401103034400c801054003030780e101d81034201d00c004612600c3c80e90103c80d030703803050400e442202c12201d500251950a060008040142a0030b11700001414040c0c1414881d00019107801c008940803120752508126081c00c41d6024081e101f00d12046000910449011202042c2c01d450014005408140c454808062406d0034560310610306420410100f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 405538183 1250 405536933 405536977
    0x151a0d05010903020d1404030602091909090b0a0504031b050f010608030c0c0121020306130905030a030c020303071b020411030c0c0f010501030b060409170316031404020604060804030302 82
    0x9000b008842c0d41a000750040b80255640c4500c207400d4007450a400303c00990030316095032650b00007034100c850f01c140c01c0a422441440d4400440b1a12401020302c4180814500f0341d40c07034050300d44c00000c1c00c80c03030346070f03080c0303010320000035088400e01210301d03014881c2520003219410400d280c0a0b100500e0b0096501e0300c8008142a14040010117120504004451801c2036013401180c0d41d009601010002150f01451010390440c03d4006640080e002001c44030344881e54480b01003200c00b1780c2c4084619078000940d108540d030300340c01228101903e5001841c218980070390f000e00420a80102c0038411004000850115655a40122100105100029101e1400305400c8000398006a015900e41c440c060412010000500030281641d5204121504540b50300c0e041c0300250500030f001300c8600d0f1601400721851a40000a98400c0000c18941c040b03c0080941c060704550004049440f4810440100310140c4c44000c01c4804480a61800140f1596241411002030094200040b403124a51070b0361 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 405539433 1250 405538183 405538193
    0x109021309020109080303090a030f09090c050703032f0901020124030c0b030114060a0c02030a0309090e0c0a050d15150e090118061d070b030a0e0307151a0d 69
    0x220072a6200f0b80392501000c2d11400c3c4281d503400700312000c117000e40c480c880d10380000748100842c421082c2c650030040000c44d29110640e040e958601011000076402059140601d0781c14000c0b0365010171104c4901410320012160354141070101c54040c1d14207d00019141c0d4540d200b58054580e0340300326048808080031002d00e904100825100c25140740c0325500011070366900740c800712030485100c6c1e174494100c0d90280b01484041d821419204040c00229071541e070143e00d052008105140c825564418641d00b800c3c61700003202c0ca0203012420310f40c054000301c0c1650301c82d440f58509680d01143d40180c40c0e041e0307180240c645080281100c0f0501d081c0049031003280d006d241740b141030b500c1e840003041840c1d490b000400d0072515514401d84071031103222a02c0d0040340c4554494107002e401158200c0f81e04000000a44c40c18610790b20160340789400104000e500482886509412801200550328081d0725440b01314410701e5052000300c01070750f50013452034903042c500f4a1217083d0b0303800360000c41d001c1d11074282 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 405540683 1250 405539433 405539441
    0x7032a080c01090602030c070515070204020c07061d03031804090f051f050411100201021e070606050f0102071404090f0f050d03050606070f0c0504090f0c0e0c1b01090213 75
    0x10766000c900d51460119100c0e0000c015141a620707010010100b40745818100020104a130840b40e01e0007104026460250b1074500051009024200051034418075064009160038030110700e00c115800a040104101e540210440e1452940e0304600c0d000f94030440e00240040010f01001441d402600208804020b40811350400c03100403004074031200302400490f0f80945000722001000704200e0075140c01189080760140050034514800107080c0407009c0100100040903000000711074001040c000100441402410041d000a90f840701c01d200091300047c1d0354040340d000d010381d002540007800d000c1c0e40321a40411313000303500241103088400d55800d0144040034109800c1d540d60103407000c42c0c0b0707a042c06400741d54011301d0050140c1e854aa11600c89408a010400e803c4500d5610650005250355841c094500e2440c0200d1844200105528044045003840d80c000203403030700d032071041149109001c0141c40d40c520398071004182c01c080c0c800300345004000c0200001d40c40b180c8218900c450f8440c4da48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 405541933 1250 405540683 405540703
    0x405030f0a050118020d0b45070303080c211e1005010e060d0b1005130f1202010309062408011d0a020d140703060218010507030207032a08 61
    0x1000b040310b82d413294401009100c015034040d4105501c11000e00010300321462065000d00085004922500110b484c0a144811305551a0050300c0380030b6100c8074005d2039064010740c0302020b40207100161460341d024000c1d6500400106041c0d4001c1401780c41c119080440316050f4410b000b140d0f506141100b030200e15101181c0f071b1140f0301c0d8085030014200c000c6110500d02a2141610340c0c1884c15568820042c1941c008a0090100742d21000c14868540320500c010503591407d480d81915800581a041541c1c5140c1e48010b81451104074200300c0d00c0d5613200c1a091494080c40c0101e036106c4207080070000340c91200140b150544504080d00f010800b000700d1501900d0712040207100034942c40302407103c0c08805481401c141e4014030307021801460518005440b803403050400a00d03548442e10454100300d0b40e9030058a0030b54001800050030004941d800004110900704503003448035a8030300075075810f803d01004044100c007040326481035022a14605288410b070711402211358480642e2501c2c2d12100f4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 405543183 1250 405541933 405541943
    0xb090d08060f030a080a0314010e01030b0f07080f06010c050d0e030c01051827070e0109050d0f170c0d03091401060605030a15170a020a0b030c070602030c0405030f0a 73
    0x900480d1075880d011203a140c503810003c1c001d105181040d10b5001142e84820140000e244e9104c101c0040c4000c5000d550b0f000b0050301c0ca13005900d42c55030800400a440c018049410050300b0010400096040f4000f9504000400120542681c0700c200503205034100c10009030052103112003000c00c141e03000c080d2039404d00c0c007035047d03420245202c00150303004e0203219504040b400346040c10054034101207030520800c041c022144c6414520a03188a4903103042501d041001a0941041c100256000f0100030010070007130b03554090003038450719085400c0380e100e00d0080144148421100802c104d06003603805c07041c02c400548039085003610340074000b0a8405c0d0121420689000303907000180c410312502d001c862894403064590b60b030701501000245072444140461850b00900403070040a1507040203c005030382c2c8010201d0010500400000880076442076040c01e0341001080300c09219031083e0f411955000b54056141d4448030424000d42c040d0344c1015800d80f1801c1e40d150f0300c072500000e004034540e01070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 405544433 1250 405543183 405543197
    0x20102011d0f0d02061b090a0b070309140a030308070804060608060c04050a09060503030a120f060e0121020f0f030f0d05040e0f0601090302010f03021204061505060c0613020a030b090d 81
    0x10043c1a41c580d40b04864034910002c800c10304801c8103502600a00702c241004100d0140503459500c2410150044e0000b6400107090f14400d100c040c0d05208500b4034440116107902d081442e40d6402005a1030040820040000e10700200d0200b003403682100000d0021041a00c825150140e4640c40b290001d11480c0d110364a0f0b4200010002c0f054420351080c2c41c0040c0c0914038003038414000b90780c00404040c0300d100c6942e41e2640c1103088010781c41040090300043d2440000f41d450801d01000e081c0d41900e04407044a02c0720851001640d44100300010303940b0950b03001c18038660800000b810008420500700b884d0081031140c0d40903541c480005c2003a103021124941d11502d510003280f410030703800c48030300307000c915002c1c81400035600441c1c0b640010000e03843c002d4504841440e1800f03005030255412500700751600a2181000310326205e42010300b0003507403110b05050b0515203e6a9508000e00500a0114142c40c01000c1d92039184402015580003200d240040c00c110308240c0c0e94855501074100041c0d03107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 405545683 1250 405544433 405544453
    0x2703060507020d11151f0602060a1a01121a040e0609070f030c0504050c040b0a1e020111041703091008060a050904050619021b15010e22020102011d0f 66
    0x1071840040120054030007010301e5141c0005543c0f0001002d0f000b0588510500d000e611b2200070321210707501615865000c1c040034280100a6800c0d1501d460021121010080803600b560341d000b48000341100c084540404c500c00c02c0394240700c0e0714184510a542203401d080101b00201400180d40b800348600384100d030500c41d660604042203000c3c0c2e0100800248001c0820070862405401c203e410000031609285000c0e591000c0c2d41659000c80d580c3d1011070385000d5820140095003508003484c200300d0000f48040c00b4092031400701841903014407181c04034000800405010108280c0d089403001600440303400a10b141c0c064440e020440d4140c1c07241040e03280218003130400304842c6000d290310a00600640d00c030990101400c1d11411311002e100c0780c2c01d005003080405087c1660381c100c0140005040140c144800c0126840e03016001501015003420901c11300000c0b003485010006c0c903403420050319070250310040f03015008854000c4c900e42e110070b0740300c4403450020440b00e149260a0f030480700050700b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 405546933 1250 405545683 405545687
    0x90904080f0f0702180615130f060e01020f010513080708040b07030824060a08040f081c0506041523040906050105030114040302070504090f02040608010507021014072703060507020d 80
    0x2084480c950080c900c0f50b610240c4040c41000740c5800d210b0070b02000308261320703627410801e07050b0300382c2c0484000340303114000398180c0d601480110000304010b00248418500342508040e5804559001094203900060003014010900f003990003070544201c040d0b68560302814014070418054071103030030303107004800001074102c10038030014a4404003900c3e023824a00c09001c02d031200342e0001c01c00d42e982e203c20555440082c03c41002405000c1d10f0550140b559403441e41ca10044540080c04a801285061079214080044c0d42e0a0b4003100c0400540c030b00d0502d445030116644a8040b460660050f051a02c00c80401c0400d0300442c1c162501a4000c010704e1616004c0034140c0d01040c1e0340039016801c400310900480c10036030411a40c050040006c001d040038603a000c01c08842c0e940d40306090136503499040c0003125505100c949454446400107004100c1032268801d0301d00d80c041c04140a00c41c03c100c00886450403400e070868400d40071034015109668a0810344050042110744030b006000b0000ea200c4014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 405548183 1250 405546933 405546979
    0x2030f060a0815070503150429030604020f19120c03140a020a0513110c0a0501060e04050d05030a06120b040204201b12032404060b090904080f0f0702 66
    0x34001080001a0b180c0040a841583c0050300ca1003a1050100b81a401d48e1030303d00400048140521005407940b403076023551400d018407100403038800d401c040180005a5501d14488044110450b1080e0711100041081c07003d81c10b15501c20558a00a500c503001404404a519800c481c0034195111a442000090390f40355564040700941c03002d101c4100b03001d40e040c1200701c082e02071214880040c11460208000d031540d0040c40040740c0c2171348201c1e038401c01c010003801054018001134924070010704007542d03251707200d0740d182105204020012000400b8050140c000b04000c10101002a003403050300d085c0152002800c81d4142e00541c140090280440360032001c0100e0b110010160504207150718100302c3e0a9000601c502800e44075020706d8001d0542481c00841c00791100c41c09141003c16400c1c42c07020220007164000c2c0c030940c90040e040113400c0300e50048a00208044405102558131b61801040d03600890781c00304060030010030700354a50160003004004090007101d6000d0b0344d0780140b40c010308071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 405549433 1250 405548183 405548203
    0x2070b030105130c0e03161a030c0f070218090a0302010e0708101802040501240f05070b07090e0a02040501200a12030902060d051f0e070c0f0602030f060a08 69
    0xb00282c3c4019410240d036a9000c250030050501c2d180b103500c400030700020b10b0401c0364000d494801720440010041c034110303a0507002c04201c00c010054218076000700e149450b03018041d9141e21144001424800719a02d140102320080c01e4080352000c0c600b0000035065607407121020031809580386c00c0c180503500e20001041c004481403000103040321500c28400e18050a041009892010149a01c40300165110701507240a41001e03411600c104480d130722004840300c5900c0b082c4040c001003081d031884056112003103a05940c1c100c1d21885082d150508210346440280c2e20110200490030107022500103260000d0007100c2090382c845002c034102c01c2e400604011020341d1200554070003000b101c0082c0907041c8400303054295040010320b0b8100d5030007003082c0b64440311150003000d6442040150002d0188a000704144800018110443c14099041480784004d010041030041d0101002c00f00104280c103901181d9008005640741d040a4070b04071121081542c0c0c1d54031601c0030f00e2010500d60000039003d005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 405550683 1250 405549433 405549439
    0xd0606030611031617010611120d0902010f030603080f030705070b040c14090603030d0b011b0b01030618050a0213150f0321050f0d020d05090c01030b0d020f0609030309030d020a020102070b030105 86
    0x10300d0740380400079621002508d2096999009150000d003d501c840070140c0b07030746042c2034808200e120345071000509180079582c26100341444c0c09014404251483c060381c034804280e400b1190f40b510b4100c42550349005002009009601050420003002104110f070811101402950800031400d80100600f0704011200c4139019401400308924002494110a060780030605004104008208000c0d0104200c1071041d07a003000d20800400c1081824402c02c0c1c012000b600c90000b1004207580c81e10749407840e10310003030b00c5411810900e00016145621445044090540c0d101202c3d035203d0035104010701900c000d41e4031251081c910f440103038042d5000c50001420360b44091620f060100f840301c05400209840242c96401d01141480801910546000d81512002841008a03080006060303501d4001554014902a8201030041c0c840c40c050341c140903c00c568254071251200046072071406405542a0700d489007008103200350b500824504c0700d650003a8250307007880791180740a5125110a11130b03950 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 405551933 1250 405550683 405550727
    0xe1b13080d090311040b010c2a151803021804050115091406030c0a0e04080906030c03090709020c1f0e0327010302040e1305070339060e0d06060306110316 68
    0x1030000001480010380380091144022a040d4038040f4100c3e9504507441c121450400005285e400c1030700285044038000bc100d040b281035a002c9040101e40614048030f8019501c0810108070080d0030400d40c41510740c0c00725068a45ea600390f038000c0d00105840d12400c5c0c013038101280541c14046118040076901500654002c1c0c5002c501c0d14107402c008005913030f010014844440d80e543c843d001180103840d0308007103944070f00b01030780000e0402c1242d500120300a84100b200c45007a004c042014075202144854042c486502034020300c006c1e02645074003180d54000003d00c1d2480161101080640f128040c42c280b9044070200e0040d01248124042e2150040c4d00d400025140540c3d01d1580c0c2089100f8405d031041e641c0d696498101900803c1c010401c1003001c0c030304800146501c840014400c000305020803018910b4440050100b04203100c00314014004001c00c40705116854000000940d8444010800720340b82c041000c1043c2c20580700070700000380321001110710600c02e9138404090f00c0480400d507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 405553183 1250 405551933 405551957
    0x606070b010e041a0c070203010b0d0210030f020918040c0905040507030b331305010f06050708070b090309120a052503061503020a0e1b13080d090311040b01 69
    0x5008260b0041c42120340300c000d00c03240c034a41000b143c0d5950140030307450002070f181c00d0640304140c256094844c0c0300340214140b409010240e038036001c040c401300000307050004019458403000e0010b4881c1c10b280a40217a0f8400e40c075820043e01c04070541c4030700e006100d0141283e80390f600790426180d040e68050031550100c1d40a201041c00740170400d03003103014800324035031090f10845801100311890034a2140d020200c3c2110650741080d04040c50301301265a0108059030500d1807410f00d01c400b40c015441080000700341c920402881e1400c46100c0ea4001d4582c90356880d0000440e0fa481d030014543e00d0044100181c0d50f10700c1c403400900440503a80c400c0250058207400f00c015410341e503650b8000051201c4842001020540c41d125041d1440b494500c4801e040e4114010b1060140c26984a030700a24200c1c1304000c4c0c410031002004241282d0825529a0742501900560152a00d600480c40c0d5000d0784101001d0250004d0b8203104807841070f410320040c03101c0d400410007150b0010324603e0105901003554 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 405554433 1250 405553183 405553199
    0x60504031106220303111218010504050312030a06051c02130204050616050105100f0605030916180e0c0a060e0301021603180e0c0904020a14160b0606070b01 69
    0x640c0007403000380100d42400d07020110a0300442c55200620b004001a20b800d0060641c0424032002c0144d40d10010001010441e03d00061441060460301c3c80c1c10a04a00800580c480d0040b10001c010040803584242c410480500c1c01d680240c81c000302c2d0754504000040c0d9810003030b0f142c129a45150410bc0e01031922034082c0004074803070580c2c0800c02682004040344a564800142c04840c100d0761843c04180c07040e107011400c4032030140c220360908007200300812644201c104003a081d600360b03103400e45d12500d81852030f80c50032100c880034501211100401060320359085c03000c190f0780528142c007407007201c403850348081d205c1084542c0701c0d030400600f142c1446a01e00410f000340181c000a00014a00807020440f0140c030442e1010490010328211b030000c840380840b01800d40580360052080c07000e8100420300000920501180501032074020900c1480317a4010180c80140300d1001e500745585030601d42c03031001c206100342e000b201c40200440c04503024bc107003e01a5640c80c3da10100110080c0d0a20b248 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 405555683 1250 405554433 405554453
    0x20a0f17070519020a12020102130e04020d02010c0609060c08060117010b030705130509070c1b080601031211060106200f1207051603110a0509070e040e0106030209010b040609060906050403 83
    0x4001c11340c410b03108003800040c9500a4009451856400180c544900440300002d61810364407107404180184140400340e80c5a41a80101ca42d090900c811944428680386000d0035500c040507000f586002c56052a113608100d84520449090b0303680c4c405410090506111494203008094805006100050945008c1d8004006050200400f0f0000c565100009005050300310b031070030005407500200da4100701110300c0c805030090504024406050825100c40c2e6500014840a4440d40d0024214803100e8020340c0409a502c04240945a607503858200c09042d0050001100d000e07006010701c3c200c0c24642c0410300d01554265500542a900744c02040042c40fa001200140c030140114511000030041001d115001144a25044000f0000c18400c00c903003c000c5070711840c09024070a04025000c1e9204c0c01d4210b09030340c21034001400703a1400c181d080c0180130b1900000e4200900f48004151a00075030050400c4400542d904002140c0700e0710115502d21451250001041c001e200500c00070302d030703604 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 405556933 1250 405555683 405555727
    0x303030910111b030414011b1707020612061929040807080a061d060718180f0f0e06010b07080d0204120510200c01060306020a0f170705 60
    0x810107081a06074a10807402400122051501d913000083c1085110800300c3c0c003440480003400d01e203c08803214040f802c40b84c2d040240040c0710603402c510101c0c0310915070f4141c44802c2c1d00a00300076120300c2c0c0000c81c1d0246074410350b116031043c0990403c1c0b11082c0e4400c0f1002003581d1310300c1d203c030681002000503404004481c1d6041d0032828400c6c800483e45038000c000c82c1303008001c60001000141d000d410034000300c840100c0700c0054010401419420f61900083d45500190039244c034090140145203812070611072a00300a80c00d41688401da084a10a9081640d00202d1240100116003030100c0d10800c4920840c0c460205030030420042203640e080001a103403590140800e50b1412400c211502c1c100d0b4019049040044203161818090100402000342100e00c2841e0400c038840810801c042a6545110004450040041d01c9100304000303411107401994082400c2d916000841001b4141c017101d11050f0000400b00743d04402c092048103c0b941c000d460340d403229480d00c8080380d00711036443c40001d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 405558183 1250 405556933 405556961
    0x160f0c291b031926010b07020103090803010801060906090209030a1509050105100312030e03030a090201030204120305070212071208030603011410080c030307150510180209010e0303030910 83
    0x1c80c80e51041d10341803008260603512516850000b200f60580030303050300f02c02e1084020942040089034124055503801c01e06484000e480181c070b410443c4012000b503c4024001070280700040700001c1c002605400a406440c00343c902401465100c4848074224001d410200340d06621814849001c160300c0500c8100c003030403620f4080b404941a4950ba425940281c0b41401c440500d21004c100340300140345020042e1905113400d020780070201c5001d0340e0740c0c000135110a154507030f511003540031607000b981150001d212039084c0c0000c4041509014050760083c6200b03a00602070102e0220a800020403980242c81d4071000e682e84444007504c2d2039401c1c2d00f00604c819059960b40a080b404156400207041c03192086003c036001ca00d00f0030040e00d0904484440c0140258000c0c130400700090071320a466810001c00ca40d0010380381d078411a81c1e84641d00a540400c081c03000d0b0f885100c900c5d00d5a50000e0400c1282a00c41e401c6200d0804103040c0e903841f0440341001030b034000c425040c000400c29080800088254 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 405559433 1250 405558183 405558217
    0x60103050606040e010824060306041211100204080c090c040b03060d0605310803010302060307031119080c0a080406050402060c1204050a0b04030302060a0c0203160f0c29 75
    0x1455400104c1d810a80004025901a06801003045101000c142c03110104081c01180c2d41415004170780c2ea0703400500010003010fa00035100300703001d1103042034a5980c2c0c6070604564001c54880c0c8000000d502a011f009072a000f02c0091030741a051020309540503000f20b056141c0341c503280c40003807101604050441b641c003c4080101c2004164113010b024080c0041e4003105942d02c0c3c1d007003c08407000444400661801005c0f00c0201d0201b1450000e5904694065607070a40d00d542e20703802180140142c90340e440c0307003040c086082004400d050420711103801d103546176074046440c0c00000e081d040c0941d40d442000140c0230303000a000200303260000c6400034405400c035410f085002e42d505050140208860502040228003000141b5203590084001c0109049583c60141191002502d40400810000800c1c2c0c0b1085a07817200c920800458081414125040140c1100c5c2d1801c112401c1c0000c41c240c4000d4a074907070225000501340040100c00c01e81d280c0040d49881010403116480d0001c40540c41e00000c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 405560683 1250 405559433 405559439
    0x40501020f0d021b070b1c02040801050c030108060f150d02011403010603090c09090f0305030403020a15020c06070807021e10140103140c090106030506130c030e010b0d080306010305060604 83
    0x6080a0b2075016091800982c446460009031240d07402070000a007071580c0009005c00004c2003c0080744d41d11080e80308168050b081031504200603201d6035100140c150f2900d8100000c0c00441d801460603200c0320001c4e202c072500c0310038040ca03644e40152200c4200340e54107840100d0500c0c0682500d082544181072860101c404680038400715042640303c080800e889621440c02c02920380c0b500d001404204d10b003000700460b681c032000007030096281d00405112001001c42c0134140208000c644159001c03081410100031031629801a410000780e48219128076804940c100c1d02540103103128010642c01040304240c0d5002c603000b11051003650b041180212651000700412078014080b06030081000120f0651552400320307031040340e00f180805150080218002c542d5107100140703044407007625012806403540000640c020301c00c500031440c010701c0c0844010081e5015048a282d81d44468000c2110b9000741050000d0044400001001c001c410400501c40c0c0d8000e500041d0001c80142c8003e04240e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 405561933 1250 405560683 405560707
    0x120e0607090501030c08040809010e0604030c08010b090105030c0102060c0a050d18032c0405190c02010c020705010e0a032607060e010f06051f030b1305040212010c0f0804050102 78
    0x41512000c000544080040c407140d41c1500910300310f41c0c858900705c1200e00d010345903160710340121042e143c10004980c0b94020903035074840550f00035540129081403103980e1103000d0307070080605d210628000d0210074000102440c0208003005808012b8000e400c05503111001c040c070303981c01000010180281441078044441041c85152013180e01c11044400c0310201d13060107000c80d050009405000107a1222080303040882c880c01911035001550003058549520840490040c883c1441080c014030701100d90900950540007039003411580d40075202c4258550004450031400b00c40c0f0185c1106201e041040042c1c00b41d090001042c0381140c21410041c101a00407159521031901030314030649480c2c402010000c203200b04070540248000c2000114644004500710008504c3d00d18121810786081c200901e0007608038003901035000300300130101c1000380e14003c0186010385050f4001d010b88c68030140100f80503c190800d004060315181c1000320706200c1180d0b00d000080c0100e44c595000d02001500d20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 405563183 1250 405561933 405561943
    0x20703032309090603190b010f15050d1503290604050705180d02060f120a05010609030b0a090819080a05040209040f0f080d02090f0a0b04050415050a030c06121b120e 73
    0x40d12404003010294507010480244041a402015180c0b0445003038ad203e141c4c010080f900300300020200462a214050b0081640c0b0140b41d03c0501800c50481d01c455040703600809482c1d40d08503401c1c40741d401e9143c0c203007480101e82c1c00301c50f00c1b03000ca074003000205500040c4050502603501c004100c490703084020750100d0002e030044440c0d00100303540807401c520100e80000e401c6522001c1c0c00810043c540c5481c00c0142010302e40e04c40035290012146c0131886215854100003003181d040148259141052407070320000903405103d06000410a0380801d81c0441e5902446000325002003181405885a4a8510303060340080341c201c40740f21120700100006030241026002001500c100140c6508101301840b0030305511070321661064550704002c0c004030100c1e9003994181c07101501d000607407140c002412100c16140d42c015644c81030080d0b500104005801c0c0302c80081d0b880d59500c081500701e0000d0803d055513480031403c9540107054480b00c20052040c881c480402c3c0c0703c840045821003028502505203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 405564433 1250 405563183 405563233
    0x30c0c0a05100b1309080a080406021612090605041d2205030306040501080610030b0702160f050312041d0a0b131d0304080709020702060c0d020703032309090603 71
    0x81d443e03030704003481403a1409050041c1c2d01214028840f20041d0380d00c08489210f2130489400307011603100460709000a0b541a117086401001c00c00131141c1c80d03400c0281f0486400107407400014044007002c00c0d01da2086056908071840030f0004000540b141c1c10080700c0d402c00800600307034402d410039004021440d049209400a00841c099503403401e2580611054500582104001d036021100307010146442000603401c81c2d40003c01d009880c0c580f66400c03802c00f00c0c00c40c03103500c940417441c17000b2618861000c80b041c1100c00440460300d52169585030300e0303014001d910a10300b1110020070610301c0c62110070026035011291520000d80d40354040300103038142c0414641160b80d960f4074001d07203941c0c0390b01d008019030340004800203604040c03415403180c0c2e60b0324813400750714901034011a0080464807030f03100391002c1c0102d0b0000e481e02030a00b048003e503a281980301c1900000c80c074140225046210562020941080205051400c0b00c00d074140640c0c2c003030207400039805104191000e080f0300300b10ba07580111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 405565683 1250 405564433 405564463
    0xf08090603011e150f12150b031602060103080d0b0f0901030f0b090c240909190f09020109030b04110306280b0306070f05040b0d020901020115050303030c0c0a05 71
    0x5001640d040c1d0010f0a029074000c0242072410003a200d803156000340100303100080303528010201e103451200c664003401500307010703403a01b115202001c5044881c80d000345105c1e810300075050001c2026000d04a81e034902c20300c406010418100162221544950007074180404050940d103198200000401d284400036882640e10761b07404503c0f40308000c0100c0a45802000c0c401c01003039100c0300e0000050384407000c0420195075000c1c40c507100040e44420390549400610007403c04034117240c44208094200c1c103041503403401070302d4005010901105442440c0100d501070355103401c6c09095075158076070031001800c169443c901c402c41004a43e9000c000703041c40340d485c000c0c03600c01b0b02c0e201e0885422484403020303076004890304080d42f44102d034a001800700d030b02510301d1500c9600d59840c0001a1070606c0360303401443c2c0142c000254211015200c0d00200252202a8000c203c50701100007030710a0314810f4014144e15410410200f01d103c1200e501610007540140207840d2031030665600c1c18545030942004a034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 405566933 1250 405565683 405565709
    0x90c2a08310320010f08150d060c091a2d0c071509090902100509120a03020c090115080a0213090f1409060907060f0e09070e1005040608040f0809060301 67
    0x91229030443d00402d4010007801c0aa1000c83c1d19603000c0c01d01400201986c50201c4c5045003400c40c0da413031800c100caa05803c200100462001500c00801c0c0c10900d0080501c4254190600d11a98502004070f42c540c001051510120218031042040d0000041040049940c0244810b02c00b10780d040c02804020214131400c01d040301d02e42c180142c02d29107940c1c04240502d190441000242e200e43c2070b00e0715007001a10b0440d58410581002489605401d94020240e01c591440201019000110002d000200b103594080c283c2e612079100b4900340510038850005425080441c10a0341c0700c0c2c014042d007101c140c0c41150041d40b100e0503c01215070f4080ca00e203805440b1040700941c0c200c2c81244581112254016050a180500103181d50780914400e50b01040740e40c40a80030071510404002c02a008018450900d505141000502010b08441c500348500070015850410602945c212000c4941c1611140050b61700e0b82c85845444411401c10b8460440c20004e540c00340d0381e1900254064058809842 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 405568183 1250 405566933 405566963
    0x180603091e07061b020402070b09010b0f0d050a02010f09092a030b01020706080604060e010611060c09010207170a1a011422020310090c2a083103 64
    0x194501180c2185005641c1010341d05100e000e40c00f000143c0c9842c9120b880540c124482c5c4007080c02032059140242419243d4010f20218600640105c10b4802d800c0700c586426072101001c100c0e005190078001170059020071450b0005500454505503462400c1c2131804d04996903200402c1603e514544008500a0455030003540607250058540c0107007562034200301261256001035511400350248206205000c40000e80c0c1d03627616080107015152002031012196542c25014082600e500f040030303007034011100010302021228094032a0500142d0041101e20710307045003903050f005940d001581c2c6e80141c01503000800c04058035500f0060b0101d141c2760b030720740c0f42001c402c6801d6074290009100780d0b0280a90a148580303d28100d41e1703007801042c01a600d842e080ca0540c0c011402c2e507c440c00540c14a0520924150440105800c20491002e40b642c811b8681903000741040075540001c00742c81b030911500c03082c82d02462420881c940d6003914109804035035105403901400c2e41e80220f4501c1e141c08680 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 405569433 1250 405568183 405568213
    0x60a05090702010b120705090f1f0b0715140604110d061508090f0312070512040c1415191106100603062301110102040506030f310818060309 62
    0x1c12801e0402005807400300c3c145400a0014017000e85400a0100c02702d0210b541d914440136120f10000c51580002211640c1d201f014419405c500e0003960f4035246103440ba01d18200714000c041d9001e241684a581076034440c8100b100810503a8698001401c0074401042034406038400c45014090b071040c54180700d00003c4d002172a4081c028808a43c6400544406151030700000965400c0f8489c9243c140300b50760361820071607080c05000ea80514031031040f028441400303c1c24030320740c00751110b880d84904080800d03401d200000c0300f210850542d6403010403000080e00e40160500041a9240c50003101500001104a01c0c00300107561100855000070000c11107541c1600c103401c020000d900700d07469030b4030203aa02220011018541541404580002c0301c105a0003941198050079006252036105e0904a00c00184104111000c0c5903040c0b00c0c041088440001000040132104a10b10b900600c203143d41c0c1c0e5840c66000050b48892901241c01042e001e42c3d03420001c0d511400c0104010b00e414482c00c904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 405570683 1250 405569433 405569449
    0xe120d061a0c0a03030c0e090703050105040c02150c070c150201060e0604060806160201020409020a030b0f0102060910020d020d090503070c1403030f0705070f1701061a0909060a05090702010b 84
    0x1254034001040203035164082c4003064910200b5010305000548803134110b410380c0c00880c0d200003542e000720010200941250180c1c4498141c070010740d001c02851024950a1340c0d00d0701d05504049031044048000b4280c2410350004050a074801e141400750380e80d880c0c20501908000f40400340150b51950700034000c5d42c2148221a5115000302c605000b014580881c583e15000003034030480a8890720717002c03103000f24001d4040318010304114000f15921022008024002c100c00c46080348980c01c50b0809103813644c070001d02240600622000350040002c0c4c010135074000e6002015010480c0e409000c18100a10188100c13011240900055a9030745442d00d8140c082141d2500300340180743c05030610080c66200001071740d50714842210fa403a50350505042061815140b40d000080c203a05210f4049500440700c440e419100303035540001d203d029100d00b031500402c05482000c4103d01014004002d440c9812080c650700b03c400034200d103814070b03282d0001c201d05000c2141d2280160391940000c3c211801d05000f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 405571933 1250 405570683 405570719
    0x519050111030c0405040b0d02030d0905150309060f0405070503060f042303030c07030302120112031409030d0507140a06020c1504050a0209040201182306090a090e120d06 75
    0x103803051843c07621004254083c0900d016544c051a50b9010054807500e40521103004950001c0c103c810783c00900720000c01a40c501e000d00c0c0e0107400301151146071a00d000c0287c90007210414081e06255450039002d00d08403600800903642c074070814200003595101440031b240038401c03c0030760552600d00350920f0340c400c4d01c042d400c0303507091070069110122110700131040d60303000241d6894a50340d5035044c3c1011800380c0240386114800245407000000c2d03080000b0040c081d810300c283c5443c2c0020380c580e0300c042a00c2c0184855680c168105011900e02580f04000a0603918801c40301e0110020065004501d0000d49140031142103600042d5008092420019031901c0255507268101c2c0349070540c0c0e1980c841144407030017405130800c00f0110781107a0182e01c0f07a10b4200340301d40b581c1202640c1ca4544030414083d0500b00703011b1041503040d46105092240464081d400050b0458141602d04940c4000615921460840a000f04100c040c004044040104008880c1060204006080602802c200c0103035007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 405573183 1250 405571933 405571961
    0x30f1303020a0320010203010909230606240a020105060a0909020609120118050c1c02090619050301020c0304090c030b0d14010f18031403072a05190501 67
    0x1510000000e03800590310290070341c1480c043d01c08000e4410f641440713401d803403072850b025400400003140c7e00e681e652080800e28051940f00900c41800081e00c28030b8410030400880d160410740003d8040d05181103a80540d80c4100d0802890340c0c0b601e140303103600d0340009440340c00503511502031102525200b45403101406000d00c1c208000c60306980011417912801034024018144c400410110940a5000a24ac01c0140822040404003460b14903150000700c1740203407081424201c01c298424a43c1044000694042c14520741a1150b0741085507030421205584a40c0714074800105080c1c5007800076111484406d002140c5032810440844281c4502c1e003400010903242c00b0441490340e4603e04490f01681e004400003012050b1640428007400c0000c005951003410030440d402094401c642d07090f02d803030095907005890311110b41680f5240c4825100c00c000207440c9a40402501071140d20150fa84000094020700b1a066558450406078440003000912a0660703100c001d005003801950b1480d0102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 405574433 1250 405573183 405573211
    0xc090b041d0606160506070809011b0c020f0a080c12060702030301180605100806100e15090103060e0408070519050d030e10110c0d03090c2d0308030f 66
    0x74115000a400141d15001c58110310804280c19840d1a4121268011050049800c12640d820400d66505064405100140300000028030300c00b4103220b1040c030304005540f03541c0304407080c010444200c118070300d01342e80c414000240c441e030580c1d0b9070700703039200404002000e096401c03595030421490503010f60400b00b03c0d811000030400f1981e4040201e906444012041000d00c0300c2c8000d8240041030590052a081482d80107000320080d0440011403080304101c4950f0011039910004442e4082007030100d42d000351400c010030000d505d9550107800105810f24000941c103503581203040ca16101540d080c1d032000380001d807010030302c04140000304241c1d0000540481884c0e195903010780d544030f107100c44c02c20180e840c6c000000d00b0b8011321020180c101c00300b101b4480a40d100d40030b00907651090b40070001c41e110341502d4290f103a0083c0035910ba600e40100c107000e11a860640742c5520f806461001400082454080003051480143d040c4048e5000785601e580302c0c9000408603860030806030a141440c83c1c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 405575539 1106 405574433 405574439
    0xa080c01091e0b040311030c0304090c0e1801030b0423011505041a040b010c1707051905030717090a061d1f030209010c0c03060c090b04 60
    0x151280d480e14401c106001c100b514a00040140004024000140840c0c00740428a00b89003002060300e181400e0100700e03a00715442608050609560303241d03454551540030801a4000200f40e9800c641e40000e5030b040d42c9852030510000b09070003078090014082040789035070103046942c05080341140a55400100d8003030301d156540129010701c02400043d5500d0680181701041e40ca00c0e5841c0041c42c1e82c1c4c0c00340409418010b1829040c081445903840000340818003038034100c20114105611020980351150a044a6285100d0386002074040a0049540481150025a400b62158281c3d030700b00c05415107980a103d02440c0c0c003001c00f1000052003070308a1800c0f61036407050704c0c04400380c10110003000509503902800d03115540f4082d06801225000394014075850405042909144035030b039aa800c80b0181030b420848409442d05064205103410040090180140d10500360501d41 = true := by decide +kernel

theorem cover : BRFrame.Cov 405395683 405575539 := by
  have h0 := BRFrame.cov_init 405395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 405395683 ≤ n) (h2 : n < 405575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
