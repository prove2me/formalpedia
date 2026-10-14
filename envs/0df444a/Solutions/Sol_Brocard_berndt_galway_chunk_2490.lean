-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2490
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:52:09.908805+00:00
-- url     : https://prove2.me/submissions/5bb7f55c-7e67-4f2b-a75c-e510f51a2d53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 447661870 ≤ n < 447841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 447663120 1250 447661870 447661873
    0x4060507110a061e1a010305070509030706020c1207031203020702030a0804140901050420071a1003170a091e030605270708030a0507030201060f030c03050d02120a030209150c 77
    0x2040d0315044450840502c0c13507410302030f0401c000104200d48018044000703541c24178002c503054032820025145480744c04003840c4c05014208000c9407240c1c0014427003120050603039283c2c03c0b5031009141152640800d000c028170031203150800b1100c051184d00a044c280380000c05941001030140d80317484040d80f01c3e5010003000580009030100300e00c0c1000d0014010a000d403014040e0b80b01000c1d00e40310322581d4059000d140c0c0070101d52281888040c504420313240018820765072039402c14200b4552482118441102d071140c950000102c240001026900c6a041c1c0f84c80384042d080c02c0c081e044c00e102100511500443f24420781c004003280d814018140604198110201807101c4414a0101ba11120f40e0304030455004590400208030008100d074460f4496140517921840c0c5403078101d000d0710407548443d0030038040310343c0072051007400304510044a02c14003c94030080031482d01661650244c03d100b4800c40c0d81480b101707012234004c2c1c0041209104c0240003c0011610391581035440e0010b0190074600d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 447664370 1250 447663120 447663131
    0x1209050315070f020a0206030105010521040506041407031211030d060608090c040908071412030a0212060f150d021605010c02190816171206042304060507110a06 71
    0x1c0740d42150700301034043d10074400ba00c0010510303004a006c0d840103200301410490700054122400c2d22030b144c9600100402d280f038000e030381002c1c2001590313100142c8003130b01c1c03842c22408030641110380060740c4001c403076104400c6050b0405150090303c0e1203020888404003400200400a055212031003810003a0200e900c1c3c040045c1814555140b50061003030f01d0318040d5140c1404103001c290103000f55117071594491b00c10b000d030802d030000140c10280c0580941003007090210510910100540280900d041e0312640c08940f5600c450806c406003401c401910380107110340d00c1149a240114008225007804441c000d1701d444510784409682c040c01240540b801d0359200c0c1d004039500d0381404201e0424180c49030040800782c80b03031203171946403103814045649100441c1c411010407400810411000110342c01c6070741c4540b50b0f9598201c8404003200c0b0355201ea0318040300300000d1031000d4802407044091990300f5065555a0340c2d450700502c40901404140700c0504200f07504420b08000807150244285004110b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 447665620 1250 447664370 447664381
    0x30c0501020c012a08010e090a140d1205070804021504120c09050c040602070b1804060311151e1821100203130206070c18150504020c03071209050315 66
    0x41c3c4002d583c010344c00d489110b0842d400c4a81e005180d941568962240800c0c0c90311444a2a440c1041c00c2c0c100401560f4103603244404810b001ca070304526035103180c80e85c3c86944540c064a5003141d00442e802000b103082074020078050300307152001c3c0d40211000c8101ca4505503c42c040305500189544040354104c070344100038000e00c00039026042d003200b0780b0704c41c00d07050500b4418080e41302c0000e0701031007140200204907180d000e800d26003028200307200900300708101a202d092070f640111600417030900603841348003111072411811089610080d01d810b82000400e01c2415004c856900c9410074055840004142c001c09a680d0039151404541925a50032105000c0c0d1645041011140800c2c0c007440c030510820450701e0440c90a00a01d503411286503503122170b1460079403100c0d402034115412a1800d5000b01c034401149030300101d124440c0066015103e940c0b001007005031312030795040c8c000c1d90700148540360004d2942c0310250506035044c00d150302d095440c0d60200385401e107004011b41668090009000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 447666870 1250 447665620 447665651
    0x311130f020a020f1b130908030a0c030c080903031803040b0301141e0d12200c0f0307360e0a0b0906040f2003010207150b12070302010507030c0501020c01 68
    0x300e10305444d0301a1401c03000041d085055100e0000f550b41c013030344021400c03844044850b88290b440340c0c2d208086030381b2414400b040000902c6040c0410300402d02d010015580c49004101d00d521807015140218515030783c82c2e903405500d4103482d481e048684070620011a00c0044440030314003810304240d610121140c1f0008001c819032030b0440c0d074084007221103442521500c1d54209a10f40c6078009100e0300400311080700444a0b00e450880b50080860791004000c01d4100104440a680c002140c81350142d641800c00c0584a203003a101b0842d003800d070300c1445940240c0b0050700d40405800f6904c0400541c0004040b103003a12119045000113030030160171070341000a184080340d04440c0d6500113000701d150644e00c01201f8500b07400003900950b12295410b60004186041d4911190b002d00255201c043d24640980c10010714070311100c080d810040408510304041404100011070700d0010100039145030010355943d44201c03015020048040002008503034240001d045400350403000007180c10301c408400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 447668120 1250 447666870 447666883
    0x2070605060a1a090d0c0e0f0420090103061a0904030905130c02030a031508190b06010e0109090506040f0504050604060c0305151207030c06080f010603060509010311130f020a02 78
    0x2541c2000d0070f00480703003d404114042d10388585044c2d44c042c0406009050042000d58168443c041c612030000400078024610001f460040d48248615100b032090241a0103090b4440c4222720703000b4071614010000f168054001a07000140f180c1324240f82226000800c81c4102c04660a40205407083c030100a1403c5c141d88000da00c0e20001c004100b4025001402520b901c5401c000800b05903ca1514641c004001740401009140700c2e011610140007004a01c0c20a101c144000c0d134080d440381c000500f603940980500004150140d40d420312941c01c02c0d1074a40100380c0a0a250340240d1b8030391454140c04070714410b4901860040c0018031051401e8a810000e881861004904150601c03062100923250480042d032030701d80441d440b814449040070f0342c0e460040e0030346c009810081c0c9101b00180c855008403040c0e0041600f207920300c0c01030380c0fa400300307500f50380e094030900e034203c14007800400100c2c02082c030b500f0709071760b004040429680310032050006407804d04000e200355036030005403030041c2e94041154 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 447669370 1250 447668120 447668129
    0x718080703020603060f041d0f0609010606080708040311070303030614031204150509040c030b18040206071103030c0f1b010e0f040902060c03070f141f020a030f02070605060a 77
    0xc02856085034041001804080c04050040c0410380000c207969443c0c1d0408158a0514021203030050252584540d890700204030703103485809003c3c0400c605c40c9040c042d0b4400d0782c0054440220a840384441103a0000c8024400da042107501c101101d4040300a0242400560103990302107a402c0c00c12002c0d44041c2c161103082d501c42e40c050355600080310349143c213440c1140c0314501e42e118281a0407100b070f5900c6c864030340d110764003c2c5008510518541c0590103407180c58001d03207403103400314001e01340d82200c075400307440c040d501880030701c030140c00642d1503071180c06030403006021741c3e04200c91180c14501e403000d450580070690300044489042140d6007125814948000d20f05500d03000c0c2202d0104c1c15401c1421f140e14050b1352201940c4c000d4bd1101c03412205036031500750403a40d440c200c07030511505c4d803051842d08403a842c175001c03080713401d40400050b80d009c1590340c103003d1050341e140e45000400a50001030000c00340f50700c03200180211000b91000e085414018940440c140c608141002042000340c0c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 447670620 1250 447669370 447669373
    0x160507051503090c01050a0c02061b010b0a060212090103091a0108010b010207051309030302040f0803071101080603060a051005040911040c0906020a03030b010c0b0c0a140301050d1e0506071808 85
    0x20441000d40005800018140038201b56549820303038201141c07004964800a50801000551442642d075007101d485100540c090003000710235000020044518128410540180c5c0b186012108003190b040082c00004014180010704444a070b48025008141c05034440c07800d50385000401103900b0a000302d203101311003403010704181800d11000a804000303048421034082c1c1e9032010b1030200b6000f94102c40c06071404c407030f00020f40c5a0300c4034081c0c1c0d6540002d601301c030101d102410340403ea5000b420617501650707004018207416074940941d10004c01e0010b105503c1b00c4018900016103031158429103041da4042d402210f2450f901c0c0013404140c1d481e804020b000c200000e2401c100081e4003044600400da85803902290b5034160300012540c040c140100545030207091420300082d0151007008103144c4502e500da09000f5902c031810060680024440e0540001e44090a00001989a07007060900d034041c410002418001d51910703858400700700c0e0800041250960311314403501d04010301c0c400a007031580 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 447671870 1250 447670620 447670627
    0x906060a0812040e04060b06130f0f0b070f0f140d020c0d0201090611030d0c030507081005031f0e0a060b0a09060b0d0f0e060903090406050a030f171605070515 70
    0x10408020f4420b078454014a850403001081c00c01001da0840c09450310010040b5440e54008282c5803581003403031140402004c1d1303c1100045501c1081906000c0f108020241400c00401d901c1e0038050b02501031085408060742001a030025066411442101e200c140050821554900307000e4500744881c1c00c101d00c5a1111003c080041c2c2c0d0040c0940c0c11b40ba0f031460008001c03116010700c6450b5000d01c21004245c5030610001104940d4103500c1070b4860303052540e4540107a107521501c40b90004490150603056001a07680f00980081e48243e851540403159001032aa00700021050800d4602501200d4158a960501e161860090080b1000d081d01a03801c000843ca0320940550b248a03030410001640c1e110040b1080b00c0c805070f03000810902204080d174000d840c002060b95143d9000b000c0390361289140071004074850800800000542e80d0180c02d807041a00301707840e4021200324901400706d884000704600e0004004110041200301d101e40020f140250800d0104488280540403030040402d090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 447673120 1250 447671870 447671893
    0x190323040b1501090e1311010305040f08090102190507030c08060f0109150b031806090309010504120c03020d080a030f0504050c01081f0806010906050d05100509030706050906060a08 80
    0x140c1c801a0880b446000c035501001d0b05000580307142c41d240d8010300b030303000004042207940344d0744c0c0d003ca50140b8800d001b09500c00009a006400b112026503011b0709003142c4944ca20005902100280a924130500494080c060011515400210b0f01801111190442e0b8003c20030800094561805044082c0c0034080b41d00c0c020f80011034584051241e10f00303031512400704801c19902c1c4540700340602810380b00e00da40c9103080c05401e00c020300d41d560700030303018402c180c001225144080145c0d5104001650340b00e140516100c4504441c0120403001da507030954451002005a5517041c545206034419202e050700e0b501c400380c0107011981009607a610310790400e810000001c0c0301040d500a0718409007882c0410341c413400401c80040c240300301d00346110248402d0200380d500000521904846010070144161030300e800074071243c9005043c004107558082c2a600e03172420784c5034011076841107040c41200e007080b07040e032651004d807541039400c0d40750360b04800144043d6060680b819405000c01400a0079000100e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 447674370 1250 447673120 447673133
    0xc0209042d0b010e04170a030b06030a0506030616020d110c0414090c090103021804030314100302130c09300803040b06090408091c0506040c050901080c1f0519032304 73
    0x8808888646c14000560042007a01076800f12800c0e000107040540c6030b182c0065100002d220a44119210307115020010340413480c0400b5900001e41c45501078404280c54031401d03103100b101458a45401c0c095a038840030140c40d903208502402c4203620180e905801c0c5040b0ba5414002c2c000c2710300340500c1c04c900041c801f6841b0010f146c11100b8070048420000d40e03072401d04a0081a10f240409410b541c07200c24481060425401d40301940d0080340e4240d48451060b4045044403140c06103a000b003440c00ca410824081610f1000c044512030310300080800c1141417280390101d0540c42c1c11101c2100c00320500081c0280324095a0303000d5400c1d01c005280f4241610303240202e010340c488080c415030206203e200c0700398840004041840d41b0000f00c4109007000c0c9840400c200c90b5000740390240c441c410000a60b540300288240150300041d0008075403001240c40d00220920580d80c0313100b13002c0204503000c05401e01202407500c40e8240d0390002244c2c24090440714800d08803269858446d04441d0501c03000c20785c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 447675620 1250 447674370 447674393
    0x60b12160513172a0a08010b0a050f030f01020c07090e0f250503060a0204090b1e01230a0201060602210f030615030a0c08010909030c0209042d0b010e04 67
    0x400802000e01e0003d41141103107007140c41d40f21420078001070552010703101070091a42c100000c045601c20481911400f08a00f240c0c0502540c070303400003280d2410012414060a41150b0700c10180c20364402410070621242a603200014140203135000741d608008005051084011007a000e9001c1d20070700d1100f2820907600e00c20004c00e41101c1c1c18030822043e801d110450329a004001c09825540c59181020192000750442e1003003500301404c0994400d420f1620390310b00b06010091440e14503e0415150046424450705186800c01e403581411070402501450094071890314144e0000c200c0314241180281859892a07040d400b04e00304007000c0400703602000035224080300054070191281d40c1c2e00c00082c040810000610b5500c03c0000a0080b810342c0d5800c042005241d07500c1d0307800c00d6640c88501404070307603501da0003400050000354030f0b100502d03000700f010f500706000d41c010080081071100030a09072034034142030440340540785a41108112514507400e00601040750034140a00c1d0a03107c04c500180b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 447676870 1250 447675620 447675629
    0x406031a060907210c120e0a1502030103020a060c08120a0507020d0311040506030a0612030c170405301c030e010c020c01140403050604031709210d060b12160513 71
    0x245c49022914040d8440d4034240a441c100d04021310042040400250310342c01402070945469007401e5503d502464280226412243c3c050040c400b100c1c50840200e50400411000b15501c0404100380b070f01c19030010b40043d0082100c00c0c400038241c01d008001902d810405c11054040c10b040c40700040203109883d0550303040310b5041c0d45080d40d13a41c907410144010700c038a42003022100e0400140d0000c1c103902c021142c2000d80708250040f0908800042d0011a009610031181c2c071501d50000b0102c0c01c0c0d861402031540c1e840a26204000c15600e046240c248024100c42c00c0031456442c20703968445925001d08140c002c0000020490b070000c03101d00a450352060b00b1207505100900d001401050407040440c1c000315004015030b11076040502d8010a80d51340201c2d442c000e8030102300840c020b44004121810201c540450400c1e4404410708503080b5900301c4614441d242d0341d1143d0014092320008010284054281030703000c61443c2c42c00c40d083c075010020044008200080c00755414801e403426001c002d45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 447678120 1250 447676870 447676937
    0x604021003090503070209041b1a1903020733020306090f04150c02210c0606040f06260d090305120310053102090d110406031a060907 59
    0x1004a0403c1440c4d0302c646031001b034101410307500308000c0c0300b0001c03500380c000f4281d80c00307110300ca564400b0400002c000d00d40220a154030104510540b1515003080c01c6c4900000342405410a045038850308a0001c0341450750181c2c0503541ca1000c41704591881d40d150408003124218250f090401c0070941d541c40c02080d1611360004500441c040c00019003000c0700403401d0034424000c11941f000c00030f45039001a140103204080c1498040004030303006082e00c50f40c400802c02403104d5a030700c0e000c0001500b080c501000c4120754030500800c207001215031072908500388607800d06881403401d0312285000c0d003451602e030803c150f91005000154004c11700d40c40c1d12000c00d19094998492945100b840c00c41b96010070340c05901da40748804001c0015550105485001c1918550988005144816441110901d585c01280403040800161800d070402d102c4c40c40150001410544954403130050014103642c2501001c2004100326441c84c008011a03480401481c1c5040c01003418284440340d101e042e810590072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 447679370 1250 447678120 447678131
    0x30f1104080a0209220609020a060903031704170f031005040915091b080f280f110a0b0403060c0219030e0f15131703120901060f090b0f01020604021003 67
    0x21401100c1c21200a5417404200020300f00c05140400c02031084003001c0740240040100090424001c03202682144d0301070f101c0181d156021030098210100c01402215680e41d04688110b0780000000a45504180000044c0c0d9900309025210101c60003a4040c0788220b0a005041d000941000c16070035114100040114001200f450580e1091603d06031000b500702120100080400f00081c81c03003031002e4002d05544441608820600050b00034100ca81d00c00c202c0d0b00c8013580001c0025440035040c0d0b01404846030103450510010340190595803000022170408030782070003441010712494505e9100d40c002005800d440b801c2440e81030130322150290500008800032580351f200d103500300d16194001050f4401202c036040040c100e5070031041c1c09204046466901081c00f103400031480072450031f140015820891802900032058500a040c0c1c4119500c5100000c1c480c0b03034510b4184050403020002041c1071014509001209800100705811548000c080c840541c03684200300d140c010162401281 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 447680620 1250 447679370 447679381
    0x11160f0b09030c131e020a17070207050d03030e06010905090f0f07050d02030f0a05030d0b040b03061305070e0115030f1e151e0305070e041203021612030f1104080a0209 74
    0x2011350000c101c5c1458022040312510342c840f5030081490204d60b86030881c0381910300a078444040b0044410300096804504d003440300b440c01c0803011a002d4420714021900b45c034a8005103007000c1d03083e444403e20390745960030710a49920034030803110041c0801001380200450144c20307070f41e100d00c5446102d026101c0c6082c0031081d03403010b04c410009005064110750b800a0580b4002e03a483d03112008441102d481e248510105141c540110700f4001e42c01001029541c5172501039200d1521800030807541c0e07125010340099003805000c502c40c000d10891411301005180e0150290a48a6242c011811185001d003614031049030f0140004034000403e80c0060040340524032440c165525030005079030760240420300d014104104030a042580d01c60400d60b82c1255803504e00d1000d01e1020381d0000c0c4100b032000403e0510b24480d034003900f0b9000c00c12800080590050315079030607200800c440040040e40f55000f0079008009401074121a818000d8401c0c501850514429218050018001d00c100208000b092 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 447681870 1250 447680620 447680659
    0x8060f070c0c2105030a080601090503010606050f09030c09070c0213060501050706110f07080c010c0905280b04090e01052d06060f0f03040c120c09050711160f0b09030c 74
    0x1030f46a0744030342100d81d266a01413000e44085021181180025500c117800300341410706010714003c4414540350325003010180d02e928170054100c01102c9805200b150302c0e8032180d654407000304e80035041d1030300c941841c04040e006001c040e02a4201400009081000403c01640d01c40c081318140d40c2c002c0360000f44906a090152500d225880180d0b01841c8046035541c28054210010658140460004c02c040b1040704400c1c0c0e180c14061151540c0400a00541368460072501d001d40503d407000120305a0164440001029903001074000d0101c081d919040d0801101d4244951908141019080403141d40c04580d18402d48241c07000400c0c040305103070b000c0340b000c1d242c040c1926640c0701c20400c0749031101c00450040410340c10440e4290340210b20350200080c0344080400480c40c036500704601210a90810f58a44060180a0300e880c040010091004030b0800c1c0520411000f08090182103c01901d84102c0182c030176040d4108010042c0200b00c1850603a60015044860701c03c16606520800300c3c0000ca003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 447683120 1250 447681870 447681929
    0x61f09170610120c0b0426011a06030c04150804061d060a0e1504050c090f071b11100806030120070318030507090c200714040b04020408060f070c0c 65
    0x24a070500220700410f0881102c6050f14800c6088600003180030414114142079402c080001325000c1c02c1d1500c2c9c40520b0419000640e40311128181a600e07142d43e0302d9010301078010710004000001e00080900040106c14042c03400202500d00c403c0949008a0581c0d0ba00c2d0180580f442e800c06640b0358203245039070380a20244c0350762440803400544900c0c040c14460346944101420600c580103020018680c1000d4203500c0d401048141c0d140700500d208910020f80c220030341502650741111071840c60080d0303640e040c0c0601c80814559100009402d05200381429507041c40780402c9003c0903001c0c0e0b800200108010764000b9501740c6800d481c1c903101c0300403404a11010f41c0001d050b034011910b001c1907444541c0c211070500c04081c0d6405883e08006082d0705641c1502052101554124440400402c101c196000048000007840002c54195490008040364001e038480112a00300c0b004000c070780c542000005030301000324208030428a1255903a0600880d20f400340864410007514000e80d503260541c0c46 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 447684370 1250 447683120 447683129
    0x103021b0f060f16080411060702190504060b120a15051314060607030f08070522170303090a170417010e0d09060c0b061f09170610120c 60
    0x94a0396070081c54181512400101d600601d4591050085618110207a82c1680150043c1d6542040341d100d40d40c805015804a062080d031101d028094007015030355060f00b0013a039600510754800700d00d02c4e02c01030000790b50156100d000c4240c0c00b8440d1041780b82000400c0d503882880003074006158280664a00c2012050340c01158203d055003000500644036030344592803c0d0500d280ea80c103c0d0351210108502c51088290060010f00c0c201d4051181d00d00814040d0f8120400307091031030419541641100f0000c0707103c1c003105003030794608804000c80502c940013518440e07942005989035150090030035a1315420084005c0082d200e0315103404601c1e0300300080d240501301c507545c1a21103204003215180a041c0803049a840c50007481911001130b401008104111707000360301c80403032f01551511141c001d094024112900640400072222545041c40c48100b80d525543e200e403600c035802d100d84caa00a483c0b1001e0b20300d0550107081840003040c03448092108448020161000500712440e2007014505991300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 447685620 1250 447684370 447684373
    0x60f0908030f04031b030507020108180f070311040603030917120703030225020a0b0a09030c0b0307021e0615130c02010518010204180902150a09170d09050103021b 72
    0x501510b0741c2d0070501c00340164001d58070204225181d103642031940120410080104900300816001035018420751a4040c802d084144440d002040a1034100400ca200107101c94120304814010401c921521318410402528200292400e5990107421200c0c40c0c025224006211207150340526001c0046000c8140b404241039198145842c01401075001250b0024034200140c0d5010511901c40007200681c0740c00814003080589003480e894010f500c0a0301d640c007006101900440414143c42c0131070020075080c030a0507564902407100034140540b900b142401e05070300c5100042d0301840050400d4008032410f2003c0300070b845040c0000c2812503015001810765080001c040d12094041d484a4400c110480c051144020b0480015080707105c0c0d40500c06650180e840c0c4c102414201c0da1040754624805440c1c21a6050303a4000c1c0851604203400c42c034000340486c1401c1c00694008250b164a480500d40208180c40307074903001030300203400c1d801000e0405070b001c9080e03607170301da444400d0b420510150340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 447686870 1250 447685620 447685627
    0x6031d030d06150c03080f0a06050a030f0303050c0304030e09102601050c0702210f1608120702090402010e0f060408030c16060801030b060d0b090303041b05060403060f0908 76
    0x41c01c0d2030180881e03118040340300c81604074544919000300b824140c0254140d8503d0001d0f5101000c440801c100a0034006a0039a22070300811326450740b40d504001365000311040381d501509858010700792840141444071100f000c0c4184000280c1000004041c89030480d17503901c00d59641903030100109599403042c0301c51001407500607000080304c070008001700180350080c40141d964400507441ea1154140080d0003412038800c581c2481082d81e10421455410002d0300d82d000b100001951400d5a2080480d4240600c000100041e02d4100120110b100c4108680ea00b030040a13000540112401040a8140a0503a110a0442d03654480c1801c58505c010b00c07158a503919800850344c1c1c0d070441d150881580c8100a007190010030061800fa080700d00c680d46040490f0700395940c8581040d006000d00b0b800004a01d00400080d82c0e21440345c0c820a4a41c0055403645420700700007003d810000c0419440c00c954020502031901e401e000c482c02d0f240c001e400481c89203020b880c2103005000807040945145c1021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 447688120 1250 447686870 447686887
    0xb070e091302040b1e040203040c0801090302030d14010b070602032a070c0b03010f03170f0412032007060f1b0302010506011403090d0f020316050c03010f0b090106031d03 75
    0x407200e010580e0300903201084503040c2c0c1c4041c80010320202400201c070340b015104410342450a60006c40d8007501c14803020141954902c40542584c42e907840882c0903800225100c0300815041c443d45c0480302c4100b6034644554904030742c51b07605100303001010703101540010001e0310650011903049001d0b9218164016168035840160410742c01c0070304203c441030404140052844000000d40b41641d14040d01201c100e0710795680c05a9410070750315020580941032000182005045001d00002c0c04502c2400c0480d141d03034500101910515404c0701d10441d21652400040880000c01c1001d841d01400d203440824500ba00c140c1b081c0b089804102c024441c1141d520301095410340050f8054002070b242c841c22158002020b40e4035010840d0483d5456001c1540c10f40f0045c0f140d8110403012140b070056074540f1009042c8002901701c3d12400750f503140c0c03111001101c9402c1c244520b220140e800318007003100b101c120300000c03940381040c440e07a0101901c034403400e80c05804090303030103c2001000088031f6031181038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 447689370 1250 447688120 447688141
    0x409032f0c0603061302090d0c030605220f0b061c1112071514071a0405100204050114070819180918031812030507050607110304030b070e09 62
    0x1000c40c440118094488107020609194050300e0050344001c015681c0202c811901070001d401075140c541d4000ea0102000004c034142040a00140d070003080c020800b450302c400c0340030503941c81a21500d1401b41e10646640414844078035118040c0e484082900039494000014409107050803480b0410114594a0020040526500c0d0100300090360400301200320350341c18544884035407043c041400c880c43c6640031064420b03c0d111810810074820746007804444e48031500704d9800c122440f25600401014807050080030007140c890410000d1703080d450b003810000000e0440d81e03802040016200302103002410405a4410b80d601c00c006486224848560000c005205c50100300c0d6601e0304550524000c2010007440c0100705121070840284e003040346140da81100c070400058801d000e8a58a41000700e01e04160303007910035805010340d071101c1d1103d0107420190b08100c0050266030034170840704850302c440c207404000d07502140d070041d400c1d9a441e910b4180603145443d08003601540142c0010811841c80301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 447690620 1250 447689370 447689447
    0x20d020a050c1e07030b0702120c0a110f0607020603090f06040c210c0b030907051504060e0a0302010804030807020a02040c0f030e01060b09040b0307090f060e0a020403080702040903 80
    0x184002c642e0803082414101490311803035041210560840c1006002081c003411001c0d40000b11441142c0345001c09c0e0440c0c03603498000a11010207500880c0d481018000300000710351680800329159043d288010300041c1c0f45206070400240506004800902000c1c403d0044040c2d2401e00d9040d0f03482490b11b40b91640c0d90441c54000d00d45035400c0c4580744680c5c2d51010280f02501c5030302424003a991401c11112103815000205030580a200c1c00c1408505521000b0756105460352000100c1e4550342442806030920301914245402070504c09004c1026030b0b41705031748681044c2c041c01c0c28001601d80100803030800c2c4445c280650024100105490b210364000c0c0340a2071604c50381e030100104150700185c0e9098032480c2c4600d8584480c14040c10340745283c1030f030020b10791481c01401c4034946650f0304411410b645104a0000f8500e03a10002000a80c42c400304e000d510001c145403c524090641d641c2808602801d04040d01a685e2400c5901c00c140c0217088803003003942d54210109080b04030b6080c3c401c1001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 447691870 1250 447690620 447690637
    0xa050f0d0b011d07020d170c0c01090b15041a010810080a050a0b07030203070e120a0b0114010e0306040c09150b03180d180302040c090b0a02030703080f06060306100201020d020a05 79
    0x3e02d401e0020781139034030100305070304010055560501d40580300001c0503010304010340881101c2e0010041d0310310000d0244185410076200318111a07aa18106808011820b41c41c4461405542040c40030800c0342800b070b40d03102e40e888090900f01c0154071803050181001c80960485149482040351076030600400003080c4036a2445a107408a182c2e65140c8224164002624114081003152207040f15910b00902d15219030048007046501d90022609c40e420b031642d0070703488180007211882403c02d56580c4000c503140000e00a07002080c1d68105a030b00c0703030501e60803031040c00d104a90703d141180c1103101c0e40a00500500f03222140584074105144148103111001c0400b20302c2c1e2094071040c44034a40031701c841f5594240c1d107101c0c44125a2441e0244009481c211420300c0030481c0000d400b01d10384000e0b80107404151055402542c9403081d9280103802440082c0014031145038101c1005803130351300d04048035440700e400c0d40d408402c0f006104082c1e029014032101044030034004180d01041540c048003030701812 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 447693120 1250 447691870 447691919
    0x1a03010503010f06030f0209040201210b0918031e0d06030302010c0e15090f06040e01030b01031a060d060b04091e051020070c05030715021b0a050f0d0b01 68
    0x1c800c3c160280201da01d507120092407801d0609440c2e0140c46c01c5401d0716801030041c1841c0030040300e1000f018a98440030440310b22100c2da10300e0380b00010309042400513440642052010b000b010341100d03e83d0769004100c06c0b032031030710682d01d00c036921001800180c4040c0d0704400d006211042e10ba15000e4080c00c14008142c000404181030701c0300074640038000303001c407a00400526151003a902d0a01882d00b8040008580100d010000015441c51041c07640e030003540074111400c0c9d154194540854966550500c1441c94958403080c8101503861303c107080802e03035011400083c1070107024081001790030b02c4013002d080030240e050340038401c02c00181100000c921a4013518403940d24045e9060880714007510fa0048202ca008014883c80f038504020f24480f4060384603a2102d694440c002450821260040c680758841e81440c42c00141e0100040e00c0c17030010182c03000b0700c521211004038484003200c0c81a81c1c4a59590040284140c5070302c40411111504001c00c0d0300c3d590b8440a07500566200104000d840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 447694370 1250 447693120 447693131
    0x2030607030605040c09150f0509030f1e03250221060912030f010e040c030b07050d06050907142b0209010f0f0801050d0201050c0109050708010e0d05120901061a0301050301 76
    0x50740300e45030351010344191b0040c1c120b61f010030100c1124008190700e40764042c40801c00c1051284c1e0b8080102c6d05074106a0780c024840701d030600c440c14059140707050703104401d075009100700d042d150480d01c00303440c58484100d40c01016540500003d4885100b074a102003590121529444404002182d13091081e2140301c100e40c0006403088007100f051004490780300c85108200010300085010b20901900705000d03070840381e0b210b034490300d0740001c91000750b40364000b03d000028084080c4600d40110300040c041220b00e440c2502e00120054032000580c10788020b28200000d51112840000703146240480b20300360302e00101ea0400c845280250f201034042130108000042e100d41c800c2c0b0540c2403241e0208103590b0702c002a481d007000d1041e00c1c0c2011a049051050600c17004030840c400348190751030b40d80179100625002e442c01d0100c0f42115106126424150092021166165040011154000003909125810340e4814014900510641d001040f8007504010400152030501000e107041e9901107008102c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 447695620 1250 447694370 447694391
    0x20409111017010b1e0a020313090c051602041508070518090304060302160f0807060b0103180807020d0506090703060f0b0d020f0a0509010816050d0f1403070203060703060504 77
    0xd080c80921041442ea21001005010f00307440000030780b880000010500e80048820030340c8802503000181c2c1100142d1002c105120413200034030664005104103e0104202c20741000004c0181c07260503d02c000303524041d80054110344959200354001342c00c20701d5829103a07494003203041e05d0303407054410f40d40f2482000c02d1200005605c4400c0d9030150a04100541c81c151511805602a4112802020003200708401c0c4c40b012800410030300a402c0d03c031b925010307a503000b6880c0100c2280c0007a51810b04061404000c0e52900c006501ca40d007609800081e00b40e120803861000504001d47c00d0300007070181c09030805001003940d00050b800162441b84105100c0c4000141442c4c046465030001994003c071a441c000c03015060829080641560141903550226150130200714801000c0c1d0000e007442c1d2100c00940c1c50b11719840791600140030f0465420008125940341c405100050280182a080d180085030009a1040088036116075000e020340d041440c1505020b0002e142c18801c49000c0c03070030001481c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 447696870 1250 447695620 447695627
    0x304320105100509040b18030a030f0e0a11191203020d08131a041506030311010c020a11040203070207030b1f06020a0510050606160f020a0b07080f160204091110 71
    0x30142d407005048080300b50f85540350024034100181034032062101550b280064207e06000408402e109a1404203c000304003100d02c003141e01540c801400b80c4c100d031003c100018458201c94850302d10840b4400008031030390032040540b52030f9034407603903c09802c0d03040001055000309400b034003030003240c0300d030307082a514456001c10115030b2582c01001c03201c040c1103508401d103c1c904841c0d006400780c42804104040b000c0c050301195129002500401c01000d401c0f202080c0900901c4100741d80f070b1018040d460026a02c050a1804c85800030388120380120000390480c0c400c1200c10700550b003021840d070072410a0714162003201558806064094416000400c90600001d14410381c20390020040c000301c0743c0ca00c0035130300600d005021164001c3e82003014403003881030041d4005d00c00b80210f06014901580348104003070310341107a209040750007080c800c0710003040c140e200f603a421110310300c410350303030b641285018061a071090480250321a14212803a42404800505100018400e813941280d541c030440080c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 447698120 1250 447696870 447696901
    0xd140f0c03010b03060405070c050a030206040611090f27070e1302040e0403080901061d0108010f090f120309061404020111010b0a0504090206040801060b12070518060304320105 78
    0x4040f2450800200301d15007001c1d40281c1c0e01030204d1400701023000055a03514140081c2c00c0c401d0300180d000c04140403c0c00b100303100314500c0d80ca01d194070074a030482003804908006000641c6074460030411400b00e0340d20361380c0070f2000140c954802c413600c0d5910f0030040161114100e440000c0c001c0000b00000e4008403828403c4406840440091194a960b51f6404450f18800108190200d540f1620b001035607808610511030462260035800b5a298149803450382101c00c503200c1d0b46031460602d000d0318045058000000c40881c3c00c8540c03c45000b524840540c080d0245179801480b40d03141c900c0410404603a642203034040d0303100340e0f905e8a580c001c0404c1c036401d0750101080d03647d101807a10300070050303032400b5800b600c03c00380702900301c504141c2d5500c4110700312881548016601c007000590000191001503800340d00040b10700f05642041c2c07807004624500000c81ea802030003480000080707014031804403100108401d14000c0d4a0321f116031004c50010148444402d16500d60070703d00825004c08501000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 447699370 1250 447698120 447698129
    0xd0b010c021c0212030301090b0922030c0c0b04060c1a010f1e1a0304140a080307121829040b040201140d0212010e131104020a02030d140f0c0301 64
    0x201c44020742c0c0580d1825480000764801c03a4400d00d20507221030440c0781030020354000c000b40d8100050b03c003115414002c60b0a001001115004140c00c00012642c0c09150040407003601403415034030055007440c0c0300d01d8000352a0807422040c0f20215000aa050780303c141c180e8418417030141081172807118000e0b100c00c0c0d05d0a00505000b214088424407044821103c1c1e41d0388011880c0d0400d1050781d482c18555520944c0350440048440c0010810007130007222a14072030010200c800401d0074007078680301c0c1003003404042d103550704100b42d910000c90a81358641088500900740c4800b030108a52500e0300342d032251201009072941480c001a12443d90003030454081c030070740e0000d45c601c09564640e401100c0c1b51507000350192070708000b0700c000c0c3d056051500c003802c42080270144480d415410044002290381000742815401c0c4a040d18600000e10b215180440c1200192030240c6c44a280d844203034111b000d000c5da0385801c01d1900b540c0110030554201c409000f00b107142500042620f696000020600c800d000b07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 447700620 1250 447699370 447699379
    0x100b031003080d020f030f4f1212051305030d0e031b0d0e0d05210928060203070b04150204030605040b0601080624090a0f08030d0b010c02 61
    0xc081000c90303010801007520400c0312200501e481c04d50303501450b040e00b003950688522400081042001d04061000c104a02140e03540c0d141009030000b540d01d1260900c5181340d005103600311100d08106079114940c22060345c8402c0030b46581c040e240d0024800090481c81900c014106000b107850300070300800e10300e14a0380150165181891164041d8064070a942c122000780c0f10802240d10070708018110b03800144414005040c401c003808400401103481c6460302841142500d940c0400100000b598210b00c80b03101b02e00408202c103803e400703061406050000341d00440c009041c0c02a0900320b60000c0b19600340807000d11728003a20b424049999000f0840300821110000d001305001c984a4400000e22480344100549040d440f40d80b414291207040d501290140c410b402407100c00c1da000121603a000c1e0055174107000e5041000321215040ca4588a941c00e40800000d40040340d854070801d450103407000110701c48550ba6102081030766a0f1007400d28203a0f80b440c20042c644603610864548200640050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 447701870 1250 447700620 447700651
    0x203100f0c0e090907331806030203071b060b06030c0a0315030210182301020105060103110d020703020322061403090c090c090a1e0902040b04060e0a1d100b03 70
    0x10b40e201205180e41c41028581521003d0a0300c4c0d1260104961400e00c1e507902d1f00300ea0740c84e03004035502003512604003600b81030043c02009815940480703031428014100040201051803810a4001030480c10038460b04103800004102d03141640e1801014141d403203603030402080782e002c560303403845c0486804020750220362850460039a41c466500e00054600c40540c20000c0c1d5640d121242e01c0c0701c1da2180d5840caa001e008808440d0350b80a02c180c952004081c2401e20441c1c0b42c50341588101d202c0c503030540782c83c29800310f521406c0c1031003081a10464810700e801c1d020b459220328515200d008481c425040010542c10340900042943e001356801819518000c1855821030400c1100182c002010844040010f0120400c160f0340d1108140c01440d54024449840780384200d00c00b0080f1081e00845041e5004102c10480c05030004100d9080700c5140c80c0c000000d4440c6000100305450310380c440405421600d11802c01216903180303060254880b190b044c5410b41e0388e654120703014002150718851124094 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 447703120 1250 447701870 447701879
    0x19020a020907200a031206050d0c0509090a02060f030f18030909130f06242304020f0301030b0105030d0f210f0e070311010203070510090203100f0c0e090907 69
    0x3081a000c515039565000301c10f450f40303545410316000c440e4000343c0c00900310f04a4262251000d10800010300002d84500260302c00e25107604c211807400c2e00c07900d0b002d0420a800a1080311091000e104207590042110381e50701c80c18450581a038006036042c019140408001c505142171001e482122024000065414010072000704280e08038024840261540001d030b10b00c002604a5194030902c51040c0c40005140644001c200340e00c5900021032400920f250900740084007031101421642c501e00013440c0c54181200c008200a40070b401008a000e000c00720012007004400d07100e150584200f64112030350035440b40b10888403c0104035201e0046014900ca110342614400400400c41503081300105594400d0030400c42250041620b01d916074126440510400c1080c42054200d0b0109100650030301265884480d19603590507104042c203680c2d8101c000071514148110000813004082c10000c100011003240040c00c00f005001b000103003020f412031154a0321102e614010094140100680c1c0d051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 447704370 1250 447703120 447703127
    0xb0d060b010909020f070c0b03061509030307021f0806041b030222090e0c03060f0705130306060306050612060c0a030e10090f0507140607030e010507050a0819020a020907 75
    0x440d0410707041051409001c10052400d000405511854008490307a845840c00d111041028a0b0081c01d40d0100070401d100341c40d5184481d1110112198400b1039460080400181c40c42c070403114025008002904c030340130003081700841d07120180496220f025241d92010f0401086421716a07e000751200e203480000d044a200c0c0d4094031811807030420b0003244181955810340410101c0e4008022680c8480040b0031611083c82100304040c1c06500803d001d00f003103507000b002c1400040c41c88040200224040100b60840c888504c000e60700f0003c10000b00e83c480c1005400b9003801c03200240030301002051440c0021000071a01c0c4034800004940e801e00e00211400c50241c042100445400d21450104818103030304c03071142e40b40003442200490700c20381c0d0918005003403548551101c4d445041424242409484038401c4a0381650b2614000071071029500050301c40b40036145000d00a03100d800d0640781041540c00042001d030590440c10200692035000407a90344414800c0250400c100c14080b0300c1e012301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 447705620 1250 447704370 447704381
    0x507060507020a020405040b061c0507031704090c08010e240913140d1412010501080604111803010b040204180b1c0302010506010905040903020303041709100e040f0b0d06 75
    0x70754070694450001540005c2d05485056134195040107602091000500e0103104200c00f020892a1130100c0000c00e480d030649a004612018040c0144c40e00c1d0451078440c0001214050020000104011003a5480c0104010424040c00d02071a5001d0042000030f104608111014a0680340940780002100107001c51000b000e010381c22501070b18004240003807036800c4440c40d0000345500030a003c64410500070000030720380c0d04507091070404002c040c041c0301141301580d06488003800c1c2030b4065102e07280450010800c100c0d180301c00c424041542c3e03a44902642d04549201c40441c002d00071015030300c04000481c45036108801c0c100da035a01d912460004c1e00c0d002964811402001103c168040b040c2007407816841c441c0440050350b40d207040106560b00300704540d0145c43c090358100716410407903a01070b60301c1c400900050921502e100c510145d8031040360495184500c00b50480300c88040618010300a100300502040c400c608042403ca400080c0e0f102c0c0b1300e504078008200c008221955241c3c2c00003082c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 447706870 1250 447705620 447705631
    0x4150314010b0c3012090709090f1e0b0406151e1205070909150f06060e120f19060f0b01020319050904110712020c09160c1b080f0d05070605 62
    0x20550040c120007048000c025000048000c107040000c2d00c0c6c281001400c00d00310381c02082d0b4003480d00a9040200e8180c0460b006070960002d6541140880322446400c04800b10100400c402224800c200030000203401c52241400c07110422070055032500341c40d080703090364100300d8048011224000c001000e480c140480c0824000c0007600e04131902e407540e00303064458006080d00c001d02e0800d248070050b001481784500c510641c0a00b001150304002c4010130191521025a200b00004442c0001c42c0c8010311030781d501011003004450a400481c084840c0d20303141508150344e242e10380407001001c82c0c02030099000c40030059000c2d5280c2500b0029400740c0800144c1c14408015040c0a544d02d40d40311882003101c02d070744c140c4030325880706201c0c0b03405050425003000b5507045402c11448071728240c86002005130081d0804116a1a6222070601100d01e411840c101600f075010400758070078112001940e40e400e03180d10b0000d035580c860b510180d140c1d40b586144010000114104441c20105c2c105501803038000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 447708120 1250 447706870 447706933
    0x91e05090d14090405150118031e03210b040e0604110d0f0602040603051503010209010804080306120106090b0103051803031b09030615010e030705010c020d050304150314010b0c 78
    0x807520042021100308440c1d07030480f1401448010815a00030304842c425212300903800c940d40782107130349400c0c5000d0100391880c04c40000d82c06020405014034050340e860311980445688852450510401030300c2c14401490043d840c000100c3d000000200b44c2900c60754110b03130081a40011841800f82c1e055519100380d94041208440e0320000b0070750300040c40240740564003c02e140c10b140b482207103800d03a9041c00f10700c0790f031040000c0001640c01106180c0e0143d00510352a440b40c4e00c034030200f04c503164140c56402e480d520741200442e4814455210141c150301c2039900300600d0f03a5070301c41d0164080514113002401ea00510004455860405a80100358034051403103003403000d0640801c3c40c3c10001c0e15058003000c4170307841e50304403541c1c0108081e241040c00c4004015851a2000107400003060503c003a000e01850b0941c4401e100c001c10894005000b100f014034000303074003207100500421400254281d40d07a084400003c0b090800c0d02510f261070003010241110800d0f180003095030320076020001010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 447709370 1250 447708120 447708127
    0xe1303020f06010807030510050f0a0b010509030a0501021c060315020702010c290c040612270b1b040b18030f030a02031b0102160308071701091e05090d14 68
    0x30241c0500001e03008051140040500c40e045103020742c10308204011011155160504018401d9410807005812003010000041d0000009004807264030640e401c07075825101d6002c025003005015402040825507441c5a0aaa05900e0b480e40b1700b42c560f00d10002c2e10007030403003003140740f04441c6600628144c0e205050881100601d40d80c0c0c500066955400d000400001803024000008401d50301641300c00840d0003503250508000000e005020258850f050103039840564151102604804501440103135405001c2d4280b24a44201d00c00c1c003c40300d10500d42080103100c210480c07020142c9080d204543d034020706240e241500030741400101840507502d40b0a250712079104590070300080c6458a401ea002d140c0e1500c13580510500c18103032a81424540c0e10401003000f6a410266010945603850303c2c0c03c83c46510703103810450b20008031031006151420100c00028100380345038440101c145a06580d881c40e40410503000b81100c104075004415500104802c008503841076011211000c0c20792200350a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 447710620 1250 447709370 447709393
    0x4090503030606180a06173303071d060310050c0a0311090a08061f05030703020918010e100606021504021311030a020a020f0d090e33190e130302 64
    0x551714000c0c1e01100125100d200300c0380c40313410503043c030560141d4040d03201c25880110400380341004d1070014a1100b6010403000b42d172441d07a414055580241200001d07101140c40187c8800070959041d55050b1280c40b41e1030382c0500c62a66405075910402e000d01155040c16800780054025009842c6410280e2004025081d030741d5517902c005401810821004250a14000d85054180803100c0300e1704200c640c420300108040c0e5400202001580d9050310030131041c1d1602982e020071403102c00e0700030250354200301c206008040006105855280504000c0c0031140e036400081c0e0300d90704580002905107648100241c05070404c2c84c85c82c5502c44e000c140004131123065140c2d0002c40c1e0001d0381c140032000d80005404142c1a41040702100400a1802905c51010038840c0603183c05551b2041044888031080004d441d07800c100031060400c0108101c0b800c15038003400c0104001425150503511a250030124401c107040c145040300e050364207d008580403500d40c1144900201c448601c118214452039000c000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 447711870 1250 447710620 447710629
    0x30d021c05070f0f0b0105030102122205120304020922141207080c070e07020a030e210102130b0f04061107120b0106140f0301050d02010c02040c020705040b0409050303060618 77
    0x3440f03035004009100300360343c040c82c1c10504201306034041c1c1d10031f03030040c09690180e003100c0c250f4a8015520841c1d110918100d0411591961000742c009045400b802600c0d0440c400b0303000003103104500c225040d810759603451080041c400786041c0c0310f040b4a40c65035107500c005108528000e0300e0440d4a800c440c14540c00b400082c060342d01c4181e0807540075001003000102220104600005030100301c0d061030481c901250300030350b186d12405002d0200041006400440e8840009101065078014802100e03407500d281c195000c0d6010311800000e4205030b800c0028070340ca0040079150900000d0000324030b02444c01c00c0031601e40d071407400409000d0084070000603001400100340807030300348180c2c103160040d0301d020b001600d5111110114a003c200403c01d00050720301d401c0459042d201c003200c20f030fa210702d02ca00042700d00051600c0025002407902d0300b01e0000c203030009102d4007194000c540c203024100c461018401a50901e040003880e40d8800d10100e10b491a2040140002074030000c015101c0c401d2010005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 447713120 1250 447711870 447711893
    0x9020c010b040f0203060906150f03010b0702011101110f07051005040f0b010b031b0a050d050901020d0b0d0803010e06120a03050d05011205150613090c0e06030d021c0507 75
    0x1409030756030180808541058020850300c080a00c0c011401c0d85040310209000450040400d4071540000003030103c3c105c01c900a54407101070f10910541c8035a192001c4d2803407035026110617030214035031145000740f40d10140039a104005110076441d080c6a880c422201e682c0d005044110b40c0341c014420000083c4519114581c07007280600d405d040d8110141c102f00300c92800c180c1101401c40c1c81001040703100344150300400d40c01d000541e00036646800021003210180503040082030714600b0502480201c11054010f406559003054040240b030100c402000030341e501c03055005000d04001d100400c4090b5001c50b4050307109030041d011245013103900010905140c40000c0c11004241c0c0410b031814507140178858036000d0800202810141c0c0140d484840e92900b08013007001c0440040e00008406403216000700144040240c4103201c800802d24040044c1000317400358280444002000136240e160024040541c00d6158024140d21828400e09240202180e88424107100c0108207540020306030383c441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 447714370 1250 447713120 447713137
    0xa0909211101051e090706021b0d02060310080c0a03020d020f0103090507060903120f0215041704030c03021e0d060c0e090901020c07090605031b040612050615040903090b07020a0902 80
    0x1d201078001340300200c2c01502c4025220241590101106000e229000213980381c501203900d00d06d00c1c2044070030700002c0311010300c8c2100a407c60004014041c8c0360800410740b03c00d81d006181035800041000741400111a46480040d51012469004001508100380d41d2081d6000c180760100340c000340b540b40c451030b2861070361101d80003c10100b4100180b01c0000f040c03010840091420b40b107200342d0008001d544c2c0104218000805540c000401c040044c50108180300e1005071a0003a02c417966400c2007807000300240300c141e000ea440d002d03034a5a0b0002c1c101107030451b4180284541d020b043e05444050080107049c2c10740081c048050030198183d5107140d0450301c1500d10301e0000d44d84252040c4040d0900d286584040e00440c2003110034842540d000c6a611984482c0c810441110588200010040c0685611041019a00b41c05940c103215002c66420311460f0044d00d082d01e120140f00902088842c0444042c00081085170140402801a8010410710340010012081c641e01d0b054400101d070f000662 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 447715620 1250 447714370 447714391
    0x70510020d020615060a0305090705213a0e030105040b040204150b19020102040b040306050708010e060a0504020715150f0503122d07030e0a090921110105 68
    0x207074100e60940c10009680c0c03040c04200b94000900440c00481e5641c010382840400b4561580000b504000f020020038000b4a4020a01201032011a001c014a8400e040d0790454074081d003068400c00d6483e6803d81c500345d03c1c81c5161081e610a070fa41c4008205101c4035612420066840301c5141b4640c0c2c00d014141c007030f90007402000c0440c1030510420040300c410000c0890102003c4504011300303c1c550068034a5841d044140048002e4080c00490081c03107140c000f29640c00002c103012080c0304855001e11b10400507a01c800a43c1d980311244460340e16011a4031582c004074408003404241400d030060184140308072000303080c8101030003920b000e84561052041c07180300c1c000420403440e003640a01c03c000700380950180c0340396101034034102424400c803c110800f941c3c7c0d210501c1c82c0c69804480ba11541800801d907652100c0c028640104035801c42022148959035440740031441c07a07142e11590380140e502015a280ba0100e0420815203200c2103e003140c1032040d208210f111100c000c3c0201c6205030f80501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 447716870 1250 447715620 447715633
    0x1308010c120507030b091f050d050105070905060301080d0c06020f03040b0402030d0e0d0f02010c0804080607030f0e06041709060d14070302070201081305030403150903020d0806060a080907051002 86
    0x1c41d81e080300d10050041c0300300340c10301c40719003c0d58440c8000d107a00b11070161080107a01001042d8554402d440782d02840c0c000b25001c1d80d1905121044d0301080c0614100d03a1100d02c0c0366914010408540004e000700c601503000600c10b90101d0740948400300205104000c05810f0150400001241d03400c00c4400307644402c150010081140b40c01e014200c54505541001d0041c0d658010210304644020b000040c1000d02c980c103c5000c1da8040e000850103c0e902c1100785583c1c42c0c4a1882c5505c4550a940747d1021030b00b4004182c50044160140c00362449004000300b50300e558a48651044400a4000c8200c1c54810082051291584001088206d84408021a402c440002117548008009100c0c000305841408108010b03a405412260004030300c12040562020a040c901e00314880d550004148140c88864800b052050b6007050790307854000e03000da0300e88240c01c42c0c040c0c607640800c54500d54007501c10069510024002d0081680104014040720402a04d038800706d0941110098450050307480310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 447718120 1250 447716870 447716897
    0xe1918030f090b090d05032206020d02031c20160215160803070219030f0f030905060c0a050c03040f031b050f0405090c100e0102070603050108070b1308010c 69
    0xc0d05088551141c0d01d0078080007807401c0c1c4005090302074444d50510542200c50f2050a10004101b5642090311811418040c030f0300f0000e80900e00d4415124280160054200c4403182d03500100640c0d4aa10101c29409120b000c121580401804105201002c01e100499280036502c075010280241c9114502c16400385d0805d401085510000d000e0030100c0c0c83c00c10440c1031046910b04c2000c10806501c8070209440385c44400040c1d0400103a40b90a21854a2414402040c180d1024604240c64410385a80c1d14218881000324152000311030058034a038024800b20f0800403a00c401020700d82ca0750b2800d24104201c40a0450860740550302c003c0d201c0701040000d01c148040203801888002011400503085443c260220701c4003001e00c1c514922039544e48002030103d04040c44110440c0030020b00c0c1159225402d2800740c001d40c0f9001500380140304007074000c64414003a1003014140c506080003012403628040d40d01405030710500744a00c28107002c8400040b040000d000302202c0d40350300d886079480f0303000c107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 447719370 1250 447718120 447718127
    0x22060801060509040c051507060f06090609050f010614070b0108160605070c03020402070f05030319180f080904060b0c0102070201030b0a030b06091b0c01090219030c0e191803 77
    0x32508420320606681c0240800580b078420140f08035202500e9141c1c94110f142c80c52001400303541c234080d045909150a0180503400c542c0f001c000e8440b406000c000710758071074032108100c52040343c010000030004c100500400d401071404010390f2092100c0e45140180c0c0e5900d981449070280d114079100c3d8408401044440d4076448607102915291501c0c40c10042151110100003c59203c0030740196400a03440040c842c09020703031010b031a00202100d03034038107103070745030f40110181c80d07280907100d504d8842040c132101211403047d101c654100200116400e015205c0311400e41c07022008551090b40d0b103500064500f98800a40043c0750a01d00050b111009400007400b0f40e080c0c1000c0500ca51403088050002800300c3d42c0250704000d040d188804a035890400d401c1c050710045c2c0110504c0c61000c202d100703044205400035000a071007a02c1203488440078040c56200070426000041c040312100d4420f00a0710010140740f41e0000e088c03040001c0c0e513001c0251500072180c1c40000a08030502645201c42415003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 447720620 1250 447719370 447719381
    0xc0d030b0a33230d0b01052b020c0604050f070801060b0d05040c090501080c0f0402120c1c05040f03110705060d090809041d060a0912030b22060801 65
    0x600c80168407402d14001c030b1807403a4500c420301c4420b500360010071401502c0d10840400c02c2e5800c1079010105a081c2800e040e2080e6080021241070190500c1c0e440040f070752048042c1c89a000c098000c00d000800003441c1d01403144501c0180a04056090128034a000000c00034103004d580910060540301c00d1090742542800510340060000c0ea05208040080c09006406c131295290002d00000d0035480c1da140c110310101c0d0a5100788030241c100000484c1000d0b0215411241001c1151504210b851400130301069010380d405900480818038001510600e02d4401803211021841070340340c202031481c021404403582600c2c15a03090159040b020f01b0540c12012008031003e00d84000c0101e03a01e4040024550721842c41440c200c1600c2d40403060400c40040145d83d1883d000600a110400c0f4210a502450710b418840d54402d100701e4010465419a51254540d101d410800340300c08803290740750581c0074004040c0826000b4040c80c00e00750b02029901e90f104060003c803100490b1103850400e02500307459 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 447721870 1250 447720620 447720629
    0xf060c09120b010e0c09030d0206060a06020111030a0203040f060e0127110105221e05010504030c0905060d050a050105150a1212090e040c1d0f1b0c0d030b0a 69
    0xe54124010116a840980904582c5640d01c020400d80d58020032176201d01414a045800d4402d5041a0340e9854010401c0f80c03003400280c0c7c2c0948501c0c2d444104a082c2d40400c82c1c030075041d1000b000499002081c5400555215000e07409820b144440b03030b510082241d08125106250382d41d03c40901010000c001c00c21455181540c00780700d48816035403512480901d51804c51410f00c200090f40648200e1100781e1200d1610f810000e00c0102540d540a441501094003000360300c2d02c3c209a400b094640c0510300380d400b03a0742c204500b1080281042c43e5034000b4640600300c158040c94245503200046c00c1000b0304542c05128100118880c00d00b002120f203c501c1c04980c07036200e003100c0d180c28452084c1d440140015075800280296070035494010585e6528000d030071800c07800491404100038000d1a40d2013100b10741d6204100382c0101d010007c1d45d1010300c4141e480001c0242d64101184a0340000078080300e1800d1200c0141e0301c0c149400326118a40410001000042a128080101c003483c108094a0092 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 447723120 1250 447721870 447721889
    0x150d0f0908040f1e051003091112160504020f030a0902061b03120105040b03190206070b1609061d01050a020f012c030405030309190e10030b0907081c05070f060c09 72
    0x182c181000111006d8601181c071040603a1a15113800303010550381c040b1840781021700300640b1035000100c2c0030b07180c1124180e04d10304100c5c000e07000034048c03d052003141c003d0288140b605003507403140d6881001070000140706030f1b0722410030b02110703d08080c100c4051140c008140000c40d540c04141b5425001100141e01040c803c42c036141a00449840120300085a8502e0900b14812400d540c400030300a070180f040060660082c1c0f208101d01070004920064a80b0869103d4508041c1d03116000c40e80d903070980900525241601002500c294041c2e005049042c845006565060640300000c40c00c55181002c4103142c0480d081c141d00310055120300010300071682801841c6020b08050100e41e903880b030002080c7c090380b0740c2c031036a810390014004208040c05880d16101d4807401c024501d40f40c152400e00043e0741c81e800d51408140c03e82c0f0b0001e0030404640180001e4200800120002d078114001c1d0005201070040400840c03000900301c08511504912aa80c00160302c5440070700201842ea0740d8000600380d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 447724370 1250 447723120 447723179
    0x1020d020333040908120408041703090a05060a11060901020901030e0106082d010e0615040903270b0403050f0c01091a1303080d0b01030506150d0f0908040f 69
    0xa481414030030741c0c0342c1e01d41502d02082c40007107490210b43c0d900c2191200704485406806000421140000400c11101030000e0301c02c8907ca04460070340c51744121611103501a61540d42044039091900242c04050764604000318451006a48142000740807507008000d65400150705080c0e603014400d42c8940340440000700120303424a1a00b607640c0c030340c640c00c83c40c40408038601450280d1440d0982042244008000c2c4120301903520165aa0344054849030302e0281e00c0340320078002d401e00e0f20490540580582e24002c5040d0402240310b00d11807a002c20392048440248040b0740658000300802c000c61140d002003104d80140b00c00c441c2450b41051401b810012540400c103c64209140e000d41940c54468406541d069030005045818099a000400000001c100700c08035010b82c2d80000c20040c400e80b8140040c0da00c0e0001c000c2050051011216051014002c0018844003036100707921020013035000103600500c58a4850741604264048074140907100011f0043d09051074454050000c1c2e144080d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 447725620 1250 447724370 447724441
    0x2406050c0c0603060f22060911160201021006080a060507020f1c1b0b0604050603030301080d0c06060b03040b0115020d090603020310240e100f14090301020d0203 71
    0x215004101d101c18450031001c00440c009644041100b001d9080007842c12115a5600da20640107154051030014680c2c03170400b0029020102d07014209901c0000001103141c00c02d80000c40e4009203e841c0103138110b100d14404920044154800d03440602007040062040340400d00e007c0041e40e00c010703c2e00d008c640059003050144040011801c0d8402e142138400c0324580c201d40700864213041d50a4070741d0107030f00801104906102c1e0501d8040d01075a401e07a02808241d440c9801d05640c1d00c004c1c4101011b42e070262106507017043c413a58159050500c65240419950358402500116400582c1d00b80c42c0c0a0304800100315442c1c1c5a0345400444000f4000f0700540c03c08030b60041c191000901c203c0040c150000005854640c007025481e02401c224a41d90043c1424505508001003808003c100400c40007094000985846c43c2d9000e140346240c0d464510444c417480e0111107544240ca0081c1c0090700510a0114942c1c0a002506070441610401a101c1c608078000d1403c141054035400e1600d0000014000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 447726870 1250 447725620 447725623
    0x90c0909092b0309151a031b010c05100c030507181410020c0d060f061a1b1e060f0606030402010906050f040801060b030a0605220504152406050c 64
    0xa60b503200c811840030155200c0c040540180c61103a030000c00080449040704034082e915441800074001c69125000e8400c40c10050595540922101025809054a00c55041c0d0310900c40518940e00c0348041e00c0c07040f0703c10390003001503811030850314010035142e200308014207500490401c02c8039201845c0c982054a4024504140a26450040d0148a0045005506a00030411450280000303030074803042d10f070b042c10424014681c0205240016080500005000f02c098455030001c070350b24a207441c0703802c0c08d21459100c3d0300c03c245011401e0b405072040d0303001d50300410054003030340c1c094044c00340c10b551a0505003100d510300000d0105104680610910001d030b41c3c811050420356403d030402d103a40340d8200c10045180d005642c001c0c1110760074031801040c02c140f08006580600200304050040320389032020000c1c40034060301c044404080c942010b00b0510313003941007180c000b40560340e903101c021403404c0c2c4402525100000c00200010030342c994880e1280a190020007000301e4685030342041e04100020307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 447728120 1250 447726870 447726913
    0x30f0c0e0f0f0a0b012604060507050a080613060f06030e10050708041104060b040b1201060503010518041b030503190305070f080c0c0d0f090b04030807080a0e090c090909 75
    0x10035a40e00c4d00e19129900030240310f010020075420b88210f82103000c0c60001c90301402c8608035035140c2420046101140907000b0307140b01040729101c10b4a1a0381d0b80003406811902070303191a105903200c400010b01082d580751480c015120359036004c00c507020040202490300b07210400c104800c925100030010b8050344035014030382141d03106404103899081c1c90000703006400180c00070500242c00090004400c081d07503005000c103c160b0940441c1c16a41c1381c0341622240404d20030346400c480003500312031481781038020f040c3e8414852482d140507907008412402103004130350012070307a0b035200081a10a914601c00181640903080c0740c01c1c00380d4602310100404464050380c8110a018100011444422a403800e071400d040003042198500380c0c3d01c00740180700e9040301075540c0100301443c0020407103a020604481c2074170703008112036141c80e40c250786140d20b82d40034aa00740c0420210400b44002c5581e00d0181e24080d4911189042d190f6207464100000114050310750303100ea03030001484450010308103004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 447729370 1250 447728120 447728131
    0x60304030f182403051e010b031f03080414100909090602190c0c080d0f08070c020a081015030b04062a03050414030c120f04030f0c0e0f0f 61
    0xc006528071021101a058119044400f041e80d00714100d1401002d900d803400100f001c6a44c0600064640389410b40050314400004a40081c20034014131516005500554202c5100111030000c007003a203107a0025aa00394000311013100c40040d00300b140d046500000e54003041c00b02c0350404c0440d8400006059000b0b00d10841034026202c5d030038881401102d41c1038851000403004000848004c3c074a000380f0030054840221400c450408021031700182c001551440d424943c0c0b541c0c40014036050003980c0666000300401c040080e90407402d8016101c848180000300404402080c0c550310000c8204152050580a94015040040208041045c550900ba009030700418005444040100c8004082c0c8241c036490201c10055000c14900300c0d85503008030b22660103000c4403400c607403210720281c5c5c40303101d5a2000f18685d48a4000d0007100c1c00450b0040840e400017000e06490180c0d680d9400044031102d01c01996152040c2008000b4000e0503003d840d800390030182a000580f60100034002c240390003030007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 447730620 1250 447729370 447729377
    0x1802010f0207050402210c0703020a0807022b0c06031a09090106030f050705030d0e0607061113030305040e090328030204050d240b030d180b030f0a0b060304030f 71
    0x1090300e80c40c028800344000d014050000e560710f0010654684d50f00300c80140300c00524485100189411401001b611841949680a0131080a43c0d869010b1903802480050342e10016816012082001c0d00c0950003e1540280c040740020150341032048c00e01c2c81e507034484001c0c50f003003001c1e0107030750b40c400c41c1e0340c0d0817040c02151140d045403603503c034641c018411034200416070f507a803488000c10301c8400035196045039021800c5034200d0800d201c08460545642d41610340000b0306000304000a44c50750041003411001e0f00c103060901100311a400300c29140340c1d01c282c01098000070700f0705c03150111045542d8000000c0c130003035180031030036070301710044400000c2030014014540803540081446a01109c0090100078007800300710007079081580c1d450030042c0141908034900ca03a14443c1200301d025810709254000d02915030302100c00010b541035882d100580d41040714800022801894640107580140c1a01c1c100203690b242032080e0340c04076140c8612152140205008010004c0d07401345140441084518 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 447731870 1250 447730620 447730637
    0x1d0706080a14091605010201090f02040902030a0501020a0c11061201031b15031b0801080303190f06080d08010f0b190302070c0821030c04060c050a06050f0604050109180201 76
    0x61050380101003a050015001c2d4000c1d00780b00c0c02c240006400c51180c9516820b9910300d9079580016406c0b9002d6010080100c142c00b00d242c0301615040d41b000164034009019a03012550320b581d4142240d110300100004544e40c6134401c814441c102481005c0c00000760f030401e2410a1340103413021010414400280010701c8001e28405680c1280c4100d002800c8d140382c0c2e00092290980058054a030041e000b1744c01350110380003100c44038812842c05040350100c3c3d018506d0364070b40b0880002c85241e280e00400f81d050700d405082c1400105486807000412520010b0803026400010007815000c060348030103940d05100c24240111030441040341c5038212941400840b0440b894000d0b0042e0080c82405008420712500000310028007044103250545400740103110868840022050760005899415a01606010510259000d00384107007403280200b048503601016507540da07003a2081100c240001c0c040b40400d000b400c0c2000d01840b40540b400280900c00d004500c003a08180c2a4102c502904201180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 447733120 1250 447731870 447731881
    0x3030705030909040c030f080301061b2003010b1509040506010c0c150e090702060f09120405060d0e030d09051203040327090e010603150c090303050d0605090f0403031d070608 77
    0x485e2440081d0745c0001407807049155428110030f6a0004d201d07800119221490206042810141030404913034011000b1403207002c410107c5814080d050300c1c0030b030990740c0c50503825803954681c0300c0e400315203a080d041d180e501d0040c00c0905c01038440c0038040506201071200900d0015400c41044400e43d09190007070031000351110303406c070703400700806070074075080f21501051001941e8040760307251040110000705051902c514250641d9022681d000300f02861303081c001801301d07181c0310004091205261802081c2c81040310801405d55000c650392030010f81d42d811902d0108013040c0030700c0a1410454211604514003603e000d011000e060f50310045803100005c0c1035500101035482400604080b910030050705280f807a101b8000c049a020654103003c4204080000b4842801018040d05070369468601c11440d5940989064002514100c04039031a002c0c0071074140c8400d20024447c450038080e003d001e08107810060121a021587c03000c089408a002640441000516204680c450b280040341d0796540b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 447734370 1250 447733120 447733133
    0x3230d060b36040e150f1b030a0207240c17070c02190f030c050a03121b0501050f01090f050f060112061203090e07050a08070e0418200303070503090904 67
    0x1104075055000345460741d1005440c1d800505114614080072170340d58151508203290622410488072480c0d00c213080050401c18900c4140030796000040800c02504125030359031280c84580c18001110b02c0d0b03012681e200c1c60601450301440007980320381d00b410340f8403d1080c0713038101c3e00c842d00401e203c041c0b0002c070b4001411504c4040781c000700e01c141c0c0c03060f06e0340043c0c5601d031500400105103c1640c1c100204100070440345850b10072001200ea11441d441c8010f00603d40035241000005081e2000c1c14042d012640030480030300916124410b081b06c0b188c400c0d03041540c001d080302c00080350240399a1070001080303040e0407802000c44e00f1030403d0030051103c5121200d200003a002035048404038811a0a0910816802003000400d482407400041c3d415035a401c0b007220140160100a80003880030030105d0607890042105500300c0102030000b00d03c1202160342c400c50340c00c030a10121000c00c260300281000c842d0142c509610404110040d500e4007030940c85071a0b681c02000c3d00341d4071941184001c1010401c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 447735620 1250 447734370 447734467
    0x903030717031501031a210307050102090901080d0e0411070c09020d0b06160f080705030a08010f12020906061803060717060906060d050403230d060b 66
    0x1071004150146001c414040c440d99041034854914803160280011601c1d80a4041d00c04d40700850110003000c00400c00400050100b491040212400d070a41601d552a100b0300050010a01031400580d40e03c0e41d0505001d94400164005103050308159082c14420381d1050000811900071200800d40b803840d5007452030103200320340d070042c6400e08140d800600403003039401420700000d010904100d60580541482114440e14032903d00085c00c480501d40068410b03441841e20074061075080d410480380e82c1d1441c0c07855020030314203000300d59500c004000c08007c8550300000b07004681d04050310145c559009c40c500d0a0040c0500344600400700c0c040e0103001e03100f10100341c01c0000504490032802c1500c07000d040d5940e902d001100182c07120f03000030b100382130000d01d05018a40140c0b02c10320740b46500d91311500500010384114108208400301d00080d6207107800d08942420740342c88142d520541c600215040707560321340c0000201035091044402d007800c0c2c0c9000d01c44500c03603110360900342d020400311000d0201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 447736870 1250 447735620 447735623
    0x150a170903090a09050609150607030c050c060301030b040b01080304061b02060c0106030c0905090604030801090f140705040602010f110306120705030304120203010509010908161a13051005071409030307 89
    0x2c0050701c0011382c500458004500031031082d1a040c0c15501c50004207001c9404602030b403034000b0404c102e1000003c4c42181c0c0c0407501801a82501c1441c0a91000660907070f01c207034402e070740050305441880f0902818003501030040440d00c000314942403424201070705c4480d541800307012189060511300159241c0000b214041c030a4103008001c4035449151290a000180c00342c2803c051034400000c0d4503c0340010003a0240d070701a152000143e10740100e0f41c018080721100d1126503601c2e911013120151809105c103001d0f180c5a182c080d111828440020308507009030443c01c1a440c24258110601c1252404407504600c1c1540d400714802010703480c942c6000444e074025074240c840028001502e0081001d201c00d110320841c02440140c5801012500b03980c02404040e180c0b18081010504555203403a0203070009128100701c0d502080b40307000e04085800119036040301d041c00070491208022041c4480340044a07040020070003410000801400d0035142d8001c04001d0740001081c403030341e075010001d488106 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 447738120 1250 447736870 447736879
    0x1090302030a2a0308161505040b01410d0503030c04030c060e1e04231f0602210d020304030c02010206070201090812070c05100209150a17090309 64
    0x1c0045161007030340309a802d5000e1500b07105594401c0280030004440d10f0860340c05c501e1650400510706004845800301603011500c003030030300c8036901100e8003a01426104038028a400d195640c5021100c0e1507108444103c0150360b141a03500c002c1d0310f444035100b054507480160700400c032a0702400210fa80221844400341c040d21000c001c114152412100a100f0740784101d00600b22160385020948a100c010703e24aa404000c182d035101900b5007231003108170f011b8801400810310503061030058004c80f4076812890000641541003200403030090f40b01001c842c0d80c0840f05c1002d1440c169009489030a000000301700207500c00b0300f204100c0420010395403021541d500442d564103003032402038030354000703040300300e0145c0030301e9001540307003070061180740e404030b4103c2425440e020020801c80f00f0040d0080644051040460300a40494020001100c01403000b03140140d55180c5101040040d15181107039403207201042041e0642c09a002e50380b0860244010302c2c580300c907240c0310505802c0d17000351409540c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 447739370 1250 447738120 447738133
    0x3020f2502130e0c06030115031e0f06090e030901090902030a02190c051e0705040b0d0b010b0304060506040902100e010309021003061d01150f0e13021b06040309050f0109030203 78
    0xb0003080364011074140443c00b0031262074044803000e000da40d02007446000000c000e469111090540283c101c040031100303080e600000c1800c1101d080c0200d1b03854808048003140c0c2c0d0ba80a000540540c0b14407820a0f0241d0015410301210500080005140340206a18950080086584994990161404040f48200c2c1d19402111898002c2c0010080c500650f503611a500e140c000102e0300c040342900c40210784000c0e004990800c810701c4003402583c01d0f03040d0003240b2000484007044540f040d0501800a03682c01c01d42e20308040c04e2980a641014188505c0b071880c0c04240801a59181c01291000d074072810071191030031100d0016401810107000c047e400503070300501021203640c1a0700007415645c0e0700c0d01110742d08003555100c4007400c0b02401010700b00c54424000502c4c542c01900d8641c0c010119181540300f261a03071000c60417060031034465400081e008280c040a0204a0041d5030816141d400100a80d14050300d0042c0550003a1207102c2c015107200704074444692013500d2520140d034001d0100c805 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 447740620 1250 447739370 447739399
    0x6011e0e130303050a0b09180f0d080601020708010506010804150e010c0305060111120706200d2909010905090307020409050c09090d170703061806080d03020f2502 72
    0xc0d0048000c07011400a4030340300001e003900742c4034464001107134005030160301185d48001010950480e012604240c40c481c00a1000c110340341000942e0116455035550311403420001c001901e460500d0304101801d0741402c04000c42070740d1203403101e0b07409504a604600c0c0c0d101100c03514002001c1018100301c085d400c0c2044001e4690701500040c0c0079142c01c0c1d8400b1381c0b95030030f940000d456055000728000c1c850310030800ea5021541c2c50b041511030040ca0500300b412583c41c003003050340652055101501c000c1d1550041c04240400c0103811000982c140c043c039402003c1100042c000500500901c5030446d514808903003141800c006403035003507070302900070403201c041420400d0703840c40080d141e5881141108001100c1c04c0d408942e1078060a07480e11048818100044404141d8600521980405a9501c1f0021702c950103410035403040c4521500006003181402d1846080440155510341070600410090100071500400ca4488100e440c0510400010b9031799081c02c4c05400d0b04001e0340c02043e80f1949607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 447741870 1250 447740620 447740641
    0x20f03250f030203071806051002160608090c13230a06050a08120706090b04080d110c0304050f0d0804080d0305010608071b020a151d0a0806011e0e 65
    0x294880101290040090756030145108104850100940540020500304130203030100c00c0819041da056080440c0c1c2e16190b501281449032460303c03d400503400401d0641c802e00d18404550090122450600320038607007201802d550f00c20755600607014840241001007030000c1e55020344012141114038010703007000e40640101e100015901482c41030f00c0e02d0700010b0300e464401c9030603049528803006815652207000300c24000d6004640f080ea025a140e41940000542c030f04642072003181f080610710b0b1100607482c13010b400c4442400d800070088104005404c000c040000c10b44044070822600c0b00c3c00c920301c440c08114035452111006001c0e40011a021a0866004c105000040340c582d902f000180e83e0f942c41142d15040603940140402c03556075a2405075544211010012400500170700840742c5d455004202110303103140294002200c0521007881204401011803070400215050139249051000098541c04103101d407004030708400760028005940c8409180007030000da00001080e1405a1100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 447743120 1250 447741870 447741913
    0x4031e020a11091509040f05070306051501020a17460212093c030c011412060109030507030501060911130e0c0d0501080706020d0f050901050304020f03 67
    0x102c0e030480d03640e100e00c0000d003040c00d00396214500c0c034418402d110000c00c0074064141c0001c1e00584240103a10502404110208030707140007103200f20800105403409020080700d011070310540300c0c1150004450080030403100548100c000078002e81079581c551802c55507039040d44201c0905001d8100c40c518940180c100c00c5940110190707035103164045550107030022601e80719244541460080103011400d260304120b8011102e5800c03004a81c0c1d01c0002d8189101d040c404001e0011100c0c400c0c40c014000d1340e060030300c410a8091300c00c0c240a521030001c040240c100c0d0251710031210300720100400080b6180e1143d10904e000b15040385c20385034044c2d22420000e012381031030700640c0c041c503040210322400094001c08543e012024a00315202050409042609144c0090504000038100340070009010700b00b44112802020010f00a0034601d2901c40080d041c00c0d800070500c1c05004491016041964014044846000003441d16070f660f5951031002403200710040d4440751b007520481000c16100f1140000e032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 447744370 1250 447743120 447743123
    0x3030c0306080613121e030c1101090f1401020405031c090308030f09010606050a05090f01020c041e0c0206060a091e02031f0f080c0d080706050403020714030307021804031e020a 78
    0x240e04185d030420020307903400310400f0b581d021030080d2503452500350344245e0102143d0070035440c101a207148110001030a40b000090f042c3c49a080d118040b0003040040c5c07035000b003880e19080081d81010310386000681c13602107a091200e000b14811403079100b810b201b00301c4803020b183d02c0450183c0303900b030414180000b007908842c1c4414540c41c0020105469004d00107603082c00c00c0996902303261400c50000e128400034519105415481124141c50b0607a49a0055501c0c8144004400d141151305418400a88540905a03800d54006000f40f01c03450b20303094620404e9400b01c100c041a03029100c0090500b07903e510200c051454404000d0110381c130180c08079a80340301c180e01e440301072080d1906520744107a0010704c1440b4051380300d4012000c80b030400d003000038602da0084100504002e080d0700c4d0541511000c484c11001a04080b40520104100810141b040b413070550055003019100d40c00b08508103200b0402c07540e40f4000400203004c0520820041030140a1098298020f40740350318080e40c0c2c0c10540a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 447745620 1250 447744370 447744383
    0x30d140702070f050a180b03030a03140a0c05040e100e0c0a0216080618030702100806090f040506130516090b01110327010507050d090e0c03070c03030c0306080613 72
    0x1c000414142103079050051303840090100088a00d8820010703014034030615801105a11806040020f81e0140003403c03440a25460202d078858100140c07056100000300100507141c134241201c0b0140303900406079409d031804d040007501c99450b412650300c03180c3e0256000709504140e107410442640c0d07050f000b07002d8400310381c2c00b203d51980d00c10a00000071803207030081100070380c018000204020040480300c039030060340c1410740c0d183c4103107030700840c000121041d086408280c3c08400c3c0482410281419648000c507180c0c203180a0601c2e540d59038071500083e01540820244031010024040280400302c003a000b202c1d2a103034000c1d0b071000110301401d0780983c46804205080a00c0781200301c041700301c0c0e40c00c202d8907a50028071000b00a40910400600c56290304110050000e1310001d081001480f003801200e840780c143d1240751050020001e0401000381c012500140140400c0c0398000041c40c8040e680360801080c0c07231020050413001008268000f505900c146070070703c014041001c00b0407202034017a00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 447746870 1250 447745620 447745633
    0x31205060904021806241b0a030e0402092107060f02010c051b0c12010e06180d0e04021908040b0a0b0a03030e03010603060203090625050f0c030d140702 67
    0x400c02180d030754100c0d406034000d021030700880544050020b00c035038056401403844140032112461030000c0289181c010380078040014485c001640094105030961601000a0000c0e0806580041c02c02d4056080d582c00b43d1740110b405c000c0c0d540e91035140300c0c9401c0c4190900380e40d201007140c003607a140e51522403480810391061035580c0e82e500c1801042121a0f164541038038000014031280b41c1404000300184844c0500506401c40e50380d4000c0c03c05820042400103c0c0804183c00a513081c490098000040440040f8003111f05610103c2c88445903102411300001c448202404500030348180b01541c400b1003642409070b05005c1c1c004600500540c0030303040400d47e42e60740720020000c480000c08190340c00780003810104002481030031114403075580507001058003640da584140c1aa0015251543d00b074111608010320440c41005200d4102e1000180002402000c90041c0403031042480c43d418428001031a405100c0b000c104035214107441e00c0c007c02809080e0030014250503010b4501340c00501910 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 447748120 1250 447746870 447746881
    0x913020a0f05091c0203070306020f04090c0e0907030c020c2701141c0501020c03040311030c010206040308070e0d0b010b0a080a051603270524010e0103030c030c0f031205 75
    0x2e906891043c44080c00c122000c0d0045101c05958098034102207901d441020008000580280058041030240342c502503203a80c1000300d0070098860492058040200e02d4240070019130710008640e4210711a42000a0300d521025000c038100b4664550031a00f00c0c4100000010940e0b40d000c04403580d90511041403010b90300c0301c00e1030750700f049200b0880f5840f0680c0a0803038031082102030b851580600c114001480c100070210040d0454100b54001c0e0b070b400c900d902c2c00c04214101442580d80068091024002c94078041d6000b9145c0d0a000c0d1084080040c0c003808018070391610b1032100441c40e00004400055a92800b1208041d1f204c1521100040c0300383e800300d0618111402000c0c000c3c116080c056141c1d14601200b20000e100d000888064900c0c010b02c42d14094943d44940d50f270203800b9001800d20300e03d2000c48480c44415030075170041d9000120f00104401c15040d041c460540743d142c50300041c1800141400c40d00d0740316a01000d401c100c141c0c807803c0c0030103401a11414848030304400501c140c6e5611b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447749370 1250 447748120 447748127
    0x9080c06031005102c0a0608060307150c06020712090b0a0e0402030c1c09061b08010b030702030705030f04030204060f03050606040b060408010906050a1a030d03020a050913020a0f 79
    0x42d2006800041d1040381031109282480c0303040b050760708620304003040e10021007960b4281e4100100101c4015a444610318080c24500c0f841c40140c0b105013041c09085c10480c020aa588105120365003c03060000040e503e441d2203604000d40307190304044159110304250418084260420401001084c121080003030075001102c00e075078072203640384c4400350300640c1042800040c4d88010300c40782965104201c100100019203004040350090042c000442c541a0715041d4121503400c010101414411104403044580c8000c5090640e900b454426480e6107440c00d00381c0c03860084540091032400f012039925011310096001d442143e0088605002c99580d8440d0600344010a000150403030f001100020520b087c203404c01e010281001e41490314042e076404a05007180c035128021540d154864090001c40395190040c180b220001a407400c03521054a4000f0b40e603010249030b142c0a05801103204400c541c000c1007a01d902cac04001c1d03c03011074051104005802580004072170300102d0902200194294407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 447750620 1250 447749370 447749377
    0xb090105030604060c210c080105060f07030e0d050a1406011e09050603070503010c022121040501200307031d030d020d020d090b0103051c02030a0e0d1209080c06 71
    0x101902078042d9881e5515090007501d20201e014040c401d02820310b80260300210300c000e0095528410003e10010540c0c401000520b060344150b10075402440301e400c8101009045454041d0f00d402c1841301e42450801140380d040c6d0400025005004001910007440a00204011407540324426640e040c0e03242c6416040c04c40c2c00c2411503148540d6010705110008595001c180c002100a003140d030038558640019094424041086006130016035400384000e94036103c0b00701c4040340c051040e043c48822040c1d10f02080c0c05d24018410045108085400c4c06400c0d4424a8004a0b48100701c013032811400e02085a548259640030000340340a00b040e00c00c030580403012682e0302c5020061031400c10429141406074103c0b12110203103e600b04103620310040580308503080b035031040400d95119032450910741d00300240d81e558544c4442c6131080314002c0c80d902204441801c02c0c2403c00c4080014081c0110380500d564010042a01d5151040e0403c4141c0041000c01210414412100310887c0923061119600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 447751870 1250 447750620 447750629
    0x3150103080a2c0d080d0516020c1c021009031403120a09020a03020105031b18101701230d05060604050601110303040204201303020a06050f09091816090b0901 70
    0x1440f40c0c400315140ca84807949805018901690034075104042c000c0894005031900204101940070344008950180311125128404641c6541159540644002c101c440d00200070311641200988040c1c0a000741d0f10b0402a5401030515004c021039200056aaa40100006000c070640c010020740d8000b010302400000c290b002e803000302448e19550065405805c081d04500d40001e202c1441c1c7c03020729005000d048044510229406819106000e000307020109007851420000f8221541c08000003580340c1d90304544401440d20b00d04c01d0000c000030740c4001000c0016511029440100e002c1c008001926401440211810041915103500640c1c6c4100452803c401c140c1081c4000380252425501c42d41081100240035010161442000030b0987c0c80540012000515040c050085d03040812004000e42481d0800504c4c1070059031a500305405025221441007010310006550142001002d8080842d284112032030a00c40b030070b02c140c1045280c0101d90b80c0c00c1c5407582e07558542c03030134210550489 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 447753120 1250 447751870 447751937
    0x601140a0321171909020111010c09051801230307030209010b031b03011d060d0605040f0510020405060d0b040b03010c0507050118020f130e030a050301030b070206190b03150103080a 80
    0x207030350110321070300170708411001a810301c850b103404a04d1042c820301417003000c1d0a0a82d22000c4003810001009000e4503102c0b6580c02040028006018500300d107418006c81c20241c4819a122106242c006440d00e622074000075001000400005443c20500c400307140500030650f100b401801c00c1560a1381c042c0024484c000c02410342c50b01c21000311a240d0901a000136000d8055640540e05403108408e8860035541218406007002e00101807050a025407507000034180303400c5d89407074504800140240180c2d040c0707017a1a070b9038004880c85503035a40d20440481d44068000d2046101c2c9a00c05040d83c0c0201c1016200c5e9400e084140c604803102044840302541d006141490890404003480749a006802e0340035100780d611002d44440500800142c0001812030b43d82568944c1540340c0f001381d07210050503510035948040240004a91200d5444041030140480013403610500000039150001384111000c0810100b0004011712100e54018a84002135458038442c410b00d400341031108590189000c0081c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 447754370 1250 447753120 447753151
    0xc170c1e0607020103021902030403050d090f0302150c0708060921040b03040c030c0e0a06170d050c07050d0f17120f060a0312020d021e0601140a032117 67
    0xa24268020b04038460062500500307040e00841d1750040d00001c40a4400540e001007010002c20004115800d07906042c0c0c601f0707600345c0c0d2521492240d11621804000d10401d054030000c0f881d1080c00080e0b0700e442040e0811a4281a95010001c3e202c42c0e055496518500a0724409101c400e484030740c1c0401e151244545a10f032500d46441442541c10241c812282403d84600000100c1c2c089c00480001c1c0c524000b0a40035814007204940450b40b459000e011062000c09032200c10107004076240b19129450b00744580d66046a0740316a0605005030011940180c0e01d50414003403002c0c01805241c0c2c50301c1011401c0941e03644100440650140004a40d4070f140802e0010f1000f40d070420145030411400740c44860703240d03102c0c0da808902407142d014007401603100125401245904000840350042a0328400044a0300441c895403110814010420b0a0000c0f40721030429846a46000d0000e54000304000355141c480015101e002c0050071001000030004c513081d601302920b4801d00ea0103080725400b003065 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 447755620 1250 447754370 447754429
    0x2a0f0906080c0a030b130618050105030c04090809030d120f02090d030f120504080d0606110c281502060702010209060d0903020a15060602060a0e0303040b04050a0c170c 74
    0x26154803c501d100101500c03200100029100c401049081c190f042c0c0000c034503603082c1002403203d110700d0390311915200c0c1000010002e940f000f01e40303032a45480c191000300d03000400381005d45140c0714001410750984155042261041d40c410315501c030447d80382c1c0c1d041c40b880a145d200c220582c09200141540300607590900d03000207004249515424040382010030a080082045800700d800468081c1e03140800003841821040103441200c000c0c140c01d00f80340e10f8140c8180d8605070344038480c501860040b40703403000c501d02c8981114004204031801c0d9840184181e240c10080200c0701003565500050700c18038020841050060085e9841e0500251601d42404584c07500304000c0c00b0604030036429070094840c08808911103841d2810250b050002c041405490003030300038a07241c0010080f00c4058904610101e404002008594020307030032541040164959050860501d02018802032110440b107c00041d1008604044650356012800381e802c103800e42c1c1d05001c1036070b003951010725600c0c022656007003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 447756870 1250 447755620 447755641
    0x15020721030e060a110709020a0e10020607030e031e070c0f0303080a1131080c0a270c03050a0e031c0c05091305091608030301090f2a0f090608 63
    0x40142092820807400c0b0002d170092030400401d03801009072140c0010700a03411503007051801c96070b024240ca05019403d0800c00003511040080c000104140d1100440d025580081096406888840c420502d1b000071f41501075645501c24402140c0502000c41c0005540100d080000116601a101d0030010f98688100d40c000700160703008484080303414015076a906010000e2100d01d40c01e0242c2e9a803901403414034110300151254401500b50b030010091802c3c50704c800c0c41038000c5070086501d00700c5644c0300185112015900385141520306103001e60441e5495415000107008507040d400c200300303a44483c4007182d103d215034809818030340c44481c0d100807031130b042d540030861480052504505040100c2c001078807000d841e13959a2281c0f03440c0c4050000c0e440043c494892011a5003458000203480c0c03880b01900ca0005124000c0101d075a040e0501c600005600b01422804600513000301c9591300714050403281c90100f400000041c00d141041c51854020b030700c01426600c060320380c00c01c150303942050f50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 447758120 1250 447756870 447756877
    0xf0e160507080f04120b0613020a05040b070602042117090f0d140a0302030c01060803160b040213020d140105060a05040905060a150207080d02030f09090a0615020721030e06 76
    0x510f10500c01c0100080420805038055400f0b8030a0f601342c9004d0038140c0811092281175584151414030411400512a400000702c2c2c048900300f02000380c80b408603050000080c05a90b005400301045d030300c071203252003c404011085080c4500029504508500d03c1c80c1528064102d205820403c40c1d041e500c050300c0c140c0a005480f074480c04c0d040755681c05e5540401d05120340b95208401603407000ca020541d0142c01e019400c087d0030400011401e18000c401c0d44c2010a01035140540b00c405103801041c19504c07000b59680d0798040910040d9038441c18034800394001c0201452261003080401e00102c1e56240150803154400a00e030749107402c041c00e10000000800c0080d00c80f65004605c0c080004400600c041e004203513401355005448914901755485040c240085020011074008005c200081c2c65001c040d04e4420b88199034818803540c03005803603130041405401c81e80f500341c000340d4860703040c80c1c0c00690501628001c204e4800881c02e241d510003000d50250000501107007a001c8401d2050801c000036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 447759370 1250 447758120 447758137
    0x60f03110f0c0708070803070201020c030105070c0321020304080909060103110f0d06030219081b03031803010914030306030d0c021c03021c0c0c080f07170a050303010f0e16050708 79
    0x1600c80f03141c1c0d60440ba0b031030110141d02405140d000803c00344195078041c010420200c20a9009100c80d18080100800b48000000c00900388000584140c91040710f440701d440a05003280303000c56880c20705081c107200700e804c620401c0d4800e05004001030b800354070034001d001c6014544032625041070440a502c294540004900e02c4880346e490780c001000d40d40d800800d5074120001c00111100c503041104040c20f1002c0342c91800d282c02e4150310905803d403400000c0754880d460701e000c030716002458440013034050075641c2805820700e01c02d02030010050704003000450080380210b089988240c0304c42001d403100b010005000c3e601030300002c0b4a10350b1503c15558a030060344248159444800e981054044008542c00c0300400038848549400401440501000140100c2c0d0010032002001c2c1c18210f5840c081c0b8061280b403140700698034031010b602082040d03210380e03202c800d4903200d41c0c40b0701a9041c0300c406849031004003c0307003002203038000b6017400c18224110801c2e80c0781c901c0c00d02d035526000c1c000c1d4080d03410b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 447760620 1250 447759370 447759373
    0x60e0703050109030918290d08160c321f020624010c060504110603040f06050106031802040c020f10050a0c0c0507060c0f020a0e04030f050301051819060b04060f03110f0c 75
    0x1230007800556100018101c05148418980b81c91065003015011072038150407901e00413014030300010106840050181002c048034440040304900c40c004140d0030400c404d95407220781407000c3d4100f003c1c1d8020800510601800c00d0507140307455019401e21000c0030b078501c1d86020940c1c55030004003280703680d000681d000e80110074610202101c10f0110350300340e200300c80c246d800b00d0144d48640100251401454018038841c6400d04c083e010041840b1010018504000d2242d036803410708080943c000d2120b280d42c0040307002922001c141200a40c005020b0840c0e40b19146031400640030581805440900035150b0040d006059160400300c065564503200c440940b00c1e01c0405c981000140d561103410320103000c082c441c03140c240c106494081c3c0002d580c42c84100c2404001d20050045031604c07140f0381c0d5406861101c20645807109542c1204164602c965205140d08041011510704d819400078011110b8598403c2c040c2d00c1100c1c1d04608030380e4071040241148400b041030805003d03640000c0d2414408460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 447761870 1250 447760620 447760639
    0x715050309070b03010f08011410140103061e050102070b1911010b0d0804051c02030c0f18040506180102130e040203010b0a0e0703180b04060e070305010903091829 72
    0x840c0f03000d5002603002c503d1101c021001031040c0c2400f0f00455102c0f140648a4184504120b07213610b20070328043c010741d0f189100803c03017242c00c1da2080d00b10784014102d140e070b0f402d224805e0594401e00003405001d614050300c150305000490b40c070f60104640c14a8082d40000c9038201d00c14200329921540d41100661640d03d5001d29031195070345002c00c0004500c50429207a070303546084c060140c149003c02415101c80c46031000100541c40c082032650000000700c4001d1345442144c0001904044400c1480401003040e104008c00c20800007141c5003e6803078a00342d030715404841c1c4842800c0c1e224007a4256013441010908128411401e52003540141c802000410b06d80304250100b010900c55601074005961044140200c240c0c15204c5e5a62400300d10302c00c401c445800f51074002c2c2c0d81d1009400102901e0382c03883c9500d11807d042c0282406154443d000f0f000c110b82d507050080011106004c0c80854400b50741c24641c3c0440d0610400700500e022242007202580312191130442100341c3e01e92503400c540042c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 447763120 1250 447761870 447761879
    0x10507080316110d050301151107051c0c1805090604080702040504020112050a0507120e03090d17120f10031208091c020106080c031609050a06170a060e071505030907 73
    0x5200d910013000095542036200d40c54654080c00030500079000c04180000b040d4201d9240c0d00114504007038a00c01d45480032440c0308084e041e02c4041621001070301405010402203010360500801c0107e40701c44101c14861525100d15150f1601d50070f9500a201c440700700320309801401d06400150740540141090030040040710f06170070642d40101d17175221149550b44204140207410030000145003190740c00401c4902c403860002d980d41e1090399240c070302c80c41082c44e030380d800c00020f040c0c46086110300040e07203900c0346151003d01c5c0092100743c45c0150343c40f0941340010020700c45660340f801200d803c106692018079084a0913a28101d01030540c14490040c44000527070138071300b402c00400581c0a6400094070b82d280611003800c0840d8400b101d480780c0c20190409805501d940d008000360341e50000001804d480360081c24004010b95441050140d98400110048100200340c2808060040c5001d0141d40d0b580c1d248141c4400d8103000da410100c01c0c202765071050511500256034800320a0301240c0030315448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 447764370 1250 447763120 447763123
    0x10603060b041535011b02030a090303030f06031410050109090f26030916051509010815030d080a0f0b0108160c060e0d020d050a02070302060918010b130501050708031611 75
    0x4c0c6807201c15140e44504601110362410600c001400350544050360a120715000000d0450700103200244c10592035407020620b0b071500f40c2c45400250760210240c090b14140702d03121038642c5200e41091045918140c00000c81c00c19038040e914003503601400310540d0300e010360b0f244a000c4501c002c1d902410103854803850050044800218080e010502c020700f80020038500001d003206050308164080d6541c2c00502004040c44015103404080c242040c14450313540307a4108450100114040390316104070701075108042d0f00321b05824080c100c048405d114801900c00c2e50826100d01052040c0041c0c2e420000078105c00c1050800d6a0300030321841c0c1130341c3c902c005860b4001501d41402c4102c05a42110f07080c0079450703404100034400c4907030070f0810b2820a2511180a52248818400a80152400169421282da5828001c064101803860300d03405541c44204002c400c4c2c004810b880440000070501050940c0510140c4d03600c1a8054070141c6190f03104100c08401c0c1500d80c10110a000c8845001c9051080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 447765620 1250 447764370 447764459
    0xf0909090705120c030304170f03120106030f0e060103060b0d08070b0105011808190309080114070f020a0c0b1b030d02070c09090201050304030f20010603060b0415 72
    0x1040300400038681848200111088900c241803090341c403090b0f0031003541d180442030707030219442541802603103c2c62510041c2001c3d000020035a081c000001c032600c100907405d003101e0503110305550821020503515071000880d41000c0d13481c0c0160b440007004000244d5a5041624240006040f400502c101c6548100d002e07000a041210410001001400696032150b41e501500007103180800d129840c5c43e05180d12100c1c1ca2290030000080c21490300c007814010303030141c4000c12440000308070340f410390306005111030b80a4502c1d500041c04805002082440000d0544849400101102c1458540700603c4c80640c49071503080051050030001c2c0004810a1020f4100e41c0403006c40035a40b1107d5150980c6905e109420542c0c01902d8010201d000d40da008081e41e52087c1c0c103080801e0480840d200030b41d50b16005030000b09022841c440d41d11016001900701c0300449210700b8041c0540c0c904003003000240c1c1c58a43c410758003100d5040c800c210440c000403000300e0044c4150f010003400100500c54002418 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 447766870 1250 447765620 447765631
    0x4030206030f0723120601030b09010b0307050712020a110a1a130306061d130305090f030f011e0608120a120b090709140a0e18010b131512020a0603020f0909 69
    0x14012621205c020142c0103070607404842461b080000d41007500001d4500705041c000c12106103004070010764401d0180007210310268006548007200000c5140c0290f44100002003115000c007840d100071490b0524200703980035141103980c01c406038008a40140c1781600b05580440d40440801d00010214601d8402da001810380000202d100c00100350922022081c0940182c0f0303804420710315400442d0f0b00c24140c0c0c00d029421120301c040c40f680d0380002450110060180703105940303407480c1c020301075000802082e00ca0151400c1801910f944100190700d800c00501c5c5012510800c00070400343c0f80c071480d150b040c01005508000b907888041404590708500c100c0e40c00c00496401d0509128100c01d0840d04207c0c1c3c0000c035030344901c0a0800d001030f5080100070340b07046040d9248004036202090290818000c1c020041c0081c1c00001c140f6a040e0098408241039000300c000b204000300b15101c0c07644101054070340203008240364500d01720040340258402d03283d00d080e01000b4000c51b446596001c9800e801107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 447768120 1250 447766870 447766937
    0xb04052e17010230070c11040f0b01030c0309120804020d060c020307060609021c0f06080a0b100e0907060804081b010e160f050f1c0b071404030206030f07 68
    0x301007000b603009442c002e5251282402c0b091044e003514526062804903880402c070701c0e00f140042c9076440e1a5a40008414907154040d06180004407050420351012540c01400d90f0103103e5000290070030b804031501500060145900da100101010b40030f0500303981c119102a040080700c408584070b40303048070300b81c072400c01c0140c00000d680002d010040c018040901a00303c0c0443c40d001c0414640c4c2400d40c1c2040e242c800c0c0c42e0315020441000c0025903c1a00200881c80503200030750720300e1500031013800003210407040070310880d1004988500c8104080d8455034080d00180f1880f030400b00140c410000051044550140810131022000d036413941d0821440d82e0310001203041d515201c1110b003494000700aa582c2c07100c40307480c03c0140300581104801182d50036605170180c0350502c00030131034607000c10010f0200a151403044130b04021a46015603c9008240d0390790341200300d5002d07000c2d482d100701d22001c2e505c480c062000c504600c03c4a610300b60051203034280524a880c554591460350780858034180d030300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 447769370 1250 447768120 447768127
    0x80d0605090a02040b0d050603070f120c090209061b0c100e130b0d0f020607050106061815140a1809020703080609061f050909010b0903010b04052e170102 68
    0x140d041284240d504060b415100354182801c12400800d58000c4090719140c2030b403101c0100d069a20203106040c05081441802c04c41c083d1680d91401010040003030484109140010016100d240c610039141c031040014001c500e44600c81d031608901d11400c501d103c05900460040c0700207651805803080c4100c803140c60348212803043c2c2c1d04200c0b00c24860403083c0c0d101401d154104a0b1966426484203000f540215444403100460000c07400500468000500702e40c41c011010a000c0d400c000c0c40304804055180ca44401920341036a0300040114402e45000b0a12030014521200220405401004a140b600c2161840c00742c12589481d110b990000443d140d0001d41d680034194096580d6902c00c6094926031030324100b440115024000c0079038074680d031072081d90b4a070125503c0b81084540750702005040080f556101c000d009220360110190038460743c80e1448101d000e04060003142d2081500d250154407461500100b02080d1040040d6822081c4103e0800704914801c070740305948407031000d000140c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 447770620 1250 447769370 447769379
    0x100602010507020a1e0302010914011508071d130605040b0603011503211b0c06030b04181214070b070e010504080d050d0e0f0109050706090e0609060d080d06 69
    0x2100c1002c0d12803011500030b241000d0225210381c40ca1840380d40d0b944a0385440300c1584c20202e0061800100003002c0d80915900842201d005403c042c8400954401c3c9421265a41e030f49580e035030390148610150000c032100c22400d003107108160998849414505d90208a03200d6894000b104c0c001c450031100d03150604c06208aa007000d12032091050030500e2002066030842d1550940d00c0143d00403140300c6030341032258005c0c3e5403092009101c0c5e5064000c0103500c0200501e0003090244c81070080200181c50503041031041d1030310f4041c41002d00c02c048800c82410256440d91101c440005201000b442a2841d4295025140800408405015000b40b00300ca04003c1c9008001c981c03498419810464140b00c10311090401150010900c402800c0240d80c1d08042100d40c0c0281029080072a02401546481050303160190807501200e407082058a00003030300d070070081d0f40c1303408a40968610341640c200007954a09041010343c3c1c101d80020710019039004c05950304100c0307610900c590002903884920400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 447771870 1250 447770620 447770623
    0x1060311060403020a090b0a05030a050d12110703030b0a1a0405090a05010303080f0603120c0307050709020a050a210e0307030801060e012a020a0b12010b0c0a0803040c090203100602 80
    0x3010000c5070010b00c0d00b40b454000031954105402405c80d515903880103200d19640301a900c800415016081d02d40700f090703e040094880b000c0021400119800400c0903801030032510483c259007444130030603401e19000b0340341140100030b0469595000314515801150500240b0058403a2003030321003117140c0d55030505003880170301c44014080300102d82c100001440080d41128584d0f0b40851260002c00e610b5a46800092610040e0503004a143d403000664a110200101c0201041802801140c2c034440d554880d540c2203110724491100050b00034090701c18250b2242220800146020907a030711034164285028007100c0f40540743c0d442d00e40c00081c060b010503400448a5006003e00d0074514281100c110028100461402d52410f405080c04103100a21034884000e1228a4015001d42c003680d440d0f0524903440d030b1284103034002e40c075071500000900c0072040048038681111440a000c91034160b84d100c0080d40c00c085d2040394400d4410201003001d0f4040c0c4080d40c850882100c02c42c00c510714000020303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 447773120 1250 447771870 447771893
    0x3090b240402070c03021c080f0a080603060f16021015031505060915061207020c0f0909030d0b01050d15051c1106210103050109030807050301030c0e06040f0e010603 73
    0xc0d000d0360041c4101d0340400c4007090914100d0743c0640da07443c2010804024003a824440d2180200508400b0034107113080c40c00013000c1d0100d04001d80321544036444071b108155075004125600725161911800186840e0310303041c0c0c0091a03200d140111240d040c2031441e0764069070441c8031196030b0201c54950800900a0664480211038280c000030465814404003280c00980000c121000c0310698030070015854568034100c44180c00603200016035810040402501c8034002d1035624880c0c0461100d55045103401c1c00058000c049142c02140b50041203112240982648180d0505001d03050107071810040e03260158423401c0c0417100400c02c0c958203080030018a00c5400880c1e021040c0120070090020310382c4054400c0809003152800e45404100c090390000382e006090f11202e06c1c0303c4100010801c8015086007801a03c6a01c0c1d00245507540441140c1d240000d200141c510a081541004000b4100c1ea000d500640054408602c20340200c5078007080d0b602848501201da952603000300306001c066400c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 447774370 1250 447773120 447773191
    0x50c0301060e010e06210105180f24091504060912050315191e08010e0a0506011505070f14010b0102010b060706021305040e0a2904030f03090b 63
    0x400740c140d414850344d000310301401400c132400342158060071203244001118922011005200030300041c9030801c030f0820b044000c01c018494500c140c10f00588011004100f03035004100d5410100d8100419143e000822036019010500710302444c1c076134965005d04c0010191089000d901c000c25050f44d140b80151020b03140440b0340d003c120b01071050000c000c1103820f00c2c070300b1550121803203070814507040e0081c850344d029644440c0e180c400d0450908070306c0c007c021b030450466003420000c1080808008030180ca60ad5541801002908204010f000c040004104014041500e1600c00e0401c0358994a2013510100000256100640c1e1481c200e0001e000b4026000e0311f180c20700c02480000101e4001c81c919001d070640060a0360780109020316610f0040003950300905004006000b00041c40600341d407900744143e82075030480c80c41121300314003200b1001240326810417a010808143d441c0d450840348903400f01521010181c4075030001010407810340f2894041c40b07000726000000841c0054424070b0a020340c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 447775620 1250 447774370 447774389
    0x40b0d032a0c030206030703151202031501031a090319050d180312240b121b0d0f02120f060109060908060106140f16030e0f0d060f090f050c030106 65
    0x30340740c00a003581819108030380d81602e081e500c1342c07540740084d0050801e15040e08505d0320340740f0000801c0e881327071701d8160a1a0300070303000d40c0c030386204409110188540900000c2c1210a444400b08412003d5034181a805007401080d20308007000300201d0120f8041d1800c41701c000850119802c0701c04940c42c452240c68480c4a41d60000360a00d41e035003c0c1c0364050130760444015540e941c0c10072000d2082c0045d031284100d001011220800c2d114407601d51075400c200d13500d200c100240b00005d041d80308000801d16014540100b218180007501807150040c3c00c440021018139502441a01503000318003215a000d600203c40000c01032400800050042000b540008208129a20704004101c0085034041c1580d9507440d08400d44c165042c442040c074418403d8800030002c0005030301ca141c075204207890310341c54466038031118008005801c00c0207104000c0307403485d0710035910140b9100081c1c5c203030b100304218201403034007240451041e11483c200b05002174040d1204d030091000602a4542071045002070008243c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 447776870 1250 447775620 447775697
    0x6030a17130e0a050105011b02040b04060803030f0103050c03030a0507120903081602011d062a100606262a0a0305010314060f150307030c0b0a0914011409040b0d03 72
    0x2604230480c1c260350000030303026030b644045541e0552119008480035011400442e0755a0600b503081003510030302480196028014000a001646800310031100c13a14042d55072303c0c0c10555503495111030021503101c48000d0003080c003000170000c1e90042c05000e05550340c55080540468600000d00303801c0c0d104071502d003590b2100d40d54000350794075401581e9810709807a41944904000c040c95607812109002510001e101d03a415003400050036410490948442d580e90701540d101c103507030f032080600070074443c42d690035401c42c000b0350a000d184d0303501d1400e000c4401c903940b21003084110364240790384180750500020f0303111401402400140880101041c0010300140031928024000c3d042c0420040d18001c044910944406082e41e800c0000501035034000d80c01e6451603903030b000540455404128a400411048907000440a907151001030720000d040e111005c402803400303144003c5030310071440c03950720568905041e81183c503040d210116051013900c81d800b03100c1003030081014200400580d15106801030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 447778120 1250 447776870 447776897
    0xc0c15040f020922060b1c0b1e240d020a170714060a0c030210020a030e101e0f0612030c03090b03100504180b0903190806030a17130e0a05010501 64
    0x2d600900c1080d081784001908802c2000010101c0061030354030034112242c03004100c00e00a11039600d60051010000701691401000075039448040100c43c02040e181030070800c13040800c0104104e0740349603070040c003a0590421690001d284042980c01c48041e8510f801e10842c1598400c0140602506500c110718883c50340e4080018114030500c00c018013001081c404980400d402003003a10014802d4102c20740d240c00c061500100104903507a0102d400703208c1d190034101c400e03010b071088950144960018900124440c0e101c00b010704109070000300006d64411000840640040082c01a00c1c417984d64180055610b0500406040300c030b41110030041403c0050110143c480f490110880300141c5000c25800503a010040400c00c2840015005034484410032803150004401481c0900581c0001101c0200b40e4208a03a82601100d089406078403014044000c00e00c40550050f41c1005000e1161424600741e0783c2507500b481550002410440d000207001d2018104c1c001d5901400c0300f842c04444502c0710 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 447779370 1250 447778120 447778171
    0x1b1804121d0a0314100603050304061116120c0510080609150303030c040609080d0804020d082701020f15180304150203040617090a020915180a050108010c02060c0c15040f0209 77
    0x1180320305001c1c44003c2d044410651414000c0d000c041050710200385401d03035698180cec040110080c1c41111120300e00c1c000031400e841e00401d440c8003211580d552401c256182d00600201843c05022504541c00000c0c9240103507400b007000b14440c0d4292504640c595191042c00341150f0020b07040150241c210710340301c84030305521140c00c0380d20580441d8000070143d20385c2014800e03485944004690482103481c1444541c040c1100000340c00000e0382264904221003075503944880444807400d10610400003c030b02411001301403602c0003074094040e03d00d0b05544000c4041060030b400400c80241e007000c80e0400245410200c48410b91450100b001c0b200d14041100c6038441018186c020700c00e61050f008520308121135150300c001c15070054203c8180c00e8a040945000c4101114924811810480007103071004040c040d81000c3d00340c540040000380c031030300c802e242c00c2d800a4040c580540300c3e504102250740c401c1c590381070040d4081e860a071081100c900500a16800c010460f104407140741111800310181c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 447780620 1250 447779370 447779377
    0x90f060b0306091b010c060609050f0f090723090f2d1f08010f0902130902030601050909100501141011030f1b1b1804121d0a03141006030503 62
    0x226443c2e201d41213441000680b2150400c1c10098042480c00d900030604403940d6105500607000c41c8001d01240e5100d0100100841c0104e406004640000c4010480c00d1417824038409015841c2178010845d540d0304012882c3c3c1c1c0703000c81d1510103842c10441405503184800495080c4c0341852054200a007213060501c12400901410800421116006100b0301c0ca1300340805070058030715100203004100d01002d060011b0305500c1c030145d1003101d44155403419018184207980149a014002d0322071a8648000c100440500400c038017043c1c044c8040b05032681e582440f68501a264000b50392947c402100c007800030828030300311108240a24010313882c240140c000140c0e1445040d020b0450354405403941c4400355050a10782c141114400c1030007000740b1004410701c64a003004103072aa80c50040100302c0300100341b841504c002e1300740303c2003008040001d80303c1e02004102210411404404155003008200d000007554003d44a100d0382a03207208030b44a0900080d8015030f0455001d10a072810344e210141c0300e21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 447781870 1250 447780620 447780643
    0x51c0906050115030b032e053c06061b0f21031311040e03030c030703181205160506070f0908010b0303160606050d050304140603010303080a1e090f060b030609 70
    0x180c21310f43c41121903924001c00011076040c1c3c0300c1071140c1d0a16503044403040c9201041c400e007c8000a80342800100d01e54030655107041007420b182700e151108030034008103510800e211003c4030040c03400380c0c07006441005840c8600042c04010400d011501840400d200445c14040400c85000c006001c41000322006101c410342c0c20001403810101501c00107401441504619040741c000402000003854140c00a588140c020341c070140075901112290241d43c210000b002000723448180880030140b407184000d0008104c586141440b445240d07201d840c540710b0219005800250044a8000f80540c400c81c3d620040844130024845c004440300002d44038004c1419000030070a441184000780840da0b04a50010701001d0640002001d05081c119141d5126005800325070000541d48491070030300700110b80c100c03074140e80e0300c41440d00e07400c96007000340480d1580308800c0060191003103441c000340d104070780d145c40c810719480c0c100c5141407800c4001d82e0340030f600d460b110350000001c2203541c590104000b048030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 447783120 1250 447781870 447781903
    0x8120903030d0b06190801030b0c0403080a0c030201020f0d0207022e03050a0b040c0203041707061d010909230a0501060807082e03050c100906051c0906050115030b03 73
    0x28a22400400c4c0d04c1c1c007a0a0901c0d0f540342500a0103001039800030f100300e068074007c425121155075075981201991085110082c44e849003006045240c501c41c40340902003074440d10000d840d00c2e68884c03200000c0e4100190380c1c0c6005500140000441c60500312941e95074004d6085140020981d00c114680501c6c1001c8076006c1c1512000014003540d0340f540001c282120040040040440d5403100940e650410b008056000040e4000140ca0b01c500146540803114640c0d02c1440030b107800c8146001404683d000103050022082c4d000c0344008060291514840403c3d615490740c51441c046a00014406091001800d2130b0200500005a1003200258484c00b681402c2070b964075811080c0708110314020032403007082c1107030700b076500403180b1000303080102c80c0102c0859280481c000c04101e40d8841d86810030001c50003505040280e54061030151842003d400211850421041818030550b800004200c5a00307a451005001080a20342d2180d220740992804200000c0c0f000082961444c00000320380d8074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 447784370 1250 447783120 447783131
    0x414101a060d02090a0308040303080f150607021801091b171503030706020309031206030c010206010531020c01062102060f0d0e0a050606060c071a040b040f08120903030d 75
    0x30b040ea601200c040031006040301000c5035a0341440304560700180000c40014852501090050346c175050759030700070072128000c40c124000c1c020820459500440c4d040303800c00002e148405240d401200700c54000d140425001ca000c1104c4c546194030360b900416a241440040100d4092080c1403160265210444107800028200c0810019155004100700189410f000100b04047e0b040084050110030844c0620108c55848800c01c0644486456403182d00680c4808010811031403c4000c09000710000c110440301d98409074031511840308403103481072900340c00064010102000344038803c01000e2001c0b22840c8d0089001c10b040c400300340900040d22aa10201e45500100340200480d4420b5400180800c102008a2400c030b88031a006141641c6030301988000480a00304601101c1207400c1d02e80c0540806400c00b41c0241080c010302c100998a90130074080403580d480403000510160404c0c03030340d4071421440c05411030b14001c0c0811841001341d80c103000c00c2c2500d4500100350f451480504901150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 447785620 1250 447784370 447784387
    0xf0f070e0c090a03080403050a0201090f0e040201030f0617030702090f0f0403050c0316210f0c08070f050a15050919020112091e06050a091e1502030414101a06 70
    0xa401456000617000400c000f4000081010009600900354400c1e240d1041403a9600140100c0362094400c405864400ca40020015071103584180038000004400017069174407880c280382034103880b1103843c40c541d000140c0032041d46041410554020418858a03900d8509861041d14105000c0d200805110001c01e80c0d080c003101c184183c5803184821500403607000c0c0c5904200340703914040d1900050002480c078490501d28499004070700100500c2c1c5801c20502c40e1641c5104031030348103074001e4070700c84590f24101000072424072180181c036004109001103942007080c000e0403100043e02e1001554030045020f010f6a400d1249001d516409007041c1d03003043c60030840000a4524030703400910380403025050561820b040d000c0f903550f29008900c208020380c1c0380910b010885251803000b030162245042703480342c500301110742000850301c141620f0084c040e510340407000386d810a40301211002100b0b0b000c07803240d000402c80c1c600d01204111003440042c03692681805c1c0d042c0c11140c003900414000480c902c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 447786870 1250 447785620 447785629
    0x2108060a05012a0b10090b030f0303130501060308120613060302030a06020307020c101d091e130b04110f46090504020108060909060f070e0d050f0f070e0c09 69
    0x3c0c0c115800010103c0d07645444040c2110000d440c0c00303200380d01440c02c4a40e60841c03d0000303080d4036a540c030740021851502c40701907681048107140c50071900f40d0b4991401100041b100800307002c0c04440010070700440e0400800300080410005048200603142a80800140e40c000030141030680c0c0100c00140d132071b02c4240c001c030b051104100c00c50303806c42c81c03480a102010354030003d000302c155040695840100380c11000c101d0611402d0710401551100360030307904c1141041c43d07103031074006003400c0c801418130145a6845a100c04200d505413000301000700e42c0d80340c6040001c3c1001680d801151460320a07030721035902084030101c4800702021080586203282901030b0702035074120311a140c406031100142d501e20061000d00400c0307408070300050802c00483c28a04008103200d004100f5103001c4d207040d9130764080940307051000070140c0b0100040340f4040070b40303900d40c07030070200010340104050811010040f0003186031800c41c903541c1740c960780042c00401c1680c803101c00701500710100040ca035546404010015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 447788120 1250 447786870 447786947
    0xb300112030309051606141201091a0a0e010f06050405031005061c0807120216030303020d0207021f080c21040206220608070504051008132108060a0501 67
    0x10720f60300c91041161240d1081711020012103109903116112815000554051805880c040c0c0c05500042c400500070440160040d80d1403842c119028008201d010f400030311000a16440280401d881e4001800140100c0c000000034120505009180601d0000401c0e42c0f40e82a05200780010350303a5011903400d0f9508072034200414426501d0450a42880c1002002c0380c0c04120300316110030501e00710710685800031501c40641885101c80444181c0303140c4064000c1c1d40320b00641d81d1856420451100140d86942811289416032440c401303102c030b001480900624005800704c0c1d0b084105005450895003800c1054802c4600c0102c070b5080394a4910116030729010350000c60180c8a000d000d01034452030f201841c1d104a039015500c07000c95482c1c81d40f0a86081c8201d00485800c0030011980005150068061540003004001c1c0b4089045e05138030740b20003c0100d80a5000004641e070350754000c803a0f01840c0d464100000b2200304206c02c5c0350000180280040403e050003540c00340c1110031481c40103010a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 447789370 1250 447788120 447788123
    0x609061d040e0d0201240b0c1204060e240306130f1a010f09030f11010203090d030914061201150507051507120504032c03070b300112030309 62
    0x41c4800c2c8545000c207500c0e0308240d0443d60066186c504010003824406c02612090191125806011824440385130120340c040034035140d480c89582d030001003085000001b400207201550745c0d14007050030101000300b46000d4071a854242c00d401022048140200d0003101c3d000f90080f5080060038000000e0100600524045441801e1070243e41c10900f4000214000c0c1240003640c0d00c401a0350145800d5403001402e00000d070256550141410000f840b100c6001042001401240c0c1851410310000b00c0101845402320005a500d2a08200b41901c1e1004188183d00c201c1d0968286040800c04a001103c1441804100707541611920520750158048030840386d0000141c40d102c689002c1d034807607080300a0711184002416104031040e0030010f446503601940d03240d41c9503c1d040150250b009401810f03603118404a141030200102a41d074200b103100c0042078154000c60325912001c10a0081488181c10410388002100003500700c074115028150540b000b0b000c0c0c0c05000d288a060031001000720020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 447790620 1250 447789370 447789379
    0xb0a05121f020706060e010806070c03030612151107050325151a0f031b01021614030c060a08011a0708041d090309010c030806061e03040c050103060609061d 69
    0x204184048a50000c00c0303c9809060f0901c174041e55101c004188450920074404a6000a80407a08582c80b0380a0703038045034001e2038040b0b90540c5502c040100580603810407101506410501c4440700034902031078480700351841e607050900c2096110745031207214030f868100f02c1c922442c580200340344001003100c84058100310514494004003a00100610021440403a40203100320030590b17614004456807039603031015001d0409101140814442211407002c0541540141c3c40400c0100200680610040c07040c00719060402c2105401d05007841c4c02001c54a000d0901003000e00c224940200c035007411114910390468905074a40c100d66614052004000c0003180c0000c0c000805070b02e804c100c160f02c0e014062035440d0039280c1606147e80c0e440389403035403404102400825804240900e20300d503404a03000d01801e15203c91a08608462210032070030070387da0440402404103101006481070042c1200b030904029050034280003034003900881c82079000704030106201e9084d904606980303800800d0043d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 447791870 1250 447790620 447790663
    0x8100801060b070309080115140a031e0c0510090b03130602070c08060601080118090f02030303101a0a1e1e0f030b03030f0301120f1e02040507030b0a0512 68
    0x298260342c1c56200c1c05041d0300040b007022011403030482c1849600d43d55918042007902c070710710348015100c8404d0340c04800ca40c00340d000d10001020400714400400e00e88050200031000d2482031400d00c1808040350441406020030500d4294400e80100e5038000ba551221940340d1a5034036144050000d03030308c85000030402400800d075401088400c44008040c0c8801805441c110f584660044401c08000d214810741660309201002e18542c841c6d002040c41c0c2c0c094a2000b10903501070300840e00d160700680322481124075a001c20030040070f4107842003a500c42c02e0440f503450302c0340c0324000625000703880c3c00720311380f9000c200c2ca2001014010606082c4090720640d00001c0b1420743e00000e050300f0b4076500f5101c0400c0c244540030200b032801000300c0394180309208a250441c0d080c095146840c44400c84111220040c030002c9502082100060510b90511860311059020340ea20510055039405007410081c113040401040b940d41c0d5060030f0300143ca1044d160f442c880401140441d181c103011041100c046100366 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 447793120 1250 447791870 447791879
    0x4020d050a1a010801020c100209131401080f030a020a031d091501020705060f0403060b0d0503070f02180103020102060721060905160503060d0b040204021318051b0a0810080106 78
    0x21215090280b0558012052907030780d80090300c0c241e01c10780c140c0c0700e100d4114030b4016030426080e41c0640071007070014003a10542c84001c000a0105c0304000840703101682c1a800400180c80e04010b1043e44040e00c0b00a1070604000c0a406581c50914500040610040c000c4a080e9000c1c4505a10b000f010020302c00501814100148030b2008500e00400b03005009076000840c803814014211085400300c4540c0c14603181c03440d00c81c0c40003840c0c2d207034030268005a910003000200f2000c1000e0000c83c0d0041e8034281d803280c0148100a2011604070310615141640c07030041000d41c0e00402c2150f440501414074504080c1c803220140140f00180d43c1c0304004524020300482c88564641c002417180b4003501011529203030001007996280003c40e0142c0e03004c0000c00401000078a034034051600a407020f0809810190390221022481e007041d005110b00480e0702c011050900c116002c0ca50b08070b080e030268400e8203007000c158480c880c440c0c10690400d0000da44081002507003180380000040c51001c00810019444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 447794370 1250 447793120 447793133
    0xf030406050f09030c0703080c120403032111180d050639030106050a0210050703021225030e100c0c02121504020d0311100b0a2106020304020d050a 65
    0x2074501c0d814225402c1c2c0042d468000000071501c201400b0310041072010f00d150b403400d40e070b903002e082c0c540c005014640c081f8a5451000d000303840594400e486c3c082400d448500d0a80080d0740501400486a0411300d0741e058014601c01196034000120040c8001c1501384000b051142c02042002841031042c0c03410030081c0030070b8a641c0c1d4080b450a10040c5899014100320380c004e5411450008032071401000100b00440c014401000d207440309005450340300d40b076082c0d40422030b00c4c00c40e0302c078012076000a09941601440c0300d215510030700b1041c28001c00b21001d80004095004000c17140241540d07a8152140400c0403c580ca640c2d5400b00014411480d5106000304012031048003280650701c1401040028040032a07041c00c3d01e032030400e0070601e540d0b95800b0004070088643c001e60038440b400f0300c1e01d40c3d03d1b0300910030304901403090b220116050f8020700038081c1400942d4008005c0e000c40990000d100c88203a2100000250080c1004d031b16629903000161081d00c02c0340000b0a244241110360040024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 447795620 1250 447794370 447794381
    0x1211070c080607020d1404140a03080d1a010c0c0b030606091e010e0a030b28020a0c1202030414040f06180b0f010801030807140106080118150603150c0201020f030406 73
    0x10130b0b0700713403860380c4483c0700c094409041c180003607181101c003130005000c030542020080c4688030000303102c0c03140b01d0303900d8482003150381c0652014422151101520a441c40741784c0300800600c031081ca041424620507883d2105000458029403c0158000010030b0040c0d6696003654040030340207090501403106200c450300c09510384500c140c04a0302c1c403000e1211502d03100c12030f402101e401640095455440c02e0a850f0004030300ca0800d00943e44003042404050110300c054212000c5a4454528410081c00e18510a0300e00804e42001c65004110910074981c14104c950030005040d1400704010b95a4030000000d0001078110312000f0701e40c2c2d1082569801150410b2103405030941d0050085c201c804c00448018200340405090325808000c6000042e00024015649991300e00c000110241c0f01e22002d425038060100e61038180420203e14400d00c440d916015802070b509400c00c100c46403841d9a0300010504402090000c1c6940c0c0001903e403034002e40444400b40c20303450080741c1c0c2e80760910b440002000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 447796870 1250 447795620 447795631
    0x20100204090b03060c1312050307061d0f070b1204290415091106090a0f0f05130b0906011b0506010b03011503092003010e070b07150209011211070c0806 67
    0x41135901003000317084c00d901100c03401e40301c10095100c01410120038554601600108031040d100c02c0001402188044c13050324440f10407072842190203038903103254a103814164881046217810210040120a02a1044940c40c020804d00030005a8a0f0f051030151205d52a030b0156135010445447d401d00c604a584e010301c03581c1f08044140041524071062011200c0d03a40c1c000302040c040301c00d00034503403602601400100300002c0241952a884a1222103c001190302544050b0851142401540303040504035010002d03480c02004072403038110015459040240c0121f0500210b90b0200244d0508643d4202d5810b410000300d03031981d6900c000c44405a4024803d502d404682c0c443c01060716846801250303501c41d00000309000009040084100401301034200c07907070540d030b20303221150020fa061045d540140801200c135929080181030000c100c214004032981940c1c410080c42803e0b80e0014002c0d81c0d00360407490001110010105450381d5803152110160520740740401c0019031140000b091032086 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 447798120 1250 447796870 447796873
    0x10605130605040503030a032705010b040c110604080c100c050714190303050903161401060515340c0602010b010c0201091206020f0703050403051c20100204090b03 72
    0xd0361100c1c200c4050003a4002c0303c0d81904100405d41e5028400c0d00107054203444c44202d0fa03078841d154011401c80710b8980c1000c441c1a51250425036681c9844c0c030411461503054233125000700780d260142500c0340c90080c00100380403004102d08403800750400c554000c00003161070400030704a1801024045401c0080100d4030030740c503104401d03941400869980c0242c1c405190782e00442115076810f6006c0e240080c903925951105000005200b1652100c8030001409400c50400003a0f4020704e140c01e462031a000240604040074803904038072241030032100209880c2140900740d50500306010440c02401e00c403442c4030bc9024803954240308040313208200f00c1c3c080d50000c00401b0040401551010510b030310180c04076288250800c01481a40b04c0708007001d10500d030040c9030100d80801ea400e640c12980d4150000f0701e01103030074410007008214100070700c0c41900c42d040d41c10b6200800103001d81101030315400500401c2c0f000c0328800504200d040b0300c0f0003401a096484984401007600108070700d80059109 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 447799370 1250 447798120 447798157
    0xc0d1106010f060f0c05100c05040f09020906030f040f0b0c0d0e1207170903030307050408120405101d06030910060e07020a0b070c0803011d090105090319090e010605 73
    0x1640c03402c09070004036003442c0c990725007a1341145010385800d0800c1005039854010306050703034102c07180b905c80e2242003081504c1c2c103901c8506200c84140001c603950070520081e80b041114040b07c1d030f901d20907641d1207649859003a102c0c1d611450010302240d40313030303000500401c03480050010710b02c0c21002801c40d0002c0000104200b08159400741e0341c071445503c40b40c041d081c04000d01e40100d600c00204110403000b2100c3d66141090032800310b46503030302c11211400080d85c007140500600c0018005100c10505159142d4101401c101c00240c503881d42882200a0010400354600b10341030107200180b0074030000340300c1e079142e2816801c1c481d00d590f603003400c41c0d00030b80c6072510110705250396045281c0a00c0d926401041c60106d2680c0f441c512071000b52183c41407003481e4030341400081100d00107502074415000c040f4021318000b10349003909030001c1c00c1400da0781d0401d02001403d00e0000b003591450310101c4c040c0ba022a0b100308040e10300d0311036500115a088006000451701c0d0303070843c004220344080408001072303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 447800620 1250 447799370 447799379
    0x120e09010f03060515100c02180c0301030c09020702010e040f0b0d06051009050c091909110403030f05210a18080909070531090c0804110d0807021002030c0d110601 72
    0x100c005c28170b03402c2e50001c0b110b0409034409110f02d41040c107891000d0449080c84a0034031809040c08030455100480d040000014401c0080d0440307460003d24012030294209101c07030f40040c1410380d244610f41e000d19a50540000860171030f800c802c042a00140c02d44c0031681143c24110013038682222150140c5c503d450000039503041620a203072003011b00c10385090910341d2000401060365940c4000c25502c032140000070852051500c141c0c8000085207542a81d101d103076240240003800841603c8060040900070010100400701e001007101d800011054200e5a6180c0700000409507422480000f100c0c40440c4010004208010680c0400c200c07100c07a03050303581040c2152240f00d00020500c0f401280e800b900420030984152401043d04594010803980c1c8801070503080311072000c64800006c16440502040c410f215082c00d50029068540000c5c0ca11140c0364100c140c421060024016100400c182d20028800d00c140c940464030b041c25185d0440c9103000003007400c5403c1c558011f05008000000030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 447801870 1250 447800620 447800641
    0x402040b0a030b010312180f0e10061b020301020f070c140a080d0503060a05060703050a080f0702030a080a110412051002030708060f01020c06040b04080f03090a03120e09010f030605 80
    0x2101e81c88040c5183c144e00b03554031905600c41e26a103450521825409003030036904c400c118030015102465064a5051400c1c8000e030030f030800603040c252115010f0710288020340d401123540300311201c40100200603030303211300c0440d0083c07050300c0782a0089180400c030314081003600c0512030700310755030f50399a80c200101080801c220044140f0031482e595008008445689014001840d88100010044092260b407a4045a8a50300ca41c000b280024000190112000d40040405400040a0f60050381510b0141400380da00e10814260b141889801030010340401c1158202c0c40030042410f00c12a2030365500c041c00501150800344c203c400b4052400a10104a61442664841c1c070361543c6000154484005001040c0d4928007124114040d5110350300460b22000d009100800200e41d1840d5140c0c80c24810505041d144414912550000c1040c940e6907616000858240c90300030220541c100d07101c4100303880d402100b0542582101c800000024511041d600003003c69024107014043e036a10381c48402d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 447803120 1250 447801870 447801889
    0xe01062607020c010809010e0a1110080103030e190b0c1c0c0803130515191505310f05010f050108040c1a3c03040809060a0e06070b0402040b 62
    0xd81c010303408480e00c40c07803d42c490010079410110301c100004911f00b50000140c00c0400080098440045000042c0c42e1410311111070702401809181400c0254110342d0014120803614408603c02d00c0a0a0b042d032609042c0c00091008049a4100da583e070745506241546408080280c041d01c580164001d08405010304111445585e1004945196945042d102e43e18281e507028150741c240320b011004001440c801d05110301800c10200d81c9242c8500c800480740545100102d000494484034130104001c1d00c4520a02d00400140c02c0c2580104143c124908074062265002d068503078244060301900307103c0c65000c03e0607681600a007542c099114030042d02d103102c0555005019003200e0204214500c0d80003512004407100d5107640d417504105480840444684102c032406801c899106c2c88030003020b0140307442601e00c551500078198903060b21928124068006064004d480c00240d4882051044083d001f9080004180f142c4a41e034078102610a0740c42210300300d008610300300c0c1c84a0700349403100781c0303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 447804370 1250 447803120 447803131
    0x903040f03031d0405040303060e01051210020d0b0904031101050c04061b15020c060603060a0c020706260406020a180506070809060409020316020606061305190e010626 74
    0xa25a803034510b550481d035001030050b261001400403910078000383d0704e901035140614001d80d40440c0c3c850900501c2d2200c14410b0f48940d2054034461100c0c4000180419429034851a0100060b2140e1030306054102500f0040500d9030b1010311042000b04240d0800340318503000d1400340080299581d01070700d0014a200d00d000310b00100d040036a1402d909020006800100d40c45451003402000500f141d940990300b000240750303140c1d0084e10821845003401c0080035400040c211043c442c01020260180d1165841c1c0140c03001c002c01341c29081c40d000296107038000b0b40b81d4149210011846e081c00c00f00000d4009140240c0000c054060b0541009807030b220800680caca00411350f61a00c036003590b68107211351240c00015085082400000341c01d01081c40a03501c84e494008012080050b036810003030a000e40105094410001485150302c101ca040c103031502900c1003031b032f02c44044142145203807a503001d40382e01c031406c100c03050800400d405e58000d210310452012580300e0550505810a03050034030404562 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 447805620 1250 447804370 447804389
    0x210020a11030d1b03020f030c0307060b090f01051009180f0b0a030302033f010305060f13060b0607020d030207050a08030c10090c03080a0f17040314090109091505010206090304 78
    0x1c030a00883d135110980e50315203e40100c9107250b00c044019415030304410700e0190030390000b00c0c012060040c035025120039042c00704c681ca02d0768980201d05000e10041130003003a000d480e2880e601c40c5010300074002c2c03034060145c40303801c0100c2d0188000140007405a00450401690400d84036581d503040442d040015664190090350070000d12001007010254800003140200c010b8000c59000c41642403110142000c0c0642d07407201940c11418890310b02000940401c504052503010400d401340220010722040e5403005012440d03401d6400062024042d00d0806580319000c081c507041010b800003000c50407100b0540340d84075459a248051078403030042c04010344c19074102280d801c0d14500250700034041340c0c0c481c0e1076208050342c40380c031410b406801c00c403405e40201c1c032464001912241c12400c80070360141c0c022244c010500d0669801002c4042c00100004201004138110840340c1c02031103414040c0140440c200010b0790903440c41d00a0081c03900c5024054011040030861041021003200c0c140c410150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 447806870 1250 447805620 447805637
    0x30e06120c07210816020a0b1807081f0f02090402161e020603041704030f0602030a051006021f0e0d0503060f0108130b0c070c140f0108090d0c06090210020a11030d 72
    0xc0e80e506440c40c040005c14118003920346044d00144090514601a0701903040f2000c51003038801d80c079450003915800c00c0406510804811580000c52240c007240310900c0403021810f98000141040640500340c1d9240d40503001040202d001101c81d0706802071180030b60303c81c0071510071030b1480321100d482d01b0101941061041000a002c1188501d0340801e208010b4640343c41c0907902c1e01d80c003d5080040754200c900f0fa4000040c01250100c83c010300750003441c42c8450a009a01e01040607582c0d0311400043d18122a98203109511040c0551244908454130010741703e0203c8644c10003880340c0d00c01c841c0c0e5442034882c40310740301c01540700d60403051040c61080d00e95403020307103262160340307040900400b101e1140c0c2d81002034800140c00c41b0480c40050030031a5500d00c0341080c40042110041d104001a81001014803c00040301400502031071b402c0310a00341020b190f49242044d20180500c800084d401840070580f8020195001450b0340425000e001003e261500035410103881d00d0007058880c000940380c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 447808120 1250 447806870 447806881
    0x2010b03010f02163c03030e0c180601020c0a08070504060b041a03091f1d06040c0603021b0304030c030318030f0303020318070f060f030e030403030e06120c072108 72
    0x4500b15890184180791400003070010050010785070040010300c00b1170160101c6400301505070090741da10740041c901a045031449680170880c02910071419000040c10305004c511540d00a00458100760f401414414000340c8418100c5e41da080c0904c144c40c0030303500d0843d002841401c540161419585101500d5030030b00602780d5039040da900090590140d5008400c60b1071405c4a007032000d89051001c00e1801b0400c20003031002c4110300c0c0818810002503403c058100030004903041b00110036502c060500503110601103a0030301c0034014103d01c85400d8440098040281700c4004c8040044a101e0b540d44500300d030801321120f00c541c0003844020801109140e000d03000900070f0b0040c41e0302c1603c19002c9804500707024006440e0844651103c614580140c50511040740e016100e800794102e1424203000a10415442c04d541e03206510000e400c000d00e4004680051782c0300f1086400200303565100001d941800300c02c5451540c0072040403180e401d9807191410b1410803d19044041c054282c450004503541c0c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 447809370 1250 447808120 447808133
    0x1020714061c090516060f020c09070210050c12071107030204180204020d140a0b0d1202070e070e18040b040f150f0f050117060106110c1002010b03010f0216 69
    0x203610503851040c00c440c2041000d982407040341c403c3d5000f80d0040c090440e24800031040e150f841d400420030804802910800e480e000580701d94080416510b2407000c4c0d4400302c00700d060101c0920080300840c20402440104400d1101408506103e40f1021085444030301040e5409441c41e0011030700c50300b2076041003000d03140584c070500c00300f030b03290380c109500000690020b0101d9100170202016182d940221241d030a40001005920500703901c000c02100a1107000540c00c1101c084005100403403407048441154420301001000301290000300206052001014148046400c8014060079401060715103060400ca511406650019000c0303510342c80700e498212050303003403000554101c0c0b110f100702002d50b4142c2c4a5032041400d0041c00107507102101c5604019540188d00084064600d0060000c5012000c600c01d030440c0c101e41429040c0c4d000d50084035080c000344480031588008441ca07080f200c0f503010340099000b09012802000441a0a90303084101d010351110410340031074150451b00051b66 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 447810620 1250 447809370 447809377
    0x507020904060209030309040e01050405011514120109121d01080c04050118030212011e0507020304051c051e0607140a0f21140127090f050706050c0c0102071406 71
    0x13002e002c1d80e103410440000b09065902a81c56005035a40d44c20801091045c284503440070011121190301c807141c0341c52503045010320002030061007003120200c6003c010030250f112880c01940b14842058012810a015201181600c8030614072000764084120541c400c10310544913030f040890850400d800d1200451321800719040f90b00124005050120260707640454030440c2c070840c40d0000c030324902e0035840c0d50000340c000c40002da400d80c209010301c0342858001c0107840c1a10001d80d5031104180d006150449144440d2001500c0e50013040c0c4d0300c40921044031400d40d075188940c41120030546481a0455030484c0740003000a005d41e0130311a00c0b00c02e030703c80c51030607051603000d1070005890442c1c0700224030208056201e04070f0315955680e015080420040102e4014140c1c1080d2032848100241e0300340d100701103c04100c0071250f072262080d003000003000c164408a5044011100210b446030009426135114107601768051003800c03000300c407541c40021008150360707007000000610001301045c004d4541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 447811870 1250 447810620 447810637
    0xf1811031305030c100b030106050402070213020703210c0f020d0c030e010203040e010801020301140a14130908031f080c061204060b1207180626030412060603021005070209040602 79
    0x3c200041c0b448402c0402c10046524101d120010307a001c909802c040c211040b81d4003444c00369006000c0742000d40d51b641c0c6414904c0520100141e580c00c810720f000c03280c20600b1481880d0f01583d4a80b096004d811980c0806a1280144c0358004082c40c2040d05a94901c41c072754084001130301f99518080041e03ca078405c2d17007100b1810300450f0f040a85400c0c07581d581c400c0c243c210908503076001c00100701c1d12244d03040254403c0d40583c2c60704d40b407908290303800398011140d50103140100c1d00f0100141a00f0000e5001001854114100b66103a0501115a010881c0308c0e11000e101034800e1b42022542c0b000108000c3c0005000416041c90301c0030105252003820b0000344259002960340d81005455110801854442032264003e040d41301e040c0141802914040289514514600142400302e1211005410724002c4809110f006044082d41058070b5403089400001c00c02c44075840c000e0401607980c1087c0f042d607101301c0350803601098400c000c44050040e00b00283d44501001c2c08100490034a600816a02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 447813120 1250 447811870 447811873
    0x1060b030c0d09060f0204290a090e04030203041a0a080a0c0c0f0c0911031e010b181f050c0105090c010203031f0e040c031e0c210204060f1811031305 66
    0x61040d072180720101e80007540050b100c58101c02c500801110a451423200b03c0b4808c0d0405030809000b420000e041d004a030048041d04810900400c06060003041075030007c0c207041142c02c03c4035100e4044504941c001c2c0411801040c4013001250b0000303064020000f5180d40e940e50010003015544407403400010b901e4082d15075041408000c5041041802074076400c005072030086a0301d00b805403034680b95110100340c440d04200030350014000c61007182d04941013a6800302d402c07001c03c04a131000440c25121110460341104c80c4081402d007403900040900701c070f029100003c0286640d80300245890b038200c14001801078204100180728003003c515070708074001e00402e0310041103480e41d01c0214000b03000c0d901500c410030752450400400c440c1e070710042c050554003440e080c0541420740e18100300ca01e843c0280c0460b1004110417500b02203e0f4400820000d030010302c00e2003190360b207100c9107042c0e001e18015108a00340e100d07000c480c0d1007546e0090b4a81c030041c800d5541e14580d6010322411482503e10000c646a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 447814370 1250 447813120 447813131
    0x61b0c0f0303051e0a0c03120f1a030c0f0f040e3a0c0c05150f040315050c07080304080d06080a050d09080708031206040b1201020c01060b030c0d0906 66
    0xc4000c0d04040101942c82030329180c0d80c440b43c01140303c144003100c615408240d102041032284031a8030604140c4080d41c181007580c0e103011460840c4010303100b5040b00c81c00c0f640c60140ca104200340518210071a09000f501600d60117041c40302071041e43c000814500360844510410b4988134100b41d0f000042050444080c0d83c072280444d03586245105001d00021074640c444100c10700400d800005c40e480c0c9048a0412116146840d61071003020380b098811a480303a42d41f111548842501c920803030b40501065081e45607103585a25155000880c03001003500070b80e240100050342d61269a044a00a940000c1c54604682e01d5645120075a40000342c00d66500f074994100203400b039000c00c40712018500c100d0245c004d10481e04c900500c00789182c0e205600e2a80311000400010b8030100480f030200710410811a500c0d5035a01c0130401502c48118400e401c00030303080407800164810b501420300e149000d802417048581d5050f1a1002d40025078a02902000402000194002c1680b20001580c81503002046 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 447815620 1250 447814370 447814379
    0x1030210030e1c051207030207030936150303021e060702060c0c15130204050a0501060c0b1f031208060108010f0e07181401030e12070209040809060a0f0e0109061b0c 73
    0x3d00800c2d1a6900408c0d00841d001d0101600300d4aa840680000d4110040074410240c7c4c0094803c2c8415887c6401d10341c0c0c41003100a0556600070303182229101c09012049a03584c60300039513440005039540e011001d601030f140340c400b201082d4107004203c04d03802070889071115401d046d07a81c0d00c280303003460580c45065141060b0b0605c0707440b943c3c4526a010740501c0180d200340144010307190300030800c00f4032500d48001844070542240100b82c80350381140c0c140d2030f10798410b100c0c0c010300c0c41c001803428083c551552000080214000f115650b100322035443c140c090301e42a0055a0205c42030040014400310b4a0062041e85031523005294045800d15001c0d2042407a041419080090754000324400603c141c014421941c00d8020209200c1011000b0210200482c1c80700925001c0c02400030f01c10340540005c1000d0003101015200d50510042c0070175503c0000f4000a802916050b40f00300124014074559000c0350700901c420000c81e8015200c030007004118444a0721034007135207141100c0300c0040c03890115 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 447816870 1250 447815620 447815647
    0x9030c02061323030d030903020615040204030606090506031501030803010e04110d080a170c031f08010e01090b01140a0920040806041b03260f070b01030210030e1c05 73
    0x71043e9220340c510304103480510706043c01c140c15031840e842450708101c0c1c01e0340000d900107811a40600d0542135090381c3e09403035002070064406d035840508068140755003c2003c01469110754040c2070110101c8182800c0700c04510007007c02440f020b0030b0b404042c401004855031008000c3d501c43d02c540d0104501080040014000c01c0303e03d2002e07141010003003220322801d90000c28903151218440943c49a038509100c0000b55444024046030040380807115041100d0104090200940490340003481540c508460f401c1c0240000003041e1500482c1c000005024800c40d00b0201100c68040c00c1a0030f00d5042150050240200d025140a2000828901c03e1801d199034086c01c0542924005800c560a0604052102541700203003101e401000520030000182110751800820144c11036183c0341e58094103102c0c645010700002e610280b20f0015500040108459100b4140e910885461b8507054400204404603050301d207a03041070764000407141c00c0701000c11007800302c0a5001d20300f8520f00040c0702c0201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 447818120 1250 447816870 447816899
    0xb180c0711180105151c0e0f0d0305090c04090305030402010e03120f0c0708030a051b1e03070c0603050601020307110a0503010c170115080c0a1e09051309030c020613 73
    0x44101c0c1000702d0060009160907021003045180082d56242400003c8442c031075110484020503212541c0d4082c00c0d0111501441807025901c00e000541c1c000300700e80341c0068081c2030b04403035000003801081c4901d003076460701344500703641c00350980e80e1039007190303070740d81c015156024101a5680d06206203041480381a5695006001000d01e0b1801e2a40310b0035200329051030904560415000354200380305011180e5400300c1654840400e500300d09100c940c0c890f007114108030381029100c40300e03c10170f01c1030758036650000010b0601510560b0100201030b0348600071811124140c403d40d0042c0c100b0004d100129402400c2c40e5141d81f00105111007103691500041d007141c0c40e1074140008110780703e0504138906151441c050040c00c10b071b13260368410b81c1001d03002810010020941846020041100e000e59445a02e512000b4501200c444041a001c0080507100055600c80c0920409007020391260444241c040c0f025084e9258452071101c410399800c0042a0300030880045150f00c08410000e4001c10400381c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 447819370 1250 447818120 447818149
    0xe0a0203010c0201091e0506070818030a0c0201080f060915030f1c1d030304090f1503031101060f12080f130f15020a171e0304060605040b180c0711 65
    0x146121140c58403a41c0b030a40e109002c24800c0c00380c09180c01050000c140c82c2e600002030f01c0d0ac03d419030740760b86465070b0605141d07600b8180c5220200c3c0c0c0321140345d04940d10041d401e000b40c07900c40701c942c0d80308900400c00b0011100700303820442d51000701c0ca603050380488400007510000c3c184c418101d1424580c0d80b0389001c0c00c070b010448540e1851854042c40e0801700c0c0007410f440e20840b02541c1991358001c0f036541d110ba846a242042e660b5504564080065400b000c5aa90407081010140780c1c0d82c14003e04481d0070301070034070719946440d00004420920403442d02c101c403802c4061782c0000115407912646034000405080c420b03001041400c25006000f03410700301402c000303000760600b0750610364118001151004080103550042404502103004141c0e560b2004018506155540d4100152800d42c1e1007143c1c00403042c0138000c000d00041082c02e82001c01600d505840410102c8280f0080200c241da44207041c1404200308004100c094800000901c803490080b20751024001d0801c01051030a82c19a41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 447820620 1250 447819370 447819373
    0x918081606140f1b0a0c0f1401050906060f030c06090a050613090c0c0201020c0d030509040903020f1009023303090a03080a0e0c19030c0e09150f0601030e0a0203010c02 74
    0x10000240801d8502a41154415001c55540d8400049402e564403c140100d0300740302c01d5290320000c100d880350347d01d80a0703580181c102c0c08050b511100380c1d029081c03d0350000c03100e000b403000281e00d6080c040d04030039040c1002802402441c2c003603000e1140c40c0d072000310042d402c030511000c0071804d500c42c40700400500307001d9501e0094045c50314007020100e030300020101080103083c243c00805170b17070b0000e01180f4480c4111101d40540340c0c2490242c800c2c1c8039244004c2c1e0000d007460711403414103401207007100f00b40c0501026a54020300c0c4c9041c9204845510200030350100700342840c19001201e544099680012081020020401c00302c22070842d82c0041301c001c0300c11b0380b02400841c20954002e80b8190407034851081032102d002da000f1155104c0d5a07640d18140510a0490b41001d00318040c40140c004507000303580c003903000d503c03400144025081191043c46900c614000144540c449042d403a100b1100150f030b04201d504d8900c0110007070300e50b07103000c075006100d10b01280c000340e41d0a11602540e42c50940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 447821870 1250 447820620 447820661
    0x15060a020d020f0304061218021302040602120f04150c050a080304030f080907060c02041d0105041e08090603061f050315030604080d1d07030302030d060918081606 72
    0x1d0000d00d403005182001c10160014441004040d41003080c0030003035441c2650124514610000c4500b08114a010203036101540d5440c1a1420b40664024400e5400980c251032200c07060008104039841f42407640480140b04020030044200480c1005440400d10f10b01540f40c4c10315625014905246880300341d66240c80081070004151704050240160000350a10000c41d1501d00d0b007198468050380f14030414011134640500443d40c0756803000c00000b2144502c00c103078156044c07400d8028a8201c13012504d002030034550907001121800c03000407950303001c2c480b54a0501048140f10701904003804d240d0b0800c583c2c842404071100d0103200641c50f00305554800e904d034a0982544804100140043c602903042003090101054401c000c44040c98140c0e500442c45086030092174001100c52000c1c901f041c021000d022040640c080b004001c000e05d200300902038240c8500014046941c4140c10904a005090705140000c0c45000900382444103884000469289074807004145c80b2301c032441c20ba0300700090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 447823120 1250 447821870 447821893
    0x40b04230f01021b0604050a03030b0f06300c0406031d0609011b030e12130308040603061418070c150204060804050d0c030507030809010b06040b07141c0815060a02 72
    0x81328000386840c0c490001c0c241c0c0c2c10181c039010386507101008090700f0941c175100c0c0054282c0720700c98451401400038060590b9180f0100b80c100c115014450380c083d85050b102090748042c0c8291101d580200d0103070725468136007443c00724261700406e0000ca0b039010500c160030700300e6100d82e0144402031003000c0740e4001040940780c61100030011903a541050091600d841440002c0c0c001c00106c2c4072001c60444241980c503000c0f07001c54269440283c4c40100442000a000300d40258942c2040c1c04130f8203c107080341c03140842101008800340c1c0901000349562907180000c0d14162260f864542103a0050301d50000c0741700380c1c0c002c3c441640d0041c0c000e079000c500f181040c0401c000003003003448085c40d00c1d450301d040f01d002a590010043d2042040103803c211903940406c460203000e46c007014038071100510065603169540704001d62500034a00948440000075001a500c0e00045030b8240c08004200550481600e0b1110903941d8176005070400710b80003018140c2d0403050b02c84000410342d10089400420100c1d481 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 447824370 1250 447823120 447823147
    0xa200301111c020f090d0321090809010c0f0507140306090d08010b0a0311070f060e010b06160c050301050103030206100f0b0915070b040803100e040b04230f0102 71
    0x61007101e00c503500b00001a281403041c1001c0c108491542e41c0960b48007191000c40c0d0f070030300a01110704c1d80030310070390401c004068200c140034882e05100c1c08644000941059a002144c03220800540307402403c0000e50740961040c850542618414440052488450785035985440001c0c0c00008000e908907218621030724003080726a91020350f21b0020418030804c0da03001000f1600621070b40340440c4002c00e100c1e1001c0d00a0308440341c400100344420b503c8042c07905117401814131060042e11340b9442d00300d5215040206010b482200c3c04060f0105140ca1405080136401010030070050f500e42c000940701143c16907080c041c05000754013035030040030903041c61100715240540f5903000d0203404215110030442c1035290b100b035405450f411110604490510b9a030b903400c0344954440141841ca540c01007004221202c4061801070889079030b10300c2d0094032500582003556003640d000d403c101c01d0070001000030300d18844242c6040d03075010500d0702c41501d40442c2440c1c41d1200385201201c1c0d4012030b8a100c440030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 447825620 1250 447824370 447824381
    0x3091f0e07050f0f0f030a06140105011e27180b09060901030c0e062106180109020a0905060604050a09020307021902130e0102041a040302090901061d090a200301 71
    0x42200c0101c141d01042c800140c440a042c40101d004400b4845000d030320b42d40071f00400040e6900680b0034807034111074010328400c0180034081d16021403561204217503030304001840c6a00840054441e505114403500d081030311074034001000200314031101c001141c60b0419a6415100c0140d201003c103c03a8030b0036040010710903008107a5401007080100400110382681144403c44010f40c401d80c00039210700b4040b420100c02c0344809417080145180a00c3c0385100000c00e94420f0241001d82d054890a44100d00e003030758070310300300658032014082040c010000240d000c4c82d0008070041210f841c195545000c264290410752041d03002d6a4040200506141c05110b408001c9000514000b0800c1d0a54001001c10905450307402c41c842d50307008d16566054003581110090540110300003111810b00c9050421540540002c0380100034620110720440130502070407050342d0106030b0114203204108911800502c2c02000403a0038882c0c40c40179000b040c281210041c14111101100e6260042403050609461 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 447826870 1250 447825620 447825629
    0xc0807021b04150306021305010302090d0807081312120302130911210403080108012901170c0706060b04080d121104030b0603010515010e0103020a031b030603031b050307060203091f0e07 82
    0x140100002c6050303540f170071140020203a0ec03485441c0c031001c4506140071a406409106904042c002d100410300502207e010075841c1d20034101d04101d0380070700504400740d020300c6950701483c0e825000700340320a0039290019441d010f04105450300b40050f02051604244076110340c2569148444144418594011051400750074088003c0c001c510300403105012003211403c07403554240c0318190203155a031142e8031001049211111300d10b094200b42000803155807052070125445450b01ea0300252007000c210a540403100302c04083d040c90b54444405440715421070025081041d500c0d0180100d9451500103000994055541c100c680c0c64034000389801c40d90003410804119484540a0301d150703030300c0704000c0c062420130301c0c02580350055141d050b400b4000c40d1944207950003007d071410071039603855803007038044038000c1c0d45070003401e10300a400481032041c11001500340c1c6c00c02c02c001ba01240d06030f002981c01040500844d41c20754162903880d00c0b10140d1481008140d44c441090005030303041000144040e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 447828120 1250 447826870 447826877
    0x10f05090f0f07091a0306010902030126071a0403050616030c0315051c0512030f0609071403150d11030f0c060d0e01020906030412030c0807021b0415030602130501 72
    0x100e044030002a540c00c0c3c940301e02e400b01a2a040d000d018800400c110811002d40503086a40c1c80d40c5540c00680650424050b02d40825141c01c0320002c80c407004404103124000c15409004040e04194001c04105504085400342840400000001034800c11031640318590088920080080441c00241030b500561300083c20141070a543c2501c0c1002c84404034202d841c102c40340705019848003410304074407004690141c918002c620108001c10280e400035071086208a40c088140d0f030721303403040000306e10b03040d120180000c11100c48000303002c4000c001140c00c0070001820312441c4140c240000e00e1601c00050880d420b03010041d54520900342002142d030003c1c69000074000c1050250081442406106040120302c1d440e8005144076903000e41c1140d14842c00034000315940d10341410008005285d4070b4088000a141100581c540c5100701500d42c01844580d01803c55070001d132000707507200c003c104040e582c0182c0da82c40c0c0001c40c42c2d403040c3c03e40003544250350240c0c9608054100304611003d903800079051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 447829370 1250 447828120 447828133
    0x705072a15020d110c060f040905250c0201031d030702040e1f092a0e0a18030e01210c020111030c071e0c0e09010e0d2f010f05090f 58
    0x30754010980c14030f0440c00f4a0a450300074015118585018400daa501d50484400607645080e07465110040040d00c3d05094140001d8490b042c1c0041b008201118050010080340141601c1c644901800b4428030700514000c078024044c15032a0b40d2001e26802c0040941e48000344c0c060460900d4001c401a02c103010303003d44000010f000c2c0768503551400c04c550803d010303030b160140400c03c845070b2141440c0075003650716a5a08110040196280c40341405116032214046001a0848019000b80e40003030401001c18491070b511a0707415140c0780c84000100e814428169144001d049011318204090020010003003503030140440d001e8215100e807230b01600d102c0000c108020f00404034904036812180d100e8265440c003603c0118000c81c0f11806400288038034174000f0000340103130a40702c02c0750240c0e0503a0001c2000c8509000342c29079880001a680c40820070f030b0804481c1c1d5045034004101c0000051402c24141200c55a038207003120791300c00c00300200f00e55800900203060010803000e80e480070480c000303111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 447830620 1250 447829370 447829409
    0x7080603060601050d1103010801020304032c010c050c090f18061003030c140d024236060f0c07080a03020405100c062702090705072a 59
    0xc980c1e0005190506000b40000c502c2000039044e40052103500746500b00395102c2d41c44201d2039000c0d5100b034400360005a405642c06000e641e82d07010100062003404d8846412405010040d42d518501c004192030714000c1c480e60b44000d48030742801601c9003c480c21610700c1c43c941074206025142c0f0255007610140e000b0001c000c0300403010b0308440190790f0182804586e500d0b5500d444146902c0451401e021401000e200d00c208940020729129050345822090100c241c4c11a0044030700010400880340c418150380944100300c0310105020b412001c0003030503c0d10b603c44400e58075200d00c411781c0c80030840e0b400340b1112003400000b8000160003403e100c140c0f90881c02d000000018500a051002d8007406000900c426072034046d40c111001000c0103000001020514140540404241401505c102d420924407621440040c2d1048503e4000351105000820194090001040005108200b40203080003010041030b51101c101e100c01e03c2c403880c91404801c1c200c140840541c25981309400041c0880e52440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 447831870 1250 447830620 447830623
    0x20a020a06020f160507051e0915010905031b030601061e030c03060510031b0509100c020f0409050a030201060b030c041415030a020d0614100f0306050604120b07080603 74
    0x4510354020001680b80d00c125040b03480240f15080103560301500c402a11004c1210206100c000c8510840740c6140100881c00c0313400c40e092104650301d03404035102d00090780701d045c101c048606610042c5001c00d88161600b020238505200050314075168403221182404a01c1d041207601d0240a00b03151500c0d004541d0b0490340720000e00d0000312800d068882580b2008944682d00250003003000801006035078008001c00741c000c0200e9843d40c0414040014110400390054007158910324010744454044025150200c880005401080f640305020070886015640eaa005e20b201482c040c401a146001f00d500d0040d003100e00c6a8405c4c03000003c24010400e203003460310195004c9030221401c00c045964500009183e515800030411600c41d000b0060040340000c5a01070300300340000c20303410885162a5081d8038802c42e0b210400e0741d403044444100d004001d1048601080050960402041843e241c1c2d000035035980064000030310401100747c1c42c1d801c1c0542164015000340441c240200301d0b080074800300703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 447833120 1250 447831870 447831883
    0x5060408030c1204080306040b0a030302032712072115050c09030604060b010e09100b13090c0e0117090714060c01061205251809060c02150901020a02 66
    0xe800e085000c8001020340000c5802c0f290112400340c60800079141c589080360301d582003a548280501d10788581c1c8503060506551080c1901e405400a609160100c205c6605010000541d804200c0c02c0044200789600d410030fa401016482c07401504d4100c0c02c250901e0b405141c00381209101e010011224804504180b4035105842d1520402103010758a45407103102a01c10484495018840c41c0200008c0c04130690002c0700300321b030981e610001180248100814002d055440284070518a441008940700940042141c0d041c12480644107a0361440c1280848400d03440000220b01300d10741d02001907078002c400443c2108041c18a01c12404d01c11031150f5a841980511201002c490941e141140d0301c03607060b1103c4015200c024040300e900d4460040220048a400720750703a118100c82540001c80140300c0803950000c11000c0340e8854980710a0640000380c1c5802710030141c1d40c4010b40c40101d21280140440910650000c11071004008000384e5446802001002e00da48180310032490740ba40403940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 447834370 1250 447833120 447833123
    0x1180201180b030a2a08040b07020d1713020a0806010e0705180f03072601050703050903030a0504170c0303101e0303230c071508060a0605070303090b0a0e0c0409050604 74
    0x10780854420a8040380b801d64401c0800755802d64180414a00e61006d042403185102e506964015250154166035a48440350903001003002d480a4500424500403800c0e48101408540c401e140c569401040036001c040d0030020310ba80109005104074510000d041c2e0700441d2515106140c04140901031010b4105001c0c01446035101c0140150543e80c00c00052000e000d101e0507103d050100070781d021000b000401c4000c501075007000c000034000c5000c0c0c230410b84503d00880c06149180d403152098801440300600c21504001401e0b0110450110580a45081c0a000e8011079a900b0f058998421318211a84102c800400c2d88500d80a0b0364440c0c4107020440307905042c15a1209146040700310040500c011007003000398040b60b1079494441c001148421119445c0c1c03000018229a003040360910011a41030b41c00c18401003003040940e2043d002809554064079000500090b00d560303004801100b900c6512600d0f4817000c00710701c440d409004144c44400c0484041008846a9035100e82b200e400a00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 447835620 1250 447834370 447834391
    0x20d080c1c12230901090204050105030111040b0a0314310203030417010207140718020711010e0f03070f051201141f0b0408100f0506030a02040510050301180201180b03 74
    0x300f281044440001c1580d6aa05030030040707041c0c80c14a10850080651807401c2c1d108500f06000058103090601c1071a0400070403070445490203040c6012007000341d01400c002000c1640e1081c0c0440801110200540544440529801110804510803c80f80c1d9100104641c2029145101c1e00503500001280d048469404010f40744550003108640207000d6458058034404200508008252010075140c00b5110f1040308044080c40402c8108124029035000801d400ca035203049490940c0680c0c107000c050b590090180802810303c0340404d04007102c44d40b260755116424242807200f0710704050300303d0690884400030013804000008010000c80054102a040c1e42c101c0020100f05018459810251094001a6a4603a81d421182e80e0740c0c036080c075954020b5460400c080c5012207090040600400000f030045c13041c43c000f502044010003000d4902c01e11030180032000a0b01e502c00b8083c91425107103001807800e40d0802e82c0005021096844200801004551000c2c0107040304901901e030014500700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 447836870 1250 447835620 447835631
    0x1b0c11010c05030d0509010606050a021b0f220c020a0305070b040218040507080c0a062c0307090501090b091605030601121a01110607050403030c02030a020d080c1c12 73
    0x40103880106200300c000c2c100c3e020008118441c0c0312260031903070003508600000c1110700c1e41e0b4030703040b2414020000420300580020080f13200e15000e141e9090703200075006022141c0b80c120000003031569194a0b0241c810607004c0b00c0c4441c5829201e00c2120f00b190a180041d1404039901e9a0080c002e00c6010001000224640c000c58203544907a51100361703420428500355140c1c181410b00590302e44a03449403510078800c100300c0721414141070038501c08441c21521504291a0155a1801040114001c00401c1d0000000010165030304000300001000b00c80000a01941854066030a0381d206a0240d40152401403d00c000d180d40c021440b6182160303442d20700d4484d295200125202e14040c0d0100f40101e0801c1201800b00c00e0283c92004460800d1b00d072000a5101600d0050b12400d08440c41c501046e014042003000c00e000d182a43c801920041c20f44540710b80ca980060150a4002004e07181910080740c100e414000c00c004107841818624502102208041d90003000b84c0c3d846d000d81208980c4a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 447838120 1250 447836870 447836903
    0x1050322140a080c1b011e02160f03021e0f0d0302010e07151e1209030c0b070302031906050603010306091514160806030a02060a141305041b0c 63
    0x407100103204494030001d44501c5049810601410307005001a5001d42c041c2054080c0400f034011211481e600040c5c6460740c0600480050f02800c445151481e82503009501c0a14500f410541e0460b021382100c80c01e654607582140140a105480502024030600309200179030910364928403040361020040780c140740f6002951908a0151a0510740300c40765114030b180104035090008800003040b82e86984141c038902105c01210343e1016200c803004003086070401d050104140c00d07000a42464042d041c40c8294407699a541480802c04031441c500007036020040c80401e841141c0c042020200540060000c00c0c00c00c00081c1243c4410f202c010542640c8505807020005004400811412000300402440e0701d803640b01d0f0741040c42203a640400e03020003d0300300f50680c090f000305406400080c0041850b40d1003a03007441000d0307220442c05070a00003005228a800c401040040500b2044040c1d05a0928a841c1c1804240c4216281c010f080e4080304003103070a40c5d82d2000c0c005038a55000410300e6080380c0e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 447839370 1250 447838120 447838133
    0x20d05040f0b0c15010906031203050f04020411090a0b0414031225060f05040213090506010512120c030705010609020c0c04111b01050f1003030c080a030f02031303020c01050322 78
    0x44d101d120904c0d01c003030000a60802a90b01c484100d90142d403105075244450041102207031001c03221303444115003100204d001360030994010340d40c28231046030705403401c03daa00000d019010302d98080f10f520707100081c06200d1001d50380d07814040f1040a8006000b100d021300d000101070f008085110400b186045070000664910304064820980c005c0b1040000d2840c940604014200c01c90741a4001c205881201d0429040c41c415001c2c0a1341240291003581d00b00010040b000041c103c0341c0300e0a104042c1040c036543c1c2440010700c0c03c0300c8104002c41e6168080e26010703003910526409051058410710080d560024007042c1c0202c1014100e40000b4018904282c1240c1e50081140075400800c03d028400700c0620154001805950030400c0c0c55a55600e20100520100c058007000f40040d6025400c080082c0e101c40103400e80d01d0f01d07401e01186e2503009011300d0003240c00c1150040c1d100890748125006264052000403c00780080c45c0c0549149020031400d20242050701c0e4501b040107030408a04e042c840c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 447840620 1250 447839370 447839383
    0x30d120906060315141905130503040816050607030801090f112106150702062d04031a0f010b090d050304030b090601080d1d030c0a0303020d020d05040f0b0c 69
    0x1400700080001c65200d09044041c90501007450500a00d45a000f00508000e41c4000384101d810005100e1009040ca4060001e8600648030341d0140c8070310503400d00041c00510140c4041d111060040c048100c0380c0b248004105400d40c0040d00440c01045002d0210343e000603c01c1c1507036034003074000c9800202c1c040700d5030003099005411200100080340c600c5112080c2220100f82400c0700030310100a4680c80104844d40c990542022940d940c01c0054000500300400030385800529520114607845850401224641c2460345c09070403040005400d008112035000300b400083d00804d0f00c0060303031420f030303a40140108060103200048400410100d040b5a1026060881c1c1036100d000d50392100d549150909543e2401d840c00d40d43c0c0d000e100d001180080c000100c44171006002d41c0c4413080b40c2c0c01941c181c601510b0441a154140c025000c0d0103070b140e200c1c110184c000754800e50082080b02190b5500904240300703041c0c0300b000c0102c1000200601400140140c085d10510782041d907903920078214a40c54042d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 447841726 1106 447840620 447840623
    0x1b0308072a1112030703050301031709180c2101080708121c14090607090906050f2818050a0b21030d09050609010606020705030d1209 59
    0x24000441c4a0b48a90081c14011101c40804080e0781980d12010069003c40c0000004204004002c003000c01c1c207040940e0520f0401c030b482c3c40000c06200070710b40500c1005100502144218204800b1140d24907180c40c0d0403030b241c1c50011039600908000740b24246880c002d42100040a2101081c40d4140c1c140d00c0ca9010f203880c00031500c1515000004000c280a140c0c3c075010b00c0554480150441e0094203240020300c0145403400004005000715040f034800e0a0602d5800c2055032203018241240b0070040b40e0354003400102d0303c0900c03140702c1400e458200c1603000c0d5070005500a4090150f20128000d41401e0107140d452017a0700082d00e0701c08001e5608111780c003200103005101456030301e0142c1080401e40c1d180100000e10101075075030043d010b40d540d8116105000c41c0a4091180a000704402c1c00980102850031000a032034007000001039042c80462010101e9a0020382e01082015 = true := by decide +kernel

theorem cover : BRFrame.Cov 447661870 447841726 := by
  have h0 := BRFrame.cov_init 447661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 447661870 ≤ n) (h2 : n < 447841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
