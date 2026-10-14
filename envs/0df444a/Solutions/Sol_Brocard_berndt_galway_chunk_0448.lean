-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0448
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:51:56.501249+00:00
-- url     : https://prove2.me/submissions/c2c00c07-8136-4d44-975b-35bc9acbd971

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 80395685 ≤ n < 80575541 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 80396935 1250 80395685 80395687
    0x111011118060f04030f0209070c15051009020d020c06060d0b0f040303060503010c030f1a01050d020307090f0806060901090614010c061e090b01050103060e01090504031b0302010b130605011202 85
    0x280540e1903880c00c50700141c2000d0a01030301d40b1341d81d14280d400d86c0510703803040380104880300108240f00c5c058100850125442081c8032615002c0034416402010700500301540801044000a9944400e10090103001c81c03c50f009aaa10b42c810451480d00c24040d044c1030151203400054408220140342d01d54000b00d1221140c8007540350350400300e010780020340010350b055103004d510000558240d840808000f21081061200c94681180400c10040340d01c07a140c00b080c400c10202c81242e681ea80115444011410709540b20354a81701d8a180c0200a03030003240540c0c0c0000144a0b039440c0070b030402c230700400000c4001d1200a04111018000034209103047d414014095031600c00c0101c2070308075060888000c0e07450000800f00c1e01d5114081c0c50000d038192500c002d610001300c2d60354464061541660201401140941d2a1540c044000c02008009400704001c5159180340c8090500d0f81c2041c01d8020b60000c180395030400100440884410b074002e001c540381c00c0c0100200e980282d48002e84072001c90b401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 80398185 1250 80396935 80396977
    0x303050703090b0a0c05070e0712090606030b0c030a0b0301090f14071a04170a0201020a030f050c030301030b01240801061b0f0503121014060a0210110901110111 71
    0x80c0da00c03504030b8003c1c003401040814155029a402078a5243d02c90103141100e050750342d502680c045580d030a584180015038040900400d6800c0744e04003a10580c4507030740003e002592519400d0b001c07081920360440c07040d0000180311000c1d00f0b0b030107100d06d20703a403c60007007120340c00075030391188210000c683c0100702184031003c95a506405001c440b00420012410b03000c02e05449211305420b0b80140681c0e00403000b11080c440c00301d0b1001038080942e0398180c0007402d40303000740e07201511034000c0480d6550800108104a0a03500000d0000c0c50080d8032400380d50200c5c1d410300a040c100d016104c4400c80140c07184141020036550700440350340c111070441c00d2554115910089528100003c554040d200090001e51401001400002010910881000b100e071a444503e4080c0b96986548124140703070380c81002054403442e041d0002c01000d00d880c0101e502c48078401c000711065410b48049900014004203e202c095600320b1881801102d200300200115200c0410614042c01184000034000350f4203818 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 80399435 1250 80398185 80398187
    0x1120303020d1104090f091e0512070305070201030b0111150a090c080a0c17030a0e0f13060305061303050d1107021c030314150f0102100606050c0d0203040503070303050703 76
    0x1203426600d4100c40038042d43c80c2d60210400b20b80e005100d40490145041e40f80100c480791403060400d00e45e4811080c00031502c1c00420000c602d142004192094011010098082c4266100410980d0710175141c403901e039049400058104c0d40c00c0f584d8517040c4540a101d071400c40c1004107100c0440d0000798028045502d41114100040c40060b80080180b1400322011805c100001211241c0a114030084458242c450311061003111000201001e02e900034085000d050b8025206442450400f0303084052582496001404078170012520b00c00300307603950780148180f00c2d05000b030551155021090b10100c1d0002e0750010700380d100d0154000700281d9543c800310084030007041198403e680003030403903000d284100c1211043e00a1442c0441c04680341080c3c141900d000c3c042c2c0503200f82121454006058190303018002c007000c404221074110b000d0400f5075860b0f03014034441c0718054009035540035101c1c02032804852410041440700c00a5600a120411184d0f400164003c00d490380351500a880310701a00d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 80400685 1250 80399435 80399437
    0x5030f090c0a0902180103061511150406020a090b1809060303070f0803150102011a0603100f09020408060c030f01050111150c1c11040b210106020105040c06080108060112030302 78
    0x1e0702561046514038000b41c0369000740c01503c3c0c041c407034000340910841c1d880c00540440b681c600c1500642d0100c41000b00449000b03100801c0c03220081025684281d08690f11154003503400c442c1101c844d6408110b207641c0641c420711503000b4120386240c0301d00d0100070034600300444800400c298442c1048900181154800340240c0b1003a603840a4a00c02511103490b00030041d41046840340c1c0d1074003003030418030741540c0b050082042200c074150885902244802c144000e1758802400030256a05889001840800800c3c1250081104900041c2c82e141000500b034100343c0c0140140035900024402d100c061190003d5990455209003403803404c69010040c03040c10800380c1580c0e054080301a60030800008000c1c40201008103407030303d040c02d414103c1085001120b840d640189805201070106000100055000300801012506116290713100300d00340c08140307a0709802c0480140d440e0400d0008001441034104081e0000f0b061a60a44d030515004698951701442110307007080e0034031416418940a0340c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 80401935 1250 80400685 80400703
    0xa020903010212070c12080f0a0b06070c09050601020d1701090209010c06050103030801030b06030303040507060f0909020708130509010305060403050a050d05090a1401020f0304110a0807030606081002030705030f09 94
    0x80f140040d0340b500314005851200080416520050302403015452544030b20420381c420146800464401e484090320312006060382c900c0b040d0860b81c00c0142001051491003688010b005840012036186880000282000e465041590501a442c12080d44018200c40f0341c5054820744180103032600360200c01250015240500609040d25001c000b200b415403000c4628140e03030154440070320700c1e100c20003819580e03c8102e030b0203421900b1050090000e68480d010461100030f0301d203051440291a90303139110407680209002c030382d00030000440140c5240c0150042c402010111254045980f55465140c4c4070700b8000c0000f010000b00081c950303803c0307002d0020340e40f000b120500c04004920300401e01540d03442c034220041e12501c075407010100302c003801402101c1b2180c2001c81014110f40b0385a031200403150701e428450364041d0350000c004c201d58504000c4000110b001e41c80100c2c03128a40342e45141000c0c0300d80d0f0035201c3ca500410401034816044011242c0040e000c030004e00d240d40e202c1c00068241041c00f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 80403185 1250 80401935 80401957
    0x80711060f0a020111070b04020f06041503150611070605030a0207060914060f010501020a020105070f050f0d090803192601090f1b0c0320010c030e010506040b090a0209030102 77
    0x101d4a01101400e1201070500a481078000704800b040e00c0319031503054022560b0050504d02e003c0b0015006003444001015416030140003603060580301c007500c03c80210218020b20000b035030750144141580c8000b03078080051070f480c1080d295128640440e2038880f1124003daa041c05000804a44107500a074103c404060300404100034010340d503c0c20308a140300241321a10244070b400d0100e103002c480700c0b98a9040b220142c00518a103c060350041d5002d8203d084199149603c042001c8040b43c024000c190640003200064101c0c07107004840503158440c82d40120307a01d5401409804000c0b403c89507051420801404c124186100700390400504450818038888120007130300001030300c0d143c6034000002102c40c203070050156491942c00c4c1103141900e58145800200444603003c0840d0180301c004426004a000303510500b01107030101801d50705490b602d40e00180c1c1c1d0f180d2071980c849080c07250b150070000c1180c06100e14052080050201000038080c01c501e1540007a12020542d02503044824110034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 80404435 1250 80403185 80403187
    0x50a0f0e10170a05010f0501030b03030c010c0206010519180905010912020d032301140303070515040c09050609160903021905190803070308060111060f010807061b08071106 76
    0x44050300400e082070782c81c034120315840704a000c030700180f501d4043c0301e040c0c565048180b25068544001100506141c404107074040c04100051304446c4028001c03c1e440c61115002051107502d06410b107c0c880c84512a0840d100d101c0741c0050100701540500b1060b201d49808012883e20042e003486030040c01c032020010581112035211100b840d4000c5091041b2507002d8030100f0104148145242d014015030b80d031000c404603070030b0061284903a202c0d03170850000c002508890511240c0e641c1e603407620020814003182d450844041004002512801070060844028180054145030011412080020300924800070101810032405403060b140da80c02580c00420102e80d41030340d050031844401c06400340740d01a810070a40740c502c08000640c150100c03445000150324000e8507441c12034031041c000d424941008610041c1e00c90100c000c0142c5400317122680015803165140480c040d01e011043c0c1d02c20300911041c9102e0003010034009524a0320a46c000507029034440c0f42d40f401a600080f0003924541c080c030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 80405685 1250 80404435 80404459
    0x207050d170703080603010608030c060619030b10030b150d030807180905040507050409030f0c0c0b0a120c030e030901050708090a03080a090803040e010b0c150c12060d0201050a0f0e 80
    0x5800084d0700e004a00980c000c000d0940c8500c14184c0b28410a11098640e92108000c01c01d00c2c2031502c8401807000311311101d03020180c1c0302c0d640e440340c00000b1744c2d080341854140e400510921401e850030a4120030600740c0c1c4d81e1441016004034141d050700d944003505200001002510700e80c0180500d640300602c403201000b1140d1a2520302006240c2a101a0b40c541700b80c80c0041024206807103507007100b0350182c84107204442c4c20f080c115840415042c040b03411141000000900c130440002415403100291140c500078013a941052007101c814010b107900309414405030901c1e01d2400300c200c0308076800c00c0c030701030360740f10303d40d0414155074802c6a00c01600440b151500206010150002d840c007003005a9418500c583d0341c000140d640d016901508242c1d62500004100140301c5100504502110700183c401084080643d0302e401003080784c0c541d52031607001401e070411b0402e030b03000035502140c21564100d01010540000708039000d036000c0c0c101401061000c0034403050107004c4001d060000103044400000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 80406935 1250 80405685 80405687
    0x40623040209192d020a02120307030b060301030303050406050619120606050a082514040e0c0a06081f080c01030203090f100903080703020306030a12140f0309060906070207050d170703 81
    0x7128880e14a500140d01381039054840829008903000414590f00410200201c0c0440102c154809404c4c1c04c1459900c0c4c0c1c103181076440e55000ba500941c003c1e10001640d140c9420000141c41c4001d005912844103092817080d941400c05504007a03400081c0d0441c080d000c5c030324100700100f146420840d8000f140c05400124094001480000c403040301480000e030001c1340c0405015140b140c0113584001d84103c92400c4242080d80c40901804044811a0719a40071940800c128403129002800000c0780342c01007184402c02c10040b10f8950780c03e8071000305014a803519164039040c08080a070b0406070000080380d1000030400a000508607204240c03084000b06604840c0140500103080300030bd9080c0c0700082c0205c0c041d200341d0340308840240241021800c01c0ea5a004110710b40d00d10407041c04102042a0340041400001c0c15480203029090317039070303402d000480502c1d0082c010a00c601da9030042040111655010036290112803040d102c91010814524149410f07100070040b0004051000c1020400c2c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 80408185 1250 80406935 80406971
    0x2090d06140103020f03030301030c05010e040920041b050405040506030c0306010b0703030b0108040519081b1f020418050702010f02030a050f060a0b120907090e0604062304020919 79
    0x892003100c03004c0e90045d090f4103142e00da0000748000361078400d4a036401c2005501a090800c0d205c03200600004030814107039900c001e40303c00030b13403c1180600b0151904083d41818801c1400001038403225160004229000414134443c0e03001d118055501c4c0c801141b141c0d01c00300107403110040002e050320340319a10b500d286c800542000e001540001c1c1040f0310708640d540100482ca0183d5000700203030142d1074803175a002420100a100c01c40c0c5d04041004682c80750a03201c1480268426140090b0282050880049c0b1400081208134400e4610400042026111003c1d00c8840e48085500101301c039600c01d6016401060340f500d40c00001d500000402072919a164040c034803840301c45055000d1038580350700340840b03003c442c0a04140c8440411415a01c1440401c0141e8840d030031004441d11030780c580104d4002e8480c40440c1d450194004810702c010400e00d40280c505c0980f2150903040b00902c00326418a030402c000d00301070b000c0c040e000081046410b400d8407d03201045403e10a000e40811030802e000c032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 80409435 1250 80408185 80408189
    0x10608011b080114010c03030c0905030f0a0201030608060c0403021003060e04080c060906060102061306090515040c170a11012303010602011a1e191d0105061c02090d061401 76
    0x40310040003040b15000000480c804c090180d49014a6104941d13040e001000c0d410f07086070503c2503000000980b07507810030030000401c0c480c802038a2815420700c00941900c140da00048002d4020000708410170305040e059904880d0110f410078078200400c2d90a500501c419042204035090301e004100c14485203200801700c0758548001c03101995180c5c030541e51112000d4581a005801c80004942041000000302c01c200d8052000010f5054444d5140c92900000c00c1280c80b1035800c0a04101c140031035500c0e12001000340814284500d07607800b00058480c0103030400100712141944031504940d10484d0981144401004a40d54900186148201d15003003481400d0041d82010403030503c50708003070034030000e120b409071095600c00c07051500d01008003402541c403508000c4901080300c8041c880d01103440201400c4000841d03100780b0042102ea02c05058008500901742088050002159560001070040c40c82c1001601e40c068280021112000201c024000300d00380034024003140c006c2d000140c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 80410685 1250 80409435 80409437
    0xc1903200613080615040507020a0204020d0b030105040b0a060608090a120e04021c0c180509040f050604080403300f02010f020a0e03060601080f0c0f0702060d0b010f030e1e010608011b 81
    0x110569445c0403c4165001124183c006070000c007a61001401c2c2303500582248141e419000ca652035800c0046030859030111015160415000140407450246229580241020b8601400d03c0d00d0456001036a03030203000001003d00100340400c102e410322580100c110103100074420b660780c05025140610001850155010040c034003251010740c5030140102c80ca00d0003190046202315842d11041080110004000703072900b1114a0003507000400900c22180b040b4420000326494134194104004960241c1c0502d800f4940f00404041007802040c92254022a4919046000b502009800c9000d80340418002c1e901600205810000d190400d80c4048010401d40c200c030850760301c0500440b8009001e5881c41041e19980004ca020703540f0010040440150f0180d90520380241c55001c1441c03035004140240d54680ea54108105a41e4002c0e100c06800020345018816024000107403501c40300760890b02080c101c44892091816142034201d000240001070023002021f98100d071280e40e8a050010080c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 80411935 1250 80410685 80410711
    0x609040519050708070219050307060212040605010506040e04080309010e0304080703060506030303040c050603070e19091a01050d18140102091003060303020c090a02120103050c19032006130806 85
    0x10744043c80390b10200e10409080d0300900305660501102c454681f2000740036a000d000810100021482c2400144602c84d00c020079030000b0314050601e01d08840c410b030041449040208400c02000001d5900e480e001900413622640d41d07215030040700e0040911407a2044c032408080350024041e400030400e0000c40c1d0250400340141e50300c3c02c0405403648802c07030700100410b41800003841281030072030185622240310300744004450712000c0054100c40c1840c0034080b500b55104400d1105206c940506c0c2e0800d055a80200d901e02400c0001034024001c158240640d155120501d07140030341c2600351080030b99000a84580e10042d0f145035103010398000c24507580500ea022200e109818404d20981080301d826501402c054042d400c02c2002c14500a044501d5290b0240820501d858120740203d0085100e0700007040300c64400000d0000d40324910a06565900c2450001c0000c14040302c45c240c03c807200075030304070860906280020034034042d082c5c0c605090307804001c0114448800081590085c0c010700c01003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 80413185 1250 80411935 80411941
    0x604060f0e07050303030403180b040f090b1c0209070905040218090108211308031b060c0c06010b0a0c0f0308092e0506040209030d0306050a050301050408040308030402060904051905 80
    0x110365142c900c1c0c45020b801d40d200b04009001710741b02e1503800310341d0043c002c3c800000940e81e03010109a0781207900a100c5894031f07110100443d40007441402c89100e41540d80d08180c00303515054a403510482c4001034020300d8010b000400341c9115800c0361024241c000c00454461082c10a015174800300b0039000ca000700613117030000c030300090700107030f03c5091080406401d0041c040d110141241e80d082150b00800c40d040710600800d40002c14005440b030850340c01e448968198900980b03d2800710b01038000c0b0391544040000c03201141c1c0200340d031815210100016651450000b100319608020791030081c218001075902c5800b0035a01c0883e85009010f40c04c02c40d40d040d0307242580344843c1520f9404941c0c1292014526400b8452260421a03000c1c2000f00014103040e00400400e017041205400e04000942d940c030709120502e0103607132600c00b900040d00200118609a030390300c0c103944901c1c08094401000400010115a00c00c8103c400d000390190081c051420150710000249206d107000190550601c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 80414435 1250 80413185 80413211
    0x6040f030b150102190807020a0b030108011a010f0207030f0f022e0512130c09050c0a08150607021c1b0503010b09040512070303020403060c08061c03050703031d0604060f 75
    0x480c2001c200318414101c900c00070303986c2d0400f80e944400e000700d0300b00d41c01d8000050351080c4400558001d10780c0c4c4002240d0032030009000300c01c071003085c1400c50500601d802c45810f003079400145241503d034840241202c222550a002c01154006040213606c0b00c109544000820361a90010880700a40c03078201e05c50101180c003c2d58540118040315400c011f14500107450b8203c0440420042030040105290454440742c02d54182e0b40c0469410012185c00100709a0b191391103602607511050003d00f11511b00b03041d1000420900c2032800203841a80544000fa2407600d080b404890556440807090072861082c0000c00c0380b04d0090704c1018032a51900d03000d4a9a03040485800c0d2040b41d0003005060b00c4485040c030598290001502502007590078403000c40064003e101d400520482905c0d078400c039107807036410050030b0450f00354000030443d4104405c400081d00401034603801581401c000c91044851081c100c980c000c100844801440740105001c180481580305003120a02014288030303010528107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 80415685 1250 80414435 80414443
    0x3150f0e0705090d020d030509030f0106150816050c030d020409050106030f140a020307030f1a030c060406170402010c120309140304050a0b0d14041515080c0f06040f030b150102 78
    0x83c43d00140d9101440c0011704d004200b0001c543d21074208141440703100300100e40f81480e0544044101da64501040c05549007206201303881c00d2503440e10444030702d44810b0740414011103640d19000d003c008501203207015818000d8402060b642001107469903070710203074100540400c0c420380010130b00d8140108050031082c014400310001040005441e5140c03103580400070340c0028030306010182e032080801d1403d84036004150030002070044066826103484201800c10702160000c030310540e02004208642600072440007120280c440c5105013035030301c074001615030114032480107007081141e02d00117400f160554000b40300c0900603001742442c00342c480c0c8034a40e80c0c4076901503140e0001a01c0d07020494203400600a000d405103024020034040300c0c1342c0107032100d850b05407021901a40080d80b1450354060700e00c5940051900700c1c20141149141406040e03e96403040640380c069040c0602480740e54448008560061420000c50202c40f6505cdc18010300300c05043c0c2f083c8018440c00ea0110031950710001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 80416935 1250 80415685 80415697
    0x190507030c050922060b120106020309130c05040b0d14010801020c0c04090f0f0b07021009110906010306030c06020726060106120b0d060e0105240d0303150f0e0705 72
    0x1031291881c2c48003c0c0100700e8402c441904510700c0c08011892841e0f1042107004000052001c442c8050700c0e8008a1900100580140c00c500d04662007440100815503071031100c082d0031204004000f45204605004642c00d100e13640101da10064005010480d003100c0343d0000814110b0b02c10ba040e45030342c840b9070044c00d0b4842d025200800d0340c403101d02e402140c0303410340c005039400340301e10201c0e0400c000c1c0d65070b0f40280ca801c43c4010791b4056070000400103c1501800a02e07455403003c241046803148940e175441007000b460500c2401003071181c000a0036070f4007980c07182000c1c61f001031583d40c00640c0c8280007035480c22a8007681001071003030895801c1c108000d1541000f102035200182660342e080801c121a552901005142c1c90f03900c521501c415a1140381103503090318080d4902064058011626500b03541c4090b00700015610304070040100c506a8070309007a09060704907142e2800450600303003100031302404c0d050040d4943e0281000240084032003046021200311419603500d03a603511070144c1c0d40b80104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 80418185 1250 80416935 80416937
    0x10f0906020607030b030a050a0f0302060109050c04030605090a0b09071508011805040302070b0f091203090a0e0a0609050c0307090806131205040819060b122d06190507030c 76
    0x1002c00f04a0300c60180c0c1120070404000f83c100c0346441c003075844051030800340e048141d558004100e420000d06a0600c0001d003d8611004207001a040c00000a692803249100180110740c2d500042514100309000003c420394001c03021992600f008103e2544031007e81c4100c500650080581401c00c0b801614418100c0c0c4000d0945c82050344096044009028004c00c11011405490310229810900d04d02070101d1400c104003450326240d0010034001c3c1d00d181d0300d1003c0460b500c00d000da101c8940d81c0d0030380e40041d1442c0400100040c0c45501607400640141d80190303404a01b81410810704c28a0032014522406060783e409030403903030310312400b51150800e540741031701d0301029100c50000c110b0040312600000201e1504901d401d9071180715070f050010010780c1a14104402100304144800d9014030600d02408454400b6802440c80707506950b540c54100302e9644060070702e942254a2048030040310003402240076202d080c9400d030850811843c048811031a21840c0c03202080c030240c8680328000e00743c1c1032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 80419435 1250 80418185 80418193
    0x30c040e06011a040302100905010e0a0302060a030b0109170123090d0c0302100f020903010605030102040b0417030c010e0d170f0a0203090715020109030e0f0105030105060310030b0c0306010f090602 87
    0x7003a10b40da10103030b1442000f01038400100b00001c0180c13154818101101041c0e40c0341d50345c441c01d0400042600721000d001f0b42c030070070801000f0700150f07458104880c050255401e00064040329040140c440104c0390344031903074a4082c08035411540d2419000401c5803190703079141108980101c80003e000010030344001c03950740d01128030a40760781e020300071400826000340101c40480d104440002c0540b280d9008a5120a80120301600c080c1030074059007010308011002982840e051145000a038011403040132034a0000005000c0001e0081c01205d0a02d520b072002403003003010203003034141d4070390790841d0410020740d015031002c589070004072080d406070b00d4041c07002c80d00e52100002400070303400c060841c410030300800c04002400ba409821990348401c6a4001050200b040d04028003204400c040e240d000d9282c0381d124000a0f80c0c064101c0e41901c400715146138507621008400342e10424250030040007076090b5024080348400c4007010b03512a107005d80c2d441d1001e041d6510100c0d2007092501c64a00980c0c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 80420685 1250 80419435 80419439
    0x40902090312070b0105060315210606040908030a02070309032a09020901080103024c02060105060301050103110c0d0518030307020d1203150306060311060f0403030f030207020904060605030c040e0601 88
    0x90004010b41e0003862190a61000d849000002042c4250307900101104850ad0100345901450601c4401c0e40100300322003c04c1104100c0d01c50717821901c070042c00200005e50000c0d0134000c240c018001c400c00f43da0406c5050104400c000030034440c80305c6108801c03c5038041744070002040c1c0618002c4580d0200184d4503c600d9910399428014468220001040c840c21008a040200c072461b80408503020144082b000080e081c4680300f10301c0504240000e421504000014026600c4050840741115401c2ca800128001c0c02c41000f091401603c444032100d004461880e0080ca60003800303010007180302d42d92035164491002c00c06a82c0d22071048000c0d008007610510101050700c0d121000001509401d001c503e0a5080108010510722600700b21b42c50340e5240010310074001134803202074080000b03607010303407504805000e00003460040d0304c001002c01101f0256508010b2003901501d0a25030702402c2d1000c03606041c07400030050000e030301900b800707803181d080b00c41d482d450b2501a580f6052104406400b550f4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 80421935 1250 80420685 80420689
    0xb0a120b041a040302100c1b110301020c03040b090a05090103120c020a0b040306020d05010e010b0d05070207050607030e011103030c0906091212071e0b01150311040902090312070b0105 81
    0x2a000800a03200088012a100815840802d440b44190310a90240c1682c0c40f40180310401c0f107112109900800416085140d4462880010319500710f0304a000e2910064400002071301a1181d02921400c0d4007010500280b07600600703002d040981c0341110170700482e9031581c0510083e0700003444040c03c5086100040c81d85180141480d10f4082d00181100f2156521020f2040f8140c0c055442111480e074000351f1400140c00c1c1e44107a50160805026a04540d45007001d2000c09004501c034420b45103a130345021442c018001c00039400184006082551900c20a08028001c00b40041140b8086541c9900c003641c101004802c0301d2250700d90358555410120313070b501032008541150011940040b101c3c101d084e5070460411219881c0d910400380740c3e9490754a40340003540140812410017480405d404200002201c68201c0b40c15544200380340031009c02d1440c0110060101c00f28006061040018007242c0300c0e050ba00240340c07030038055040703035092101ca00c00484c040c4280074025182c0d0301c0b0800140154 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 80423185 1250 80421935 80421953
    0x4120b1b031801110415031103090706050c0102090a17150601050406051c14010518160e03010b0904050303070311091810091103011404020a0225080f010b040b0a12 72
    0xc6160000004080500e401131130419030164202180b158401d401c0c543c41ea641c90300405800b828440c100320b046d03043c200c4c2115610016030285000f481408200c118504000b541500e174175010040c5403c0c82c9644c1d8802005005039045003c60140c010028004114178036500c54601524069603200d16151508004541c0e5800c410020850000c0b50154255820058022103130611040d010f0203a03503524000401ca15000900d0b40d01d003a50480e1400c000400580e520030503601e201d1400c0002c0398003210381c0040e00502d00c0500340ca900c114244140801d000300000a5446a0f0464404000d000102002c1035070324091007103003a5214031030060109030507640401281d048a2156081103651352191600b0701615417099940d00301d0000400104030000c401000782080b440192021031400e0b0b044800252180b4202c14010200104a0311150400300400002002400d004041d5a51006c4004c4031038041c0c201040344d54030440c201000300d485803410b24035030f40c120790740c1d080304002c91000c03507685450f1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 80424435 1250 80423185 80423221
    0x1401030506010e0927060c21010609090518190c050f031f140108030a0e010327020111010c0201050114010503090a0b0c0f070f03080f060a03060f09050304120b1b03 72
    0x40408111000e00c2413017401c02002e4000d94076112500c0d25000c0c400c03200d030424214848511405014100100140d6402040e02801e0300e448030310108079542e44d5440c2e42d4000a922498195a204101e490030340071150400394030b1814800e64075402065610810071000400d4408521f605421841550340e611054020034185030304800c20216005044181d001103c0c4400d03441003070b06030000285000c8146c0d12401191025030242420407006540b2402002c03050301e80303403107440c0740740c0f00030300d00340540e0f014200284807805604024010301d000048001c1c0600028802da403c02000c11081085560042040d02c0c0b103002c0c00002080c0749007954030b031a6040303540501443c52a4108101c0499170741c841c0c038020a1000e015030b003014207662162500500d42c840007020a61041c040c4000d11a4030343d110b2000d1800c590704148046052030040030100010404140000c189120003d0f0001d5407865864202001e079001c0c040c0303040c00d07645100c20701d01403044500782c8407040c40040001410b400240c6a032884 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 80425685 1250 80424435 80424481
    0xa090b0919061707050333090a06030c150f270f0303080907060e0d080906130503070611070509150306092512020d1406011401030506010e09 62
    0x1800082000ca05440c40c181e64010200007189091030198480e0380030b8980d50480c0d19842c0c5140b035442d25606000a4103441c103000c000403101814904104004003520510000700203003403011900300030084400429061104840020100d880001c2c0714010582e404d00f50a029150ba045100c15044219401c510385c1814910701659003460281701e058110300c500c040c040744107103181101c0c01c50030044e29401c1d000381442500d611140081c00003e134061601e90302d80d80306550300003181010340f40141990190502d05904203074003040400c4880d46c401e80c5801103400c250155420203440d000b048a54000680d0003035904c0c0d204042c20001d60821101e5a07510041075408241c0700c400001c0001d0426005650201059201c40d1007078030f9502c0e000410300c082d003d9160552101925010203042540c81610010f4480d407201806c1805010b030031800030914550a000346c0301c03a5a1120b43d5048468501540540000e2415000a45a5002d842042242040200340c444035039100d91040420760401007481c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 80426935 1250 80425685 80425699
    0x807120f0606030602070209061c060c021906091a07090b0306040f02031f0b0405150c0f0d050d0b090f04020405191805060a0903140703051308060612030a090b09 71
    0x40419140c2c0318030707009035100702e401591303e84c070a00400c032800d00043c0c000c91152940890f0384038101c0c502c2c4c0090170709075072186000c102801000ca00340e0078001e448201100c0c00300d00004003420000c0a61001b840c06120b000c4e203807071103029000d169869110440e0980045412488248000c2030188003550b0701c032000800c003180c0e01c42c0380804001039030400c0d550f6607500000384e1700f00c510281c2c120344030201400b50703017254904040c0380c000004d054030b00100038544c000100003590484864140801001c15924604403804544044001001988119204046649842d00520161402a4403980262003107616a5190b480d01d0b000c000041101a100c0101e0404a000d6211901028002c43d454140c1040c10900c010644e401e0a9050003030061000c580280391010120019403c00040ca0407055441c0305603494100b5880d00382d889224039003480707404500c4054001840c02c3c0006105100f804156002e5503250080c540b0241e0380e0294a003801c002c034603440018407500080402500c1500c00081c00c1c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 80428185 1250 80426935 80426963
    0x90d140712080702090105030102090102030f0d06030c0602071403011b031a1903021e281208030621030d020a09050612070815030a031101091202010515010201020301080712 76
    0x100c07821110a0400300d685038408200d4509525190480030b0050006030001e5103403103190700c0001c3d00c3e8450494120100640805d00582c810302540c05039010b1507202c9982040f150f03d8600c003075a100380741c1c81150070b50342070207103214400d060601816000d01041c08440f003900311004000d40103030802c0042d80140f101656017504941d40c80307500e0708088125203800300d03240c503045005002c180c4003018202d1204255001e5604800e468122821a40310300f20200e0414181411100742d003404982c0d070100c0154459189018144450000110301030034040b50301d0030f1104146201d94641c401e090b0305031025900180310f10028a41030b50000e19014159140404149480c0d4001620341c0d08850208018000701104000400b80c1060740713260011600c0c00701c407034009107400000741d4075842818001c0070001d44600304410840c003504525612a440389040401c0510703042d00038000d0400300e50400820040d82d006044650040c822281038503200c04c05006058201240c100040c0d0f80c440f401c46071131400c8080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 80429435 1250 80428185 80428199
    0x20102160309090e070e010e04051c02010c170f010611030d0212060901120809060f0705030c0606030709060e010504020a11060903040e0115080f0415090503031902090d1407 76
    0x14555003078400d0b264448203070700346162542129440006581103038032207203044c001d0101d507041107411a05120228480f41d0340b140ba00f2400c000104400000f000c1d804034a4880c8a6019001944001c8a40d070341c401c00b656540400c8810301030142d6110560803068801800510b00c5038000c8003030f40303049004903841c00c141080100101c1c0d10900d1420780091a010078404907107424103c1900401d02601280c0f2035443c02c0d101c4000c1c602c1381880f102d110304000102003086140040603110f01942000549840d03d00c83c00c2d12540f92042181c120341300b4007034103a022900708054481e007815520001e9a04825070b08040c248402544074400450500002d01424018403008000315032189090002840d00c6074500321580349080740680016080200e001002c010403940b250b0066800b8074101800c5c5d106856500b00b4a40700f241d5005e030420841c0c10101d445081c414000003c41c0608144482050300c0c120b1020003600320702406c2e2000e07900c0b2980d00051400700d0300030100d49800c0048002659005c0d41d0b02e400b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 80430685 1250 80429435 80429467
    0x1030210033222081206011b120801060f050403030c11030303070f0e0618040b01111009031e0f0503090708010501060c0210090614071b06021e0c0a05040507020102 72
    0xd0364240c2242100402002c1501101c0078003034509883c2c8607242e0b030007082d51094070f18000c0d0b9a0a60700c4130031290000d4100d0303100d01c070307041d0801c6810b9480c2c201010390307410a494403003032411101c2d000c0b825400000071880d12940412440c0b000a40d919400d0a0540d9002c4030410b880c40c10543d580441c14400e41c3c04c507902800214041d94440e240d01507d150615800703084150043c0086108a0090014078500c111180da01d0068890032180010820b1007400165002d1140841c3c0003118401c490030044c840c01c95502940702c10340a51100542d00300b0f00800e0040011523181080000b07070340300207034600c050b0081e40a107410940c0b1780d00b0b0b13404240d102c40744603085400903406032001801c5072400c1015070501401500d4211102d141041303400d82861000f600d03244211102d0f0204900c0003840c40c0078043c5150a491180030030401c0d8030301c8030b81d030707502c1c003c4d40d480c00046100c0f409031031510101035035400001c40e07000a1202801d1900803516102c1003100070305009041c1c90543d5000c010a04e88205002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 80431935 1250 80430685 80430761
    0x40e0607090602070b090105041403011514010e04020403053003070c03090b12071b02041803080f090c060304020d0b090703062004050d0c08070b03150105030103021003 74
    0x541c4645405251040c02864403039158000e00140030304020161499030b019007214207640d510500c80c1c5456034108046801001103038000001e2541e103640100d02c9006290607a9202c94099130740a00341d54000041000720b10407031000500301e51041000a800c00042078214400c0c22040d00c444c3d0015201120f418519881100c2c24000a1000c5a10404040d0010482030241401e0703e031050a0a52401e240b0111380310190981c41440034600449556401d80d140744030a050b4081c0c414030402480d0103101a00765480340301140440e401c08000b4245004100c113261041c3e400f400282141c0904030103011480c0d002420590f009840070401c0c0b40840e00114440e405550800c00034962246103040c000129100d000621880000440184907106502c03802d840c02da80c0202c0c3c9500d6006580c0c90500507242280e4041e18081c001d0483c006a400b180700d02940c440c60441070010b2a1040340340044406210900000f94002d400c0715250000781d00c268045a010780346010031044500290310841500d45601c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 80433185 1250 80431935 80431937
    0x161106070206040e0702011a0616020a080304030305030a0b0303071218030b0f0603151b0c01020d05010e07030e0a080d0f09060e03090111010b060316090e040303090b0609150d02040e0607 82
    0x4405d000020340c0c244244c0c81070245815200708038214141c0000c038184140c000000c0c1e102c0c20342e5200800d6580da4004403008001d408102c982d501d60368034018001d43c00440e4542d022528100103c2000e04000c0100d801c4154001407240e804070480409860303264000941d42d0324400030311004400602c000c01101e00070b110445921840b450031104040c541034628815080e045014010b0002540c884c030b05c40e00e00c0d0880351002c2900d4564003201d0070300a008a1624038941030a0400000340026142c000c0c902600c0650750901c803031081901115903410720b801004000010800002c59803803933036070002c81c9002d42041c0119182595031200020742c0c6034419400d6850b0400210841590b03081030303171101310501e400c00a008032102d4030001011808018000080076850114400426105080300d0001d0b000c0740001c4203050038541001001080c20f00402c840d411041004501c9520349802c00a115800d182e0790700384440703101e0040c1b180e034414016049170410745a100c075182c0d0401c1442014403645071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 80434435 1250 80433185 80433209
    0xc030a0908012009150c0141070e0121020a030605090603030307030513050d021c0503240d0203011a04050f04030c0f020f0d060c021216110607020604 66
    0x185211942181c941c003080748403c00703101450004040f5090162500000103d46440350180980032818441c41000101641c1c1e501c0c4c0750380c0c0350a440b001c9449056092107415800100c0400e203c412640c0c0301002c44541e0140140740005000f544100d011030240041858034840a10048000d085030081004500e10004d4002c5001000c00c2d500d4400c00e40200340c22100d00034241420030109480380f0000e02041d04240d100e10000c0d111441d02818103c400b50300c076044820800031214020f440e00d080712201d000b03585110866150561242c41544d000c0d0a00352400c0b2007c40c07001c0340102c0341c000e08200941e000030703140d007000c1d01580c0c003031155aa8411040010410b6546144c04010498600074449000003100e00c0a0001096103d840d12050642c840701e00e64a2004600000d41c504000681443d482524129481c00b0000903800c44042d079a5190201ca1005503c180380103035038000c11402d034407050150043c60f008030780c4200c075140181e0000b0702040d242c4103040e00440c0709540103030402609129 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 80435685 1250 80434435 80434439
    0x609330c052101090f091104020a0509030a030306060813020f09042303071208011d0a02270a090e12070602040504150312050a12020c010f020c07060806060403080a050a03020c030a09 80
    0x5441d010311140e10175205010070085059584520f1920781c01c00307085000790f501281c2465003600602c200c0c0c11a031401001c070b85100001d454000c000c0d09080c041c250000c1d52000c04122042840c025881d026980140100100d01c0c940d8244525028003c0041d1146040380e018514409908403205004c502550040e40c0c0d209032074200f0425001d1005003281c204100007004101024008505102820301c0311649a096161b0b00f104038080d003e002c190181d07032110a0420752080b18940300c1d807603105009480c005101981d03114604200d902003a160302a5410041c81021081114002024940d11840005040c16102c3c004541200c0c4808a90070340c94100c04024414002c181c01e1140c0e554500740b41c0180391203990040280910020603408203003d4011522840051080d080380207030741400c43e01191180144000b8981d1001d2a01c100d1020902d04030114a141c10100216810b50380c0002c40f4a103070195a19040320580d00003050341c0e04140d800e100b8421441022710040414075603668410040074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 80436935 1250 80435685 80435699
    0xa0e10020c0f06030f06090403050904050c0703081302060f0702210604170a090b0a12090809040e030405150304050a0b0903031005060c070501080a090602070609330c052101 76
    0x180048542c1c1c0308840a000308020320480030b42c010b40c0f051055507510100e4489281c150780d14000c210f1090360041c100b070708002d0340d00709080107024041e019580b10042d03a12961005038035405402c00c042d42008040103050741a900302d82c0244201407002c1c1a15144007401e05501c2c0c070101800141072580e80012052005010500d000c8a000307034480c038005841c1a28250000d840010030b8484c480c002000411080102401107000308845c0c0b065070b2080c000c0030030038503040c5104d0788004001d0748241e1402694210440c400426107068820180c80c07030300e40813440004a0a2900020403c440a03c2421003402c00690208546801104070400640c0c403403c1078905c0d11191117003904442e00400d010302402558020000c0c206d011030754282041240d54403140001c4010307148081c2c0c06050035000049400c1044075940c40301008500644c0c0d014808516009414010a02d403135540100c4070728410580e43c1c0310050350002e10001c036030381892490f11207142e035a810b4170b40045101c8104075540c180100144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 80438185 1250 80436935 80436949
    0x60b040603110307020c0d02130c08070915050412060e030c06060102010b0d0f020909030f0c030903072c07030902100809070608100e09070902130f0b04030c030303020a0e10020c 78
    0x1080001c40c2c014154640558001d659080c403980903880b85d01c070700142406644600d031001c40d05414148092046a90f04a8060a142015201e1800203032040000040b07403401c4055a00b2000702903070b10b03d0b15041c0340c2003a425001c110484251038885d900c509080300303e08104000d102903104071029011902d0420006400c6829111820380500800149d00380055496224885a1681114036000c940c8404c0c400c1c0b4954040e581d41400003c0000400c0c07020400c00001070240b80340114201c42000b17454a0f080b8210000b0318481c0c400c0401309203007282c0003007000043d00350300081c40e20340003e02c2700c0560001261000c04244010110b5130040030b004603070006101650144c125800c00c0da025050402500c08406901e2065a20981103d8003050784c41506000ba8401011185c1042d900c0e0b803001003e0020240e00c0b0321407403240a0403000002404c0c0303074040c2950120780d00b0060030391a4918607142500070b90b010901240401a8103404803501c0d030740b00141c1c019000c4260340286802100c1800740001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 80439435 1250 80438185 80438201
    0x1020408250801181410110403020a0f080a15092405090d080c070204110304050f06090a11040b0f450105040905031603050d1a31060b040603 62
    0x7099040440b40e640a0325408080741410380d0003142105031666005e40c4074140050740c60f560202d50700780b000841940b0809400f0f002524000c480300c0702d00b40d0b503414507000740103403c0c03043c0304054110207000004501607026421042c5d114480201c0d2400d01e50b580d058204105001b040301ca00369003000c4101e039801500c1883da00100c1c120007011448032061024141200c0186000c0042d80000b46000071900c494005c00144100c00c40120b4072030501780f4102e03844245e442c0142003940309113030003e0341030b40f400035150f075401c0d4003c021116166440b501744405080c09042440c1c1019001d5161003554441c0300501600e5101044643c02d440144542c01065030541700101010000c40400d031f020204000101c01c0c11104119000100900c2d01c0c85d00900b94028000c00c2c8000300d01c080000e000f4503030003000070000d0062141c800c1011210b81140440d190ba202d400f96074010503031140b494900c840c2162200c6140304214084200c10030b1041c25002620400c1c0c10085414201080c10032055406000f01b43d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 80440685 1250 80439435 80439449
    0x3030c210525030c0b06060d05010e0f061008010501030c1b050a0302010b0a03150207020f12060405070e04030203031807050d030903050c040b060304060504081b06070801060908070509090102040825 87
    0x300c01c0180e070b20020044c4903c01d01c0076054404d03a102103000c65444204481ca0f40304d50341c2044c062580e40b642c503c3c400050845011038855005800100c1d1490020303041c110880039500c40e0809642803900450007050852048820721805458848211201603202910030b0711a1b8002e1010340d95614000782034400e010f220f40d000e1000d0107420b000140c0c801c42024006e9000c00340050701c441f640d0000036420707150208040c0c0c0150f942d459000c1c0d014000300d01144101c1c0620220b40310350355a00710000354664111400740c0103820602c042003025404120707240e450b80700081264002a1908001000006261030071404100800b80400802c0018802018000e138102c40400800c044007010540502c402000245180d981d000020100501c210954105683c10004091000b03000400302e545d901c01900c0c1c480100c0d000364000203984d407207030901c0c8040e11180c40c050000300786040305104060b080500401001c1d5020701011410039010007070804040340a000c581d9012189000c00980e900f55504415 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 80441935 1250 80440685 80440747
    0x9060910020f0913090c0308040e060108040206090609010207030503040801020a030e010e0d140d020d0903020606041512020d05060a0204050a080d090b0912070906090e011503030c2105 81
    0x52825a404043d07484005003556003103d01401550700d44d004105003d80208104807405001c420301042c0400761054030302c1d4441c15919911420b0041d44d8180045400a51002e4100805011810404007400d620346c41030048444031340d241d60b40d0301d05542240d004048240c0d400b05d0b290b240c0580c503016001000da0444000c00c0080365542d103c42e21a05403503c030f80188a006140d41012040360421940c1c03501c026107046455926070301c080c8014085404040e4018450500402d42520b001d11600c11060b10b08a10040682d103814050400c07210340540580c0d114005031050b00100d02c090158030b00c80c3c8052400180d941e81400c0401c20350740d4064201c100d99900040241c1e64058002c040c960548450342c012540325092b800028000d00d00400c80210300740074405000074001850780100e4103403254420144030f011a650402400c84004240c480b1141d4900401000480c0c0640c02a0f48868080c07640c5c403900c0c01200c850103500c50f56070250743e400070707100181c0082017842088800a138042c0304c00d2a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 80443185 1250 80441935 80441947
    0x140628020c120d030e120706060315151a0408010906090501051605040e220302060106030513171608190f11030306090a0f090303060302040e0106060504180b090906091002 75
    0x107aa540d40c10f42440d80e0526070b5404610000032801c004002c0c1c0f62144900d12943c1c1c2e4607618001c0041d006034881103416011030156402d1a0f1094091504005460302321703030003c1850840100d8191b0009010356102510402c800703e07403100d00f80105074006000f00404101c41d2203519105086035001005100500b00b04c00300c00c6040f60b0b02104660854500c0c4021810f41c0e12000c22608a01031070400f03001108100a03030a0302015000b0904504071100c41c0c5007080b140d940d0421030032880000410060142c03441082e0000040c0e422806002010080c003a14030003001903603a47c031042c1e40805400c2d07000d814981103441d01a0b501020b03010441105241c8404481580d050813952400098201489214284000360100c0050342c40714100e02c0c000c25007030008880324140a4000c0c00d6501040e4080c0341808064074103110140a040111030181e81d80c3e51802d403030718111500704560038002c100c00036115920607040d80e894408090044101c1c00c00f42400e410305000c0ca502c0c4c60180107407603011500520130 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 80444435 1250 80443185 80443219
    0x70501030b01081603061d040605010501020303060105040902031504090f0507050303190815090c09091003020a060f050f0d020415020601060219081306090312030905030301140628020c 81
    0x50b94004920495502a500110340140c010f41055006034a032160301d02c0f00c50058505030360405009500889c0e00f0400d598944004a0f12032204442036404103104200c00c1103800c1d4264000c680c41807071440000c0c0d02204003400102900e02e401400d8400c00048a0488240801842800000d10081300190f24111078100394909080c1c4042c46841400451400500401071545146c02e41203c010286081860510340034800c50300100c16150040020f0400143c18020422020307040e02d40040ca02d40451b85802421101c4038040d400f500101710007801201d030001c440c0c402506480c10120005a1500d080000d520607035280ca4003240110b610035001005002d0b0041030034004e04003031a12a00007001c02d41800383c8a0700c2010b904090005c042c1c3c900181035540100c440081d80e100d19800200c0c076510b240110165100c8010103441a08100010032035220305d40d2620480d00c0f00900070070b007480061650004402401003040512292600700c50710219818007a1812001c000c490059100310aa00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 80445685 1250 80444435 80444447
    0xc0e07080a1a030a2607021305060604180b10031e1a030715020601050604031101030c120515041d0c091e09030406020106060302040b0327030d0e070501030b01 70
    0x3050841070396640024102d003812002d015041c1d0b0b6000303403c84506080398540b00c501000940414048403140035403550002c1c034014225070800b9001032041d8508032000e5088401003502030b040641c001820800010100590b09a0f4200c40d40e07000c01c00144408100180001034901b007080300c2c101480d0140800403514180c1c3c0040c200312500c4400900111081c00641c103402d088400198907100d01c42c40000c4100a40d094141002002d900f551010303613983c8140012030045000081a900f000001001e241d48a81c0c004580402c080c98070b9070f404052107a5030404c844060322a440d48036921140003640b802e0502a42100c40030b40c0100c440100300b140446034881380c21703c40d05442903105001140703181c0d960307009400b4480700500d03811840341002804160307030303511a10880c400b550034603c000034818084d2080c0c5048421856403146142d950b01e1441e00c0701c5402d41c0a81016528000c0309071741e02c80f402c03c05480e00c04020803002480d840e20030003aa00d00906513000030704041c2402202003069034061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 80446935 1250 80445685 80445691
    0x50a0b0109081f020f1204020a09180b130605011502060601020c220906020a02030409050c0301120f031101020307020309040e0706050405130906020304111003060b0306060a050f04120c0e0708 84
    0x1a8050f5014480040194003a01c11004211050070b80401d14108203004690507900840c42107400040706070b590042e0384290741a0703008900100b51420700b402c0202e0b0300c1040d8294844090768183d0300c0241c503950350000300d80017030300000700043c0203441aa01080d010054035810010900050140001c2280040c0344025060380d4010f2181600c0010b010000203034211901950380004e040d91034050350341000355690801d00c03803101201e0601010401240724442200c0c1642d1030b4150005a0540503102c01600b1907a90400b2810000030340308018141d1001e01c0a1800f581c0380792b0243d030b51200b00000700300640d5418810b000480d04440401c003c004c3d081b1084030102d07081074400362004100d80c8100d400034051080083c0c40580000200405c00c9040004224442c1d0101c404080701000d4240031012182d80c2d00402905040400c0441c50f9442c001010300303401e241e02c2c5400c51400580200d0100c0c160441d40c0070f82e81d0740f0590911001040325045412003d0710101c8044a958075000c40f00520084004d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 80448185 1250 80446935 80446963
    0x903051e0c091014030c0d0b07080f06030a0303090f06050103061a0a0f0e060111030307030504060e0c15030c070c0b040e09060c0f0904020d1404020a080f10020903160306050a0b010908 81
    0x784c16440042e031818080032850b0380d4028005072444003e42400714400c182140d20310001600e8000096500701d4402c0c010b4054140600200038020841d40c007940100401c0c0e06c2940d1800358403c0c0c2000081030783c02464082c2d841004085802140c8015000c03a043d01c1070409807090092841c28031004102c00c00e01001c80d003507200aa441d0ba26a94010303141d5206506452116000000400107055010b03088180a9846604108814445001400e4941540145050b884803102c64140054000c01c4080e5801c4441c181d9454a0060740303940e01c3d18000c80d268009a502c450204082064200440703100d54000e1500010344010729003003001c40058030480c101502c03640c00104002031607131a0b90703040e5004e070036400c2010030841c00758505000c0000341c1224221320a40b084000440c0391400490101042c8803000010010080e0380301442002e50058840641c0500c00c0b0313100d07504042c1401c00d4280c000c501072040000c090501030995000d8440640c0181d0600010380c2c0c0030000c41ca000038400d0103000e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 80449435 1250 80448185 80448209
    0x1206041205040e070305070f050f190504080d08061305010501081b0d0608010f0c020d0210020f130605030403020f070f06110c041104050306010801060506190903051e0c0910 76
    0x14a402a40c59000343e0704940d00000080c030400800581582c401401422140c40382448500b445004a03005d1140600c0c03170646e40e505001002407020403086c040008409814142d0400d522801814948a440928032001583c16818001903040441461508200804c400d01142d810500040c20803e8064010442c3e240300800c85107840076948182c940c0e00001184c03d00105544410850103820000c0b5500303a401d01d0907100b0100c260000846695884640d005080c03020b096254450080d08448007218448100300f25078502514150307080c5010780fa50751181038032030806040003440e150640e21842032981c014601801405030501d4810111406486e020345511945643d01303040c84001d21450f50071a040a20001c900c05054024001303407a4241c1c2103c0003680e840320f04070300f40d4040d4401c0c030f03030013400c1041281000344c1001c2d01d9020b03001c054101040d13102d0f501c0c1d0312946001100034a500901c800450414007210301800010034400c07086800d0030b802d05082e018203442c159540314403c0510a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 80450685 1250 80449435 80449463
    0x303050a020f0703030c050d0819020f0d110a0908030403020904080d091208180118030c0309080d0e0a14010e040b0102070b07080c0d0503010605090f010e06071b05120604 75
    0x442000300b1a88500090306840390310395603182c044d0640030140402c0b101802268281035901d48100505031041f43c02d04015143c0c0250408842c1c000d5008804042c484a0100050800c048860107408070b444042011a981d40040c043e0050202000350031010301500100001c2016980d0b041c8456040794000341d085640700440c02104004100b4108001c045552081c10048820303080078089100390041d880040c002c0401030f0500742240d68034200c692400541c1c00644c00401c0c810b481e1340c0101c502c07a0401d01c18264903080e0382d9140035480f440650019100c280020790a0030400141c400522240e030400c001c00e02d4100001c4c0640c40400e148a00680c2e80312006220f980c401c00c0313401c0c01410414141682c27843c540c1821980c55019241d2511148180c0361003207100c0d80314030100d0381240c4003a56002e040c40c0745038007080100281000740354100013030100c0c1104650344070b2009000c0c1900c40c1c0e003144070313420099503040c1c503550b41070340924814026403000204038040441d80b280d0059004850040d414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 80451935 1250 80450685 80450687
    0x603020f0403140c090a060602060103110411030f0105040c0302090303070f1e0807020307060809100c02010f0216020102010506030706140904320c070822170102040905010e010f0303050a 82
    0x802903a00150454480c0d80d680080f2600c0412086141c0d0000c4e50141e03d551b440780351180c00d076019442000010781c0844010400301d98000d00310f840880d0010000305541d030102a200c0b01c142c0098810308075226900c001000107107090720410210340d0181c241903051003000320020380c40b03000d4808003a1000074030290090412041071500c0050301480214076103000c0d2103080603001d0f9000b040302240244100c1c54045142c900550182d4402c850300c600600180144070f060130054a40400120255921004001c1ca501d2190002e0000c03440140448141141c0ca4000203007074032409000795001e070f0013108060200d0340d440040075038a101e4a0301040d82e95010380300490003c1072030100d1655984c038100502003442c141c11100c807070710703e00800f48003106460b800020f011522a032030300100004010002060f56044080c0d003461280c0c001410080d98940d10b00f139082501c0c038240b080401d541d600007414401080e42d449a0390140c14608110301503581000c104c9080c510440c00040e0074031401081c102042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 80453185 1250 80451935 80451937
    0x1051f060c0c140a03020301060b120606130308070809030a08030402010f0f0f03020f040503060112050d020d050307031d060a0501170a02030d1803060e0a0b060103020307080a0e070302040212180304030b010603020f 94
    0x2168054000c014056944ac141851b43c2c202000c030125054030540451030501d002d001380d4000c00069a0101006447d44d9074640d0300d0381c00004100d50380304091002c14100c2e9414013691a07420f0003484030070745c2da00d4184001007184207041001c00902441c920914002640040100d081c05011f08006039a000300f000d500900d406250301513039140c4102d030008181f010b104940c0951151040045501821072024260384030b69101d0000c0001840a2001844191081c1c00c5507075030340e8020308030700c2d506412034441c07600b0003104881504000351242c0041103c0580e0b401c128001c0c00008000e444000e040392300103030310342606120340c1041040030f90b149648001098102ea00841c0c1c010f404102d0491000d074030a8a81c250b07a102601c2c0e0840c3c21000a031a54040d000300c81c480c01403581d40344810360b0740c1c4da0f50340c6c001c00800051560601c203844001c070040e280c0744010518003008031004030083c6400204030451100412282d052074200713220400c0000e00f01290709065480f04d080158698250403010703e15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 80454435 1250 80453185 80453189
    0x30c140a08190905030708060703150e091b01140d050a0b060c10050106030b0f13020f12011403070503030f03090c041109040b010302031009050405010e01051f060c0c140a 75
    0x111050000e410304034012007006070051409181c0701c64504981d00c1e030425451ba201c03442401d429400240008814170700c04c5d44030a507080341c1003081c02d461548495005007400e078100c1c1c000c0c2a6902251280710142d44520902880300000d1a01c40300aa003a00142d0740d40303001d281d905209407a100c102103180c0f6102038200500b040b50146c003a603291700f018117880b55904503e5100280b8030340380200100c0e54503c00c8c051094a0080508140e5a201c030f038500380005c0b038000107070420721254240608444481200b000300441c4611005c401059410600130000c4188000b0019102c3d81c00710348104111f07103001c004c1d10110b8112402c2c0c56200e640f80c0310194100704210203d039038014600345400484c5100c81000c0c2690070429101084243c0c04603005504038802a071b42502c0445480b6420811151540c102c0f980c4203105100108120315600301040c2520016220400292607401d4800700200e0900d049000810151501c0031403011944c840100100d06400380000d00c2018892a00c00c5444a00c08400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 80455685 1250 80454435 80454443
    0x9050906040b0d05100501060203030f010510031410050405090705030d05032503050103051005060609280b09030607050a0c120509030709020309071205070501051b07060305010504050a09030c140a 86
    0x80f60800c9190454482c9003007040c01c501c0614010021400074400415203200356000c0240c043c85074203010400c0004140510490109500c90043c1c41c8400500c80300b49000362a030100c0c0c80f28007403c160402c810341e40c004004030704507800000e0811255800040424100b42c050030a240e403500c9121412035860704440301302854040011048002c540c2c0b560156040341c1c092000d90f60018408201c45007612010f03501103611000602a080c0d02d881c04900b400c3c9450750440000000c2c40343d070440e010540100b40c1c0654207104000c01c0700c190504050060f141d1101d601d00d00180303810f1202d50090a0081c0482003d840480054051004139000d80101d50a0310710050444542d10358031a02e40000c7d40c0100c9200c892400341e6030000441001c01c0c0403020105603c240584042400d1000443d05600009501c08001603020380074800c85405104400107800c8643e03001c02c1c01e40c186024801610805072101a0f9546031000f800c0209034003101124482d6441800554030343c4400903e14544070220802038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 80456935 1250 80455685 80455699
    0xd06080d03050109182a03050a020306070203161704080604051606020703050304150c021806030105010f05060a0c0204020d02040e0f070f05040b090301061a0a090b04050109050906040b 81
    0x1040808001035860644031039a9024006a81c841c4404070542e40d000c2d865502019071044050000b402c80d046901591425040c0409003880015004107001303402d40c000e0700d5503005019108250b007000d1080e50340c0b1071000d000a504d40a001242e4411845592002800c0c401c0c8130140a004150410102c600421403e006c0703c1c0c043c1094100651030382e4009032840041d00406030005000350000c034001003201d4105002d54201854031907200010710059044c10b0402a00c3c5a4034001a0784440e90003180c44a28004e00201c0d00d4950103244c21241c042c1c00c04c80200503d20401c1006030384246c01c41e442100d50b17190840e5030031107034800715020b40184039842160b1130000c90301241d006581540d040c4548038078840300c01039440b549030998540c0544100540080e8040000f8841c802d1090000c00702c11001400000d001c03a6500c0150204848007018480c0348040061f001da4170310b038006c944030058070302c100d0254601403401d000640080e501e0301c10a030040c6850400a040d0740d40d07540c049209804064461 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 80458185 1250 80456935 80456939
    0x60e100603060b030c1e0607020d0206070f0b0705071203020703090905160e04110301120c03120f0305100e06010e0a03080a0305041209151b0606060306081009080f0c030d06 76
    0x454040c0c524084824085e118000240d40d03d8905100c0c084065102d440e016180600603c0c288411a84510710998000410491880040e211a80180481401503820086205251400d00952200a40450200601800002c01241c01c4043d000e1007190141801aaa40135618041c0e035203110f00e0f401101550700e040100300146060300840311800d4030b5136554008414070311040000310f514681ca1006c41a0081c0014001213451001c2265058020805003075029030301d964006045803101e04090010754144000701c62a0b1f00b50117000e41010110b8200c0b00d01c1402c0c44008010080d00a200d54100103480031080c03095140c00403070002071500032102e1607a40e0380600014026110549046a4401007122484203a501c90107522017994064a21303c502003680709022125000007440860b0140c803c1507490000446500c2140e0007002142c6020030300e6850051040c3c10104034130029401c0c241081c90060000302d801d030840d00110306440e916611440c1030100c10b0f185024001c9013039440c1d403920b280 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 80459435 1250 80458185 80458193
    0x80610060e061c0b090c0a0e03060f01031209031502132c06210307030e01300b060d1409030c07051302090a060801030204110406020c040e0319090807080f0a060e100603 74
    0x410140d00548c4400005c21440000d01d41d40b404202c0e00f0401c2680c50f800140005000c0034055081c01007589040035a42e43c9a80791504030030020002a81c040d580000d40c0c0d09001200c3d4400c000811000100202c448420105200020036000d400380c443c42c05040080c2c46035562082d080324241c54031070f02e41c0ca0025a40341540c0d0300d44c841502540401e8824074100642d61040035091003402c40d020b03500312540d0700c2c4000007140c0104103403c6a4041c0d16001d0340380d010780b600c8c40505425401c500020485503c0018840200900a0450012500100b054150f4490002100c00865409940d801081503098240d14024011400701303690242000c1d0380000d40c0303503104440d0b6059a000f2901085007201515005c801d030320541c401c080150300043e240441c01c0ca8a58032100304030701d0010549141a8000409100c00710380083d0700700104078a12070078015a882001558007400340b010003814600c0c5440d0000b643c441000000501141d200d01d106401100140410340c3d1030721444006000032030700d82c64 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 80460685 1250 80459435 80459437
    0x1305030921150a0f020405011706010201020d020715051f170703050601031505060604060c0f02010309060e0a03021c020619060e0c18040516030f090c080610060e061c0b090c 76
    0x101c500d14513040040600d000190b43c4215001c4607016110400d001c0c01c0340107010464a002800c03d81595030a02008289000500082010600c1100c50702c1084000003a21000c450b0702400341080f02c1c01101213140801051240d4605451404c402c8500e04603074983c4141c5170900c5508020102d00030000000104000c02401c041600c05070442480555501c000703000039030040e4460a80003850400c40f503c04980580308080d0316a0049c58040341e0541c00780c44190030340d082200ca1403407540c0824148000c1c581d05102031034040c505004030384104501d0043c000d55520780a803072008070381c03404010360f0781c060001da11180080c09000f002d40868903184244041640041c4100551020044108411450a4810144110752040c541106107040d01011401007582c4105003050580e141680c0e07003c90082c4800c0c5008010150052884d4a010006010100e403207071f10100c00e110b00c0900c0b614840c2d84603420b0314600d810030b2804199030000782d2403140143c00c061040d283c01c90b5440050142025082c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 80461935 1250 80460685 80460691
    0x6050d060501081b01090b03090102071208071403100e13060e010b1002030705151305010f021e07050a030e0d0b16080c0c0709020c01110a03090b130503092115 70
    0x8203071801c00b584948a01200c80f10313212018002841d040040c00010f0903000555086100310000508060711a0343c0c401c25140c070010080d01045c448410000c100c0d40c01000540e2081400c0c50360380c25420308401e800c5080300d4600414100000c20000550348aa2003c03102044a17003190303062186200b0752070568020000612403901402140d03100782d003103500010450303886507030100080821014102e26032030018000791507604400385c1305407480e000c20024021110710b24045500180d80380720a01e009508000c03001600c10032024140100700100314041038200000c0d42504203000242c2c8100000b070104010404001e102d500c2d04000d110b0101b04e070303149656260b038481d01d40e60400e0712503118200d0180284e0a1049140e4884003060003404406d40180107001007a40022a180301c1e0f00f5150030282e0800d903403003c00039a542c1000c00a01c0350000440f5000400401c007540000d45a403982c0d82c40344140d98101d40078011940300340c188400c10440d84110b0407168029a9401102c840c01885105026 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 80463185 1250 80461935 80461949
    0x1021612020a060305070c0210050d150801061e0312051b01021804020c0d05090409060e0a1101080105090f180303070309140d0206040b070905060703030b10080c040b07050106050d060501 82
    0x40b20114000340644500f600a459680300c52425184c217038200098000d1840d6001d08026041c401c2003000c039494012041108071000744004450708200e103080c01c48400d1750003c400c01400404940c809141c42c060f650590f50410b2401c01f0103101c1040660303d0303224894612400312034900349982103000640c0074221003404107022000c1c44110070304010507402890400c500070b81090a0000c011800740e00203010007035015102050155460321100c0441d245030007a01c80c56003150901030704015030825002c0340781c2c0090030841c41da541030801069403100300606a11800c503c01c0b000c5409600d4401c004110300c2c118000712a503a02d030134140240030345038124003118a4981d103a860524407101013480c17200e55200d40d00030100c0e951180c81e02030039110060b0992080c0310750702c90082890744131080140b100300d000e40c03000b140c00100702c1c00380010807180003608010030500390184000021030340100c4040b0f50390300f1b10700303a00e41c000c3d03007080e81c0107020b00c0e0b0000c4c0d0b0042603011500100051600200d04803086 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 80464435 1250 80463185 80463199
    0x16051b2103071b0c060e03010f05090f1903080a0b04020d05151804020603070804020a09110702090f07081512070f0302040b120607120608150906060d0809040207020102161202 77
    0x1c40a20b880c0c10501c0a4002043c0c030f25021014081c0386e02c2160424100700005001203400c8507004001c000322401550005040e4104a0450441280401c001140c481c4960580c21080c51540c50013022404050849504907841d622101d8080e0f039582c05403100519040d1041000b800c2c0500f4425503080000303911801080300d00c040640c00f02662010504c9950068101c85c5103545440b421183c441005004030b86c4041c0c50200130501e10054800c1c03444042500ea50a541c4400030700400250203c010103417400c8115200800c02c02660100c00150007240d8912003216101440000503240750000441602a102e56031001a03007400c002103040450303002790760400220301a1002d001079440d448c81150015402140801d04061052022500190300300d00000f07010390b22200300f84e0410200c87d03c000480601c0d041070141c44a03003440183d0304450101d903540300e040e2a90b1384040c414080e24104e07910944c0e010441ca400c1d64024082d064107002aa00c0d071001641c0c4031105040300700c4141c0400c2c2d0141c59 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 80465685 1250 80464435 80464457
    0x1512010512010b060f13080d08010503280f060e030a08040c090501050108010605180a1d06041817040e0907080609060c070b1b0307030209040516051b210307 69
    0x10043c8a80d41c030001010b41603900d0714000318081185540320742d186010307051200c10006140b035001d104e034a109403211780e2a8002540f421041600d8001d1440e64920076298000b020000a00c404100c5421141d00141103c11001e01b424a00000c0c16500000c1c0e8071030000041c03810f00d055000e1900f610a5209800021541d500d4101400c1114401d0151078080780581005010390307070050003e441d00003c003c05015035000000301050317200b0103652144011200058090b1588040440029804402910100403080d0320314010707030300d81e0de01480140920a2130550301f132210b50340608071350207001e240d46048840d0401078602d559030002031088072458011500814400d44000c03c00a000b0655054100c1c1045541d80b1009036044000e07244810f6030065840c0781c0788110b05000514800e020710b480c01a260a59001800140d90f402000703510300c0000c0350080141c0540001c140c9980b03880d00200311b408a10039101d1a403401601107881c0d0b070680c44010070201ea000d23071070000310300c80c00e10340c0c0d2200b46c240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 80466935 1250 80465685 80465719
    0xc060307180801020408060c0705030403150225210c05010e06010303120b031c0e0405070305091902060a08060d08030108100608010b0d06020903010b06030a05010914070c02010e15120105 82
    0x801179004001744c940003400490b0702040360b440a4202917010314150b0707241c02d6880d03988015071034681c10481480d58010541c03404034a000c0c03028808048603842440600880d035a111020500781c40d6401610510311032000c40d009110382c0211054a5100c030003081028018043c49640317074400d110441c0010912003941e088840701e4015110805d402400905070800304820b1110001092841d1034108840b060b10181c0319541c500a090064041d6100007a06040c801c00190508400105d8007525151204103880180c40b0007044408080103072402c07a2031526003100243c0341e484010390150a0a50210020130308000c0402d00c030b600c5190102082200560301e021503426102743c5a40643e00c00041102130000c40c116030010441d541c0f009000240301454200000c0107034100b980d0b030150301c542c0c820051140e038105105001d0011001202c40f03501d4940710000901400300300b04024100040c0c03055141c0180ca0784002030800c0030302c25580c0350f2a0b003000400481d002e6070074801c042c451921a1002d100c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 80468185 1250 80466935 80466937
    0x1d0a080c100906080705210f07020d020106080303011205070503031b060708010308090d03031104080102120a0204030f12020c10020a051b031519060810060f05060306120c06030718080102 82
    0x1d41e00d079100c2d511340759140007065038540c20244000b403800f040c66100c4030400c100c1c0100c0512520a6a10a000500740300340024a0411490110701c250780c540071007404640400000c2c2d80c1101c40c880d081c00340d8035080e8600542003945980c00359416201c085075100b11180e0103100300c203990b900e0900711002c95846050440d581c43c004e10020700421000c000f41e1509007803030840300c000d260003420007080200482808403c1607101d030f485403030181d5020460000166259164070303045148103009508050070740c0c44007450082c1c0e03410000c140c2502e00c4200c0c2c116600a00082c0c10182c002440c040c445400c40c5006503c400f900c020890341c0f4050320640c10080b6041c51000e00040c0c501400400202039004070700107012074050100c001044e440c580240600e0103070300586e000380007424041c1c000c200e1446480c80a5903400c0c1c000010104c4000c80602c41500d610040c2c075070118003200c1c01c0346181c2803181c50900308141d4684590304000000100400d494100604500008551490612103581c030100c813401c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 80469435 1250 80468185 80468189
    0x60d1b0e130b010501030c0e03120702030f060919031206060815092404110301170f0109110402030a0207020415060f03050c040905190912110f07061d0a080c1009 71
    0x642c00c0400601a5520075401041c152059013401c0742002d8248000074909901c0000303035244160001007100440c10144000d41c501003007500209030500f02400352589442c082084407101500d0b2050000501d0701c40c400400c9100c2c1e00c100104002a29500014203101c01110442280084402e005145040c0240000d04c25820290468031100000c80380c101c66060700500154802d132940c181c1000880d800d80154000d0a0761255460360000c188651400c0c8841c0303a42c0ca0b0b034540d01d40000200424000040d50041050403900140e5903500e110703800d0002c0c00b81c1a07020390407034a404030b43d11000510360205000d46900f500c40b08003c08ad10030b0220141da00c01c444500c1c0f900018001005074a0180c0c00560b048403400001200700c2d60303692039200844450b034a0503924441c10221010b400c5812614070301c8148100805040700c41903110011f42d5410040c0b0590b400c05c000d0f504621031050b00819902400200149071544403540c820304070340e4403003005018901c90030014441101441c019540c1c842 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 80470685 1250 80469435 80469443
    0x5010206070e040e15090a0605070c030c030804150203130b1005060d090302010608030f1e0a050a0807030605040e011a06040e0c03040204021303050a23100203060d1b0e13 75
    0x1602c1a1440b0030b10015082212280040d846118035416200c05800c007894814035101d0300408080d901400d050050381c0c0050726100078000b00c40300541c0030035445648207002c1a003504116607180c48a140008401c04040b0b4190f2689201000344038045012100d84514640102070590850b2680c810289c1d141c8098410960300010810000e00603a0658104142c034500a00000490996581d5281d0540c0c1c020822101a0352000401510111081220481c40b5001080c650b09200012078090401d1041c103e40c1c0c0144141440044c4601d071003a04104040c01d0041d000b0700911441801840c0030707003086c01c40c500410304031441c0c803181d506001c019101140c43c100d695a0f007a443c3e00c405280c40c0c0c2e0010b08140e0308240c0802c0540030b01828840c0c06d100444c410002420342000d1418140040384085072020341c401e510f14400382006d8400200240061000440103981c2d803181000500d4209040ca8002d200e498059003011040804207050320480301078441c6401035584218020801111140c0028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 80471935 1250 80470685 80470697
    0xc080a140106082107020d03050c121206010e040e0304090204030b060915010c08070b040818040509060105040b0a230102061006050f0a0309061d010c08012301051c090c0501020607 79
    0x50b120061351155030b01d1419000aa0b10300340d0960003051a1108181c4150080350707000414184000c42040950130200e03000c03c045003007610304090691034800281c01c0c181000704000c58440540d581340d02c40740c030070b4415400b126562a507588032440690081d10080d100300c40b500001031201d090081c41e6030700c590481d8000c415080042401912411990002514071a20501058001074021b1203414010341c040d00446440c0e110140c44140020090346040d4029428901404074001001a40b10705490f02118007142e00211440454a0f4124940c84002d201c81005600624014a00c08209065000303a090b6403880d40e60b501705112058030343c410382000550030030000022045c11405441d0b009500d1402281007191038980c1420b83d850150031502c100522251403910007000d100e8048018005d04045801c3d40c0b5001040903010b0400c03070040c5010b440380d43c03600440ea1140c3c00715405500c07526807598043e20b040600034010000007108640c001041100801c1c99030001844901c41e40e40c641d101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 80473185 1250 80471935 80471953
    0x20c0114070b04050f0a050a020a150c02040209010e03010504080304031b0507090b0406080d030c081503070b030402010203071e050c0619030c0216080312061c120207030c080a14010608 81
    0x410b040802401941c281c09000d0408502e504103208940703c00d40110020309809015004211000400354488189046d008090032022600700c0e060040141e0129401611080d4000040c0d0f0020080282107038036501c1c01c82004200a200d10246008501a45d40c40c2c1c5110f50803000303480b140130300405c00741c910350060404211800076504041038180c1c0150012903046c2e503500d00c003031800035100e0350040825260300c2810b00f2150f1240741e0a51165a101c102d100780c00c070803000300b41c8500c50f0307002e002c0340e012000000506690007081140d642684c400c00080035440c0358055405070b500d200740115410b004401d0254100c0c0b511400f42c2d2030340c40f04025000349a80c1980015001000300c0071241c002d60145945182c0c842c032205072800010b00c0e2240203503686248948100c00c481400400482c03043c0068405103410300302d00400c44042d0360707110901c40c3d14035030604030680c036100c856800100710142485011620980128103e1440c074844c0418006101e0040003603800ea034405e0040001540c00042c0d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 80474435 1250 80473185 80473193
    0xa05100c030b0a08060901110913090501110309030315060a080619030203030c07141002060c0d0f020a05040e0f010e1306090822080601030f0204050405100912020c011407 75
    0x40010181001c0c2400102c0b00c10560208000e004294881541c94120300100a0110b0b028010140e410a103002e2070f0b450614910700050302e244280203103169141d524141d0104100c0258481d140e26118401529206d01c0c03c681c140381e4a90081f203041c00003c01850821a640c18980191500704059441d40d44c040e43d503010621412685580c0c01011200e040a07001015032030038001407607480a503101404070b40d800e00101054600341d10034418003540d010001c400510380c2c003003080d9801c990111221a503500c901d1034a400906609545d080d0060b03c0064094000c0760000d00810031140340130440c0c2106e50f940290064018824450101009aa40001125490310070801030130103210302c00000d6441c885896540c041c0e00031929040d030318002104212181212941039000030700d110802070006604584c1d80011440b202c03103000b4091500c46011400f00301007840100c0000303180c90300810030071b80c881c208880d84514600c0d8880150242c0d0301e01043c02e5119940014681c03001200c803a10304174031580c2e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 80475685 1250 80474435 80474441
    0x30c070f021c0819020601030203061b0f18131e020a050d0501080106030c0806011d04030e04050403090e010b04060e0d0302071203020c0306070801060c1209050d20030a0510 76
    0x908076800212919400100000003542500d042e00070310002c1c0e100d40240c1d001c13413840d060f422031400130341d409100100016580003030015480001da0b046a81500100d000366469405001c108024031400483c5491092820410101b0358000403207065100c00c8004030303000d040341d05491010920460b407031501040105150000d111803410351902515081c420038000e012500d00fa086035055944a600c104207020900c1d481038060221a0050100d03545090038052101c600032588065000c140c038001402c1c103001d040c0490440c08041c04c140403030f14207460300400d42c0d0341901650b84c1d1440c0c1d580006c103a48035501d040d43d094682c2a120a2a1610810100f101200510600710300310302c1000004182ca1590011801c09140310b0340007032040e4209082014180800240301408012119004000c0550b000174091400b0703030400300318220016210310440343c1d501540c001e90742100407a0002ca0400403100441c5038220100d80c80c80115a0301c0000305601c1e2441e091300a000c0e030f0f1004034180001c01460b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 80476935 1250 80475685 80475713
    0x2070509160f05040b0d0603060f110a1b14010e0609010b0102030a1b0206040f08060c180105030910050903070501060e101a090409030503040b09010b01092303100603120302030c07 79
    0x3050403810543c5d40e0101d24a9a440031003084003032919101c0800400c44140600001d400600c2c1d01413004941c006d940a8960141401d11400c000f840c0202c5c206501d2500948030842d5000100c110740d107042e15105501070005480c1100c42d5105460010305026810310802003d03e105038042d6140840c024001c5586079485462842520100740720744005035034a1b0000c0008100148160022503d031000040c1416802403846034050010840d003512200b03212038001d104e107024208542c0f01d444900c0081e180070301d1880080151441c00c018030008890000203001400c1c400c0000748021900c1b0b1130f260520440540d010704840011200c03e10016030075002d072030105081c05507200c0c205414000000c05540c48c03003400b500460700000c280803c0c006614101e03507101000074020b11035601c0100000748003803101d1150046091107007a003d40074000b0b040703e00b00c0c5200b000381240c0340303086d030a8240c07001011301e48421581032000c2140c0e00ca55600034000e49228880204a807414580c098480b12503a84102c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 80478185 1250 80476935 80476937
    0x71e02070b090a0807080120030f06060319090c051005070b0106080403110a0f0201030609090f0204020a030902030111030a0608070f060c0819090801061a160c170d02070509160f 78
    0xf0030340440c0d000000c0140e0350003008180d0000c15120095404103170031141c5454142c40551041082001c5015290081900071b00199800c0b5629686c4418000721625040a550041400c002c0d031707881404150101042a110308540c00300c2d03a4410047c0036101442a1000100b54118800c010000113014008541d0300074041e0400d201113111100c0c82034200714003005d08851501a030b500e040299641441100b024104c008010040b40720310b510b41c500c400100620082c401c940006414203118400d8100c4200755038041c0082c04070f030a191146200c107030001c0300c3c0c1040c000d00e0000c1c009544800029140c01f00c88100c0d118040060821701d048034800074425080c1e55014080090521510302c010b58002180100d0343e40825982c24440703c10b00b95082d541c800070901d0054070340c0e55000e078050002c9689040c0c62114284018070070740f44c1105414141c1e40140f100e44034800078002001c03808221140307068069402e80d00c03540d46440410100500c203490542c510200c08404524580c00b1304641000c0d0307003003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 80479435 1250 80478185 80478199
    0x6120304053312060f06130803030613050105010f0e0604030c06030b030c0102031e0c0f0d020a0b0709060c151e091e030c02060d0905060f071e02070b09 67
    0x1220301148400b200c50b60321000c480340b4014507180e582400c0055000044981814901c0c10b501070349030722000a409010b01d4441c0011114920b482d940b03110450303400c140000d41c44041155140f41c0c4640f40d0b007044070880d01420b022415800c03019103912400d41641d01c161103042001e00c1d01a411030300d00c100d03084080d4000c481000040081901c506003440241155a00071400040341c406260a203006866070038107652091181901c80c41c0808413407070300c00d00012151900c41c0106609686456018001108140540070b0302100d141c0c1d000c0740c107082d403070b002e4114030556403510300c0200c441400e40e01c9100001078031180014009480c080908404001a00020881c1501c495080e075808030028420985980e8070200b003010080b104c038820185100c6080c54180100d07407074801518120000c00020700c10080010740e821100d81b04c1c0d01c400d01994018045540da484c0410400102d114250307081c40c08941c064890014080c3d4401c00082c0c0c012059028191203894407110b42c1c159005440c07400c2e40040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 80480685 1250 80479435 80479439
    0xb040809060d0501030203160e0c0a03060302040501030501020405090c090a0608270c04140c1603020a05070f0f0503031602090603070b160c06080405071206021210030204050109021206120304 84
    0x10301e14000d4010b800031684001503551462042518000d43c0840c954610b9554810810a001e07204498541c050200d681c01d40c1e5441c00203c00720020071140e04000d501903c2c1c440088103105055028205440dc01c0d140241c803900c4400e50f44c040c1e4050088610f07032000310b02c041800a10b118a40c101c2d000140a10301e80b020910a140c808075180c13402c4c1242000354015a42d8247c0f61501c1e0250380341004140c01000024207015048007400d104030307441f5085e54088640d0071030400d4400c200901e00c02350424151041c81c0e0710f805081300d484202e840350200c012043c400c01702d203610300030088404e5103056446440701e01c401035090002c1b100c4c000700f58a07414050303942c00003807910025000b0004078810038000300e60700844d841c0542d090001d81d00158200703c2d845041000007000010301c07001307498100e00c0c61006d03040e40e40b030400064418500d0500c80a018001808040b0756282c484805a078401c950501c0307143c0e2212544800c0b800350507941e8030745141c03d0000c02d490382000545000403003030745015689803035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 80481935 1250 80480685 80480689
    0x302100e1002010b0103050c04030201200f0d020a02010e0a05090402090402210f0708060708010e041b1203080a05070c23340f03060f200a0207170a0b040809 69
    0x1488641d49600542d444030402c0c1d1a0390b03854400c413544020140740c0181028190b1700000d0a20504620401600440b49625181004108441101d58410004803030010b5007110009445044502080703020800701e00d03046000c0d00d440c0000c0c8050740c1c00034140000075640d07a020403d0b03401004d403003a80c0050000c821403818403010040c000b800e100c0c410044c020780112040907850460f10b0b41c00200071b6004503040c850410b40c0260b1a60460740c50403401c0911b900e69003400d800d0000480410380103003061180c0081c142d6480c0b03010f1803c0307a00a440c0e040e895601c258030314040c3d135801c960310380004151400358030004022084a00001c07100440303022402170308088080c60102c0a8030301b01140209003414251040710000309600241c201c40031420902d240129480c003055880c00000c096a031241d011174420314040c2d10402241c006400c1c500794071030021b27003044c0c003550060b80564018040d815010880c00c900040540544c4201401018020515150200c0002c405001140c8400307080010000369 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 80483185 1250 80481935 80481949
    0xc0609080409061403010513021026010312142a070b0408060a061d1509010e090c030703080904050606070804080303070816090302010f1209080c0106170303010302100e 74
    0x19010b03000c00010042c0c18038806244d54004402228426030500c4200030b080a01c1100c1c42000d180d0650344004240000042503900d005003010503607102c0f0244031411240c0700820103241c1220b0190340e038400340302d89200c8111a403220700104500202d404002c21403113025514040000d8030b8080c01d1219110f0100303081e607814120b41d40d002420351000400c040c0511003080c0f1146400450035101040514036002e495200e1500192070100300b06800c10001c1c00c0540004004c07050040010b000081c103685030995018580030988020340e051007205070080d0315080001d241c04c00c0d250018107140c10003986a0800015200040100d50040700c1484000001034801004e000504650006582c0b13914080344000c0c600500207140344a1490711000704a010b17070f04a0725000a03a41c0a04c0e001c2c604c90f803c1c1800b07a81c10980b440b6140c1445181402d51800d003c6050080d15407030041e08020300091759070f8a100c00c50f440c1d43d1046407006400800040005162a02210540c41a14140080e84a01200c0002c0003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 80484435 1250 80483185 80483189
    0x1021002040e01030507051f0c1419060b0109030f1b080604030203180f011d1f020a050c03060403050307030f1b0e0906302d06071e0c06090804 63
    0x120a9082d4018801c1100a00201011744411342c3c07404048000c1e034900300080c1d005800c1303030f00902c100500300200340704c4071030078418540c02e41c50221000b10f035605d01d1814a02200590640da800d1401c0b0040034103600c903407081c40842c0e030400011800084580c40c2c01c200f41c510101301620412900500082801080c000944114002e401950300d4400d00b0409044540740000101d100c0c2c5641400b880c000c0c0c1e0081020000c0021012080c4030b00280080817440e800700d1410349685150a044195086a0380000c821241c5449841034800440000b030506a550006032401008100d040c00085c0900307100b0361042c0c0310600500b60210300711203600c1d440c0c20414074603140788000801001e0010380c035042c007042054200809480c41d0040f10700e8481c00c85004030000030425014040c045104440036000c120801030f9411246211131150019485000382d0301844c25a42124001ea50000708103034086e60240c0820902e1030084064542d01b0003044840c0e84070041c00b15110340c0d81d02465004503400d507002e400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 80485685 1250 80484435 80484449
    0x3050a1b05070510050c030109090201020a05010f021e090f0105160804030308040b09070501050d020906040506030c0304020a080606031e100501060503010602070b0f090108041e060609140403020a110102100204 92
    0x1603a003400e03003481400d004c44440300d07941007800c04d0f05100011801d4404c03241194413030300b00081c051416100413410121091405011582041f159400c08080d55004180008030001c0b40390030b12844104425550103100e2003a03a02c2410040078200300d501410040c41f81000d81d4041c0202c81980c0e039102c4441d83c0203500250005400041003204100d46103541030f41102c060b4009000080c41c00c00020050f208401180107400d801017128080307512132605480181c000140240d859140400201c1c401d9081118142e100c0c0751501340001e8503c0303010820742c1c090f00000d030241075000e030101d02c809204906800f031214a0704c036848a10723401c04454440c007400781c5010b50741d142d40c9500d0f05c00d00a1030040349400c910a006401c214455800c00d0f00b03001c036060f008081c20060116075a0382071841485070714a40c002160180320b80c504c410010790340d100c1c400790740f421101044426000c1c01d00c0d07036201c4821540240541e0100700ca075004104100040d801c03003001403045071100c8a10200a40680c1c2007075000d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 80486935 1250 80485685 80485687
    0x30521040305030402120f0624030105010305030d180305180607081308010b06040e04122706140301030f020d05100c020604050c01030c050a0f022b0801050f1003050a1b05 75
    0x401186840700e049180006d10070001d00402d02981e41c0c15032034481c081c0c00c155180c140c80118003089448001e800c042008001c0080080d9a52810a25204c0c1d21184510f070680b0f2400e22850302c4030b100070303401075040c0c5d07019682ca070f04003208050071802c404040300c04540d1254041c4440000500244020080ca51746182c00e00c100b1407929041d1403d45d46c0f81d81c4058070031348051005204042d40d2800c002d51064120148054071140da241c2a20650800203040c030003000d51843d142c2d1254410b00d00c4400b100c009640d00c80c40480f1640700d109507030000b800024044044220072101500c0e1074000b10007080e002c1d50650b07880000b04404213049411107601071000d03800c00c81c104418011309120a1154031820300b81400740902e4408014043c1c41f500c020741d020300030840b05c8517200b54800c200d04105021103101c4141c46032014915900c07103003540d0009200007211540041482d0900301100c980702032028000c40191841c1c25826806003000400b0800c07450350390010000724035804441c001c1d40300001e803125 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 80488185 1250 80486935 80486941
    0x405040f060f02250c0b040608011404020310291305010219020604060c050c040f0b091e01060f030905030409090201021902030a0201080601051e0c010b03011803052104030503 77
    0x225003601d80300e0010041c414414440380100d0500406410888060302d407200c481350605142c80c642210351360300842c035544000b08000c10f419030000703a00d9060341c03070464285a503580d642040000364882211000ba8290510104001c02d82e2480c5110083e0b14902c640c40440365045400b0202940000001200041414400b0456540c051000e19002c0e804408036030118238042d00400d400e4403882c4500301c01c1107880080c1a0078454140851814214024414800140c2001d01c40010f00240b40e0320340d111710f094001040c0484c0b85200c10750f81c402c00c802284142a0300e880b5040c0d0751075061114070000c0c1900d42d460800003034030500051019240c03500c0c0c0010b185c00d0f6070000900d4908680714041c0c5c8a000d00c8250000341c0d07000180c2820240e030910f000c401c2d5566680c01240d0314000c00c0190a40b139200032202c8068810080d01030965a40e48000810074205050101401da8104100c41d1034401c01c201884000b084c031030300040a0050108170403954417114050a50341c0000c0880b0141c00240f808018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 80489435 1250 80488185 80488193
    0xc0c0a03020d0e09010e010e07020a080a03020304060b0d02030d0302030c040306090503120c070f1212020a0807020c010c1a070c0b01080105010303120903051c060911030402090a0e030d0e0c0405040f 87
    0x809060b02c0054804041341d604204615504940602076411756a14220024000e180300b04080c0000941c08400c4c80c1e01e944281e400640690010ba8003100d0340341c00d00968070100e061096440907401e40040090602a490319810780081d4405040c41c820208108800b1000c5282402060440f91041c80190b556401c19103a41c1c074500d0340580b015403405000c00901000c224201030b500306084d04040000140c4252400c1603914003d99050700d5074160011400c500200d0308100724038031450507902540d80408030240110f1740d11a00d010001c2218440c41404c5a8081c509144140c0c00300081c02c003a200750000d40c5650820240c241d02420050b91038000602c105640401c0754011039401c5442401030300d41c0303540c01421902512070100100000c040c545402044103130400801807402c520f0401c42001d8400c9140884d80c0100c0382640550044404108050614441c5032503044080f805503041807808840c8002030308031f40034002030078450b200c65204556207601c1400d000d58810340543c80420340b540b070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 80490685 1250 80489435 80489447
    0x3090c010201090c0603020c190b0f06030606130506030c03060f10080d05070609020a0f060905011404060e0d051f0b030c0d1104020c010f020403030f0801080a1a0c0c0a03020d 77
    0x60050459040074141800500c1480d81e80003510313164200581c8550140c0415490005804074050820103201c138140180460021440d0040903550390700511580e400c410b266443e00d044e103e00740c000150444010003000c40d640029000b0f03500400303031003215009000084c0b50407816681030140022803c280080b4900c081001c600404c1507501402c42d03845080e001612a00940c000603100580320103c1404548d1809000406803880c0c648000c002c540310b1000506001d502e010b042d011170046034a082c5c1c2038101806803011103046c0d946601007031010340d06220b00001540000c64241c801c0340000800ca50b4000724010003036120202c000381c0c800303012040528150500103014040c0c104071b000e0070040782c0740162641962505480140c2d88001204866006040c00541a03203034a201040c080109039000101c400072440c0c690380e43c0d207681d884105040e110000400010070042c9440c801031501d2a40704606030340140c149900b181054945000c980c1094100c410890041e0803813071446080a410032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 80491935 1250 80490685 80490703
    0x24061b0601080604121103091207050a06030b0901120302150906040c0b0c1011070803040501020702010908030c1902010e0316050102010e010608030304110402070c0f0f230909070510050309 83
    0x14441400d040e1a480003010819803c0403c0103d5078540c03940c086d20070800c48010700b00140508600401e2061400d407540984c2c01803d100750400d10001039000c1c82406a41c215100050103d801c3e03903c0c000810034180c2c440d81c4124150f008003040c1305420441e6200c114030600700c601c00340110f8a05403070000d2a04030540c0000c10b1404050004c41c4110b40f000810898100020790002480303940416059001c2c040e81c01d00620941002081200700001900a04040d510030788400c01029255548541c403030040003120080c1e070384440701c801201c005c20303090000e005d40181020b09804001c8404030b805c1000707980801078180b8411300c1c03c10103541e0910461962a1100300204002402c6c003200680b40e110140c8003408030a21480c03071a0b150b42e960740c11030b16955030244560041170b03036a405007010700c0d00511034048400716014001a202055020000c208903c22034650030003920002003101510b401390240341903100700c100c08201902c581079100b155040580314a81c4034030700214080c0c5070071a10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 80493185 1250 80491935 80491949
    0xd020f1e1c050d0e03030409060b1206030705031c050f18030c060307140304060212010f082a010c150f0e0c10050306060d0209130c180e24061b0601 65
    0x5050501d02141c4003007443d480c41d0540f0710f886003080066a000901c1d602441c0c01c0004054604400010b0703504415005029440010034001000e0340e403542010f482c0c010902c03515416420401c034202d000707030080129090b041141c1c100903003400760750360500c421504101c0e90304983d01300350081e8841c2d07445e08010303049112004888040c514602848014616401b6040c2c041400801002103404c0004c0340e010303140905220707002016190317550049032440142d10f20030000940243d9489400120040c0f00201c86440341c2002e420840c0d280000454210111213002e5a5140005882600f08030040c050402c09591918000c100100e40c0280d0b5414440300f900704904c10040d0000032004c0c1038101e415654000c401711031964881d91184581406846484510780e40129090610200084981d00c4030140e56101c1c0da411a960b40101e007200c245104d60300070101e801c00c090307000822403841c102d82d02c24490300200d8608088141d5002044994001c210043c80004040d8629180340c4003c0141c6401823100d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 80494435 1250 80493185 80493229
    0x120204030510140a0e120703030b1c12020703031b0201020f07030501020405040b09010f031e05060906040b0c0a080a0b010306030c2408040b06060304141e010b0d0c050d020f1e 77
    0x6174001907941c6c0c07550050700755603084000c030360325040c14060f078040084000d002e420a008130b9845d550b0008155180f82003120091950801c03840141e04c0069008240c035451f0702c40900f078400c00c2c001d0100361049110202e04607c54516019104141800550001c6108400140c1c88506000421082d40ca4007103440f80540128001000481d0861400900310703500180c0624603071041c0a84074150001101c405031036485200188551881b00044551266015401c403134101d848040101402344074007141c802c0010f40d01d00114009010640c8403207c1102d050400041d0f07241e60340d4841c4188200c65010710480154401034940c0ca0130361400308502c1c808185410449407909a840041e840c5028094501075503003c800201006182d411031748044002100721815103540e8014107810001c0c0c810320341401d50030a00311700b900e4141030004140c1294012815906c0908010130b2002c0741c043d100301a0303032080d6801c90f20816510b9005003444c0190240720341c105000420004e0007042ca2960840001d1040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 80495685 1250 80494435 80494451
    0x50a05010c110411070b0405030304060b0103020301080d1103040819060b01090308070311010b0414040606170a0201121103090304030314030f01050d0510051e06030705010f120204030510140a 84
    0x544001c5901000e0100c0380011307494034000c440907042c06001001013131242c02c10b050006128001018500c203d1250303006014070359112004509034003080c4201d0041d5804800050307800ba024040c00c00c1303015140301c110f03400d007503442c1d41040c64040321581000c0c1203149032611100f07202103070013010062102820320f881c0c0b162035650340d000c00d0b108800c409400c0040880030380300100800c0d00020180080104140010302902c010a200000c007547c00300c51844c5081030000d034060350600000e00070a10007002d4200c4a24a40042d100e081460b1000c0039105d42d10501c040701d100203c03020718028101c00e4021034a86081d85030150650003640403420140e50240200805809a41d17203460541d030b07080d80c6101c0305402c640b820925107944491682c07426410b000c00c01030310f80310030032110000841c01100f001c125120380042c10780308c40d2035000713082c0040c0b10fa5082c0100c0074040c3c2d1948500182d40031005141c02d56941341e280c240240740840d031035025160648801c222050b0030500f904080001c0e03080048032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 80496935 1250 80495685 80495693
    0x301080c061806030a0501050108130321020408010501170d08010e010312030e070b0904060b040503030a0302070c08070b0a1e17060120060603071a031315020a0207050a05010c 77
    0x1490400c0841d00c105000075402000281d9110341c0e8101d25409440b007070322800c044514001600090080c6c42c001802c400006404202c4c0c9802410510f41503111050444205442690208a150451040740d45c08000c00142000240f10b1030740206101ca8004c48200d07902d822040c2004035a540d000c082004d81070040c08126017603110b150469901152600040300e4901007513001c5c0841d00890007050140050000d1184013000c01841e1040381210100031040d01e0f001c2c001618066030013565050b600030311031248103074080d600600300180900a0f04c01320680e6a0140c5291130982c0d0020103820401040d100e52481c4c01c00400494040c4c0c07500842c280a504240003044030140b103941c02e484030b15910100e80c1590056041c03295100c240c4003001b41082001444659440c0251040d42c0a03210703030700780002c003012080801b0f5035000c0100000c51554641e018000140c0200850645024030b075a00743c580b5152142c4000d250350b40058000c0c1181615100030030142880c180d00c128140000007450000003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 80498185 1250 80496935 80496943
    0x60d02130f0c02070f211406041202030c0309060d1413050d11100c05040f030302030909060a0303090b09010e060706050609010e010f0303180506040e0405010507210903021c170903030108 82
    0x180740303944052401405289081e5a080c1c010003c044c1c02c41c904003071610b040510208d00c0c2c0d803203070380a203000b0490052041012a030301c2c80342d03a09040c140c3d0010f2060801ea45815801021019030b041004135520041d92214141e07171009580c03080988244146050400c80280440700d001c4606040003422000140c1c00b05880d0480c501010001c1a40c6070030060925004006031005040105007403210281c491030065075a40c0300310503003407145400e035000908030315101c20b1070010350754594be4100103240791442c0c020f21f031380040c10001d040c00313400410094252680c0000d8a00d15004500c0440e950800d88180840b40d84180c1108000601c001c3c018088000c1141010048a6162618182c1c424101c0e14501080c0502d421030307580035100003800552905080f0341d10780240d001c1c0000f00519140c01c4029980c02d040c0f070050140c01403c010f221903026840d9404100c480e4064010340306881d44044851000c1c10b803103c5c404000c10b2645806404281d60081c11541c040da208004601e1541828106607031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 80499435 1250 80498185 80498189
    0x501051309061b050901020f0c031c020109021009090509070803161703040516090203070921060608030309010c0534050d020601060f020c09060603060d02130f0c02070f 74
    0x1005448025800820110394000e040c03c0c0845030340c203910f24840e804001c3c44d95100340b02e028010b01c6131014100b14400081105032a400c80180106006110f9881a13650001c0015401040d5540e55840c0c401580b50702008102e01c4407295500c1628505017100881180e201602d0f03082140e201c007109206c421304c00400c1350340300980d4158540000c2039528150300941c0600394550312024010082c03104000c00000c0c0d0410000c02021007000c010f440d01c0310303070049000490b0048000303a00c070102000170300c105200c94032100f13074404215004019140c8030001500c1099100c440f1660001041003e44c1100b1321502441c5e44082c50b1852509403160916240076401140c000c907a41e000c2d000c1c60081c528200e204107402a40001030b210062003503440a51101800d20480c004100d0840c03942c08140d101050700380341405d008100c0350054885d0310511101d40c1000344101d4100203c2c60030400940d8401d107851401c010b241c800400c0a540d041c44c4213043d1696145014103561141030240304410321404e00e241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 80500685 1250 80499435 80499469
    0x1a0403080103020f0a0503120c011803090509041e050c04110702090c0a0c150b030705010801030f0b090f01020d0506030c01050c120d0207020925020303070e0d0f020402030721050105 80
    0x4201d840080008005e1212680401e0740b611a4070501c20350440003002615140b02128003c104c3c2d40740035401030380c0083e8590790040000301c140c0b105009602e0008400d5801902490420440b01501c0c54102414481e003807065545078050000c000f05441c0600904951180800c100d9007042d606501190000300f003d009911303028000300b40c2c82c0c1c6d002d01c42c010035000283c0015240341e03010210030800000344244070701a4028041d03401d0108065015180c240c0c1282c1d0f10843da0301d06032000d9142c0e0040e01c0400f40c140b9081d40100d00d02a0070020302400036041d50714a030700d00010356040c0502010b1030503c035001c6690611400b0b000721a800b410114003803050704000c005095854001001c40c3c0c00a2003410320095102160380d0504c50650341300d10004e41107800c5000b5420b000d00c59403030240d0f5280011211940024030002850704542040448218840c0c42000800780c110140d90000b000d98104441c814002032400c06c00f000000c4161840c5e48a4460500342040395506240c04140d01c0e1a100b05100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 80501935 1250 80500685 80500699
    0x15030201110f0303040f060b0108060117182a0405090a0803070302070f0605090f161a0f04030b0f0117060a0504020f04050103050706030e070f030f080c0304060302071a040308010302 80
    0x101005020702c59100c4100344030080e282d580c946458440100c500d840380580380585000310200155000704805401380304141c540007405452014030b89458a401000115070303250710940e50300f02040c1000302c4403480b076030110320b42e03070901c00619440001c00000454503ca070381424140224814046005a030403074010f07285c0d60340e950b0744201c160040e108004000b04500140003082d42400307420741c02240925030642c141c81d021403000c02199500d604000b42100401980f007000c21080d40750f480300801c041002c00229083c50310044030070405412a83c020780e0031000400820004250b41c0c4003180c0034004078600540400f00403600384d6640c20000305010042a900d902040071356944007520030042c08010f200b40000d684a1509644541240c8074010101c1e0500ea90808411070204030075082e00c5130f404844080c545107464911101e40511001e4800120070442000d40720002d0000340080c1c049610b002d03984012520b400403100360450010402d0091003800e04c400640e2000c07050381140c2e0121002c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 80503185 1250 80501935 80501957
    0x603040c0b0406020309040b010e150307030915020705010c0903120f030905010e0a020f0103090807020f0d05060f040b07080c031f0803040608100f030503032202040c020c1315030201 80
    0x280c084621150070922120501240000d4426800070081c50003400c295800c0c004402e00d0310041d5a512580301c6180e510501d460b076102c2c1d1103038401020b154010084c0c540407a0704d402c140c880d00c3e48414541840c10300c2640020301e140c1401000d00480d22071814620707100b41581d00e10781342c80502140b100100f104001c510842156441c0c8642c01500b140740e040402040303110551003c003580d5014604007207024491601c06111290b01a00c0391520541d00700c20303907a01d84801c80d800c210900c0b440303041d040d5010480300c4042c800702c0c1080200d80d04c43c0c040c03101c0300300e510700f000d0908514240c2c0090110702005541002c21421078200000d803500326860350700d051100c071101c250010003400030b500040414480440d00081c26540207405134000e08030403244405141c0ca8031030481c0c16555a01001d80540c0c401c002144900b0700d0302d12031080407022806010461940703a40000c1c141c8049069481c01a404454450402d2034013a54080c1c0c181440b140070030008a401c00c412900103410b03c00030703050080030384c44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 80504435 1250 80503185 80503193
    0x70308100f121b03080d05070e04020f220f15030f0b0a051e0603090d081e010b0d0f02030c18030109050d11120c0313060f08060904050c090703020903101a060304 71
    0x10441c00303035900c4071980c0c1c0c4828410141000522013200d23882c000800380c01d216507150600e4400c03541d01c2041c02c0166072074410000c41e07280e0000c8201d0404071010484020000e0209401d061080c090030301400e0080010766115401000c1e41c0340c8ad001641e40a1a0558401d43c0d6691119000700310380040c1c0e294149000b003003810000742c400e140c036081e422203000401c120242401003500030b228115074940d01f82c0c0b6280c0030802d560305040911030680c0110040c0050000c59001006081849500e81e004264807a40701040c01c1681c1007a00c1115140c000800c440b43d806100f000b1100d1965800c0d002001128140e859a545d02c242d140403c80070701421f80300c0011140702c103201e18a04408004029039581962909040e680e41c0004031342d0380000344100010842c6440b403260380f6098143d503900c9112544403501000010800604100c403d07100740d01500c00d45031190341720070b4440c20a9450050711101844141030a00300c0310712901141501c0d100500344060052206018440c005071001c1d501ea540d5454 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 80505685 1250 80504435 80504483
    0x90b041a0d0c02070501020f0609120c0a08070302010f0f020c0d0302030a020c0610050f150301090203070e0d06140603010606090b0c030909010305060915190f0b06070308100f12 78
    0x45a24007890604122014882d00081c0e0103040750820b90854000030248042e003601c400d0f0507034241c2003a40140782c04075584a650b4002c1c180c43d107144000d8484910042d0b465000700d5012603c200d026035103500448142e401c07544180c116004811601b9440e02c0c02d83c03011039494801140503031007415400320101d480c0340c403e64140c5c1c0340d40015000321042c50a10544000c100b1106210f0795116042a04a031201414205109200e00750f00041460660742804400c40194000a0040d0108500c1c103d07030f0f50f6103586503030000041341e0291900203156030a05100c2c94018000508aa00a0303042050070002e50780c3c0007120f01e00300ca41a0091984a4525200c2e55040d4407030107416507070008036100007005000c3c0c003056150080d0f08600444140b41b40c01c0b42e04101d80d4904503505001410500c1180700680c41e135030001c2041610100000840d112400001400742d049018240c000443c000c080107a41c0102c081200302130081091148105031a24420264440c0703031050052801c82201510120074150301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 80506935 1250 80505685 80505697
    0x4020315040602040f0905090d05191d09041a010b0406020a060b0402040b040f081b0906060304060603060204170708030c06070507060e0109080a0f110705040207030e03060a060e07090b041a 83
    0x1745010810170717a2154a54040c1406449254481c0118006184058000c40c2290746800c80000d000241441c1400d09845070082c3c500011002204000451015074079043e207544258890140800b252005038450400c800050b004410601c008000a000b159000200d008140c1e0b070010700480c500004602060181c012540901440b4101007004a01900040003200a41d07418000326240c0010543e0b0702d0600d251003584450b040f4640700c010650504000c0d0045602a004075008101c89030f0740e65440f012a40258411058030302c0040460510140038045076005200c1178000754241105005d04e2603e6030341c09808242803040000b0540100140313500002c0d1844480c02c0200b1841d19281007154242d484030482c0e4000505034006a00d400340038802207400b020b44180180402d03402c0005000095002000c01e405010181e5440c05841d40c040003010310404919501044007443c00c0c110544440028000f00d080c4611240c042c030000d0100e00559044842180701d0154840001000c413a42d03210300c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 80508185 1250 80506935 80506949
    0x609070602121b07120b0c0f0301140f1008010f0e091902120609070e22020108060607060915060b0c0a02011803080a1106090a0b0606030402030f060703140106080402031504060204 79
    0x1080000404035034070300c45d60b9940d0380144c00d862066940c214442030030303100d181811412518140014004031004240022526002403e420b141000200000c1c00a03940940304900180d10140144450034594600d44010241042c0c08440c0d410b0001009880300c520110383c08103280600c10010070b540d14456555803040240081d2002401c104010940301c500718043d804503140d0b24008160200d10810321520040000c0e80540c0c0c81e0b0b03d19900444042c2c401a000303941c0808140088804035210344510202980f0407035140101d0740c910080801034440760b50088500d03841c24001001c0811001c40c4404219a09107802480ca0300109a0342400359501c1e00040e1174101e01040048500e6008a1040c4a0084110031102c455032090004c680e1100282e00042405500d100441c0c400d00f4854040c41d00079200809032411026030341c003014504002203540d080040d4482c10030310041c602c520f0301d0502400c550b140030480b914198010990b105803082c00303100c80c1103a0340002000c0c000030394181e134060840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 80509435 1250 80508185 80508193
    0x2062515020c011104080c1306180207061113060e0a09020d0e10020306060711060412050a0605090109020f0105070309081204180207020f09090708030d050103050609070602121b 78
    0x103281030000940091400c0e490540c607140d26040f0442500040e50100c4011500404041d11508244040c6143c04c2d00d48030b4030951503403000300340d40721420550b02c003506003041c00585500c0b41d818540c0036220542071403807044000304800001021584c065206030745480c203081c2e840f00b8801000c680c80c42302c40e9014168180c8003051150350b042454001e080c040c1000030450304c1031b420302901e100880c4020364949500403c10403072000052a00304498458400040c8507500b80340e516046010160391681c000c42d40d5070000c1c00d25204011003840307240d41114003d4020001a1516400705c3c0c20f05c9030764000d4034180000442e00d0720416201d898010301a0102d00e064511100f4003496000c0d49800c580108003880c220324512030356510300c5200356a00b85070020580000849c4403028029440400742565049004200380460ba88000704020060b8410405001580c0c0d851424020304020020340b42c0c4602d5044100108101503001840182003001c081009590ba014a0521880c1c41c511000e0a001402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 80510685 1250 80509435 80509463
    0x10203040303061e061e0909020408010c1202040806040308090a020d03021608061005041503081224010e1e0306090312010501051c11070f0b04030905010507020625 72
    0x240c5600031604440c4c04038141c096048801c02d6250100071680203600001c0c600d010a1b14070400008180c02c1036050508103201c03c00d458550801c140da003e6040b0b00f41580d117179000e00c403c46503c89009d03103058075000401c41c2804e017000d81a40d01c502000d4000340c100484007010540300001449034440880c0d000b05807071440d03151840c0181d100e02051a00e10341680c80b90000203040c03000401c1d0140b055000c0d6490022450900e001c01c0010f1010140d00002285c2401e804000501008000c000316482c0805036507651900c1c1012100c01d4444d4100042030350003101c13040c40c26076001b045104401104444050040c00a07020000041005d040c0e9a0f40c184111030a200c20380d50080000c0284040440c4840c48503a2a2030055596110b104d1110fa00001c0b00c0c45080da002c00d840d4440001030146c59811490000c068444ea001440000c40544140200100344402c158000c0350103001441e003820700c10300307020355500064980d02030b41d4612020495001104181140750b5900840c40550003030a41e4050b030307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 80511935 1250 80510685 80510687
    0x711040203090a0b09301231030f080603010f020a0e0406050108010b0a0503071b03050d051506090d11060309030a0e0d0f060209010306032306010e0c070816050102030403 75
    0x31030f00701094403415100ca020070044d44000c03480c1d03440341010941a030031026000300c0e24043e060b0300021040c820f100c281b2210100c0341112581c640180550544800d0903611500c0c002c207506204481004c0709542d00d02c41d44000394001c80a10040b801a09244120307079145000321307000d815000442080c1620010300c41c019107400c40c4515805207000c3e14100102c50300c80e40195404403080c0150707012110280040048940b0410045505c040c842c5005016100d8030030041c00c83c2c1030500801c40108002040b4828170002510407035030301ca0075a20001610900d0308020511078811200780c1c03402510351030241e0051098200507221048006403546e5502d25103000c41980700d0f0415074100c00011585080b40703489107898800080d18942003a00c4d00030030348a903a2104c0095102c000c00c83e06164644600001080aa02c4000d1503085442c0c0c6070100252460310b11030400c00160840002c030540441401001451001070380c418540c8000240da455159400d860415042030300020560760000003044101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 80513185 1250 80511935 80511943
    0x405071a070605010902070b0103120c1707200108060d0302070e0a0608100212060103020a0e0312040603060f0b070b04020105041806030605090a020108150d0605151f14071104020309 80
    0x7941c0281c90402007a601d500b0810242e10509201030300d10f851800041c0301040e040340d01115401440c4c03c00c5188014141e40c2d02c03d4051800c03411009602c80402c044041c00300c2e8032002c0f0030660400071103000c09010034002a001c00303030240c0303024010228402d0100415008001d4500038003410042f002c80d17481c1007a00200501014054101180a000101c600b150404e00a0702c600c804001c5001d5065655500110025080500030301c4c00c001043c02c5964154034240a01032503500a201c8450341c0300d080402c00b4041d00c800346e00080b0140143c01c4100030040281040e1000c00d0391002d01c201d0943c9480c0012600c81c007403504051121100e8003200542c141c1c081d0701a5045a01c152414040d9589021400c0d840d80e110304000307408901038100007140c10141903181c000c0d0380801003629080d500702d40c540808440048030007003a01745903005441c8007860b002e16418852240b210bc0c04941c8010303a90002c0c20002d1440d480780d0711002c0030440c801085080b03184440e00500241c811901da191010302035a40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 80514435 1250 80513185 80513197
    0xc060a090317040c090b060405060d0510060e060304060911030601060207050a0603180f02040f0908031b0702012304120b07140301080309061c060e010e060108011d0405071a 76
    0x41000c8004503003042c0d1044111510564028201ca2081840c0800010180c207210036095841001000003181a0343c5410190640c151481000189450000c0500c3c11800d102c2d00640b003801000f450704615070344e4241c216507005034022004a03071145289440700d0003da0400f10154540141e0002143d0301e076000401e00100c0f802141c10860141e51200d0960894518150007800b1900002021002c5125501200c02603840a0000070780205c3c00701d1020200c1d9200e050031200b400000050015106000444401138030b00d59502c41d1518505500180404580080d0b65006c404200b030707090783d42c420320003d51b4000d0840015070310014050b46058078040720700f02d8520001c00c0c030700340b40c408242c00d0031010b99050b902c210300298a0040c180d03003001019000201412080c6445c80c20102030003503d0702920008000b80c207038042065040070410918500018260b9041140d0000108400b103100300031151130311000c0321040181c0c2c0711410101d00340101604141c8128000d6002186160902001004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 80515685 1250 80514435 80514437
    0x8010603120f03020f040603091109070302041e050d15090c0e0109050a0510050f040917030403120911010804150e060105040e010e0705090c1306021c02030705071a0c060a0903 77
    0x2c0140340c810300039800c90261280d00403402105000a01400f40660310001083d40640314040c0300b03114900c0040c6551408489060019402003000c01000940410f0a0940c607441501002010b0907c40800c944c4407080b0005040d40c155510b010030300b50f6082e40808980c43e0040c1c2c429000ea40c44030172860000c42d00f8030440361441d01d8240050190300e4a40b1400c1d014014a98940c2c481c24540030402100c0c1000c8481740f41c1c81661100e0f45800214589280c003420303002c103005180c0380d24090030003034560f102e03031201c507403c45e414454440c0016482005494140100b4240300d01a80c959052401003406400c13002100c0310b10b8810044c80001c80010a94101c4404442c03d0001ca550035605034203039041c43c4562031003540800c109201d6450904142c5030301454560056080203604071400880700f501d544444056005030401c030306c907542e01c2000001180d9581c0011450282d1a56801d40da40d045071040c040c0500c004150f1141c2940c03a0021580c80a010400b103442e00d00300821040000c1c903c15038128 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 80516935 1250 80515685 80515697
    0xb0901091d040201030c09080316030f02061003020d08090907030603060507020a05071404181b170c010c210e03060f070801140604030b0f070e03010b06220801060312 73
    0x26181d015010032500c0259a0741e015406444660064010b0403401d2294014461003100204844030304002604000030b008401d11120720036820050890014442c1110840d0008010082c03c3c144645040c41201c0d03040e20452018105410890464010601c103942e00035491024041c40684c107130845020303203000780030401075519082c4050344d50781c2e629000104a50002c0d0402c1200c004141c0a41c41004000340020440030b40c0301802e6a24001c828408654990100303044034a4045809049406000c580e03840c1a0740549000c0c205564a00b003030102d0781003001d060066010483d02c01c0030400c40c00d8001c40d103002c000340e81400c0070380344800c04907040d03029109820025006040b40d8003041e0040c003980e200c1c00800e0b401e0040000c0d40200452803103400100410002000840c01c034126403040300c0201507c48642880ca4005102e241c0c02c8a1541c46a814210460346070350b6800122664103600d5030401c1820385c0b441c55012030f50062503004801e0380d4a400000021301502c2e9000080d1207285550765 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 80518185 1250 80516935 80516939
    0x2030c1e0405010212030604060b040b04030c1e03020405040c0e0c070501050a0506184c210609050d02010519050907050f060c0615010909060506121308040b090109 72
    0x14100390069204203801a071041420700ca0002000c00210740120700944045103040d100c48441c45aa8819400303203041800015041051101043e20400901680c0000c240c1d403c0f0000184010310780b86000183c0720f00c3d41c500c045010000300b502501c0c02020791900c4424980b416180078181908080029034543d400c10380003801c0c0c00c0c02c0c0e1180500c0781c20014240154604000d50540d12000018044410759119100e40c295240c1440c520804102e0906074800c07052491094541407401020002036019402203070601540b07218800500385803110500050001302c0303a06084000c0c1060000c090002c0c050205040342d015819003089103d281d00140e07208101070b44886400031a84102c6000c0303115002003105004925010b07020441d0070300ccc0140000d05000003800041d0519234165034400c00b8105800e4440c07a0740d60001c03000d00050030b150078104600d85c54240840d042c0d22511000c05414240c900c000380740c014042d1820f41590750000c64064450740ca0b205c04000c99400555454003042c000b002c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 80519435 1250 80518185 80518237
    0x6080a0c05090a240c02090f07020a0b041112031c051f08010501140117040201120b061303141204050904050715020705040b09090a12050c010c08040b16020d0c110402030c 75
    0x100c550aa01600c51740923540e440b90717400b414600140c015802c41c001c52140c1004038041390b442e180924090072140381c003042038101300120102e01101c928401c0c0c005001c01e0b42441b04801f00c070050b00c40300e0400402c240c1c0d00c110620b2041e000302c4c103090480103c087e4000c5401001544001d0594a00400c10100304041c0001541c4100720501100b40000c1301c0720000300154400e02010a144003503800102d12030404200103409034001c5019842040104c440c01c0050100801604500d0310503d0301401500111074400384491041d07001e910f0103048942c010404014081007a0801030240240c1008204010307031000303403500568400c0b144994100003040e1918a801c041090141070614000d0008402542c1d0708490445c0c8a074104007401414480031644040038044e00f0120b8030150395140c100c1c64036141140d5441c0020380b18100415000d80540c034240c0e00004c1281c9841078904052905a02a1418100c021036181150f82c00c180048280900000c40401a0000040c290103001e1103940c00e80c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 80520685 1250 80519435 80519447
    0x160506030907060507060906051501090e0c0901110307081903050603010c0e01030b0d05070b0d23060d050f120304030e04090503030a1107050609150f0106080a0c05090a24 75
    0x8800031075810205041016a000310000c1030040d00c00c445c0420800d9454913908125401110b00222450408a0b034030015a400141540941001c200d900ca840c00d1200d908026401035280c01c0341440400c1c400c92850310700c2003065904c203030340c010030362991010000c0c442e00d0301c010f550141d24007003400e080101d0168a01801040c0000b05160f44884142c614a00110082e1141c4207003540c010000d04c0100004c82c1051216001600c451410103954040f86030403401241c42d4554100d8414034101d0b900c070701c0031204004080e04000b0840e0130060702080c3d81460b81c204000004052128418160b071004a041c802010f503200d14041d403106e500c605480000e01040c0c0d0707080400100140c008100040700c03100030340d001e120034900f0401e0807030030034003940d0340c80d40f81020540d414510350b0f10001070400c280c80800b81281d840700140040060300c4d4549140900000b0780507200c040703030301c1d141d0350442c648911610a0b100e08402c000c00d200c100a64411000e10020360220015035912540d008440c0840c1c040c030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 80521935 1250 80520685 80520691
    0x1103090303071518030201060515070b010b1b01020315010801060c03020618010603060f0b0910060c030305070c0615080d110304031b0308040b0903071403030304060c0306051216050603 81
    0x603000c0e5140041c15614511079044001d0418a103075513034a00c085000410042c0030810f988a6000045c54500b0401045040c2042045141c0c42c14010001c41001030a9106581c0c1185c04403041d850700c410045084050422299003403103506d40c4040f00300010b04000450160b000c1d030081e218075003030f0790305c502003141c40c507440e280c011700980d01c41e00c00304101951454152044118a07000050425282d540d40000d0b114100c03070b091001c0341c45049900941ca06207480907001400d01c500040114542403024200d14a00b1101a09141d034036000640100e02900c1c8100807941c0c403410800a100b02401c5a4400c0492030041c0314880c812507000710f401c14007410051000160b00d80086040c5440e6985941c0c3d12000d01462000521481c900000001d02d2000508081c089001003181c4038403c5000b41440c00b0368560090f11031031250280001e054401000701d940007500181c0c04501400500710540241203541d01168000d1400302031259090310214403020380102c140303008040107640c0c9082080b640030a03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 80523185 1250 80521935 80521939
    0x60506060c0607140405060c010b0f041e020901140706020703030c02010507020a02090a0e0105090604060b0105090a05090916090b010e04140105100201060503100603120c030504050609010509030109080a110309 92
    0x2100842c585034003500401800016130000945490340764000304115400419030b540c0c0c03a039111140c115503031402081c0f0300280301094408110401c000800d501c0301c1c000d03c20181840d1a40000e0403a050392040c50030141c0d0504860b5402c2d6120480d140140c0207500460081c0c001034a00000980010310600610340108860341c02000007020b11f400b04418480c0c00b1f421214226980c60030000038032800c2c05010301c611840b034080c00c2e041ca0907052071010394001c00c0d221410420100b110b0220f81c0d0f61128900d06441c026036211242d5543d1021143c9001a00070f1b4404000c1030640000941461680100c1d80d10082aa202c1c801d003280307201400151480102000f10100802e00180518180b50400c0d406c0005248004551255124046030901c0d0901040441107070322020148248016034402c61a8542d42c1d140024002120391002481c50240c0c3c040d89108010000d81b18180c0da22500c107896040c02d005008002441007443c0048181e4040100c40020940a031440c07086058040700741c81c050840 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 80524435 1250 80523185 80523193
    0x1014090f010c0506010807030309081203192d0b0603040b060405060102150132010e0105090303071502040306050c0a0804121b05011a04020f0d022a030403060506060c 73
    0x60104100d80111030384089030402c295450100c0c04510100400707402005501c02610b045401c41c00c008001c0100c81d0040c02c100d034003c95a003000e801496003140d80c46098035402d83c46e034035042012013014000a1440801e2040e8401d00c090388104807640d0300300c14144240701000300301022810702a4a02007285d01800350000b88000801606041d0400c035400381d41441580e10310581200c2c400c900f05021b800c41246118509440e00800000a140502100800749a00c000c40b1100700002c160303045001045c0c0c1000f80100703403480071391420025070764910b902a62440215480740300e628029045840309440340c5051102040f1400f1170031045462546055031000c041c0d541d280c548a162940b103404050400044032641071b03100000d443d005101c1403040300040b80c505440e105001b0440d41c00001d00303100741d104000c900c021000f2031046508041081c0009a01d403254001055510154000381140340c190307041c105450b105e004001001560b01c5440100300076142d030406d00505006100d840311306070340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 80525685 1250 80524435 80524447
    0xd1211030c030601090e0108030307030b06071e061b0503060a120506040311070306050a050609070816031505090118060e010b040506070507150306080601080a0308043804021014 78
    0x94450010b5034040c1040c10320001ea182d0310341c18040391000981c00382e0084d410100a1101d19989800b44240c4000201c411500748166034841e8150804800310300032804a841040d84100328203500301c0701d1003800c5412111805041c0c400c000d80706500843e01c003446800e442c9000306c4d40c180030a000480e25030300040101402e6072255001e0f00d403140180d24483c0144a10780001001a850b0300590307101d2420303014049080d0034904244400c24a02400402c148203d000800c1144040c0c00140e000c50080e0745004190a4811200303441410b065420460304540c1503000807400f9125002e640006d944809002c001e110750719220080d107a0020b01031201340d64000c004c10000ea01d8840050525240a04103582030143ea1310040880d003001402d40d00d0101e0745403503040110035001d00025004028010103001144010390740104012001030004241c645664546962075500d146022001d032000d031412a01403926040804842c0c10844041780314000380d60104860078803d52002d44610118211070742401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 80526935 1250 80525685 80525701
    0x45010603151109121207030f030e010c0503240d11091807051002010f09140c0603130f140604050307060605030c0a0302040b030c04021b010b1c0609170a020d121103 72
    0x1401d5511540c107902c149940d015601758071000803c140c40c82506c070302800c550f42d40b5003d0295051a490610140d240c10b000808440c0c004048a0b802031228000c4440b040d843da40015046c0c1c400802c0c5030300062008400d804012881c024442008001c0781c450125036605030009502d295000000c03034040d04241e40800683c1401d81c01680360211a00010480f19904a41c2e10100d64180000b0380c4d10300e03103080c1c0c00c4546c02d805100c085c50302107040d90b46502e1850700700d0030880150203401e002401b0108a00c40c52040c003240c441d42083c00c1603100c041e5401d90800382001da0740c13a001200c040d42da840c60500e00082c2c44ca400a00e407103090002030000c1e403842e441d640030003008215003c48a034041c06842c0c01040e095503184001d05181a0380751360b05022a006403802c0c2d007120301e03c2c2c0341140126070311014148100a681383d4461856444100401c0c10105490400b64001e0801012075068a0104407408651b0700030030302a461743c070750341d85480301c0b18403003145c02d0180d075036240c1d080018001c02c01c0456840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 80528185 1250 80526935 80526949
    0x50304090f0e0d141303120f140a0509131803180504050610081b1b010b01030603030c1707150c1107050120120c0a030806010845010603151109 63
    0x5a2170402c0002100c0d130740e80c5840803100c09080c1443c00049031a40c0118105820071a4140010780350b403225401c0260f1131710040c3c410321614141c1ca121320302c40032a0160035421a0010820b030451034401907003606240c580038022440c000f18621100d2903410303000c05c1c0750400d407207220321580c40240350303e501000024055803030400142080404209611003d82c03101501d00040c1240c44a0701041e120f003203d90076596084918030b0001038109410824200003081c1d12060751300e2003c3e0440024900910a00c6c4240d00340d04c00e0300d40c02444007440405641c41c00c48940e01c000c03400c40058079000b030301800d090070803500c40409020f42030104920603160701c890109078000c0826508124201c80714a4034819036054950081e40705501568810030b145000c16500c809202d8101d0001e0904c580e4608049100001d1291001405030217400016060b484203444201c12144410003100c51b1600104181c29080c0a8241d070b00003680d000090260700700881f052441065140c442d01c40310a420300313036803408001e2a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 80529435 1250 80528185 80528197
    0x11070c0b03070e030f0706021c080103031107050301060b040806070f0206070507170304060204031416062f0132060108100902130905010b07050703081303050304090f0e0d14 76
    0x10824407040c0e80c83c3c2500c04003d1300c3d01d40e181c1100103080207850800024075111441c140005e44d010f0240249041980180c0203a040d2035050074100001820107804500d850140e621581c0d0640c00c1517000a507040d080e00050082e00e80c0c0c1d86c1540c038240c2e00d500c0181c480005500c0c10600603400306000a000610030400340c041a4400c0154046090b910b504c181c81d1a042601e00b0341c0c41c6c55000400700708028800219050000b50f10002c0c210441c0c403221500c681c482607200d1181404102e82441c450b00d520030b00d5481401c210010045020140010780500030040d100704400403641c7d40294040c0000d1005103440e150a01041c0d400482e82c03082c00440d5450740150a40400c041860400303c4c0303a2085001506030f850801008801442c54525903c05a54060b40704c1040c4c0b003020040d1401050005c038070081605d4001c0007032079845075680b5a15401014a41c005800d9003c04180802c560019800c0f41140d90803c00082c03200394010001c0c0c40c1c90701e200440c1c40000ca203020740c80000741e590364009401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 80530685 1250 80529435 80529437
    0x1401030b06060702030307080306030d210c0908010c0306031b0e0c07030e0603070201050417070506070806060d0c0503011d010b040311042909160207050d05191511070c0b0307 77
    0x10030500c80e68017180c907603002620100e4075140c0c04001c00c055400c1c100041e0045c500a45000020210f20104a02c4c0c40c0d0b403581d50011181c2c1d1140640c1e20128020301540009050f41c40080012012420009000700100d0108072010030504041c8085031070504003080927a01010082e1070161101040c00b0910ba0003200100e050108a83e402017090341c405000e188114090f4001064510b007a14040900350204070903100d01260030f0154401140740041ca00e640034100d410b0103541901c0c1c12001440c80d019015442e940541440ca000003800d90100c0952f040324400744c1c07040c0c414281c003040c5658030202400380210600f0240010004104d403c0061040e0510190000440e1446503440c0611000507544111b507070251403804c0404c0d8280108242d6202094800c0180c40301401c2200944821080c810760f841526542d0004041c81810700002040100c00401d034000050700c1c0c9012407060024080201c0401d00c0c00d40c403003180b0440c200880d5030203640310801d0032655007418111007141e04081c01c040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 80531935 1250 80530685 80530687
    0x40504020c07150503221113060302030709020a020709050103020f0d0807061103060f04090c170c06040e09070b04030f061d1b040f090b0402010c0206120c0406121401030b0606 77
    0x5003460343e00800040c40340403941c40c05d50702c2c5040001260a11042e5844107040500c10b001c036408502c1c0202c104034481d1085858000d120000c141003c00340029800180d414021064001404552640182050440394003a200700a42d91054241154000d1201a4020110303803400c0e5841d1418010075803880d4400c102080c14048a611200201d60300c9918159030000000288411850304071208a82c016080710b040c00b04010503a1402003040d01442610b40103001c030b044078001a0024461200c43c440041d00d070781d441c0c50341c50001c41a2010151800c1a19002d0a00d0105001c1c0303004080b2000d4135004005d0002c42491580c1380801080300c0d452a004402407101100c140f44024040041044200760b482101090180100411504001030401c0c91919001c1d5500001e138071130710401d6015409080980c5a0f0b0201d002040181c400c5140da4202e0500c50404c0119039560500039000b540e8443e540d5900741000c001070301049400c181e0844801131058001007000031800400340707500102c042c3c005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 80533185 1250 80531935 80531939
    0x10203071d030a0f15020d27021807111501170304030308011a0c0a0b0702010c030b15181f080c07030e0f060c01060902070209060d020a0e0408121812040b040504020c07 74
    0x90303412038004581f5400300e0750700c5a14140c914404034800c0000c8101e80c1c5107840c0980c00302d03800a10301100b03400040c110406c0500000703241f41c0c000c84801018000d40d106540c4401700c0601c5503e08840c0074014a02c1c038807100c02c1c0380c403544040002640e00ba6640b648070481075034200385100c0301c2c800082a40262807041040082c2c00d80c607081c06803009052048401c102c45007041c01c006402e45114032200020185401010041c0365150f0708040450340c540f41000d583c3d041546010400c60954603699a0010896021644000c15051103484d5050b00c641e101c1d00f1586900541340d07014498440c0240010304108850840d62402000c007100b00a00100034624002c0001c00440c20b5510a80c803148a16a01088200560806090140d4040403c0f00c0e0b44920481650000d49114010f000f002d082201940001e02000a01000c8a52407108a81c00201c6407500d5032594a0761500460b9542141c040c00c040761000c80c04c01c0702a541603440d12040c050620781420140002500215001001e900c980100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 80534435 1250 80533185 80533223
    0xe0c0a12030305070806012c12030a080702030708041e050306090106061202090303030f040c03080d0504060c030e1b0a030c0f0602070b04060203070b0423010203071d030a0f 76
    0x200020100c80c04038410300c00007828003800322400180480d060110203410017039540e0f80101d400d05500c5030320320303051040603c2d007440c0620720280800341c40c2c1140301d01d2140c0b07040c030b10000301900343c3c520705a0790800141c3d10382d18100d843e80609200105148024001807292410700410503078071803060403003021030703c0e036400001e45040c60640340c000c2540d550300750900940e44d00615050301081824420340c40e214880001c01e07581d10005110f0125503080c800070808119509102000840d001540b00c0d4480b03140e651340d074000742825502116514580481502c60900034001e68110790504005450441c0d41d42c540d100358a80346955495100c0b94801c07010000801c0b44881401412070030a044010b9400c295020b860115035070800780c480542400100720581d40041110003030341e8020f902c10130648030380c41c0410542032861035814803513010350003080c03501d4415409144070750702e941e0350207203800001042c20f51402c03020403045415400011000001c550441e0317503041000d01c18400c0b0105401c064074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 80535685 1250 80534435 80534449
    0x21f0e030903010f150b070f030f0c0501090506010f09090b2409011502070605030c030a02130302030d030b0406091e23010608040209071704110105091801180207080d0e0c 75
    0x4484400e096450000000c1071180640c5c041c083c200c800c0d5004d103080115111219411840c800042c00c0042c0b1115040b0868401e0a001c03c11942c000028400d0318020b2828a442d41c0e0240a50810281110b000140100300742c0904500c203034001043d060180c0711f01c42480041d14482c595980c40081031166032100e45c8407413a40c103000301440080c6200e0034010540c02810403c503a80403070100603080c0240290b0202c40310849801c0140600010380e00c81048240e04041c000d40d03403019600d406a101484091034254020a40841044404018040d143c07100001104e03082c800a01c00b14406c80c1d81c40c210480d240d0302c503506000841c0c0003800c00005044110449000c00d070480740009401c04e09120841c02d0420ba41c0b60002c00c00e0901000d0000c03000c9582e0310b0048001c20150001d040c6841c0100b469018004440c1c840304003906030000e41e10711460040650b00284208980c6041d202d04100300548144266a03010745d1100710a071600550001c400d0191540364030510207030048540351050b82e070b0f0b000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 80536935 1250 80535685 80535701
    0x9061b02030c0d0602070507080c0102060a0b031c0f031b0f0804021302070c1d040b04020105070213060b0702120115060c06022a250603020f120405030c0d021f0e03090301 75
    0x554090b0b610442c45c039181e400c0080d541c2c85114190301030b11246103283e8010851a80c001c42c0a0000103f156698000901e4a80490002400070218042c01042a0760003250901d212034551414064503400b5a40c50840003800080032000441181614400c5481100f0a50300b15000900d81070190351004600c5049038401c000446400c80080020013804c01681c10013803d26034614480c010514080d154410307541e500500c001d04001000603100700315521020f104100344182c0c4810001c036a00c1da60444000e5200901c20f0384200c0c8046a007028040d01400b81416101030744121003447d0b403030914140c1b140641d41408450440d028055071440c211001e9150b21402c000c2c0c078441403400c507054825402c00e2060201c40701c0b00c8406002400e400e032030413191442180c0482c907005031358a40b07080e000c00c02801031450f04194450030174240020303c04000041d2001c0c9443c00309030307002c90314030701003e07a075451451754014030404411002029821069000d40e00e415254400c1d03d05c6c1522240000342115048 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 80538185 1250 80536935 80536943
    0x50a2303101202090106030b01030e06012c15120f01110a080606070209041b03060e0c0306010b030712150b070b010f060e011b03030e031209010c09061b02030c0d 71
    0x1104020720401c0c1180d070000140080c0100303506105241e008200500b105000720403c1c0344c0c0301c0340c80b411264880c0d03001c0511041d0f07590a46a080d612803240c0e0b020990721010f4052141d800440024440740c000c6000b5018401404007516007a5812040c070861000c4000460581d008110080c1d900381002e018862100c086075900c203541d50003030800039010010242035507004040503c00c5a0040e03c4202031941c00a0f0029800e204440f050280c94000c4401034000a0003941040112043c24800180b901c0000008400381c40c3d8603130b2500188031080c00103c520a00080c0d00d0109114587c100e540940035030016010101c0a8580710390300e00072640c1c0035000880d1220b0b540740042200800e060041009403516240c0242e56138030110001b01104040d80084046100d0507440404060003641300d001d80207003100036030b41c403909240c0c1c020390000c0040340c00010310350034801c0300b01c0110300c200311040c1550390a80380c03114083c40401c0c1c0551005482d81c000c83e003621032950100c0056842c0b4025517121889 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 80539435 1250 80538185 80538187
    0x1606051e09010209101d04050c041703040e070c0c06080403050f0c0c040606111f090f030203030708060a1a1803060a021305030610150c020402070f0203010b010905030d050a23 77
    0x4210038001e0581c170080e106010443c5001045014900f590301881c40420200ca000c12a074841d400824030600c1207a02c050000545500380d009841c0005c0041c00450f01861070038840381d5035401d001e80f07418450020050503100d000c60305000d83c0d03006014558001e402460114144100f00040140c1d81e488480000b6032540101d00c920094941400340d007018080c14078040101c2441c0000c007554802401d482144215a8241c0840202e1142c0d44030002d0036812190841c000c003020b08000e900c0b54001d0701c1b0030000541032000242c0b1400c14161440c00c4911108a0000042e803000040140717070080c198100d6035588200d03d44e07013945da08100550044004e0440103079920381070603c0c13150b40758441c0d00442c065003008040040b510b00d20000c5004079400051050100560749000715a81100070b07038001e60080c80460410b003480505001d81100610a03802001344c044110700658518226201d0b10394160700c483c0c0c180101c42d01c206c0c081c0422132071a0810302d086a8020703114158621040b41d610f14a164 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 80540685 1250 80539435 80539447
    0xc0302150a0509211c0e060f0718030309120602161211070f05040c02030d0606030b090105030318040c02070f030f03080f0103050703020609130504050d020c04021606051e090102 78
    0x80c0601000000d40a0034540914002e14201010302c0d6018401c2c2d0380280d05071421040c2ca10170126042982c0c0c190640c003c0c0c80142c0f5180f074019054a0040d42c0d01300025031086082da1108126103500c4041e039407d41c550f841050b1505c0710b01000304245c010300725502c0c0c1d02440019020720710f07034003c402c04038460000400302c1a0240001020140101c6240a0035401941c041040d00000034201c1c0030b42e5425140440c03c40c105101c268078520130990348042007454441c002503425450f031700c40c4840000c11214226266620000c00d40e40740500c400100820a180407140502c0c9401d40c410162400b071801540d40d45951078005080701d480550090365181c0c0220800001c16511602c1c030380cad2294100c2031a8010303504603121213942c2c0b40203000080c06580c001849000d03540c3d910002d800e01c114003801c18012850b1600e069500c91991301d69071000343c4079400e05040d1601d841d0098448524085010b012080d001d91202409030501410005607212039103500701c810810a010780340304411070400540d90f01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 80541935 1250 80540685 80540701
    0x20f03160e060a0c0b1806090d1202091012060f170709050108070e0421051c02030105150d0e012c070f0608060a230405011e03030c0302150a05 63
    0x8907080100030b100e80760070001114030070f4108000e000c2d495001034010000782d5907410b0306065001400309121041c0f24500400c402c1c00d00004443e0071120403607030f40401b0001540030f00e005030b0003610311665010700d40d594051311091040b0034104005010100100d080c55540081c0742c0c096105070800c0046c14040e01c01c0e21900e40e0304114141c000c0c101204100074940c5070103e40ba8580d900390203980718011004000c1424030107601001d003188092503840348940c0464100252860f8494224405c0d00f40341240303c8a43c001041c07090b80d04803200a00404101c0d0051025200168072614803a02030560b1000c107558502004d104800311007001d181c9803882288880c1c2c0040880c4492800070302a644155001c0c04600807409080045070810708000c4645d172508000204000b0721500300c032080c04100b2440344d503c0c00c40362002c1b80c1088020b4a040080d0790300d03a1220031941621502100c00e10003054000c000083c4211050360b40c8034040d1040d03030000304104100306003807841075a4000c000d07a11070003405001c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 80543185 1250 80541935 80541947
    0x70e0903090a1e18061d042001020d0e0102100f0501030506100b07081818010f060206090705270a050402040e011509110c01020309030a02010c05041d0406020f0316 72
    0x15156203c3c0c59460a05481d60a25250205000c0d400c0108111034401200f0041600018060064030002d40c1c1c002480341026007440000b00ca041e01d0a000280e48041c1c4041c0c000e42c00000b41e5070680c040d00c0c0e41c4030100029203035600760b005124118465511a05c0070308440b445401c60710302405501140b030f945941091468510040c040300c00c1610f551004100c0070f0400c1040340c2c0150341c8008140d8840c180f607041158041200c1907002e4000c0c040064090b00f00c511400c1c048c0c1656480354010390700d1607d03114100e0359a00c0484074080c0390383c030803181440039141640901c80e051a0058034501292000f03201d801b0038060a031280305080e501c2e002480210329007400b030035034480341400003003201003d09540d10000242a00c01ca01650b9503c800766105550008200c60008425000070343d0f0f68140100742559036444403100d04015403820714041c00c103070303c100110ba0464900c2410032400209043d2048050040a0001c941d00c1d542003120502d0503008202451183c6071540d01000c000034092009046 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 80544435 1250 80543185 80543189
    0x15050403020d0503071b06020c0319180803040b0310080a030203180108040b0402120c120f06010f0605070605060604090e0a120504080d080402030307050109050d0e040606050306060c070e0903090a 86
    0x5116041c802c000c5244c0e0b00541e030048102c810020142c500120341000c074000d02c510511a0450700ac000354030350f40c0004080864414040991740c0c4000e0841c280420640c2d0340c0c42e40540c05075500100400c0107407032105006160084050048003405d075a550348082d28020944074200c0150704046002e061035045a1a243c00345c1c0000e080c00901031500d0382d214072103004002e000a220354914690000718170020400c02c41c1088020300741c800440041c0c0843c0303a5074824420110400e104000020034106000c1e00200221a195101d0358189990b40d95480054030000b0314054020f031b0140030004011500b4020030384040c41c1c800140400088509048400e20341e08105601804002c10013002580000503124442e114940780c0700d941c0c0d842d2840000d0461283c01740140c07007982000c814400713000c3d01081643c0900030545400840302040c0d0288000e4a01c148903a401140052001131002e08252006050401c4501c0607909880d846514502c40c404c41503803102c141f94808503a40e4050708040d017032580 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 80545685 1250 80544435 80544437
    0x81b0406120308010603231f03061503060b0d111002010b13020a030c090302031c020a0b010b03070f0c02090103110d060c08062d040c050d09050d0e060c0a030e0d15050403020d 77
    0x44040c1c0038100c0300e81100000d03190b08c0803800c54070a40d021441200c9015005507034000d00c00d010194038a030182003841710b503000c25240a458000c07000c1003442c002c9403101e0443e5010000003c21022101004640f1850050070700647d5200c00d0406010780e40c006003025040c40711100140c0300c07110008002c0456a0314140c600c28010320440900242c0d400068000c0780c24100204070084180904040703041c0f142050000f00701e10750003c000319012002001841c854a8290f8403094007030700d841800c840220700064080c2d0440e28032030040c00413500e038900210002c040a4080c00091a0076030324081103e020030f0000c0006441c031024486646000348a4000302c440307466041010305e44480e0110030b00e950500e80f480c8510b030340d03003102041c20340200c0c04e81e0409450b8400801c041000b50520301c0c6ca418540d82c0a40004000700300e0340e555445d104094441303442000300149056081981c055400c0324210200c40e42c400f010092280c0042c05001c1d0070b00c2000070900000c00d0a040a00d40641f0f0003256a01c41c82c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 80546935 1250 80545685 80545721
    0x903030f0e0a08030910021c11070b06090a021b0609070611100e01110705060a05070c0b0f0403020c0a0801060e01120b070f12050c13080106081b0406120308010603 72
    0x240303050714002100602d2541051589a4070740382c2c00002444d115610305045c0e0314500104048038101041c699035141241611f41c01e10400d0300c2c801301d51080f442342c040c0082c8841c0001700860181d04105c0c5489501a124030401461b0081c225440030540301d0741038001c0c005034051010018010418414000200424100b40024100600c0c02e070782c480900d008080c107060350b2400d484d07841d0002500050801500400f07620765034503580c20016100d40049808d811200d09181c00715100d2441036411200c03054000c0e00303081d102d848814842c550540058015011845001c20203841030755450440f000078112100002440c1e803515480a8402d541640442e1600c7ca0702080c03080410707618240280d000002d841d02c0f030300c410084031041d6040301d091001200c5503440c00b0108036904034200010b00700a20310000300812155034820713950985105001c0c04c0740d0b41e00040c14049030140f4070b4402e0000aa402400410030a03110b042c280e00c6001d0000b8103500013210038004224280d01845011b0b5141c111817008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 80548185 1250 80546935 80546951
    0xc0e0c0904060503010c021207050a230d050304031b05100f14010503010b010207060804080d09080405011803021c0602070b0f0712050105010c03052a01060f0602070f05060c03040e01090903030f 85
    0x48d40310074002201c0c0344480390001d68902001000d0000103a01c683c0072030b07242d02c01c840e185a8003007112004c60155509200383e0f0410090a80100b059078422035040d9505866911402c2c40401d81220b00c4100b200c1d40c0c400e89594140b0142d89019003075010003103031400910040a54503403242078034180c0c00280a40d07d000110782c0e5503640032510348140c0e100c070b00700400c040d05c803480c014001d480754500030380711503141c1808038040103000320040080f50b0b400d0340d41d040c40c4008a8982c5801d13600e41e2100a43c888002a0040c480e1850400e40c1d141e00760107038100500303083c166220040c412808030751501c8511000b804200e8071036004590742c1016003c5610403c040d60500700040d00500d4141c0d00034051010211310b541c0c020072440d0098070000c503242aa080e0107942c601815021300a1406103d03884c402044002c070b8030794400140282191984054410300d581380c1410b1191a40c085528103502d0300007040701169244032017240d0303402001d1001c80000c2c41002418000e080f06d00c482c1044018608100344 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 80549435 1250 80548185 80548187
    0x1518070b040b120403110f030405040e0d020d030c03020d020711030105010b070803070311090d06050403090902180f030111040b030130020906040204170a06050f1603090c0e0c0904060503010c 84
    0x1034603151200f0700700c9a12180c40b0350609461040d12042684030600ca0045402800c245c00301c09881100c8041d1414403000c1780c20112139454084410303d050041c1d0040c036810070700c90320075085070038031999500b0014a0007460742e0101042e070b48464401e0f00c018201d00860351980c1024030860340104042078019080c0100c6130f031050144d01c0050000c1b000c158403816507050f81914442280d058000c0140101c16110103490008003901d011242075010804001e00014410201c0c000c65001a101900d142400c1c1821401c011400400510b00c41c1c0541d0f0740c95041003800404001000540803a41d545601d0b5032400600045040054213103403046041400c050450300c601102c814803003039040f281c0300100d43d03d1030003050090040c1d921a21080c4400b6280c100c1081001c6084c40e83e441c054031052040b43d80e100b8902001043c00e40364005c0f0120190340b203108551080c0e001301c01240c443c06010b519550b03100c00280c0203480642d15400c0c450300014501e4640c3c54140300744001040705030000d101190032850 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 80550685 1250 80549435 80549437
    0x20a12050906040e01081b09130605190203010609080606040908091c0501052d06100516060203070e1008090d0c050c1512011403030301060c051518070b040b 69
    0x4405024464003103011202980c1d41810340700074040b5131420b003080b5a03403548982e03580d0080c0d141e40c003240003051000c9245420301c15019841103c0c4000541800c6072035942d10801040010044442600d11140c541f60039505400218028849540d840004030b01708451941444409049640709a15104c0000c00059843c0c05903410701c201158210300c00c0603403448660150034240d000601d5035281c08100440492600114130002c6142214400005c005003143c40b408441503c10940c070100002880e1701c0c841c41840141106009807040f000107034802d031b55a200b03a0704203895a0300440e881d18429a05400c0041125500002615007484107040c5101e010361540301c1e944814041048030302015003800300c1000314070303141c0c1d2000d000b071003400488221407004d0390010145000152040000042c00d000404200000000014041c518591900e04161086000850211041d02410041c0c43c800c0202d51b01051003016036018080068103403000b042d003480c01c95004008181c4060000707208200c883c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 80551935 1250 80550685 80550713
    0x40c0f0e0a020a03020c101a010e061602060c03041d1f0608090a0803040c050a080f0c01050304060b090702070501030c021504020f0301020f310b0d15051503010f06020a 74
    0x700680e0b815020034202e010f032260b03181c400e80900c950841d0615285240d800901103030010910181c000d41408011655860034070100f56000300705105030114030740d940c440703090000d01c001e00841c0f4055000c2c000d130b030460700309500900302200c2da005001203d584403d0140e40c003621141c15691000d001c054841030b00e900501800301084502c1300010141d0f41c0400040c02c03050b81000c91143c807840d00d454508100c8000e809001d005808120002507a0000000e02c9c034100382841c40900034409480f0011100f07600010800d489840e220340c800041d03629031000c418040c0c001c40d4054041035040000240644201203440d404543c0200508140c1621030a2540d0f005a17048483c00c85007003003480081d01900544030030140440000031a209018640ca040702f4003240d0316081d510f448140f55203503a071290210b203d1003110362020800703801d42c02c0c0a45c3c8008043c100e814950001942c40d5404030f0620a84089100018400003005025a1030103d5403c001050781e031008042c1c80020b655007980e0f00003070f4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 80553185 1250 80551935 80551951
    0x12020322030e210706030207020102070b0a0c0c060201021803070f260610060e03010c0c020405040c0b0d091b03050c120309150703080709030b01120201050702030a0803040c0f0e 78
    0x800d216410107114011145842c0001800c84590300850480154900c041c0c1410900c40e206440d800200c86000b8001c0d0341d00740f0b4058002d0580d1515140444c82d40d5405043c9150804c5079400300300c400501c00c1c5804002070400303a0300040c1c5501c043c14981420403da00c585070311a038480401008020701440c1600160360991218000c103c0c5200050154425200280302880c081d40c6c0401001401c4103540c6822210300e6174400c00560000024903081396004280c200000b00c40841c0b600260400b5000341d42c001d4402c4014604039566003029800e180c100005643c06281c407800084103000002101050000e60301c00c81001131442c640c3c62964421601884034054909030115041821091064920140d0068421103031a28014100003060b48505003c8002c543d07040b001c200312521808184050703e6001d1580d00c4140d00701020504130480c0c820313042341009820004035005841c140006210244a00368650716420140361045050385590018040311031200300800a074050350700142c2d00000b107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 80554435 1250 80553185 80553241
    0x1006180b010309080a030b0907050403050c041a0405010f26060414030720010f020f07062024060d030c0308060406030f050601180902010c110420030106120203 70
    0x940300050380074240156000e0074405001c10f0f00c16405405801141d100442118004580e691380201610f040c01103020241440d400f4104454850409601000c80380010003c4400341c80b80160015090b14800d0300488404003c0701c0003041076418a0b420309080b200070045020046054074075140c0d840e640100003070140100048201c100302c10900807200201c0d00100c04941207001d18018541f040031500340e40d400648a941180803642c4041002d81041c881c50003c1d000003458018100d46400110344015484900f1501d44601d101e0100402072180c01c1e940b01c1404552248030400b22032420007054603004070742c22031010700000d502c01101c44403c0d9042c202505a912448042001400540c00040004140702d0f07031a0144480021414100c0301040c4041c0000d2042c1c48034181a505e4000c0000d0100d03900e034501e980010f6141d001c5100d000c074060030008640e0068980a60b0b03214010807030080c061130000051007025484420914901e0f2400c1c015880c504002c401503000c06890070002410a0f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 80555685 1250 80554435 80554451
    0xd0e0303030a15080a110906040203040b040b0403030e101b090e0103060f1401170105010501031104030f050c060f040f09050c0d051504020307050d050105030f0607050d090606030305040305100618 86
    0x103d05440d20001e01109000c8418a44061803c04480f094040c18139200ba581a8006882e81c9003900850f071123203600071840070309511160b885411105e0b018004806041c0c4134142e0342c464200401c150721864200310360102c4e190030043c2d10710141140820f400ca0401442c95402c0c4a10a0442c4030b050440703610200000d1102c0d12b6080181c003c00011201b4022207020000000d00401144000341075102461300030860fa90382e540c0190111291036104010400c0203100030004144040c960140050003001621100c403507070703000150658484007501c10b04100c0031a0178030041c0c2c00c4118007400340185800401c001d0170043c02c1c10b03032540240e0580c1c1901c1034540000888070f02140d0440003e091020b08295103c1c20503072805000c0e40c002070b4450030014038220001501d07250026900c104100c080b00604950380b03440070100e074ac0e035001c80320100c0d61036103d40d0841c00050152003444011802640da0588450452a01e607007003044075141c203400d41c1e04156091002641c455031035804d04021520004210b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 80556935 1250 80555685 80555711
    0x315090a1b05030403050c070b03011706090714010e03120c07060201050f0a11070606030b090d03050c0307080403020a05030f1201171c0309020a0e04020a050306040b070c030c0210020f0d0e0303030a 87
    0x8426407140080238081c4c0940040c04511705405141600c585241d0f4901400036850661b5070b0701d50843e0702c01d4683e880303800c0400c40740102c0c0800c900c0d941010301d00f006c8444485030200e85809070070b1005c41030000300000c2e498845042809500d0190445200a01c403606000303098170015000030303150103115907903120301d14588079100040340e07007071a40104140181a56410086450002190034040a000704001141040c1c46440382610070b40c80841c5460a43d20f80900888078050003c0003201984a80e44419001c10000c101810102c118626250350750412003420941b0580180e01c4400310607031840d190311005c40089011400c41001010310001c5000d1800b08402520350400003a4101c810300c04042a01e500061800344624000c0e1400717800140e40d0b50a041d40c0311801c9801810300e0041101040c0c140740301e0340d04286500e029181c0fa200d40001c5400280095000418000150344a0170082188110a10605030ba0b0311003410071000c1c04008001180d100d02c002130240000981c0c81c80520020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 80558185 1250 80556935 80556937
    0x7090f051c060c080406180b040b060a0308070f1a0c07021219080c01050c2a0102070b0f04030905010e0307140307030c06170a0603020a14030c04020315090a1b0503040305 75
    0xa4000b04244440ca0f8100b00281c142c030029201a2112800d010406105002c0001c1c0510001d41c0a407500c42155696100d0424212002e030049a00002241d0000040741c080006410518080d61028026000500e007002104004c103038034031201e21842c4100b140c101c0000d4150780d949601990a000341c1000c0000352406c266000611b1b04280d50440130f10000e1051080c00b41c90070191100c000c01c100e0b211001c0840150213000045080c1e0104070310482c01407041502880b6544040d10000b604181a951f20188000022291104030a2a12040006051b8848030400c000c000a082010f035410011020984545003801900000300750742400d115070f0745003000528002c6400c407100303002c4076440d841b0060500145010307085c40310310a0700120343c91081a21400c01102d138001e03c1e25071a05d191480344040c07840c1c40e004850f8540501200001c0544650006510900c88601181e00c080303501410400000c10150075155a00d01e807020345250a290700342541e012a42504001da129515458101d5076 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 80559435 1250 80558185 80558239
    0x10c05010902040e100e010506062205090703050916030206030c0c07030c0b13060219031b0f0b0709120506041b080304030303020306040f0c0207030809040e010203040b0103030807090f05 82
    0x9207007440300c00342d2400105d0240030000c0500c1d01070003502050801a426150700390746590788030030104005003240d00341e11558030000076101c01420849070307501c0010b11442d5088a00d800801d0300c4004000c07032601c3c117001d5a0448251084049007060641c0c000ca41c15000080104003002130010f030b0001e00f524200b000000540d404140048400d45411108102d500000e4295010034502280442e003180045180046800788040088200c400d5407000c03290084204020640480e00722145808550411b680c0400e40b80608034000d01c50802500050421400b0ba200d420100f82d40c2a003240094030104500350040c0d0800462104c0b10302d0b06c101c0040c4040c0301c0d031000c201444000350001c09c044d010f401a603c900c0c0201d508000c4c2458440d1003105403840d100e00000160842039007030001444141c0984154034020748005200d5556031890b07800c82c0d01c01d41c1d05441d0b0f000300d80b0041003011390240c1c00640c010300c1840e080041c2c43c0380403c070220754442401050301c900901400c4001000c818200ca43e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 80560685 1250 80559435 80559439
    0xb2b021e0405040503090f1005090423100608010b040b04050d0201030b03030309010c0e0a06050316050d0e0c03121e030403031b0f0801080706050a030b03070519060305130c05010c05010902 83
    0xd600b8607107462903486c1e00040042c1c0c090401e45820350711134a0100120a011760310398881301d03e0881c0f14010003005040a03c0340c480b00303225241030440244040152144292801c1c0d0b80c40300f0440c2000b001500750302050f4444001d46004200034003450340e000d000d0701c080320340954081c1121409440181c01400104010344e4040c40088100b213050001500b0504c1c600ca0251240c2826585140c1400000d5a00d07004420105404001003030020000c0c0c8030610b403d42d81407401c0e80c2410203050034a016140b000310a4000ca500600e80c00041346070902c00c428180181415941c680b0342d0a0055802901c4130742400340c2202000300009040c14025003251150082004c007002c030010164001510300c500e1507402c000050038000002c940780f0400103426050b82c0a1340c075014203019000e403044002e41042c11041d03415005a880010311900e6402c0b0480307202408030790040070700d404d01c40000c08907017000380031070342000803078110074003182180001c002998001c1c03811031040c00c09414080d000d00b43c010b40080d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 80561935 1250 80560685 80560691
    0x1020903030a0815030d0c020f2202130f0531060b0c06160503010519080a0c15020a03080103020603131703071b02090129030a0b2b021e04 61
    0x30b80442e8007110781841510640006000c01110340241560792118091034408a1150001c0c030002d441e122100780500c2e00c0003850030001d61300c3c401541c1d444c201b03100c0c4c40419941d008901032048540c0c541c61a00500400e4101e25645860003001a1589461282a10858149a80000d525079014981da0b452001030b400601030695a40307039000c0e1310361241c2031521032740c05a10042142c4200c1c40d000890710310100d80e1001d041d64200010421460480c1900381e60060490717200255141052010b021414000c0d410500000d10781000900040b585000c0ca4045410294807100043e400084403415240c060700d00c40d49a42d0740080a0760080404400944a202c0303001410482600d000001c6116211940c0c40c040501c400c5481c0d101d0714910640000c1d4406000c0740140840c0c80c06100c7c03482d4003003000c0318460b1848400300c2501407c0d44141c2d6a600c6003910780840039020f041561400d5190211400302d03400c40741e01c594002102c02c4c0300d610024031424190308025205459249019512a0024020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 80563185 1250 80561935 80561947
    0xe0708030403050706090902070b061c0204110a020127060f02091906030f090c050d020102010b0915030d080c0a0e01091706010e150901031203020d11220503100e0102090303 76
    0x859602c1c42a07204400001d1142440030607c050a4000d4443c20741c3c0c09140300c0001c0c0c1f01c40c4200120f410201101000d00c010052407100541d031240510a4400b81c1d052400756511203100c0c1c02030945260b014a10301c40885e24503511049442065903060b00c1c1d81241d00020a40c02151062000c0c0c03040ca1403455105005403010801ca400c02000f07042100d503182c404101444401e10b4100503640c071003401800d141903192040210341400c12000030303542c0c0f0510002515455940004903045c0081e11009051805144869443d040400a05c0c031252014245441c0340d1802031401074040c806d00d0002003c01c030401c00010540e074004c1070108054800350740c60018451171005600e03600d80b0b00b4800c885645101d0008102c04000104004983c49809400d1105030b0b0f00350b0311345003000d000490799401095420018401e8100d52407007050401a5590b800555640082c2c9180400040460604103040f45615042001782e0303001942008164842c640851041d1003100c07920700902861300d58a4044c000000c030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 80564435 1250 80563185 80563193
    0xc0d0f180e1806010812180d0804080c0d080405040902120106060201020a091410200106060f0e12071214010216020117040206030a05151f030e0a050d030e0708030403 73
    0x80754402c80d4419100c0060800300b06040340c1e41c40b828814001d040d00111a100b4014411070020404005038294151001e241000410321290120324195003000001ca018801340d4400d2110340251001240d1280da031800039100c0030110300c11441070510555a0b000710b08110f4491103170045000704c900000b08a407a65a583c041d0103548031540e10000506801e0004c24803100c0e8040d1040c588101400203c0c070a00075807800c0e548148440d00b4441d405410004a20300c9800034007032030018010381c2e501c62100e00001040a02250218050300388940000d41e284003410900081d954100c030b10741c01101034031486c18240380c42d000b00324021484903940001499020081c481f5941101d1074402c1c2d81e082000d850746036031520280c50035103009600407420000b00c0c2411030250130558005000036aa40190075006d030004803c05000416241d5062001714030440306038040c8500c614040100740548000091686d4035629141218910814903544110b0304041150401c440006040c02e601160b54598036420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 80565685 1250 80564435 80564459
    0x7140607180f0b04060809030f0c0709140603210f0408010605030f2103060604181a03010e0304030f0311150603010f060b030a0f0f0c0507060c050c0d0f18 68
    0xa011004511075600025240d002c00d0414011a945480200d08007810071404807a60480600054000e12050000080b0b1501808c0141031030013800001b0038100340340101c407030140c40c81c3c8461100314002020400055850100d99556050f8001c68901100d81d585090b8480d1401048000000000003060104030440d05501020580d50704070210303840c4030140201c441c0d50b40104000d540000d00c07800868210044c0b0310020f1600028024a1141090348511240d114484218a5248800d8548480d06c0c034411018034000442c8109070020b1151040d01c43d0b12540d00c0c072031031100a01602e5640f031040245841407070f00c1403012503928207072440202c0ca6003180348440c0e019100e0512952030145607038031940300d80c4103800450b0910f0180741d0641c0c0d124480704009100c1950440801a100c1c2a034000c4400644030707200fa600440e403525904d50040d82401d40403100420156001e1000c03c00c007a50200400144002040d10f1070724084003108890354040f02d00e0146e40ca1a80b500c031000410118000750900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 80566935 1250 80565685 80565707
    0x1150c150e06010e0f07120506030a06020d0506040609020a020307030e0d020402030c0d0e16030b072a1b120f06060806011805060102060105090106141606090213050606040b07140607 80
    0x140401c6032a1107417030440c40426420b445000119608a22408580101e5045140e01000081c01d58554124039110201a64403040742461000d0342c5e2000c100903840e0a10404000e0002014118140001c200000e9030301e02c03800c400a01480040311010722695112080444807650180095449041c820040c100a410100e18112501d003440800f4154001c001140101c51102c1c4801003070340f03031441d200e0a000c03a40282c4060100804503410100364038001040840c0304001440501a40480c2d003040301d0448414200340c15000040c240c10481c0d1101c500e07004a02c1ca81280038024200c425161190090246070300c008040d010741400000c08250524129801401465040c4101d07034132207004980364502401159405500e079001800002d20800e2182c005c146050800780c40c011042105506030202c00c80c046404a854100100440c1401061040741252258080c40b140c10300308000340b0103014070300640c4e02240c40424080248001c0180900c03000c50b018090340c03a64182403400821304002a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 80568185 1250 80566935 80566949
    0x60b0d15060c0203030307050307020327101d0f0d0b040c05090609040f110301060302040e0f071d13021302070614060607050c100e0a0f090605040501150c150e0601 72
    0x2058000401901512010761030390f0b8024080c6145683e100010364098101425a0046210601c0b150051408506129443ca0080d080340100401030034104410442140c0c00c0c0720401030404294948603604c2140c0d69100081214440004650300c1c003c03038104529404046d120842480a020030f1042079a500400d5413010340b181103090b940c5805014000d501510001c04059541700f9403408120f460300401d039503000003400440c041d640e940020742074418544113030b00650011320340380f4800c4108209100051540b60b031450030346028040c00014140c0000e242a14615825125104564948052025040c100c2008545840c2c0034100040207010240078210102101000715035649000c6041e01c0c21240c0c02030040c42039580041c14803200540c044400d0050122000c1c0d0b83c910b59498104cd40d004d80910300403610305a1410101c48180d424541c0041c4c000c074a0f0400500000c0214100c1d0340c0760303400300d05068140d5003851500126140100381322032019071600400070745010012441c3c5040b00d0035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 80569435 1250 80568185 80568221
    0x150801060e030c0d1509110f04060303021902030102040b0301240e0a030305070510021605070906050907050a0e060f07050c0621180a150c0906050406050904060b0d 72
    0x80c0d99095075600015805154164440d4104030014070701001009169446050718441c0840c00d6201c1d41c1c00c1e102c502004540d54a10341580c0b80c02410030380f02c01121010308440500c00c0914588029441d84103044610007403c0c0d0074195001951003d40403503000707220b00008030341c1d80d60391444400000680036044142c80880410700500041c45100030151000b8018002c00300b051541c1d605072120350007050200c034540070740149840303946244e1014100030010103201000000140c135241c0d04200a680001c10f240c2c1c5484824045c94484a0a082e448000e42c10034640e03c0c2c410701002d503401031142841d10303809100060302c1c1140d038014801802505204900f20798091802c4810464103024100311280050301401c07804441c05058020103400c00c1544507444540c841c44010b0b903003010480704050324007480e440c071030300c0c0d02c01010701c5801141001443c0021440d414001c005129100c1d40c450b8204110010035640300a81d502d6020314000d1400350300c2156903414000358100681040c032240041c1800c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 80570685 1250 80569435 80569439
    0x91611010603030504120302070b03090307170c0c09060d06150504150503060411060c0105010605030f06010819050603070503030c01060305210405060304240603060c0311030a0b01050c0601150801 86
    0x10050180300190b03540341d11a00d09050615003140006501e01c101030303003188610710002503000e02c02001035005529101c042c540d2081241072100040e003400400502104040124008036000130640c0c100500e0100e0b10f80d81ca50b2100e400013070b805503078000d000e04120700c0d0031603580c02059100c0540d030807103074140d5080c4510180a4803052000365144640e5030560050000100003440b6440c840070721078801402e0034244548001c625007100c809802c8400400c00005c14003003555080c4074843d512020900e03200482d45804803843c00521280700784850440c3d110004075900c0c0e030301880040043c042c094106c0e40c944c0440101a03018001d640b1040d51180948a140002c021030342880040e42017003101405d143c03603d414288807084e80000e10507a910714500241902d940c44420401102ca01000404291a401c50900c1d0003280c81d240070050506d0314000ca1203503849141015aa803024440c0400182c080c810030068441d481030705418041805403900200c0c41655252079000f08520702d07a03070100f45030313 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 80571935 1250 80570685 80570717
    0x604050a09030c0b0a0603080a02010506130b180603071208090a06090501090e0406020906030703090b1614070606030209041407080303060603010b0a0c02060d0b01020615150307030b0916 82
    0x1d48514019000826900307220700491074001a058000080001c00030b02d060790303500c1d89a141d803c41c420b00c40041c0d449600b070005e14509480700d20b09804004e03034100700c0707035440b5400120b2014103410a1040c201400001410582e000d0240a0007801c3e0189450380c940c40030701e00201d0039800001c64511401d038140700880e04034400e080358825120181c58025200303003022400f02d1502d200800884216401b00180009a110b013030145002c0c011a440c0450510214540318641030381c000c01c49001032070b042c4d10140000707a100711103014911810b42810381d0b52025080500241c281d58001071340082c6002c09000c104261201d180100448400590b140d494507819800d44910060307400d59403020b424401031081c243c03490000e01820700305040948684520f5030208200f81c01c010011400d90b40d075081c08410a507010b000c00c0b80d0150304c6803100d2900d2401130300007490130084a0746150540801100144659000b40d001c0a000d4400901000e03142c0740110700a00c000c14181c2d00e0034001000d906802c3d40d60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 80573185 1250 80571935 80571941
    0x1080601060c080c010e0d08010602060f0c030a0e07120804031a0115030b01110d02160b091003020702060d0608280b040204110423010201050105010903080d0207290604050a 76
    0x40c407441d030368150307554050b40c07501c0405421000030b40f000c40d540c0c0c0080044600040202c15680d4050780c07a0704c0c1d401d614041e0043d01300003000700180383c03480c240d40401c08843c030203e0403254088444000080d50f08140341c0820319040141d08408090305110038000148183c40e070242040320312480c000d828a00c207603104800c40c520207201d0101621010302074075000e9406600000784915061500307204500755409000e140990101341e85d00540c2040d80342c020030318504c24032600a06a104006440c0c0034220003c00e04942c042c1c1e102c0020980d012901000715590581100d500074100c6505020300727601c03800700544039061551100b0705001c0c0440080d107008502044420410382111241040b5501c9070288030107029401c0780c001114400b00008201c000b040302103488601d65a0450040190250001908444040c1c00c0503050200c1e00808000055101d0100e07640e019200e580035848060300d20700181805c5800022414145281c0c2005900c1402860f0103440351500300c400307000f6034460a00d947d040b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 80574435 1250 80573185 80573189
    0x130b0403030509130225030e18060603090705150406030c080402011205072102190801050a0b181f02071403031614060702070e0105220c030b03070602010204090501080601 75
    0x403030380901c4150f01d54a0024504545a1402c190261034203c400750300c40751056001090b8100500103010388024190f010865006481c000d44400c051200104402131080e44000c1195100391000000150b901d0408d00c41c0b640200f00280c1500d00e020300e0a0742115040d0010700a00d40002c2c50303c118100002c0c49003003210300468068485c4940354002d0b10002c1c1c040c00300146000144020101c68160070718100801d070850f488106d50041c3c0755003507921000300c2d11418001036810013a208005014690f0b502801a08880b12a03490302da4980c0c242e03080b444410440c07407140d0303400094003864000c038101094031300a603110035070f090390301d03850302e544000c6451107126090301e405600070f204000580390600c101031040c82c0110b00740d242008114540c036181c0381e01182d02c100140c100a10800003c0301321542c05000d01400c496030301d50490b91404c034090540d1404107480080380c4811100ba000350196200d680c40740d5024060b40c0101e500e07240064083d40c0b103403003881605417400e000064055404910380e41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 80575541 1106 80574435 80574437
    0xa17090f0301090506061e10050307030b1906140417010204030c06020111090409020f040c030501050a061106060603190203100504050a020c0604020105130e0c130b040303 75
    0x20303220511150300070b0307060100000000391302164585c0d120105851005480343c0381031000c0c3c1c07800700710044160000c0500440d204c0302640140112301c60042510705002030030041003030100c040300201e0010820611040148038040c4501310561041e1290004a42815110300243c42c00568901c4940c00a0f03500203000c00c104500d201200b80103002a000802c4086200140c0b28100d12411401512482d070310803100c41196500e41000c0001d00018108005120502001400070b0034280222807107260174860002d03005d48120003160007403402d030000d04840d4440000740602904054488004d03010b411510400c000e071744d0300c007561080280040c0003940c58070b80010300003140d0010301000c42d100c0c010400c11890080000e4569041503080c0303441c581c5c0b4284001e0303040c4104029000203082074040024031030380c6041f4030007401c06d1441000b54407180c0d5580e401c4030759240c0300301e110081c = true := by decide +kernel

theorem cover : BRFrame.Cov 80395685 80575541 := by
  have h0 := BRFrame.cov_init 80395685
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80395685 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 80395685 ≤ n) (h2 : n < 80575541) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
