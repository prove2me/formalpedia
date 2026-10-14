-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2422
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:14.403365+00:00
-- url     : https://prove2.me/submissions/3c6a4750-2ad1-40e1-b28b-86f0a89ae10e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 435431654 ≤ n < 435611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 435432904 1250 435431654 435431657
    0x100e090c0d030c021e030d11011d0706090608040f0b090f0a140c0405190c1407110a0e0601020c120304031e14030414040f18230c21120d050403 63
    0xc5020409007076888045c010724500a4002e1110003100e80c030a951000404403094004e66030348107940400110703951401501d50350280034091080c0ac02e0340060943d045500a5018000c21a06010004400c5824041d200350090300180041e121405414200807800c41032088074400e0000351410b119000072800c103422480c50803500d41104000500c015564126581551201ca0f240c0d8070032150b80c2c6030408007191509180002c200503101d8801c42c0e858004040c26141c0f0a031100c859101404e048a010300581040002504c081c5040c40000f035403a501c02103801c1c043c6008621301c000f040c1d01001500c1c0510350183c44850b1101f01c0c450781c0f81007145141c5c42540d40080a041c60000e05802104031810780c3ca102802e0071400d00442c050102900610a0000300c56548004245102c2c5070403c1000543d481075529030071088a00d0740c800d060191110703480c0b80075000f5100030301c40b9a8901c2d80b500c5000001c440e1800d010a500d44000c0e09116849083d0105a0310001c2c548418a03100d9200f144940e10070b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 435434154 1250 435432904 435432919
    0x10f05060f0a1511070f0905010504060e04030f0504050d050c0906010c120e130e03070201030c0906020c01030f0b040203040503490f060824100e090c0d030c02 70
    0x484003001408640203650940042c0c541c0d4082c8200b42d691800000c2c01e00c0c00c0d041c10b080302403008452501d401c030780d0344c0000c0580404010078042075005000700c42c01042e0403601444540d09041c25a8000c2c80064402030507c1100c42c12203030701e680500305603002000014100325040d051402c01b21b03122030150120b54801d5001800150341c540c05404004455074104820900782c620808082e1034491100c244154003c00002c0c00d149824a503000300c2014100d2240034580b42d803107600c009410b881101c0080014080c0020042c4079403076000500300c615800910300402e41020307c0d14050010000f1f2030505800c580000100020310a0000082242064200907c400c20003618240d80401401003440c03480c4070103407461204503855410441a041c145141c002400302010162001207800310f502c100400c0e00300000000032441c04200759450001c0c04044501c0d1841d0000d69150341034802e00403c82c56404207808030301542d004010200320040080c00c0703580360440900b03018001030389203030301284244074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 435435404 1250 435434154 435434161
    0x140714060304080702060a270311030d08130c0509090a0b090703050709050c12100f0914011a1309090c120f060216052d030f09041a040905010f05 64
    0x400c1012644100d400a50450501d0100da0810031940d0094a41c142001030300400b15001305080b99130030440302000d000070030410386146459504240110203d921903003084410043c929004043c07150305c80d01d0500501141107861070302d011a1034007a0440e86d049400342c02001903245002940a000d07a000b03404118099071a804115500c50030741c0002000c3d90405102001f1501c281e400150704885c04128171803d00c0215080c01e1030032501190310340b0005400610411003403032a10060005031800c00341c01e121581101c840c850030140306101d20514a461480f50441d00840001903841d02c0c000340c0301a540315aa0348001c1000791144000558102c9408040001c159030843c00850410380d00c4100540c0c040c00c26241d10000303400c980b40c2c0501c513110f0340c0d9040000400070f01500d007450050307110050301c0040002e0403041440c200482d198140d48100010700c2c011752900c00b40c8121040458000c9020784e414400184428000507800b81c10905194050003080010340000240d008410b0382001160f8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 435436654 1250 435435404 435435409
    0x70507080d06080c15070f1505090606100e01090302090403110d080108120702280f1d060102070e190f020a0e030f030301051c08041d0103170f0307050a020703140714 73
    0x1a42d624458003105c2c410021440010101107403107031618080e040080889040c5020f200568504072030451407604240e0030031015140906110021801c14070b0303c248070910f034500180a0480902000c2d10822041d00041c08142c8035421030f04021109100f518040180d04038064001c100130700130b01c92980101e202110b030088421050f01e42440e001001d00600c0a07821110880c0c40c03214440304840101030b2b4001080011003500044010320541d07041da45a52640500b440c030142001d4400303030454102282c208160700d003c002c05d5802050184840503000003400f00c44000300701c401c2800c1b0f98540040380501a0541101c00086003240c00e805541058200e103000944070320003406010f60102d01541c408204004046e40000c0c06803003807000514040d262405040040d00c41701c500c060090002006000f00a002c1c040081c030641c50740a0242040b0030a0000402800010020000c00101051482c46603208000b10300055800142102d02d203a6186142c5459045600070302800c60400e00700c080050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 435437904 1250 435436654 435436669
    0x16031a04150e010e031903060b03010302030a080f0c01060605030601030e060c0a050901030b041805070f080d0509180c1e03040f080c0a060f050601030e0a0317070507080d06080c 78
    0x1254041c8a1507445022642890020701510240c0621596102011180842c0403c0140929104411820a032080660000307083d2009600021525001840100010b803400510940c00a5010501580715901c80079019001d00904c16031007195030070894005030304d5810200440c020082a61300b40f0103c1c016070601c9989400c260342002c0110001c0200d540742070f10440c040c103c50741c41450003081c46d03d4884001000ea94135000c8880c0881412801c181c10007038100451001482d45003c0000355078680a0015141c00c11210500140800007943d145a0b03036441d542e0160385000380c280620b0f2420414406142d03500b003010900826203d40c010503140380d12540c10341c8c4c4104ea014900c1c08484500303944811351504141161202849108c9054000890b0303401241c483d01100400002d6901e80000014290b03603101c1c91001594101d82200404640c0c008810500002d00c003040c0142c6448481040b41c0b28418003201404209000c40d01d0b11392210b690700450219421041118010204102082000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 435439154 1250 435437904 435437911
    0x102010507140d15140424050609040b120d0810030507052709010b04050c040b090d1e0c03120503010f1404060f120c06140912010b0316031a 62
    0x100d110400301e20021440480140365003c10040702050020003d0000300280e03403030703030041220485100380103101406c0500c58884842d40c0e020000501c100d41c0580503004143c80e004180c011000020f050b140d40c0c459070049030f83d07100041c01c010b000c1c0d684088115181d03440c2c612200002088c030008110380d0111490f15070305a0740c1180283c4401e921f08010009014a05aa20b440b4100780c1e08905000b84880039980c0d104000c01c50000c644d101e4000208402c44200501c01040c0c0d890074031061180c55806000e807202c1000c250342c03c00c07100600e42881c070340030a2520804031610104100100403c014440c03504212481582038003a01c404052095605000074010304020340300040081060004014140000074000303440060b40a0f180c00c0c400e113809466400c80c00d81d03140c4a4020800304420303017007410014455071502e54900051103c50406902c80e00342060310440105107609070354082944681c4098030010704a500100040034201404c038010711040da503100380a1704985218510805c030510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 435440404 1250 435439154 435439157
    0x91401110d05061201180b1b070312091b030605060f0f2110020307120905120c10050f07090e0708011a0702040504050102090a09094d0f0102010507 65
    0x704000c0091100040c03800070003a13540480c071030f08070155558082c480da0405010b15420403141c00034a0600180041025240c1c2c2c1d80300800344544100500c10030180d80d00c0c1340e45443c0140c0c0852251a00c3c00142c0700303400d000b605442801e0710030404d1042c540450030440e8482d4205103e140d451134100404501002d541c5500704240004800b1503113850f160b1034030fa103040b41411031280c11182c1c941070b240c900519920744c0142c0e4000306002c00ca5401440c00c4440c0c4440460500c00340d03140d951441d454014000e88840350840c08550a1046401400707403440314043c0141c108020301d0b00741c480001460341620b400c4d0108908a90100341d4021801441c2d2050b00c6945074001c0c164600020844005100c06c004240300c00c0502101d00141d6450007480e0185010b01c7c0050313140c503128010031801c800d0b29401240603524081e0b403140000c1c5281806a4001c55040d1007501c43d800d100030303a200c01c05816581c070070000e40b014508078402c0030700440340b0700008040c3c8401d410407401c1c40041e400c070b8809849000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 435441654 1250 435440404 435440407
    0x60b03090d05130e07030930030e03091201020a0806190317090d11030c030d090311031903020d02010522021203091003060806100608010b030c040f060309140111 71
    0x1581034062801444a2090442c00f80c2015644884c100c07030215043c0c4079000000e88601c0c0317a00921007483c026080070a44000758000245004091121010a03400344200307260702c61174a400c0380032040c01a02e588140180c80701c9580f0f20640f80e1503000790711946180000c0b50904001c82c407241021b40001d000342c600700c1170f140755090950300c87c030024401482a450400400300080030782038992220004c80c1921600c2d1281801c03c48030201801d02c1d449101c00c6011b54054108800d100b0340c000c3c07034182180c1d040b5000d00d081e6114000440d040c800c16030181c082c0702c5412070b01c3c18209075000600c00c0b16544503500070003442e207c0c804a44001c404c038424071140e180c0b0714050f43c0c001d86820050321003059481422a881c00c401d0f40d02003036443c40c0e0500c0d0b480100c0e13920b020400c11030741c00b4405950300030121600a51501d08040c8082c0c036400041c0038410f03007010044005843c4142d9801200d001c1d200904041420680c0e0740340c0200504221041165002e00c520341c10b504601050003150260318141c030308603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 435442904 1250 435441654 435441673
    0xc0b060f0a140a092d0f090807060c0e060906090a032405090606060405040c090302040e0d08090102090a1208162012030a0c060f0908040314071505070f14010e01060b0309 75
    0x24040c01c1141400b03200240e629010243d9880e0346c2d10070201e4061248661648403403041c00e0650884401d00c10b0305043c0310b41e20384020036664a00b01202d40c4204101c076601d8813110300502141600e007140d00010281b101e400c0c296988000a001803216490003100e0a2005903a942012915140180d034402d420a40c14402805140b410707402c1150007520f14940140e450303982e41c0000e1300f40e0710725114841042c0c002460030344c51203500c880e2040c0d101d074101d13000b03505d08601c207408034040100c81c0c800c80e006030003980c400300c0800094030110303034101044811038040c00d1020700f410440025030503082038641c00d80100d800c40d103041c00c4800c01e82c04110000a0b609104c40b080050b141c0072008a01101e140395904003401c1c00840b81d1043e140308a002e01c42031b81d02d59042d49088007410f0340351100315069510060040007c5419110b41a01240d41458103546a1a5910300442410091003004100f64420400002c0c4102d0550017a101900c01c0c41c003d001d200d9a5180c251130324403064448030412707001400724 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 435444154 1250 435442904 435442961
    0x9020a030303050c22081603020607080f1605030901091409070503060103090f0f0605010b25020111300703052a0d020c0901090203070c0b060f0a140a09 67
    0x2180e100c0d000040f1145020001701501894040b84c044e20a84502104c405006801c410000341e03030002e90300d10400399903d00315000a071460090950040440e5000110030075000f190b80143c411035004000c05069640d0280341041d00c9810128940e80010f26a000c00144401c0300c00303010301d0301400030303103c48401c0e1607031041144c05030300040205050580740c100300000241c4004440181078042c004c40f020301403440c0f030014113840042e88074030740c80d00b000e02c5640707070301113207a400034607070107041c07410201121494030058440784465650388100303000d0f00e0009010411100c03031404604c0c0e0100c2c00d000c0001c0103c44554581c1c042c4280180008000f03000d00c00e05180080060343c4240c14005c44000c120042800062070700104002c0320005030040b050414290400f4400c90340075000a0740c0550452600c0c0800900c1c085040342c01504032a8110003043c82512000808004140b020700030002050300d840e076002e101200d91100c40e00801c024039000980202c1c80c460160041000689012080b034440e5a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 435445404 1250 435444154 435444161
    0xf07050d20040611060108160b180612190e0703060e07080a0c170c09040303021c020d0603031d15030415020406080108010b090f0a090c12060e1009020a030303 70
    0x28038070200e0969440310701c01c10320007001030402006290344100d86120420b000506054041e803003a4129441108036200050810340c22400380c0e101541000c2d1a2001c0304a01410b4110034940150001070005001002c4460105030511aa0102030007403003464000c4140d004580b1118880041c9410405085c07001607503031380040092040010440e80100d4554040e10b00301422150100d030000c800e080100303c00d081036521204005c4030780c0c015108011075a4040303144d00b10002d20060030164000751110600b08901e040e0300e0a02000b60701107403203d2901c034981009007424001074001c00e0b000314406c48417200500b100c6010903030240a8404a0f0044108111550030140088900e0240107002d446000014405880204000d0b80c9503640c0d0351402e91b907a4211410b030140f060080300380c01d00300805242e0750720006402075441c61001a60010701d04202c0d47d88600d5400c10400301410340c1210003400714541243d80da40703410009503480701141e095a8000c94035100c00c02900000003038003c1000c01d000f0350 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 435446654 1250 435445404 435445421
    0x80a081608150a081e150c1b010e011401080c0f0f011110020c0c0a1535010b130b0301080a0303090816030207031203020909150406050a0902120f07050d 67
    0xd2050360f030207445120790390500c3d6603804201c205142c01c80c020820600d00704019065002c41180003002414860070902c200c0c45031221103104903004880c4058520b0096002c034186081940c0204255145017503907540c030342c078284106e4076079105086001003a881c1100101c400420010120000c00c0000001543c0001c18405070348010b0050100142c00c8502e2030004020b400000c40240600700c850400300700407280c041d0000e42d41e003015414007007001d0790070140c6484100111001c0c14410301c184504598007802004050105c01c2c280d400000710526441d0180000b07821181a22100a4640410641c0c1d400244184000303a8040320241002c2402503205041b4640030f02c03c01450520408592149444a118120010380c40040c0410610010348500c4c2000b15941c5429843c1103550380c00102488805407840203030003001c2001001603a900e61202c0d0003048050b00070021560340780b01e640001e40020740104925019440011183ca51140c5107038400d54030703521800c0c00c00e900340c0601c2e0010820072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 435447904 1250 435446654 435446659
    0xc09060c11030c1f1b12180b0403150605010e06192f0606030606030c130204150507150b0603010e040609060204090e0114090304030201180b07080a08160815 69
    0x500b840441500c500b095602e8407804d03600141205086542c0040c001c1a1044096643c0d9220350100710004540b502040351403500d40c07030a20703155000150611925001a4000c900c581c50004d0004200300d41c03584403640e00b03a4694001c00910b41d451006540c2c0c1c00c0b5400079140d1201c400c00c1180e540300d818041890342c0e40c1151904d258060001340c003190080b040060607590400c3c3d07080ca034082c1108100040c960141c0305030043c082038100314001c42e64481a070040d0b0b52142041a621038642200e0364191801031002c3c6010480c194110b1402070080e60042c0c3c025100c0c03580c103462142001959008405034100c000e812070303246a10700180703a113210311301900448500ea286d603171003000704100c1d002a102425090200289402d141000c403403c4802495880c00100d401c1010094000302c00320a940c1280c0c0c082c01d101c403403482c81042c40d0603200380380e0b0807034844004040f40c1b181c1404001c202910b900740040c0c440c1111512001c0351403100a24081d45440002c491100180c43c0714013004c2c00e10300e030100c003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 435449154 1250 435447904 435447913
    0x240536090c0a06031a0103060b1b0a050601060926070504050601020c0d080a111609020a09090501140103140603061503120304060f1b050a081b19030c09060c1103 71
    0x481c0022030900c2c0c183d01a100003a1241780142100c00c00d6130034100c901400742410003103146050400c120354003541c0714078010f01c0702d02040401006024441c52220a41c040180c40322903031500e40c00341061001e4003964038030314402070658503000d4103182c1c070328982c4104c0310007043d81c00d01e0301c02044040c04c0d0042c0118118007c85260b5a101c0e1655540b03031103c5440313072154984515000c040140850044401240558030441000c45003407004018030003500d482036005070f61840d940100340c0c0d041000e41d004000c0c1074900000010300403c104885107104000b641d081c04200072400b000c2107568401c0c3c401d01d0745500700b140842c940314039450009110840290030340b550306800d14050703144d541040b00c040d00d0858523400f0100c100d480d05c2c41006001d44084040c1e01605920140c02445809001e0300d401c21b010b9424003091040c01c80300d880380b4500c440f4641c25655a14039181885103c1e48005001011030f007003110309141c450180c0108030503104199210004040d0a484102c0120030051450303405005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 435450404 1250 435449154 435449173
    0x1c0203010903171b2208060a20030411010c030315060801030c06021903030203090c06040306020904060e16051305030303090d08100b070b06030124053609 68
    0x8003805070041c00390203500c501c030207501644044561124020f0502c1403051516030541140f82080064640340c0b4500e0b4a0343c444c102841c0b0034200c03000882e8002d42c21a200c1c2074100b00754104950004103c01110b4488440b81da05481d003004c1107408155030003441e1200056062040d54410307045103064500907d000b02c3c80c019000c020704103540d43c17500b141000801b928014001c0c01030b8500c0c40d00060440c3d20050241110044c1c0291030384c00d03800340081c2090340000100e0300d154400c00071101c50460041c41540e8480d41c13458210029403000030080d00030390511a0025900819026092003407084107000940e003103101904481c0c1d54080c0205039a41e503080000861035407002c1000d140300e4900c0720020032a403040d0703000c080c2040c00010244c00e1581e0040c04140324a41e003010940300700c941e1000c0225500d40310000068050600c030301c0ca100c5042a8191505d110321030400100080307440549064280303060150301d545c40f4003c90301403600d095144416204241d02405940341c1c0c4607240c4c109031440340e00d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 435451654 1250 435450404 435450409
    0x320122119080a4a120a050403150209040e0a0b0105040e0102040906060905280b16060c180617070813050a0503040306181106091804060509060906070c021c02 70
    0x194840b00700c41043d803180700d0f04c50105140100115154050b4860010b100312041019650f6988403110fa820540d0701040c02c00c03d040c01101500c001d150b21100314402100702410000c0250415500144942d0500040031079881c00880d111440907001444442d00b6030801c82130002a000310a10480559400c00000454904a100390005040326a40d5941020315003001c101044018203000380c45c0b01207030300310b01a482e941d801d56035040f07441403d42135813501000b0100c04403903214590060007242c10200640380c0b543d4000c0c00500c0403446120420b00700d54454404031207100b800001d0900064020020071030650081a40303070350207641070011505284040d66040d05007500d05d8ac0032503441c4d0005c102401000b18501410214910000c0307c409030101d03d0300c4040191004404042c051100051044a503131540c80071a80f0382500c9165035a0349003040d1508000500082b00c480c1c095002e05004241c4840d0b020802a008581e40c0c1d880b045e4a910680070011940b105107900311a031400c00e090000180c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 435452904 1250 435451654 435451691
    0x120c010813060f0609050601110705090c071410060b090108010902220303081504050705091e041e060501090513052d070f08100320122119080a 63
    0xb043c1004001c80e80600c0d1840d11415550301402e0681440340340e0306004401130f8002001c0c012144219101c10326601c8074420506148220000504500c2d40e0001f551194140001c25a1185840c000d04000c01c072342d500c14911190041c1d50005001680c0e000040019064a0b0085c00051550712081a24011403401e0400d0080e01580201c000c5402d150400c0340307090a40c074280c482620152824070444c81d2410000381030f0702c204c0144034803c03550b07aa0700703808080d1190005507605401400c20000c0300c9040d200800150b450811130040e942c100316022886512461424086400291840301c00050141703100c1c003d4070b0000c020101004100360b12151002001ca04d00303126162071ba107403140340e0400d4407004100d0781d40044008240581c150901c509070070289a030b0350442e50401040300d4a003400603004890ac158a42c0f04940c40a6801500846040003003100c2035203003040c01030380d107283c50458120300a174040d10085000d078540294040c42e03580d0244100f40d610280804000542c0201c420720381614 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 435454154 1250 435452904 435452921
    0x60504020a12060f060f08071107120b0a020a02070510030b060307090302040c020f0c1003110a050301080f0a080706050408090a030503090a0617131410021206120c01081306 76
    0x42c0701c1031200324126118400c0c00040c24500480c5441141071000c0600041155035058080000c403000090790f80b072003211031b07601c2020042c0a0307610781d903954907582c030b001140c00e442502c825401d2004142c503003210f0b1007100c5401c03060750098440740385080301708540c03441c00300035401c1415180c0b4501c3d00aa91418011441080c45803189482d030790541c010700040f140100e480c070041d0b40c8110005030f44500c0c0007502d0220b00400315964950026140421000380ca0b034415050550a00401c8184506401401860607074020034102c92180900a003150350301d800328000601003200801103107012903e02c0d00010ba10a000b03034140c629204419000c1208440d05520a960344c0d0000b05a00c2004e03d002c9400d040102020b142c150402c46030f0f29a1050640300c00b400016814422082c8031081000196409034600010000d4448000e400300e401800307036204201066800a04038005070052800c40c0340008150f07030303280080201d01001c40054801d880c000d401040c0005440c01c80f100040c8032030255104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 435455404 1250 435454154 435454157
    0x507080c0609060a0e01150b13090212090f0d0e01051810030c02100207080f0903010902090f040201021c021b060d3e0304030309020d0c06030b0f04020f040e0604060504020a 76
    0x199807134150784090488003242a001030503410018807168100e000210401075610f9100440e80c2c4400700c04c102030910203d54080e580b05030001c02c060b00a003402c19043c92041d40d0200075100f450a00700300c12502d4030390b04049030001c208016140c3c441da52140c0003620b0404041111b07051080c61400c009440c030400c0c1e098590002e40c80d20f84000c0c2c9941d0611810b03000c420506015403d041c51551446000c0c013a1418011100c140030448021a50702504120040f0303070050090350b801d0502c00780742005020115426400361042542181d600c05214030103030070f0003c0d036a0103006124100c40841c02514806100503a20140c20300c1800c48101c050712803281640c008405d806090300c0c2c240c12284015883c04000341942100c5a01050024860021264000d60518000032104028400201682c00d404000360420303503000c8001c40c403250160302010301c84a088510004400c410010801a485a140d0820540a05000070481c901b2640e05aa4220354010300c042600c9450b035010404076008015900d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 435456654 1250 435455404 435455413
    0x9020a0e07020106061404060e150a35070804060b0310150902040b040b0703140301030b010602010e0a08041202060702060d06060906051806070318090c0e0a0e01060507080c0609 78
    0x4081c64092055000921490914042d03001680c60409032a01861013003006000d0f4000708410700e035586402481020100040fa50384607492100700074160340c00c030700c0c000d0729001950211014800e071000400c140c0c48580420400703960381e6860225030320310024000700d540070b0301c07034880c12030340e54050180040b240701e16900001d1244103070070282003032101e41d806048154810002070008820031400c5030250b0b0904940315a40c2c1c10309217021240d141140781c1810080d0008000801001440f200381c43c101d85069000f0b1149103091a0600d8a400e070700d040040c01c08408010070009c03140449070481c0501d00042147d4142011038020490741c0e0701424081150903580c910510140d42c0000080020704161b1800508091400010340e2000080d078001c40d1140340d000c0b4000c0d081520070500ea07070014021100c8502c8a0365900c080f00003030f000081d08000130881c03220f204603280c100f02c50014219032004440516a901e0b0007029156503100c0a000c0e0b4811008020310228858204049806020b10354000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 435457904 1250 435456654 435456661
    0xb030f060a1509060f090e030408030d14070e0d120c051b041b0819060b12151806060f0705070e01031211032217010603140c0303031909020a0e 63
    0x10b00000c01203800181a007442c004040c03218404200055060b0f440b03140d000a510139042e800f25145000e16444a48144400200d078103210210740c01080789510024445c000c01c2c4c41d0400c05030340c00c200700b0810039044901e1248140204a01168806903085a403c000b01c0148058031440c3c140001c07091202010302d007220500b5201c0c2058400e00c01c1a00904401000c10030980c0c2004201c0c01c0040e0a8074681142207001000c0c00400e580108010f022408002e0b80d9281d090880c0c7c0103210f42103030103540c68500324108410b5800d0041c907a03a613000c010258500c2554803881000300c9504560103104000c0014450000018010406500038080308400801c043d851442d11001075010284007101f0403c1030341305803103d284004141d81408c03510448075039802c00c02134a075800c0303000d4641c814040c00c1303180389803c4034a076819446102500d000704900381c1c40c9030a1601c039035962049a10655050381c01080050009105440c81e40d01d602401d03040481d01e001d0310f800140d000d4000341c2200c0703803032072040f03051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 435459154 1250 435457904 435457931
    0xa03110a0e04020102100b010e100c1401020a05040504181a0f0109021908060d0c09020c060a090c0605071505100819030f11031e0a0906020105090c01030b030f060a 72
    0x10100070103011a080304145801e60000751580110101056019150107021450368003c2d8600a44580054100d0714044469440241203041c03452040d907040c208410f044100c4401030080329208052520f0f418070302440c0405020040070303a0341485941140401041000a038480c0311080115000d0442c6905818428114408951306a00409840d40b0400042100740b41e950350700e4449030494140f2294136540d181c0070600c4c4074040b190040c10b010286802050042c1c880d8060980d0102200455402da130320016110120348802e031025202c820440380070401d07203215400030911103104001591060700c02c84c00001c00d459041d80c41e28045415100300348240002000401e0074904444981c000946142e00c0c041c000a401a0025082104800b10049505000c1040341c100c0304017082c48042c05412001512999040a0300b0305000074a5410300060715441400341034029072021001d0306c4065102001500102000c801080d054002c0060000580070184580c07441900c050001150048003840c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 435460404 1250 435459154 435459169
    0x20301030c05011409010e040902040f0f021e03040f060e07030f0308160302070209150105090607140c0303030f0a0c030608060f040b0a020c0304090e0307050d0f080a020a021c05090a0311 82
    0xc030b140b000000d000e94441703680d04c030b205036103038010070340d00060460303ca400440c016240001030980c110b0300300151a040107600b80d0051007000b0034403505441c4000980790543c0c4502c4140c4018280302100c9503000c012400e5580980a804090401c55039040da03260b5990345248000f40064022a0401c004c100c444140031380001d401e1140c0340783c00c40c80c05031181e000071600310000d02192107500702085000d420382d010360b003101c15031400282403507180e890610f400102e08008034042d00340c60142d03000155507030500209490080b4000d401003149aa20042002e0050240c09484001c064a425000680300c0061000310b001e0603882c2c100c01000d2425040c00040a0406800b50101c64410010321030444004410340c0c06580c40c1d0328000c0b440301c074540030312869030042c3c1d40d001d0200e000f00b040202000303400c0f0f150402d0a400d80d44a158040d51523020010072805562501c0c030158004050407641c10a51800b4540f03004000d05000f03003003002d6003010440e0311040e42c10481e42d1754400c00715070105203041c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 435461654 1250 435460404 435460427
    0xc0306020309060f0603190201090f08030301030606090e0303040f0c05062a070f180e010617010c0206100e0a060801060f031a070f05030a0905011811030f0316050f01020301030c0501 80
    0x140701440717052400109a445815400c03102c060980440349100b1a8410302d5504010b14165803072101154958031a583c0326402072100311402c1c4e02d0701e0000282440b95000d941110300040024508599070342c1c4407950191150ba400b141c0000c0907540c0404c280d0385403009007214090341c0c0d03800e81d100181403502246100c2c800c881e0304030310340c01084200b11070f8050b424500180d48006c5207000200090301980c4000d05a443c010f03030300039401d00340302050700302c1d0f501c905c010f200c40c255000703100c03404804a00f0390f03c1d19010f40d044203800340b400300b0074818042100c6100d038000c4c440340400580241d840c1041403c6644a42060b01c0d0706103a440200140301031032180c80b0410400c5000d85110b070070540401381a120143c0c01c80c1d001d2050101c0040d815030001e5000d01c0781c26402000074040320741400384007608888028411565244641c414107600d0500040e100e03151200c44000b5840d04040c41c16103151801030410403203441c82503281c01100040300780055030007180b140c8149441c07241420009800d410301e61 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 435462904 1250 435461654 435461671
    0xc020705060f0a11010f090c06050403111e0a2c010e01090e070801020c0601031509110103020f04081207020420030103030c0f1a060a050a05010c0615030c030602030906 74
    0x25000c0c0100c0c0d850310201c0d100703a140295001d54038281c0f1503003074401005000d50368449510b010b4040c8a0a9081c1e045040e10390310407030201d4001502e450082c0c40601403804007600740503010028034901c6c1052000c404960204843c3c1d000140c85032000200c003118640c005142e0038503100c4120300c07070f030003815a0403a4103c240120759059605094a81006010503c2800045a212021050b0a41040c05a83c020340240d85c003c2d5511000301d54000d41c0c5240c2840111a0b540c036160100401030303482e11500201582c00403406600302003510045010b9000704812642d084420040001c134a4403c004d65040c903201c80515a403a11403c3c010001210903518425403080b419581c1d14481c2122501220305481c2e26060aa40541050810a070b50f810b50841c02071000180f010312076040401c9003500d510401003142d80305242c070b03210000d012465417941304250100318030010181c0019500e400190b4480a0440c901441940d2502c40010844456200762a072076400024491141c005209095002071503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 435464154 1250 435462904 435462913
    0xe04050d030f180605060a0f1d0109060b0910031d15070314070c0819080925060507021305040f0c090506012f0706020f150408030423061006030c02 65
    0x43c01940c40b00700410303803004000c039540700c00040780c994032001c02101a007020120210681d4541c96058101c0821a4030407843c3e01d0034000005181c44980103510540348805071142c10801e40f5400d12403030002400c940f00501d0303100c41028545807a80c2c040c40040700581c85c020400000c40003194100e417400500020300300f50138402010300761100034204a400032924507042d405842c203070411504c82d000f040c0b01c1000b104c4031045500851f95005200b54011220b480075102907044c00071500341a84100c1444411000c0440320400c400c5002e00060701120b80080c2045448001c0c800080c000c480003282c0840c1c0c0e902c3c42140080038072002c1d000241c054014144104840e09040c030001c2c001d5241c110300c2075031080e041e00f40c04849850100e11000481246800c8448081e101c034000307911150310310482d10301d52003841c0307030440300d011101c80312401243c0104506155417540c1d00c0708da4418002e04200b0f88071512050b29009034440030803c0c244600450744040d800117003004401000e0320a071181100c00c5510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 435465404 1250 435464154 435464171
    0x20c01020a090909050c2e090302090f01030302060106051606090305071e020a0308031806040b011d0f01031b0e0c25111e03030409020a030e071a0706060e04050d030f 73
    0x10000d81c5011200d0110342901c2c1e40c0d81400d140c2c44100351806040c0d1f00b0380b5003800c0c24028041d007020006064038804c68480b000c90b136429064281c40a000d2202900690144004003d0030b0b00440c000c060408507403242c00030500d1540c50781030a40304201821800540000741c900180141002048651065a02500500e032141c0d0005070980070640006080c1c6100000172421907806100780002e241c4011090703440a1900f420294840003003403080102440103c1810035130240810481032150999500c54001a400c5440c0c01c500903000d07824a402041a412001c140d4407040e00605100e2501030781a25a41c0840c00b802c0702c0d02d083e00c4001841d505980641540000e00c10324255486401e00740c5000111420700030b440310040c564446000d415000009004c5982055600241440401c6440c05d10090f50764404d41a512a039500ca110444020300381010b00080d0f00c4002080ca0718058140403540d80d48805c03005540d0b000590b011540b40e0f110659001c0e4150301400750500c4581c40c00800c00c040c6a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 435466654 1250 435465404 435465413
    0x2030f210f040b0307030e0615030d0203041a07032a1106030103110906060d0906090b090c01090e0702010b1c0c0b030c070b0c04030b2a0304020a0b031306020c01020a090909 76
    0x10b540180d0348108008000600102d12940c0101d07800944502181c0e8141002c0e6100f1b4220200414080c1c040d000c0c43d141840d4260000045504481203051400c4002c02002600300c034540000e4801c03000c0043d000c44181d4a0280c0007031130304506070140c1100d00100310700e29001c2000d000519089000705814001007001c078010ba0250303040c0f00c405846181d8666545000034000340b0801c100385403070510304040c0c88103120450b8080f4407103500c00c9034160003e80310075107130566408040d0402030019400c403006000544100004030b400c81458000410955090000962080041d03aa9640d1004510014030300340300a00801100134415922403901e142040b1000c80118882ca0502034418110b52011444034508041101c2c02141c100c00b0039a90707410022240303811074421034200791001c210401040002060703801204d004950040c1042c00081c0f0300f03d00d021141d00020300040d00e15035140009030104e80c2500052408802d0140010f80d65074042d0f4025002e0200d5400a4602a140c0300c040c00005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 435467904 1250 435466654 435466657
    0x313080f06070e0d0303110f13080715050c01020d050f0a1d060112050f160e0115020613051c050a0908010203160c0813080102091201020c07090b0d02030f210f 70
    0x703e00c15590490465003904040d4041c249820b6044661000090f0400c0c01c207907400098100c11041d0800114510b560749042541c0e0500d900580f05060104110340060a000340001c0009105500016040000c0c5038640340444800310346902000a40508002c860a2680304070302d203901d8080020200d100e1000042c0d41e0792081401121880c040b02130a003000d00a0820085000106d100101c445081020711005d00c0c0800c14811040203180000010401e01d40304008489003091503030062034a650744282528445000300003d8036180544240c00004c0200d602801003c68500d841c1c1958407148502c00804445155101c0b0310f069205109101c4248200b01d9150340c0304c500c0b803078024201f441c182070003400d9215108064040c1c070324031a000195500190040c11030544101d804503003890580c40e50b28240d1150400084458000450074020000c00c0c4d44084950140504440c00e40841507011030320700400030040d10425031001041e001103008000342c03120000b411880c8541008501a02480355 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 435469154 1250 435467904 435467927
    0x10b0315012610030b1003060e0d020a0b0c0706020a080405160e2403061003121d040f1e02040f0f1220130213050108011d0a09050313080f0607 63
    0x80842c1400407540c411400d516000240d82c000e82455041d00f48140034007103200b103070303c002c41c0c0d580e04050344141c54031004602603817024450380107030035140400e9580c50811140248a100c0c5c07003006010000209510788003802c1c1881d89500c500b410340c04e2908000b4642054001c4840991841d0107003031040c44000c820070758100d40700142d0000700d800ca8240c0c40b601758100a00c02d603014466041000074820081c400141100d001e000184000301d420501100c1501a03410403004c41503001c0041680c5050036800598540345000b40003e440ba00c0d07a26030000080f2000d0301002d02c0760085010300548514058110040600415100308189000d0015860320110100608011080c0f201c03403004d9020444007003a800d80080c680c6510301100002900250071403c10038950095200000c40c036035016200550586011050a0494000007128480d4148004018140c0f8a03191007503500041e42c1000a40103041c4100c0c0e803071b80701c2c40c2070110903032911801100e0403d003070b4802014400459001237404e1031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 435470404 1250 435469154 435469217
    0x1e06022122050c0d240203061c1104060603020706110a020c01111c120c0f0915021e0c0312030f04030c030e0a0f05010306320a0e010b031501 62
    0x6041c015040c02d07410310740d21104054004040c80c10b1041000380480301d0504100c0c404001040000d20421510120701049450941150042e180b4803020b010300c019103440749103c7e0b62200b1414283c034001c6001c1d10700380c3d8000f4010a03004a500f00c1080313414042c80c40002c11802150381841b1090300000d540380d031040c0403a03060040055800d4040302060001030500ca13000c400c401400c240461000741000041780007102c615141201180d1240e1041c9018803581f1140c2c5c0d10030703d12a0802e4810216080021045c80551250755140401c1700c80c058001004030314900041d06101c000f030828142060b84042d00920000404c01c01c128003543d100c1c0950341c2158041c50240c1e00c90105140641c4d0701021910381a52000c00c04500045601e1140c5010017562020f0fa0705021640e83c9641d402e00a940c031100007180610441e140d03181c000f4101d4003405040b44c0040059480c2c56860f8019007c1032002e0304410307030180000040180603401144488080030082c83c2c2140f4105c940e00d00d440c86112003034100030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 435471654 1250 435470404 435470461
    0x40207110d021903030507060c020a05061807091104050102010e030313080a050c0a0c03020f0609030307060f02040315050108010c2c01030b040212060906060c0312041e060221 77
    0x810b544500b4103092240001c40041d0f0159030301d07801d01078840e81201404988050408840d50764851020549030329483e8400000c00c00c640b1032800e0703560203c84031042d00705281304500000829803854024240045000007546558038149000242555a031640014041d4070400074480d00b01040d0156220150f0040b070b5954482041100031503030341c4510f800405c0c40744a254158002d0140c241842300c101c0b8400c0b6080100300f20500c1c03e00929010f04441194550410b0202d0404103105800c402012040c0359401850701e5100e0743c542082c26080c06020444580e0350b40140301c00c800902c0b960054050a060068465031240c1c650748201c040c90400d09400526604c04055a902a40101000c01e01c010025501c50b2001d90340c0302a411b01c04c841c100d00c9500c00d0000300700c1e90704240048584030592500039604e00b07003200c4101e8200d0f050203130084074100c6152901c0c8840003000001e50f89610320032840980d03115080311002600320580004008108100b03428019201016900c00441c0c00107a1640d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 435472904 1250 435471654 435471679
    0x6100b13030b01060e09060307210501060b04030506010e011e060e0315090102090a0510270b0307030b03061b091005041203021e0601030b0f090f01062304020711 71
    0x14044414941c401011121101c0010802175005000d04043d0101914000401d54540c0c0400d0b80e0f4040c01d00c291011041090008000343c42c01043c400047ca00030300011500e51354441c169405540507a000741d07010313001980140654400c040726507004281612400c0030014426402ca82c8200d281d11812042c4120714002d042c09880500200411004c40d503040c410a00e8480440c03400b0f0740c00003058500c160880b1102140354a45401300740070715640c40e42c5403220010900d2500307100101a21052103032109640c00011041c811800451181c1c041da83c010a041500005040c60301a0244c50050219868824108006101d03c00d440b10300b501243c140c070300c50003d180b081d5018411034005001000c8004400f50516800044030524140c1018500ba41c8913103512000e901c41320280402443e00a1a1010402c5071040e4084c60740c000030403800b501d001c074400c44541404c64642ea48240007188111b030743c0c0c40100300000b0b81c42e6078550040e10150300e40700540d92102d098100c0501d039248a80181e0851 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 435474154 1250 435472904 435472927
    0xa06020c0a30060c0e04020f180d0f050c09060f0d03050a0e03150f0c030907060e13020a0c030206060102150c0c0c0d080d06050616030c0203032a0105010806100b 71
    0xd400301800d9401c2c00c085040c40d08249010b0a6404040008903042c4129243c0c0b906083c0f088a0601d0049503449042003c00e0b4500c0c0207034040000c0781580040d820701d10001250b10080081e010511610041080c0444a070504c4030790480144000d07c40d9070b0162901016880f00081005c0755689032800c5503848400e25010745007503224889036900340c07061a9505c01c5210303040710541d010b42000b03180e0420aa40c0c18a00000360f2004503402c902e40e0304404810000e0b9405100c000d9612407000b440f42140240b690102001c80e0041705900001802401000d4180b5406001c042d40040c800e2026290301c001d0004079110326940a0a00300c4100000194070b101c41b0428049150112802401a01450038034241195142c000d02c010f0b041e075901e001c500003014030b490800c40704420014429160011a552000d51b90b8600b0f101090340c141c0000c00920f50001001e010990201200c065500c00c5500281c02050841e10141c008560035406501803100c4103048814007412150b00c550140c0e503c04d6450712 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 435475404 1250 435474154 435474209
    0xc0804020603070e1c050a050f120d0c210902040b101b0c03080c0d08101401030b0a09060b070b06030d1b0f3008062404080303090c0a06020c0a 63
    0x24550405c0201c5900c680801001081c04071503607004504540030700c00c2280381701c0d480310b1180032500301c03e2400300400340407038205c0e402c2382481101b1418003d40000c0143d40702c80c403480c100313030701c035050303242d0b103001d2071045107014486d0000e11401034400c44041040d06070b0240035003c2d844030958603401c07408012420400100b8054002d07680c01500580c13292440509295030700c4c403101400021510070740c0000c095036641c41c518070032641c032150124034010304400107400518050130b0385a000011803901041034003140c02080010070101b94a10b640f21114101040c45000c041c18952191700039180307028040c1e40c807813207000350350b120040d070010400c1c400c1c1b41251010095070402062040a6001c280100c1303000c150000309203400b552100903400d20000201d0b81150304650322540002049042904200300010280700500140c91440c074140d00c4c4c20015295401c11075006120350311030000c0020a00303040341c00d0700050040c1e000a00c4400008000030311515402d0040d00c441100c1c03540c2500406000a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 435476654 1250 435475404 435475429
    0x2091203070f030207080a0305030c0f07020307030b0601170915091912080105060c12030601020f0f030304020f030a0314090607061e060b0405011211090312030108010c0804020603070e 81
    0x10440756106a01c0c40c28142c40802c44505901501810100160209020810b40c041e10b9050b0f84661031580c8038522000e1039000303a034943c94030002c180110b100684042103c00c0140d409070142c0340440c81e106c4001000d1422180100390811409400d000034803c0025045014520740c1900e200e141d070740c6a020130b10345819001c40344401004541174074113120843c6080502c4003000e13511035000342c1c0c8410a0102e940700340070425003640e210074010014101018065a009a01441920100352030f03111400e15012000301c165465400c00020302045180050203103248120540c064480e80e401618003820b14000c040c10700c502d0b8000010506650b1b9140821909100d9100804100b2140700045d04141140b0b00d56007600c10516281020034032030b00500607039044440c140c0d2015289544e4042d000c0107000002c0e0504c01e0548113000800b0a41c3d800c0c85804101001005010348940c54a641182541d428482c8541400100750511003d0384458040320340c0708143d801e0135150311100c01c01143d554a03008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 435477904 1250 435476654 435476689
    0x15062114011e0507051c0203060f0402030c070b040311030d0b0a0602010608060109020307090b2b1a0f0315010b0a020c010c0330050109020d06050307060e1e09010f0303110714040209 80
    0x50400f9603489015031f01031401030b841a51240c042c030b070007903090104a110688420006400500c00d00d0001050101c80c540d005103e03207040440f207181c4001461458000b030b815910210703202c280103001828041110401404c20317100078040c1c9890880b8854840a0601a03100407e03000400201e504c2c0c09130601e04014004044440d035184650001324001a02c5005601d4844041103640c025400c4140103007250040004c441400c0c600480040240d0014903c1e0b0240c0c15001700c50700b268140500c000414000c00e400d08100303594030b1182c10001d0030002d40418440c10b119581020b0b401003070384015103035041d2001e01e03907664640282d072034000d4007009049400d503105400c2c4800850168101e4000d440c204908840600415403a0307010961901024000d5100040460300e141219181400c05412884000600100c0002403180800e03a1680f09030095000e01980ba01d081003010741c004040620468250081d0140500b000607800181490140c103034406c5402240303c4485550380e03042c1c0100c110b030f403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 435479154 1250 435477904 435477937
    0x415020c0a030302030105010f08101217030906040203190812130b04050c0a0902040302090a05040309080615011403070e060c0309040204032001110a15062114011e050705 75
    0x150b25005010350300074040c00d40003401181d401000e00740540d01d441e0241d01140d542c5048a8182520007001c480040300558941e20383d0310010407070440700313002103004108841c0035000501e0035006040c58500c1c840040e00f0300035050108580402c0420082c0d42803034481181320a220f840d00800c08611142e202c0b4090180c04c448000e100c00c015001a0000400405488180303815032764556078000c0f402180b1002c0d420407600e100185085105a210a40c800d01c681821040b0584074140b1034903200c001c841c03904540d401010f112a040d038000088010134a509403104d80380d4a80400018004c48a03070304014041e90703000c107071400081e0051050b2620740102900454849541703003080e045040c070000741d000b03010341c3c0c080d000f80e01540309076000d03000380c14500300030445410f070741d51910b01041c070041c003084009a440300085113100030300d141811141c6d6000039140c0448011304010040880c0780a43da0301582c0f628450307106000201d4181c0500100c4098001900d80d6030f14401c0e95144200310849211040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 435480404 1250 435479154 435479173
    0x106141903050601020705040c0905130e03070302030315040c0f0c050f0d0504090b1002060c09150408060f09010e120c0708010c1806090506040902090f091005091b030415020c 77
    0x1e056012500c550320990840303042642c0d902c1440304680d86003446000103961240103119600305921104c10159541c480040c1904000007100d080d9007001001320010703000003003405103903209002c49030075000c001c6070308001001c0c1c00c0c00c3c094199100b2105407400d101c8902e445070b0070f0000030712841070352000e10029a01405e40b810801003207030b4498040c03081098a410181c0140f41400a03d070b191002c4542c0040c002d548680d460410305030881085d96510161031b2124120010030440a00000d24200004106038107100c42d140a034410000c0400f1200d030314011a00e0903094000a00d14030740c150403241d041e615050b9880c040c1c1081d075650820034056090401c60040d80c0d41c0950b02c503050103c000003140005850f55401c5a070304000d4811940c0c082410f10042c03180205d07682c0240b50b2450014000c2c00c050b80c000c03010601d2070004172a030403241c0c3c2409a080007503042281c0070b998815000006144100040005104507000180000c1c01c50f00c00041580300500310703681101c0b400b04c20101140d0000b031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 435481654 1250 435480404 435480407
    0xe1003200a0c0302061f0e0903040306110d1d03030a020c03040509070c0b0106030216080a0318030305090c040902060a0e011103190f0216060e03100f0204080609060f01061419 77
    0x944200088006201d21700024902d035250007801d1206e02d422080012883d4a0800046140c000150036a0a2130108002c00000035165103d409015010508000d0315000d00424550854805030469292040c07404540c0d0521607020049951040707920800680f50200c01000500d54000c1f5044107800c45060414030043c240c100115000d00e034428000c450140c6e0701c524040b026070240180654207080d81d00012800508600040d241c9401103150001d1055800c1040c864a145545425004a507940c0d05104c0030380c00620002007a4981070f074080c0880140307a40807071501d220b050a280d040088420000341e81d0381c45800e502d901840c00e1012603850303440350125150065071064080e008200000340342c44c905400412120207942c1c01240030010755146c1441581d840c0d4411821079414001c00b95a995103011317034419044444051100184c0306c6040a02c4149040c60260020b0240d0303200d80e00708042e500d080584c10381501c629180c02514401e0988203200c40d400f80c07542848004200040024006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 435482904 1250 435481654 435481667
    0xd061403011b0f0806060708030f0709150212092d0406090902220b03010204060e1302040e0c0c0307140a030905102a02040e100b010e1003200a 63
    0x444214001c1110030b81c860402180d10b08181001d80210f102002d04003030030343c09501d00c030358011005801c144ca001d175035580d0254980d00c21144000c1d84060401030101684e800786491001c3d14102189070000b082381400a0740d01e0035082079010740c1c00c1c0000f8145a00c2d46a07640f440511040b0280b4800c82c030110b0392011ba10703814800848902031460850001800c54090103a40021034016001c0d808142c0b00d403c24410645841150000e41a01c42a4043c8591800d200800c0145000e0765000070480c20781d030411082203401102c03045281c2c010321082c414540580169074021200e404955619203054071481e0850059010180c9889840a04040e03003141c08a149004148a03507201d43c0e11546038070402005184503184600000e0705008403501031000e01241c640308040320020302207506c1c501d500041c242ca000311100d48480d045802002010189800b80003101002403c011700201000008900c5504407a0840c50401d51586010f000900c1c10f0066543c00d1300d07a0f0990166903041050010f02003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 435484154 1250 435482904 435482939
    0x402070b0103111c02060a2a03020708030a0e1009150e030f0106260a020307060906020610060f081905010b1804140103170d09030e090105100801050907050d06 70
    0x84241d40c402c81051a081d0f003244c40310301d0843c0b1070080c2d0440325000d00c049130300103040030818011403190b2099555103006000340c40d451340031002102501c1074940281081d1007984100c0f003552090200030001c3e80c1160100182c10342c10365503801c1c0c071a6254402c80300c1b40500c0c1d0004821130f807071612080419603c141720b4040503100b0350481d100c4130450b114140c00ca500c030f40b103849003001c0395040346003001e8801486c401c02404900c00b03c8400d1101500000e0a0650030303400640890a2154100000b5406010050340001d5500d03c2c404540d00e8800050110380200c150380040141c240d0000300300c6000901c08901072121000204403039130f19a19140d855501c5841c00014074124008444c020345020701036a40035007031400f005042a40703981d4030711520619208220382c601005024034001501d00b0310582c5032040c000d07643c4c5812000110305100003d00182c01081c050800300068100d180e8110071442e0441d007095441900e50743d100c1c070b0101c485001d03105401a103a0b040c850001014101980140d12 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 435485404 1250 435484154 435484163
    0x2030d0f2109140604050c060f0d1b020607020f07050904030314150406050d0c09050601050702030f0c010806060a0c030807021e0109050c010503060901120213020d0c020d031104050d05010b0402070b0103 89
    0xb0f40702c0080f50080e550041110018150352040e684107081d410008080c01403440300f01c10113400e004050103032030155a80204400408890405280b208a504000c00d6070805441e00145c16080e003c03d042d903440d614070340603550050a00760007060030148031b81d02011045c03e081d840c040190416101d1800200c021401141c411400c1c54808034840c0340484c03c84c1181e69000046219043c0b4058040002e0034000708000e0511000b4010b0300c015850901842208012442c0074290010069002504500e000361410780204414890118031f0340c0c02a071000581c039051f003000c1e0301c41d5036240710807841c1ca9018140362580000340745203002450707030541000008a1007101501c078520114001140c950000315001035105903000010400b6078a150401c0d180b90b80047c2c002c42c1480150001d039816a4410278180a031541e541c001854460707414441c958650030700f407600b0300295030407489030240c0340254020244524103419032030b01000001d40c4802c01c0420058020f64450300e550820a0604000340310964 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 435486654 1250 435485404 435485423
    0x7080106020705010203040909080909071106012405031b0a031d010203100519030b040f11010f121a09070801051201020f0301090c0507170c0f01020702030d0f2109 72
    0x14625001281c40000c3c0c03001a8019400c0030b1405c8000c502901000509683c219010001451b40e40c5550308501d1040c052900c03000c40d4461510741403450050b0507413181c9071102e203d81d60205200304a2003c1d842c14801882c01030b4580d1146480c1404014414950508504000801e0401c99416030007008446596000001810344010041400d030b00c0104d034800900080b000d0213212614201c19000d2050081c002c900b40c00b20348940d124420781c0c1003030724250fa50012101c0705234104030300d151100215000c00e2038802047c14025001812045072502d41c1602c007601c1d201502c0404018500d143d42d0410010680c881c603007010400501003401c00e014003401044040d07c40708008005008599908032985c0c40301c2d2450b072030416034030002c1050803000700803c1010001240403402d40072840c105008000c45039640e8140040d101450100c10918004003a40103018060140c0d60108080d505896241801e0304034429040c02283c102161520440103103001320765428078002c10b54400b4440c24850703001c41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 435487904 1250 435486654 435486659
    0x1b04060f050a05060715020a171e0412020f030d060801051e0103321029040b0f030f070e1305100b0604090c0c1b06050307050c070905040b070801 64
    0x1401400c05001e440e03000100039204120b0350611038010f200882c0100c5018246d21540340144050745c0c4a0007055000943c0e590210f5409440e44003100e40021805844050890a8044d112100c460081c0302902d840100d5003480311590090001c5d407210318010090703c0c2d0740c544140d6454010300c0c81c0c6c040e00e001580390000040c03907446000205058a07004034040e1800c5d03841c40d03446840e00260803001c62800c4034040c8900d035882d0080c0035100603140420001d0b001d2912610400d0044500b080d000160b051254410031501803540c041d0301d400d080040d074000c20b5030741e1000b010070740c0c0081403004d40340c040c4078844e0450300305000800c11f0310603240f8004502c540740c1c8402500c418403081400c1c028150380c1107403200c6a803407801a4000d00f500c1c503010f01014100390303031140120115200e0341070030400f09030040001010072000555036048400343e035004070442c40c14100000c0c51400010104414003000051030b40111408205e020001d22003002d091082d89024949482141010366180c1c01081411001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 435489154 1250 435487904 435487919
    0x14091e01020f0f0d1d06040b04111518040b0d06110f04170105090105040201080610090509100e090a05031c09020301020414040f050106020616030e0607020601030210050a200f1b0406 80
    0x145d440715904c00b40104141e803501c3c2c461503805000070b0301c115205402c01025041d40d8075107043c041e189a000e042d1190b16400d0840e0040d41c165051010144218603221614400d65142d183e4008c00300c0d005440065035070323178501c0e50b500c56200e0905a4449200082000209820440392405150b0b0081c402840b00d901c452042e0303400d9403c25070b00203002c0740e207160004103a0f0a00182603500c2e04140e00d81400d95a42d140b020600020040d24401d14901080e0414445a10b0100c5015005080711006200030305440c2c4506440380124444600c1e1110141c18465500030b858000211040d00200215503c5603a1096100c02c0807050301041c1c002c80c20007404000105940c40381904aa00e40d4001d0201903881264660384c0d8030118130b0a1090581d038507940e8418440030004540b0070b48480d0002d10303240d41940108964800003641060411008200080c09203900111103008030b103410700d444100038400c8041d14100f4030410300d840024440c101c100c10b031307200202107007a8488c1d800380e030701700101d9464400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 435490404 1250 435489154 435489191
    0x7030e28031b0c14010c12050901090501090b03010e18010c030603060c05030610121509141305030a0f090819110a05090103080a05091008060414091e01020f0f0d 71
    0x151100c01c609000708000e1041c41908421984140351012801b5084d0383e4400c070080030b00381080c00041000c290315829580042c0079101030442402c1c00c82c0003070300d0704080c40b0f154841401180c1c000c000800204920b20031032000b14154546060082c44180c0683c90b0040050a440c40300b07031150703400d00d01d0350001280101304072405404054440784d03080c5000601520300d2280900060407030760350743c408152840c00002d4004041c1082c110301180c40801840780b030000748009802032018003000740c584d100142d000811514a46628205003009444064055460304440c3d8003030086401044914501e01ca040e1110402c6d0901c00c1c01c1c00181c00c40701500b80019245540246a0881c4001c00103001081c8090098120740d503e0f45400382c5000341c9031f00401c92261501010402080b00e020900c0150700d01809440007802008848800f24604092403940d0341800e9503c6084030411800185a101000e40445490514455205903941c4d650302c11611690b101288048012303250220720000e1442604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 435491654 1250 435490404 435490457
    0x9010f09050a020d0312241509030314160501050f01080f0d0e0f04021c0f02130b0306010903060204170f0604030e1c051b0102010b0a0303020607030e2803 68
    0x30507005555500b8000c0d84011110150284901d845c86948006c0d12805603824404800c403011640955061000030500b4442d048821f084040c1c440a0f00350643c04103848084a4061500c2c9000c00a41d80c0092880d11030703860301312541d0296110030030a121054121038040c10702800b180d03001d1f0703988030029522404000d0f00350319603070410b42c0010000351044545c458900d1000342640020100180058100c0e03000030981301608a90300c0c030012541d1014800c000501095640070b40c6001420040148c0400b000d0141070aaa4008400700d10141d214001d058060b43d80681300f159100e45424014515410380099003071644202400710000300c0380071030000e016a616480d2540c890144400f00900455424809050a8048420600442da08202c0c00c0380081403e9102c0c0030105604000909540d291102c060080200b2541007000940c0011825809142e624000070741050150489007050142819464045003544045c0920482c030240f00030035078845c4c0c55419000d62001e910b004584d1612 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 435492904 1250 435491654 435491663
    0x711030d02120d241205061008100207060e0f06160c110d140729090a0e0601020118150c080c04050d020414130506010504110711010903080c0609010f09 67
    0x20f011001c0055440d41100d213400da00c03403100d1081040620340c1e580139115a07520000255408240d50014064103000d4550082949074035059500d00303140006942d60340b00c081d00714070b82c1c0d80006c2ea00c082c04803951001040301d510b4010780f44940e40c1804566903a030300540d40c2d14500c1c42a10751425a00b4020054404d0050b400728210411404080c10404644801101074a16062203009551000750501003003000d89000c1c80c0140103601c51080c03140c0d00f490f8480c10740c0c1f00d0180401106920703a1f18000604100c41800201003031550740c110040340589501020b010343c0118659251041005030076110100d02d8002038100545180758800b00c03041d5405503407640e00410100000d21050802075107040c1924000351020541490340c445019018404a030380000d01d011540d209002c00a09002e101e00510048405010140f403200c41143c040c4121140240415040c0400380c0c416405900c0e9040119086443c10fa22030340d0500c5d4940d00e8180c2159801c4e81035280c070050b00011003a9100b2881e890384c02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 435494154 1250 435492904 435492907
    0xa0902090612070f0306020a0206070509010e2101090507180c0f0809210309010f02040b250210020d1b08030402060c0c0405150103060906061e0509060711030d0212 72
    0x4690621001c50b03416402d02020b80502d02000c240e800e00e0341260b01c010b510070000169a072a00d5130009041c0600508010104401040041300e10b80c1c3c8009600c00c00d12044034140c4a07108030451402d05800b1400c160700d080d508198403001404000700c4c14030704030b8100d54480003034650074414603400c942e035040da001d01041c0300c80d24808150740b060100960101c03152086a0303400c000d441881345070103a885c4041005e41000420410500028050410b40f2200d064013582418244046407040e0b000b01c0c01c20140b5800301070300603558803071802c080f1100303180c01030502620007104090081d140c18500783c0c00c1000c19803001d051048a034481010b05000d6400045080c1551610f508100301070740072402d05421417040000c4920035640740c2c4189405181103d612030380d8200c0c07070b10014007030354059400700001500d80442040302ca40c012482007100501c0d6601c0e290f5500c02e0f81c1d01901c150140d00d401e140c000d400803d2070410050f0a0740000c250704e604a085a5900c007503201c1c200d0703440345100114060201c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 435495404 1250 435494154 435494161
    0x706150e22080d060810050f0105010c0201120204090207200109030b04110a060504060306061b060209010507150506040605032a0a080a05061812090108070e0d0c0303080a090209 78
    0xc1c00488886a40300e41103914448020603100d050709504007408540085a66100421440c0c2e81045006040801d003202070115140903518040d2152051103a14107111080c403405085a2080541210340410440110340f610745888032003000350010b0008940345006200041e40d4112130108508608405a49100d0780314110744d01c410340d605010b80111080d03c58164080501d41e0f50003884409007003590340341920380b490010020b05a40040c0d112310107202c40d054164200032808528a25034070b070450409aa9151035200403034452003100c902900f581901c07003e0b4513400c881900494010503044401348415900c0b0380401d9151122058007032030791201e54000d01003646600016841340007005203603800c015907400986090200e000421115904041c00f0000d05c81a440c08655125401d040200455480082203144c00d108940d009414407690800080090703200704071080d0000000b0b810181e40c01d049103413805003550709000c12800f240411000075141011440ac11400c590018046481c81d203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 435496654 1250 435495404 435495421
    0x3060243080a030209060c010e0d0e090105060c03120f010602010c080108030306120705031009020418030203071704091806110a050403021c020d0506090705010215010303050c0f0709020706150e 85
    0x1402102c0920903d038007407108400c180e4880024001c5800310000204451054034010350512048c03071408414010481103618503070712540440307419a10241d40890352400d02074001071560081d10801041c10746110100003051481c00b4086040351071a400a201100381ca010584403a00e0034001c01155500601c0066402d1030100b40089400120750180c503c0c1c540c8440c08203050216021002008a88031201c40c0d0860805101c5c1c040a401220f4075941c0401c150340c0c3c0203440740f0400001400078071504c15601c940301c4a6104890041c21070134410042640d414200010b1461002e40a95803c1d2901e84407004d80c0e44c000d030440f6a45582980c034207103000d003180d0800c200c1d0302218440010110040e4040f400603100c0d402c0507552140101c0041220b4070b04145042e1908120750022411500070760490b0411711207184125064035410300b402904d40c000c480381a86001c4121100000300c0c441e8050020b02240c00380d004109040c005c0d0b60a100100308a044076922690a21840b55a0354038000000d0420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 435497904 1250 435496654 435496657
    0x105030706120b010e040e010b09150906011101152402011109210706031d07030f030309290a0b0a03120c0503070803010f090c08130b100306024308 65
    0xf0414140400b1212000021408075981008500c4a42c3c1d52032031900000d1401801041d03000d04280384800040344148080b682c5408040c09060600ca090140e200701401c0a400c00d4600410141010035a1581c4810f0007440b03d1403500203c4d01c55007050107006c2e900e4818001c150200d0001206580340512039810301582907100c9254a40155580382088203841c0c00b0b20240005061a5401080380e04201386807074480c40f0081d2250001ea03001e1181080081d00c04828801c2103070b05030400282080060800401c0c2c0002c030000c1c51103803281852000d041d12400c9080c6400794020043c01c0014100010038083e84600500000d031807084501e40720f040d828861080100c80620540549080c55100e554a000700e070000e03041101128031184080c05008803510a05166031400d1030030500c2400e0a60084010404020019042020080000721010081951000155030240085598441081443e0302c2081c0301d03010700c2d1000c010203241c10014000d03444168502d800c08680c00605040c20303a611400c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 435499154 1250 435497904 435497921
    0xf0909090606100e1504170d0206100b0f040503060f0711010b03060103120215100e0709180f0e0d020102070c05010906120b041b110601231c050a0317010503070612 72
    0x1600c00c5011049801c0e1714800740000b07000c0481158110144d8404031820032022400300300071580408100700c00a14840045001c40352141d030401d03610140b2070f1402c1d0385482a50061b5030503200360f400340060326100d9580548a40903503a5032468200c2c654100318265264100704540c1680711100610108a64190360403622009004460b6004401c081031480810201c40e10206450300403010810b10850812442e80401d1078508a041607040c00c0109402489010740303504100e50360138115010301e010790700062200710144100da64900358403d0081c084d40c407401c1d084889151b440e1002500d540503e80c0902900c4164a80c1030158001c1400f400003005ca1030495a84a41c61340d001825001d07a4001e1724020100c15a210140100300351003c0d8036046060b402104c007228500140c100003010b000f5082842130b01122a040035000b00841c20304108260100504030f40640391040e0300301034028901d04d88400441304103007040da80e25000c060301c03a0480d10070140895003c844001c042915903004601 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 435500404 1250 435499154 435499159
    0x90f062a02100203130806070c0f02010e090c0405040b060a023004030f03030c0e0f10050f043506010302281707051c060903140f0909090606100e 64
    0x42030340c900c0d00040c20401d5800c4141c0c0242e0800034800c481314508006640240145100401039810b212170014080d407610388020b08204502541101107a100f461076035a11040201540501e041422601c44c0c22380c820300c90782e0300c0745140400c081641d044c403006032001c201180d0003402c0c4094a0b200440c0f05145100c820300c0f440a00340c1c19003800c5001140c05072000d940101c00c0250600114078000c0d040381d54034a41e050505c100340d000d6100544d6030344034100312060142c58501c480404a5419645030081c01540391b0803100128010030304180d1108400c0740015003149410110366182c60030183d40f00e803402e1060040d040800140058280b911182680039440b250b200e541f44005200754084810304c0e000380c0c00035081c0c15030140d6499000c11480f80680070850b184020340f07040c0220800b2a4162060040c6090784850b841030a05014882d800000070300340500d030b5034400a004005c18254401a40c0c640304844840125584c80750015056115039005040074046c080a44425034a1410202842d507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 435501654 1250 435500404 435500477
    0x24071112040e090f4204020621180d090b03040209041e03080f09030c1b06160602030103020a210201121d071d070f0c060b040608030a090f06 62
    0xc070761408004d050702500d034000354081c05c00302c04100003805920011002d00300045446000c032803007140451250b0400e074101c840655401c45242030f13890007c500c3c010840c0c848108401c1040c0d8a0f0320811000c18542c40c1c40a9071802c1038010010b8070740d00d03c207005904026005000160050a0204080750414060a8100c509071041d9007290605c2c01114011400141da1509104882c0c41e040162a046200d14002e103040882410240d80d9429000508052085080b0300c144101e499800881b00c0450500d490028440307014203005010758000e100c02c0780a00010180000ea000ca12902c2c1091403112420744095021180c0044500c003030340010005086903140c0040c900001c0c0e415109010850f180c0207031850b1407405130001d805210006806044511301300411a03443c0c0e02a1703a030742040b486820020900320550510b60020000d0f8201d15030030619110300402d01080000140010030116614074031102c1e1100c20f901c182c140c1d10b11503940070825840001d01403940c401103020120008031403d9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 435502904 1250 435501654 435501673
    0x150108151f0b0307031d06090c1903020603040c06081b1b0735161703040b031e0604060303090909140303010603022809140324071112040e09 62
    0x14422a0700030b8601e140800e68407030300d00b501c00303054a0b601000d030701c50b600c0a45182d00e03244232002c0d1a2140c500740e4900c1807034140b280120300001e040c0e10340007850700981030f103880746054a00b05000b0001400fa03c40450032080014014092686190030742c050004001404e241014440c000c59040704c401d0058140141d010100b4001c002c4242c07000c2071403210010094000c540c040c46807001c042c2010b5600d207a000711001c05040c44445a000080360210740224240c3c650f0100380b07038114041c1703801032085120b001062191401c0031031740301c08542c0d1b400e0100301150b803212001c103c11190513110040215103400d02c01c00242b20154490309440b4050301c40400140c640b1501c060556000760051004031b0b90100750a1684886100b01c0b400e4100c41d110b40c1900103803102005418001c0910400f244c1c00d0400c840f00703000d500c06001e6116510300c0c030301914403080307600c84002c03c515008a401400203020308103141203128001956101d00151086003d141908114941e000084001c081080900c5244441d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 435504154 1250 435502904 435502919
    0x40501050d0f2a08040b010b030712020f0912030a140315040609020a140304051507030905061614120a050c12090a03080606040b1c061502150108151f 66
    0xc0b00c507103e0821510301052400030700641d410101d60603850707040094000403c00001c038000d104506540d59403c00355101d694503441110036000c0000501c458a0001c00e0f00b00940344420080e0a8006007201e26604241480e02040d540b070103041d0342c43d4002100004c0c1c0b090081d01480086802c94283d034901c0e140308c0002c00100d0180c03280707980100f00441d40041c502c0030499200703e1059503581a01c01c018034604003a01ca4a07554a204000707410f00059040c08074241d01d000c1d034040d60705035a00c07409858052400d90003005124502c0542a80070030000c18540041000f4501100c0c00420b1400e61844030751221010a001408020701400d0130781000c10504010032800c0c2c94041c4140000310052207800014580146139070805041140104030600c0280411080c02064484076002042000b0340c00c00400280c6009d0081d592040e6100b43c108000d120141c0c0d40402c042c8400c0c400b80c458012180d070394030000c0303a460314048000c140c0e1000040c04513810328802e01c01c110b44480541443c2c0d2410b601c0b090f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 435505404 1250 435504154 435504161
    0xc0506040605070320030a1505010522050a0e04110102190f020d0203010509101104060c061e0c03060302010212120f09030d150311030606060d090618030206100e010803040501050d0f 80
    0x40c2c17205809008000c00c6078584050146c4030400091103400100e5a24001c0040c105006100c2c41095500388582d000e12a80d5450700b042000b05001050040c40070f41c2c851901444d01d6040d02c040c3c0c2c0c0300340b030b80e001018954000259010031405200300104c0340d09890f210a601a001e03800200d85c811b40c00840c1101590702401594050419034026060350101e04400d04121004822001c0220703030240403c0001c030781c1014801052a4000c8004141c1800d01b0328400d0884c00e04880c0c10400c90324013424000c1c0142e05a0180080e64401e8003210301c3d60100f00c00004142c0500c40804610100b1213001412036120741c6d000e00c0e00b000c40d43c01100c0c02e00240318070420aa0341c5a40070064450a0030800304240040d54055200845068020701801c0c104103000c200e45200303100c48050b0164840c183d103010040158088200c017642c00f000d489000c440c1e860b000703403140c000784c48c03003013894866240100c4c3d6840c6903e9168100d86500000b1f42c54545014019509504815000007146594900c0002000042e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 435506654 1250 435505404 435505451
    0xc12080c01020d050f1008100b03010902030d050a0201060b070807170c030301081507082e0803070f0b010b0c0a020907052b0c02011a1318030e040b010c05060406050703 74
    0xf0102d40b615144030703070281c524001031034601e80e0b5217039039400c0108940224100d644000408008607680440a0119000d0590040c0080d014031270340001e1080300740d0000240c495003c10b0340c001e200f21a40d80134445024028440301805001c0e04022040008150000d0707400c018014102e080e00b49098203506d20b06540099202e220a9008101440c4803c4811841c0130382c0b02d10282407001c8241000303007951142c400c0340360023004042e264140a0242c0d98000e00e8a100070003801080741e40e161000c0c40c120303441121000044500078105000820b951010b20256658a100702c070040480f081180c08000c000c2c103014202c1ca0500c08208601c402462401751301e5014841e03030f21850b6010000d501c4280d00bc841078a0303280d07011079141021041628032014034110101408807403081d2078103045029107004001c419561075402c4810041c00c000c160b00b004a00401c48000c079820064400340070019110201d0604000f011034208500007400100039501058001d5110300e0000790034052440c12400501d082c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 435507904 1250 435506654 435506677
    0x12050601090b04032618040b01350108010605091302040f02041502060604050603070308031f0e150a05150c15010602100b1e10050f0f071e0c12080c0102 67
    0x402c041c410080480980c0404808407680f01385486851b0181c0407080301034225441c4959103c02030307040c4aa01c9448608404030408161920024684d107040010801c407102c001e10340140e00000040c2020306105580845030044d05212b061b95404091001d00c4009400c00c9070b0040d0b5904e140301404c4420710185c0094821400e14000000c00300c20040d10b0304070018817a5100e81d05103002c0020035280801c001d4100c1e42c2c4400159100d440d0641c2a80c1903440c03030100d521856003041c60000d4049441c8401c1070051301c004032100c03c042c8021041c04511013040c013507503804c0a503c600c891421040c82c8002c0c40c912034140d090781d61001d008411200c3c0004207900800050380091081c240c840aa0b00c504c40d030100003203c0c0740c03000070280381e0708a0040402840562081507600035064000e401034044544060307048503882d69420b80b00213000700c950010901590b84c0e03441c090035160140050510702c0d00032138010392140010703490300b140384811091400302155001c9040c0300c103280c0d0702400d00180881040300b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 435509154 1250 435507904 435507923
    0x1d07021204030606060818070510020c030f011e091112010e0703051b09090606090705120708040b090303190e0a0605010902040302191a030717091b1012050601090b0403 74
    0x30084000c1c40700038045c1c50400040c031008070250031f031000002c1100440718196078520f44d6203101c40c0306908002c4550035294043c01400c01003c0c0c0c088040d4041e4a07014403a101c107201d044481c5108100b01d4190703ca005001c1c1c1c0008ae10000360b8070300003c0f14010781112000104d9082010b00b286030400542d80c0c4101e40c20340c404410b10403e000d20381c2e039800007101c06850102c8203150080c0611b5807400058001401240d085010420481c8907600b290811141401d1200241c180510014510101240c05440c0c124541c1c000c541c03180340100c11240205a00001170310b9102e0f940503d0001044280c0e8803c20620412204800080c4140203460007030022010040e1143e1450040c40100000c00703a01175943c2204041c14401c1d40c1c0c0b44030040301060525403606441e0783e56070400355403040c50328030750142e00d80c1c4000070020411000281050014400417180c1616410f0030240b040d90841112003d0100350036003900405008103600c00381c1e02c0b040516000451940c2c42440101c0c81d4043c1d00240c40d80c40c0d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 435510404 1250 435509154 435509159
    0x18030a0f082d220201050d110408030f040e0703050f04020f220605040b090103050601030f0f14010c0906090605072009100806070c0206030a02070f0206031e09071d07021204030606 79
    0x18283c0980c2e06928081142d25103c807220350000b40180b2800d002c0d05542c0d6030321901007004485c1001a2401740c1900c07812665544000b405090045e0000d01c54142048540d8001940044c407a0050601403420072010b003000da2503039401c2160b400da146c011150410b030904030010715070140018041e8194924900041c401d410001880150390152031500d000b5510f5500400015000040309411a90020501c5a504c50341d4549440011503032103000d4040d20340100e09d0a4140310650200d0001c080c2034a41c10603a0342c3c0d804003035030400402c0c8204c00120340f0034400071000c03961903180c0f541c031001c4104010403040b4610000484050058803015600d941301c40c01440f21042c2000050341290300390400c182c140c020303640000d47c54070008243c15980c03a0040380781d60401c1a40681c2444090b80102115200e1411200399810101649031105909000c4404500b01c0c0e100421000d0a039040c038100e245181000c1000108090800740a000840c400c8412900c0c400c001703680070b000958071a80008ca6030303d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 435511654 1250 435510404 435510421
    0x92707090e06060406060e01050c03090406141905090a0b010207030209010e18070b180f031b1318020910121209080f150910020c0618030a0f082d 64
    0x2c0c0185030900803890150280280b40c1c000780034103038840d030902e41660f40d40701450213a0f04600030004a180c0003414171401003404102a1012070308004e044d19a0904002049200ca1070640540f2640343c1105540003c20100306140c0c010b02c40101c4d06004417001607942c0d9002c100401e0b4241d006000d4103c86106000490001189248013502120018501c1c1800c00350468418071400140003040010640704096070b846024041401100003010750b001c801c00545c00d074600404132040b403445440d5a01c1040c11070b080510508541c2d0800c815400107658070f56080c040c050031301501400040700800c90002e8884030340c0421801c458400d00c003501115030340e014003401c40b00321900185031a8010242600c080c240c005050340c3d0507070640f086d210551321407060641c280501141c244a2a5000190603c4806800525103008400c10503401d0f490140c07000300e858580c024506100009216803040c0400103203e010701d42e030130402d66010030902c4000340014002440400d050590054201810414041d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 435512904 1250 435511654 435511663
    0xe04020c1609051305070605031009020c0c040c180504090206121815190f06090204060306171f0209210a0605060f03030403061e060609090c030209092707090e 70
    0x4800140084c10000160340e6140c0340e4966002d49020450080700040180e1191141c2400030840918115039422100b01400d4a658664000600a5042408058250348601e0451200d07040805c101c000e45802c00e01044080c007200f10f0181e0340722405001009114515054580c0208c042e14140c0d04581c0412640b1170401d05807291b4241320060507410480c0641000280d00c010190b00c20000841c10840c684000c001e1104d50014a5018030100b40410590f400d07074407400a60350b02050403a02440003001380b5070b40c3d00604c1d0700c0da03240ca2855441250031203400d4024156103e402844010380c41d44000780710b80c2c9500345c41d18420745030b4400d03004841441460302c582608044192400d1001460740710200703559208034840103002c2031b40c4855808022400402812082c00d10b110b091107042e0b40d035540101401c40702d005200441340390030101904a4040d10840d9204c0f0b4020b012002e0f81e644240ba0041034440d112194400704019418250521406111782e00141980b020000340325050b01c003080d0302c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 435514154 1250 435512904 435512911
    0xc05070c08010c0806010e030f1209010305090111040302010f02150f160807050913061205160f050d0807030302090909010f0b01081306050606130602100e011b0e04020c160905 77
    0x2c0e454003020f000941d520542c881c2d4482006c0c2031a030300c1c130800303200401d01d0305811604c1c020b03603801944a480c42d01c4d00010000d110503007003660144004c0c0c40c0e5642540c00c85a541002e00c1c08000304000c00c00040d40960481c40490ba40350068403142c1034241c0002280c0102200c2e15500318400004101c03042c00940c0c954010118039240052803450414800f405034801d00f04441d01c14031010b4107410303800c505604030708041c044d10040040c1d011828980035648075000070300c03660080c0c128030020401c1c200c0c07050120202c5200030200c0201280300d40700d804150340400c1c415020540c007040044050746602c0580390142c00994000500c0b00141c4024200f101c207405502c60401070300009010340b60401110039565a034224100243c03580740d400c0052034500c03070400f80c03490040d42183d000501c2c54000c01c82900f5401121000d001801a84000608844440e404d8640e40c80c500010894400c2c85411007071407407074014200501d042d40e00000b803403410b0541045c0c3c042c1e40303600c00350a02011000d809410381 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 435515404 1250 435514154 435514169
    0xc03200406091e02030603030c0f0f07082e060b0a0c02132013121a01060f08040b0603161707050d15020307050d090b0601140406050f0705100c05070c 66
    0xc0000300200c0240300c00f0700c0900c4845680d8001c0046242c0355001d06c203c80508240d44201d4803003203050f000b01901c541401d80714541c980620400003c000b0008554a441089242d007001460214503910b803525400e01c0e0300542360140c1d03e10000c0b481c1c9010300000c1454691035140c00f0054030703c40c41081140d100c4120f0b40280c880c20302060400ca1400300c46158042090f5407500f949808070040c1e1500000a07135485544070786201e4075001c00b030261191004c0170441c0c1079508400c85a07201e501c1034402415200c1d903000081d50303034400100445c000c41c04a42d0032003002020b965403680d11801da455078000c541c01c10700c00008234a02202c0803140030000c94004100540b900c0c44045026120f0404146813203070040f0b4a29000400201035a10500459903000340c960010005450300c0d041494008000b100c0c0c04d80400d03190020042d07060340780d078142e6003200c0b802d543d103e150070000280020141c2049804448600c1284c80341c140e1074105001b1041c01581c00d580e515210000c50400c0c6800803010340c042c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 435516654 1250 435515404 435515411
    0x2070f0f021219020d1109010e040c0503030306010c020118050613080f0f0703030c0f02180108060a050c0901110307050a1208010609030506060d0312090c090b01020f060f040c0320040609 82
    0x146121140c43c0061100341e0100c0d00c0c1d50585000781890a0fa03e40c2c03a540300f640c842007020011030800c1440b0b41e40c50049005001203000e99071510103040e500c0c80255034041c00308048026000c01984100e0400d0000300c40c21010010895071000032030629002010305d1601c0c00030202040c040c2d280c04108138180124500001c02000c400a1011501c40d001d502014041000d83c174076030001d01a0050a1074081580508041040401c0c03800707017081c68000b8000d401c0d03140203010104043d00c9041c001c1a020700c0e50b164007113250240180c010b40708101c03000d40b21b400600040c80300c5008250300380b009405c0b480c010140f1100450840c82c0003400e03403005802c0002400707150f10060003c1200028003992040095804520100c1541820b41d001d03e0f0100c00c1d14101400c024901040082d40c0c2c102e00101d400c1d400003449542403440059845440a0a07140b15a600401c0042c02c0d40c1d01160300c2c10f412500582203000000d80707903100c2c1848407031510450445461107050b18202e80c1010321480e0001d004090042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 435517904 1250 435516654 435516673
    0x5090f0d0c02130c11030705030d0c0206191d06090309010806030307150c030e01020d15090b0f0418021206070f1d1918240f0303030507020102070f0f0212 68
    0x280300640f2125000448984c0d400326003140f603000341924203001c0c52050440751201c08502d00259070780e0040d050040381905006160030094000610a80070703204812500c011242c04817610340003009108d10311400040c1042e4400a41d580c00e201450140c1ea004010b9a030f0380d9900c178009088007402038207042c000d0b40301b0001500400c50800048040c0f0001803004120049406002c501910840b905448070307520000f000d00313450040d9440366000c3c100010b40d049040742e441c03610a080f2400004000e0304181140050241da140650044101c14a0403100901003589900454180c0d190755035880c499503c0740701840215a0081e015514943c0b603403400c484124011004c800c1d1030150408a94004d104404607040100d02c42c06991020700184001c0c0c0041840b00c1501c00e016190106103030029564030b04246002882d0744405005031000529403c51240c43c0daa012001031178001c0c80482155400e2012100050000c02d043c841c503030103845800c00300f12603801080340c0d940c031100040c040c035031008007813 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 435519154 1250 435517904 435517909
    0x602041d07050703031a100215010501110309090a02040f0312080a15170f0303090102120a02120105190510051207031413170f03071b0c120204090605090f0d0c02 71
    0x44a168680c14603001c030f180d00380c000508094071700c100c0c1b0481c2c1c07007819084400007075540021f680c04158070210f01211181d0361440150703a0446000c015a42c140c0003040100c2300c604140c0181908804030600040c5880d94600d841c00307080580e0340085440300200900702c82c125a100410303030f81061252908000403580122040d2810f601d510034041106c084080f01c1c0c02c004801e00a044044419a050b0f071b50301d150808131607000390b00918410742c400002034040340281d441807003903c074540400001c0a50796420141004495000c40c060450301c001ca0903008100e684501074902c600703090549400b81c031001c41c903006142c2d4000007841d40c0700705440d040303a4809160f814050203400c4005c545400c0140519400c02003240401f07110075800c60b890000c2e0349107000c4107850045100d00b01e0350362070b40c45802000c03108214054200c400074101002034032003407004070402b0402058140c80140002a084030560715407054a004460038249030f000301d5201c0800100a11010480f01c400d45003554980d03615500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 435520404 1250 435519154 435519157
    0x30e0f030a0507141911120309030d181505130e1006140d14070f020307151e09030f111501090b0402090d0b09010c050a1b03020313030602041d0705 65
    0x30140a10204d9030705407403044028085001601502c1610380ca0035200d074100b40014041345420203000d6480b06808000810011003520301500c0d00601400711458408800c91322081d00303c01c11009042c1840001500040c09221051011215200c06855480c1401544103809042e4001c0b010602050200b007450b4039000356001c261040c0341000c1c5042c1c034000000450902420321078000d02d80c60b00c00280074501c07050110f540300341e0a550b51070001b40b4840008030707164000d200005040000074000c1860b8080c2d503412040040c0002401c1741200c01810072103c003900c01c40101031b008102020740c440c02482d80b00c5a82400d00140000500d0180e44088a010803028144aa20409aa1604020300c142d545804480e50340700000c2144030700900d030342409041840203071000f20701d0790720706200c2c800380d540a1340c10f07629010744980b2413020240311445642c117800c1040350210114001040041584400d60442c0c102640c003034040140c6840c00e1a082d0342200c003084012203c1d048c0d00e038082010320384d031210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 435521654 1250 435520404 435520417
    0x50901061b1b080a050c060705030d0c170c0a090f06121116150b03160b090111010c090807050306161218121706030303010501050708040506030403030e0f030a05 71
    0x15403024000c441c1c20840340c810307100507581030b50408440c4009442d410000303003032003403500074025140c410307a4030002c0180c2d52051120082c1160030500558440c000c40d0360200d0320480781401d1090003241800070710302d00140c0071191281c00450100c1c115030650f500040c1c0d80701900301d4a941820603418014094404050701480265154031038203000c2c4920601029554500c400e00140d50f1600064541824030310b124490003107519103081e1100049160000300d40200d0820285100c803820304100c62001c0c258001031001e4113102c1d40c5c00f0441c4145401b40b1800002840716a21150141c3c203080c0300c5401c000701c0d984410305c250300c04014002d0b407181452203411500c5060600c5110b000c0d842c1f084801614016821101a00d84c0070302410a002a584420303001d043d607070b030b143c10140038200c2600a1154041d2045a01944140010b020310350103440105001801007140600b815950030000303505500c1107608500194030303002d00f2481d0300d0b0108095030610f6000400f445c00d00140e458020610b00800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 435522904 1250 435521654 435521687
    0x210309270908030103150605090a090f0b09160515040b0a110a2301090f020f040b1e09010e010e0a02070830090a1a06041506020a030905090106 63
    0x31034031209500c045032065450618800c0c02401040d00900b080e8929030402d11098454071103900d8400700c90242c0b446034000f0f56600900c115001e0702c500745000010045040d04071410000501d5072070114110642d03d41c0b04250140040001c81550010000c140159600a072f018246684001000400c603106840c1036908a81d4001e4880c408903804403914000403082e100140102c498040c1813120940d210b02c800d8100031081481c0003c4003d4040c00c1f25001b0070007a0110b030550700c203000186080301d03080d5482d280080000c01d9400340c0e40c00048000065070504585005189034541590800628003070050013018890603a43d0315002a8040b20f000c01084041101c6d030000e100c004002c0c130081a140380300002d507501c3e9a03081e10b0f0300703000c68544410541c0e03280d00b402000016050300c03070004154502650108070103140205d4407090f4240f110010300301c00d90154507030441c4050141c007203660400901d00c0da07000b08003051040c00d014084200c44e8001c076000301c03511401402030341e07044030700d4180500c1e01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 435524154 1250 435522904 435522929
    0x3020f010e100906030c170406050604110a0e0906030a050a08030a090602042909010c0204050402060c030a081509040c0e090f01150602070f06140a02070b0d0204210309 74
    0x54000489040c251401003079840b060100341200140d41c425a100300b030344c00984040202e4130480401f82d502519010301c10141020440c002070000e2010341110b5000b0030054804510302284161000c900e80109070710100040714244983e0040c580b00c000d0a0b009403042d009009249101c1d143d054071190102000f80c180d103000000b00301c01002d07540c48185810740244045440e5522030000402074003001d9541c0b1400a402c0000f0580304001008a4a86090584840642e010190b01788405098014000d030790044092154010002042c80104400c0c44160381d070f001c8500d02a81c044201031f1044040358001c01c5500b04010004500c2500078081d181c40a030340031034581d00d80500600d001042c000441e155420051038800c508411021803060310415029030740c0c0b460b22100e03042d02c44443d0703100740c41c001400c1400c0614000303061002807010360090f2050380c41c070380d0702c840f0103495940c0056118900c4580c0083d04000f03045a08901f103100362041c841007240502c458500400100090113031881c07880e030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 435525404 1250 435524154 435524179
    0x14091f03080703020a081204030f0201062d03080703030b12010606020c060d0b03010c02030c1b100e01050d02041d06030307030e120a020a090509060105031c030c0c2a1e0302 76
    0xc205d00e102c01688603161a5581c00b4403807011501c00d0054800302e0100d07600c9103007442414018051300059070b01c000d440303910401114403000ca04214581d17141004804110f00440030030601802800458065100403403821108014030a0178074407540d44003066403404030240252503011545080b4010221600d0703482d902c0b11840503006101c9168119415860500b09250641d004806080b00300e0005044d030b8003450341d15002e10001f00341c51001c164800796514a0010450040440c00c84074881803512900740348030650300404981c843d4002a0402105807400440008150306a903071041040c0d01035420480035542c0988075a0900040c24412141144c0e840d04800c4104041140b940c0c009150b010915940c4c14920000d10080d581c03402c250040c00d002140c541000541100f100c20343c1210341d0380030480900202d004100d40c420040c03c03c0170a1480d440402e262124100c030541400e1202045070b11042c0d140301c54100f0a034495080072503010300701c10080c1c0e022485842244d4065818104014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 435526654 1250 435525404 435525407
    0x70c0c05040e01050103110105131203021f09020f06180405090c04021218010c05070605100e0705090f010315030b04050a0501090f0c05010806060a120e030414091f03080703 76
    0x41103030003440d0060310305009410a0b280541100b412640a80d00b001d0720401510011a22842011180c000f0844034680070841d424a07651005680c502904c151110380114004441220b0441e144103402c0315110078005055191081813400012801c5407000d18003840310b42007880c00110305424502c52541c0e040002c106071421300480300081c3d8020f10841d96114407004504982d1801e440d84900b0001b1243d291003407071700c14071036041040f5281d1559414044aa500d941c0602030003401d40e4040d11420000052009410b042107026103a182c03030700e0b512040524103002c07215420f400828101807c250045049081c011141d0064a411600401441d515401c00c0d40c6000110703403001748298a00608801409880f000b4035960f607105e1440420300980d60001115006015610307154403510420292190a01480380ca040c8254000c101084103c400c121440c11a00310303620421a80c81c0342c0c8680121032809400301030380703c5c1084008042d009104c20510b1800c101c2804018961400001d0368018903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 435527904 1250 435526654 435526673
    0x2112290307080f07061704080301030b0403180b120906010e0a020a020102040807090501080f06060625150f06050901080309010c02031203010909061802010e011b0602040b030603160e070c 82
    0x500c9510203c1d030b46401210141c9030b40d0042c9102e8140001c0e10701c00c204040d40c0d260302405005a412051075400c59007951581968071001900c11000c2c8044080b15000c5012001014402071600040340c5482e100c0c69911011004002841c180351078100c2d00041c40151020040180c002c1111a030041e218a00418103a0080c03040e50000b00291080354000a1000d8640c0c000a0613106003100b9500303284142100b40d690364000b070f20740691221007401340400300c0e250340444100011109844031400c0c01c5079103515910070541350400c500141c590480072003904090080c94002c10060b030700c20300d00f50b1505810a4590240c22a00ca0400c0314009014041d03603820091a03040d44074080285a895a64105201c01003a02c440c0032030b10582060b210501d07040c424240d40c24100c0d01030b12540001110007004580440e038420b0880d00f008840080080800c101e440134102034105001807d03601d04241c4d08240ca040c981580d1508a0300c0c0703440301481080b150020180c1c001d4450305080888446614200d600e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 435529154 1250 435527904 435527909
    0x100c0b041101030f0501090c020d020f060606160614040605071110020a1103030a0903020d05030415050403030204090903090e0c0f0a0f23092e1101092112290307 71
    0x4c0318100310000c80c0340c03289540021000c2030701d9021907078500d041c02c0042e40c40d120584110001c0d40c00500000b21a402c100380102224881c04041381c035a0a00c45e5141d40407a84140c240100c0481e10500304410400310b403044035000f4026090500e80c0c50042e0016a03507030303c00710201d410b420b6004600481c07803500894a400d20070307000d10250394403840c080a180c4014204400280c2c010310035a4180c00102d405241280e02a81c1c10090b41c14032040600340600148c00054022820140e0802c000507011405104102c0302034031a0b07a980030003511304010740480c90300103050844000810030602c002000320404403041c81d9103905184000040010050720405515100f00c1292850500c41030064240301004007100c04040310403118404a4800c40102d40b403049109200c040c0e00000d0011125008040751415941b15100120320548980d88015040070360b0b440d00c40030b42e0385074000690803e401030b86408000e00826810056440d80441c000d00c944001e04101c035420407009500740c803070346080c4840e401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 435530404 1250 435529154 435529181
    0x4020405060303092d10020f100c050a0c030c0204020406031a062a0c03060a0219091536060815010207090e030c070b0408190b040b061201060f05100c0b04110103 71
    0x1b010850118007a40741c0a089012242e0b80c05407070340301030b03100405106002e10703500c13940c3d102414070202c088143d40541d24208280c00340704e0b82c034502c0070059540340010806401c50b550046502c1c0c42b46014182d205e0b01c0360048905c181e0b0103000303081d0001c000409503e96007112242000e500c0100b03890641c28010f0712507026405020303040030401c502c900c1d078000b0010000608034507040700320700001c00c0f100b00419000d081103070300020803280d44251284c0004d407070829100008010709841541c11218244003070070441044402040b04001c801d800201c000d900c0480060030340d484c5412840002c1d01c0f4901d50103288200d42e170340c031300c4059004010000e9402a2034040c00300c2c1e103480d458081e4103481e86c0291241608a100781082e00010194820304240c00740ea001c82c458071991543d6403440d00d200300040c612500500c11040d0801030800c00d01503000100b180e0050300090350300b4401802100180c030342011060060011000d13000074544442d1300e9009821294007440410441c00480140041030808034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 435531654 1250 435530404 435530419
    0xd060209061e12090c0a03030f050f070f061808070605041a07020703020a050a0b071115120f07110c090601050d0f0b0a290a0216080604020405060303092d 68
    0x4510200040007011079154100c1061034075036030110895503454040038017903004000e80c101040068020440010300440c1c0d41420f80c14140c0d00c000304030841d0001d0006499a000c01e04043d0180120391103280700f1010900440c03800a034035501c1ea014180701e04280240640d95580c000780a12115169018007142c3d40c0740011254149440e00964034022804260300c9120745100000d06440d040c00c80e402111014441c650500d0000d840d404801c03000d0f00852508111010701c05041c544188008041d0003001d11408010350414000d12064034200511000901035501e0701110b41d080d000906060f004011292030955135580030040301c82d40a0b01d42000c00e001c0c24208040740302401c039005007100c0d2b40305485416549540f0303040c01c920f05800003244031070b1240014412540e198030f54014640c02c0c400d4012503010b03002e140c02c41010b0b0b00e20b6500c9040d194100700180805c52600303010726074109100b00d0040d0b04118074480052048411040e20b42d00c40f003902a210341506c08600c0701d18540b00d100030300c0f04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 435532904 1250 435531654 435531697
    0xa08090112050406140a02030115030e010b09041a070c0c0b030405010f020f270f0913050709051503010e030f070f0b040f0b07081311180907050f060301050d06020906 73
    0x4401410000310000c285ca640d141c0040c52260003482624121020100b55091182005006400030034840c41442c406540380c040c4500c030f584031840914004ca00c40d051030b0324405488c41c0c85072030075400904110104082d44040c08042131009105500303540300400455a29140c0b494a5401414900b40380c1c00d0071800409e0030401245100c0280890700140804a8095100120a0b046102c00d0441c4982d01c40780c84001d107034603030416810a6a120755400e440302147d14040d250302c0d150148070783c40b525815458000b04204078403031007c1400460003d030005d00040840d4144036499005070312112200000107d0f140c4240070603118141251504984480564105030a00710000380040c1e4054852240800104241611812006100300708a151908420320f42e40d0b43c80c0f42c246914600d46a128544005446c40584000300d004d0103000312030002e042162030401480155164420220300c036220500c010015a2240a860700d040e50b80001d0040e62103041000044242c021a40540703034440002588 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 435534154 1250 435532904 435532913
    0xf0d050405010e0109050901121e1506080d0807120209060c06010306061a030a23090c0f06040b030a090f170a180b1902101404021f020a080901120504 66
    0x60041d560282c0c0d5a0003900401001984c40d107200d0302c40c035500410000e004210408518070455030f0305108080306441020ac0303007031020107040d10b040240d810084c842c0021b00d1805003440f07600f006182c40400b4180144d26030a001d45404130080000b814070210031050314030f507a410f904607164003100409550711340c00e2000c60596105000d000440c0e05500c0c00d03101080140026007041030080521510b0f516658070382c1581c1c00944123041e6421449080e00030104103140c5980d92107441440840010104824000300304017512555841c0140600005c0006100d00d2000d1012243e2000407a44d0110307145040c0e107011000142c919402400481508d4502030080400b0340003841d0b6412036660301c44641c05d0812040c0191400f1348580c1450103c2040f200030b080c8501010032900911078015140b40700c40302036450b010f4a059100100940801c0004c2000f146411044103039a0003003c038442c6021b00d089072010350780c1c00740700c18068104d00700890071208a038440c940401021740050402d20840c00c151a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 435535404 1250 435534154 435534157
    0x9092001031e050f0702060103020607140705041d060612100e0309030a0c062a1209050901060203090102060c03070219050f03270117011a090a0e0907060201110703030e0f0d05 77
    0x21200f04e6501340f60b01207040d051000410350b050300d400802d04c40c6019400d655000320040302852030b00480c007410b40c00040982e0743d8400c85070000c410f031514200b848020100e160900d840180010b00c80c0c901101550b0001500003403051701c03507400a00004a40380940d06191442c040c1c6107004c0c1d81032040c00101130801c42000300380c0b000c80d642d075110301400d00741803d0011080c82625414100c425040144c450100740443c8101004075010b0601c16035045d10b0340702044000c0d40903000100568000204800196410041d25030300503903540c10541181008800203480d400c88203070450111641c1c0c121b031028040c060005403041484030b000c403907403003203404400e0421211100c1030848000c0c0c4c80340707451070320b5018243c0300000c814001d07281001607083c00051051451008105054090148a50a200d44510700c420b009080c2810302c12055180c1220194544421500100d04690411000035071511a16080d200016850b00700818034071b06981990340380400e20b4854000c14030800f8000000140c0180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 435536654 1250 435535404 435535411
    0x40f0c0c02030d0e0310020a110a0311071703030622090615170d18080307110405060d0b0f0604020705010c0c0507090b010509040c09080304030c0f09092001031e05 72
    0x702558040c61000001391180954680f1103601600080000d41c046881c1d80c0c01000d5804403410803001c824503080400341342c42d000720f0048020807034250303040855807000c100840c010007000e8440c1c0000d81a45c4000354481c04040d010703a0190620743c03c07910f00360005c415880a9056600300070490107031241002c00280c02415150341c01c2800d0140302040e100c00d00ea8140800403008801807800070310034032084032500130020b050403581100210200f605841400100625405404c014140401c0d12040204564010704031a200f4454032000300c00140000034110350090b5a03180400143d910800814041d105242c03009000303510701280202711a80010303803400164040e8048585441c3c80b09040411070b054800840d022440602c004c000a00c1c050b0001c1400d65aa03140020f0050341d60030045185420a400848601c12420800e000e024000c0322042c00030f0407101c40a100940349916413800d4140c808003091040d900c0c64a15800d664045c2d0030140c003044c07031000d2403151800314a00c1507000345403d6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 435537904 1250 435536654 435536659
    0xc070f081207080606070308060111070f05040c0507021c1b17061005240708040803040321080f04051501060203070b06030105070207050d1109040f0506090109080414040f0c0c02 78
    0x107012803100da01c07031000e240c411300018003550320f800e072592800c0e2851342d802000c3c04c1c1088030443c403a10b0300113001e100e003400402d002501c0b40702e01800d140411040d00c102c00040c0041000a200660141e620350403100000684c10740804a1005603081c51031038205d004602a01001d800d9200082c980c507459129404081a041910550348500000e4000c4400314441d00c1d81c8808401c58040f503200d00207032000c0100040c962814507001903030f514100b4a0300640d101c520f441c0c0011404105010300e240e459400540740041034000d100d2555005001c4002c041d090408080c2c414000804100c4100b2141c000480c070f501140e4203541e5900c00080d580d5211000413500e10000c04042200c0c1d00303050140900608464001c1d00600741040e05002140980744420f850340c004040d11404141c42e06200f06005a01500d00f02da07110905003801d034600300010b014401303182e01d40810580420001c0d41a1403e6501e124241007591080030001405441c0394409003c0c03c902d455055400ca80d04061302d011114400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 435539154 1250 435537904 435537937
    0xf1309060f030615030b1915090603020a0614031308090a09060f090501030206030402010c020612090a03200c060d090b131b06080a0b0d050a0b0f16050d02030c070f08 73
    0x445440c44c0010055210003041c2c0c59801d0041040c400c05403405100315541c04100156880c1d01c000350002500c5594042e480303041d520b100600075030a1045050001d0a19420840501d0144030009407042c40020310600c0300760f00c0d503800da80401030120121050000002d1600000c1e40c0c03500640d600929082c0300350340e90380100c2c1000084a05050040c54100d0b9001000309045990b03c1c4c00650f001d00741034204980c011b03000c1091750442d01c9000c907660b004402001c0204810b0060f850003902803441042300c10303075102c090400e100369070354002540c80f07414909035445611a06005026405800b12020040c4030300b8008080142c008002200e120055010f81101c40240c4401980e40300b10040601401000425280c00500b4210003500100000c10000d01804403207030752a01c4803400e1101e00c420880701d0030b1980c420704c0004400c4103459030b041002c60030a940340e100c40030b5000c0d22500c5086103501c0030580210000b0140d6041200b0b40d26503d80040c400c04413020b0794074004595a22001c042000004c4c5c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 435540404 1250 435539154 435539171
    0xb060619030e0c010c051203060103090c03030903020112050609061011010f05090c040509100908040902120702100606091e080109031701080705010c0609060f11070507050909030f1309060f0306 85
    0x4a1005c0c0f200094008020744080c2d0040c1c101da074034551000382814141503c6401c9640003a0089020200441c065a6060703601825440014202c031107400d0034003d06401c003424000103540d12864160024070480741da11014040000943d102440050801100d500e400d81c0d8040888031608260720801640c0199100b401204040000304c80041c1d07182c0800d03070320400c0f401d60000c100390300614055010b1411141416a2906440c0c160b074848400040c250140d001030042d603540403c40005801d0201009000341c5052110041c42c5214a20506030180d014500100345c122100756000301400c0108000d00c00c10f8a50704014144070341c3c2c0d19026955100030400026100300c085000400c3e01c0c0141d5620403100406e480d00d401421401500356141d6668121618804543d4400c1c826540000000380f910307110307a8103015082c61040c0d80524003641010041000c0359001100710395100304030840b4641c03910000c42c1c51112010503030b00318418080c5801000b10b600d00d00e41d444042142d105440c10300c4100d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 435541654 1250 435540404 435540407
    0x15140609070e3c1e060309161512110f0702130c05030609010e090d0c050309130b12010203010b0f07050f03040905150303130924030b090d02060c070b060619030e0c01 73
    0xc40d011620035104c18100c250b805a142c120029a00003000c541140e40240e6580da0803180c3c1000c613400a511300b030010070f0168034540c000c01c031102402141842040750b903110314010301c940d100744030a41195040c005032040031556805203041d400300c5840010058070425080142c655801035031414400c5c1c3c1101c00000e8030a0150012a114241100140c550b100b80311200317403414001d114081b140c0e400140000c008948820740a103d9800808401041649902c000e10903610602c1c0a5981564010001800245020340482c1c42c00c0350080310107aa1140c00d800c02c03e080c03103a125000700341c0c1d00001400181550194124900411110710101c8131710104004259407403040031310703030405a109920200035100d136070b40c414803011507070322400c00b210010780004001540543d0000c551001401c1d0a00a0741074003000041652111030005081c1c500704460603c80c103018128009040c4280400000c02c00e40f254002d861010403207408103118040f042c00048d01428004111440601c60890b5807503466 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 435542904 1250 435541654 435541669
    0x6010510270918111005040801020c0604060c090302010c0b04020a1208180d030f0c140f01090605090d0903060b0301140f0f070504151101020408030715140609070e3c 73
    0x25604c040d4190034503c5020500841c0b207000c818440900a0034840081c81030403e00082c1452520031002e80a00d1409290207821185c0e001e100c20100001b1314800d00040c0d03000581c6510305904009180180d0750340e07100013158280e0a4214143d07136025202d0300000c2100340c00c007a00e00c400782c1c4000c8000c6c0d01d900f80240301420205010190001e40302d43c1c18000c00502600640404a0040414100580409210b02d182c5034805040303240c0f07a13640f000800103001c2c651142c45e0300f080340c03c2c0c0039100800052000501443d000d000c054401c9944a0744201d80c0c1d03601b5440ad20301d002c004282c1c045540741c19284900b0701d0a04541080e03500440c100001c68542c411001c0301e041d00d1008002d41155a807480085031120006c0e40407902940d820840803a010100f000500080c0d44103550416000c4800c3c4003070b0b81590b10748005031400c1c0031500c4c00e00299a4032843c1c8a40e02050700c0c40c00c84040203904000030005181c0390b03803520800383d90003c0148440c03004c01e0495915803182c07403011440c0c8125020300964 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 435544154 1250 435542904 435542951
    0x6060712051e03101715130201020111090a0b0a032903061602100e0c0a27050601020a021e090a151e0e04050708120d050a0b0102060105102709 63
    0x801c0240c000e1064140071200540ba041c84902220601500f146d000c4001003010749800c41c1c00c040c2640c410045683c24010740e03000b501500c4031241419141c5010440480090141c0c084002000ca10000c1e01da2282c3e0141201a00440d183d1800441c030064180301c0c6440180c0b200d000e030080300001000040c848942c80ea5040055005080c5a01d0800940b801841d40c0b401c2000f00d8041d40c00321032865030b9240c489002030f200584800c408207044a072039030044000c606030040313007a0070482000701d50307a00030440500c07041e016031b0f0003001d041c060702006d1300d04458020603990290000c0c2c02c0c4114012107a001c0d60a01d41e060503a0344105444242c051110420000c020148000d240c80612007048070000031500301d0b100b072044414140c0c81380c80240c10488907449110080c01c01180e10304245015000d05900200c201000300103000d100380c0000d4a480c4140500d85c0541c01c00c1c0c0390700207020701c44c1c2d900380d0750300c80014072007189491301003001c0c00380012600c540c4184a090461151443c040f40100012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 435545404 1250 435544154 435544171
    0x190c060b1903080d0b0604150305091209010c030e0405071836182901050123130e040506060a0b030103030309061b110d020304080304050906060712051e03 68
    0x790b45190b41d0076420f50b2080c2500064140c5400c012400c03502d5401c040d00142c64280c451000c507c0d80c0f01401422a41e00800360380856211049182141c490441200c01442082c40d00401d0400141004e58824074000e607126002494507003002500341c0e10100c490001000005030007010307070f615003100c88102000410411140c1e001e4034210014031140c11110000b00350b10001240541c1500d105000810a2010564405084400005603120700f40385c10114107440e040748000650521000800b016880300401000e0104a01140070911501064907900d4801d40518441b0740e4480d0400c01141d0025903040310648140c201140f1103280c092002010340c0e2400101c503013160320b103450440240c001c18406031416a80c456229080c1c01940a40800703950146c0c580d02c0c0e001160019072443d0048441e907000454100780000c1c04079030703c007008030f40407240304a424151740d1715008001802e0b0710690800909042c0300c661031914a50300301018200c18074011220203040c90300d0b541107440603c000c0b0751211 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 435546654 1250 435545404 435545449
    0xc0f08030433150902030c0714010204060e100e09010b0c0601050d030e2b0602030f0a09260d152405030703050403110d03020405040c02190314190c060b 67
    0x1c4400c46070b20183c58410303240034000000c1e0f9142228401c0ba401521003401158001030b13004240028808410018804e160003145414501103000302410075a08200740b0038244d004030306a41921501c2003145a5400404d40c0b401542d4841c58030005074001030710810180500c030000565842d010544001c000e80503103a64015449000c100071071040c03102070801002003142e0034a104180700303100e07401c440e0740b10f0080140e59050203403a1a2a018005004801c9581040070400010324098030081a143e410200c0c2c2801704001c0107030740050f0140469162034075142c4000c000003013038110b4240085814040300072165295246c002215002a450020701045040020440d400d00c2580000e601601a10b4890000c1d0103510f4414280302510000c0c50010390045424010740c41c041c440ca041c412002d0004046030460300e001d1180c1d40030f04000140900003c507100e0422001200200c032408100c60f0044000c0f42c12001c406801d102824005a0304189451110141c904180c940d51310031301c0c0c1019130300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 435547904 1250 435546654 435546743
    0x3240403031d010e0c01110d09030206090303040504020c03030609070f08040314040b07060603030f03060e01030609050c03030705010533040b010210090605010512120a050a0c0f080304 81
    0x9801421110b80360691526035001c502e5a480800c0c8146a5802c0000c030252040303400d82d10004240f0541c2d1000540d19070005098296803607084a010360442e0341c19118a03884207021000282180100d0b1300c01d030740141c00081c4007091500044000c5201c0c60b0101d8120045031143c100071181680002500c50100b1162030101e0701280c00342c1c41d00c6608501d076094151429403609820a8180c0002004980782500d866007402015044924088002468602007212a20341080c10340311481c18070003e1f00d0103076078916a42c00c3c0001030140041c4100c0180480784e6a08030303407418600034441160b400081e01c01a011024100781c580001d0f958044400501c0b8a95140c0c2c1010031000380003119425056100364400c844825403d80110f107600c6004003000240b5600d050305000444688441ea41210342080406d100c00703002241c20f41d0b10a480c685045601e507030340e004050342d603140558405001c00b01d681c031105040001410040d48038502c0b420300c3c00c0b01241c0b008284003255411008182012000d00c448 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 435549154 1250 435547904 435547907
    0x70501051e0a090606031e0b01050102010c140d02040b03040b0907090912030513020301330f060f09330207030203060106050d0207061406150f030402130f0c020c03240403 75
    0x200f050113005036000103165a403130765054170141160407010036000c01ca00e0407005120054240c0d500401d020300081c426040940b030002c0000e10f115060240390b00c00454190303450503240c0d042d50090321210a1003aa41d0400303040002401c4002c0b40c0407405032050103c0800c0e003800394014200304907170106401d1600b004180f400c2d4003070300c1c0080c940449000c881c0c03598000750b5401d0041d04c52107845429845504a00c06074001e116503030089140d41031160300e40c1e040129841e10403d1104485803440d011011419600d022030b48481d10b0741c4014100ca0400711402440180d8224000b6005618107085901c01865101644c03994800d10010394150407460040180c076011b100100307800d130b004660043c0303000000d6413400116a0781c550844440141d040410200d410701c2ca1122004808520b17a050a080c50801400e403241300081c4005d000301e1406203041140303030700c2c0d800009003e4040e850500054002c860020740d540c0711a1541d9110f84640d2020152a09821042110580007981e50714402c0d0343d01e0701c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 435550404 1250 435549154 435549161
    0x6070905060301270516020d05210606041a09130b0a090f09020d050f0d0804051c0507020301020c010b01030b040e0a061104080609070f0b0f03190b031002070501051e0a 74
    0xf4241c41019404013054052250344621481082c40c401c0100342041c00b000001d280503012a000d00602208011100448159180d0080c1c80340c5c42e40030b01800ba48e04da00200d40035020750f078060003a10300c880607a105a45c0c03201000e0400d5010585581d9018042045034600362100181c4142d08a0070144007480655001e4210094450744144081205032060303001c9840c52541013826143ca0304a00f5140c12444818014014240700714036041030355041544410385c4034401403000d0039240c0f581c4060060300c01d01030340a070350009030010021502c3d0328a42c1c0c00030740a041d0b00314280340080d141c006a20841c1c940741c41240440c407080b01c01843d00c01c02030350311500141420001407015550a000c005100b0100704540c03803041c10802c02400e182882c008584458058035003080007425814851070b0b900841c0341017500e138090303003120050300302c1d00b80300c41038a008204800d0b000790940940000e001c40c0448680060614a215034001c2040381d80312002480321801a050038038018201c0404103103c11320350341 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 435551654 1250 435550404 435550439
    0x4020f0d0206040b0d0213050303070515070e0907080a0b0415030b360105090106050d02191502030403211b080c062e0b0a0f030e07090b0306070905060301 68
    0x9060a10f099255000e0043c140c000740c000300821900041e03100c166090644907600202403e9008605007000c554810b07445000751850b0044080318000001e03407081c42110a0103180102034006c603030380d08124000600c40b003421604441c513617042c0501c3d40c80304c1c00c0074401e10000800c6400160100341c00d55448507080706c800b030401d4042e0201d141d1181820580700000301914110300d009a1004000d81d04420b0965034014416013031070f450030f2340401094030741b81c80f9008903d904650300305841c0315603128260f9000c582c1d0803038602c13101241c0f07100310881e800000910960b8050804240912078030800c02803c1081c02c00d42c03100048202c2a1440e2a12003445007022403803240c03031440c0c240740c03980660918101c02142c4108040c1d4804052134051106100d026a40c1481c0000012a540c1440d4008840c0e01c42d082450b030820134620284a42ca6100b42d00082c10103180b541a54481c1d41c1e2580c0c0c4101521a8458441c0300b0b001c0e580c0031071303c6036000b00c130711500b107800203000c0506603072030325980038070320749058 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 435552904 1250 435551654 435551659
    0xc1807110109080a0201050108060a061d250207081002032203140304030c11060307020601060809011404081b061303210216061d060408090315010602030a0806060304020f0d02 77
    0x1800503000007021500504001c03407651740005020740c5841d40e6075141010103026002c141e450a441400090003401d4420a00410110b50207095140c1620300c1c1700d00c07051549002e4202110651840b4200c2c0d011500c4805c031080001142c0c0500e15280544049101c29502101c02040c000da000d0300002c00d000100c50450300906000b41400352041d40c5155a0740202c60407000550030300b43c50f501304200c2480f01d100d15001990460b0442c50240e4002c3e50707803039040c007900f4244140900000d00c07401c425045880d001300090744890352810b20385042c81e50751304190007500100500301c3d0a1303100180c0000b04036202c2c10042d41d03c2001207280740c5041d2154071035220303020011181c0d034940d0441c03d03400d4001080d554034820320b403041c400b0b000d0604104881c0c4c6080e0034a0f150144d40384040c3c0c502c5000900715009500300d0141543c0302c4c20100064034000840c50703146881c50707481c4000641d142c1c0100142c034051003191500c00d081d41d00c4030104851484103c030020351003621454080755600740080a8070289101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 435554154 1250 435552904 435552911
    0x15091a040506031501140907030908070320010c020109050c100c1e06050c03061002010c140c0115080303040510061d040303110d020702010306090c05030c130e1003050c18071101 78
    0x64180c840038907042600010540d843c440c0203000241002e90311f266101d00070f4942003045040c42d0303840080c60308c110f20001e001c001d14050a024051441410300d40d81104010003041540300d09040a030207000380c80c000352032600544a501b0b08a050880c10429020455580c0e2031185443e562a5120101c480310840d1030850361450000009040d48540f50080500c1c00300c41d62a031a01c0c00803c500b0520b648529411a4140851009040d0300001c80008804810f04c3c07264450210f0008180102482c0e41e070703000340840e60100004c2c5050080002d5014134010000d5880e01d41c040c80004094414501c9003000040c0d84c114051003e0f40003400c8d15401c60710074503021039075010000008100707401c00030130b2000c040c3c0d00140300001c5603010b1040700700070088001e051005022181003d03100e0f01004000c031112200c000390040c9801300210a0001420b0402082e80c800d050482e0306446410042c04100c030310784681a0081d409141c04503040320525155060700807170740d841702000c1358401c00102c0c0a1155648 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 435555404 1250 435554154 435554173
    0x8010b09150328050604060e06061f0f11011517031201060e130929150f0a1a03100b070b040201050a03140103060c021c140a0e1315091a04050603 64
    0x5101880c000c038020907020800300c08c0c4c0c0c4a254103107031019001c1427259500000d150030023004030254458034902820240404c01003150b05580c014400b07100c481070b81d403170035114040341b03911750f0708030000d558540f0758038840041450352090381c2c1c0c46222210020f030300801d40104000c52041140c0060800045c200301d422000781d40c0c00e01c2c26140360510482e00d080d5000c0c510303107010140115100001c540329150240302d0500030790307820000082460142c000d500c05010302d03019031a031005060040000100d01d000c3d051480005030b07180c3e041a50f954440c401d4500000603800141400e0301c1c0d000348c2181d4460320070749455005548035845124080140b54031580846c90b4480030100150096008210206103c54540c0d402801c0c002d00ba0640035020100202120f0b2440c0c0c07001c0217542805809003103075640e5180e110180e400286840307070540c0c01100c4a40c2c2c2840d445003034011424250b02400d4902c00c00da01e07502c2071010380390590603c4108213001c0020b8070036854103800035500300e02c001d425900f4191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 435556654 1250 435555404 435555413
    0x10e03221a0d0b120601060f0c020f09100e070804050c0105030f13051f0e1608060a020309011803030b01140a0c0213110712020c01090302011403060109080708010b09150328 76
    0x440c1340c5030001c0e0f0420001000425006455042c403010140b0740307141454425400030f99000100024180600030020002d20868202d900b144060024143c4030f501524012000400b80d038002c59086402e40143c400071822940500c003075a000b02c88052200d40641d58011100035502d000f03c100b07413658814225a038024825040501020003880380010400040f484000382ca851160344000780c00c83c150380c804200740d0102040310364102c64134900141e41c0392540840a809850300d601c2424a060f00303880e9800030550564402004901c013070301e40c007000540884102c070150044022410110396801e58803801850407094054400b50050400100164051a4a0b905804c0100200c0e0240360704290081c1180c0c0411810b00f00b44001d02c0c0c807855032421640020951109581c81141952022000c654168050004038000c3c012420485001f603a44a03485400381c41d142e002c190144220002081e1030035500107401e5021880907004110a000c60912035410030031510f4a2540e0b200103040000008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 435557904 1250 435556654 435556669
    0xc0405071206140607030818151e0108060705130803120405060f150f01170f180c030c060a14040f050a06051908100503010e03221a0d0b 60
    0x9010950394003054007090001d1004440d031a8000355882c00918540d006169108000c41c1e030301c07541c5842e2420b0a40c0700c000e1082000354401025007114020120f03a2401504c60003032191082e011001c117040141030780c1c140c4407800c910130f01070f031030303140e0130400c00540554050303c004e04031801c12641c0070208070b40d1000d0743c0307040d9044104000484401d031000d102c00e001e002c101686c0c21070400c881480705400c15603590801801062285400b580783c0550300e03a1141e0040b600254000741c5030f20041030341d03d0403003100d0b5502c010407a07805403d0042c0140e80c59010384006110380d0b640170060010900141d03071100f040300d030340c1016000d4030030008000154680c08031204041e0004040503a0b004030141d08040030403243c0301d1a50040800c01c1410b204012820035a00300c2c1c20100012414500110340340e4094400388800d550300700641560804200414045e000002085010001c00c003c043d12842c00c12090b078183d40506c1003402000c0c0407400795603110030050062800d04412000040d4565001c804624003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 435559154 1250 435557904 435557911
    0x150d080a140310030203150f0103030e0f030d030e071a0d02030c0405190306050a020a0c23011503051615050306040f06031401060b21180307050a1e0c06030504050c0405 74
    0x40c0c50f010400c0045042c00c10000c0604440420702c030300d01c0d1170018090301d548101407001800b0421281c82424444d12007900c00c4c3c40700c0300042c040e220006105030020b000380c4070b0509403901d81e10a400c1c000450184000711805075007840b150540c907210b441440c040c080c0d0000350a50724058010400000c081ea24407c045041500810b8910361041c6135060903001c68074000e10400f0360340d0040041c410080c0d4000c00641d1a2980f000c400c5040b800c10103801d10280100b41d030507108a610341800b12580702008540b40003201c0c403a80071a60815145820100d0307021483c403440c4000d103502c04020311514001c03070145030b00c0007020b4000503070714881002c0d840581e80c1560080d28075041203241940c607500c00380148406050b0601c1c0140c981003407103c8100f000c044201d240c2d410100c0020104200468001000c0c000490240840781c0380c100b2400d2440d19101404012291141c5610715030703140f8686c02d400d680c0b80b65008003c0802d101d20303081041d4081d000041c01120300c1e000d1a4507601c915038170b603c2011300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 435560404 1250 435559154 435559171
    0x30d0501030c090c14033411011508030a0807230414040902060901050c191a1819020316061805061903090c1203080609150d080a1403 59
    0x1240c0303160440c1c501c01c07240002112803c101310804c441500d5074045c0112030f00042118192414685d034601110207803001d06112004001e141c105086140c1d42c0904041c600424070402005107610840b00f082c2d658081d40708000280e081030188080c0742e805078550943c403002d9400c003000c4060307140b0302c503c0c480000301510b1040f040010034103200d404014009881c1c2250103646c00c100302c0c0580c0d00002c500c0d00403240c5a81c108000007a10701040c0000380700342030084144a005441809451802d42c08401c015240200c5109040c400610204002c00b07001142c0d46900015040617608030880c03040c071003809802a42c040c89860080c40301c072003c11041d04010310141d5120002000c5145040300640c2090740440d1040704180044200d51a0302c0703100500700307031a50400007140c24140c90903103c9180c00380e002d9480500c100304850140364000301442e02c511821100741800369955040d1340150f4204494064000c50303c1c0d50f28100240c2010020000d000180c1010500700d46120400411640110b4104a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 435561654 1250 435560404 435560423
    0x91501030818010806091b040e010b0c010c05071124030703050105040501081218010903140109020418260f0424050a021c030f0501061d0f01050f0309030d050103 71
    0x10219062102c2042e600c00c02d20308032025003810f00000b40504406400c036111000c01000f000e002075020021107000f0551000c552100e503175501000b03000d40e000f0010b13020541d400c055000101314441c00840c3c803015801001c455205841d64140b0058440c440011481c0614141c03098658040d00405984105044d550228056041c20103000c02e442040e80200b01591098201c0d02c64190204280d1b40e04000305002c100300c041d40000100c8010502c0d51001e00040741c40c520170b03040040190003041c1564003c2d00c00f4071110001851010582402d40000740218103170b520107094003050700c0207850600a181c98418102000400300d83e0203640181d0105011410307490020700360070b101000080342d20f11141011401d20b41e03017080c040e4542d50324000750440a004005081c0c0d0960095120301c40041103604200103661315244081c140e0988208841c2a0b20201038801c0346e0707441d10180781c401819040e51018208009180726482c690009420803c1c0c0e030001307111001d104101072042301e009501401021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 435562904 1250 435561654 435561667
    0x901170c0102010b06161106070b011a0a0c12230414041103180a051f0f1a040b270115020c100503060409060c02010204050102010b0102070e0106080915010308 70
    0x9440c0821860306030341564101800c0b00110780da0300064400c000c000c0007034400b883c41c03c0c2c03a100014003041c103e0706034090030104143c0c0c01e02c81038008007416174403466500d444514106028800500804075090005081c0c1254030001030354207074107102c1c681b03401c0c18a40a1540c8507940c03016103002044114131014000b1804000d41294410714400181043d1000c000c1d0752006a00c403481880010075010000c2a942d44051054000b0421120002d8100301600d144207040f403480c1c00800c0403504000c0c071540c2801045080d20740b052050740c4400c00410280800300b0094030511019015100b006540460503107268810b020b074803560340140524a0380000c0c200c0d8100120900b0030f80c041035209045600264081100f52a1440340301440d02a9003003640d1203569200010340034010403030b0000d10090800d0300c581c0070320b60150050400e0705d6098000f40000140000126500d01d0f29100f4440c41042e0103004100e00c074040e000e03980d007042161080c0d64030344080416410994030700783c0c82180c6414000905 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 435564154 1250 435562904 435562949
    0x12050405031305090f0c070212030c030a0f210e031e04030314070c12060b06070303050106322206050406031406090417092815120207020303090901 65
    0x1180042d043c22a0555110b05040140d140c0040008100c040524000038840c415569150100401c83c011a8200c0e0394a0f178400703a109889400180800000c9090000c0d1110002c0c001c010080c0b02c034801022600b0541c80d030398031031800b406024861018a0008200303039166990106485200c054000300d00341d545a10314034009103001c07802a9101170800c8148488000501d8050f004011120001504490008141400b034002c0565030b1036035520190002d01c003810560140c000c17a04031001c83c0c40d616074200159a41d0042448a00505006c40015090800c00000071a0142201046072044944640215a40c0103400b03a15a0021400b268001c10108200c0b9032501a0350070000480c01d105440d8100324011500d162000382004003689840c178450014401c4840a49188280040880b00b4040c03100fa98580803080c4903403d1507c4a0000c10080b0b103804002400130075002e21507075400c8151072204080c4000750007194040f41d040c0010865031900d0741d54500180d002e040e041c1d566a00b607010001c2c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 435565404 1250 435564154 435564187
    0x501030b1003150f0f060801090209220b090715020f01060b0f0901080a09150b1302030402010e090a0e06071d0907091a04080a06020a0917030307030c1205040503 71
    0x2000c6072001c16030342440002e03810744220902c1a80c0c0840031551201e582402c2001d060141e0407001c43c0c5140880005c1d4200b01508400c0f40c040c0251164030799078441240c071070690b69203000c0b0340f05060300c8400c1640c0014002c08640c2d5209400d04140c0c0c0700d00c0c1d110160003030507881c1d0440000c01a800b000c042e00c24030600381308180050415120030780c80c1004040d0f44100d00e0061040b85030603c558500081d0841e5a141c01c119602648242c00e0000c05020790101002488000382042c0141c01e0300b040585c500794a442121f02807034050f11001d0344506100104000400700402c400c10b150b1f1a4000211205010800640104c5840d114224500c152810b400048000d0132032031841241740e0b500303204090360040702030702c20f907019100c250ba40c07200c43c00e04001003481568410029849508000c405111041c0d028150651240d40c480c8040c03541c03000700d19010103403496044005e4100308007084c00f01d400b030f42c08415000301c58140102d100c100c140c05101100c0d01118192082d0300001070842411507481c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 435566654 1250 435565404 435565411
    0x1032025030207060801140a0b0a0203090a090501090b0d02060f0901110f1e0d08010608070c0507030c0f050a060801050607020f0d120f0f09411f050a031a0d0302010501030b 76
    0x186030100621f10800096025201446030b40141c120000703800240a20174002c94010380c1c80506142c981c6546c4180c484000c1200344209540e551414450119600d01070440798140c41e0014802e9051241c00c1210510365400707540e0070713030503c03040c0c0780707900407694040c40360b141c0803203012000d402071113070384503980c03000143c08070319032125400c9408050342c0d582e040351200307054030000d241c140140c0c3d407910815a004948020301400354070580c1d80c008208200803400030165203011030280c40c0b40f655141400540ba0360b80c000c01c0d0100ba1f09034014007190034403101502a090006041d10403501f00c01c00800c250104200064a51403481c2010004c1c0e20780200d400f40c4031017003510f0009010300380c81400a10b401e0507401111407008500e004429a20004a9405d0340c2400824940c00c014001850100d04102d12400c4107005948000c2a03232401e00f600b00c03e0502c1c610940d03c1d09440e10380610400c8000340b074101714032080190b0000a00c29961140c10044c005c05210350000036480d419824603604806004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 435567904 1250 435566654 435566669
    0x6090c010804051e160b03101d130c090608010209040b0619121b0503100506092b120302070201020f07050a1211041b03050601032025030207060801 65
    0x103003440000390000a90326818481042d0131860a08040541c5090040308000c0704200032220502048501c1020004c40c0107118090b1780507150740e6523652440c0d24210f140d400c2e500c01e81d801d04c00220003c3d80e0503074400c0c8541c810840c01800c26107540e100400c540705a0880d9a542e9808100b13800b41741000c2c801d1900c4e190088515a0034240703c40341580c0c8199a0030501010049016004400c0e240d1640200b041d030000821024108010308000810680040700d44034001c401c043c4c000680e0b030400740200c86450001038540b400301c010480b031007420204098103a802280810314500c0100e444080d034101c1006a40c0d5025039500c400e0300009290452249441c0503980081c0d0303040203560758007070700318040300d04140c5404c031100018180804000c0303081408580040c10f055800c01c42c1c42055070803180445260304c0c1080541c456000440495005c0c80038042c484420f091610550203088000c9c281c00700400e201c1c2c048203000340503031001c0d181d14101708901590151000f80310b0325400010441c09032042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 435569154 1250 435567904 435567917
    0x614010305100b030613110403061b050c070515120405030417011506030c0c0c0617070503060a180f1e050108030a0206060915030303040f121103040504150e0906090c01 74
    0x20203411201900c00503000300d2145900c821290001180f64020b451007c0e6071600085c3c032203a4074140880603107600f142c41c1200e10012400010101c0c0105c0544200011050003030486a06050922192030081444515059001e01c07904243c1a02140300a00c07691198015540b50303403030129409592080c1b0310910010341d041400003588200308500364022541e861031301050000b000f610956814520500140c07054280f200c3c0400d5040e000390740401400601e0384205c20940d03076040200d50b03d003c1038601075032090b07071220304201002c20b48602900840b25000c0002d00c000448c0440401c9486032160450515080320041c0800340e000d104050040800d0780c0070f1440c080503a1030003515142c0c000c1015204818950108070305101034944a4041d0802908990b524101030411000740c1c0345030402180c0d013204262240c290b02d40300d07441d2103585840f6000110708281c01c1030108800f0307048020581820382442d0400285820140746028050b42c03462025180f2801c1c600b0440f4201001392000d1810300c00d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 435570404 1250 435569154 435569159
    0x1203051b0c0108072a0c030209010311010806060702101419180807030206040b0c03040b0c0a020a0f050a030f0615060918091a070c24050108060108030a081003020301061401030510 79
    0x600c050320001d4410301c0c046000d0320816241c5007011b03024580001e504059180004030800520300101d0310442c00903203510b98140d451408201481c841c0c07010084d0495205d4010b40541d40c040d085034111078070002d10180c00c0c01c0b4070b810b000c082401d5506860000420070030901103040781c40b02c0710380090703d401005031040d2400c58010452601c114480c00c0000c2100046c0c4036030314081801640c000d446003910442d55500301d00a40e6650b1680a5400c1e03110700c06620000075491107450300902120000b07050f0081c03a44c0f0b03503203400303440588609055440c80d0700c2d010300c0304046080700c03d00c0020b00713003945907000220b00b031008040300f94825403004035a240c030303003000c40000c540030219608002000b030000703903c9590f40d4032081b5407080e80303840c000741800d4028a5403210007804801c4604185c0c5041e03c1040207a9891007125a10032080c4205140390b04100b10041010340700d240010b030301003401c4a807451020382d00c0e40444d00310384083d400060041c0c03140260701c1441d80c0c14001c403504420000308803600c050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 435571654 1250 435570404 435570437
    0xc1501080a05150a0605030706212a0e0901030b070809030406120902031603150e06160f11070801050412030203040507062102070501060824011203051b0c010807 71
    0x3c002d250440c0c142d182c41c4005900702d401c0b40c0010014207806801d90300d049503100c50242140f800f8000c919442464a00c0d0404007500c10b01c51402c2d0b10207004040e42c0e4112041101150301188401c0300010406045200c42041d190501142e008620035002e40901d0310700b0880c020809100500180c4403900108010800f107a4010380c0c099002c0d074070701000664220320f8400a0b00c1c010032110f8103000c003801040b001040c0048581c03440c41d4001000014803403400c1e001c0c0300c1a19140109e40b04003840700c003240a04c15092081841e80c2150f552803c000c07401104504d13080707281c040f40b58407400c0d0682d15541000108074080d0541d0202c4901d0f0700341942181001e030340300c07921101359029480412070507007141880c000101c0414031264542483c115600d0f503290510354040c1c07a05000e0312401e8404c0b800c00f400070b50349106407500100168044604680d007400f4100007660302202c030175810802706001041d0300c0c2145003910f070850300744080200410300d1036a00141003400028429000c0c0700341c2d02212707034030314 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 435572904 1250 435571654 435571663
    0x50a03050a02100f080720010f1a0109051311041d091b0112050903040b0a020106030b090601180c0c0204050c13050108010510050d0f091b090b0d030e01020f030c1501080a05 76
    0x344050800b0031f510f50f01c80740244032025000c1309241480d030910308140303002c44179984040c42d00010400c400c03128444010041d54413580511a01e85c004911010100401043d03502c0b00300b80310030020106280c5907a03000c1240900082d0944040301d1240c900510200400070411910b044821805005030324048100103882e058415075094601c603207030300005e42007e4042c000c44020b03207200d07103100343ca482c03900701c002307000b803105000c2191420011004108943c0c80081c0c0c05040724000318024200014130342c0820040c00703e03040c0c0002841001c08030007006079128000d07907115000056400b51074002200000c01041c00c241d210f6814404124014080b54941c96105426000c007800d2440d84c861049500c00000c144241c503071880c2910745050300081080341080c1034050301220f952041ea4548403641203045503510b0b01c4e85580070380c25008940000e400340028030745190b0140140c48003584d0710b4074003d056a1061401c08040d41003140428540744003c101503024003040e0300184807001e020f6440680c0c0c3d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 435574154 1250 435572904 435572911
    0xa030e07050f040b0a030c060203070c1a0406050d11030106030b0906010c050d1d030312010e0f0c0d0e010b2e0e0901170a052401080d0c0b0a06050a03050a02100f08 72
    0x201d840e0130704d09419071076014054004680c00404030071415a40c440007500c81c5c00c0080220b50742c003c000b000040551065008000b010030014480d0702d0207242c148291200d9105042480b810f0b62103407082c03501005904069030080c4520344010446154450400004007002010141400010600d00c0c02060000900c0010b12885050410040311109410b800d0f0a1111040561503c4002942c4e0b24991220300f1090485449002e45170b125143c1194aa084040c22134080e0f0611380e007402555400e11050300102c3d200d010000000803403900c0d041c0402d0841c500b00003203e00e0580448a00000049101903444244c8980d250010104002e00000f80c072400c010700c9403c0072011200e035021030402c1c1c1405607208580d882000c461200140100c181c00382410501d10303207060314602c400001d10303250100e08105558980e640700009003500e03a40380382c4406405005c51202569a03000410030b0b8442c081d00700003a60203080240141660703481002004002d8458800800031103907130080049070091100c580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 435575404 1250 435574154 435574159
    0x2030a0c020a050d0513081e0f0a0f0f11030d020c01090f05010e10021504050705090606070302030d1104120809041a03060114010311160308010b040b04060305100504110a030e07050f 80
    0x80da01010a81404420701c6c64000341c10751300842d0026500c9020b1201212003440c03040c1c003900c00c180300301c28519490300d0301c03900041d001048803421040003894a42808042501c2800e80c0c5000c0346c1c080000c246000c01403400b900c0907920130070081c0c100f9078201240384020300030507025811103410200001c2000301540c0d0307054040c049440f0210261070003804502c0e4004202c2007110160300c0c0a05089541d0a400d00c03440f4040c112940c08203400e41040303001c441c082070705900151b00c2d144002d00c40c203000700801c440ba503031051800d00010594010211006e541d16000d02c0b000c80d100c45030078003040110f5030f00861149a40030b0907c14000760341c07008110709045461001c0c034058811410030068002e4211a2401e11141c0300004040624203034008008007e94080d0b51251351984e284c0324429598800c41c010703040700b0318040c80208192442038201a600c0001556252107243d541c078046001d0740d040b11015000070b90045000e0b180a94075105900234502c00800404c1001d25190100308216048200e550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 435576654 1250 435575404 435575407
    0x203010f0611030706090b011404050103080f03062b050105220f050109080f04090b010f0806040e0a08030f160309030e04270311011d0c1c0c0902030a0c020a050d05 72
    0x4910b5018002e440d072045c0c0007401032000904610740741443e131030240687c034103080c0c034200a450681031030702c24641030f00d0b80402920700c4e240e181d1204018030741000f088a6440982504013000030403e04060040750000e070458268012498900305081d41c2d801080c1c000381001e00c10307142c01200c1e520940e0301411500721103040010000750420320701401074000040c200304000140c500e00072640c58010b100300c800d0712808110f44140da4004540f02c91104020300c00060204c00030461a241a501490060092104882e40300600d6956038000d03400442d400c1c1650401241003094202d0001c103a60100507880c50104600c222a9401600b511030070070025025666500c20722021034040298200c4040821501070340c40c0d07816180041c0710080241405e0700ca03500741122484075161140745244003070113a101800d8041201800d01841021180442c440003440d0421070000ca103458560300040c10039250056507a280c1000c008054480001191b0215400135100e903000c0f035000316900010084a16049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 435577904 1250 435576654 435576677
    0xf031413080c061f05030118020906010c021c170307020604031b02180a0c11060402092e030b060109060e010e0a050a080c1801030308011203050d05010602030d06090203010f06 77
    0x401c9005103040c0031043c3c0303d07074400e0203200300c205181040420684400300c209941c07540107050907034000c00c10114008103c07012000052074034101c051ba018a06160000c041411500090341b07805261440e40b841240d44074030b180511901144c14510352601052480c2b0303508149200964070107000340090104801070f01e02c05c40010807065003181c0c0c1c9400a0914130b4002040314600150300003500d403c1c10360307880c080620071001d01841c07090148070300b010041c150030b9940e40c080c0160710200410b802d221660503207500b92030b00f0000305201c0410200408001110707055241102c607414020701480e050040507102000b041b6070250305050303144020319265011a0001010071034406440d0070080d0301c80100c0c2008100400d0001d901031400034200c1e4820201030240300010805c56081c0005070016280c0e400500c40140c101d285151040e2207890911320b000399848291040b544280c021400580001440300c01c0410319018440150401617011440c0d5490002c000c143da9501d4480c0c04240414003014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 435579154 1250 435577904 435577913
    0x20a110d2c0a1a030a1505060f18121e1603110f0603010618090204080c150c160303020105070201061413020c0f0a1203020307050306220f0c0f031413 66
    0x209001440440f06007407000c8150703000d00459030400c0303c030101880d28045070062507506c01070401c411140e0140019241101c40d5425220940c0003005440740ca142203d0541107984602c0c1750140300d80081c3c4c01030000d4803c03040300040461040c100040c1c0c0c80e400344e580c0e82c8494046110b050b0840303901001c240500003518011601c40b54076101d100d82c2c0001d010000042d0280c11844c80c07130440c182e208000103201d80750102c40d03040b0301981c00b80400750703400304400c801705041800b104002942c03040801824100038800341032400c1c5000c0f0450300c10f001500c800300205602400781302d820101c0d42c0001c2c00010304110211000c00714a800c554030518400d4035180329600c0c258100ca0390403261713804ada00b0380300c2c0d4003070700c156282a201d10440320741d41e0108506501d28032074070a6902400766590b030b56103591652403c10820070211140380c0340c0d00121040364110405244140c40c0a11030380100407810504800011342070b00511041c0794107260074020004040a0405c5060ba406161141034000c80161800d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 435580404 1250 435579154 435579169
    0x1090b010e03060703020d11070c030b0c0c121c140a1a09091c080f0714041203080106120603050c0418170405131404030c1401020a110d2c 61
    0xd107241c150145100f0300041c0c039419001080070320000c02042c01410b044401e860202d06c00d0080140600500c80c00910015091240b016080148201c846041003000c0a8090800342c070150301c00c500100025a807140440c0d60306032007084102c81c43c0c0420288550b2541c8021601d001000d03034024503038a03042c01301a840b01604c0711844107005041c101c500d1030605c11240da140c07500070300c00c0f540700580d0301c44100d1075100340b1a4030f100b042c001980d030703580f80c41e131100658108078005201091028184000704403900402c011600a5010769503001440d49072007005881e1081410001001c5410041c083c00031400014086c90410403c0c1c600041c03498810b0880e001034040281c1c0107182c501c0c2031111201c0c1200d801e002e402a0b9104544180f01d04a00302c0103041140c07080d0028070350403441200000d001c01d0046ca00c008009000e5030041034540d4100c0e40391822680304036400740100700c42c52550b8020980070443e040c01c50401e814034040e079041c5041c9501100c20704000d009035959003045404250340b181107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 435581654 1250 435580404 435580427
    0x41b0c02210105011a13030b090a0f0503120604020f040506090f060c030a08060328020d080a0908011d03041a0c030703050903150403120c11060a0605030d1701090b01 73
    0x120758150300e04030700301080e010b000c080c86401c07030507240a10400c120000e144c00b1541c0c50311010b00300307600e440e20b5981d511004003401010800795000310010000421043c0c54450422171003000a1039640d11119254804d0070760140c41c0d940102e10500c498400b01180d0700c200c0b0145e8000320f03649a00d617070032180000c000b00c8040380420303040100071a50a4175100c0000291000e90010f032203003541d42c1d840b90141683c450300d901040c4400d03c2404005c03048039203400b843c802d049001401c8402ea00c0020307120300180d940000e26180000b4030707102c1c042001e03040c02c0c07003044030a4031a50f041e440c03028030404071a660f9000320b004441f840000d4012401c40e0380e08800860f10384407104800e8985031105801d0150480c1c01c80c1207424040e020f4040c42c00c1008007440d65907840390703515841d02e804070140b90340034000800c0244034042c03e114580d41801002c130030400041c5e100754000744001c20f485080400b40340c10700c811010902d00303101424440c820204090321580f419510501c0d800182d41103031600488000c3c0491 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 435582904 1250 435581654 435581689
    0x10030e030d18120507080f0703030207020901030c0f08030315062101120201030615140313020a031211070b16030e04050f1501020a15020304110303030a06090b041b0c02 74
    0x124503014052801000d816089004205065494460b203000380c03440d111704440200825000c10002d01702600c14406014030502a1500604105a56010840300142a001960000c65a66007004804980c0d0394850140c42c021340654210b04010140303a250b281e034505402c1c881c260110b03030f40440a0090240c00c00010090060590360b503901c03c1c50300544001908241c0c0001c0c03c00401143c08070507180d90085403210750b621400c40b003040c0111600581c0014000801c901c04100710440583d64026401002d0760080c00d034010002020724014110402030741000c07949401494003007010104240c00d8403000341d80c44020200704211480d049442c080101c000e168011318001c02c0c00f00e0051120b080b144a9140040c0d40750030114802c005a030750300e815280003840ca040c5403071581004c904d04e4029542151041481002c860070420000b42160811203004075041d90750303182085050903600841d424094152020030850040506008150b150f0486080c203001c2a0a960421500c03405000403112161 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 435584154 1250 435582904 435582911
    0x90c0d390b0405040c1e0c26090f0d020a150c0804080a050c010201060f12020d05010c0807020c0f010c0f051501060507050f01060f030b07020a050105100302031b10030e030d 76
    0x1240291040c41e00302e8022030703002d60f18020b5104c640c1406100d0340f10540112042000741e0140000c01180d58994000341224100032070b10401d640300740d0940c1310204002c0c0741d004c03ca4880700e042c0f0500c8880300d94261224030071140803907003e0140e11040b10600944506481801e03413201c0c4050107440c40150028004c100e41c4001400140e0100c021403940506440360081ea03030602c8102c401207007a25898040d5588112240100304135042d10342c2d0040c7e081e00d20141070f51302405001d8480608441d54800e07010041030f000020005580ea05002c0760380700c0e2004450811041c009000000c110f014a698010311841d2001025000d00c00c0400180e4080070f01c8100c4003642d0368465070000c0158004c3d4130121254031452402620060b81801040c09540c00144003035440c40c9551501c440084001e00600d0030b50180d85039503c0480c1082c0203d9120b2084e8402410700c2c0d503c2e51051519002d40222080026004071a0741c24030350341d030034400d020707101c8a62801003581c04c003226101d419841069005803900e0318 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 435585404 1250 435584154 435584159
    0x702011715060a170109050f091506010c0507050405010e010e0f04080304150f0c02030d06090203090303040305091207091a060316031a06070f03030506090c1e040e0f090c0d39 77
    0x30342e070040c0381318000000c8c0c2058103490340c1d40c4955490000302003070141940c4410000d0301651003800d01d030114a0040d011100d40503a81c001023400c40b6001c1c0c0118905003400c0f4014801844000f82d070b5600300980440c082d0051034103483e400ca0a00002d8001000c8041c4011194403403600c54214455290010030208001248078001961b642d00001c1c4107070f4814180040040e80442c0380c070983c2d204a1030400139610710f90300d83e17800700c03100e50001c130840f54042c000b04104444e1800401000d8098420300400058814407820002240b034030400b1818482c6c0b0f01001044054120b060346c014a408aa007030114582641c7c0c1000d2003600049010150405c902140f84014845404000044c086c0252020845034441c4014401109e00c1120040c1004100700020000e00d80c47d98580300004008100d110300f490349034084141c40d4034040d50980b12010000091061003241030210f4420b10700c080350303100744e0201142e171a03103c40204001e21025480d8880810700502407221b50342030303045900916071007140d41c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 435586654 1250 435585404 435585419
    0x302040312032a0818150112021306211e03021501080114040b04170406030c120c0e040207020402070212070306060605030106080a0e0c150702011715060a1701 70
    0x100012020102a41d292100c1416003945480000c2c4040c103580e504d240c2c1c0c0d80d00d469880c860a00340c601030240b40b20b0450b8206e0a0181122028060b0000780c6258039480414010860190340b00c51511a40390301e0240c04000492803006500ea00e4490418505003410950820785101580501c48002090150000404242d8085054a10782010119840040e605c85c0d198500f2a02e030350310800d403500000b802080210382c3c80f2540d540d01034030844a60407408200403440c89541c0140d442107000c0394440d0032400429070411103002e100e28268000b000599180d000061440c149080000d00031540001d5140640d25660101c90b200ba80240200038100210311100d640c07594140b009030b070b945142c50000304000340325078100e034101d03910303655080003d8541c4042ca1004000583c4458013600c100041c02c042c0740c0b03495006940c1c0201406015440b1803903400094042c081c0403891012029025081200341e1004905648818001780c500701c0d1144510081603500710301ca040c10036200da403490700005810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 435587904 1250 435586654 435586661
    0xb01030e013303050316060612111e03070909050a0f0c081006050907030f090203120d0e030c030a080606040306050a02040612020a0806120709060b09030c12100b01030204031203 78
    0x80d2210007103a40e444402c05032044a0300460b00004085400400411a4801800d255002124021000010480d82d900342c00c45030003040744170880345e480c40d0703010f64612484c14080e4080c005518005a41021200e030300001d0b160350650040700c148982d01d160000a00500f0803c40070000d5100c1024101158203082c80c002d142d00e40d04c01e07205984039609444407504900d00419084070000b50100340186c681c40f2095014203a04040034001a503610000800b50340c1c200f000003404408210001c0d0740300c0782001000151103440300e401c20306034002c1003003140c8030382e000003181c051000c246403002042c0c03201070000c0c00e14030469101809803400c110600ca000e0805034014030460700682c8500401c1e602c840c0c3c40b581640106400d260104010304006100c074242660000d120803004016245c0c0c29484901c01000c450341e50700000720140000c42d0742500e82c1400c001e9002c102c04101c3c2e251030300340301513014996280c600c440c1e403840e540d44981201c0d540c1e07402034065401443c1d121b02d101419064144008005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 435589154 1250 435587904 435587951
    0xe06010f090b0a031101120f0f0f06050a1415130b190801120b060f030f0f06060910060f020106050a17010c09081e0a020d0f120206190b01030e01 64
    0x1142c80c2a48401251402401080440340e11034803602001002c0001901d00d03104030a25001166124225885904614407560a0341c4c00e044c80006000f80d0703041040c00c01c8400c0341c0c109500942e1106010700044441515070fa4501008a82e10b44698403401c0903400d250041c040045081244054081043c40403e80030f40301c0c40800540c0d64101103401002103c03009000c2c8034000307040101c10303041004039030710080700b0350301c400007820a1508180b1103010910b044201c20394081d454000004105500105124041d00850221a00a13483c200340d104014a01110f1190505200400810018882c004e4110344001c2c08000c0c50346114503907900c108015054a4602000c40354a4101030541a0303019103030100036141160010210038a00411007020501089d098546a1044007152001070351850b401320449842a604024507588a00e4494141d0040112680540d00140e041100c11f40490f0807241190082c00008208095040c00503030043c4041e4501c801154203000c00a10105101030f9007010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 435590404 1250 435589154 435589169
    0x9020d0c030f0318050105030105040e1f0207020a0801050601080f07090f121101080108100902030a0f060e070806040f030c230d0908070e0a02131701061a070b18010e06010f 76
    0x310500b0250192004e0f441c2405040d010071820b1006021904143d481404074446000403070740d1004074104d6502002092907010780f1034640004498003141404031080c4010303c0300000074000d505001d000600b00807001002d240c03500a8100001d017146105125142c020064240440c0d1101d8039502e00e203158550303881084c0c2c0d07440c04104c494413030365110790043c9040360681c001411400d0388a00d602030180c190244e041e81e25206042205000c11030400440000901c540e078000f650b500ad40c0703245410502c069200c1c0034182c000310104004106400381807001a5031518010703180402501d04900000a0344070000422050020b2040c011800020f40306417110164580d41e002e550f0b03031090199124100d00a0400511458020940300300094020b040ca00a2101c2922041344e10703101d071020702810406100d81c0c01d031f45847d0200b0148000340c01920040b0b8005403084d04c2d002b01c9450f0469141005088030804222100c1c02200d0594294003100c9801305410550308036503500c40c10b003070140d40c441c0205030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 435591654 1250 435590404 435590417
    0x513080c100b01020d0c060c050d1506090b07030e0f040e0a0f1707051b06090310050f0c071101140f0d06050907050c060a11070609030c0312020a020703020409020d0c030f03 76
    0x1495600000c3c80309600885c1c0c0d912212042420340d07484010300300c80c52586090001c14444889508918010303049040c0c100e0400011052408100610190340390f40103070b403940c3c000c00909010030340c0030100280c0d0030300c165400b4100e0548240850014207000d900d0100c02d01901c0710210030001001120303d9000c0c000c540b202030115102e00007084510038404010141ea01c0380c03c0c4000101440451100e414038010315050400300c0d0309011906040c2510b1284003056510030030400e0010200c80030350342000100e83c40c80d092407480d50350110f9407120303c8599414000e40001c0725031003c030642e04444500e1030311035159869415411001000e44010701500b4800c07002180003440461050068500c2c010180b001000c60b07840f40c0e500100104880840703c00d98620820611010842d00e0081e6401640302c0e40d180504074099050051150085001801c203043c010040c3d4407c207640015004142d13501103800203a03141071440055024080d4180c0103110700c1c0305041c0082404100010034510300d0180c0c542d80c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 435592904 1250 435591654 435591671
    0x10c0206030c070203460c03051c080c0d020c07030804080a03030e0102030c09010c0f02040203181e03040513090515011703190e13050c0c10140a0513080c10 69
    0x285901e41d405c1100b61b0250074803d003081d48104103907001074043c5440d11081c0071045d503181c0f0f80034000c00d09508203503050b03072041822810801000f800c3e140300c5c2c0441c2c0780540c0c19003405001c4030094030072a480d80b000c07148c01054041c40c5800a0082000030b55010002595496458007510b86070306d80030720103801003403601c021001031a0043c022039128056407400c00345000302c150015280f252207040140d034a030026582504c01a06c0700c2c8021401403600014800680010a01d8285080307458000000144984d00d041881d40300004240da0a80343c1c11903d01286001004084d0003d265565010b0102c0c8075010704c3c2500d1035240e00007a410795840020a0245016034007002759a0b1151800244c3e021035071083d403100b00b0344180308480384240000c100301e4543c01d0040440c025203006a0740070800c641d0014203220211020892030a915820b00310500082111140006503074000512004100d80c84100042004aa02070b1020301c26034014132090701e6510480300980d95454204170180c03003d1408854 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 435594154 1250 435592904 435592933
    0x50903010e010c300908040b2106010e0d08160c0902040503060612030706050a02090301150e1e06060304050102040308070308060103061406160501061d0402040f0e0615010c0206030c070203 83
    0x29401802d1003030a10700030582c9131050440061000000513581c581040c400854100340c07000041c044035402e802000c1f5040840c0403a42a0a80e0103400c16050003000b2000162076268114480006a00100c0e0681c071030043c80f450000050380c002004043d818221404030340c948699026006540c010760840b00b6560720034061024080740740c0590425588107102c49000503115812a50344041848000350401c07840d00d001c00e0a541010001003400d1800410a100c1110512901a030101342a24014243c01c1c1d80c84501051040240215015003000030020b414040250100e40086a02248465442c4040d04000f00003400c10303103141d0300081c1030810029102d01c03d2100c580c0700403001013100340f810842e44194040055440403c80d119500d8040028850181504101050740070394051242442d0500c1000704039002500390301c181600d060143c40d400e1400042e141c2e440009002c05901e00c0d0f00b0b0200684003040500d400079840580041000385d401455806068041d03c00c0e0112040c10040c1440d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 435595404 1250 435594154 435594197
    0x14070207180f060506160209071e0309111906080a060302010e0607060e060901090201140a0c02010c1a0703091a06010f140d0e0313090606050405010f050903010e010c 73
    0x1c044030040460740c50703410301c0d54580c04602c440d01c525400003242603403600030425036008030149540c032140b0581108150304107000f0880d03004c40070303180c000440c081c0b902c800340c1c03280c1d11401c0502c00c16642d14500e80410640d00440c0340c00d010003c06800300b02e03d11815000380d815090254231300040145001c43e40c440d1090040d90b090342d40c143c403444032002d204403d01007183c100c0c0a083d9800b5440d88207401c1d41ca002800542c1c0102c041c54008642c2d1030681c00003615411491581c000c600104001e0003501c5035129507500f0f00d450b42460160007411581c186a4090902c4124955002580c4401c0c4141e85402d540a041d02c02d110b4034220200c0305080ca45061842c800b20b03541e42c00308510614060019105c2e0070300c580d074003020a0505050280f0b808400b0100c580501421450b070f0b00024803c0ba18207210160f0100402ca29070b81400141c3c02c050005209010314030030706050015403420280f01a011b04140c901c01c4c84083c0003001450550a60707580039207050300c01c12000c00c0301203d980440c40f14402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 435596654 1250 435595404 435595409
    0x506090a1412072d0b0105030c010816110a1b0608090d0e060912030c01020904060806010f090b0a05100915030b09150d1205030a112a1f14070207 64
    0x80690b0803c40eaa8440c05400742014002c158894203140440403e102c2c21801030705034500403c5400055810074090501d0000d030a00402d0601c03203a17200f01712520700b010350b00004000081c5040f14035000d8400c10f50740341075020480140502c1c0c000c08281190f0841e00b12042c00ca4400e59030390f000d16121100c4040d112000001404000384081c2c508843c40c0c10b04000400d03014901138284502007040c2e55195043d40c101d214807000c203940009600c1a189481d0090f030b400340031031030060316540d4036002e070410055819100300090940c5800401502e9603034515200c004040c044d103008170604140100130400034aa000b10290075007004041e0f00014071034030901165440140081d038198480c110010030000e005000f81d5417109000c24114005503407490940c17881c1001ea01c1340b944908103044c03c0c000759141a11406544441401610215440c0d034000d041d41c07400b00c3c02c02c01d2590404400443c10484d0703040481100c802190f000c051203145951207005800c0c04081008100c0d11100e01c200c1e00c0d1521403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 435597904 1250 435596654 435596683
    0x6070305040305030f15031609050705120103062a020a12090f051306170303091917030907050325210311010b0406060909152706030506090a14 63
    0x180005444120201282c0d030f04614108403038401803070100002823801070344460280300080e010b4020050b01c2554010b40380c01c0718503030520070300b00002c40300350310300314001440b007d0500360300c6060014804150003507400c0614481c019a290b45101904043c0da42c00303140c10304403402650f0000c0110303038500c50188042602c54050690716210300e000208400c503007240101d845610fa07640400501314a019072040d081c256000d000e95200d281c45000c06040c50391005101124088800e00d40000078666004002e0075031500440580380c3e1144a6102c1c030384005504401e07003520a036258100740d07030148140ea0034144040300c060365050361550300e001d5282107084c1c80030032a204031441c49030000740500080e9a07040c00030000000c1d0030120700c1c0041c045d2a4035520000100d0b10700e040601c060740755406615034120108401e80f07000ca00e071400c40441060650b8440c00b02d00640d90100d0510030b25a00810011600071003241c030182048651030780c4590140742d0880f90840360703415000d404000410406c0ea090102c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 435599154 1250 435597904 435597907
    0x4031b201e131a03031818221415181504061e1506080a020a02120c010209040510050a05010207081002090d0f03030f05010506040f0902090a12060c0206070305040305 73
    0x210b4007481c020348031004900218009042c251503144c3c4040000d00300c104041004000260b000340140502101703441c3d902c502100383c10b01040304e4902c080c141d0750030a400d49122000322038041d00700002e5008411211180b140030355003409810100d00b411f040c1c024030036450180b60102c80000596a00e00c1e4009091926803e5400094007150540d44107840400780118444e03c4060302d0380302001190783c550414540c80c03440b8070080c0966a4880c50103680110000d80462500c20b1900000c0d56580c8050702075002540300051000c1d02c0d60f02901612a102000381c4140020b003400700c205000300c5c08a0107002d0182485103000a0716620010714001103a8403000076200707803808004401b000c2c0d03001c5500c1d547c10490301000c01c1d0000703e000f0941d5620398025a40040d03030304240104001603e6040e1300151081c0300a21040c00440e452969103000c59001000043c0e40d001002c3c0803643c540c0560f80500c40c064848645502401455005114070b010658281c454a80c1c07266010b4040325420766026001500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 435600404 1250 435599154 435599179
    0x30f0f1b02100c05060408031e06010c11061c09050c0102010c090b0c0705090408030405060a05010513022d07060e0604080d0e0a14030a03060f030b04031b201e 70
    0xc250100c02901d80c0c1a1030b01c0c1c525a00162070303045c40d000060b10101c41900b0b000041082550b83c4505460342c0390300d1540c0703034000d905140c0002810806143d0703000c0c003007440f0b0005001c0c0560307408040303903440000c0c468401e090000101481c0014480000185c41a01607041e101d4800d40c03042c840c55440c405c0c151180c03403c80b81000501e04454015141c50a070030320800030041400d69a1040d00b900c1240302c1e000d441c2d640d2401e032a00030b04208005d400f02c0720f01801d090050206aa03030110f06400411201710060302c9203641c20481c2c403c4c90703090503031203001d06000c0134070301d0b9801c0201c0c001e24000d8002c103824404186420b2901356200303011103000e8480b420602c071900c514407180c0c0105c0c45688200084076101300054035586260a440c1074120bc40e980700150b00d01400e074040c00388400406200b81261560b501e5500c58100c070484c010801810000b0910715007001c94400c000004800303402c44036000d03450785400c042d944c002907040000303441000301040c00c00c40301c241660040b04103400541000341d0981c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 435601654 1250 435600404 435600409
    0x151203112d0c0d06050114100806060f040515040e09061612021207030f06080a0f020f03071703030f0115170a0f090605011d0717100b07030f0f1b02 65
    0xc040c080c5441d49400362800c0103241e5610300e500428401c3c010040010301d0b5250070880180300380780200c154017805500d03801e41041030f04049801d5005109913100d603170b1080140c02e081c0741841540c004a0744075211910081c0b041200501030010b5801c800c80440d10768464124659603072030221100c411401480003c642241c0c071030840c2000381141c6440160600c400300e004010310400884484000966602c003030103c140040c040d04004017813440251640080c2503c501540e00d002a2001e4040c10b05e01c100fa10403920204103a4000b0080c1c00001c0d250723380002000f0303440303a1003076501e52400d201040010a0a000c514440d49000e9195151544038061120314801a43c5c001045142c603540c1c3d5012a000800e218040c0c4d00c8024820000000c00303604200d0400d4200c2c0400420340320b4110740074200700142e50400030010500000c00610082175640340810741d140741c1541c001441651000c51401e080540203d10090f1200f0f264075010144681c010040312385002c42ca0244a030b20329030142e42000350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 435602904 1250 435601654 435601723
    0x30b0628090801050a0b040c2c0607150e0d030506132007060f05130206031302060910030906050603060606070809030106120b0103030807050304020906040506030115120311 76
    0x4880e4281011441da40307841c1542115411122541034640359454280640340500c03c4144c407409904000040310f00203002d48904050300e2440031404031640d81c41700304607620001174800c09a440310a00e1030010234120b0075006002031001c990040d01c50000b85900701400307406000e1140c2c42c007500c50b80b080c100000e5650b01400d58003011001c0c80c2c0036034551400c03607003440d0020f014040c0584004035892200003424011228020001100302542e419200010703500c640c201c07600302d19403a02c0880e8410883c00081c0c802c1c071945c0c110035400004443d01003803180c2c050f00000140360003208208a0b550713411003810340700c0c1030480b40203501802c100201e5000a82520140445071806800040d1300358807141c007154541c4890b9010750311f100800004204065000e400c913684003c41e813034100d0039801c296010079403900d005404203100c1d90300c4000180650f02c1c03d600c0084481c5070111001c83c02603507028041380810704000141d0000302c3c802c010111304c01000404072228010780101501171200400460307801c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 435604154 1250 435602904 435602977
    0x30c090108040609020301060602032205100c060605030d03050420090a020a0306081603050d0309020a0509330f01030203040f03030908160b0f090f0703032f03030403030b06 76
    0x3c544c0d480054025840900c519005408141c00031070b91052000d03140c1c1c0b200c4503800300400c50850b0382401800503071651400c15182c0c0000e030a040740c00048626148001e00825000746816114a8030140f003083d6150300400c1c081c1e8001c14040504e803a00450180c14409001100d81d008440d0401107202030005030300611046e4210719000500d5a03c0c1d00195081001c05031000e4210182201c0030310600000b4004820844c1e2141020070264100c0d9011841700c81c1030344600c40c4070b40c0c40800020340100c0803484115829007080210030013100c0100c52098907030b5003100c0c1140545a07401d07404499500a00c2242e00840d00030242e40e65014241d90f084000e000344290031540c0b20f07010b00000d200c00d010741d0010400548500701503100d500d4803d13120014050014a001c0641d880711a4032150480081214070a89416203030940501c0601c594404c41003100e08410001040c01003000316000e000440030710b010f42c3c440e95051081510710020480c2e540184a036608801440c41e80d905800303050410000c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 435605404 1250 435604154 435604163
    0xf020c031e0102160b04032d0f2d020105160e06070302071e050108060108130b0a060506040e0103060513050706110118060b100f0f03020c0309030604031205010506030c09010804 78
    0x5050111360600001000d00401250b00c0c0700d000c41070000300341d000500034480c0c9501300000e881850403400c00d8006c1920654039141404884051f00311181d1091712070300c050038180c1500c1100d4520240c0112200d07400501600d005510344404908840910040341d07000300c2c0107542d03070382d9103030120020842240e009280c02c0702588104d220018180160700341803485411308000800006140c0000588801b01c000d150a0403c4403a90800c142e4030408414600703d690403003040017082c5e88000c4244010007558001d10b48c8803d0102d00010906001078900781078038401c007018030240c0c071070141e050300c00740e00150020700580091600303224092040c4440c3c04c2890441c000402e6540381007120f08018402e04009458883d110820f489150034000a001403400d1949000c40101c210200000d052180900c140030070590002110b5840203020825203a00c1319005041d80c0ca9802c00345005003203540704600d800b61907414100000788920740f260540b8491045c05405e6860302403900c1c01103c2d007040040c81102c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 435606654 1250 435605404 435605407
    0x21e2a070315021e0c010c0f0503070c0c030b16020c03010e0d050f0421050f060709120807080309010b0a08240c19200a050712080c03030a020a0f020c031e0102 70
    0x5644c183d40030071410140e190440055550305600c18000d0a44804585e040184814220a800c0c0503501c042200d40c054503500d411103401050786007140d9449007650003e41407036116828064007461074503420010400c0f540854903601c4592090609941c4085030400799900201e02c0480b0150103803005102621590002614054a60104d40d509910744c0401d02040040070284002f0800200f01e80702c2c01d440786800800040c5040440103207490164001c080b421a58842da080800031018140c0d48100d5102c9689502d81c80c0000740b00340200b4082070550300c50000343c18005019040070031024410031b80c00c0001202d0707582d441885400b00c10040c1030400c2c40601000701c1500c000329203002c2280d10070181d50360308545445541050605d03075032140c08038a541080a500c07001a400249000032100308080201c06030000303042c8580c00780120b40c00c0081a000000c1040281d800340c1d4003c06204e0555152119641c03589c8100f01d0369180d4800c0c08607010ba020030980e640010b211044030200c44203640026 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 435607904 1250 435606654 435606667
    0x50105032a040e010e060d1101031d060f0c04082d0d180b0c0c0d061410060906032f0903070608100506070519020103021e2a07031502 59
    0x3005103403000d20084507018004036051000300300410a1600509510846500351308190000528030b0028120007408010b4a0001000907402078011f14204580032070204a046108000c10340c03238480c11286080c054402e0000110408005d000703480550707280c803005203501600b041c04003110301444100303070807402c5a6400e1450440001c0015410003c1c80c1e82e02c800d141c0190f1200900180d059401c0755540000034411005d0f07120000403094a0003034210382c03080280c40281080d60060200d0360310758150800003c2044147e000c2c402d0064200d03015543c0f811622690740324120210344901c50b001d9450510410000804148010101c00c0011501251031030101d550001070314201d5560721003030100714810100146500042140c0e8002c0c041a80c0711490f15a00f65125500e60041e404940c010124802803501035921a50540b4400c1d0200000c5a44c00034808203400d07003942010688502140c4a00d8646c01c0c41e0143c80c00030081030940c9401040400c0c190707a0390000d80c4000c00d008a010950a00c0320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 435609154 1250 435607904 435607951
    0x10501150e031c1d030d020a0b06150304081b0a0c122102070e01080a080a050f090a0311040509070501080105060c120a110d050703050a0318060e0d020d170105010503 73
    0x1100c442111a03120182d03c0d8039900c05005000c01d0706140c1c240f190b00b00d454049146c40c0c01003914030300641d0214001e402075456000094991440e0411101003002c04410402007041c00c034001c00300c4000024000d00c1005c401c0380c0c950313602c158048000301070180201003000307140915540b0100042c41850505400d0030302900750010004410154030041e8010601001516055554140581200006820f00302d1f13103034481d204244221501041008000607090094543d40da00740c43d5500002000030441036941d0030181040b81d401c1d0050f611a504e400082070b40130f40e00040c000c0441d401a141e6031241d0707103440f0800802e50000c402c001e800d030107076000005a0802c604004c1048103601d45070f8400c0861f412042d1441d219a1844081c244030007000101c010035000703410340307007020150725010904001c00c100b0724800916a1a00601e2503081c0480f0046d40500811410600781c242c3d801c4880d00121203a048401c10804080b2200c00c2109900502003544a14002c0da030049100544000801c1354218 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 435610404 1250 435609154 435609193
    0x14070e06010c11281a3118020711040504020f040507020a05150f090604050c04020f0f03070c15180605070c020d05060105010801061403071116091d010501150e03 71
    0x190510040c01100d8103002d008070890704e500c15080d40010090400f002c00da0500002c16a003289424041509550001007190350345044010b402c5114240c6081e0001f45010f802075000703207030304589c1541000c0c54060700d0700340742c414284203680041000801060043c1440001c1030040d00800840c01080c2120001c58402c0100c600901c0360f000d41c0f10428986020b4041e07943c600030b040c0e850749800100910020520005a03910900003c43d4010fa0701d4a400d114800c0345d100308000d807401c0d44804030410540a4029074400c0c0050300428038001c1c40d6841a040004684400ca51002ca0b00400701019010501039401241e00114130b05145e50007140540000b031012044d00001c0302d441c0d111400620465034440313007080c01048542401da49100b00c03681640c1a42c04028811820040c04481c00415a83c0810280c004400800c100c03c00103921054110040e01100c0a029107108502d03c031003036290740520a00d4101c0c1d03040c820403c201e014040c0112040a484a0a10742c5841048150030f040201c100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 435611510 1106 435610404 435610459
    0xb01021b0102070f06020f0c01051306030b0a08120d0e01050f0114030703080313030e03070803030105130f1a0f090c0a051e0714070e06010c11 63
    0x40103e10744101035020004492500030005811354000c9000c2c01e0710000038003580d64249a1f8001900c1d54458021411840b0920a508019043c443e07030011101d07407002000d049020b0340e14060745140c1050b1400c00361031540c1c0000c40d071000150500c59800c400200710020302c000d191400300c584040d41d0504c2043c0052600e01c010804607981400008050b503400702071140c59060005000c00d0003000400203c02240000507480d0305890000780e003004840742c0000540c40c60b8208001d0001540b016803a142207aa10384100e081004442d01583c2807030440c0c0b1a00801100d60b80b4204103400342011240340c001c0c2202c20511030310100840c2200c1c2e00c0100c50a040e030781c680c01e840074030f640010450024603110502107049820000e4a16003001002d60340e00440d070b00c807901d4160070201b0034070581e110f41c08a0340815246000418810320200c42000043c201d04101020040ca00300414003103 = true := by decide +kernel

theorem cover : BRFrame.Cov 435431654 435611510 := by
  have h0 := BRFrame.cov_init 435431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 435431654 ≤ n) (h2 : n < 435611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
