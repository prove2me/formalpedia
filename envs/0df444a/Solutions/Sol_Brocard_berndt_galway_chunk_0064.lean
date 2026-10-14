-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:39:02.74099+00:00
-- url     : https://prove2.me/submissions/d232c8be-a5bc-45c1-ba42-5fb6f00bf7d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 11330942 ≤ n < 11510798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 11332192 1250 11330942 11330953
    0x190809031e0304060204080f0c09070306060210020a0908060106030e0607080603030702010c0606050604090f0c0507051002030604092a0501110705040b0a0306020703050414010f080f0a0905060c1b 86
    0x1400d440c154075045201d00c0c06000000003401c2244540c1980d01811141088034503480180d03110598442c0c2480d031452180092a0001e1f05c468440d028140980d0160b41c0640b24200308913045030040e41004650200b8824000004a9003100030030007540201034540d40030a14034015480d09040000c00b40c001e07010440100c007000455100003088940301035082c80e10841c607146a0400f0002408140c00c100c0d407040d03002900181c80030303003070b000502000d01c081810880f4001a14013544c1c980700fa90b80c010400e0f004400e0f01d204140e025805503620080c040c03c04641031040e96502e50846060070541d540120110303106440d41c41c44031042c81c2c05807200f0b0a20318925050140d10743c0d40d4400c01d105040c45251111144601c41d200c502c2c600e030095034081000d646441c03d900e000b506d01d40081c080c0c9000161141c11401140d80f05455044181c0c2ea1a01c8202040d242d10821001c11000100400c07d04ca80300ca808400003102005854804c140340500c140e1250032000b4441664076000601034044d9008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 11333442 1250 11332192 11332207
    0x2010503040f02130216140a1208040503120a0f050f0c04090c02010908030f0105010807020d0903120302090307030b190908040506030601140a0f0e030f0d05090f0619080903 76
    0x1140d03049600008000e0b4100d40500c0002c044040105400005a0020420711284002c1400d2144503910842c0004180d00b0500603003545c07401d64210180031840c6c048903c0d00414002d00656801c5409003083d00d2926100510700e00103804113803a00c440c01c40d03030350b0591618280d0500c07400342c11403d00341c000d500c035040c0000d681c0e0050145006915010b9071b00c1030511040c03070003544218501c69200b050592a0301c0c29094450000000744101070115410400240307265102050b02c4454008139240e00c0070803070468407408680081150300d101131550801c1a020307503680800804008520810001c0e02c5072501000c40400b0108200444202c00e0800c403000c0c000841c10420ba905460040d1507064881e924100100c408081281e03541c580f80340d0001e0784441003540410201282c8000781c88028900d55840140b503a10851040d0040305070700800382d40702105201d1002400e9a20008042a08004020002403c00d92005188000e60070344aa001400c1c503070001652640400c40c00f01840c14080e2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 11334692 1250 11333442 11333447
    0x609020310060e010909050109050603070b07050607180e0901050702010605060c0304120204020f1602180402030c010c17040b0c12090303030406020304170f03071101061412070e190606020a0201 85
    0x100c0e80692028008007080f0440b05901c519407240003054148000c0c040355946441c200d00405041d03070454001d0103041e0b404036141860b201140e0341540c1c030000404890351241c900326000143e4148c02030f5001d40b1140e0006031000e02c80c95560041c2d20220002500703017480300c8040e0860f41c06d0761000e4015602800048840c0d400481a90116040d440c9140d0103004a440010300030320400000103401c0801154050750f45d5180241c1d070400d54802c0c0d0b0780804000c0d050071700a040c0b01c01150000e40c1980700341e4000d41d09500c594900d007103407442401c3c40d50b46242d54803401d10858100341c106030101c220100c0c821104403410441c0700b42030150003c5040c6070400326000300b5200e2000520242055070000045420041c4000304a90030400304803241da03c030004045884440c2d030060742e1110004015001200d50380c50b041c4940c1003142c4488800a401440400510442440d01c0700e012907240031385100040c0b8045892a03140c41aa1102d4a55680455181913641200c10503008081194410541c0c480189d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 11335942 1250 11334692 11334721
    0x60105030a20030601031203180b04120909020c03120c0c0a1707050709060519080303150f040504050109020a090e0606040209030a060903050301140904021c080c01140a06090203 78
    0xc1d0401001d040c42e06400103440d0030710b1800030364640c0511420000005101446c2840600000a90303018800d035907883c2e114501c03260180e5405440301c110341c0c01040010b54100c5d681010400c1d9030405441403681c0d03a105a00f241c000100d01030440e0030019480c5400150f1205041e8414091802c0a0400c20701c81c6c0c0c0ba0b5a20160620024888100942c0c0700940510050959880d00d030710508413141903490304401800380000f40f19450080300b03c0001d4005400d101c218a500f84c032280c600850840d03454010081c001204141015004a0031a58407103141d150b5000d014400c0e4000c0d4008900c0c0440c520602050b50b519500000d070452400d482405114000704140f0b400c02c80880300540c40c1c07010304000034240301c034201d0014019880d102d03d4004058010300a14101e03a00f81d050a40c9209001d014801d4614003150300035840007128070842c41c3d402423880003401081c09045481e040c14500403019084441540001c88808110b0b01041403481590064601520380c0840c25419405d00002022110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 11337192 1250 11335942 11335963
    0x5010f140607150b0d1b031202060411010e0d0609060606080105030f030d051503030703020d091415031003020303030a0b0301050a0c080415020d021209010c02070303050f0702060d0e0c040b010206010503 89
    0x16144c4d180d88460303660350341808a0702500600c00307002564210001c2d0700c0d41c0340d0740c0c0300440d0000c125411003c0c0990010452600c142c0e000040c440300542440700441d07030541944456940003240150035030101d0128481e01208520441000517034604100014000150590106109900500140003c0403010060324001d1004000200b200c1d15410f907248952403603160450303054400403964005155002500501991064640c0003085444003079030b0503600301c8000c242e44c020118001d480800c0f0048802194080c000104a40700310f0340f80d90020341594011b482c0180c074a925074810214614080c400c042d08408142420030424009800280c00640001c00242c00d954a0151111883c4104d0301180e9412108007021075842409900d1440002800c0d900d1064542ca80016044018000210720050b17a80546810b0700b4068038103001e4456920078139003241c00c5041400360352801c50050044995480034035001e404c0450502090200b101c0c1c0c411011811541720b400100020744021541c03403041c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 11338442 1250 11337192 11337233
    0x213020906070807050c0405011401020304170106050d15180b07051803030301080d02070b070c120807060203010b0d0b0d0201080a09030201090b0906070906030b0906040902010309020405010f140607 87
    0x44051100018220b0700904002408049000a506041200114075031086d19022141000b06036259541c5800f240380000c11103025a0040005000e2600b0032001c1c3c125048220001003400c2d92240082888140c0e01441165051010924010143c146010f048003000001500040700341e210744450801620107006e05050060003e0098540c403405c00404003004005402c0b03d5036941e45848055540300aa080d40c40140111f0601141041541d4102c6101540294000c0c800a00307212000c0da2030010f0f10011201c081c2c040008400051250024500804615680c0340e1910080d0243c02c00780c60303040c88090302c92a181484900143e0300314011030307040b903507070f600c0041e0034104c500d01640141910100500001c01c80020040e07064800950326114504035910030f40e801d40c1d40c0a06805071416614540d51002d003950008005050640c4041c417a070740145004520b000840e00410100da000780c220355024403020380300340000442d855011000100564600340f0705a01615248000c18485260000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 11339692 1250 11338442 11338447
    0x30603100903030f0504140c0102030c0715120501060905042304081303050a060903031b0801030209060621040210050c070e09070312020d0f0306080c0919060603020711030a021302 79
    0x1850f129a1000d0821590004100140d04041c2031480c42a07180000c0c81902c0c0c41414010100b80d4408400e86584442a8005000250501c0c42180b02c0080d0012803004000c00400030780034400c168010301e070085c040c0d030719584049401c0801b4070080e98a20000140048102807032180c000410fa4119a409500706070720070340700c045240350008280c00650000d400d9100c1c0b25101001d000007540032000c0b0601c00c0e1000c02500d550358881a0100844486500124030b082d00104098102034031410382c0100000d00692030a500001d941c4c24170686100200e9414280408110850628035607407001340381c80342403890425103080f2180385d60725080e000d034020108030040420300703100040007400051940800e80c190001c42c0380000035501da007070070701c00d6001881003041c8a610600134841c28094a0100020300480d04414082c0310000c00b0240040c0708041800d41c084031813085c00e1040c0b501902c041d58016945080b1820050080042e4200e100e201e5044008041c00699408048a0182c040b200d13000d41c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 11340942 1250 11339692 11339711
    0x703050a0b03070906050906042007050c0a080609070503120d09050109060507051309090b0619030605070f200a030f05120403080412030506060a031802190602060c03060310 76
    0x5003201e100819050302c10843c000c03c81442c65008501a180103031074420086e5603100810090f2056001541080780e10741c21542c41c80084a0001d00d28503000d54119202c9400040101301151420f42c000c0080350020f100740039103400d05010040c01850214018688070300c6112283c4c1c0d8504c542d40407080f40695428013541001070039003060704019040750b004c00c002e203400d40c00600540e00000d5542400f480003003010410b607025201d00d9414036080940c5d84000d560788414030140c40c256074020180ba03a43d5900010005499000b05842120180e40304d9503000d2002d00043c0480400070307014034406041150f001059000000c1d0800e4913601f5203400c00501502c00c40c140d950f441201403004812104000300800c0c540c001034040d0180303204000741c01c0540c682003002c808440c003c0d107032b090380404100040d1a41c0d6110ba008920340c20041d040900f044040c0e940050003524018810b09041c5610394001c11240d41c0510071140c0c4032064030032151561038000c0000e6100c004808251010316510451503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 11342192 1250 11340942 11340961
    0xf040902030d030b030f01020c0c1f080106080a0b0307090b0414040b0c0a09090614130207051209040f06080a02190f030807030509030105040606080d090608010e2203050927070305 79
    0x407641100c080c1b0007190340700c2c410f1140ca0b858610060ba018004c1c032031441c942da118110040c04080d010340950b5080840d07406c2c00f10403640381201034440d04806450b240c2e00750040d07809201c4500249403c100026901000c5002c0c801034441c071105001300b002c01301c0300700130210301d8050070035900400c9010b9141c0d84000d4030905030b603035414a4100540341403408a01180ca8005e602002e42c04050842d400c0d02110039041c0e11100340e10412000500f942c2107184c461401c18442c8000d0510340000034408110742d54114489801c0b6443c03980028015030200010344250b007030058154085507000318a100c0041c2c00c00031080c000340d109202c000c150030400501c0c0d00c103041c031807015681a650000d000340300768102410046c0250003c0e0007141064010f82c040340c08428000c0d800b107822209180c0390240d15a18221608440b440d0040094070042021007020510000d002607070400320b48240c0700c80d074582c9041814000c00d00985102d110b85429041504281c50521880140d4806842e15002c602035a410585 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 11343442 1250 11342192 11342203
    0xc0c030f022206030c0b03010b09100207050d050102030604150501140306010201140106050309010609151205071e080c0303040e04020f03160f0303110604020a03030c05031c02090f040902030d030b03 87
    0xb140c548080d0320200c0ca2004125088502100c0c0101e2003442074503100c645400d20b9102c288180c02d05130710204502101410404103202800b10a4019200407640d02d0000c144e25040d0790304126126540082000040e1034644079840d00c02d11207880c0031200c507082600103855034060071300012181602000141060307201350003034a0011f4030740c030740340c1d64950f568503014090b5081901c244295501b01900072442d5940e5115141628025440304480c03070b481d002d80c0303810010742c007203040e5164084d0480c0480d410142c0ca00405803040720041702d85450f03241c801c0e00c905040310100047d01c80e8000304020416140e2000131030760403076011100060100c0d0007100007441c10400380c5d881c08594290920006680b2285440d0358110f0380241c403440350100e0700c0c51340240c40714802c94000358415941082030011030f00c903020345d14442c1d200740c080340d10b800601c075072203113120300a100400040303600090410814203080a60581c1c01c0c800361801d204c1160f00342c0c00251110358500d151b2040507a02c2e44102c0003036408114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 11344692 1250 11343442 11343469
    0x50d020c0a0803010305010b03010504050d0e010201091b0501120501050f130f0509100b04060e1303050412060207020418020f04020d06030b0405010c08060306130305090103020702100809010c0c0c030f02 89
    0x201c80c8050620315001c16507400c24030043d40c40d94038003004000103082c1030058500c101d1713000000c1c16155950f4141034404040c0b80030010704542d81c5e60f12070800201c40c60150b0106004883c03040a001e0b2a14000511000340034114000c0340b81080010407450300c03400100210003504490b082c08850b01210708330300030200540860366081c24403050081c4110045a135400380c1840311003d00a0800c080184420341e00544540306010043d0000102401c0c0c0249940c028a0b01c245080b038900f6684007201408462101e109441075580056602c0452400780324281d40020341c040100c0c1d400d4296000284c500d10850907450082c4e80016542e004041c096015030050341e840103c241a5040900746540208070312840a804941090f0118825140002c2c3d554803400c48510a8801d88050307039001c4805411107040c05050507001d00c0f00c0c5006903100075141c0003080301d0355141111440c01c085120b0951700c1688429047c098421002400714592080220a6a80005803a0101011440482c225894400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 11345942 1250 11344692 11344717
    0xc0f070605010e0c040602030d0c0512040809031b01081602071802030f0105010903020904030c29070f030204080307020d05190f050c060307080103060506010c0602191404050a06050d02 81
    0x1201810000305034005416108540041100713583d038032100e58480d20a0b40510009031780144400041520700350420107515000e032814078103151422001207503000c801d403000c9500c5c101c04194500c850608018031581000d0b241c2e000c40b0804208000607007260343c0035198980013404000d0140390030380200100700061a64001640c040c8181c00d184100070341081c1c464002c421842c00c00040e00358810451442901c1d0001e002c45c030140c9a0369415180600003400c22201c0c85a4031074850314540e20380803514110308131010065420703d440c440044c905505c1841d000c040c03600c1440240802c2c0350000986041580c1901c0c15450895142040d5242c82c4a4490b007007454400c0719400d6003041041003800c1d400503c51007c039010a4080c9040042c10b010846c1c83c2e200185034000100301244040c3c0100c1d03080101810a50000807980d129079090340e0080007412400030150700141400c591191f4480c1c1550141a902420640bd2200003020400644115800c001c000300f84498800d01540c102e50381040b014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 11347192 1250 11345942 11345947
    0x60f08040606170f0106050603040506010e1b0304030507020301241a04050a030302030408070b070b0406020901051207180803090901060e06041d01030605180c01110c0d061a120705090c0f 82
    0x220b0000d5919040442c0c134610301e50900d0000103043c2130000171349000e617030300101400344c41c0e003002c1c101c2c0021600104100c03100422606080c5040740f40000179402213001c2e903512507903100603005060075201009210200d58000c5811201340d4614005d010054858003a413030300c58190420740f5002180602e41100354003140c180d40000405800200070f01c01c580c01342041d40d01081d03450ba4009200d0283c90401f078010481000040e00241460f0b0040640340d8050425900b00319a40002d01c0482504031407a801081601469500041c12070b04200010640302c802180b0301118503010402c1c040061080c0c4090141d20003802006030f4841007502d02410301d03206c46d030039103204aa0755038511890a2006407940740c604004035407240c40799100e5105d01c1c42a40010054078540d18011160804420300c1011325008154000c13999544003c10541c1950181401040c00344c80345007281c0400d82159007151040c0d080c6209009030490204040c41144c000701d40b8150181d83c4c0d800601c03c28444d200642c103d85100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 11348442 1250 11347192 11347229
    0x40506210a020111060106020c1909090b0108060a02070314070203010b030604050a0b060901030f020f0103020904020c010905010f02031303082503050f010611031204140102040f0305100204060f08040606 89
    0x11241c52080c001d0380c2d0f1184140845a815442d03680078054000103801c281d156021908010869280030004030044604030f664900642c4122415514100c416010355001000400010401c242d00075140d0f480c06c6141400556021b04010203a0340b03c002c100f1004034105c019541d0a521901a4080140c25034030140b0f800e141054407001d612804543e605a400089000d5041044c00541a03d905c1340a000720240c41d0340030440c1c5078007034000050416808110f41200d80e01c65001512030314402200100d0305130400d280a40c2034131403e4008450b030501c1031040002034140400a24070390f45d0142400a540c3e100c0010928481c1d112229041d402c46240d036201704000d038142d102c14030441d040d102103101ea0762600001c81e800c03102501383c0300445c0c2c0b0501c82c007240c1f200100001074200d48103220024813400c4001c0c8290981e0826031080450510780310b0100184402403010800c5815102c0c005c42ca020301b00340020f480104030b080d00f2010800d602c00050300304030310755110b4005000304010394408045da = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 11349692 1250 11348442 11348509
    0x60b03041203060501080604020c070f1d0108011103010e1b03070c020f01020a080a03020c0307050a030201090b07080103050304060807110106032102010501031106071a0a050402090f1302040506 85
    0x8265000c480c800c60306400c0312009486889003805aa00507075814a60340c582204200107074015420400e0306014400000854518490000340201403032029601740d030010503a10900c821050b40020016410081120300d5846400100d90644011143d1000c03079031200144031141d4110300c810601d1a0320000244600542c000005c0e1107410710031504800c0c2c0c40a01801203880358420704006000036824801c1c51412070080c1c0142541c00c51a50480f4204225610f0f403d03d0101003035410b0b000760355166011030038411f141170460f0703101c1c0309400c200e20903503d50b681d15030f034034070440c40303210100000030001c6130400c0d204401c000407850100c4028003180d6100c0c20042124207029100181c54901801140c00c3d02c0c3c018098503040780d42004000c2c9606110300c090052030f6100750350071030b000d040e400401c6050341c4145004902400a0050025051520b0b00c10b00c9180c03903014003030102d10400c080030030001c2d02c0a02c038094289a819240810141c40b02004194000b450700200c1e445d8460341a440c070b50448 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 11350942 1250 11349692 11349697
    0x30804180c020f1e0c03070905010807080a120e01090302090406050106081302130e150403050a020712021c0204020f070303050603010b06030403080408162102070608070c020f03030d060b 82
    0x1500c00c03204022485007030300140eaa40108022403080e503000301c40383c0d0880d503030701035008140d8009110541d0108080040000d00301851a001454000ea842c001400072220030020100a007407a140203242d0f8450a803640c2c860301a071004840b0420080d0315251110764455000c0074020b44e8083c0c42c5800c10705151518a024090034001d04001404c0c010001d007456404039a02d8445a03009080302c1544c000ca4607a4101405440b2001551032081c1034840305810340b2042d00740e10481c080d0303407040c6c0c0326004204024140300706035125180c9681c03000904000b43c0d4074841c04148076150501168480c1c0d8a0b4404240070b4040c8070050070b140751011404034207154040e00000d100b200308138001c02030040410308020300340c0015031340070f0001130044000400107242a40142100140c06420009501240e0b0383c034944000c401100c070041a4040744c01400342e40d010410300c0040d00c400d0a2595551420800c010703d0102c0c043c2e0301910414581540741c01c00d403424812600c18030b004080074483c403900d421586510b41e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 11352192 1250 11350942 11350979
    0x20a12030f020714060702062211060310090605030606150310030203071805060a030b070c030201020c010207061a0102060103050c0105090105090603011e08030307050d050403170f0702010c080603060c070507030804 94
    0x240070386400541700c6c41c40814810b21071460080c03c21012480b400c03440b007655150410448070340300d0b000d0000984d5a21440030310f00c680c80072a80e01a045080000400070b44249a120301d02a40c400418000c0e0340da28860000d00c28855904a16184c0e5501c0a580307103160a45d610194140c002c40c000841c03050709040044a00a004903003e10281d10b6160610140303119502c000362442c01d50401041d041881250760603213046c060f100142c18002c504402a0881e4040d4a0885c0c60076980c940312100b10701403140340034071000240050f1142d980b4540342c403900d0700169103a42c1d0400600042d9154a603000301e0660300041d1300a0101611380d07840387c8902488044070030340304d041080c0d584000201c2900000840b40720b2000c543e10303142030501008030f02001d01030191049060040c490440e070445031a4070040d501c10b00d80f2038503452036810443e80281c01c40d00044149010031401404201c0c00791400107007280c101542c1040c6658520301070070040e04000242c1c10043c4500400100020001c08450301041036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 11353442 1250 11352192 11352233
    0x9020c0d02060c04051c0b0a0515040216060b15030903040906170304060f050d020a081603090f15090b070503010302040c030501030f02090c09030d03050a0501080d020a12030f0207 79
    0x5031000104140d981c0c1c0412280c00300c00700d804103c04d2045007001c0c006c110522144114a04581c00d25650b110140402110b10b204485e0742c8804010003070403c0028034100f00d000b62000c40c90a15158a8090359a4109002810984e10755040c102e0544900e07080d81d031800043c600164403401c11700e0009031290b103e44540a00b82e41000000f0800c0320342c004140310141304500042d45450b203041c7d01500d0700b648100052040c401c00340010750807450140010182c10207241d85002d1145000b00064042c0301d2103044003401c0500d000100302c0000c0c401407201c00b2054102c0381103032160000c46c20f48805081c0800700180034a0b00002031181003a00a800740d41070342e10840e410300254840001c00c43c2240d409100242134116440042405402c200100607040034500e03031403900c0d050401002c02e00d044540c0c2c0740240040e42d00d000304002c0030310320302c00c040c0503001240140c6258003443c10029941e80b44e528010740a62409910b0342c9013a4000d0340480e4507034517940400e42d184c420318141000311030f07068507581c0d89 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 11354692 1250 11353442 11353453
    0x6090702190c0f0b040e0a05090c0a12050d030e03040b090d020d030903030806040203070e0f01090e010f09060503060702070b03150306010308030108010507080907060509010c060f021e1801030207060b0a09020c 92
    0x84c500c83e92400e0703400344c440607055004c45a850907031547c0a000c0241130707502540102003032400c903619500600c0010b0000e4454101a103034191401c03914100005c107900c01018540b140300300b140c44010088408036104008043c0c0c035090080c000070740e42a04030303d00a6000f07400d0300248040507005541c21007186e0094580c010729035180c00c2440164882100d03003600180020861036018076280b080c00709101c0041c5040c41100ea15005503251070740003138102c107100c440807484c20042401c1038014080900010b03070140180713080c41c0d000a0740e0b5442c5405107004400c1301000103001502e10303140c109035000c4010103d654035690f9003031800d0164000e000c0e090b0309500303190006000c80d000e41c40c0e86001d1078040c001001030903d000f20480c1e841d0051040e40e4100103100380e50320702085c454010782d4030811313981c2801692690490054007015584413070000368081c06100c00d43d5106000d45e00c0c204030ba8000c0c00c01503614140361030208010301c0300c1041f080d4401713440c2c800402c0920f00e55015045140e1208100c80703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 11355942 1250 11354692 11354699
    0x1103010e06090f04031e1e120b0414010b091309030804230c060a0201150807051807020c090414060f070905012a0606080304060c030206060d02010806090702190c0f 72
    0xf40c0b04044a016001c05c0075141000c03e641c4400c0f40340607070388000d07103811650421262801d90106040007048800140d0021028581d00c031540704000c80c45808079820428540c00300302c880c10000052180c00364100c0040381d00003032034952141c40c00c481d0164030f4dc20042c4402500d0f01501d826829902600c0768035400818103002c080e603020a40b1001d000800401c82c0082500c100300c5541e001150540855403a01c402c0074501a864002c2c070b016091705009000e081c0d04020501c20b00551410420307148070080c0050000090300843c00c1c100c3c041d020303500128560381d142450b40c124030011206410a20411041088205c041c07643c0070b029540039540c44844590740d20044801040c0a00c08065080e0205c0341001c98442c401290b02c107441c070806022840c00d9548a07450300796000743e0700c0080440d102044100400d5414014580d00c1038048a1181d04030001e900000c002d00001001c081c021007552004c9100d841c000c010710a00e94422740300144000055140803c00320486124440100f0081034012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 11357192 1250 11355942 11355961
    0x705070518040204050a020c01020703020c12010203070504060804051c020102030a05061203040501080901060f0e07081e0105011209060c0302040518070503070c030309020a0b0304050c090702070605070203011103010e0609 97
    0x350703441e824016035008a8403507808000007010701806026a250b42000303284080c20080c00a0440e00d402074000e0280c40a500e01404104040b03000307040c1c21640704100300000d05810400780e8041d100d031450203080347c1c0d440389030a901d88284c240902c118841a002d03003448140d4150011031045031104400d009a46849090102e50680740701416041d40090000703120552182210303651101c40b4034000700e80c1651f208003007524a507040c2c0081ca0101080000c10451f180c00c000082c0d0803c107224400c13501c66030404a2824505018007901c2d04000300c181900180680035000b0701015070f0403210401000244143c0540294003c0c0300702030240c540c1442d0340c4410f0410700001e600c16505a01c48c149035503a18441101c4600004004038241527945100101507290104528054032144a009030359003030609006142900c216a8644118048000c0050081d40400d490f000c40f025810561f445140d50300c00a03002d8000304144080f00900030000280c001014048140251000d803800d0080e40c61300b1119 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 11358442 1250 11357192 11357209
    0x4090c030b03010605031b1807030c18030b01050d0302100e030c010b060903030403060b0604030807030e010912030c0303231003021005040b04140f1c0302060105010c02011403060d051207050705 85
    0x14250f2680140c4040491241503010840301c0c5280102608d1030501d81700700d840300c0b9010a03101080029541c4a6203007000790440140c0f10116401210700015134510740d60401c41c460140a801d009054410380c800c201402045180001103445205210700f00f1210300980c1e036034000624205456007094944803507428054100e50a190303020303026624090854540d50003401d42d0701d41c25038106504000020104022a002d402ca8520030b58800c09004110400180032842c02e41007491200c0d5071142c050002600081aa40015814100800c032038070040c243c46200d4a0303451004504001ea9401c2000d010301d500c0c0d00d002070300d2086800305040c40240c502110305004034022540400780410041c03025002580e6100c0061038000c1c8004040481d480124804105075916546034a140b5880f1a042640501485016080c00e2808410584850700024801020042101800343d03000002c140c00e510b0702a41c030640583c02204030f600790540e00d1381030f070100d600219040c0c03028080d2110114191505119 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 11359692 1250 11358442 11358449
    0x12091002120a09020105070b07090e100806060d0309080a0305090a080f0a06090c0b070602070203071401050f0c12040b030106030c0302090607241505040614030a12020705040204090c030b030106 85
    0x4409070301d80e9030060914028030800d01e0513810300806022900001e803030360038802d21581407541c4800d04d640c50030383c0403606084060811444150b41070f00030f0145080024007540d1008080300d000307626016030705007134804001580200c1033a00401c60003c0602d504800144100c81c000c1d10008840303039a64072201e40707680ca0310020340c4071b40e081000c0000c003040071a0000c8035424040c00b01d50081c981c0d10000a00550f01081045450b02d40109a2005611703003486400c0c010450300d2041e0354142c1e1420002807641c4220007006108120108203890008410884c0b501d030040c01c1d00f159941c6030389803082c4420342d4000b445510b000034101729050318043c0c468029591342c0f10025080d2410441c540e5274101500150900840400c0004186180c4044480c0280030600466400c240b600701e040100b0711041d00c003d0781255042000c40700003039580b41c400164211000760401c8a036503c60b02c1010ac200d0074a40c699100c0d0768454008500820308900319400194600f00584040014107a504c0c103060a0340e1241c072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 11360942 1250 11359692 11359717
    0x8090606100c060f05100501030e0705010e01110c030a05031c1103040b04050c0406090209030d03050f0408090d060e01021201080a030207030305090d060f060e01050d0c210203010212091002 83
    0x80007400d4040d03507001c4001482004049040034070140c0d182c08494048545401d0712040c00010032455806104002c410806900a0180d06041c400080d00d4507403201241410060b43e05c80c3c1814070802801680c000303040090079100b12880c281000e40e52038118039050301002c18004400280e41c001489800700a0800c44061800c65a481d00d4207201c0c001c0040c1b069805005603050b00300641d985102d00c0c00a0030316260700507112901c11040c50f01d411031001c41607040c5031419080c00541516074000c0ca13406a03100700170316542d444440100705096080d2030700400d040e0410200a12881c010740290030702e0030201007031100700ea0f61911142c2d0703540c3e00c240020b0f0160301b00b00c0090000ca4810b178010002e0020103002040c41a40f682d5588040780c03500302082854a5580c00c0900402180301c003c5c030300610781198000c5024900e030321101d0490300131f482980e024000e1103615203242c0003116a070781d60140d00200210340390010310302100009002110503200c10701509400011080d098804c3e246c0001d001d0703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 11362192 1250 11360942 11360959
    0x118051f050103020702010e0306070801060228060b010302160b0108011104030b0411120a0f060e03040f140a180c03060503190f1703010b12070c08070204050411040509030403020108090606 83
    0x81c01540203600c000701c16810441208100c00181d00d04002250050081d6959904c281d89010b00003410468402014030051205407501032164800940e0307440010303005403000500c000d44c0c40042e030091180f130600d00609550190040c052041c00e03180f55040300c0c2e40400a1160403d181c902c1c450501c510300004001c11800c001090206a00c041c3d020f8601401074410000341c0c880c605618a408a50042250329a0080ca03941080000602890410341c407900001c1d800c00c1c0c05c2c06444d10b5020600d0240e0000d065000650307000385d903500e60800340148000311020300380e000c0318281c01d0040c05440000c7c401090408500090500703001031b00d120358500581c281e6440781c1855440c00e100741c40003407094a503032584098000c202400200154024203450440981d100000314290490841c01030907501132100305030304400031aa00c5400ca030001581140c3c00a039990700d619041042552166155800500e82420007141280010040094034000d8840c0d81c0243d841d412542e55441d022101540c003c40714 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 11363442 1250 11362192 11362199
    0x10510060e0a03082a030408010f200403021e0d1101020d0f0516030207030b0702030703080702070506070b06011107090c03060b090f01110a051501030b010501050c12031504050118051f 81
    0x4004504006241c016401c17084038103800c0c00946150440e030401d142603555114800301c0140107115041c06c51290900f414604602001982c1150042d803001070b0044000505c00604050720000400e031407200100f09051001c1503052996000341b4481d41075000d03108103101019a03a00804416804100c00d5403030030328120b8858004558034aa9400071425403140c0103000c0000745e61000040d110340143d50007151280d0843c14010180000640a10f05541103d0000c0c4141c1d1144021104104d4001c28400c85a840d500b0048400d5980702c100790003d4040c000d000304114030143c10801020703880d5941400707600d417a40c01c0402c1c0c910540300782075841420300d60704803c917501030f4040300700303068a0005840c0313000425100c280c1402d040001d85607449481000620402c80380040c90f602500c820701e000390074180045192503491244a402c003002040103c0040c170f507451f40010116003060040d109104c1542d4610402e001d5090500000c0340356420500025401e807250002558900b940e0384048070300b81e24 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 11364692 1250 11363442 11363467
    0x390a05010302180a0e040605060105030f070806012105010602070503120d0905030714030301080d0503040809090c040f060305060301050c0901020706030b04060509070c0201020c010e010c170c010510060e0a0308 92
    0x42c424603101202d440d070451016507604c80c13030b80000c0031010014603507803070300b031600c1400c4030130050041e814481c0038014880034500d200c104035484001da0409241645803040140d80e6a8514107a06203082450520b4544115a41e00024102c0b501a0204c50300305403580c0800d6140c9001e10141d0045480511417001c0c0c080282c0c101402003401b400c26039290001946809500e5100c000010b255a4400801000759880801811f4004040c2d85405415070900c0e07a030345641031050500e40e41c071444803800403e184241100403240180541160150055070341c55025005d440200e501c0c0743f203540303018001540b1500075000c0316059034050340600042070408034280c2c004c1208200d06030b0401c0c1d4580700421a03490b00007005000d05d0994075414480d03030036403000914240d10304c05118104144115894026600005507520140c0d100f506409813481b8034101080f00d0040035040003032503081100b800450100300440300180c3c0d0069881d0f1740301c100e0a800384081b14205201c01082241c0801c07014040e10b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 11365942 1250 11364692 11364697
    0x10c050d05041112030406090902040302010504050f01030b0316061103090307170f010c11100b0a090b010309020a120302100c020304140402090a060f0306050306040f0605040311390a05010302 84
    0x103100701e19180400f0392003800300c2c64141365842c0748480340d80006800c1c0700d41d9400941010007824001c41c154078160441e8002403440c044c80c801c2c18010506158064006e80c0240c00ca4038092030007504603030800341c07034011402942007980328100114042c45115031104074044101c41e84a84c1c0540140003591400241c0d036142c0c0c24140000798a8014040c0340f550621083c080c00406004980c0c5480070500c1d4041c2c040c1c1042c03a241c590b032207101d1a0003104a0310380c440070460000c54008100009018a5000059002e0550140020362007021004041689006e800320902602d0081e13080b520402c05003903090048880114400703000d40c1c4144020009070015003c0342c802120301400c094180300700301011503200c1d030060700b14802144659800c80c5c06240d061041e03c1c01048210000c1c031840c182601e8503102201d00207c00f41480e41c48030001000c2c1405040c1444403c0c0c19501110f01e22801c05803440001d135481c081561607045a500c0040090b40520750200581000402c04c6107130525150040d0000e5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 11367192 1250 11365942 11365951
    0x1080601020f160f060309033203010e090106060809060f0601110102070605060111010204030c0b0a0306030f0602180d05151b0f03090c060a0909111b0307020306010503010c050d05 79
    0x520461540c2d40304684140100319503c1042401c0002042c1000c610140d46269608480300701443c150441020903400094005182e41c00700514100c088141403007685008a50710714010410000000910f000003000220b00c2242d00100800c034154450800b1941e2600640780c64640d03a01100216170544011180e40d40c000c181414501c90569a001c0d909082e17800c10070095860343d81d160204602560400100041d0440203c0211303d0031f42076a0700c1c0c00703c00c0d1441c02114200781c00030036000010f03802640301c171001d1500401d0500d0342039030307130b141407806980304c19400c3c48501407600d00c128850404d082c45040341c81d0700002404c449001603082c0b40702c0d800d009000b105d00c100f002c200e6602940c1c4110090103070080060000f6920318061403002d141c00d02c00f120b0280036030020015803200c03541c00703101801619071610700480c602d213103c08100c0c614000c8040c260301111041d42403004c1c400000000b004864070940598100341e036140101800c883c2e55042c001e0101740700b040410320005580e407246920 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 11368442 1250 11367192 11367197
    0x504020604090507170a0c0e0306060d030302090301060b040b0301060224010506072a14060f120a020d0c08220302030316020a050105010305061e090a020f04090219050a0f0e040201080601 82
    0x1460b494170fa01d500c410103407040e110301642d400350002160f500040348808000240d0042605081403804501200c0810383c0140c101680810703000c0681e036003900100d00604a20b0402d60b103643c4c44840d10a0365520a110300d4025114000044400079801c2e03841041001036001031000e10703031924041c00415844004210781100c0300d03030111888900c0f42800b4241c200c0b001181c0481507410700c3d000c80f400403c403205072407043c8020721400f4400400030085801c0c05244c0d07441d0090540740c660100c0302034000d294041c1d149030304001e0090302441c1e201648601c01d15140250103d078251224005d00000c200d20000390042e00200b00081240c1030311604844001281c0c81290b070341c150315072103240c2185c500303800484140d0000700c117100b14040d9605034000c2d803040d9140158510b003418140190740f03101c2804024010000451003166035a1682c2c011000c00f90003422f1003141020313542e0065007012050003603510840d440d1801203003001710503142805462040c02d11440300e8841c0d40040d01c62003c020a100d04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 11369692 1250 11368442 11368457
    0x3020f090d0b0106020705010c020603150a080a11040609020a0c06020f0d0e010903020c09240402070503130302030d020109020a090e0307050a080703030c0e090f1008070303170601030504020604090507 88
    0x800d500ca1010500076580620154050755061500007820100143d10041c10000c107500803402594032271003102d4002c00e85141030000a00c00c0c80c04510b80391490380c00b10b60140a10600381c400d00258204244114608540c10000382761900c0d40c800490080d18911000188040c0074140041c1c851760040801e00400b01c00e0328200540b80c40600c060341c15080390500140d448452032800c144c9c0400c050203420340200c81d006894503061010b08101400c81d21903001192000800028681b40e50303040b00c100d0b60300042500e54501d50065001407604051100728040d00c41c2524100301d01d84188250348801d6401003146581b94504003400014201000c840b50103400208680d42c0002e100b0401c00081910a8440d02e031140918280a412076221307500740310a006141c11030b002d036a643c013851140d1002902e0000d08407a200d20310501e40c1e100864100c113820740716001c0080305060b0800350703c0714041c01e0600d20240669880b4011001e60b4802d480c02508030009000a00840f450740d00f02c180c0c0044070786001803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 11370942 1250 11369692 11369707
    0x31c0609020705100606050403020315070c06020408010b010905040e07060c021503010618050d020a0603090507080105190509010b0a17010b0a03230f060a090c0305030c03271003020f 80
    0xc00300e80c0310034400c4a840d4490280010505a6130045030b0041205040c650f00781491500820303100c03601d1202d4500b014007840000b440c01805414600f4a00b500620704540707a80d21400e000c1e0003803081c4000c541c04100c1c80040007920740341602840541c400f1300d0f07000e420300324900340040e07031101401041243c1c003004182ca9a0601e007810700265009082c955921400131854849000000c2c4a0360400b40c0036064081d03041d80542c440444003001c4648914000403010328a04005080000e00e4220035115401c000038441a51506021008454100b010410003500c07a04a0b01b030032202c845901d147c0184ca039207020404004060010303a4201051400441d21040034000070b85039101c2d64000700c949510716000c121890360828050004a40042c000340402c0c030b00c10401d00d039122002032942d13011b9501e603522241003081c8444c20500070f540c04000c0366103d10303950035150703200d80200b000c8510341c20028200d589048610703252030a1300440505083c000f140d1a05085010350b115a1644044074820407148 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 11372192 1250 11370942 11370959
    0xf1c0f080c01050f070f0207120201051911010f05090d0807050f04060906110a020315060f04050406090303050f0c070609030504150903060e070b030f07090302030f010609050c0c031c06 81
    0x610341d0944890002070a40350116451600440182680d000c000c07180460040b100d0b000514503064032580384a420290000b407004035810302c80d01e0001d24280c2038000285280e80e41110b01c441803150380100a000c5400b200207640102c4030100c481c0c0c212640024940b501c80e0b40110005508500a481c10f1854a0451540f15005510580c4400009048000c040006650041c0141103818900c00900080102e58000070355840c00f0307410396160a50f0100104034241d03589051801c0346c88001c2d1081c001441d050070300d0070003080980020f4000c40e0424000491304a03c14801910507607d40d29801e040442640712a0002c00c444101141030000800012582100e070703074501d091103401c5542d00400c0904616200007515984100c0002d241c1c0102d405020340c10340c00d0103496100080003070b503107603d42da0920221071244035540081d4060054044002410006400103010380c0c0380a1002e00c019240c20460200c94030501100046580007403100d40040016102203419450364018040b50040d00d48955 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 11373442 1250 11372192 11372197
    0xd0207020f030706020606030c01050304210207050a030308040c0e0f130203010207060615030606020309130f020904050106080406060501050405010507061d030c010f050a0203130201050706060e0114030c0f1c0f08 93
    0x13680159128500308296031800304080c2c40325207000c0ca86203042d0304159481e6600c0a456110510039032245640c42c10116200300910070080400821951b00c0e141d50303007005007207020169802d035071039190b06230007080291240c484c2c0b0740100c45034180824281d8483d00b0340c4041201406c42268036540070003070000410004e010303030720140200781c808000c582c00804018045500c0359101400b0764205000c1d10b501c5030798584190f81c2d121048500400d901062480c010002d02c00d4545040e4040d01d81400450320030743c4205c06511a030701c9040200011603c0381d0066910380628409d09000510070008500024240c0e00000120180030001c500d02095003903030581941c20005028009a41d10102842e04200724001d80fa0000c4814a0031441e47c1400104d4901380c0912100183c140100000c00d001008001d91010006044141c0241c1c01c65842e071031002c1d82a040360548903ca44036587d01c08049190407000c01401d400020b050b84100003140d55001088138010a0648250385000c070f940002c981803c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 11374692 1250 11373442 11373449
    0x40c080a0605090c01020105090c0f0301061e05030714060301061412040813050a030f1b0801050403120b010503061e0105040305060c030a050702030307080c0d1112040b18030d0207020f0307 83
    0x100702c0e441c11044a6142c58500300d6500c0c11a070500f0300740008441c002c01c1c620034805007039440a48007808100402d014128030752064180c140c141c10100e520660206012081d00c5045090f25061a030311080d54101482740302510398416010401002518040c101220303070954260700c0141010800301d02c03056154011607065542041c0040d6109507001001e041c6806002c1c00caa54a04941c00c5446244404903c000000c0c140d000f000907182441d2080d00604000b0300703505009200602d0140f5005041d0018024152b107850b05051011100b98000c3c0141c2e4800e00780a00242d090f60030017800e1200b00900d80710124140041000044041230060000520035105041c0f4940d882c10000003050444200610501c00c42d00203000f8000c260303338400c45054000c1c3c04004619203032001c0190744070042440703101c250340b003c00024900c05d103d80c04145083c4250f01480011400d90313240740008810243d00020703004e2503002042403820050a96001d0281c042c0090302c00c88000c0c80010109161498540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 11375942 1250 11374692 11374703
    0x20405040309051207120b090a0f030f030f02091c02060c030d15050604051003050402190801050a110a0c02040504050a14060108060a09020105071101020a17040614040608060603040c080a 82
    0x2d0701400141800c0d1280c80d0202d000d04018958240f82802042c1601c5081c40010040d840420200e0408030302048440b6606420031f082c40d440d020649000b529108580f007550002c04e0408062203508282442614000d61700130702200d028946e8030801d00200c0e1000902264080c000f8848540c00320010005481e010118400c001640d81020550203403224696000d20b1007600704200c01e00094070340001e02e80100c0d20504020416440303901c00640e41c0414070035840000c01d0503410008140405401141c0240d041c80e07402c10014180c05d49034502c502c40c40c040500860741440c40c6000504240e40542d51041c022010f66040300841d41d03c10002e4800070803242d070541d00c91001844108400d002440c0c00000c86141080b24079800c0e80060309d24002c50402805034507001c09061084d900178001c0d111051340c81403140031001000035641a00b60024095034002894800b100401c0720b0180f0101ca055941d15203581e50140c0e220000c00c41079500c01042142c0d5041103020000d044001000364584841c0b096 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 11377192 1250 11375942 11375957
    0x605100c1b1403100c140f07120509040f050402030606280f0509010f0617090102070f06020301090c020303010e010b0a09030507181a090414030909040f030801060903080301060e0d0204050403 84
    0xc2c04140c906100c1014445445281c40c4100120340e400c104500d24070701d0102c1480e0703103820342d00714400142d000321840a00121260100814166488402003101c4041107d017008140004080c60003100c0c2c00300c0c1c0081d01540302001041080ca01110a1a50301001d401c40384801c1c5070240c111418a401503200d1523811400100074005460721015142c05070060810001c0b501e403518800404421603600c65089030014000440e0f4040d50a404654180390808010444014640380c0030000358070920031440d11a10b490406210a4408002c0320b04a0b40505601c0e040f503400c206446085501c042c1c081418801340840c0000007503400d000140041900091514036110400300c0f40d0305035440c0c1d00700360a28a00615180d001c23951000012a0050f420520030102d51845640322880c40c0f1071040c03000c2e4041d1845c0100700030006103507402c40030303248603654035805641c3c0c0d944241c540c0401400002d052443c02c2c07005128051141341c8a4524000040111400c0072403a0041070440394240c90560020351034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 11378442 1250 11377192 11377229
    0xf04090b010314030f040b18091305010f0606140c070e09030d0501060f050a2106120203190b0a0903020a06060b0306030105070f0f030209060408010509060f09010605100c1b 76
    0x9600d82c2d40c000c3e03114500603501c0d040e49080d24407070601c513034012000448400b04081503d01003000c0f4403d8070180103081c440080c1003d984030203112941081c211940d60070451044074440c850b0103501b04540140d01c99500e040221100c041d00b07900000b01180345480340301000107254640c055414060842d0001955440a0350000c1000384c0c6c0e0b050300802d003130214034100e0340c60ba10b42c060100c550302041480c00301c1601709040f41c200741ca00300c00b0380e00b64940c5041420209401f05c00f0041311070540e00c210120b94280c9032140301d500d214600c1140142220581c100000c81c52640c1d41c001c800c24034401d01c1a0f480111241d6240800c440350350700001e134002c1000c001c000c00c0e810240314154001d00c0e582000305050380340c400d00074440d0640303068a404064010406440e40d80b210b200351406450204001c0c0702074078183c03000695902d801c69680128030803000c041800c52030706125440903240058036000d6813803910281030710500c003602d5040741e0704031090002a2506800c01c062002400c0c2540c0003c11300b11a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 11379692 1250 11378442 11378453
    0x14070305060103110703110c030105010602010c020c19031202011b0903030f020c1005090d0f0602120a02070f020609060d0903081005030303091b03030c01020a080105010305150a060e0f04090b0103 86
    0x80c0101901d040c1840c12110008280002e401d480c01590700d490404e449240c805000d6040040d5138440c9a055801d01001281e0190190484602c0000507403c43d020485584200405400350340d20800c038802007a9000c0c008070b200c482044913024a940000326401d0911460100d444222000c00000030b94051014000c00d81c1c0110980040302c0e10303100a0002e0095040000c0c00081e0042901d41403000000d40c058050f214101100c2d038060f003105002c5034141c19030034040f010754000441100402c4003080060180e0034a8426505210b4001c501c0c80c1041c2069820302241d64003100180d41d0003030040c00611888107141c05990700440c840d90300c4008a04003d00f625400b1251034002c91300c25007092041182c124000110190070101907000c11002d0b40304400400d0031841148900b440650000500025454215040a048600c00c0e43c00708916070702c1e00d854000710700c400b40d00c0c1c40d4070400f6079204114040c860201e80f445100c00810101094048000240032600d01100c1220b0801c1a140104280704 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 11380942 1250 11379692 11379701
    0x6100504050901020307170915090607080603031305091024020d0203090303160c030203030f030609060406060c0609080d140103060f020304121103040b0301061206050109120b06060c01140703 84
    0xd20b00c400a40c00c504109002806010072048900000383d0100300145400b80c003000700200304807294180303070b105040003941d0a49483c4d04544c2200865060070100320075040c00800c41d0340b400c0c1c0840b03440d450581070404001c2b54240141c098882c00400800101c0c4404a494020007980300005c0704c812030200c40c1c2400390910444104a409540082c0705080098030080f04403150454219250050000545400302c45405039400194241c40007080d1400b8480002004501443c01100d8641d55070340d030b010800c0181c54032030140c1ea0005203100555400200c864001c1020389118110290410312019002012262140a0000d941510200400600100380b0601c4900154400d0561451a05869840d008074601c0004000c10054207030101b4801000d00c1030300c014100c00f5410310390341e503954030b80240350050f06d500c10f00d0040d02c1c0500c0052251f0151802c141140c0c103007501c1901d11031198903507101003000241003a4000c1030802c440d210b4503200388a040f4005807071700303d400b00909144000800706c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 11382192 1250 11380942 11380951
    0x1080304050109050d02040609020a0809010b030a150b0a0503010c0302071a040b060d1707060c080a0c08070e04020c0604050a140c01050702130e0601030507080d0e090a0207020a03050610050405 85
    0x98104020520060b40d00c500200203580c41030b59190031781e541503c00b20300140041e5000ea0744031f51000c200310400703d500c02c80d95802465001c009000284802e000c0588503480203c00409080c101c050301085842c05411041120304001e185a0400341e980020900b0f55007400760f9080060b82c001040c004201c01800e40e07003600216064170300614609079450f80418180079201d0703031081c418081848100a1014803201c603642c04034180640781c43d00303841e20304050030000d010310b0042403580c4002100080c0382c4c0700f40d4944112541d00c14071075480303040098501f0400d50b05a182c0154082225107428030b810464907000d1403196000b050101c46509003491400c0658a40315110b80290003206020b0380d0090940c1c0c14150100c5500780e0021040c44c02000908603200441158010100000280040804c2078000c4a88000a89560040394581180c00c00c5c0494042c551149400000c80d5046250340d014015084c401341201c074030640c6036158103207008402c9400841e004a42c0368148050306150041d00e410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 11383442 1250 11382192 11382209
    0x602010c021e0a1704120507051002030c1c09030501050907050f0a060503010b090616150c0201090209040b0402010203041a0a0f0c110904060609090b09070501080108060103060c05130602011401 85
    0x714030300b1114080c0c0b00d1040c80006800d081c2003540c810b020100090484004000386190030741851147e00d000343d1190550b02c90f8038072540303211810310a11400131088548945545001e01134011a220007002c409180c3d0703c01000300041c00d5000300010702c00f4030650b802642000002c100e130a1401081211440b08116aa40a02c40c40c200421146410000307503030641c2e5040c800c007a115602c40c40810114020b1202c0d80c80205241140f5106220000040780c107242c418103000d0245050708003040e030030390b580108000d4000e48501300003400710f1441070116410500c144144c0341b4148d5608040150900d03664004070021000043c442c88107600074a4005803001c050411549500307c51702c5590080581c0007489000702142d10001e401c01c10603500ca00c01034800c64004001150b8181400b2000310411204e100181c8941040440c6542c09603003054100c03014040140740e01e03800e681c0c40d140a00040c1427a1028084240002c4034190308074400380d00036000ca6800011901e15880860344201d03c180d00104c030b07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 11384692 1250 11383442 11383483
    0x5060103060c0e010203030406020a031e0b01030507050c0304050603150301021210050103090b0a090204060506040807140405091c02030c061e070e0102120c100f0917090603070e0103090c0602010c02 87
    0x8640c5d0f004802d4a5000f07400200058075a881d85800317074050a400c0842c0c0d910307a4541d011629406030541d00c81071850500781e13000c0289a480c00015500da128480d450640f590041c4400c101c2c9180c2400103507030014852021140c03d0141d03201090980e0084981f0713010050a1004024602c10031414400081c00d00f46024010074108e43c688062012000e02019034050b06d4601c92415911640c2041004110140215564641d110034094035501c590040c042d064001001085003031506005180c020080c02e40034000341001c64605e003c8039480c0a41c400294082842545540b601c184805882444040c140300d010200b0b1005154090700d0080c1408180710341d45500b0706880e6400100080341003c0700a0320355403900305c242c0161410040300043c950560400002c002c44803030a03000542041d1003000801070007000c240c012039150250802c241c1d04501c5c140001707106103200b04866445440103040c00204054551900490b0f40415040320b00541e45a41070032204941c100000031090810200741c0c0d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 11385942 1250 11384692 11384717
    0xf0402010c03080601051e03010915053a051c020d090e060a080106080307021203071a0a0b060304061e060b07060f14150307050901030f0b09011805060103060c 70
    0x80640805200103400c104600c0002213180c1d024000b1102d02000041d0500e60355040400045841da000740034203500c80341070948200760f8031040100881175510040001101004203031110b062006250507a030303141e60a4407030b2401c000554250010070300c0e0064000d000c08441101c044c034414900c2030440700031580702240381690254441c0000f410703030307000c1400700140f51a031100194a041d42904031156075403a003000001d0040000004252151003a1542010740d10b0460310f458682c041c0f80e0024004c255848000c0256009001c61a58040400c40000490050640c0450020341003110212034050b5541410280b80c5188090540c8800f2078050500c6110704001c1c11000b28001c000e001410b56442d0a0300050725111070300a100706014101c1d0300c2d00340345054031514840c4403074a41603030301901961001050900303103c44440d040e642c100030f104a5607100da5440050013640240b09581075561100e012402c20181c0e4111401c20713000c2d40c014502c03541181000402c481100300d40c00c00f8406461340344c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 11387192 1250 11385942 11385947
    0x304020f01091202040e1c2109050d030b0a09090305090a05030105010503030f0c07120503040603050c030714070501060302090a09050705060304030f050703020a020904030503040501050f040203070b0f0d05010b0408060f040201 99
    0x40da013a4195000300d400d0500b02043c0b4074101d0030410061054104400018900c0d90066240c010324840503c1c0c42c0d441c80d014070b202000c072402c0140203030464100340c920200d01402900454030350070000c2c0c9900e090f240c0c0c4102810881e60035040403400100005142e94162404640090103800110020001545481e00085e62849000301401000c64041501c0f81c2541d8140141c0009000b00c04580b035864a04d484d00c140c8a60040c0541c00c08a4906030200b511104680c084d03a1080646498050340d9600300c2c81c200b0300e41e4000c0c0804071401d40d2203400200040e1544582540920f0005601041c90005407504600f40f0255070071050040d0814010040130940c4802d569041074079504040d82d030b03800300d400d0803400c09000e0800650006485010700c0301701640300000303500c207034002c038002c03c200e0b10741d0740303100822a1090320043d5040d880614144052180d1800524004104071100303441d2002401b0f01606a942c2640140280b031000f1804114044003801025803100c0301051001080c5403aa001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 11388442 1250 11387192 11387219
    0x6010603090c0506030c091c02010e010e130c05090315090a02012003040308090f0102010c140a12050112032304120c05030a050f0c0a032006070c0801020304020f0109 73
    0x216020103450740e4184041c8040481c0290151038050b10b9140d907860700e0000700c60a80d0113442002c2c02400e1800650741c0500d0424090024680e05940310762009009000440310480a506c00603803000300f5104540d80c440081c402d0490381204c07515026140d0001804250074074052015021640c1c000d2410007080036000f11700c44500690909080100c070300b031354400804152405944100e20302c400103001c4103000e001c0e0301a00e2440700880342608443e14400c01242640c0021221401085c040d20102650000360700281c040b9a64500c1c0c0710040002c0411a041920300030703400007001c440f00310f21002c1495402902e201000b040b0140c98030001000c036112411a124034440c400d980c0b80d051b940c0c401040700064100000741002400c41e40c1d5a00b540c20b0650f15103c1c620071210035403241100d180b0080c00d00400c028100c036040354201d600404280b0003090754400c070503e6164801e20800180d00041d55500700300c0050b00e01d240005840c0d10b05803040c02071100342031080e0303410300802d03803404c0024140302c0341e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 11389692 1250 11388442 11388449
    0x1e180309090a0204050901030f020a050a06080f19141806010506030103030c030509061b1c020a020603040f050601030c0305010e0303040c0314010f180b06180f100b040b030711010e0601 81
    0x240d04040703a58002d542d90090060b030700110341c0301c50312500001c140080c1c12449034005000f1503a4190582d03541c8200240043c5510070000440e6070b4900248030034154454542e448500d140d070950703601c200304901104688900030103010601a0b0424000090080007811003142000ca00404895050000003000d41c00305100050800401501d10010144180b0680780d1314000508903a407203800c6600715003442c00c040d00b00c1c84410300c0790900034024901c41c4d0905c00300d10a0640c02078a600c20a5409014103903100820980e03107070141703050540c0040d0040100b0340c001c1d0f0043c0582d6400c182503241c86401e5031070710040c603092a80180700b8040030403820f136801000c49a00c58121001400040000c0340548803002290070b070945030003048003208040c01d504010541c800d081000c1c40390369110402c0140340d190341d008c3c98213100440000e504d498560001c1500410042000584160307503000b002072650003500032440e890404000c2c842c070290008a149145511a402400709140d41d403034450380c3d17900511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 11390942 1250 11389692 11389699
    0xe0408030703060b120a0b09010609050409020a03050304080303180a0b07030515030a060f0f02120a090f06180c0b03090a08090f060415090b070b010303050a0509091e180309 76
    0x101155405002c2c0e404103000300344041d48981c9910581c070880303800c2042200c41718481800c007100f83d141458102c0c4054181c0ea000d445030468a410001884000d1503030043c103e800603640703400480822402c00107000100f1600700103543e41e00d072500c0d5240501d070601003000e00503402501d060000030400d003081c50f40720b140b601d800911a41c4000307501c03c60b001d40b6460150103000b40d0030654244071007600004a0ba1302c42400600104244a0b0444105c0c4030b980090320448c5181c00129140c526190840850280649441c44000b40d107602d0f1101100c9200b04017048152182d09600104100c1c40340e000b0003040c0f2003c415040d4540900001e4564441c00e100611500e800500c002595403178079440f0242050150942c0c0e11a5100e180034681001150182e0021034607260380010038941c43d804a03003169070f001c401d0305126481c650301500c0a030807403480c07001445010300902d013154442520f15407180441d030f003401e44902c909000400c5001b9010340071b403c90403094000f80410341c00000071079032102d6058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 11392192 1250 11390942 11390947
    0x2030a05031009050708040b0106090f03080a0c08031014010302030702030702040b0a15020f10020304030507110117130b090303130b060604120803010801060801021e031009020a02030d050606040e0408 88
    0x1040c184a502c0940c104907007891805003842015030b1b000206500c501c1c402d001103212640c0b180c205032040001881410b50081040d102400011504809403007101a60305050610040c550380341080350700708603840c10034449291000c002d00010b000d1120ba144800b820214510709010f84000d489100356000a03001d20b80307881d00080d85032952105440202135074034500301507000c0780200a460f441c0d05c3c040740ba11449a41108640f151380380c8208c900407980744d21a640340c04019a50002485140ca03031242c1886100171310310203c840d21201c0b20748501251981a9411b405a02c0d051100603005064030549910034410004000340d00010312007110b40007a026850f41e550130002a800f486150004c140200c600041c010030400b0354005181a00c0f0050000c0c070030240c440c0c03401070807070092044003e000c5140d00e814413802c40002008503044550340c400c100c0182d03202d040203800e0342d2002c2c01c106c0c01a800025100c003001007922031070f6005075046076141c1c68145440e40076108910080c00251915400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 11393442 1250 11392192 11392201
    0x405011805090703020702181003030c0602040506030705040e070207030c050607060e0d020a031b02010503010e0619030b06101403070f02150a060e0901140106050c0304030b010f050a0f030302030a0503 88
    0xc8094680145002003034a00180b8040c1001400303900032010403405910744040d00035000241d40c084e10701c11056405404d45503882c43c1c5040310520202c0d001501c401c0e60800c1701003240d0721544011032260041e03845942d0344514041e45840d09441c010000011500822002c0c40080d41042d9500c040740d40484030540c851182d1300b4503100800410500126600ca500c1c0c5a1b80380c2500401c41c50b0649000b5201c07030f11503032440c02c40e141c40c4402c0008024000340c1c041005100e54445a00500c0d0031683c0684080c20b100ca44400910b03a900650308255806000041048928a81207100030b118441034a03142288030f281242c0a0200d020281000c410320641c2c0102940c158420400414018540002c91010b82400101c4400400003401840300040d02440002c503020014010554641c2480003030140300c0e0b2a14401303c5507038001100038002400304001c0000490a404034041c040c108900c10120a20301e0f00007048922801030b403058074040b403d0201040071a401009031144040c0a0a01c2552981c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 11394692 1250 11393442 11393477
    0x1090e10150504080a110a23040f0603020d060504060605010302091e010509090c04030501051602060a0c0203090301020a09050906040b0319060204030803040303020903060703020301050307120606080601080a03030b0f06040501 99
    0x1d81e400c0748030720f4855043c1017410312150340c603440c11050003139503106085502d40400500f0034030014003414003d05074105a10311070416600003c4001d130b4261000031240e40b01e9000074041508040207551113515541807105014407803048900401c400d08045140c15000804100d041d2082c0c0c2c545516520754150b420f500da40620b045500c01000145111b0311854020201c0110750024007003941e482d07103418001105402c0074881c098103818503070020082c1d60707030b242d04c54000340c006039a10204500051010500589090025081880316501c034101c0c450f00700014041c07408802001c03944101d0903c0d10030856900c0104940b08100100c90311105007180b03d0500101a00c180c0d40006c150703a10000070841455810780c041d02c3c150341c2c00c41c2501d1481d103c901049060340428041c2d1585908070135810800e000c00c03d41c11410280c85083c010811f944d0f6014503c0c02c00300260302038040303504403c03031880803d6450b2042c040440b4041f580c00d01c0e200ca000c0003041307083c050341c01124180110203070b1b503005540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 11395942 1250 11394692 11394697
    0xf0e0a0b09070c06050601020a080403020402030a0608010c031a090402060301060f0519030e011404170702030c030a0302010c020f12040b0a2d0320190504120c030201090e101505 78
    0xc01501400711410301d510300400c00070b960541642d29038a030502041d901d40c80440c2c2d000c0da032604070502900b09030035502004000e40c400b40c103402d06d0564070140043c103110280519050040c0350749000030b11030b4070f10603c11003100c0c090340418819003c007410000142d440e002504c9c1520000d143c0b101c2c500d00180310a0b601031298a81c088400b001e0380d0b403100c14550b0316030030040c0b84032501c40081c0046207a1001e03c809400f029a40109581a211510b00002d25280003038524107000070100c1d14038541c1c04010904000075800185c0050b5150036483c0100c64042244681081c41304000700741c0700d50644070b004d81c14003d90144480307140001603c003030385034481c0c0035490111002c04a010700500700d00c06905032044803010b410340800d060030060000340d20510740301c034248a01e24840614105c0c844c0716142c034080d80803c980c000d1041c00c0c4004100001c08003d001d202c0e504c981525440103003540009004032103550301210100d24410200100c0551502d429402c55200c1e0003000c1110070b402e1004d84050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 11397192 1250 11395942 11395961
    0x1b140a080403021e1e0303040c050105030901020d020403060204080105060d05030901031d010f15050a050102071203050f030c09030c0a0312140409020c030301090617030304030503060315010303050918010f0e0a 92
    0x7044c004059035102c000454965000310850101c1d460300411003c0c0d058507804100c07000b47c5401032a050411040d40203100840d400040390000600d0210724805d0002280c000740c1058404540c0481c2c02c0c040e00e1801d01c507807600400c040b141c00000074090758810f6928443c01600300d0415480b10110142c0120b514214246402d1000007880900c03411610300004080010000c00f070a425054001580e041160855042d2881a805030220600306121070126030180740c02241005410031000250b20080e801550050340d030540c0a6540c0c102d040c00301841c040e00c803204180f02e604103020400000e86041e44e0546014158240402c11b260000054001030003550b022501190000680782c0800001000442c180c0b170b4466010881d81c0c3d1907040f010b0305038122150021282d8020008240428015030166500c00300c0102107038055143c030140c0203180c0b44281d008401042000c42c10301e0790340c40c0181ca0b0910003084140c04400c2589410b8045003001040d22820014035071460106540d1a4541c0020691 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 11398442 1250 11397192 11397223
    0x9020402040506070f0c0621051003020303040602060403030501050f06070201030e0c04020c0a0201140309032505030f030403170708011e0504090804060801060e0609040b0301021204061b140a08040302 88
    0x10350807542003150014505c45c904584c020050703032010a030140900d2500e141d040c03100b04403804024030400120f00404002d8180d020f0481c40444c00801a60200000d001800280d40506010b080c5031070003400792075042c0c100da840b4a011008030005910340000f5101c0042e02481d0224005040303003480c5040861500b0b242e42c00500000f00301c60140c0c40013030300304503040c0300f80d8400265025926541c0001e000c2511440c1960700200010b082c190f011002494041c20341a5a0038a00314150f41c40321310b10340c0720054441a15402004020605802000044043e4000340746400701d403811000041074010140203440304107001c4020803810300007003507020014000140081106443c0c49c01c02800c2d81e00103200c0d00c00080c540ca4002b1a846108030030b20428100e02814080c1030001280070031010342200809240c141d90b00744610941e01d00700c4d54015008074090a000a000c820045d040f04e0a002c0d0798500340b0500511492139210300803c1c0040f070b00e43c01800d2500603040c3d03d962808901380044203441298 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 11399692 1250 11398442 11398447
    0x30305270606010e010507051506060d0f290306040305030a11030109060312020f06040f0f080a0e13020a02070504051015020c0307060305070c1b1518080106120609020402040506 78
    0x15040000181c1901540090322540c00825001c00111001d11a02400a06070b8005c0d180e0005007030b8001038000c2d00032900500d0b981c14140b080030200122001c200c0c0307001107180c03070304e8580180d024003410080611212000304540c07510541d0201c4e0f504c103030140c002010003130004006050316071103612010034429030042d2039541c2e59441248201401d101e0000340c0d0224185206009001d000207002a10703035040801400d0309540e507441e4025a10061b000c03e0b00e203491848600000508100001d00221407a42c8400304042c082c0c81c1445a401c1c15060f030010810f20400540802c01c0d00002d8040494900702d40101309903849030055a0030480950026445152482d01620059000700380064070b800c1c241c00700c40c030581d03131b81100700d003078039000c0d180c0e0004180c25141103400710b081c92001120701458110105034081c1e40b02200000140c0c200c4240300064034000c12002150400354802c4010110f03000203105090070038161280340c20610070001d160036a500c0c0070104546071501650000d080061207641c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 11400942 1250 11399692 11399761
    0x10b030712020904060b040f06030b030a030c05010b06030106020109030f020303090c06030406090f080703030506030a02060a030209012a030216080c22110d0e0d0e060a090308070606031202030f07030305 89
    0x1b095001400b640820b61062440812141c0c402c3c42189920711000b07008080b000f4a0303072030540c1c20500d007101c02d1382d09540350b94001d1030b180c590b000118001c14080e0b00028495425040090406200301141e80464000308140042c11000084882d041c200c04c4525554036241c0c0d2900200030b043d940c0c001002540b001c42820184044d0001615041d8060b4a0900483d83c54500309601ca021441c1c000b50b1000041c0040b54043d0f111f84d001d0008418107042c2840c0c0d9810407044540f00700400c1100d40c2513030001440306003c040d03050013030800840048900146c2c17107003030110898403a082070f00704034001c01022940c25003074140140d0140d208100b0303803010401c0561660451750703d50310981c14089000d0408112100d2404000307030313110b104182a9036011000c0204400c110850380008800c00410810600100c04a0070b4100140002031060100181b0913140d031030a2740c240c480600c202010343d0418087c96002d4035980d4201c402d001e505140004007a41d074000b1040d843c03010b002200b1003e414030b26000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 11402192 1250 11400942 11400959
    0x20301050705130f030201020307080f0c06040803060f04050609010b070f0b160908030702010f05090d02030114061f02060a020a050d0507110c03070506040302090c04030f050105010303080609010b03071202090406 93
    0x300444030000030032800058448104213030101d064031000b40181d00800400d00402d410340040c008109042d01503034981607078504040d107820030542d0292401800001070020600d0081e0781082d50f94025142805540303040000135500301d10510550240d000001240801c1100a442c82c046c0039900c92072038049414600d201c0561050320307082d548040b43e2002d4022895090000c26601615816910664000d102d550119120303007007080c0003500b2041030114500103a4080c00b403c4110410b10107003903003616000041041440280380740940c07034014078038403a01d059404520f0070381c0903040070380c0903a031003400c41c1d8101d52910841d00030650343c1d4034000502240c1e682c00b29002e80c10100600880b040140a80105606c0d5801441842d9000008200c01c00c01400c008001513400903001440c0c1c0d00b031994948581844c1d40f044101124240d640d035005000b0903802002d415040002950860444d45c14004100303802d22014103c1c609025900c020000c007000150100d9101c02c0c0c000d00180080b580c0d66003107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 11403442 1250 11402192 11402197
    0xe0303040305060108150103050303060d05030c120d2301060309050a0f030f02120c0a1e05010203181606050313050f0d170604090302070b0a0302040509010b19030b0603180a020301050705 82
    0xb01d04036030041c1b901811000e055100f010341079030780000155207991500000c2000000e001c40c001c9849010520032418144030503c03100c00500045a092903441070000144e0007240d4580c5035500e41010011442d41903070407410703481c0b03040d00c106003130000da0f0900c80d09016283c035824407002040c0000d0b0001f000101540020050640d0725581c08490031152007880102c10740c0916183c1400d03580c080305200010406004222117250140300da400240790325a120740e030030380c2d000315244c020003201480081c615a8082105440540c0028207000301799041c100018881d10015040d4504264840d042c075041c01420b10102d800030800310201c440900800b94042e088009540031040e02c4440240000c0150410340149013030154154043c000040c02c11501d607c558100c184058100b60b8240700115071a20707206521406041039a40c070b1502c84801e10110075208038406000c1c020103040c40054110750f158141034076040440307509a0440c01080380a101c0c45e0086100010b58590300b4071040c0007045811900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 11404692 1250 11403442 11403449
    0x506040f1203060503210c0601080f120c060703111201080115060201050c0306040510090507050d1b14030a0209031b0a06050307020703060c050705010c082208090603070e03030403050601 82
    0x70152080181400030303000c88410344600c0342c041d00b140902c05e820781d0b045101002d0309060540d81508004040d905a8039190b400d0700817404590201040380d8040d4401c020208000c541e0504841c0303015080e02280d9140d6a001e40340005050b11050106480b11805080c1c0340211402115100d0b81d40e51100d590740a40384845010340b02000038031000c03c01500c10b020f5203100c0c403443c0302003034a03544950003848001e210042051481158040c03000c101c1e103115002d070074003d032401c1c1c0d0f80d2925441600d00c0f18003242d40f444088240c00c000a800b07565031a800088603034034405901d0809869030345544551029220b060400ca6141c000c0740e031440b000c415401c1c041000400c0a9402010390394451200b40c40521081d524080942e00001c01080002c0054000c0c1c118030445180490803e07420781c3d18a820f42d03d1300c0b00381c20086010302d801c12550317070140a8110071090441c1514101c1120310b4031865418031812421a015050000006103010f0240c400003500d80c5010342240d035527603640e00b88692290400e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 11405942 1250 11404692 11404703
    0x20106051e0d080a0e0909061f120f0c0b07080408010606030b03060f04060605150307030c1b021311070503040e01090902010503060f1201020a0908010f090803010614070506040f 78
    0x21030003080010307524411640c035401500c01c5aa80020351900d5107541c010040c0d101c03c2080444142e4081e8540540385401140f84c00018507090030200c200420003001c2c242e42100010203900e0401c200400011180c0c0e619070071811444480c01d4906101c6e1741d410680d00310240e04840040c0080402c2103502c010400c0ba00044000c1242545560040b429a0410810560b140e0b101c2d1020541c9100101a602d030001d1003010002031690b42d40b0003040b150808e8500311129a2404020055900d4140c050380e94a010b41d482e00064403549081c08554410202c8030103801040200c6090b01284a941e0122840d01c001c44604c44e00d507080c51070000e03a20351141c041c429000d40b03908000200c40d41d1a004000c3d06603416110181143d17518028000d000094036000c0754403038003402218400d400c0a00c0284201c81d010b9640820715810300d900c242c20b443c41d034404132406a00d015280760109515500380c9040d14854030b01502d80c40c5444180c0c0f542070143c4c030005051805881305000811840d800950002071051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 11407192 1250 11405942 11405959
    0xd050601171b01080601080a06050d030503060102060a050c04120309120507050117010608060f040b0d03020c040c020a0c090c0c05100510060305060a0b0f0f070606050a0506030408040b0706140702010605 89
    0x6003003030b8001070900d4000d80e01081160000c541c4540c0544034003544003035074201c00198a40c0e10400100115164001076001c50b500009001d03017542e040c061589d000615042c140003505000410210600c164400d50301441c0030b48400e2000c1510650000300241054401d11561030b5103810030316104c21003482100e01040e02c440c08000a003c00905281c1201d5103901ca41000741c1d142020701003008204c1030010342c0305580b82203001007035558405d8448440e0080d80200400d030601400c0c40100c491849505043d980300303010410000700c1e0b2410600c1580d59403031011650100014007a00c7c0032510540c010300c64011400422204400c44e480700f441072508100b0401659958001030301142d0b8117a80c02074000c0d00c00d40b01804203914040c001c04100c03180f5040c940c9400d1241235442080d03000f4400031202c0313a0319450b0400c02d500c0d00400d144080c0c1000c0700c075a85907050035980d07030b001403040b48903604124202003003d00c203100c22030740007500949100d120300b0f01c2440c2c1034070028001d0040b4007505200e88100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 11408442 1250 11407192 11407213
    0x5070303120605150406170c040302040b0d05030a0c02040f090f0204021303021201020c060106050c030a0e0609060d0509070504020306130509120304060f0c030e031204021f020f1513030503060d05060117 89
    0x747d190760040f210a100c8a01d000e085809210145c1040000a40c1124200050200164040006040f0041c280c0c0d01d05403030751041d10400085d150b02c42c85510499040002280100e07560020b002541c640c1118016a00d018040d01c1805109035540040d50018030809460801e1006400502c8241010b00640d28140c2e00e03110241d4460045109001565000744030100c1c41d580100b802c2405090001d08950608000d0b800080c115400525010103440d100c00501288817400c00c600f0002e407400b180c080d811482c0c40004601d0041047c0d011002d101c0c2c55038080713a41400300f03009807007003807038000881a900c1c60319050081c081c0c800b040c000c507616403070021340a001c0b80c031030b12031710000c254014055450601c000343d56107600000900162f81c440c110000e40c5030403a00c0320704603052245454014240d0586c1c038241d042d09150543c440c02e10705601c188200044000c61309254145c1641c103061a03031f00d9403120000b2032608003d103240245684219400030030b4103800e00c521010940d01610841c1d210004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 11409692 1250 11408442 11408477
    0x3120f0103030f050a020106050306010902090a080a0b190e100504030f21020a030b040c0201050103050d0306150309050f0d090f060203072d050102030103060b0a1205070303120605150406 82
    0x74030020300010f41249016010740d1168006000e21900f9100110300e01c2e407203000007818030100780e0011405607030000e141e1025091a44c0300303100030049031000c0c0285078403580303400010500041c080240d404004074040e41d070f034a4951207555078004080444ac04052602d11180c0107140590f4107401081c8042c61030000248502d845180001211030200303980440840301e24042d4000543d0303001415103070712440c0e410361114414010f4071074030b644c008143c9500d141081800c000d1440000820075007401402c3c003814410031001181c00500d894000f420840c1030400f9804d0006d410000101c90080c8103503031805991020003001034440c820715804840c0d944000990356841103090013048182810040102c080300d80503115010300900c06d403260104443d50b541400c9a0098004541407035031543c0d150003c0c202034103041c0280c10581455000803084c0d449503a9034140d103110007000c0001101c0c0c08100c0c2d040c960081700040002408113580c00ea0b01025128290300907015601c0000c0d140048480e4116 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 11410942 1250 11409692 11409721
    0x50a05060906030c10031d03070308090307031b0303090219050406051017040201090302130501060f0c020102031819170c0406030b0408090117070305070906030c02030d050a090f050312 81
    0x88009004240c1c0d404c240f018462075004503003450061650342e00f040410603150300c3e07054004112001c080c60740d55050385000361250b2005008040d540d4400d204a400082d0060f10003044e4072040140c00d0440d002c946401c6020b0940c4800081d00b108800501b00c91000a150900c400d41d60121014409144c44900f0300908008030083e060028000030202001c2c1e000030705920b60071a0040c50081c24140e1030b6004603100c000b918100c2a206580c9200412000d903016600c1c2420900ca4038054403c10b9240d00001e50f03e00640e44030465040080c01403191170354030020340c00340980c420044e480b03010b5542c0300d0b401000c0c005162800c04501640d200241285040d226800950394015442200741c0c07515103620100740c10810446040c00078a80c0c0c80071070051403800b1680b0a01996402003aa440d2041c801000e00381c1d186d120100340350402d80707208191600071065611464090100041907640e0044680180c4941c02c00909055a40d400030b03414024040000d01e403040111a0140c0c203921030800710039810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 11412192 1250 11410942 11410951
    0x5030c011209060f110d06050907091502010e0f0102040e0c03040206120901020d05040c0312111f0b091e130201020304060c0501090204050c04090e0106080309010507140102070303050a050609 84
    0x28000c4031900d2000c5001c0d5005211003409818001010000d1884400c203c07402065154040c04c030105a40507081001d00a0001518095859640e10f04140001800c01e544d2409542c08411540032a205180d02c01d5110140790100407040340c4040548645240c000d5205018100340c0c4848500020480c0c1303004000c032800307039130f0203401e881c0340c04840ca009400034900038202c3c581035502000101d280d840c40703014441c0154000c2c0c1c4030401082c034614000c407803501b5421415050000721080c254211101040322001d001c40c205000c044082d000074404002d0a2402e6401e81c48000c1100740500300e940e03c4c400d200640d2031619000555214141003a505c00d4020384001d005900401c4180501c5224403011480c50340316100200380ca8820341c6c00903056407804c0f1424190300c08040307010070010301c09004518041070120002c00c076030343c04d03c44003a803a40300d89405541804000078080042085440700380c40c0091190000b1501c2c0d038002e160007000b030b00b000e840d02c007291400c04000c86d849180940800703024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 11413442 1250 11412192 11412197
    0x318010605031207020102070e01031109070804120f0c02060c06060a060c0803071805030f010f0b0109030209151f02010506040f0c1718070611100e120304050c130209010905030c01 79
    0x1c6249040a080c03c680c420fa004034118040c0030800900a0910320390b4074040e40c82003400303212002c100010711185010040100c0d040140003414000415002c00c0101841d10761894081f034076240c0d100040d90b00c0035158100940219000540c0c00313056901003645130140b14100c658642c01aa05d00d41100c6000b00701201406202040011428050203803007803001a5468511a02c40c503555a8002030034044208450750060f51101e04021962046204401e0031030001d090001603141941c000c281299002010720340501d05844205c406a40c0380003604051130101c500b5962440554500280039120588481d40600d090076203091000c0200d002c1c0303203108044da03a80c03000030342c808c42054550082c01034584114100440246480030b2000d124100140c0001c0c0c40f50321000d14203ca10501c0c0110760003041186510740914440c41503004510b010011155840c00c07a12512075050680c148614625550340c040e80501104007852040d030090402c500c400d8844803403280d035a6051503201d0043c102d44900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 11414692 1250 11413442 11413453
    0x315010f0902090a090606020c091018050411060406090e06030604031403070e0a140a050901080703020d0c09050403080405010f05061c060209040207060b090702010b01050702040f180602031801060503 88
    0x100c504690701500f030325100280542241d5607180071030001c6410b560814001600080c05c51805800d02a00032038101640d89441c0358124903281e184c00c0b40c00ca890800280864551f000f01d024032811000400782c40c0303030007001960780b90741d20039000e04600c240d0b02c0b03410089c609000015006280100b8000c0c03007190180c0b50b01c205400901e9800450360310041040f41030005286048509468401000d009414401c2c10035070200c1c0c2410806c4190320841c1e02c0340d480b9071144001489030000204070740d004c4036415140403d1494881c9020500c0074407e070048880240f41400300801d0503803290010b80620300940c004c008a00c1100900d4098a9080780d0580d0000170558110f850150b904021080d8a80198001402c2c020603000040981e4030002e01603c0140d150040d101e01e5141c000c003131640004d118002042050340d0344002a04034041c2e80006446241d4600381400741c040c01c0d42020404000465002d2034910300c2d4508400207400c15103a0b20000c0c0c2c4500b81844150748144944025580c00600600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 11415942 1250 11414692 11414699
    0x20606010c02030307050105040c0f08010204030c050f01050c0f07091112010521030c03070614010e0c0904060b07060f0e0c01090e07030e0a0609050c010e06220b070f020315010f 78
    0x15a40046200704a81601c02000b00c0070102d603080c030415000d58881c0d122841c6d802d2500720410b070503043e6a0000f0038140d20401c810000110085041c00880e82d0a41d076210840c018880142d5035405203071849820b03805101c4403664840c40c080388400a4941512003004081d4000344808090700414146035801420307903006100501e4034400c1c580f010305010071083e060302e105c014a90704580045e68818100e51000c034245003041194002c203a203203030320050f881440d90300d01780e4464029100580801104840000c0141d5141c0b1642c1103400600064082d00d42e0b920b20624101009040030504c01ca0f85d140740c20031300703404a030010480311a4818140d4074482c0d0f90303040c1400100046801352500040c50781e00d04510719480400e006e032114543c010400000c2c101d0290070500e08049807100c8481c1001000314204446603241030a5841c101140034840c2e42d040c0d4268821402d142198100d02620140450800308101c0000d0b07081000a20075030030388140541c0740d01e495200000a024074044072804041c02d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 11417192 1250 11415942 11415947
    0x501050c0403201c05010b090a050408030a0e0102040b0307021501170d080901020d0606020303010e07030c09031203090503030c0c010b03010905061f05090a06080c090402061603020304210314030702060601 90
    0xd0f10181000346001c590100c0803040d003401d40e00c1c0800854841c0d460303403c61100751405007102a40440f140d21b042c0550700e1311fa07482102601c001080d413036000da6581c113243d0048001358103480c0500001d00c0569500e003000400a961041c2c00c01c1c030900c080c40d03102c001050404035041d10009901d00340b801011100324082c41502c001c035008050030030940d0300b44008032130401c0c0d60007400014074080d0051560795040040c4590b0341040140404140350501074100345507a03108d0400390440b5002045d500c8000a101d90880207845075a0000d03101c1e21012080c0504901c5420080030360b08007807402000024410030030700d426110402e10141c01d940029000512410b03400004c8041155600c04411072030361100c002034205001a00ca4160340703a91064240902041004603104141f42250441071614040d80000c2062103108121100503000145000815000b04242c40103840305c14a00d01100448044078910f0803414401a40082c02902000c1c1000401d031044900425030b42d405445159240c0005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 11418442 1250 11417192 11417243
    0x3020a0c0203010504060203010602060c0301030512091201050c1305030c0a06052508070204050a05060a060f030b040204090e062d040f0b0906010302010f0203040b0d05090a0c03030c0501050c0403 86
    0x9860510140c5004180103940a101e0b0707038851482000c00580320b5050100082c034002d4000c0c030303640e0070100c204010b2003c00e0000824001c1d10a0b4100441c1c2e8a07001c407400304440c0d5054004001e071941c2448140703e6210300c0d92001d009d030f46681d00c81003410140d64200b003540e00c1d03203408060342c0c108441d040f040c015a1300c110000c00c48000240d0101054000e845103500940207208010781e1441408546803046162900410741c01540740d110620007410168001707800c162942c0300b01d41c240a4103565142c0360a020343c10402203108010821900c903903440100e140640089081c82c41180520307400610006811044903c04201c6c80d140c001420748a008030108036100508240c400000c110007481c0068501031181d403155170201c2c040d0440e540b45200142c022401c07402250f0544d00140001c0c880d441c4800d050b50440d0900d00c1c0c0c003140c0740d10303a00603031414040d5150000c0c0c80141190404001d040c0c03c4054000c099120304020041da42e40c1c014101091700480c0401406414081c0441c0311001c05200b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 11419692 1250 11418442 11418457
    0x20703200a080309060103110402030c0a0c0302010e0114040c060801060c0807060b060412050c010212091903020607050a05060a06030804030f0303060b04080c0405010b090117040305040807030c15020c0108070302 93
    0x440718804425124442c49400440d081d50f00b681c417040050040103d000700a400c007940c299010750442c1460f1040c4000c50061888881c1040403039480c8009141c400d41003203020681e604001c0094a001c000007440c2988101c40c141c0d550ce5244c1e10000d5130f0780c403840d800c82c126021030b66010490009952425416031100c0016038a5603128a14210b984d40d88400610040103c0c2004208500751031404a09080410309014150f4102003402c08030b29071558121100143c04560030104ea071480145200050600d8102a400200101e4200b08100000441d908510b00942c04c0755030551b50340000409071010340c080107000c0f501c01c0c40100b00082c10440000304440c828100801d000f40c45440c01c02c000d40255100781042c0d800000c8071081c80c20503206642c05803c408001c0391515660100280800c2061045824103440542c00a418140f180e420b50700030b007036080107440101d6600e003441083c01d0040d01070039007000080365980c52020b0001614280d004010313121602681c1e036075030b07040e4002d401558 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 11420942 1250 11419692 11419757
    0x40501170c040f060306050301150e012607060c0b010801051003030c05030c0609010f06060804080304080304020d05011406120c0102150a0b06070605070905180c031308030702010605030f01020703 86
    0x84042507004103040d8020107084135036800100c10785080105400d44030309519078440103503882c40610031502903250860544004042017901c41c006100304030980c5241403080d01c036078000c1003400f0680c5540f00100c1d40116008180100300d40c1d8a42d56084d08950041d207401c0c00c81c40d942d07001000000d004078001903086026100360390521011103030060030118200d0b514092655903072400d6020310001c0c41810040c146518004000e0310f0513a560003080e10000c2c2c4094040c8202000150441d907401101c10300640c0c0c000007d1141041c00700c0c2135140c19000b40c800d03910a9040b00c022030329401002401c601840b905900400440070000c000c80c1c45240090f00e50b034021a02c4128021082e214040100b43c064490725000501d80303007800e8002c3c40d011060300070038412504410001c03000701003003c41c5c6030000d08410f1015665210b0010124421040b90300082c8680804020003900b96019809901219001d40c2540d0400c188414407508074845c121000703000c525242440081c0b141c019208058072103441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 11422192 1250 11420942 11420947
    0x80c04080607030c0c051b0103061d060409140307031106060105091c0c0803040e10060206100e06010509040905060402090a0c120b06070f1b0603090b01030204090309030b011401080c040501170c 85
    0x58980ba410701c124011040c000c4846005102c1055074503103c0d4100904040f40c007200c90074007144100c410b8bd1000b50605105030349407a044010301c00c080107101c03503050054007260b0365883ca519003c3c041c0270584c00d400000c0e0144100140465004004841a5210080c5540170300c5030036000300c12400d544440140d441101d04503000c1611401040244040d2000c0340b89108030740341c00b1042540c4400d8a400c001c0071500728109003c50604522002025140d4042c202001030340c655004071013601541c0801a4058101801e02d02403200120f2050f0050303000395207140c4070f0b680d2003440005407550888884001980220045001a200d81c0840140d031002000103103404075603152054111241c0074190b03408000040d204500c40c1014042500500c0d0905051040245548a00e02440742c140700c064040d58545080c402018810080c1d0306c09154800900c140c030b940c5401c107410715107080703100041c0030071100740100d200c02d0400780a0b1811518142e6507585100710342e1100c100a039001814445d001e1106 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 11423442 1250 11422192 11422217
    0x12021305040501090f0b030703030203120711010213030201020c090705030a020702030703050a0602040e07090302031f02070611040612020711040902011b210c05060a0c02121603080c04080607030c 86
    0x1075005060007404060303008035030300940d0240e40c81220703000d4155038482c0d404044100002034002c002d43c1e841c101c6490108074256110300c410fa40c020070542ca003c0b907030751000a10399030780c4001042c89000d40303000780c1c22204429029014001d41d2002601c01c400402d60602c00074405100d07036001042081d01c054140c4407101c0e980e9032018070344060392030215541c540124090080380c0e00a17049035803100741e504c2c0c181885842c42e00403a032a01c1502c0146d034030a032014140f0803401002ca404031200c5691000c0e00700002c0d801d400455200b60000d020f1540010304030744134403030040c109000380ea81c0207401945041c003052805080200a03c040e01080b0705100b03a010342401c0c000c0041321943d900030302441c003005c481a03101680300528106040e03524244004006107401141c1c0009249034012100e800c0003034000c0341604183d00d400e1050740c0a441c444000164188004800b450001c4528843d480d0310f1115114180c40203e68010380c025040700390701c0200003903102442a00821041102810540c011412 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 11424692 1250 11423442 11423449
    0x9050f0111150402090903070803060418020d03111603050309040509071701020301030c2403050601120903090801050705160b06040902060301060302031e0105011d03070b19030b060a12021305 84
    0x10b8400000d4482c07401c8108000960800c107802e0360b44007402c203002d11729101c40750b95000280c2c080940000e01866442070185950f1041c900ba0040e010b0b00140540350070001441c0c010940c40032580000058022080901e000c03030082c030001000c0d03d43c0b00024508008003801800018030000300f4503074492060250000b10500b04101050001e5140000569a5811403c01900c5524150b10050581e601c0e4145040000404440082006000d250114140e21901c0048901d00340405508504615080c44c9004043d00000751100b11809000240712035560300c80f09580314003071544d1141340914480e200c480010441c0103c07030340c8807200410029050b40c603900854146c2d0403d0700b1110101c1d5000080c08001e0604806d600444000121400d0256060000003007062000d4800341404c108090511034003030b5410b100d0007024020140c106034031741c9040c1c070f94041c2220301e0b002e00102007490305d02280c0b0241045012584002c00315102e01a00c007020a06400c02940480b0341c98000c0303000e048011400c0e55 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 11425942 1250 11424692 11424703
    0xb0402070c08060601050a05070803070e031020031303051e1201030b060d080901050a0512041a010806040b1305010207050106031209090218010503040c0305070b1c0c09050f0111 78
    0x40c001d02661104504001c0e9003458120b01a0449050003010301090301c40513800b0f0211000d0560103c1d0384c5449031107182003510038180c1110b507264180200102800c05018940c00410030651411840b0810481005007064500c01950000000d21030352340600e000c0390207100107101141040d40820124001244269006e40294841c00300d074800e0032004105010303541040315002102120f01600d8403600799a400094802c03104685c5c148500070038400301880c058425180001260b00804241c2d2030301e86025201d40d0441c101c4541040821000840c03c3e020014401d40b01302c1e40110210900c0c1c84100621100c40350100c01190250b408008100000e10203024104c002c52085d14082881c000c0c949024100312020740055030150320600c6a1490502c2002207540c0b20364007030a0055483e115418840c02c80c2e500d54002512501c285d20700022100c4600004100f41c1201500140359a0019107040c41660880000c081c00505881c000380001c2c980700d0303c50750403040c05040040181c50080500360511 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 11427192 1250 11425942 11425957
    0x70b040602030d060501020c0a090b010306090906150611030306041104080114060a050f060304080702010c170d0506040504020f1003021306090314010204050102060718090504060b1206010503100e010b0402 90
    0x5030000f28030050720031064019100038020034005440c60490705000318245200328800c1101d01e9449400b0410755074000c0c2d0040025004980041c415960f460074508050f150b107c46030240601e0111001880074810801d01204e0943c81d00503500e180c44440411001d01144003c901002c0010080042d20038424892492420200400701c1c0c400e1030b10000b0482902100e03404140580495200b482c0e140d6150b03800c999010b40c0c490100e50b1215083d00049440c1100400300402c007031200004920000148000740040d007440d19000c0c003c690700d1034240416210140e6000f900301160b1740840c000752400506500c900816464014184041c0b078680b081c8183c620780c0302e9070204017214402e00c1480103401098455014400c004d5280a2400300001d6540200410a804108a030700c0217030000549000103600902e001d100034071440c100740c1406401803c0e007031071092049800c0380c58011026000300d00c890407101c00a0250102c5a1b1846c2000702034a00000020055543c401038915241d0303c134030241c52038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 11428442 1250 11427192 11427197
    0x302040513090302010617030706110c01060605121b030703051509070e09100f060809010207060603060212090106030201050f0d0605100e03120f04090b01020f0709050a14040b06010c05070b0406 85
    0xb0b0030ba0902908440245d0009134004640300030509900d0000800c50301031541c05000007505c005000c903429005d01603281c40d100300d5403e1080006249502c600034010450304c100700d02806131903013058800e0b01d410840500301842002e00c0001d03e00c074000e5000319409044443c80030148500e050001c0d940d2102250b01a000c5010740903149003c4c100380402980c81103218079060031a40c140310314441c0c0004248108020451f07080c0000b02c140c8002e4041d103500a5001c60700303000f00c0da26454014041e40055081400f4521548001078060034140104022280c040e10742d81e1404100f41140920390707024030310110049844440000303054860b9602c94440414507a544482c4152860030582040c03000340062112442c02c3c4600300f12241c00c001114122620100e00107030841106005070b0420f0301628104049000306c25001544030704a4119070310a03000c2400400c40d0090320740028000c1d00055038041c1c201c40321680080e600c0d5008800001e035440c040c000300c40207607942d480072444550007a00007000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 11429692 1250 11428442 11428451
    0x206091201062306120c0403050109080405040b040c0909020310080601080604020906060a0e0d02010c0b0709060f020f0c040f0b0303160c060e010c06090602090d03090e060405100e070302040513 85
    0x180c03e10b2800c00c1c1c03045000f000b003020010060000160840c05100c401c0c00780741c00a0004200d500407640c048030020b540c000000d00c1404030301e08045130f00e60002d1040502a0341401031480345880d1601c54802d04d0203682d2074148880e400c110488000f5003008180c643d030751040140110715158100901ea000308125802070030203141510511405480141500d8000e400070f00c10a542c0b550030034a41084464184e030394181004044c00101d8100d5200b2002503c2640313030340d0074070034005c2d4080007035000e4032000d40751740b6040717401e40500300e0380c0d14a015040384164008206207a45482d26030024000135105072004030b00c19000c4e0000904590140440c20078245045000c0c0c820090120080c100034451790412003a40710354040040c00d000007038400100340f140d03030315286403c20071258180d030100880942a8600c6030080e1401034018a980c1c003841a6180c059000070340a440c0c14040c4612400d00d120a0122580c42c0174103000b01d210024010b0024160248000302d03045e100d182e1241c40e401c03840c1e00080b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 11430942 1250 11429692 11429699
    0x105100f11012d0e0a1101170103050d0f08011a0721050418020301050108010e190c050405030610060c0f0807020301021c0e0708030901050c0f031201030309080115030f020609120106 80
    0x100810383c003400820703681c1000c810b0307001403c010410130744240d004200c484000300d12000403206c0410018441000c1c0d81d41a00100a0003000280d0b940c0244c8240c403501550078a40000b40c1d92a5000d11599001c4401c0e124079082030549400130f40141031040c003503001c03900b4246444069003031032202003000288001c03504000b10340c00701c070280182900d0f019045203103505000c00209a0101405614451010080800c48454048101d03d071442e2985408000784024440f004103554070501c00c0b2840ba1080001080800c050000c40380210f90380c1d078a03403202c100d00c165286072000c07507516000da41d8040144486005a00d00b80010981054035416840380d00d800303004c084044503154003103113105a00080060000707140000c1203420196090804503290301c501c2c0b02051612040c0e0b285030403240004035061480000001d21607040e41e1007511240c0079240c075008501d00b240d2114484040c00c4115030010404035204600d05801d890000d0413076484d050314100840c45142c6110303109422a9540c11003007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 11432192 1250 11430942 11431001
    0x28060b0c07300f0c06030e121201030f02130507020303010513090c1a0f040305010e0105061e090c16050a0c1a03040204020a02010914030d0605090105100f1101 70
    0x40d02410814442c1c0021516503244154840241041154048150407000c800d02c941c40d40f40c46081c550164a5090450719018018042e002c21440c448043c440c441000c60010043d8050b10304142918410f90411b070300c2c0d500e9405400c03103400d40a98001d0095207400502c0303002401943c2c4120916001140d0300c0d490081808140d00c6012108481940780140c0000096546560b100c121075a0000191000752070030810070301e511030518003100d4510300080000c00c000b07064005054000d03418008200340d941d1141032202d4101c00c2c0d0f220065004002d06d0304882c5241c205042c1750085004c80c801420400515040a081203003100e0a803140da01460900e002c01c505078600da005040545114541801d440200c1c14280c04081e200910490f0086441c03001e89100b503003c590002d410610491040c0d507044d807400d860b82e0000c440c104207035041600110f518101426900d04a56000d050700314080302c00d11045846c0a0451201400c001c003003803582048850901404101403400001020722400100c0740 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 11433442 1250 11432192 11432203
    0x7080a050c040204080606040c0306092306030c0901121104090809090901020f0a1b020901060908060f040209040b06010c150204180501030206190509090a090210020a050628060b0c 79
    0x82c0c8200e004000a01004102051450f01300d081611b021841c1004504150090300c0c0a80111400360715107400a140c80c00c800b10700c8003500c1b8450f409498551941400e041d01c80440031003072508855003000400101d0590b00c80300503a180503107104041c4101c8080082d06446400200f03450180b800310301c00c03403a460026440ca810451500007145006e030801c034010b01702e0103450140020711810766072000c05c00b00d80c08504140030390300410280700b035030711181c0143c144015400303560494411480080e01d40426810707081d0156400074480e000719a11030707850701288480200814100500b42580400142c0041c1c8920b44580e171a400c0981c5032810305812101210007003041d040c107203041074010405601c510003110b1508640c00b101e6143e03403108101c03d40740c03032080021083c0c00062400070030408c40d00e41d038056842d0620855a070300c0342d03503424541266903007400b000181c5607230045000702c3e41c00c0070402c814070950141d031750181d800070001212035000c8071a130340d02c007031100d44000994101809080c441e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 11434692 1250 11433442 11433463
    0x307121e081e01050102070b09010306170106150201090b0402060705010e010906020319090206040e0408040f080c0a0b0a081801060509040f060606050f0a080c0f0d0606030501060309050307060b010c0507080a05 92
    0x607400280d0314040c0000d45c2d60045100c0c0c468230040015003880b899110390005800b6146000441107540d20108040d07008102900c2821f9200ea444846c0d0078800e44103000d81c52070207810405100c0262165020044c1d9a400390408860031341da0340c140703041c81582c01c0c0074200d00a8016000141c03603140c10380002d0071180e02e407820440f000703140203600001079403004d050303409071014244244125074a910b07019070346126542200d4410300d9040c40000c0e9110340040d10030309000041c0c6809014075502d007890702032070150f41290b001040c0c05c0d000054010103003421001d0407015580010641c16030741d0002c134101c3e0381d00341d07400c0e12420400c496035024450140039040c001d007803625140b03161500030710302c203905130003400351000030003105030089070b4191982801d5460610f03d44c00003a5a405480c02c808000f40494031030903000c6800c0c00c0000070300c0c0e8000e100d4070518070740202c05189003800741d680c2e02004101e900403640c140700d8082c8489011030020000d070000307045180b0040c160ba00c074505106207010072042c4c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 11435942 1250 11434692 11434741
    0xc1b05060a05061903080d0e060408030a0609020f070201031104050d11040c0906120902010e09160816020d180306140405070902090a050405060109030b09070612060302030307121e08 80
    0x90030503501a04c4d4400c95402c40c0d4102840c16140c001080d58407000d4190454010294880e05051109001f1150f000354001e21801000301b0807a0350300c00200050340100500d0031041070062000380f003d0350003600000040510a00395a103000c3d181c0c00082e8801c08401001c1c3e6400c51110303000107a03802c09101e40b080c08440740c1006901145041c0000340141e030460844a03095442e5a0290304690040c0d0881980c004010001091450627000030890a07810349900800074140502040c584d100154101e002c0e030310710390f018141d83c201c1c0c103034241c866484038148066031460b021400008548207101d0034840c515102800c0a0ba410705e8100316180c41c0c40b60f00100d490500c10010304140350f9810400e0700480e00162404242940d80100580f2444540c1d4000f501c13200d00c10f03042242010000c2080380540302c064a41070142808040458101c540034000250113500c2013080102003100d0598072074018107145055101c54018561054201d510a41c402c0c0c08156040d05101d46c13003142e00740d83c00c0b0591008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 11437192 1250 11435942 11435959
    0x3010204050a0302061602060d05070816081803040b030a0e0d0302040f03020d050c030d050d060b0f0301170a08040305060403030c03051005040203090109020402040f150f050d0c1b05060a0506 84
    0x103000902c0041640c84020310810b0000307201040f120215522448660700108981e80b0b4070b03060140f0001400f4122203690025003c0c2000a18407444164642c20341e0304190341d525100d59417420926a400c100306404102440203010014490700b2410040d403044264070404200c135080c0728070080c90101c0f04d80c810301c140360040c03105100e0b00e0140720110f000c894048401540d840840d05003c0d0520703040344121034250041101081e25960040020b16100c403444034204081039440c0b404154500074001c1000e00701104000402000e4020004622044400c0742a500c0c04440b542d00c1043c20b600c1544101c1e5203410110803c000e141c6c05200f015100d0340b103403d040c0400d10f404902000c81c000f0301d0151500c280d80c08004106606000d42c4003040c0b15601900440d0b4580d2690f1240e05266228071803501da401e480503003c00303018481c40d0b0b5841400d110343c036100d00b4000301e00110030150003580800000c0110705100004c1d9010341450b541503041c01000980002c5c00c00020460070345000600450149118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 11438442 1250 11437192 11437199
    0xf0c0e07080708040f1103030304240b06070807020a0e09010e060a0c0e12010b040e01020702150c030304120c060504060f110f0a140702040203160f0e1c1407080a020f03010204 77
    0xd61007035840350340240d14400004442c0381032030451180c4003546d60140700200401c410020040f560001c420600d40002043c500d244040c202501c121203005900b128061107070800045175900603041451005014103900e80e21749102100070841100c2288503a0744408500d0007000c0d0a0141603080b20145c0414070040106501c0927003c2140545068000c440726a50711808100a44c064043c0c070500400034440b11a20040d518042e401400d42a03100380d1844100380d03054605001250a4140d55101550031640d4036140c203071122900b0310201d010b001c6420700d00301c001225403141d24810351089400003019090241d05e80101c83c055a20b82d00c1c170103400c029041550014074107031814080030746017404012040d000c0c03001c01c40c090780000032b4100f4004418025400e40080140e400b0054640d1104644a00ca203012555079562900131500301048506459440c036034119400c0e01e10b406003a041d5410301c13000c079495240040c0c5912850781030f000150060214940300188031f4118004a0095041c02d05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 11439692 1250 11438442 11438447
    0x203190501090501062007150e0306060303030f040807050109020d0c0602060f010302060d0c03060306020c0303061003050c04030326090105010501020c010507080405011110020403030504060806030307050a02060c07030f0c0e070807 101
    0x102c010608000c402c06c001c04014001008101d0103410900c3c84084402d0307500d040a02003115004007180300c4d00038000000c10508000054070300c940096100e6135495180c644802001e54090340c81524076540b41c80e81d800260700c521210b107400c0e0f88a0340c44081643c2c60f0a400034106800a40320501d40e0542c00e00400150b40c8010507030701c03d82000c4a001460b00d00e906030640092000d503000410050010840450714040440a1803003010283c1d070103820702c0c16602c0110200c0f1030888400521a03414401400400d10030f90b102d44520b210501924403070120b4059002038044201c524120a0b07442d44018440d40d40d05010700c1581450070302f040c034108540c541c4c4180050103a40101410820f400c000c1c40c040200400c0809958079102008559558990400800c664001c1c0154808510660007280c0c040c00e0001c00c030303001c0315009009408500c46035030802c45135500c0249600030364842c0b601d010000c164001102c180003407040c440b0000c81480e11b024255032020050900f001d0101c2c2c0400c100e00181c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 11440942 1250 11439692 11439707
    0x110316030504050a020f0307170a060b0a081b01050f031603060b07021c0503040b030c040501020111070209070815040606030204180c0f0c0501020f0c0c01090b0a0f0c0203010f020319050109050106 86
    0x180e0407200050b80041100c01f05c3c1c039200142e801201c000071607c0c0c44020140340070540c205000d0003503400b8089902001c0174444613050a2080d071080354000102404680c05d00c02d1141102034052600600c0e020300a00701c0d0034a900180c400070002550200c0010f14903406119020092108030f02160510b112a00044c4c11407482150401c1e0700f407010448174013000700500449014000e08040380c1d0700ca09108019184941090103150f0140d840c25180e560b001c0400d400351101968014001140c80e90b0b4014101d40d5080058a08a43d80700b0781d9010f403030542c0d541d01409018041e66900107071101c0c0707030003400e07040340085400c211105880d0401c0e0904183e40b01310049080095030501100d0303503d061400900a10864a11000c035400101e00d013803568002080800f040d007001daa400044070b0325580c4404003446032444080108408001c01c0c25258001c02141003180d00044c000140c541c0190141026a441110071141f510709080081424070240e100300350140810079420002981885005050f02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 11442192 1250 11440942 11440963
    0x90306020309070308030408070302060603060105131517030909150303070201050f090301060f05090702060708070f02070305030d1e090b0c090f040603111002031206040903020a0611031603050405 86
    0x1a0340010001d0b00400b8100000b00c015580324080560700e107060b080811b00b075000982c0440050240300042502490000b61441c1170f1200240142c0d50700960050180c020124004100000f0200840024103000b84040b070340c4410015070007942d61400e04004103e4010f100038a030034280ca1040f00580d10989000083e14055682801c1c0141e5800c4c110705417801c0c6001301c041003549507003429004150030681d0500c40d0102c0c1c0d425588015030380c45079103007607032200d40450700c0c2c10008015500050038148641c00b11291440c4500550786031030703200c0d01d5070303070550303011403a516505521400200c900360300c0085003030043c10000800b0840781507541d545080482010704082c0124401003009011a9101e1004004c0040d006100304211a45c2c2d16041e040c0180003c10644583c0700300e0428180709002008640b844500000491a2980c3d80c4040000908207080309404501c648011080056054800d040310344030303103408503500c13850003050b94001c02460702d0149041608100c00e200004000041c2d12092 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 11443442 1250 11442192 11442203
    0x40905030a08100f0308070b0106020c010c060c050903010608010b0f030304060207060e0f030d030902010e04021204080c030415050705010b0a0305100b060c0a1110090f030f0812040602120a0c0903 86
    0x790f00c50004043c81d251454002c0004c1a1a56000108000b5240010051144206880441c0360790301c0f40306070f8603001480800c9003c103840302842c0c400030300240e000769182032040c10400e003013421980200703007180d07031507004204075170341d40c80034901d00745481040c840d8241c030210021850141410b400a44800306841800c081c411041e80d906c00591352080715140c0100040d007203900c4100c10b0100240a403a9001050b40802d083c0301c4242d009041ca4021070f840b0940214a05146e62940d9554a907030341d00545400f401c81c00280070104a00d11462030501120807540d96580d15000c0504040b1b003144c4942e007a482c460000d40c030003017001540105400e0800c451040c000500f14440c000070032140c0c818243d400301030f409201450410088940d005000190094960420400380080c050f2a4690f56015054801c55034003800c00018081c9440d140105118030040c07070401c040c2150b422021981903a00b11103490300030501c8120400c10b282e1103680021201c40620411841d0316002c1e007489080e00002d0328 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 11444692 1250 11443442 11443457
    0xc060a0f020118030c061406030a02060304140312070908061012020321040f08070501050702090a02070b0403050301060f03050c0a0c11060403060b0a0602010203071e03090b07030515040905030a 85
    0xc88500030360201d074070740c0d0074108041080c01d031a01e0010000c480c0440200c2e6810b25020030326503448120035400d407180d20007400030000300c02284c0802c2200d4000400465842480e50003025072407000344060b0a580c03a20480000450500f0030b4040d041e6034054000040b0ba03801182003101461303403112070744100c035030701040022140607a0020908003041c6001340301e11111038044190f030f0001120014005c0340c04203070a050009845242941e1107119511500780061814002c0502501d0a11910358102401c050014584402d0f50355001407444200c2d0181c003c0b0b140400100a0107410110401c40020b240c60201700615152040c4465030003885054400c002c0180318403c20041e10a40103a00043c00a1009440e15500e24240025001c08004140118016000012a58014021b0700d004400644882c0c081d1200080c00064101d42d07085003c04154842483e08003040050801a000d10102c3c4e0f03020885140c42c407403400d120955000f1690081c0e00d070560110101c2c0020007a02c3d410080381c41c0c10b00d07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 11445942 1250 11444692 11444717
    0x3030915050408031504020708030103030e011808010504031b0506070e03011410030c060504060801230d050105090105010609060503061207080303090c0a0b04050105090d081b0106090605030c060a 86
    0x109030010304010312251628140074030091000f402c01461242d070b031100031310454460b80b1007400141c0c001e212000b400100148010b0000a01810b40040c1551040c54400f0003c1515042d9600a164660154510b44d5548060009150b40309072540ca401010103944071810142c0d43e078495035004010408420041d002e40700c0851135400790082c924a0290114084081c100b91028040300100c5200841d00522901c4000860700e00420036078007222100c0e10340b0b0300903a18007419201008008141c9600c0850300b4222030034161b8907031059260503402800001a5460244c113464211074045c2c108001307011321500c04006141d448000c42e94400b409130b45405951091405081c54209260007241d003d00000c810000d070031720b00150440f40c4a8080318154a04c40e515290280c9074481c5000d0107000843c10070401c401800c03c141c181007244d120b03001d5a80741480d01020b18030b4007a030071042088140d4550108015000260042002400c0100c0c09000c552180c0400100d6030f00c81d40244000b888018510342 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 11447192 1250 11445942 11445953
    0xe040f02011e0206090c120304140a050603040803100b04050a030204020c1005040807030215060f040914161814040b0a090f030302040602060702120a0e0a030f06020c0f0d0c030309 79
    0xa240c1080202c10140a12101c42c0030f5104d1504443c0c5543c0c40c03084942c02c10350f5107403c503070505140c4007101c061031900303083c580304000e070741510030f1400c3d0401007484000901d502d400780107500c90b40c0100b02c1350303860b41445021005004123660000e001d00c4424001400b5968800303401c0c804482e81202c00503a01e54a540c100c50411100030f94140d68180b6200800c0207004450b4000d203d418401d0b4283c0d251510302a4050440250030307908290400c105040004050429520034554079001d0070302c410110214801c0d8516024441404a9a04072036200801c018162005000d4071451035160520801480704445289600010006440d0410407000719181000c55131110f080d468018040a0700038407142406400f0703521920550006100300000550010300c0441e00380407060058400307518040d81d441e011100c9100d000700b03080c0d1102c1c546c0707000000154000c0155086a20840016031034010b01d0750001e0078007948105a4034150032030310801150326030000012080c5a85410001000c01090405c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 11448442 1250 11447192 11447207
    0x1020606060a030e0303070c03020f01090c060c1a07020c010e0f060a030b0d0b040803040311160522060906030b070801030804150507060903030b0301180c03170906040306091109010e040f0201 84
    0x80342e00c140000021f00610543c819440700425020760201c034080741c02907803810b00300c4482c100c005d424802e100782c00380300b0745208803048060980284c1301841c011400e14050309000c01c05481c0303000564485000c84659507040305100c0f40941089074035102803031460002c5090b40c803034000c030030041690fa9000c400103a5115034401d111250030503403510031031138a8a04202e42d9070003aa0140e02007017010b03400c00c0044800156070142e20030340625050306075140c68217000b420640c86041c0b66024130b4003040d0b41d0f004039941c410301c00244036a01011030000c2c51800c10b4228400c0160050080040110050011521250468044035101004018039440e040411902c40c02848401013619003001416001d06905402c0742c501000114020040b240101d03403007240703c40c4881802000c02059031800c00114072a9039a4454110784da840c25864851502c00040b021f91103a0000c407201076503501e40d90f0611030344101c00c002c4a103068480f00307080d504003e20010407070300c002c0004200000050310320045900c034182 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 11449692 1250 11448442 11448461
    0x304020d0b010603020a03140610030f1d061006090501050301061202040909080309300904060302030d110705010810051e04050115030e030703080105090702160603020a030b0a0501020606060a03 85
    0x201c6000300e5844040040c041c1d48516602000241070001348071907100710498103400b03035070024542c0c0b0507498260b000b0360140c26007003542d0030896038800110341d11710001c480442c0820480d40c0988001d10b00a0504141928150040400c2026030041440b86980010071241914a18200b242004007101c26160103071189400c50300c141800c22002504221884002e18080c0784400c3c15113218003c161411102c2072502041149240400401c0c01c40b8402c01200030484407002510204516071a0740229240201c10090384000031541b44504602000030b00c1035002030842481c1c240120300f400d03820502002850b0086500c80c840f0b02d1032416200075a9040e881c074041c000b401c00d00143d80d50b030310070400c40c035444010701c004281030015030034000001104451880b6816118001681d090030700344501240020000c0d0705500c05c0040c1074002c0c018050340c4100404082d540503a0715101b0400080030745150350817883c007503200300c0c0080c0704980e004684942c1c490400e80381640c031001d174a1400c034040c3c61043c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 11450942 1250 11449692 11449703
    0x11b08090a150b030c010e0907200d020a0c2705070e03010606090f0906030f0f150906020a1b0201170603030913020c0114040c0303140c0f0708070b0a090b0304020d 72
    0xa00c2c0c5071480750a40201203610000c4003036500a404000040d11585a044070752540905100c00241140c2d01071a03001005000900500c4184401c1c10705443ca807603d102c0d0800056440301d00c2c010100403003511858040c02d030058a10390300a8480b220828004117086440580c0303078581c800544464801c2d4000303044c0d51002002881407550310034026200f820140244101074100d18004103440101d8050340341140d900c0041d840f4a00001e0301d800e01070422142d4129030b26410030498a0398002d0a0068040240c0181c0c4c005030340b08028400580741a01d42004030002e00c810641200240c1c0c2c00083d446400b101703c100e41c2c0300036078030100040d0461052183c40740d1b2180004610b01c142c41820b601800860107410001c20100398640410b114000080340d00800200081c4001c0c8002072007010681824801c030002d007410840e1080c4014188003000ca000c3d40d0a60142204106038101000f1a000034180d031001035180c240b0725000200141518003500441800001c08201152500844405000c1e0081c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 11452192 1250 11450942 11450963
    0x609010c0515090706030b010c020d0201030219080604060905040305031602010b0a0303110c03030f07060b030c04050108100b010f0917030706020c030c010506060a0e0108060103090501020a030603060e011b08090a 93
    0x514601d240760009a99021032841805404951176000384101052003005860310000b00c03146608015a40b2102c1c0c8007241050303003d21840d81046403982d14100301101d1a12180e240b8a862400d000403544507600c032155044c1407500b40804070b504082101c0d0030010038030748461046030050050340900b0801200e19040072880900109043c3e010a00e09000540d041c00c1d40c00c480016020540c0e24040e060f03141ca40d407032003004400002900c6a01c10071740504060706407143c400454000604881d4243d110702c0d020b80210325540d41c200400d21a090081c0740900f030078081403001000041c6034004900641c825040c1a00014841300303c20400e039100310344d001206546c1d403041e605d003680d10b030380081c00701800c50360819002c07405030324161040c1c0d01800469a44c4494188031240110703007a440142c041d605041d0349210481c04101c080c00209503002003910045180d078618a4948100c419510031500f882e450001c99040c0c07801000000c0d030314180300d0700d4000c00c1500c5140000c5c0c144229510024000900d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 11453442 1250 11452192 11452213
    0xa0b0c01090309052704030e040504030f03050a05040c09020c07050d050a03090f0b0a08130501060f080705010809060609061801060206061c03080a050709030f08030612030f03060609010c05 83
    0x150401c2000d148680d594007002a521003d00098006014240c2650074802806021094030b25408a50140c000d1909113460741403000400c0c100c2e82c081d2020740020304840101e54206030540035043e0043c0146000704403c2ca0301ea2503c2d038241c0214001d402042d038002842c2071282c00300f0003184001d401c00400e54899220a4031f443ca40d651070140040380481c000020000302c4038596200700b0304454044403d1880c1600103c42169440c03c0140b070b10180682908103280403035001d128400c003808040241e0103c0314200345145182424a0340034034100003041c010090981404901903400c81d505652006d003075121a000980c4130506111248000c3d29440000940180d0008070117016a00c150703240045500d815101c041340ca40300d8100a008a40c0c00350100f800341c40c0c60b41c85558450035500c0c100e14401d450303650303181140200020030b850700070002c424820f89241c07590070300702408082c0d0000d47c038110304103503031441900000301110311420340843c0701d405e107074042c02214811075400700a4600c0c00c08c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 11454692 1250 11453442 11453467
    0x10302040e0f0103020a0b040b03060f040e0f010608060a0204180207050102041d0103020406140105030f040201020f100203010512010e0a060b040b0402040312020606061e030c070606080f12070c060309020a0b 91
    0xa0911050b84120090b46d000102031003800101c44c26507074440702981c6140d4600c0300784040d90032081070007a0801c3c1d44075011031041c00140013103030089102d0000490104d182001703c600e4407802030266010544100400c0244040c00344500840e5094540c0160f1070708514184140240a0b550041020142040250000a41c44e500c0141131328421602004030740e440d0076444800c3d5040c480b845012560410108808151080c0d0f8907502610500c12a4103000704203a6040c02e0507030741007107074142c10340210044c0554036020a41c3c00e124540e01c00204a50190230b40d40540e281c61068002e40309941e210708249081d10780750003101d40150082d00540d55180c1d2442c0481629542d100fa201c014015800441c840d840c20604a500d10345038844a09070515502c1600f248544c030240806445202c00c00c01040007400c180212001094410050801440078000190600c3c1000b9070030300d1400010050074000691006e5007c040d11403c0c130b00010b5039425807011854443c096004143c5921000c00c00401c10a03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 11455942 1250 11454692 11454721
    0x9010b0901151b030509060d060b0a02010b040e0c0303041a0409060608090c0405010f0b0c01020903150702070f030308070503040201020f06090105010612051302060703020a0b0c03040605070509030a020f010302040e 94
    0x1002607644400c06480300a0800b03c3c1c800b0200000d0000360704101481d102c1c90010050003c10301a0000003413425541c8031080751540c48640101e000d80d4440c1e140304458031306840317038111901c82c440140400f002010f001030f46a10a0303016001601d101840304200000c1547d041e20060300740078004201e03180c1c03103410141030030340103c0e9000054070502c2c580001d5420076001e400d0480d498000d61103141400c0035400c260940182c118a41030350344c00c0c8000685503034100001e03640d910324100300a000713080000c0c0090a125041d049a074400d441131004000080d4010800c0b42d10034901e161854483d1034510040f4107200201c4006d9949104403010302180c01c030b041d071000d4126845521022400003d0396000c40599500300c030650500048800c044001d41840d0b8000c0c00018800e2040c0c0d03080502c296900348509000340d43c1040b08140c04820441000441d1003141d40003455810083d0801c1200400240da0344a01580240980b114400000050340a6010743e8068074444003c0ea00a1520043c09210346 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 11457192 1250 11455942 11455979
    0x20a0b0702150c182202040b07030908030a0207060c020a08060403030b01030b0301060302060d111201030b0f060d0210140c0706110d0905090c090d0204020307020a12030501080c0909010b0901 84
    0x3018000b010400b108180001c0b030300c01001c0c06041d080240080e4003004040d1802c4002c0c1401c8030401766100c0344029032803008002802d61482402e440d0f9030316040003130140d200c1d030300103c075117520403c02400315680000c4c8250860f1918038001141d44601d00c0440d24441095008000c580700e01000d00007050342580103001d0f5103200303a80c20011086c8500401d826a041c500c27000c1c2d041003040001c0445190300d074105001c40c54407100e100385040714116041030040c1d000d9105132800d030b002c4011320001d000d14005882d0000001c40c0d199207800c18540008020750740c00d0307002c48203001840c100f0030018111242520541450681074880540e0f0340d40c4003520004410000c400310340203c44403d15450301580d100303130642d038014040f65010b0b40d030b840302c40100341e21028403260301240c1e11000c03a0060b076803400118070a62007070703016006a80040c50400455180042c910b0b00f814184801803068007800950010b01b86000c8500d02c403603860303042d091070040810340f0b07015800c2452350b400440c030002c5440180c0341c0c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 11458442 1250 11457192 11457223
    0x109090b0a0510030507020c01051303230307080309060c04210212010608010b090a020c06010605180303040603090b06040506090a0207020409050105010b040e01060503090a11010215040606091104080c090403020a0b0702 96
    0x5034001004540601c100030504044056194091010378002044407039410920324221142c1e0308101c0050746103810120044462600c00802c10cc2d481900303111403600305410784040f034101810709000720b81441440030700e01e01c0311484561070b2007956a014004940e4200f03290080107da42c030f07a202c0a018040c1a4101e5000d030312404086445507050b44203c5a006408202401c196402e01008450f194040d00060650a03402e80f00b0342820f40d0300f4401800107000c0e680b00010400004c0c58601d0a4540042400e84520301c1c0404014a079160495041e5000341c401d100103985524510000c0c00402c41c4010250003980b81500100d07280ca008001041960b0000004008503a030700d0344112982c0c8000c64601544d0f4000100c1030f0009441030300000404041401036944080020b003450803078103000c4400351010b50b110380081061103d14401c1c0c00c440c084141c8000d10b000d05107040c0c550303a1715100e60070b640141d00000000d42410f200b0f10030700d6030369580100046410704003800c0080d600c09000c0e8080b0070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 11459692 1250 11458442 11458453
    0xc13020306040b0904020d030e0d05030a02011b020d0804080a0903050f03030f0606030106090b0307140d050106120213050613050607030e010206070c0203060a09060e1204030b0106020307020109090b0a051003050702 94
    0x3c0a00d0229421441198001d0107045094101d1b502118441385d80f44031150040c0c0c2001c00e4800003402070000c0c011540c016400058140265903500c1040342083c6880700541d003041c2d441100c5640d1121481c0d5020b504004c55503514803807400c048641030844e510240150040309111202044044015800f540d410f031400000740e2540010820303144001c3c4981004035003400410407401d000b420155600641d58284880d06186001c60040c4039405510f024034100d9507140148440394119110100c42440c81c40114106554081e9a000300a00303802400d105000100300d812800d1034031041e141c0904800b0f080709450b8005490090074400c030080c0c40030f000d4003418000903003007030bc540700c0900c0c09500200180b4540c1c903002c10070300007440340010079079a1584034548540700e00310800c00344242507080d1100541e25450349c00d112600c6001a0041d0045420070480744001d030b82c0c003600f45426078092000004a41e42c456002680c0b240c000c1c3d000340e4001d60b2501c40001c0131074059000511402c41902643c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 11460942 1250 11459692 11459711
    0x5010513090506060d0218150f0d090501090501060807170105040807031b1410050906010b0307050d021c0912020a020306150315010803030106020709060b090108090c1302030604 78
    0x160640940d000c260340000d031480c010003074000d075604035607003000004c0e015514080c2d030119104242da0000c44466000044215020f44030304100120740e2008281c3c1d00e0b440d09110b803c000c0d8161512070210b03611040c51329000740c8001e001c000c0d44103520607030f8030100030807000c3d640d050150f8448030640b02d445c2c2c681b803d07034407080c1e0009018000c1900c29076100e242d981c508400ca540a540c036240e02082e011240d070504503000005081e070b80003400c00910540080150134400c070041419554028001c1c5156013000d80100300d030030031320001c0d82d4014006042050711a4808404030000380604640f640640003100104240c986d8140d120400250142d0341a610025405c0802d82c1e5a115484009415034040d100003074219045050015083e0300003810750b144940c00c500d04540c00d0f4000e820401f16600008010050b15404118040080540b102d040c0f01d580d2409044240ca8024610381906006070800000c54451040c01180600d40c8003e000446826644880000035001114030700e000c0d514100038a07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 11462192 1250 11460942 11460947
    0x11103070201020d0318020405070207090b030708192a0609050405040b06210601090b030d020d02120304030311071203050901020708040b0f040302030a080702030705090103080a0e01050409090606030b010501 91
    0x112006a0107800034080b4540c161000c070024151800c1c0c024203006402081b00059445004240c050b4990b0f038000e05030345041c020510202c42c685007881c0d101b40e226003000c00030f490011a88204030203510b2940c01c11031034281000d114401481a00750800b450751078070000c03428080400ba909a0304a40c0d0384c14006525503081c80200c40064401401c0b1407400c80002d003061902c1640e075089101c0c4001e4500c448541074130882e1a1070002c3c2c101d0b140117522051940c50900741046280c08040382d9200920800d064000040d4440301802c00303110040100000050078140039802006004441001c103e40d686900c0c1002082400003090792400a41003002103240700c14140260b0380d4807900000e2851800c7d180c48100131a0380d002842c0b8081ca140103020010242ea418004c82541c40e01420069549036036901c10182440c006070032851160314510018008100c0000c251441c9410a0038000b0091340420010f0300d490145900c40030400341442d2500042010680196084034030402480110380d8942005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 11463442 1250 11462192 11462197
    0x90f150c06040c1809031704050106050301020409060306051006050f0703030b0907020c041a030c0f0301060504230703020708030604090303090c0b04090f020705120304061119020606180a090c05180105011103 91
    0x10f000102c401051f0303240521070703a454640251144000042e03413641da501290a80e00142d01c010400d6540300d80410034441240102644407280c041010040d60400030064842d006980d82c51004032004260403017014007980c8a40300a610040120010b0701d031035000203580b641d905007441d00a6041044080c0c5520902084500d014001009401c40100e00e200b4000b421404941c081c0d0300d5922030340009205c0e1554070891070240315844090340c1d1001886140c60701c03181d01074039010416104120900108034445d090301c0e0030000880740402d10f07200c18102200503040d003100c00340080031724000000b41d0528090080040300c0c040b60b02071040820140061080380940d81007c0d080b500413140f84401815041c00840c3c0c010b100d6000043d0294400c400454250458040f003d81c03403503044004078540e40c0401c000d070781c40342e421100d000d950395802d9140c540d00c440103810410300030340380d6402070100450040c1c8200a0000609060a0302c3d0a110440d45032010a104090218070564101401d04201204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 11464692 1250 11463442 11463461
    0xf061d0c010c06020d110702010f0806090403050c0c1f090e040f020105070302120c01020a0801080604030e040b130e030306010e030703050d0e0d0f0b0615090f150c06040c18 76
    0x6400100349800040d2900d50040504483d0142e00b00800d0500c18203e1003042e442e20ba03441c03040b54991446100140045100312404818041540100281540c4580c074035a406170f80740c9002512403442c8280b071444c00381020385103507101060515206020b54002440c1d2840900f5583c0d036000184d4a00701d404503802b05440c00341c0300002464030000554000c000030280c2500c01d10459404c10708102d40e03c007254014604011040c0d40014420503400d84c401110350142c200036010b4031440c2081d50303000e130218800c0c4024501407612030741140500d41c1d4001c00154640584c500038480b40714204251612603108840050100703074160900c54a5040014600080d01c3c0e001008282c3c90704d8a480030750b01c00c643c40150b80e60011440c4200300004080d00c0340c1f982a94407600c1c105600e81010006c002201c1402000c0108080d01488440f0855031021001420218203a407140c0d80c801810079030301440e01c2100c420315038600c07824050200308402c1c0c6a02504441c152510048140034a614a07000d0f60603061 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 11465942 1250 11464692 11464751
    0x20610050607050c060703110703050a020a0b0306010804030e1207060503091204081005040203011824020c07050402070c030b130606050102060f180f0f0705010801080a0206120c040b04030f06 84
    0x3060030060b017030100082050354068104041c1c210248a9060f24050280d04202ca0641001c03902e10110b04203020400041c103c40e010a074214507050000900b8500c000340054100042d803140d14a0700e841e1444100d100c7c80702032090f174413010380700c4d0b0300a40144e000b0b0700d03105081d02c55004284100c49100e0309950580e24a5006404000510400c81024120142042ea0b041d503036070014002c500401031500340b401d031151846000f8404c0320015080c0c00f024120204009074010000002d5000011620009607071044034016190165414014400b81380e0390030081034441c43c4001c1c020718103019000883c0c414403640341480101d881c1c070012600c40f2404c0e01c1d10fa074035044001c0440c0d00881c2c604841c0c10300e24140012943c1d40c507a404c070303100d00c0c1025045003040303e5003110b11700b071003070356031180c04507014011203001400801c02c5540884d00724807910610f900f15010180210b0903410741c00080b10001d015000d643c0b5200c4ea141d08000b482481c00c0c0360100c0750030f45003520030403107a0705002035015880c6030b14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 11467192 1250 11465942 11465953
    0x1116050a06050309031303030815030c0108011502282001050909040302100c090503010c08010503030708030603100e01020d05010501030902090109050c090306150a0501020a08030109020f040306050702061005060705 94
    0x1c0030703111a000a412250a40000c0c4108100e050303494440b44002c40c061f59075040e890404028040079080395041c4070f0b009803c1100c00900c180d80100090703045420b202100c01c080c000400049080c81c000343c081c1c04942212407550f80c2102e5281407003803002801501c0a03241145090f913909400854501400e01003102403003141c4c068a0208010b6a00c20300034016100400c800701103404c1101e0b03110441a001c210b000105102c182400d226001d121a1170342002c00081d4103040001c0d54034060484000c010420000000c0d42a440903c50b032084129112310511030a1282c954480c041d41090750b0507031003280b82c00000103280d84607004030350f1100c0c0c014105090a909050101004d0b1100512941d81074004004055264408100e40782c81041d401c6500f01c12185d58000304031a40171587d000d1411940030f5441100412000707401c690440d02e07070030401a50749220444c0041d5038055644060805840d20041050103500454543d200e10481c90300120100d40352002c02c800741c000c0b84c40151269008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 11468442 1250 11467192 11467199
    0x601030c02030a140d06030206031003060e0c1f02120406090e060d1a150a080102040305010b030a08040e090c13020c01060603020a1710050306130b07020a02090606130b0301061116050a 81
    0x1c60b000781101698044041051b507240d40100d040e0713601c10f4949075010000101c013001030048600c200700c1d0181d41c54004d003860007541e800003511203c5100d080d02d403a80d80c10583c01c10140c0200070015965003801d02841d155581d03444050485005072044501545044000480c3d6146c60518040090b074131283c0c082d6440c40000114414120082c140c88403036851a021a0341581c4010501c4000d102543c0096940c9085103031031400d449020520600035031141c00c7c001d000036030a20a40f400c0e40c40d00c582c80b1966640f04110300c1d240c104a050480d4014036003201100850300c403500180000c44a160090215a5480c00d00f00e089205400c0b68a0000d14240d4000c0302d0f003012040000e4001c8100001d4038101d0341c5550000341000000d4400303d101550191016080012a1502640c05142030000c1c01e45c007109600407520620000b008a449150000345c0e201a944103090080c0c003501d483e00d8200d807203603190314024066005465203c5030a1141c4200300210740403298000c82a5200948868140c070314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 11469692 1250 11468442 11468477
    0x909060925180e0102030c040801060b0406050910030605090a0204030b150102280606060c0b07030b06030601030c020f1608070509010f0504051902070305040e0603010c021c0201091a0601030c02030a 87
    0x2601c0c46102eaa1140403541c541803003400614003442030b011090b035449240102c11401c50340203a201d400d00007800c1c8410070070036402c030382a02c11001c001e640c440750341800c8070403c030010011a00020380c410b0340d001c20305c61400c80580c007a2095a10030148030701c8c1d503141c4480c03002112030107107181801644451000b14440d0f41d070740280d9400c00900d60300781d00380301403981c2c800042d64490b40040c1c0001318040782c8a018810201c1103250000e003a070a00300030b103074410008140c0c00e120051920f81403640721000e43c241c1074801c20481a81c0c144007810303100202c40708800b9851244291182e40140c0c843d03000040b80314641004001d041795014810306401c146440140700c081c0000a018541802d0300d070b150a49103c00714001007004034880c0d0307200c583c4c9034113115154090781000340020313010360703d410303621803046400260025000400048004103c50360500403800340081e61002042c40f002011455a0600743c460f056000751000d0f00c1c00d02100e5983c3c40c080703030742c1e0040c19140c20000b1135080c0d480001c3c0c1d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 11470942 1250 11469692 11469719
    0xf01111e01060513050406110a0207030201081902070c030203060105010e0f0904020d02030f100f090f020103050c0412080c010f020702010f0507021504080309010207091a040f06050909060925 84
    0x40c034000401c116035a500013907102d6600c0c64030100d605840b50200410000644520011555800102400e0a0601c54020355174055404024107100c0c1c4000400d52442c04030b0f030348200c00780c40c411055654140c14035001070300c10101e100403402480b404001003036940c080c03020780419a0b00500100341c4402c10030100480b03048060004d980214940d0814005a1014004c40300001c42000045c21040025003c0d4011503c141b014a44441d00e4142450001110003003070329501902480c01044644a4a0249440c2e200b40d500501e0519604150310082096200180410402032130080191480700c80805c0140d00c54102d000f0f0001d00e09881c102d00f08d0380103002901c41140007a0054420131a0340400c20f01e542d01c81d800c9940540c0c030105800669603810071122000e400d046030180300e85648254986c02444504200521560315020700035035190859001e8801048014450755003801c2443d20b103511080d060320046218000d00c4442100014649120794804104c03005440740c861030329040c01140c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 11472192 1250 11470942 11470993
    0x7020402040305030c0601060806030606010815010e06040f08100510180b0303040306060e07090303020d0509010201020705031201031e030c02010302030711072d08060103020402130f060503060f0111 87
    0x40d400e01012001c0340b0100b01403c0c43e40ca03400000c00003941486400b07002c5940003400c02d40f01764001c1c0700308052070340d024000f84d0b084840010040001c2401500580700d04000307030703080d54104a022800050f4001001400e8044a03800019250091383d4401c540003643d40807250052202e0b00368508025032840c000c03140425040c12840000d5601420b00080e081d984250320030740c1d00e103840e90800d02a140c0b002c0d4000b900030205040030620103156070390294664500389a6407041c40f002065618259000790111210030364403a003581c0da20000f10314840301401c420700080d1403281c008200040e4030200c0060500d55030741c064443e200404080e50046002e1350000f80a20700308003042d071802c034400d10104000c1c00601754544040c21034016040003644c04040c1c04041c564419002107080141c3c42021940301c1c19660162409681d8100c0717404e016540034229072140400d0300755200300152056014018500a0404540d81e469001c0703a427004465803080e0400c40d40407504503188884a03c0100c028803880c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 11473442 1250 11472192 11472199
    0xa0e0102180904020a0e0901050a06080a0209061002030705011103070305010f06050706090204060e04050a120e01080408070804030506070201020d180809040902030c031504060e0a050607030203040302010209100302090103060f12080702 103
    0xc20341b80c0010701c41c050f505940e0f000403691614103102990800707006a03805051080000c0070103d100e600050200000074190340e00a00a14135400c1503a4401d108030368545800c540240214800c030052595140c0c8200d510b0000281f620b0000305441c4030700c440c02411a2a569115418100c0e22f03141c060040c2034041c0200d03400b5664190018a594070001c103544240e00500c0a000c01c121213007800301c1c83c90b80c12082c40041201d00801b007101d03aa00442c0745500203030840d03042c2d61212540d00c2c0c044540d10507500050079501c900c030200242250305400505440810000600101c100800446035030000e0160040882409000c4d0962a00701030384011525400203048844015109002c60b040114400805015292071000c02c0705001c9a4001c2c80c210501b000000d084040b00c607140c0c00d40300d00c1c02400c00c0e0304164001010405040c0300350155210a000100545080c01c0341d01e06c00b0b4001e511240f025400700b0304202c1d001900802c203854400440d01d00c0010350002d40b2040d9101d454580c414841280e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 11474692 1250 11473442 11473459
    0x3040605060d0f050312070503010f03061a04020c0609070506040303140c0109080a030b091e070c0302101401081b0604120302070801090804170c0f130e060703050a0e010218090402 79
    0x101c0c007502401109203008134050f5984e0106041c1e00000124020503031170611100300010084030032800501c00859801040004603480103a260300c00000c44c010895610600100311481c03421030104806014481e24800c40d04001da0b0b500c288070180c0658803016003c11550000100c3c080c0059004015071064400001544001641e5400b0241c001c10b210000080d5603201c4814103041003404c143e000403442c400c800d007240e410711580c0c5500d000203050200700143e0800c10410980204a2207140f04403100c2d060104580341103071015130220034414840719100360340c4d0b80f845000c2c0c03040d216030580e0805051070b8541400c0142d80304900a684804030300314440e0b100000355a000a1146802c0c01e480303400c10550351454030301e10141c440080e1502c000c1c5504024900d031060f65418105000c038110030713581454948440011f400041c800c01001e0800350290341c0400441603030652289100e08102c200c1000041d00300e51081d0300301d00880e082c03402c804c10400d40b0300b8414540b0080e019031040c4014403024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 11475942 1250 11474692 11474719
    0x906040201030c18090c03200313020105070f03080402040c080403090b0a1107090509150c0703030506040216050f01050702070521010e120901031116060c0e04020c070e010e04080304060506 83
    0x403003041351079000c103006660392082034915990600451400700e40ea9161040880e1540d0b210402e2480041c1c0600c3c100c90225082c4000c6900aa0a40b004076800541c02c01d1402c0316410060440001110300300c0c862868a0711003c110b900078040140150303011383d184200d4900784040a0701c180c1c402c184039014001e152080030590401040248090001c19102140a06066100740d04e026012007503440000d00c00c00810072154041030131766074510740510b008a10340e1036010100740248030381c0d10012408001c5616210601c6800215411820000c1008104540c1d0391502242ca170240c070b00038558050000812120038003061003102080000520000a8001043c2070142c074110300c18003481002840032480e0a155030f09849800900100b520081e403500741c00042120300e0503070180c1e008000070342d5400084007161180d4280b0710f919001030811550b601d503648800d80d403000148208410844010008255110700c0d0300307028021a4051090760841d10b0360303503c01c406024003c00e000c1d04424242d4590 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 11477192 1250 11475942 11475977
    0x102010f0603031d0301050c0d020a050403140102090f15040e0c0408010606020a0b010b12040320060c071502070206030610032c060906090d11010902060c070501080f0906040201030c 80
    0x8001c501c2a00c400f5500d080b00e8113080b000c005000b030300c14400d914102c10017600b400c908080b0764817403022280c016034902241d01c0c141c501d401a40c10252030130a40343e00302000d40328154004c100c20001129849005282c0c001000303000c0d6901001d0035803d100c1844100451400050107a81203030100c2240e034200340e101d080d91821900b55a02c510010b9002c414004140b0845402c01d50242c4010402e1510f455114203044918580c054002000c01422800c21a50134907000013410184e030003803060b03070701c40e0400b5400100325800854040d12440c00d101c4c100080000d10b4800c8a0a4a070b014140a09640e680000c0002c1200080404400e258460040c0d18001504200e440112022030540032100c4003c6507100d46090001002c0d20401e91014007803003c102c00009007503e0000355864111441e4006103811400740c050200000d4000801058058510034041006000e0790300a99982040350364131114002c070b03868243d0b00342c1540d4009001240155200e5041281d1420950800740c5c00d845010001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 11478442 1250 11477192 11477201
    0x7080f070506060112020304050d2d03061806031502090604090e0a060605040b010e04020a05130b09010807081306020d0b0303130306050106090302031203090705030304081c050c0606010e0102010f 86
    0x1100c1c5034001c10104020f96800403484015413000b03a50440c11494980e03665542e13016403054800611070040c2181790b11400022000b03500c0000071410520702400b80d00302a02034541405040400b40582d544281000070601c50801100d801c00030302200c07600c80b81c1582e4025800320b2100c070381003001000041131315440e0340202d00740c4000600080c9003859150402504403001500024810f60402601144580e40000d0703a84000000320340041c0e5030078020100362030034841c0c04019058402c1c00341000841c1080f2201403d511442070700e6145150b9600e03502251041d4044a40c00f07240d444200b0f0505c0410400c2c0d000e0030001d08580000581310018400203450760f040707081c0e000d052007000702c0c003402045280d000340d40c0100b03910304044140904540c006500c03621185c5560590034400310029118440c2008160010702c001790a481e60b40d030721030003681d131260b10b00d4001d41c450701d40314003d03807000d42d1080c41103032060301d840d10280c030840c8c0700c000044403050220201380341103640381e501d01c0d031407000306108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 11479692 1250 11478442 11478457
    0x30603050312100b040305030a0807020c0a080a060509030a0903110307120b09010b0f031203041a040c0f050303040b0a030e0c041802010e0603070c0f0305070501050f0708090a020f0607080f 83
    0x42c00301c0c5103014840100e961800d900049044402804100001071b00003007940e0800c581410b10803006ea0750f40104916090910441c10b902c5104200b000500c3c00300852400d0304e03a40100d030248510340e142d22949a992248294000c00101c054201700b001c50589440c80001d181c0c0101602c5016545601014101d07240960a03554443d0500074010380c40c0003445201010801610360103002c1105100117078075958400500500710ac0000300082c2000f180020110149614100d20403641c101401d240070700f015039000d114103510101001141602e80082070710100c41c2c03013681c25450821402803c40c0600f040e0350b50b030040ca10442c10142039541d5107000f00c5421402080c0c0b07007002700c4e0690000400c6a01c0801c038040c0580410024004640d43c804010b10281d50071038400416000e032407608032524818031001a00d50b52800080c000b00d003035608405802140c0f9a5210030080d100c1d1407070b454443d0001c940083d07000030f440d0420010303070602d80007400c20715000301111030400c101c209103400d02e45d10881 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 11480942 1250 11479692 11479717
    0x50607080d14180109030503010b07050f06010602010b011106010302030303010909060e0604060c0e060405090a0216050303040c03061425050409150f3809041d0601050415050f010306030503 83
    0x4110402c80303074140c2001010f41c0034001740034607501c1d0b0700c01811034403040c052040100400586d10060003001c012200412445404440315581e445500900a212501d1101e00040b05812041085140000c40794180c94001307010754556440c0045540041c40084411120300ea00d5109413298042e00344070341d601c0341d405003c0101e00c00110328802807c400d00045a60720840040c00b060103262107690360640c0c4800560030040e80c41d51103411011074809905402441d5100010400080003c95100e500840e0b101c1d800500620345504204c0b05a0001126810000314045d500e030345128492076002051101c55082c1b0a19190f214072100c000c2d030300354004001c10b00c1071030081007100d0080e1800410043c01030040103c0311070759044400c0500c0f032450040c40d81c41c410031191825694820402c45480710b4009104005100b01500c0b4900b2400e00c007000780250f805407000005580c00c0c507000710001e00030100c440220031400c10007004004545604520304060340d6003070100000ea402c02c000c00380c14a02c0b2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 11482192 1250 11480942 11480981
    0x309050909210901110307061410030b040f020a05100c120f0c0602030a0605040212090d02010c0504050103050c070501050103140606010309020a09020a0c0213020d05061009050607080d 81
    0x40180030505401601210040d84010880ca205541d031141410030303080140001d942d1420303c88012211400e8a41c000e0300c00e8080019031400300205070b44680c0c032100302d400b4030707108030390351254028012142c0e407001411002494000800041e07148441c031040a1000305a1103000d522840031900c2e84100006410101e038881d203101080c004007a800c0d060600061400c60421109004c000304032411050004110b180c021020498600480d0041c0002d4040030b0021900c0b2894000c10051400c1d080d52000c14a00821034600800e51040c05000c1414107503460f864174044c41e0400440003080000d107126007869043c800880080c0080c000c06000350302445034030403503c100890b054180301c00900b01d50306042c03900185100607201d1000503c200d07072103c00c0050311410510010b40b10fa00d140b02c0000c0d844801c528140d03403400030381d90203072120303e1030408100306a80e1040d05120f81040d40c0821400460f2101c4400c101624180004048042c890101142482660a01e03c0300740e404a1580c20302c0c80511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 11483442 1250 11482192 11482199
    0x303090d030b030606061b0304080a0303091a061c0c03021018060801050907030b01020a020d03030c020c0105130311030313030f0314071104020a02030c03070602030a0e0304031502090f0d0309 84
    0x2500800c11800b0702100640307002d00b40240050a203100d20010220b50812000d4040c0c44001e0500c10344005010b4081a02c603190f2542c078005009001110341201d854134001c40303581c65050f80c610941c0c400e0754083c089191001038643c6400c5102d8500104880151800380c0102c011384a0601441c503559054450483c02207040c00c040c0078144258004000b008548401000299255020076802080034100000c0076909480100d041c0b10241001070742041e034010f5a00d04141d0305074400c010b01d0216900b0b42c2c421342045001100c0d03d00c959042e00910040c0e0090900128041c010304129108000f0708481c50f2600e0903880e4400300381c056000b91540c08401251406041d0840190513032050f100d400a80341c141aa03036145500b414501d10240956070206521a07400d00800881d02800111021641c07165540c0c5014030203548122070303610020f410701540c0c0905030000401e03202526400000c403d4000480d034006002074010721040f6620810b440d0003111940c4803032034040599400b0740d8592018504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 11484692 1250 11483442 11483447
    0xc090207060c0807020c010e040e03220b04050105071b0f0305060604050c030f0f0619180b012d0e0a08030702030d0503090a03050306030102070503040816090c052a0303090d 76
    0x410402d1020300020000f007014481c0d000c42c00c4260f151090812010300c54465000c038000300307040170202d001031000003407034904141da032100404108005240d13100f180380c0351a000c03c414003031440307202d003c030340203000510010308030081451001d501d0b0350340d850525a45202091344000030740d10950380c0b90810300501c100c5003054081c01e54000303440e43d4824507500384801c1c1000005001040c1034034005070308010483c00d03612095210107641c0080d4011000d107031a112050112012444400700103450070305042041d50089aa01420224a0304d200c4030310302c406182c444050a050003403408205007801c034401c0720341d6100c2d0008050443d07a0300850b110302302441454a0140d00f410410144030742407042103541e8030300050003240c5513858941281c036034849401103406801020f2004085010200d0049640040000c000c0ea40403040110710380c440307030380ba44400d0441d07508446000005000b0040248424804805440359003009280343e6481d016a803815400c0d5001581c5270303030b01070b0040c09810350740c81d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 11485942 1250 11484692 11484701
    0x60a09061106010e060409031202190905030a03080118020715060501020d031109040e0c030105010e061f05030f0402031c03020a090803040b03151c08040303110c2b0c09020706 77
    0x741100410320307941024842c070155030004104520503922006d084003018490740d0008540c14040c0c1e004e41d141c400501000300b0a11403035403204001924400700003114500002c9000c02c407900b688952000da402c0100689c4c0101107a8402d80c2c0b016002c01c08400040c140094091402c51301030800070381cbd03900b000002030804d06100e08440c00c060030300b4011650413139040300b29202060116000240c1c3d2000b024880c1c00c0ca80103002150b8194603290002400b0700c0350039441807050000303c5d608500c0c2011856003540d104000191080003072010300004149505854200390424001030440e02000518080100c1411900604200181d008a4584502604400c0510250a81d54042c50034581440c000301507034040205030400c0502e5029a280540d25040a0f8000c0451940c404ca04070359150f0820721196402840201d00290308613174048806080480d400b900c800f001402141d10b4000710307003c1c110f103440e0a800f040c402422603614200040050010b20000c2c0280341c40944c541c035540c00c1030402c44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 11487192 1250 11485942 11485967
    0x30801060206090d050d060504020c01020a0e1c0303050403090801051005040506010918050c04080607050a1205072304080d0e03010606030207050a0b09030409020301120c0501030b030706050304050c060a0906 91
    0x150300c040c092010fa014007007280310b05250103103807003078807400d480c0c01c030b0b5000e008030307034000c1e50850300c0041d81000114041d001020b607000d10307485529140c1214400e1015481c00b03101580c00004c58841a0700000340305e508110340090080c03511450907030300c56032030700c2c01c50f801a207504001d1403d056080100b801d10f4020300d9440b0509081c5400820324100d60084c90318003141340c2e113203503550321000666915840c00980b4060403a40c4220350701440c050101401c554000400171000c68141c03050708040c0c0006006031132080c0102c1d910007501420248103003c094a01401c440c041000c240000300359682c0410666030440070f04e1392501c100114400c10b140c2100d109070000010180100039040100c4c1e00061095038660b8004424903030307590764009441c21401203400c800c100030700000001458481c0207000886460042c40400149075a60006604a03441e900d04950550071000003000f80b20301810103181d20500950540300c04045400c0042c401d580b040c5035842c045504800306004259010798000700c00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 11488442 1250 11487192 11487197
    0x40b07020606130e03040b160b150604030308090114100e16020c01050d0f09080702040b040501080c0609010e0901120c0605090a2705190e07030809010305040c030c0902040303080106 80
    0x160500b04003003080c00d00c42c50000c54240f9211800b02c8155a81082210b00501c2c3c0080901c0d20b91200f607484559a80c3c4422050701c0030289040400c0d0309041030408581c0702c03030300208072516081c5960342c00e070303103903d401003000c0711342d541e82c1554803501035001e40281d10030351402c0c44c0c0000060034600b2103581890080c110300d103c045d88840f0a24640d0f00041d03c10801a000d0802585030ed032402e503030310040c092519849030000d003010900010400c0b03c4d0003a12185108680c2888110aa0b400f48001c07140b013441054220391061020080340d0070014001c200110062400d10b40010242c000706602da0300a0b8490601c881e0118911000d103c2d00103c607002030b0086250081ca480751890002d65600700900441040d041c0548081c918054025070300c8001010812041c010b9280c0286d03071050340f45445d102800540e0620b030070180000d07400300f00f0909481c2d01013003150401c10800011001000b004104496022410802002040514100d0f0000703080200d405647c032410352400812120046e0b2100c401d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 11489692 1250 11488442 11488453
    0xf05031504080d0510080106060f0305070f0c0b0c0c0303010803070201110706170612010c0c050c01020109080403060b03030c070909050d0c02062209020f07021f170702030d0e0105040b0702 83
    0x5140c142c101d9034290100c01001c1220740383c0c05815812181d6036489150250702e0f1070b800064094200500b0403c0800986040150341d035031020613144014140c402d58001645d00e0400000074940005040c0c108d084204000c0c14039030240e0310a0b107558820b0b045818a540041003020456a0204040f0207900e10103002d0030000d031401d0b03009420700000001c01065140480c00140c0151100850303401039808140082c01210349142c00038100b00c031501c03806e40d201e020300281c01040c0e500501510794540d510291452402e86035403038610080c02c82c10501e903414041008421070710031003080114080e00c2c20307410009111000f4a00706182c544200f201009104880e10044050303500c940640c0c01c05401070f01d8641c0c45450002010504184681100344941d10100d662101c10710380d04042c004040c401e03100321441c00d0b4040384007200c4510f0103841400040503180d1814080c010310400b15048000d5004480c10201022070500645404100d00380580e9594000c01060020850700b264001d100ca002905 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 11490942 1250 11489692 11489701
    0x2040f0608030a0f0e041a0109060f09060509060403051606080f01060806090907051005040509090c0f0607050309040207030e0405060405070f050a0c0503040305060106171317130f050315 82
    0x180c59014035007100007404030b0144c485140c2805a0b07100301e18038a00401c100800e04001182803200103400007600e0020b0254680440d03c80e000e0b400600e20f2100c2d0b900c4c1c07003110f10300c2c3c144111910380c41404501d811044c14000000081c50800903c0590800d030080098902e040103c010b1130000300420004841050400401080350014201c035040103068660a41d580d4580b940340d49401c043d0f5002580210042c0c4c11294500e038041701800543c0d808440041e40c54031003040380c40c0da50262200e8240c1c031261f031851802062416400901c0d1040c8a24242c03414495043c0010341241c2001e403040d0b0108100c0f001501e010715042c40380c40c0d0f02141c115010452828001070082085140010140034010005a10b0782d031213001c3c032642444203601c503040f070b6a20f40d100c3c5062070f00c1c0c01080c414100446e0307210840703107407058020010038441e0440f001d019180f03031030540720900803c40c1c85020a0122000700140d251003170b48404440098070741646100405071500042c145021007842e40e214038072581c9824030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 11492192 1250 11490942 11490959
    0x1502030712061208030a0e060703020301050f0102070302030d050c07090606020a06110a0c02090c04180e19051507090909120e010c020d020904032007030309060509031c02010b04090302060402040f06 87
    0x1403186404c030f04020340766950b412005d0b00900c0c0c1c20303150f08090301c145420404d49681c503070011416220140d501d070310500030b40b03001aa61200c480c04000e41c1600a640307100003052081020309002c66080b4111405595500c1c0100e003160750039040200140c00800c0c1c5041449140e015050b03652030341d501640c2c580818200d009260000340ce130024880c203a45030100b0310103023806066a029081c4800d582a4061a4000030001004801d164100c180a2410316450190a00d00000240ea4105000d054941c0c40d01d050307281e40501c002c207210280b2504100c0801e07900308900c10302d08441d11038038940446081d0444090080201b800301c2e5410049a5182c2e40c005841e48072000002030780c152182000c03038650f0329007640d60304040c213000c412017942d0b0001c100c001080042c3c0502101d000380c94010089864074022100f602c0340b030f45c1d0700703030554850501c801c151104103960000741d24480c4000505120020f00081c140c1e00398100540040c0c0c40340b0705000562806115440c5d0061000508200141c80c0003104d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 11493442 1250 11492192 11492219
    0xb0f0306040f06050a0e010306060503030a1205041a010803030a050108070f090b04090602030c1206040218090604060803161b082a0904060c030f110313050a150203071206 75
    0x40c54001d680300d040350603101c001a0840805401d005100e500110b03210380307812140d101d003440290740c3c0500300b4800041a05000c000c031661900d19030b45000603181440240c201628019004860b141002140660f40306c81e0032600358080c5c40040042c580d64240990600190341c0b042c3c0211a180c0c00603c02082104180c2e000882201c0d00f010000c01c4401c00040002c004240201d1701070200f5000104000ca12941350005211040b204980903c0c1511190284402c0f4014603014002c40c10507101c508200d031401000050307020750000c01c04544541c44210450850f0001d00c4410840c001025200c82042a0030294544608102203d05949441d005d1013070b549100005014003528030b80700843d0000c1c2540f0074904c0d04e20f90080c1c0098114185440d10800902d800d000b540d000a144c9a80486402d405001d281c01218004d030040d802c5d5258900b4940b104281e10f00206e681c0d1059208a40003c0e6594200c50849100d01400588925103000c01038201e02241200c9202503141040138459400b5a403c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 11494692 1250 11493442 11493451
    0x40c030c021c02150f07110102040302030c06070602070507080619090c0308070c0f060f0305010b09130c050409090b060906030f030301090b010e03030d0e0706030b090a0207060207080a090305070b0f03 88
    0xc2c003500418009a05040b001c550100300740e0314850801114404031500c044c040c89003951400500401c0d070343c0d090700302d02441c00001d40c183c01c14580b2145520381000900300031400f40c0001403030000e10341d0f1107529140096014a41c2c5400c100c0810280004002c25043c0c0b821401005010450182e0b0f03c1002c400394a000080016001265103070030310607043d40400151003282002104641c40d48006440c41510500100000c0e007001c00110741c0c0460201600e000e500040c0c91701c50300c1042298800003400b00109900e007001403d10001504030524014044500d020729040c007107d061060900c480088002d2086d070190b40300c40010b183c2c50100204490448030a0071001500d030b0b01ca00c00407110190209007070f0f549440042001d08509002d03503c100411307130701d190445100030360f1220240c0565a02c2c01c2e41660080001d0002541c071a031a8004103d02c91049034010302c3e01032243d440e050107401040030b2100240c11540d050003046030401205015110400c0c810781001440301410b201b6100080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 11495942 1250 11494692 11494723
    0xe030c03060402041a0a0f050307171e1c030e060105010201050105030a060e07030f0302060a0c0e010c060207060204091104060801080a02061603020a060606030b01020c0406050d0209070903150b040c030c02 90
    0x11203810fa14016000425031045c0003030224041590314035000c44142e16500030548030b4020352030300007628000d84aa403200d0032030307410140640040f4071400092126000c200c01c0034902440c20001d00300c2d104145c0e00600e1030441e841c00143d200c003d100161800c60141c001505580c9818010300c00c0c0d0381c001840c08403181d800040490b0350040810710b107080850680c8024000f0301000d030460201030f00800c0c81c034400e040303602c410008080031000883c1c1941441c804103021034882c4c82c0c42004501c0c160002c010b500d0140401619055540312132804440e034420440b805240c0108050200c1da6100e00d00e1401010607000401c01c003405074001403403030f2090075a000f80801ca4109070908240c0207000f03001e41250085070030480280d07648400b901801c6d4400c031faa801806031001c00049440c00f44141c50603a0409072105e1940a215401d100780305c10007600b21820301841100c0000000d14030380c10b18242041601021513416040302c180410340e238203820203106050408400303600c0243d0010b20104034507080e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 11497192 1250 11495942 11495951
    0x10b0304060b09010e040605060108100b07080c0a14060f100b0c010b0904050106050a0501020303090706080c0d02040303020a0308012301030507050705150f010b030405060a02070c05040e0c010e030c0306040204 92
    0x61074048000c002e6802c0198100743d42070000541022401c2001c3e201d18003400d000e00031603450b0700045400ca0b004442c12012183d81000c2800340550850140490502c10109a813400b600512120310b041c00f01c9100320b03840480303120601140c0c5024060f035500041c0da9031345900e050a040b103581e90004100e0040e8808401d0125940c6280d5409400586060030003803c000c00b2400c0c01d0404074068011707170007158000c2214541c0080c02d0f502c00003c40344200144000b402007141880c404540380c09001e0000324000d8002d010315401c0700c100d0300c0140000d5210350024502c4030b15624024207003100503408861140080c00042c070090700113210080c01030b0002d10b4001801c0d647e10304180ea6a0180c1000036005100721494100090100280c4178012102c00d190200c807607a8a1403ea4114401102c00078803941105001c5020101141c000c1e0030020f214402413200079445101242c11685030006005007075101604283c881c3d40c105800380601c4000350701900034030301c403200031039038404000c1c0c0024015a0b07078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 11498442 1250 11497192 11497201
    0x3060e1c0f0c1b12141608100518070b0301030303050105040207030c11060d0207050102070c05040c09090902010905090712050106050a091a0f03040f0506072d030608010e01020a09050a0608010b03 86
    0x390003500582013801400b00c05415030308100004202c400c203d071125109594844a00b0144640010b04581e0000c00814400440890b20406400080c00c0c600d016030038090307500d090040500070b810140041d256210388940c51410014241c0300c0683c0710741e00036032041203400c0103c3d41c40340d015944142c000d40d80320ba844500502252483c42003110702c102c8180301082d1801004010340080a03030364022680c0201c1c903603c4104020454840040c2140400c4a24030308200c10700365504800b0b00b0074014105212807980d01e41c00328608081c1121000b001883c90704c02c84100e00d1452180f140540712031302e003003410500a02c1d4040c00f030740b05034082c0ba4421104202c205510020180071580000f41e9000c49944034289803420b90040001c842088840740540700004502c28030843d140310803900d0b040090606052044a00e2603103280b40102142010b0300c42d03001161401c003d00803411116506030005913900c1d81c841d0010946070389a00060322450f10322508104030381c2d100c0c2a09042d20328594001e90340c1c2d1074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 11499692 1250 11498442 11498483
    0x2010507050f0607090311030303062107090c030902011806050406180b0a09032603040803060301140906010510090e0121060905030405180601091401020703060e1c0f0c 74
    0x10310400d07268503880349030708010300321740e00405190460f80309500f115030070141c0e4410580c49000440b0b0840c0c00020701c8851820030b2100740000c405551a80083d10b80701600c50581e04141c03000c82c0c1d1000d002ca42c84025600440d640110040241122465180103103400c1203401000c61003140700c2d40c0100214403181c1204d0fa520959218000e00000001c284da075038404030301600e00c0d201403100740d9100b01044040d2254803c40c0fa100ca201c1880340d40c48625603078a43c0e5559425400203022113030150368880c607415a040755200c030203008150640007800380b07614103010000003d2824842504201d03403502d00304081205547e100d4191054407001c0d041410024944090f1081c40800142510341000e03500001c1c0600031004009a070400d803003001c1c81d00300545081580c01c070180d641d41d001503080d01c02004400940040440c0303034141441515452903403525004144c0d842c4501c0308086420880c0d4027601680340c00d407140f101c9016402c1012000000c3c0c400039105410704100504880548107403d80c4070b60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 11500942 1250 11499692 11499703
    0xa02070503030d060806010e07021002032215060603020a02060f040305090612150d020f0904030306050607030206060f010e090106080601140409020304060e01050112020607060207020414040501051608040201050705 94
    0x440981207a40f80c00c1004860000790140740b180f14114010080041014980640384030b102c0c031600c0d00140b00c5600850001d0009600041085c2c8689082982400c0207403212180c203518035000d4901c900e90303071600703a130407108030b0b8403d6110f0420b040c030400c1215500f64000c14a50b500402400c14014265668102910b0900c030310100c0301d61218000078000c8821207030403940350180c1500343e4285100741c000b1080c8882001c00c080040d604c8450701908405a18100030380a40c4a442441c0220b646070341c901c003040094110394011000341c9c0001f8100081403c0600341d03041940424a0450700d9549098082060300380103000300d1b4100300a010000c1c070b041c0d000d10102490090610fa03403590366542e4400000081d0803d983c2120200d007400b20400403000140030b8031341602c00d101c422030112159035007082665480070718101c8080c0d4080c00060090396540c80307800d610500344840c2100c05e190918220742103590042900d15a54220103c105603903500c003007030039170207542030a000c0e03034490007410290b1400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 11502192 1250 11500942 11500949
    0x50609150a080403030608070f0b03064501050a050d060e0303040f03120c0503060105090f06030103050c090a050c0304020411070615150306050906010c03111015090b0d0303020a0207 80
    0x14140010005040c40d44404640c3c4524043c1c2d4080001580f41e10b03589841d40440d104510400c0511b00c4240454900d0078015508080c000b40f05103120a40e065130a42c400b854100048500c1400c5420304400f1303017001807400e04c51150f406284442e581018000b882c02c0c3d840380074250141844645d04810480580c0c0110207164141d8110f03070301c3e441d0a20b400d600c42c0c04c0890003200042e0707a0301c148441d003030880d0044106d0300c0140d40b03845085603500030044505810141100b076101c40ca001d040c60f101d44884004501841c014030250450740800818008000030181505800a260004004198080c641580e070801d034111008950482403ca83d040c00e40103120001e01451305c7c040340c10100302008102c50040b03403c0d9408603c10500050b2064045801600c0760b5604451036000084143d84130301a911005803107424045041c02102507050301c2c000ca0244074a00d0942e80c0e501000c010000d0000c2d020003802090810b0080700c420102140d51454483c01c01020706402041c0c21008900a10035013014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 11503442 1250 11502192 11502229
    0xf040909050714010201051303030507020703140f010c02190204110403020907091e0602060f060102010e060a06140d0305090f040e0f060f06011403180c060a02030a080108010b0109050609 82
    0x2500d10600307120340c48452030b115202e0383c6240500103254550041c0038051003588403020421400f815510268040e20004001c0011800742240200001d01c003c820252101d92040c0205151401625010f00711014118010b040d9031007201030b00b8103c00e1043e80f0f680003a505640104004000b480e40d00494003a54000a501c81d0407a030800101c99401920b040440d02c0f406024a1714000401600d000000340340590001a005000007980c0c0945090b02c59400032010b2000045034400c07041c4680c1429415288200010303184c044c1001400f910401c000c60340c00c811142103605500540e00075106104840041d4001c1c508010310811503540d6074002000c2a003442c05683d05d40c04041007668075000211051100c4941e90400b0a005501c100032a000628401e48014516103d903080000c03052854001c4e079480344224484071a098a4a42c00381095120741e40095032107042c4040c0c0070341901d505800c46040c0341e01d0008501100c1e039200c01d0500840740161000c03903451054401080c5035402c070720f610540d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 11504692 1250 11503442 11503451
    0xe0406090c030b0406050a050307030f080d020c0a0c050315070804060603050303010f030c0b07080403030516170909091b1009090207030507020306090303070c02010815090c0408010f0203040807080f0409 89
    0x1c915070140c200e240b020000b00c1d403c0145c0368640f001c0104041c031501030a90907a2000701d061000600a040545207603028481d020b00b001006213000d42030781d11034407002c0300036001000c8080800106600c80d1014002c00c41c0030b007040028051141480c01c1000b82140104031480700824140540340c2d1203440a59004402c0d00e50300e42c3c480c40b41d040e40b980f40744821500c1a41c0e9180c0040e612081d8815902d40d26484a00f5510b0700c0e2954500b06c0d090b40101c0e0a600d4003003d003031125030000340390100d81c0e4030080c058a0b40c02d4031054800c04200030780030014020040b81d04001013011443d0403081d11119426021912000020300d0a00304450f0030b60703180c0194101902c001f841505154200d000703800d00a100301d04a40300c036030303804d82c00c16128002030300c110740454408440c9100560080410507840080840a00740c86042c2c600011821a41034494000240c2c4c001820701008200b8040c156108210b0a415451424240d0b030b6203810784200480644441c034086105114003401c4400c482c010401c0b45030078031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 11505942 1250 11504692 11504711
    0x2d0c010507020c01020f030403020f010c15020a02010f0b061303120507060608060612070605030106030908090301050f07030b03010903050d050702010212190b10080a0b0112020a020f0c0102030301150e040609 91
    0x1d6483c81e80708030490141c855002c10300b562510000840e0244c035409840300a075160000e0042d52150059081222025001140c829000100d0700c05072400107265400410b820014144003001c5851916105005031810020700e051140c5220060040382c0d84100020310640380c000701140c05018504000342804d041240024280f400014001d0142000300c6001502c454540300255079944644240780101c1c00502c010000704d8000e600215580303010b0f001103807a20214500180c21508210b6600d0301d094030013010301003450380c14460822080700c260001c108524040d00c0280030381c020f655811038280e440707100080071103200b074041d90721013040980002440c0c00c00c15196170150024500401829280c25510003c61410302c4084c00f0b0074410b03444909054451103210409008080702d214141b210b05105590b41d10110b1000388854035856000e08010789205000e5800d00f410303a20402d045501c117100501070480d0790b805440351401c8504010010b910940c0114018201c00d0303101c1480d00d440d000210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 11507192 1250 11505942 11505947
    0x50324151f03180b0906010803070c060806030a020d05031b03040605120612010c09030615050a1205071a0d050a020906030c0a02010e1c1b03020705121501030c15052d0c010507 77
    0x900540c0117006a903039070303a200c001040d52402200e2000d0200300742181c0800c106805000302d290003003030240a0f01d40c0440c80e600420004140e0040445031680009424a40d01e082c20350703507616004c070090256140903d4520011710782d0003440b03145802003040b5400b080d02d6580301c01c0c014003e001b0b01d200a210020300e03140083c2c83c03884244010f403851401e0001c060030300b07000300d01254192040285450252403c00381d81604400718880c00303d490744a055030103d0b40c00d25010744000c0d15102d03100081e54581055001009552014207128501c0d401484031505945c0d03040141ca81c402950b040e1076442e0048003c0c01c0f805000f06a0054030503008090900300c200c040c401074211521040d40310003030140e04840c0040301071050301c10007900580044005120a2030080c40c1d00b229400c0c1d14048900911514074619003c4500307034800c9854005e052410445003040060003402c40885060541c1080c0b81444a009040709c2221040401c3e10150f0401410f846040180c0ea120600340008104524148901 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 11508442 1250 11507192 11507213
    0xc040b1201151502010924021209010204050a09020301030f11060f0301080d0e0f10081005060d140c0304030c080a0302040305061906080307050a0b070306050324151f0318 75
    0x40c0e011183d42c0d041e101d2a250b0050150038040c590200945031280c118045010680c10912100107181307408000c08000313854444542e600912400b4001a9501c7c80e0100708a0691400c0e8004440c541c014401013006c128140a000b18468105034840d85520120300050b64a103e0350303031599071106000c030010610030400034495065008a0700c6241e06108014100484001e000034003d9010181d140d4070849540b142e00c0d200d401c414001c1d800107081e615803001442c4c03500f20048180c0c880e5600c604c4aaa85944503178110340081040406c10300d1400e240e24010020340d5003450240c00840d00151080d42c0600c2641160019900107040d10ba00e8102101080200d0031101c03488005142826804078158401008480c4078036070010052010710f0031030b0b4030309004a20060421052607a5a040002c25450030310a10426019040b004001804060108d415090002e880c942c500c84078802004d206450381c2d051050700142d894642c070f00a01104404a0280080d4112603c085404150341020452030000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 11509692 1250 11508442 11508449
    0xb060c0d180e090604120302271003020301050d0807020109180b09060307230d020907080907060801030206040501030e07050a08070e060d030203090909030702030105042d02030c040b120115 83
    0x1d1400d09240d840c014038042d001c0c20b458000e45600500c012500050629025041c488010306016080140c05408510101030a21594405008888024120341b409107600208099203013811402c40d41000041540c54101081c000d0005900280050035a0701405564000308a90a541030612450207840000f4180500b0020301462821020078440d140c040303926025034114181e002c60409040c8114805585084c8a01d500689078082440c056150846214400d81d10307511092640d05100c07010328646552580301004025a42c801440107070345410031541140d509290118000d8901000b0381d00b000c07056030140b513001041e6900020f04141c0401c240b002c40c1e942c13032000000c2c0d42c2c81c0c0041c0b00080400c0400180103800c2007001d04060320741080c1903a000104035045074103060750740d4082800c40f40b094409441b0343c018503454800812611520b22107031a592982c14040c014954007080d0b4500c2014100c510486d1034054009441d102e4840e050408003d1000a01448144400c00c2680007501d02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 11510798 1106 11509692 11509727
    0x1021f09060e030d0c080a050403080105010c05011d0705040c020102030c03130302190b0a0c0513091a0402070f05070501090b0403030e0d050a05010506130e0705040b060c0d 76
    0x1000d010200303100c0704001100b4110317010213004180010401c2007400d08103420040001d0340300e410723607044460a00b000011014a440c0550152030300c2c10110b150a0f0b1800741542103038070002200021034030165070400840101040881c203078401110a01b502d14820000b003141d00410100c411390742030091040d659000601d5141c0141c580480030140c4283c5116024042c080b10f141c0b0402c1000d07205428000c2ca0302044030803805d00100a0310403000d10a41c1d0703090a00390a500c400303c195144600800031980c0e4941e92070101c1815800110503142d03841201004035955005900d510242c4d07003640010750900d40303542d0302220421840c541054108820241c000b00151b410860070a4444c0710300d0012415190002c1800600300902c40c011442030700340f6412030280d0b14003143c02e41c281c0300b0a0380d010030003403500f002103140c030f104880100c0380910549040840d80f1b64041030415030381c0e0340305 = true := by decide +kernel

theorem cover : BRFrame.Cov 11330942 11510798 := by
  have h0 := BRFrame.cov_init 11330942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11330942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 11330942 ≤ n) (h2 : n < 11510798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
