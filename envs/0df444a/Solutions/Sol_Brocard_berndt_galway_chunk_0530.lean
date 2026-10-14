-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:17:02.93064+00:00
-- url     : https://prove2.me/submissions/1d562bf6-b410-41f5-aa98-4267267bafa7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 95143885 ≤ n < 95323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 95145135 1250 95143885 95143891
    0xa020607060c0e040203060d030c05070909050d020d09060504030b070c06060611010515010212070804320a030b011a040906060309020127030f0510060602030c10140103080306010c0b040b 82
    0x203111410946001030a02c011703440202c4a9691000e0303031114810000e40520300c0c905509001d8021929899108c0c5c89103402c44105000664084d44140140044164104124035449405d864a0b070b40303462910314042c0040c0590f001c002c1030803003000000340420781715002840020303803c0041072044d1680c42c84040e2a4418821202140d03508104c00a8014034450703003d0070500c6d6041c0d000b41302c00950240c840382190409042207850040800c0002a40030510801c40c00c0d488840e80030410310b2050a05503c4180040300da05400b0349417110080002c95689000c890440300c2c0c1c961880e120311144013840300301e07120315001480c5291500c1c002055056040d446804064401c0c3c8840200201a02043c4045170100043c115845195001032001480d415403001e4100e226004684010455015032030a641058004030b0042c0d00104001030015010000815071100e122000c103c800250320484080c10b80501024048510000c00f2500d2640310350340c042c801c00d421040000c06410241b4255200c15404e17 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 95146385 1250 95145135 95145137
    0xe04090c0b030a151211030a080c061009090506010e070c140a0b090619020f0c0607111e120a05040305060a09060c0504060509240c070914060a12050a020607060c 71
    0x4041c0f070303442c40c540000445099507900c220160562242c6c2d038030034001030b440404654050184400d12000903102c50007070036605000e80060141c600e0041010000016182c1c8006880c2d4100b4800002042c4c020030030354159824000314028a07900c847d000d60f40300d0304040340140f84540f4000080c4607004045405030304d092003030888010b69100c0c02022640d441c020390300404c1e204017417255144004100ea00510107142d003004600e080c2140350030341c903082403011154000840e24402e485103140c00c05001e01e0300c00300f0340349590904050260383c0781550341e8408084810f001c0c5002500d040c0650103402901d004583c060100c4000c2d103440700d4164041c2c20320302421035104c1d0070880c6c0007260380e01030803d540603104160b850b80d06140602c0c04006e0407988282c07810103100800701010140003d481c006180b030110003401010454a0300801c0c02c102c60b050004a00d08a5400301840b510342d843d03007a20011240b003101700c2035450341142400f0b8145001190029070080c0d00003090f0b420020103801c030f40141401c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 95147635 1250 95146385 95146391
    0x405030601061e0e040b09010303020309040e070f060810090501150905010503011d0a090503030a0903020f010b1807020c030115090b0108060f060c0f10060e01170304060e04090c0b030a 81
    0x281d0b410507520a901240038160b0419820f0f0400151880b45150350441840108081600f2290340f003c280c10020a0700301b640140c200241c4451a8200b6001c0d0b000f8004040009010b0586030005085823100c0d04e000795000c01c460384001c07481c00510307521940050a038401c010000da580da04030301c0c60303003501440c25a0003060307809030300103401d40c01303002601c2c102d5422840c000e8000b0078142c375004060b5070050440c0740c0781d5510500700340450801c20140d0300c00e0710392020000341c1c2c18041c20043d103030044010300155283c1c10400031150355150100400700d1850303041c01c05105611804410307418a2500c540241d00340d8a0640309602c400240d0000008562414008020100d481001101d260b00202c0304103410440341c0c2d2015106040c55801050700002020558100c9458804100d040001d4151301141254440b0810300483d90702c0d904460043c40c4081951040d984c401c028103440c1e00461140d103051000382012528140c5440d002080c205034000b1403030754001d80314010000710b50002c2d1000800d1502e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 95148885 1250 95147635 95147639
    0x30a14210609010b120f060409050d030b01110105041a090f15060405090f0d0f0c0f0b01051203040806060f0a05121b04020a02070e07050403080403050102072d0204050903040513020405030601 84
    0x103c1c11301100c900510510300d02d03c50740d483c05000c07021400c1c05414940c01a59404000c00411010b2000c4140300c00e50f40d034082040590381c800103145d085107024040d0f040e407403d0280b10004445442540d174261440350800196941c20383c501d070a1200c080c1d20f00c0380d00c0c06012140301141801a07030180c4074640c12603041001d51100180103a9070106100995042c1c0d20103004002081e001e29001c4040111901c1c0c2ba0300c5109032641d454840031001e000441d0300c0c8841c000188290318110a003940c8140510740214109880c100416503103d0f400381580340580728070383c02e4407429100c295440c00546000386c019003100301000c0c0c1d46990b800c3c802c0d075010a5020000407184841ca45802100c04c0050355a000305900c9061020000305403a020703160809110082000000052000c0041c20040d40200f00050703c50105060210911030501c5018010f500d40e03020081c0711444085403c1c5040341c040e5000585070342d440e02141e10710710894100c41c1d07204204800004c0c1c100ca59400070415500140c05407030840c0d07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 95150135 1250 95148885 95148899
    0x50312130f020d080c01020c010207060c08070f030e032104060f050c0403080d06080706050409060803030601081303020703051605030c0303090612090c150307081008030a1421060901 80
    0x21250004041928440300c1038090324002d00f80f880c1540c01014018606040c40d030600e0308a074051003141e40c1c242d40101d02501808814031400b080e002c41030a1180403460040d20080c81d0440e00c200c42c00034140d0f903039421800b0f2801042510f008860303c1c0000100f41003209038002d001c0b02d007200c0480342c0600f0000103060008907400b0302800b0b00401d00c0300302c0c00e00d8290350b44c0c0425908036a4403015070a65940e800140c40004018020003881c0340d4950319540d0342859112409d56549803c0500075900801c10b01506036031000c81e06034444e00360740c2040e026104510381203007031104031b5002824900c5290790341810710504462141c00c5030021400c40304140c00880503d500c900079120b00f176902c00d4090040106c0c0000a0854039406054107080d10f4102240c140050f68150400b03d03890249000030007008070068001402e5a0407018482d40000c07214034164865070b881c424448010b00304001c6007039085c4400c030a50156241c460070480401d82041060416058604089516038403d84030640005403032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 95151385 1250 95150135 95150161
    0x603140603120a05090d0c0609051509010e0607060e010f060f0f03110d021c06051602030c07031b1a0a021e0303060910050907020c09010503070602060f0a020708030103050312 77
    0xc500c00318000e820040e0028040e50705030003d036000d07500b0040c6ea030f40500c0003910b09444000505880e0715141a000c2c10031050003031242924000702c8064108000150b92030303801c115413805040d400c07104155590558038002020300000b6200040e250300700f0f8010030700c40605402510641c0c00907800a4017055442c0c1c500300c0c4070102444003401c140a0325880b44c0c40740c200544051500740c009080030220042518420180a90440049c3d580c25a58400d125011451401b85130300c0704414401541485030030380d482c0d07032114502c1c4002071103041140043e050b22600e401107100140a001c4110411240600c81002c059200e102040d00500582e8524005001500c0311860380d1402100290300356030720002842803041d0702500d4117424001080000a06580748e081091040b6100d9010b0b1035038090b00340c2030140c50041a00002e1007500001424005c04d680050b846a0064051400c8009525103038101002442000d60180881100100210500c2800001013400550008041c04203541e40007a20380c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 95152635 1250 95151385 95151403
    0x30b010e040915020702030705060a0e0a1212081503120c070e010b0403080901030219110c01050c0d08060f0d051f150303030f0f0501140f060406022e060603140603 72
    0x11580c443c4011241d82d0300541c09001540d1002d822144055199000181c5c00d4200c4440c1d20006803110700507052506001d400300006201108044031440507940d0307540e8800b08203400c1c100403c01e2080014207403503d01c1840c054000d80242c1a01c3c01c1400c80c00d00e054296120342040d0070140700d00f04000aaa01d40c894020f412a00c0010120f42003d00707503a1040030991200b68034038101902813040001d110b4244010340c2c80050103494480c2e844a00b0b2521600300459500160705001d420b00082c0c0076441c000c103102032201900e1801c01d026548520018000d45030341001d00c1d030071807004150003081010005404950a44a620f02c28079182c2d061041803d40c3d0f40d6040e040c8060100b047c0400c0000d001e0382202c1c81c2d50064060220380705071200100d0301110000d03030149007041402880c0e1622130500403e002e0b4a4401982c1c0d00e45884c1c200300010799651101402c11110740306140004107507a540d09071004048c000c5d202c05104040d603d080c0100500b81d500101d8003501d0030500401c07c1450001000c0d48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 95153885 1250 95152635 95152643
    0x1104080a03050a020307200f0307030b07030b1203030c0304030215040c1a160c0611121b07080609010606030f02120a0f02130e0f06121c1101020a030b010e0409 70
    0x24852180d6600711203030740040c03d282c0c0c15840300344124400190b2001602e2241480358804105007902030b000c010b1a038490000050090300b0125043c008100310586031940300d00c107400d0108032132041d407012407190198500d041c1800d02010044c0911561710300000c60003180030b03500722441c0010030110f04002c40815100108242072000040000740324203600f0130700c0125801038103400c03e040202608264812484112400c06804205005080d08806130040040081006000383d050803001001c080c030806045a020415007031590820740400c1007101c010340610020741d0440c3c20900d407000d01034801360040c01c0204e41005074881000e5501d100f1b440054040061b001c0f45a1980c00d91070000f86080f62900301d86980800001307076034074040300c0c6800081c054132600c058180783c10003c401d41001e005d0311a030f2281c12211102c0c0204e050000380d080c518030089010403600b8594060070389001c2c0c11010b440c01c0c603500100b074006205405505c007040f098070a0b02d420915071030710010442129100c0b54018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 95155135 1250 95153885 95153893
    0x4150302151902190b100806070903030f09030f0b06030c0d05010917090315180718060b0c0303010312180905040302060a0501210602070807050a06060504020406080c0309010f050c0706110408 84
    0x1901150174543c1050300b000058010780324682e2a00089410620105c84040105802501c10810554880c0b40e400c420003c0c0c0c5095000030741584d07154006501d62050182164011501048059130140000900084010034520004a1034900540030b0546d6440644d540b59054503001d031b81c1a000d500311020741c03400802030040d0b0203141d4100b0b10405e8000d0038150310b040809c00c24004403034041010b0390191001c0004452401054151241510055000101c650341c0c01e0080c034490803000400c3c0ea0540786d00c83c0301e00243c1c40c00f1a40c100c41c513071004610b242d0742c103a503d030000840300c40c1a805a800713a0700942c00d5171071391354611200005540c0c00f842211418001b81000c80316015885c48240c2c0554405c140143c074140182e103807065650403a540507640380d00906c0000c0104055846081c0041030151800d600700380c0740c84009800e42100a25080550b01c1c00800a900030100713600940da0252441410019400e05100e18112604005e2007140c4682c0760003040c01d070000c0c5480030b0354111800c080041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 95156385 1250 95155135 95155183
    0x1203050d0510030b070c0b01120f170d0504080d1a01020601050f060d0501030804061e090504020304031b050f0c010512180a050106092a090504150302151902 69
    0x104001e0000909400c19020480703004030002d00102aa03a0054800c0ea40300d0948a055050801e1030381d406900019940180d02c4035680007400404891407000d4200303801e0405641031060342c1e040c901c07540142d252440d282408000070440500054641c0c55441c903020441e40c0400070030030311503000b038a1105026a114400400146ca44408001203140b0041c0c045801c2010403c0044142e8000fa0000c58007180049424070115a0007405c1000341d0041014500840340b4260000d41805014080c0c0c0d1b02581d0000b00250505002e41081c1036045107410070441e0404040c286540c841700b41030404602405101082440d940c03090003034403412a01c2001c00506500e48600c0f51400c9580c88504200b54001c1001071800b284080c807503003000300808500441c0302000114014040781e41c440e544000030305c004d60070131410795212000b941981e40c252000038449402c84040e0300e10803150b1380300a60028004041d220328035154000340890841c1144a50f0301d982030f084043e40c83d8920300d0000100c003030404c502 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 95157635 1250 95156385 95156407
    0x101515120b010f09091a03030c0d03050f07050d02030705041e050f180c07020301110a0c110a03031b0201050c0f15010b040509040809040b0d0809010906030213090f15060c060501120305 81
    0x20000c6d21808804007410030703a40c140c0c08642990007511100d02c1a8000c64095107059805000d9a0b5025942400010071803400300e40142083c0a00b4082020702a404030005030500d014200b2030f4081c044d4100f040f450700300503440754004c0041d01d0150602500c080c46001a113801d0500d0f14942c0725201000c40505941c030410300c503180d83c002c1d1409076499901d40d1180d1540040302001410000034641d104103403240301e410100c1c1d086545100d040c0c01044015020800b080e0b121a004550151803a00c41040c0c43da0783c001201e00780102d0200c3c0340c690241442e00c4156a000240c0c01e1103c00f0300070710b000d10302d03a070300c0600c0c0034203000780d200d11a000034894000800060072039006210390311004100184422120000c20b0781802001c100710f5090070006540b00c06580c0041c1c2d01c00c000c0010780f0303043d403501c0c00e9446110b100c02d41c1ca11034144c00c030342c0341d440410b85e254151308040510505c481c0f01040c0c03196245401407550125440c255441803130600080740545101d40c148504c1a0140c41346480c00d84080c0e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 95158885 1250 95157635 95157641
    0x180901050d030c05210a030c0c0807121707030605010e0a05091f0e0a02030108060a0c020d0e04241719020f0d02040c03022505101515120b010f0909 65
    0x3d04448501988054014820040c0e8010000c090b000c403000d40c48107060407000d0211100c46841c9010700c04200a004002034001e000c9450135648686d450300c0000340481c09070703400103103104518084c401281c2004500d60341a0700c007004a40007641d0f110107183c00c000500801020074050329410002c94400071741508041c1e04542a000c80e2460240c4d90240e8030080814043c0b010f9610180c0715800100402019004100b42c07508480210300400c41030010810207580c0d0105c400700c01080c010f558400080d01c3e91307a644400040e001040006d02404004540340703104013441c2c05840c00f54a1941c00d003140c042c500103400380c0340101d41c076404826462280c0820450700400b080e0264008071118000c0016110b500640e0400c1c402d0303403005038071581070402d01c1e1416001c0d24000d21300c2500000500010070800559203e4242161000280d143c840a4001380400503580180c054042c5600b03404919a82c404000c610a075054482041001d114800440d00000392800d8000060b843d50028003035080254 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 95160135 1250 95158885 95158907
    0x902130e250f15090f03030201090b0601030e061504020d0212010501020609060c0f07060b0d0b0601091e0909050c090f0907090209010c061d071706070f0503070507020315010902180901050d03 84
    0x10611403081566005ca61a0300701c550f03001140141d45422045e1b0802507110349282d041002420140000300c01060200c0d9650001042c2103041c089102000000e03072a6507045408048503004103542d104c1100a52081e400070a00c2054014400c0c080019140c2c503001c03c040b03025030300782049145406210b81514109801446080c1c8500b903441c0400c0c0e0003075035000d007030102f510711840c0408030914064001500300c035aa503100d40c04407a2201030100301115010189030039600c90650008409006042c8545005a1050300c036800070605014054108101c90301d0b10b10a0484e101121403c44d204c1d018002030b03000d00b480c4107011561000425001034042d4100e1581c07012001100c1c0c2c100080d00c000d861505850358001440821031101c0c07203030340c0f20050010f540e01a47c0c038281850070300c4202200505600c0020800002c02002003590403c56800b8046c00c07004483c00100480d0550b11480c9010086d40308800b07070f080c00d100000d01380170740341000400e050499100401070304140c1580d8a042d241d5030341e09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 95161385 1250 95160135 95160137
    0x30702100b1306030303050601020115060e011b05060705030a0506011d0108180111070c05040c090513020405031005090c030a030807180504050c070507060315090902130e250f15 78
    0x2c00b0b0722008015a114440042d40290b40109450401d200064211030000c02c000b042c1c40000e89003403000c66001f088582c00b03444203290881410492407200075040792038040007400b83c001e210600140301e520001031400384480300010060398440c20010740b000f0100b00c440c6040f1504802040b5020342c01008120341c001c0f188081c10000030301a48148bc2110b142081d002220040030501d0b0007882489015407002d404192000c004480803075202401c404864820180300d107520203001e40c0d0303035102034055500809001c0c04440300c00340214041005800e003190340030b07014443c00c2c0c0310011600d80054003265250b01134403090320f03075154500b0449408100300c400061318070101d0000a4079841d5807090a125090303044840d519864281b070004e04148003079211008150818a02d4255204650101c030215035001000003003544070f89c4041010500304100220f036442c5070a040000092021846100000c106010040000c00d520320040c41807640340101903000880301ca0a00520a18220b181810b06503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 95162635 1250 95161385 95161399
    0x30b0124050708070c03051b0102031305040905031306030209120c0d0b0a02120c210709050609010c051005100f0303020a11041407030c030f0e03070f030905040e010911010203030702100b 82
    0x3152292003d004843c0c1c400c84055200c1611070361007003112303280c261010000b440514a44966030364500300c1c440080c021584103568072200740c42000800c0084070700c0d6544061840d11b100b607417000040d0094102c1820940070b1000524004440342000c22450b01c214001864400013001e2078030b48401948004041c145603139800c200c1c03440320b51a140502403061622810003640d90074009418000070081c41419900113b010080c85001031b0030a94400a0b1141034a07074545803412140101c42620103480043d0642c002d540700c511408070513401080c0304406c40051400398980c1c0300c001030803005803440041c0050708203180000018401504081080b480100007052102022110714034003e820354021003c42d0790352004068050b010b010340490303032004c141c041005111400d1440d44078403403900300501c1c021010b04210201402080740602034407001e001044815000c5140c1e9000707010819081e55110080b5224815540c8000112480751910f41c2c081c0c1a5168003250000180c0414549594003000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 95163885 1250 95162635 95162647
    0x309080c01110403061112070c0602070b0a09030201110a0f1407051510060c021503040303060905150f06090a0b1605061608091606110a0c030606030b0124050708 71
    0x509000b110b19400e40301c02681e94607865450442c04650501c1d00703082100741e050000c2c00c0308443d440b05982e801040383c14503020000041c60214024070404c41c00800000c100400c4c41800d4900798005541127110750020000a41006c03513122042c01000c102030002032241e94083c0195109a00074460040005070301801d11842d96a03c5080101000c0da03c040d074881ca40800007024501d1400d01c000788030609003008800381c03640125214846901c01003226600c00030219040511a52004000340f6200600300410300300000c164542d8036100c400a84200a5150400742d189807400849034038040c02000001060f15090824903640c1150400740c2d034901c0404500c001143d4148403062148644d81011070080c040b0210240c0341f05030203800c0b5803403076000d103400403089082d20381d0300019103615081c01e6106600c2044100e103000c0403030748024221104190300004102c001d40000003a40e220b000c00e501541e8a4170b0760b0100740c403d0020100c0225109150100e078243c0100000c00100d400345041d5440c1c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 95165135 1250 95163885 95163907
    0xb091203071101090b0702030303040f02010c060c020d020706090b04151437020d081b040e1519030609020112140405012405040e0c030a050102090a050402090907030908 74
    0x500020700a450400800d50103070711540e80184003001400102e1109800d0503183d4010a03a24000180018070450304c06c2e01d80c0040d6801003c0541015a12a505010b66100c0e07800081d01c48084000c2d038000742c0f18074580407031100e000b08070300700a40b1110348010341414030300380c80705088242c0703803270345a041c000704001030004c90a2030402403d0b0121400351106401169030604000d40503100d01c000c00044646010002403075006c20700c00503424051030100300a48801c140c2c1007681c218184a10290300c1c0014000820b0004046000d1081d203a26401002c080d074010140304c80c02801d000000c1010000000c10300000cad84541c8098400d600614041185c0b4034050b006004480a01941c031407945103602c2004100030b02405040702c018a0001504614061402d42130340c020366500810b4401d0f51150450a01d8003410003000c804010000c0803640840e601d0b0038158000d40c0a081d010380102003d42c4086441d081c40e000700c0c0c010a00140100005a8807558202d00502a84104031f4007000204082c2d2140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 95166385 1250 95165135 95165137
    0xb040305071b061701030b0402041509060303020f0f0d021528020d0501081218030a060c080f0f042f0301020a2604020d0308090a0203150910060f0b091203 68
    0x11110040b55110303481c14028040e0103c01c2a04030409000014030040c8000386002c00401d802a905550200300090102c0044540703540f5500041075051421000009059001808403850b0000300d041c0c800c649507881c207450301c46060440e4040075034800385030851074001890741c0e96840b801d0003080842000c41ccc1d0320740c001a92601340301c5034441e940100b0910000746a51040c82d0052500e2802010f04420b0070f1141c0003a401201c2900c600c410180c132001031151011721081003407517800324041001c44101d503030140802d00c0a0792000c0e074030301209000811452190315428095504100070082400004158003600b000c805030468980b0010307078850324641c0b0700b4000303003024044648030380c00c00000301c07040c20491803402140000e5004480092101603100c40418030940da070545041309090b501c20382d1251901c00c800c4002501841340d0180b0302407412003400260701502550082d1850540803203000c1095818502808a020200c0c500411070502c021000b00800d0b00080c150586a9414944040c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 95167635 1250 95166385 95166413
    0x3030f020307060515031e0d030207030201090203010f020c1011030a051806040c1703090d0b040c030c0f03020429041a0402040f09110a0f03020a050906030a061a090d0b04030507 78
    0x1c2c0c8101081003d0307246c00c0c04441204d804030b09000f1a210082e4006554410881d402c0c001403607400107a80c403d051007074000196450f009402407080c3e02507038040e0720082d40143c0240a0300e0148030743c09004685030b0f000d1005107031083c40001e030458035144070307510051801070000c1329499950761500d0092170091050b18815802082c08401145c6030203010700d455500288140c1c0e20390410049d8942031b66446152102003501b140ca4034940360380e685483c04000656030401f9000c2407600e20009201d0b401e006103031066078802d41d000d1040e01d01448810500d81001d1440e07082d0f2601002c80307129241072039804465007241022801030980e20031408a422a40283c010031044000000c007885480c0c80d03400382c0e05100c50308400e07191401ca0751030741c02070600110503041c408254001403070700380c0640300d0300541d20b00104c0100300581d40d05006014000420080c892141c00d010f200080302003411181007541c40644000d0012039641c5150f941d40e03004207500030300480920000b8000fa0000c60900090416 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 95168885 1250 95167635 95167651
    0x3080406080618090c0406060903020d0f03140c0c010306060e0906150405061602120705030709020a0909021215040203060d0602091201050126060421140c0a150c0903030f0203070605 80
    0x281e05e0300d4400c1030100350340b05600240306200040504000580341c40035241e0410750090000600c00380c0c00d20342100c01c111a41c0d188441d003200410b6011003004085111300411100740c80401a41e036441c0d1060700c5209040000070b074040300420008502d420500882c4200c601448125440d0079200c4000482c903800c0101c020b080c5015100b640c004504008480b0b00403003070314000410903185002c002940e80d95260241496407600030611b0820240940d034044040d024100f015525003410880e90801c0c0070086a41c4c400e11910b0000311689824940300300d03400741c2c1020305519200074660326a03070080d5000c5190160020b425482041500e4000c0c45600e01800c183c420101042002d00504002e03c4440c1050500740c2c0c00980510002a800c074601c0c81510400f140032100c1307200080c0040c0e0300b80e060302e10401e0540c640022130705009072010030340900007071040344021449502004124119030090300d411000c908196401d0010a0181210400343c45040c0b045078a8074000380c5d6032900391141651648 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 95170135 1250 95168885 95168893
    0x605010902090312030121030207120b1f080d2604140f01020903030d0504050a020a03060c03061a0d11040306110403020f030d02070501180e090f160308040608061809 73
    0x902c2619090001101800020800b5030031941003c250022000501c0c0d00910b403098062641401c16009009080051484066103003c400f298284110114011076401414049144520003583c00c031491100035140c0e0394004100d20314086406070340000405132105000c02c1007c041551444810740c0e039a01c15031150003a24420340080707464514004180340311042c181d0050020400030f890000c140c0300814481c010202d11074503282000b505005c0380703c4022b0340100c440d481c0441807090540101565203481d07a000c20580e80c1e18010940c1180600c040c00100c20010062441d2000da84e40004d07503c00f54080790f0701d103400d9895603401c08071142100c41c0c01181c640450100194a082002c520100c10154090000c0400b8480000d4070b40d80d640c000c06041c0000000c4104c0c900b80f043d180180900071400c400481c5044c080c80003a0b4804941c0280f001a101d6520403845844100c00a041140e92100780103060a0400c1c1d0305031508100245080d03002252001000c41e0040001c0110707000780010320244c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 95171385 1250 95170135 95170147
    0x1140a110c240702030a050712030b030102070609020f0609090a0209041104090b01120b09070807030b030a030903120c0803010605070809060d05150306010b070602070204061509090e0607140904090605010902 91
    0x1840c0002c10080034002950818005400590780110403104290ba202d2101001146000310076801409001d0810340c140d8800b06921040200c25030140c001b0034021100c65050900d55800c02000d882807006c103942140140002c43c00c20341140d00900742ca004006c10101d140c80c1302d000b0a01c031a4200d94040c13a025601d98144521658003c072403e040d21200030418000c44810340c1c0400c3c21104040e041004101200340020600ea02c81c2d807040d00c0051008003521340000c481c0c18004c001c3c5600d07010a40311100c0d40e0902e803000c24014100300044640c06800b103800d5a1802400b581c0c0c1d038000700005d41c2d60703c00c01c2000c41e24079075034440101090b8440d0703200083d070760038940c1c148000d211711580c8440c000e6020600502042032003800b07881d500c691101015a035901688041000381141f6402560644003000326214500d400c441000d041c0d07803080904200301c0b501600050760b598000d5500e00d01040c3c8004203200c41e0440076000b0000c2040160012542c0c28403580c0c1d400458100b41d2045401d250302050f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 95172635 1250 95171385 95171443
    0xf130302121f02131517010b0a02070b250507030203060106121821051b0a021309030e010804080c070e06040612020310090212070b030709060201140a110c 68
    0x2d02401110000000c6003030291024081d40003901c50301400603a0980c10440000b078034030550030001030720040c80004445d965038000d40042604011848809030080080c04100682d03080155980204030101c001400304040450000c090ba8031001035516015464011000d600e04015450080046603280c0700000401181841194400352094001c401c010010300082013441c008002c80d0301a186d82e000e100304030700205a61600c1003031003024010502056810003003801090003600c060003640e4490710441c000f00c0f0b000895806e0107005010802500346c1281c13a52180c008030f40d21a21440041e840e0502c0701c0f01c41d40c500740c3d040d805540085c03a60070400517581020700541c001082e901c40030400f204c8460b400240c0300c000400c131007d00390360b42e410100159999451508000700482068030841529207203000200c0d44212524004250501000901284144103448061208006ca840c03203450700f8000d03a010300120740d5200c0108905002c0c40304404000d206199080c14112003407885801c021007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 95173885 1250 95172635 95172673
    0x4050c0a061112090625020127210f050a0c061404050402070302070e0a0501050f0f010e0906040f15080d0908030a14070b0103030e030f120f13030212 66
    0xc400200100329410b4900e20400050702503480030b043d0f020319181c14031007020036014003032444166000c1d00e040002004c0d2881c0000c501980368002ea84d0030010048450742404102d4007420080303106c80204100300320000c0ea100c0101c00c90001c247c14481e0980b401e44071340c0116a0001020380302c41c0c02c5041d12004010400181200410403401e25031040f03c00000c100318140500d1246501540d00022078204051092285102402030900c6240b02828451000780081100f40075250240c41d40108070a420300e00540c03000504d100503500d92207590030385024045c05100241c04542c0082d02d070a80c15440185501512200d86074401d01c40002074a80000d0520300420740f00c01070144408898203012105001c0304840d01a0030500749041141c28038000300d0b009124011000e410044440008800c25034070a0541d6000c4504904861020905001460b100c203a0f0081c0403c1d00c0c401040181e419207160400760580c1c01040f0318191a241e03903030f000300d0029580d03007180d512140c024404403100c1c844480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 95175135 1250 95173885 95173889
    0x9060f0b0108180304270501081005010603021602130b060307120f0e0a0f0f0b070f020f010e100e01060819021003050601020c0909160603060603060b03151203040e04050c0a 76
    0xc01140e003070420f000d019645920403070040341c40d01940d605000c980c900100214000780010030000304810f40e9107481c00c5480d954214003050000b0709040c00042c803540300b40251107035071710440c1c0c0703c124520181e402c2020f80c0301100540c1600319207518460f4103540d43c5802031031090400340c071601503440b0001a03c500700c03150040c12180e0a4038021030290715440000e02c21194652004104008c030f14107050188002c107032600c0003407101c0d40c1034080020070307a0301195041481280e6000c17034041d02e42c6014102d0a031101c0d042c44100660083e018a002200141c01c10001c40d0b0304200000390300354940c00003c2c02c0440d5507904102450040c10900c046080201072095244082e1508000a0408100003500c855a00440920480d1000046803100209021951080c4040c43c40780817003540d50100171380070740210300c143c001017031801e5000540c1c00f02440c00c5a214111250b400501103407544100841d1781294449a1842e2106100109880c400e0311182030050340144010890240c2c61000c002c0030000c65 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 95176385 1250 95175135 95175151
    0x607051c1b1214040303090201050c01061e1d07050a090e0108011401080307030c030806010306080618060a06050112090602040503060f01150e030606090723190201020307120903020109060f0b0108 86
    0x45100d004403050f140000c250401e6140c600420280f040c0d000407a414058129201e003203503c0c008000403100d280d501f1500c40080f500d41c0b010b142e580d441580c0f88040440b8444019803001c3e030000134900b14419402450200f90b80e061101c8000d450318036000308640b00b40c00c00c103503603955101e40c591a01c02031070400c1c0c0144042030080d458425180d500800c0c0d065250002801c2c4a08030700403a01c0c0760300031381109000d80100c000700e0341c03a80f80c1407117045103025014000d0340e001c0c02140041400f5541c2405580f05036601a1584442000050860802010741e80c00036150030780e00b4040400c880c1d90610849005020307a1207110b8155050018a642848002d0b188034240700c52104110095140030400a600c10421207400b0360941e1f40410a4034010720144000b071564800f400c0c070300c210300c107480c028000b01c5801880c42d081c84004440240d00301c0c030050b0b400e080465064011174011000d10303000009003911a10012030910b24540e10917056898148411215a89032500001c0d1541e211201961250300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 95177635 1250 95176385 95176391
    0x603030e0f060703050a0305060a0504090602120c04140d060e0102040803030106030b04181103070513020a08160804080a110105040311060907030b010b0f0915091c050607051c1b12 79
    0x42135801914a211312507541041c50344031000030321242e8500c0d1035040280300c05001070000c14038525080c0c1c003d610007591000112100400314a014804000b6102500c01b49010045440744607000c00512803240102103858030349a14210000400c05c0c009000107044400065489504181019040d201704080c0180103d01e003a00c0200c40c41c1c0541da0100410784c00c440703201030260a80011904040650300a1904507540101c402c41c0c0a289500034004c5400b15924403510307443d0300300c0d04211040c0d1255407100083d5150045800315018034001d1828034030034101a44000441094503003510401c0364184d0210b40803880034803044800f03000d260b52181c81d42c0302070700c042e80c1595550f0391015010b0007114a81140480c540308c001c07416030226000300b00000c120700803003d032080000c0a640e10440032103001701d520808018003001700340c080d003400690010140c402507a84a00c2181c040d000810340300400c0d08600c1c80c81c000032905101c5c41c0c2e000551030010040c05652028003a02d034140043c080c61415103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 95178885 1250 95177635 95177647
    0x3140f030a080a0b04020d05010f090b030a020904080f1315080705121f051921050d0f03110a0201060801110a0212030403050405060c01090507090b010c030f050d0603030e0f06 77
    0x94441e04643e44034032030500004000b140000814000d00401241c61803552070540007040355140c6445c250700710b1381a0311042c801100d0800c241600c074010144020f402c05881c0f008a0002013001740034001040148140c1c0c1e0500a000b8107070f855400e0142e10018404203000c000a405a9100050766802a603030b06099282020000c413440d59044010007009984000f400c50f4a00c1b40c1c455460440240001041c04189000030a901c8500011520802110010070300d05201c070300c5840c2d21f00c2950380d038010010b40130381c000d0410b00b901c1b009a6040e44004250fa110740d007903454028103010349100c404c180e0000074124280040a402c46080e00041340103480140240200b090740003500c014080d9004d0030346a281c2d02c5038607060340c45018a0300003a0703024030007080300c030401c1805602c8010346600036800c40d5580c075640c0f840a0f0031504406011340c00600401d0b007100110b406181001043c081d2440d1040c0b07040d00180c6102c0450f4100d410460002e13001c90608104c03440c0c8040b94000d4004125400e0b2f140070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 95180135 1250 95178885 95178887
    0x907080121051b01020f030f0301080c01030b010903030c0602070c090e1005010510031508010603241103160c05060c090a140108041509020a030311150606091509040603140f030a 78
    0x3c00c1a440b552140c84145089840c2a4424000c400004942da411030751140c00380c50300341c5440c5c2c1003400f132280305204000707145009600c0390040c0f010f4000d040c0c403804d44090440c1c90450f0842d88101040c2c6019400f00122000a40300400800007003505a01c001003482903580304500342240c10545104141c203010060141d0790390b0f610310083d1450a41000550078450402005880009911010342c5520f44000041444650300500d170801040f4080744c4c1c9042c400c2c40c40301c402c80305691051450050f0500c001200d00c510352460803803000741030074080600451562040d181ca40112240303505201e011550101c3c508005007030360042c10b40380620910701d0f44900700081c2001c00052018208065084c445000d2801d40d40c0a0f104d415000b0b0103801c003003600d03410058514112210003c10f80d00c2070040741d1620324002140180142d030b004001c04c0c0341c0310481d81040f040c550b01071f0744141e20b5101000a40b001e552140b0074900214400d002015181c092960800d040000c070328a0307121a40c2080000074043c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 95181385 1250 95180135 95180143
    0x10e1621020901180902090f06010f0807020307480b041a070f05070602030301060806190b03060301020f070b0f010b070b070f050c060a0501090c020d0516080702090708012105 77
    0xb6130b002e2000c140407414108000000343c1540310010790410301c41002d200000c4001c41503071340305d4034003a00c0751821a180c18504580d207590031590320005802c1403200400007210b81d042422810f40111180c500380d00003200115003440c0001c0c20400c0344081203000b88110100030702c0f903001010030b0308045062030324200007032400d00e0145164200124000441c0d00402195aa0b01507605800004480c0c04644444010f0341c0d07580f0070302845010810000020b581d80c6041c071803c0160194914101c0d0751b41d032614100d8007903600050704140d85950288008096020400d0281c04501d0188000c0040e509000440140820040e088000381440800800380401c05100ca165000b02c0c45203001e6444a6a184045a45e400b60000400040c0690014007482031982d800080c10b03115403071000c110480070720b801603903151202c0010201142c414891410f1082c0c3c404803000805002c0c121044c50407169a00092a046c401c940110108800350300502000f488426a20301c00388049904100440c5035854159503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 95182635 1250 95181385 95181389
    0x30f18030905130e06070e0f0f030a031211130306140103081602041b1701050306010621020403020d0f0501110313060b151305120303010f0b0309010e1621020901 71
    0x41c007040081d4100e15440e035100325613894200081d180107080c1804010811042560000c1c400c01c401c0188844510300644503c5000000400801c440280d5650030783d5611034040d00d50900660701c6103042e44049a010041039146907402108101a0561800e03400f242c1554990a0100042400500018013a4030840b0410241d2245c5070002c4880c0c1c1c80041d0281c92041c03030007c140c071508540c540700c40da00840c074400491810a0f440100baa00c600078503071b44d180244142400210b86c1402c54010041852004e20b4040494501502e800d4481d004171b541201090302c01c440166208415006014081c4141828031001c0c0d10403525508285180d61018032089102500c0390303a0343e004241003580e517040d20800c04011a9102520392410420f03600a080c7c00f40b00b854066030030082c01848454000c011a030585010000c0044e03483d040017080041508000c02d0507030f896503110320800947c1000c0002e00484900c03800c00742481070400783c42859640c0500d00d00043c201341c4502c0c000060f5505480c2c2c0741 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 95183885 1250 95182635 95182639
    0xa021201030f0f0204020f03040203060702010c120209010c050604050d0f0201060b04050f030c090420090f0106080919120f0e0109060e0a03060e01020a021903080f0a0207050d030f18030905 83
    0xb0000060303003081c0c00300c1c0ca990f5000962240c40081c020444005600c0514840c0d03000701c0c02c3c0d818540da400400d030700717070f031200c030750810000c0c2052462038074000c8140d024008085041c03400721108003503075498514214082d00c041c0d41c42d03400707401d00150b2980c1c02001001c00c50200c0c402481450f160800ba480c05008502650b8841d554140c0054201d031810001900d84d24002048800141400d00b001b065406440b0440c80c00100d0054810080e410000115402501101210b000c16841d04904a42c2440b000e401c900603401b0b8401100c50105091740101d0140d0f0260030180064004040c010b8070500905a10000307200f2002d020034140d03a0002004c1045991a0a2581d10b000b21000024030203105030b00b00400552401c405900b181c941503019100d0044240c0858418081c0405d104100d41000325000b4000b401d2100098012040f4409003034110010390b0000d0b043c1174595031000e080c06031902c41a0006030740c03000680202d10750f074003403018100070110186081140340c0e10024041500390090364 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 95185135 1250 95183885 95183903
    0x3010909060b0303070c050406050d03080a1104030506040812070801081b03010e0307030801050406050a081c03090f031107090221060307030618030305010801020a05070201030c0210060b09090a02120103 89
    0x522901e600001074081c4002e0503a5514605031601d40744201d0140582801a407404c1d00c0850300c0d007000c2e01c11044960b095101d040e0f150744c800c880440a405044410300d100e040c140070000005104010286c01030740f1079500252030f00d03440a030380305c6036260052100041000c200c00402c40c1e01404111310301d003102201c07070850404040201181c058107200001c10003920000604005140d80520900d0586404541c240001c95944040100c1c4141c1400380f481d868020160213141d00d510b00e280025a1242400c0210328802181c8441c1402c44400a042e0003151020030000341201041c00300760040e080d180d03411820000d29403442c2d0180c076015041000d10003032500c042281039030204581801180e12502c18007024001945200444581001c1240481e00b418004140301106000b4dc1711b456016035074181c249801a0011000307030150100e00030950003064000b0004814034040c00c0043e00780422750507036a14070034060100b9050001e090310304442c4140a24100344100c01e407420b044a422580078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 95186385 1250 95185135 95185151
    0x9020d02100e28090b0f0d0303090611030f06150306010c050a062c07030305180f0a090614010e030c0904020604080303160306060e13110903060c0702030106061103030109 75
    0x9032016603200240640c44081e003c001030000360319074040c4100c003692401050f14607030307203403207030000c1d506000805540300014410900030b5007801c1c400020014000d280106113080103450380c008880d00c3e002c00100c14080041081001003580d4002c6030800c1d810f0b01c020345904450200c00d103090102504d11410810100d440c9818864200034800c815600801c04002e07140340030303407190500c040d5094415403020b81507405c0c1c0000e22012403a401142c0d0591221460f0401c031020071a51249001421a40100c06200c6d483c0c1c030f03490320465200684004034001030028100001e90082c1c50307914000504012089118140645010443c1140c01205440100e02510b907480060124010b580003668030348804010489503181a050b0902d402950351002c12000d9110742c0300b1103038608000c06c0e031604204200c150643e0003aa1703901c2030095100600080c1d0034441c2d01c4000a05040081c0e8241c3c2100d880032589000790703d800c0c0706100040407642401c04103100d071050303c291240014855228980d42d24441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 95187635 1250 95186385 95186387
    0xc03041709010c0209090a03140a020304060302090619030905010b0d020a05090912030f070f260c0c071206050105101b1a010303050d0e032b110307050304060f09020d0210 75
    0x580e03100b40e500514171182c1d86024580c140d46c400c291641500000c40088045000303a01802c01c5a0012400350301442c41d10b42001d909801070740c400300300d641c2c10090800c56550102403e00341841100404e680103da000301c9424801e003520103642c3c006111303104141803000160303502d06002c4208c61080d5425440c6584a0342020700300b00c1400c244c0303e10308000004108d0340405c001d1010b803250b143c07516100c0815107032013011903810184802d0f49041a25602803007100303142100110760b0003080c0d80c2c841498034440e04509410003440f603015100800c00c202c00101045080c0c09003502402042c0c4081c081d06004030710040065040702202000d2269218442040c000e07039603224150b0020141c0d90300410f503528500100300391b0000d46107002c81494240c0b0309131b00341004000c503a01c04100f41c1d0320000030444006440110039002d10045403d1b9a00c103d503900829210b1b01561007194191a1325841e482c0508015059603a14040b114001d403501584000581d0784a404008858058801d413118403d4130f20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 95188885 1250 95187635 95187647
    0x4091e02040b0706050a11180f1906020f0a02010207061d030703031709010603020102070b09130606031508030c070311060c01050f070224041212021c050c0304170901 73
    0x894046030001030046101a1140020400c180c8900b40400a0369544884841110715110009560500801000b01480d9054803810386001c00101050481044100051020300d4550070240110507141e0080281c160140001d812a41900020b041c40b000c213030380000c0d1250050b004840502140c80c03000b00810300c80c1050308103040406001ca030076050301c9080c0a0a02030501e04045405510300000032808441801440300b01c96060700102041402d028862545810a0741c41d181c01024000415410f04024020078008107417948000a91130803801450780306020341e0300500e4080e407040200c01d051150024074502283c1e003000c0c0240e0131024000c00034440d4401c454810740c0a60034002400070001440d08024000e05246d021a00c620b12400400612030900c0c03ea9000441250b10000c3c0110b40c584400303101c5c94080349000b58140d1000c088210032070300034400c190742442c1d1404a040c0350405030712500742c00020045e0050f003549415550401c2819003e60501080c00000c01d0034107059025072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 95190135 1250 95188885 95188931
    0x10e1f090903020102030f07110c0f120601030c050a0605070305090105131e060315030b06090405010204050a03050a061a03100902060c010c26060108150a0302090a0212010501080603030409 83
    0x800307006104460600038041e40041e10079644041114000c1038409005103805460b01c0940005443c2a03481c42c01001001c5005403002c980080036004003505200c010710400e40690300c2041c0c0d60803801d04000510a0781d03581508103e007401401c00102021a810409403480c600003441c000c1d5840080b014207500703a440e55480350361406a881c045030001c5600ca030a11046e5021075504000d08840c012084c404000309101c06001d901e50700002c9030701802c014040c2c95000e4000e0700090300e010380d10004103109820680c070958040d00f01510358800c00481d0f020b0380b41c01c00a00518051004603100c00a5211241202d22004807030340c4456010441d20749009903020240c400d4001c00440c002100050000c034079144030040c2c2c0c2d40c008030b0705080798005498440d0080780b041c0d45258050366039a2240c0152404541d4040e0320000e0b0110001c0180e403444a032034440d8650200168030fa800030000c0c01010601030300000c1c1070200820030004152000003d0301e088905035000401d646a5808070701e4803d42c095 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 95191385 1250 95190135 95190149
    0x81305070504140f090d1407020d0f031d01020604030f1107030b09010902120304060c020909030c1207020f04110a03020f09060d06030519080706050702010e0609070f0e010e1f 77
    0x1d1402c0900420b80003d4414040c282400c1501d5a4002c407140d101c0c424449580045a40381d0801c42072514158041d04400c1d00c0909440c1d0000e000b07031070356080186400d008070b00042c2a440d9914000c0001001c884089a080c002000541030586d00644500ca00d0412181042440c1d0080c00c801002002410300942d0440c038400441d042492009010b0715403100c069010b40550050800c820340e00004032000c503074043d0740310440000c40380e017009000b001c0908502c88502c0113001000e103100d4144422020300c44a880c1c9a540d400051050041d12403014040328400c618180041c600e4410040813103c0003a054600180e5844072113910000c1390081c44040c1e904820b0104000043c0780440d031200007500d00800c202d40308080c9040e5041542c90319000003c200b11800e0020070002280c40c7c005540000c902c0c0004541c00c0b1248400c2442c112040384c600c0310039405800200480d0000489130405004c000c3c3d0311700907660400b074000c0c3c48180080c020605e1078060401e03100c504e0b8074400c1401e000d0251 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 95192635 1250 95191385 95191391
    0x81c0c0204090c1406040e010509040203070911090a050910030b0705070b040f0201140f1903020c0a2001020109020105070f0c0b040b0a0801060e010f03050a0b0a0902040e0105030d081305070504 85
    0x2aa06241c00f0800682c00b691100c0c03113169801020394501601030380c1c212081d2907443c050f1130b030800040c03100401c030140003240c16108413280410501214000da21607034a00311042c0c3d0321550a41e0801c603010f002544441c0c0242554001e2100d00c511041c0550141c94100c074130b501c032035200c051040f14284107001001c2c10051564040c030040103075010021007418002d0b40d440c0103c5090300b8403a620351185181d01c0c0d80041c01000707141140c20100511045040050800600b0f01c220388250a081c00240da074111000300f031242000d68000000c103c0000350313903402c1c4000c10074141558006051031283d924081c000d031050840142c20015541c01c0540a07203880c0381e0031606c3c7c1d582c0c1c050244994002403008008a0749082c008100c140c465100c51702c02d0001652440080811400d06030003d2501508000043c1d803514680403050310b584450030020084a42d0040c1c0d51442c0655800700d600c41a0403c1e8407a03005604000381c1e0b203500107040e50300003d1001240001191924100d132030f10303160341e01107500941 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 95193885 1250 95192635 95192651
    0x30a03020301170d350f090d1412100b28080609010b03040303110a0e0103230c130305010504060f150503030f161a10090204081c0c0204 60
    0x9855005141200c040701104652030300040b03c5980c07166a0711098800054801560714078444681d0041c0d01e42c45032500c0401e000303c001500710644034004031103144c10104490180491008108180455844c1a103000700040422003d42d40581c4954140550301010f0780e00882e1404150700400c0c8001c01d0701c0d03e8641c1d80c0304a903148020301c5005081c9540e19141040c111921814002e9540500c601d80062105585a003882c0e044481900064001d400b09a601d50305c2400d0340512100501002600e41c5a021020401c50001004d40b40d1840d000c40c4030300800d15004902c0c80041c0041d540003840c040031b07152903560909466803402c000b41e00280080d0709280071b000501c5030381c1d8400c524501c921001484400708006213401c00004511070f4030341541c070400880000442060290802c42045460341146955644811400840810490700004410001e000030795070243c0003040141000e8034150300b003e05d0014060f84800e944400ca1451010345014140503078070400e8049182a4003c0c8100100c1d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 95195135 1250 95193885 95193887
    0x170708010509090a021c2102070807381e090f03030a02100e16030c0611071202040c0302040e0f0402120f030d0b0105040f17061003050303041106040503030a 69
    0x1142846150701071628603020030200100804c100c0c3e002034010b031251440d10411300070380b000703070601000980c4d100f10300003c1c0540b88903e1b100c0059800e6459401002c0d85410705400c070342000c07034607880100300145515403418044161009051102d400e00a090140c5084c0c50b02d0500c60311844000c860100001d00c5601156030402028001c1c207070050347c0800c51000c3c442e081c945ea1b4440c0700706810269221011003444224a41c011400c80c90701d010540300308100c0c3d4800700c28881002e4108582d10800c1c0380c41403000c961b20121000002d40d64000600c0d140e880c28070003400d49a41110080e001d07580b60301c404104240281c04407002800c804100f030300146046054400000b10581d4200e2080050b550b0780d5a9007400042c206000c1182100030350300d8054034412140041080d0309441e8107202c828000000d1040c48010900010301084401e00b550300c41600b499414034200501d0b901c03402d0b280f04010300200d41d0010a80340e00503480422a200d02120400103200b501503988425854403001030700700354003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 95196385 1250 95195135 95195147
    0xc020621010e09010609182301020c0606031510060c0302120313050706020102030c04120606030503160c06020d090303030209040609151e05060a050d150303080402090603150a0b011707 81
    0x40f07080b88020061151101d0080303003910850701c1d903800c164184400200c00319503e1b0840501e141c08103101400d41400300341c50542640c00108070509181c00c00c004110444c20140051440300e400c4032030b1800700d458003100ca614100b000e8040c3c0b10400c102e000081c1d0030140200310243c1c0d0101002c2140e030701c07403a02507071501c003400c00d015049649001d94500012447d005009880c01002081840c0e82083e0400003149000c18490000790340c4240c580e4400400314a040c0300a120320310544c6071840d595402070a003140b0300e1080f58009411503000c90485200385521800b0081901d41c585405a91600c260300080c0180c07035030360404103285150010b0404070500c200f52980403a0802802e5050400540c0c001c481c04800520030250407140400c00750050758031801c014000340c080c0301c10010322070f0b507050450104454680c00c21404929002c003401705515104402c550300c14400c40040040c4080c0355440c3da0403030405011007610035200c5480d503d0582c080c808e001144845642c0038070311450b01850040917 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 95197635 1250 95196385 95196391
    0xb0d02070c030c1d0705030a020906090402040306020c07170303060f030109020901081011030c09062115010e040c020d030c090320090c0c1216050307061415010c020621010e 76
    0x110a120404e8001d0b82409a913a603200d0165a141d16003950b1b02c00790078102075030041e000654002401c000d002d2003565030384043d00c00345000b403000584417202114801d240034019000b030703c07800491403081128a54000308a9138422002e9900548a9442c1c0020038050300d40754070002e40c0050007000102c0c0c071a4000502449013010b20006104000c400c0004480300d00c03065900030340b031201c100036108490030f28400501241d00300140e000c40842e0b80400400180c17200f80c0f2546c00386401711580c1c521b07569000700c0702803812400700c0d0100551109254040d5541c0383c102568002c0c561100080b040b11802502401d00458012203c1500c03e8450000e52200036a4020401d109050800100742500214015070b05588034010051070b100180d004141ca00d600460214541d00300c840c20321000003a810700c058801644211030111f858803001c3c00354840d0b508000c040c40d0300c1100f000040d1a0307584e03220a0410581d43c064800603954040801400074000c4800d00c1e40d040103415000008181a0529030303544 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 95198885 1250 95197635 95197649
    0x2060c010f0c0806012604111c030315050f0405040503041203030b09090304080601090e0a060606080f070e030d0c05030d15030b07090609050108060a09050702340b0d02070c030c 78
    0xf020b40c0d0390400546d140c080c5034103000700030b00317034000104136140c0c054901c50b40041c001d071071402e01d0686000020f540314a06a60090180b8481c00702407007016054003c01c000b0101290a059199040201041c0d1a8404050720380c4681e40340c80c0450140710003032003110301801510030014510012802c016020f803442400e46070040c2d05e950300040c1150004410355003581c100030040d142c941d180528060103401d144005e4251070040a04950004056105520040511b600c07450120f10700902c220b034810b10014990700c28000e034492a08a140e6010400c2100c0c90a1810440034404045c203101d491070295555100700c56181480d440b5074040811f1560080364811081111541d1f120300041f961424144560000300b41100070500140d03002d0030039035500c803001400801e14560b0300d00410b01076803000d0b42c3e15400350300040c481c520f07180c10300c1d00303c03120f0900900e81040e0081c51883d014081000148035241e0500c1010800c0e420318031a42c0c04a034643c1f900420110b08090700d03424481d181d0b40b09442101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 95200135 1250 95198885 95198897
    0x60f0b0a02060c131d070206060103110405040f0207080c0304031e02030a030c030c240c02011b0807170405010507030e01231008060a02031506070f060902060c010f0c 73
    0x1248411001120612003480e400380c4801e86520390f581e84a034129400030038000304520f0b40415a400c0528100015900311019402d55081045005e418068003900b400c1c101803c1c5185501c800c0543c03401c40d012120191400a500310700401030100900030b0003001001600006074242d004c0d10000050415a4090100703000d03c412590340a616418403510020f405412811003e0302103405a031618000601904003004441a02d45e62084014801070040010009403140e40d844c0749480d12a810300c1102600080060070910500880d50040f0304008104002e80440041d072100d1080c1c11001c02516440d1548403582414541140a000100d5083c0002481c0401e00300310030b0814019080704168600302481c0c072007054034400c911548020884c002e0007801c49000551703020100800741c81800c001d0b0340183c582c10084095a015404895443d100d0013060007641c1c0401c850780c131000b80312588030400040c2a851480403c8160045103c0303408694a840711001e640e2041f40c0042c41c41289543e969 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 95201385 1250 95200135 95200139
    0x50f0d0206010f0b210405010e0115061e0306030210020f121602090711070608150d0b0a09020409140d0905060408150411030d0507120302120408130503060a060f 71
    0x301e0360344109204071100c52500c0f0808101d4108410010300e218070181c400680f400703410455184500324107440c1168103a541d00501e5661110a10555011900c80800040260710f040ea00911a191007030150050b00100041200814040c1e44094001c40d03002d0304402918600c080c000c1d4a521024400f10282c1c001c0031540760a1154080846540440204d9040031103241902400541b440092140c07081c00001005000380550400c850402450700da80d400c040b03031900803440300d642140f600c00c145c001e602d20311403440000c103000f01c0c199000541134000100c0381494000a00940404030015140510340d40401100220108840000354280d498142e2075a650f042804007521580c0300b040d401e43c103c0a80815641100c4d0720498105001c1c010f0848a1926400080e0400d1170713120035900072900c0040e8000c01c1006040111a042c022402d0840c14502011070414050400420003004008001032a00d2008181002030000d480060110380e01440c00c1806103004100c54003e018201042400c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 95202635 1250 95201385 95201387
    0xe0405250815040207020109060f02070f15020f0303040f0b09030913020c0105060d120e01050d0606050304031412010b09060d05090c041104050f060913020307200c010f12020c010603050f0d 83
    0x22100606d5048c0d440c0034036545801403c0300e4482145078404214000c1c488001495243c40c801103018200c0780c40480d0104200c8800640382c030041c0c1c42d0308449900140204008036030080c114910654200d103400304540e5032812814110300c43c2c10100d59000da0030030385003460505650301030881280400c0c000c000c580c80b100c3c2002600465020002c01440600e10180c0105100da400c0c000c24501c181829030614100d400490182d5000d074100e00c1c0020b601000b0042407546c011003c0200a4051492500e065050241c0c00101c1005010f00c540c40e51700003c482000b901e6800c122030180001000c10407081c1401c2c0e6941d03446000015655219a041c04030406a409200c0225400c0f900010481002110041300b849440e03045211100d03130000c840c445a20b40c145076800114460303200b5a850101504801d101c0f82c4d405c2c0c0112282040c00c8d404020034014030b90f0001003010f071469260414900441096101c200680300b242c80621065090600000400c900080d07118a005040f0064440803045140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 95203885 1250 95202635 95202637
    0x801050f030a060b060408190201180e011406120f15010201060b0301090b030c03060c03060406242a08090307080c010f030e010615180e070e04052508150402 69
    0x40140c0d040c2c014210340d20001d942984580300100000c0c2603a42070564608030301e41404509800f01013401014450482150f900043d07081c543c016804101c10000c0c20312969691143c014080c003094198042054003950740e690043d512039800219a01240d07140c056008154510142c0d20302c4000c8000c920805595030041c0203007402d443c1e868030701c103003168030f40742d1000302611210000075018081c0081440d4583c4082c4041e901c01d01c00c0c03100482e52801e02034140403c4504582c0b0055489000c068850300441603411340340c95071074440c5040f4401d8011080405203001100210034082c10703415140104009101e4013504204004030166443c060ba20b102442d01d0700c5000100c2c0b800a04078031507042001e4040d40c0b2800802c6021000000d0080d22002180c403150307104a034500c0031540d4401910484952959040b0241480844003405030400c0030300a40072251540740f840c802c07600c4000050b0742e8a1030304003850210000003d80403400700b055001401041041c0c4842246489020b5100c0c25070074031380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 95205135 1250 95203885 95203909
    0x708070b280c0c020415080102030705031014060702101101021b010f060302180910020a0801090f09170912010911010206070e13020f09030138150c030d020703020303010303080105 79
    0x1d01c1d00200f010940e8200f1000f0441031000003408032070074002003103a01d401d02c003461040d8120380b10726a603414041c028624a08155002c003010381c00714402903660380c40396816668042e03410b40c0e07007070107800c0349001c00e49400d80c02e1104c958076503101060000010040417440d0083e002824020003d1070001d50f03046007902c1c2c0901010350080c1504040e0003a400c130000801e030b40082101e0640d840030300c0d2a10504180da010038011400a40a80014015455544985140c3d160721050820481085d65078041c00200302c2d130041d407403540b0003003082415611110310103a030f21201c0f200200140105460720503106d43c0d03101d1181c1d006100341400609044c1c000d102d28007440200905d510a19121414880041d43c040c640428035450b050111002c2a182402041200c0002d90b850300c0055555101e0361003a020360b010120105074610141a0b169190014040800c011004e03a003a5100d801a0101c3e266200d01400d62860342d00c0026154141680131010314180c901c640d4800106982c0da03000c11080c0011a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 95206385 1250 95205135 95205137
    0x311070203070e130507060305040b0a0509100c030b130c03060506040e060d030c050a030207051e0121020f0a03050a05060405040b1503070f0308030411010c05030a050708070b280c 79
    0x1c4109101c42c03c03d010751690b0052561600c00125034550b40c1d41c82c1441d0055003c070001c60780304c2050004000741c0c00d00103980003a1104e4108403034030f4020344040d42d54824107481c0c04c2880e90b44551040d03441c440c5d00b02e54040f030409001210342c0709100d096900102812403c0b01c002030b01c0e021004c0707000e01c0d05204072070480d6244441407000c0e03207540b810840016200360049051200404840000035802c1c81007805090080d005000f100e4540720611006c0f80c03580221229449500d03016440681e00201c04148204000d810b542c04c0014032410f0b44001e20418290807076403a030202d0b0100e401039154004074440c1e80c811200303010340d4813240188015540141c030000c0801f400307000004d26075050b2000c0c01445580040c12160465698041844c8041941e00142d4855500104001c2403124980c1d200720700103021311b450f400b05441034807001e03121300950740010704003d800960f1800b0301c440c01c816030b0b11098009801c41301c0360034107008400340108070722104d0414481e600103a4a1000681c484c2c00041462 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 95207635 1250 95206385 95206393
    0x1c0203040b0406030507030b0d08070501050a0606140d060905010b03100e0c0304240204081e060408040314120f0a080702060f130201020a0503071a0c03010b191b05010c0311070203 79
    0x1040700c20b4001e417000404810404d030f986d10081c100c681e550010b482c0d600780142c0300b0594500c1c03d41451400d40c0c03c0144014250b03420035104109907075102210301ea11b41c100b21590f035110000c00620303a0192003030394006400304c0d060400102d1881c15001c0254040e48070365008112170340c6c0d1440c0c841050141114542e008070814000a00031030304607400c1c00c035042200300010b040703040c9507510f020880e00b00f42c1010016a000b0a601e140d8417070f0849469601541046c020403140c038040c4c0d00c01078540710341d020050000c841038100c030850060802c0720601142088019984902c0548032050702d030b4001020400c001b5402c0c401051140d070000c2421400f590882c000c0504541c0d42c03c0007040c0003024240c080b0b045103d541d20010104100f440074201c0d2500c104054142c402d4050040800700501900380d06610b5002c100402506038004103c1c0d03522040c07800c0e00d440c02120400140d41d0010561100b00d21180f804200c4410004190700c2035190168580702040750701004401100c49005070300c0000c0d01580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 95208885 1250 95207635 95207639
    0x3171806060609030a0f03050406140c0c210109030519030b130b060c01020301030b0a0605060c06070c0c050d23010c091202040b1f0201060e04031d0609060703021c0203040b04 77
    0x410380e005044143c0c0c060111200f00d04103030fa82510002154000b82c0c0041c401203010700c4082d91092206542100c43c0402e1400d002d161030002c0d8032001c0c0030700b145108035181d00e18092651004d03139582d9801440c0034020808004035060241c0300741e0005c600f04010142c002090541c00f8001e01c18081c09000180400402c03207100c1101c14001c007800d920550348041e0510000341d080000340001c8d03000c1c0d44513484031011402c0440910040d50001e8101034400c030010701c0000d032908400142c150303025030217141803003907604541403800300c801c015000560890002c45608041c00891682d80f50240c034454103105850b030344d010106003200c1c0405450000941844800c000d8113680c1c0350f12071642400100000b81e00c08292002840034094002d014446c100c0b007003900c0c1107143e02807244a000701804104d12116151a640041915080c2d4140324501c80c056280512076841340429501a000c2c0600307441e42d1040a41400303943c800c0113143c10005a4000b8041d0003000d4404001d44040b90704450100b42814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 95210135 1250 95208885 95208889
    0x5010510210302010213090912020d08070e04140109090c06032f040503011b031104030b0105040f0b030d120501080d0f110c150301060f1112070f0501090317180606 72
    0x25281ca070040e011503400f40061150110001005001003c150000207004030b20b0f03282c4110f048047e90f000740159000f000d06110b403613402a00d115840703106460079114000714a00040c00901c100364031400107408010000c51290040e61107915000c3c05901c40e00c9040c2e0f0350b5001141550f0525000c0d1030b190101c00c82e85040088044000d81e00303668000440d60802e5110300100b400c42c2d0304001081c402c2d03d40348014480d51a010f20410004d64204a8014600740c219250344401100c18410f80340956522a100c0d120082c80741d004000408006058034039201040b40c0091038200301004c1c10362540c0c5094000112100c00042481c800440c2e500d614445610011040d00c03640316043d61000c3c28002e88841543c940e480040c8110400441d0f1605622541401d100400303101d05246007205100603d02d600104c40000030340f282c4200800e0241d0383d40c590062410304811100700700014949d60802415100701b60704030060000740e110810085080340e40340b0b0000414640016a006910381000c00402c1c814 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 95211385 1250 95210135 95210189
    0x10b03070909030e100c03090807060503160e030a030503190b09060405040f0b01030501090c0806090a0210140d050411030307030507060c0c0b07080105130b0a050607020409050609030705010510 85
    0x14500038204012100300c180046045c000790b1046250004405c0141c41c000c140e00700c0c5095002e003c4900c010809181080c0c8050590301c00a007240d02c42180022000000c58460f682d00300351200c019044d00c103143d03200e01d805009500b041d03c0d00402da5075604018504403440344100c42d01c10760700811021070313500d540c818400100000303841500d084070710030f21200c04201041c0001e030003503100f580002040811401c162001d80c0350303904035007801e07003284c0148040c1460019001801c0d540440b20b44569107203549003594003500c15205000d0252002c60000d4a844295003c01c0c4600e0060501d4010503040d181016103031b105036200200415801d0290001184559112103d80307611814014034001c03083d21351044c90f60040303075118005500c420046c80641000d50400200c1c1039050400d1149601040004180b1a80d2f400f405008010118006096544680250048a030480706903032036401c204414030345070f07070011406076019800e001c049007100301109203242c1260a0381e1075802d00915028245100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 95212635 1250 95211385 95211401
    0x70206250314181c02100e01020d030608060703050c0d110705060c0702090127050a05150a182703081501180504051503060a06050a08070602060f0403020a08071a0603010b030709 78
    0x25540f1028036013401038942c00d030381070801c0d801600d8100000780c01c100024980700109503030404250401104001c007441c001985a0009010304011509645040801c201030042652000d166400d10003007100c000005c42c01410350a000d101518010783d295030441c0e44a200b0518025049a080c4004000c0103203882e540e81980b51503030410f55501003203540808103446047d545280d21a54030000c2c0f010b51103140369126658241600e00200f017511f82041d51006221901d0200d56281d1100c2d00b40d0706040781c00140d00c0d4030b5400c41c907a1071210062400c005002c0b003412600111824000912406150300031080740b03104d070000490030028182410284405401d02a1035031080c00c5030080001503640d8107010340c1c0d100380b4440d080007035100c1c40d150400010360706c1c950094000703400c4610305000050780031860035840480c040100006440c1c61070105e2420100d42c8010b403290601050990070809403903402e405245005c0030310700c1c0a80361141010700b01c50059100945c15170145000b0010303200c00341c2103444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 95213885 1250 95212635 95212669
    0x10b0304020d08040905190509010e10020c0a1a1812040303110a0c0314010b0d0809040903050c0d080a1d0a03030c0c08030901051f030c0b07020625031418 68
    0xc01c4c950741c1c030004800c1d254155903190b03d54121b028807080c00c0c04c0e288503803039024658000a008000d43ca100b03403620303016045500a280f80e000203030b40361540410400050201e5014900048040c1e00200b0b003030924400344c841d00d48032561905d41021001000407403060b41c05d20043d1661809140d540e0558a12500c800c03c1d00150081020000c0840c7e0303c904003e00a601800811107400c195014081c2103401c02d40300c043c851055100c44e000440c5800058a61150003601c0c00148040c107030a055905001b05034203852a41b09410b0030781c6a0b281d11a00712406000c0402d018000842d03040810b0704043c402d492284041d078000322408002c6403003a0400c8605402c1e03820f1689525507992101c1c56a0f501c11100e00c081691102d080c07003041540740d00207160800c420301c0d10803080ca0841d694103025030302e244100b004064020407288150360b05c41080301c400c00d0300328200e03440c2c00201040c0c01f4100803420209401080a10281e1200ca22004040f03c58000d201540c042c00c0c0440300007000000c40404040407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 95215135 1250 95213885 95213887
    0xa060c08071e050d0f0203130203060a060f120602040b030703020c01140603030a210903020313060302030c0d110906030f160201050108030405010c0f06020c06040b09010c0c0b0603101a0a090203010b0304020d08 92
    0x5d015a020384011801200d400040e403008075460b00501d132519501515002406280801c1009201d600c00002010b442c00429040500140e600707240010b40180d0f006044d02c4100081408503240d0182d00030003000728454000e108034000d2218000c0012001c40300e06d43c03d174000b00824081240f03c0c01e40703243ca550700306540d039942002c0030703075594100c03000490100d001d07030700020300200e4004407085000001c00307862800f27502e1850a400c90007428010244400c3c0040d48a144511003c800c4206990076964007a1000d030b100e140c5000030301603ca1040d1b03103613021103000d01e071401d41052040c003a041c10f882c120310041d49014074000044400d402e0401d416030741403610010070380002e6402c0c00108500d00314000105000d09060500511052020780350109030b038540540000b541d40c100102d59181500216441c1680e035403003020900700320100604880a5241121181220482941c0035210300303030a4030851480e07038903085003c041380b20a00440001080a200142c010315180060403241032040c0c0d111 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 95216385 1250 95215135 95215151
    0x604061b0219090903030506030106080a030c0515040807020103051807120206040b030906070f020a0f02130e0703030207060f030b150307021501081c051305040b040207050a060c08071e050d 83
    0x120303410380d01d8100d41a01d80d15180000203240e418000c7c40d420032000c030001c100007860502c0c0b240d5500c168100080a11400402c22070500106000b42128440c190b612000c0c98074080ca03000c1c0303266000c0234081f80031910305004142c826040c6900000d00544540042070700c1030612082030f0440300c0b404401c903803103a01004086254043d0501850180c4000e00080c2118145414003500382c1003029038074003c5503c000c8801010030f00f440d417007007074060b0151a006095803016242c2e20142c00072050302c403103600c20b40724000201580014840304a40e0b160f0341d0b0107030b040c3c40050f0407016030b44c0303491482d40d00c40700d912503107102501c01800550b00851140101c5400c400940c02504c2444070990001e286034004183e000b2a40100b241c00c0112000d1500d0030314540902c401401140e8242401414065a501e41c4420303115111070f812642d0940d00017040b2402c0d0038403403425002610b00140c41030000768528021496280c095806c0b881c4014a104c0c00700750348608004216030030741140951100098585109d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 95217635 1250 95216385 95216419
    0xc040b1207020105060d0c09020a14190905120601090c0c0210080411013e0a060204031110091205031908040b0c041a07020402070602040b03090c0604061b02 69
    0x14401100444250400303440c0500000e421900d000700240c0c0280485220240020824000c0c00c0590b004c80a00503168040c820b0308440c0034a806900c100f100000140c40c100002e11505914641c0320155070b00600c850301c8409000844203170340e2001c400d40d03103c4001480b4070300103504001083d10350b501e000c0845a1440c0c0019554030003005103540400c0c0114240000d002c007184005510b07a5080c00c0400e01c945034881300681101001e401c40205240c0e800140c0064040358081408503c0c081080314241c04490620000942c0948030480c0c5001c680140c0700503602f05480c031800c0e601220b441e041d0501c1d00d010750040c00100081000c69090004019040e010080f40a58403010182641c07030721468070345450181c8249030050540f220b400401c2c4000c00002d4101c040c0301d07a41109450790395464600034804100a4000d240000708175500204001c00d85032000c0b80076600c1901d40740304a840030700e0b4640920886200d5801039400041c030311300c0c5079504503481000304e416061020340071001440c1000b40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 95218885 1250 95217635 95217637
    0x80a020d1d070b0307080f040f05010c180504090b06060d0908030c0d0b030708120c0a050714100e09060d080702150a030e0601080a23030a02010906060803030601170c040b 75
    0x50810809070380d65803544500020007a540182507411080d03403440c00c01d04e001801d4044010034108199060100003010003000c011010403d130f0b400300085c0541c071281c0300042e0138400440e888000e80081d400002445107071500540b4207003030b004801041140c079007000740001c1394012004200c0341a118804640020b07003030001140700d000e414038110703140c0c00605a0007041d144030840341486a8000c0500740510400800d40880c00244807070780075500d8074800c00d007034101060701e14050418015820002489401c0401340c8082450031030740103110b80403101069922291a4540c15004a601d80c009482d03030912810204003540a849454201942640060340121850040421505000c18003042c3c1603058081e800101500c076024046560400203c59944c8170754010281a1079003003c491000c542c044020680c2030303800841a80c0d6100741c9241c029020b400301c0101240c180340351841c0001e446802000352401804140c1d03c40201040f03030b0034800d5072880041c0031908566020000016214101c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 95220135 1250 95218885 95218901
    0x160306050721141e151c0b070f0804030504120201050d0903030f0e0106030503161e0803010501090b0901120c030204120b063109030201090206040b120c09010e01080a020d 75
    0x1e00c003141000300800115003403000900000c138000609020800045001e035140740d4480c90750b66106090724881000903100100b03640b404188071848070310b10000d1000c094806803240000c1d4543c1c0000c0603181ca42140c140c181140c018002071000c0c4400e00c4000003e041070742c8564014506141040c400e28031543c111200658100c020a076160007101005040707010301c01c1c0380b40c8040e000300011445c545581c1e4580c801c542c000712074540b010f0715900411491000000c02c01900c40e80c196204070305840c040e0920303842070241d107020610f089000030766400040115050204107039107266011690721b0a9001601c0044221024140c00344808181c0d59410007240d084540203075001151810f1440c20700080e0046c50603c0281c54029030041c42c0f007014203000500d00c210640d40f00180e0000302c0e0034102d00400c11150029446a000500016017000e031101501c0501e40400380b10080744c580004041c180e2140404050104407103030807030700c1103600411b20682d011819240c00f51404104004807002c581d500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 95221385 1250 95220135 95220197
    0xb0d0c09050901060f050a03030c06020d0c120b0901050d0209070210020c03040906090e0a03110f060103030c020f031b040f0209060a030608060106020604020f040c0e031b0f031603060507 82
    0x41c004010740c00c8024003814000700020480711301c0721404c0602054082c01e05000240c1400740004900d0100031060f0304458081e003031820200300c01c100c4624002d000003448541442d1060608902c030880345403100c1050304850000300400c03480c0485600b07001e41000010b104c1d13130540c0a002c981c0c20074003015000400d00c0400ca07002840c0c0c4c0342d060a10100c01c44106070058000145031103c40441d600002500c0c10703200f90175003480342c900c03001718290707610f0701c584800c50b40014000c1d0000002015041105c43c07520328400c40d00b00a0300140001415914442e500001607002c0ba022001c3d0101e00b0103a001004101316a10b01525240d19500031610703941c01160110300191b5543c00401c1058018040c1c14050002840500740c641865000200740c10503e484244c440c0341c2e40c5444946043c0a080d1401864401400b68ac810802403071842c42c1210082000d6070044406c1c120b00c803030526002c01d05801081c080e25065000b40e0564071a40c0050800a043d941030041980300071404001c61000c81c03c4d01852 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 95222635 1250 95221385 95221391
    0x7060c030605130501150503100b07030203040612180b061206010e0f071d060f070f03030501170102040b25140f07050f220f090507030b0f0c04090b0d0c09 68
    0x2d424140461107401e20450780c01c1a01d400c00600c9800441d8039803250591161800d00e4594489401840c148086540200b1042100090714800c058002c406041107032402d403216881d1f0700505040c0c0d002e40308141c1d005a8081d03001107204000a10582603035401100c05080050880044007070245840c20030f8000c451041001d80811030025406d000c010b621464519207200c41001e9107802c40900103002d65010302c1b40b107000c101c40c9060b0500700c0942e1991600401501484009420003500410b000c0c0989180707a000002c0380c910b0180d05000b11821078604504083c540040b03c510015030f032070040c490a11a01e80303564820046000d11001c0210b01c40c014002c0d001d5500246119450415660b0001e809103d1040208655950f90b42c012040503520040707080c0140c1c09800382900524135500045001844c008480c002d1007030006011056034428444404a83c440c440300040c00b100440d54660600ca08000030f0050f465650010f8101100143c00f030101031200344d444c01005240364000070100c9135 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 95223885 1250 95222635 95222639
    0x20703020a021f02060f04030c1203021e090d0206180a0b030f010501030c09060c0c0e0c07140102120c070602040905070305070f0e100e0a031e03120e060105040c030207060c0306 78
    0x54109550f034800704041c40e401906041c4100045c0d198a401070440a4940b0020300207414540a40c2c0f21140d503503400a14850011003020000d00290002222040b9440401285c04100d06c4250100ea9050031300402c0b41c482c03e01d881d0300700156948240604c0d0302a1405040d91040340d2144241c1d02c0207861403c0805490346003880e5001c4901e4016402541014203003400c400c600c54020f60510180c503005d140002e04102c080c2803040150110754007402c808150740003003000048420700680841c81c800d42019113043c600351400c0c0d00b40d00880750001d5800d200c40c804030704c019a4002c001d00303926205040250030590380d0b094042c111941102c0f603a000c00e84541c100820b0070ba00c040c1940c0540d40a050401168400300c0c04250418800750f00d44043c040c80304108030142c0e64541521000b16071005c1d03c40304402941d4010740b82c28001c0341045010450610700455481410b0041c09904680c000081c91141e20784001c210181880440c40400e040d1300708030720804140d403801049110718171a1004240c080c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 95225135 1250 95223885 95223889
    0x10e0102041701050c030403030b01030e0d0f0311030f01120c0e0f0f060102030c120d060302032d07121b0b03160e0f060d0b01020309030a1b050607020f1504050301020703020a02 78
    0x50220b01602095900d02410008030410743e07010b980d04160149000918400d1010058004110f5004407400030700c00d401c950086103501a402c407000e80302075074007031000800032318a2072440d0106031801440565040018000d8040b0741043c0f2031010f000355243c40c18941d54156190202000f40c8007045107482500030009503090004d1519000002031008524040f04150305075210307443d0582020007803000003008100d14202e038116201454000b401d66154403400042c0512423680e405611840c100d8406a240d6010340c0400c100e0121880344240065450181e17540848154950030903030340c0801c5011001c51500c810308041c1d0300c030b9041d43d020440d008c0981c01010b845141808800c0b4462841406450070a84814041d108180c9400300701240303c070800c04c0180c2c210702503c042e20b0380500c10308900b1824030110f001c3c505010342c82c0f0300050802a0b19003082c0704a07031003072620107504400c02240603002410072482000500b184000110700f0309460340002400c1ea40a01c80a40040e841031948100394 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 95226385 1250 95225135 95225159
    0x12040b0a060b0d05220b0703050603120c01050907060806090a09050115090b01090f14060304050a050f03030406050105010c03090b031b0408010e0c0a030b06011202070206070f0519031d04020408010e010204 90
    0x21018081700da00c45000d0564600b071000700020320f49410035407171b04082211a1410001540a038030a603840075118400c03108010300030802112411100d101c0c0e24070000d5100d000f0101c05020f650050b2003082d072540c0e511034580180000b06c6c0211515076840c081a02c55560f81c9520401401917000c000ca002c100d80400103040d0700700364020781e00b0a040044104003400d544200704541500603a80151207a80d0350802d90705124240c80c010b4040e0007007024451030101d001c0b000354440c500c120f000700714698a50b00115185d5401120003004680429000d0003c200c4400c0a50307030020002c0003a101d080003085000010f50810790000d0b42680d1100305040d03802c1024860148030720015902584800d2a544071b11502c0704001e00a10f051119040402cbe40c3c0c00c2c0c0940481d6200d0350040d018030754540151504110742594018252241c0c020f1840d440d201104081050440e140c2681d0740010508207102100301841d84400f07802d03070007642040001482902070180d07002d550040c0000680300c52410458042d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 95227635 1250 95226385 95226421
    0xe0403080a0506012133060c030e09040f0c0e090705060310060302090d0c031b0603020307090509130204050a0605010e01050c060703050604020d0510090b030312040b0a060b0d05 78
    0x5160030300c803c019460340e0051a00001980c050395041d90381e4141e00140c401488140480702103419035501d240c1c509040c00310f005000003074008100701120350b10b1600703d400c1d0755044001400568280101c2d6807524001d05080d400c2400303042804104030140e941c0ca080750704654048140b030345400781040030f0301d10280300c4200200720035160700f482c501e04000210003840342c3d8043c100034150301282c084100c1d02c50034168648594841101d070907454881c107090220794180150f034501c01002950110ba020702c41c0c02500d000d0030094540006170360a241c1048113030900242082101140040390b107000d81e556000c3c0f580110841a40000c8440c00c0c03500051101d000391046a06000013080040820180000c0c9583c3c000034901d40010b4079101c1c0c40c00900a4411640c40402c10f07403d05003880881310044180b9400c031b403600030003040403450b0242855224000d00403095480143c05001401062000400c40d901c00c101910000e1026102d0340646204c6c0c22074141c45100980c1c60781000507180a851301400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 95228885 1250 95227635 95227651
    0x91a060a08150a0303051b01021b0703060506010306050d140c04140a1407090e0613020a030b0102010c030e0a060203090c0307030c0e09070e18070e09150f040201051e0403020a0e040308 81
    0xf01482c00c0d51400b404520541401182c0407041d45040110407000307505965404546e51420100d4600020266949020500040d60200e02e0240440c51a602a1141d442102d0b000380c020400b09569488403080c02d81d00000b0840c40b406060601d1049540b18400c03040300b140883d41000b401c0c00d0041c1c140046076034006c0c030455514160406d100300306401417070b900b0032148403003040d20065440c5400318007421401c0d5407840600c0d0021422058031505130304100030003d402e0f0b008011071084010210700352070440070644480c0e042000000c000c034030160011039008503864200d512201c0c811010a02e055584da01c00c0c0d0b0b07810f001d00f00601121011902454010186c8001091643d00300416a407030500c020b0180c0c010406445d1010301e0000083c84614010412a160079038945420401a0344031640c0c1981100c0200510300061007058148066502464041c2d4500d410000c0c503201100700d03090014070b0840d0b003920500001006a0311210750740013608807152100d42504003450060452203001c0c01c052 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 95230135 1250 95228885 95228899
    0x8010b1008040b070207030804090903020c0108071e020a021527100f020a14060621030a050702010903050109080d0e0a050a020f010323040210020d0504091a060a0815 73
    0x82034154400a09a04981c000042881c140c0720404184d1030410b41e075000071700d01c1300e001c1350000c0c171940b0307660186810368041d4098903c4032445c940116040c0308110380c2940455900c0e1400410701c03110b0320b41c00040101e04d004903a100c07046500024140101041d0081c030300c1d03070001880c500c00400c90341c2c0d042000c0c480c1000300174240103031030005400f940b1040383d5800308181c4001419000e4400c11605180c260000303400034244270060f03651034032220210382c19801031010005051422414801e450315201c90300024600702902403204540d1a80600b006030704120b0200740c0400810420721a09100c24401c11a050b80c40c1d1556200d0701c26201100404e50b11b64100300c1c1002c012072808a40c08240030307412252041442d005d200107030000c0c8070040070004130940701d140c00c440c82501411858082c078002c031031620310101404022030791070180e02071080000300e090100300710081325a08114141d80e07026680301d00d41c080000c00729075140c105a0100000074000f9060041d02645001c0c00d00000909403844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 95231385 1250 95230135 95230159
    0x20c0616020301180b06044109120d1d2b0c120c05010e1605150406120f0207020d050a021305070504030f0503120103080a020d021f02090414070908010b 67
    0x60010202c008103141d000ea512001481100d0310800060655140e641561817074606920342340d015404600c2100000600c11b00000c81c1019100194011507140a003034414541070305a03076a0000b03403651040348400c9040d140200300c1007030341c00d1264003000300118148100740011071011502c8148203820b6502804400200d84011031131020702903900480a05103801c860344d03a4036010f4018000244012000d004100851300341d0b68100c20004122002140c100d0704020b10655070030110301c0340784101e101107051301c5044080305000740c1128010304032002006080007001c0e0041418921a070404070f4254010b6450201149042e0030362060311042d0b05001c00c42d42c40c205a010b4600d100c1d5000250100f075000b001c3d03404101c410000c66072640e820341041d4425596030b1400d012190084040c10b000760091005403203401c1c0c4002001c4c402890417084010007a05016140300003980032050440e000780d2500c1000c9000301c404211503002da00c140c4d890b503d0407440c181915003100d500e40030b918403484803541c0c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 95232635 1250 95231385 95231393
    0x527010509040e1e0309010915080f070c05060109141015140c0f0a051c080105150d1508010c0509090703051f03080a03141006050a020c061602030118 66
    0x69600e285020b4800140a503455401c051030202040741080000b43d01542022000d0030100103001341406c280c03a600d00c010748514504c02900d21807410180011204000104814810302d4103e0b0003540504110440013200d88489050034000d0b081f0500058454445c1601548411042070340441145400c890180c10700e500e544100313200809800801c45c0603000c1c904500c08420482c0c000c0c2c0f9004044404605207100c0441d100c2070441e50a07203003400b82003c002d500c031000040900ca00c0f00c0b55650013b41d80c3c2480704020070311400141e1001580024811710343c41c001540300300d84100314000c3d05440010325220207079095410303581e0702c403081140921a0303000c951540380065800004078100403429a9594861742420901c504242601d414246400014454444014903003c1c40c03542d0248030000e1005029000c140041d1122480b00104207000c0103545e208401800d00b9800798411340b07032034620b46000914150003203c14a180920507101020851609118101c0c2c0000450b141401507107050312 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 95233885 1250 95232635 95232637
    0xd120c021513060e1504090504020301051b0405040c1106040302011b02011a040c020f03030106080f06090105010509090a15030b160314010308090a0302040f24080c0402130e0705270105 81
    0x4922810700c051262132141a50b20000d019807a0b610140e001501d031590381c40000b01038803068034160b001b54a401e003c2141898845003101c240c0d104600c200c2d02c3c203031525051000608444800c00c0c20030070031520101c0074880900026024900903400411079050fa2490190324030350186290055a1501003503441100b6000c0e00025145012a400a061050440c090b418460002c0304000711780000000400e1301c5030402e0585004501508025040f41d42e00d40038410024000e004480c0030aa0601c4030364210325140c8445135004082000101d1a003000c007041000c601001c1d041150410400407c000101071040c0c003886800105160601014489400b0154688018040900f5001002900c101c0c00d480d084071b10001981d02a104010a0a6040c0094010b0032780350340240c5840b10319401c1c000510008180d020595080308040e0054102000c2080000d5004400300018400010341c005490b0749503c1c4824410982d03522265031f2980ea100d02807103040c15038410202804120402901e050b6403040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 95235135 1250 95233885 95233889
    0x30b10090e060303040f170f0a031205040f06060605070302011b0917010e0303070306170f0705010c06150b030906090109150207060b031b040b0102070e060405060d120c021513 77
    0x703096024103407242c40100f800c51217240c00841e400040c0c0d90000503c3c07035211800800c10f8080405072900602602d002a484090301240030300000d500400d0031081c55071a9002e140c21601c25000700180036650ba40701c4055031081c1d809180410700c040740000600d9020302540101c1c24a0380442c043e04110303c0c00150241c1500c0c020020407616400a81e2900d074002d40c050f13a100c0c0c0009084076200e2400f480c3c02006402c82d80914040c102c102114010b40400014203410091070050107042024202001140d40b1605400180c90700e544540113021011148941d20001d850030a8120b5a40d14148040c0e525203400504440315507031501c0146c0021a101d05a10680d1701900f42000d03942e07004504102019285100040da854000c100442030300c5202c0350741c40164813a06480c00e02850091f080166118641840b810944026450000328030740b626510203640010300511130500ba16403034440c0000d40da00844c07000081181500e442c015840c01111002c144103600115914000c2d0803c0c40c01e082c00e80f00c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 95236385 1250 95235135 95235149
    0x90902160609030c0501052a030925050405090601030b0906070e010f09090510060f110604060f0905160816060516021210050a0605010201021905071b1401030b1009 72
    0x74401c11010588280208104a130b0000021f104038181040314140e10b00e26840d002140000301c0140c021b030415800c2c1500e00c18401240035040f6206c01d0b0031840e0202012000280d024222100040b4560761140320b1a405007100700300514140d070561401080d080f03409004496654000030401480a03806032007807020080a00c1c242010800e4002c060356501400d4101c9081d55080c00100f100b140c206001c00004c5079010340e0740d9101140d1310b04003529a14a44c10b00100039400541c001008a801034010511984101c0000141d42d20300b619100e043c0b50107075030070310501d9180e00000c001c1d050342042134403842c1c2a10026243c074980707040d102400c5441031114400148241c0e0013400250350b6904100d007148880101512036203509009040d004003421034a07203201c00c4c030303000d40806d541d441442901d180401045101ea1a644c80c50006d80f9590003000c0f0440380400294511303000c001c0586038100081c0611500b00340004503007000034007500d0342945d64074014184546801c2070103a0001840040790b900d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 95237635 1250 95236385 95236391
    0x30b060a3309091802030c01030203010f03030e0a1703040602012003220b090d0210060b0406050310080a030c02040b040b01090909020a03140705011404031a090f1203070909021606 79
    0x300742d40c1841036501840d1201d1130103404103000071415031002c42c001d10881c19a07400c0564031005408900080c05040d10400b0b2011003480028040c104581d04400d0041402400956446400001180340021100590400f203020002c0603024005c1501c6590751035901c8a84280e0725403105000c2c0401040290107150504e0380c0303a404c01c03d01c000e42d020190031485e80310f1507152410b15540d540800060040044c4611528415440c10781c1c031520040d03540d190744640c503003032a1074402c0b6900e0f0006040408411007280f00099805003c0205100c0f00d0305c40c0d11400d00c001034500422044540683c0d60b0742c02507003011405141c580c2d0040300c00c0306444401c040041c40c94600d001141e6940580d800c024190910021201700003840003038130b0003c65400340d0340c0c65034260300342458000c5030089100090841c04000500304003c3c0f8030f03a145c0c43c1d00141c004129000a205c0c4405e0b40c0c030700b0b0201c160302e060306003002083c800c038039502042d4480a030041079400e525105900300c0c07207000021400805061195 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95238885 1250 95237635 95237729
    0x20f100504080c0a0602091203090a03030f17041208091504023102030615070503190311031603060609050d02040203040501150311030105010e0f160e0a030b060a 71
    0x18040050b20f58641605084400f02c000d40d18150000f90321081449200707015a40e0488840400001103903040c51025141c044031502d9594140e4141c0314940c200400c0c0b010040841126a600c440c14900c00c9008002081044100c090701a0200c1d01c05482d901c80c1e90800f50003d420000001c41c2c00b030b00940e060f55202900c250301c00400440056140c8850904681c0c40302d1010300460701c0d00030b58025182142d0710b9012a174840700088091168440040c0560030a02030a0b4100403801d11071070000185007000301d4000c01c0f0703508182c81f0b5401260051005035601080004456040c45108090f11260030005429810a40010702e8000c154030020320683e000000501000001e410070104525105041c81c2015100d00d1305151401840241502945c40e1100005030061084005401903441003884125600c8604003050290030b4224140306001d80030b007260219441c0c85003042c00031805207400b0b581c00c1c10038404109904030749920045420340d0a28a500d802d5003c19030b200fa20303036200c1785190070785a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 95240135 1250 95238885 95238893
    0x302060f091c03020705010f0504020901140406050a0803030411191802160f050105070306030201080a0b0d170d05060604150f020a0210050c060f010e060103110f0309010603020907020f100504 84
    0x8000b000c03200040322116000c0740303501e40c068000c0c00289118000a0000a054245010490b0340440c0c01075400f00030b210040000385240140c00010341c002810105143d604d980c00301d115100c1715404108554400001c000a00c04002c7c41001c1811080f141f1aa030800e0704d050703071b9403804410b0182042082107188045800390103581256031400100c81d24503581c8060382041c84445035000c0301038815500788400a031a2621034410241580d03816100e0004948030a00400020843c0c4001d80d81c001d01c103c00c210000c0b590268007140c003204280d0700700395180c24044001043c0e440187c05d55010f204140000c1c4007492259520b686a80d8062a20014a08510004a2800300381d4540a904944210b41c5622901d9100d03000307002030002e240449880b602d07254000d42010909200721810001d4120115070113620a0300202c03491703131000c8041410984903050340c42440e40140ca04c0e80340c1e07a5642c2d03020021410403044440d4030842c0c1d800a8585c050040b60310545949200c42c0c45403001f591780d40020108 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 95241385 1250 95240135 95240143
    0x806120c0a0305160b0c060403110c0405010906090c0905030a02040b2704120e0307140105041703090909060c042702071406060d110f010c12030203010504050703090302060f09 77
    0x4200400414205680e41402c503200d58040d050540c0c1300200850124103407a6034001c50700101101c0d001411550307119102101d99000c40c0070060310300d00030b1680c0d0b2803069490b0b00516001c0e000c0c00e50b00041d50307071403c503548084411008665040c00b20290f81000156004204860429015100484c030040082c000030101260802501d2112060381c3e0320665680003114914416440361341402c3c115452210151000312403124070552587c0320500911900700414450080c055040c18420b08050700c5100411419001c040c440815900100c3c081450f4500100d004e81c118072500050710302030400750032148171489180115a00030603d041140032150300445010752003e4910021034803050030b894080114080c14014032103a00c16800071960740d01d00001041d81180e44401030744082607007441841060505800241d051006400c464404140101d400c03030f844540c00d07030380140d0300c1d81440c0c2080102e810142c90f005c2010315010003800000e0b000900c9540080280300c2c0c00a2681d9050041450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 95242635 1250 95241385 95241403
    0x504020f0d0305030f0109090b0403030f0b120a0203010b0103020423060712020607020f0c0303070308061c031205072609010b03010c031413030e0603070512011202040506030a0201080612 82
    0x1c0860300c0c108406142d8000059030095940d40c2d1034401c0340e6a205800c6065802001c3c014050403d44404034001074001d50090a10520a807000b040000038980001e01840c014601540303941c02020b19001185000c1c0f1514003080000d00b01107003048c0c18860814840807505902c16503180580420540c107a0380d40303055641143d40500240240321688030f009464140a440301c102501c9044e8211003e00c01c003150320842c20302d000d4019130410b1001c1c0c4003144c19a034050821070304100c8803006106652840c2d0080e10005003e611000d568890a114003c120f8100810352410484404d0a0a05070401094201080c07030708075901c0c2d201070315503141c0c59004000000445a0540c42c00c085611400d82503041390f040c044040780d8074441940d908580810030300010600400046842000d98038600c1c0003000f8580003c1d0914000381001c40e284038003040107100382c03c91030302c010038a0014030862400c2c0c040c0c1c6503c82d02c180d0203003001050355800605400c1000d0175641c46a0710311760316008100810400300007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 95243885 1250 95242635 95242639
    0x10b0702130b190801200a0e0103180302030c1c09050405070512091e0f03030106201f06050402070b070516050a0b04030e030d09050d08070516180b060d0504020f 71
    0x203030410300f1550704031032040c6074410000c1c29402c0401c000c81140c840e2004981001901620f00e1030041541001c0303c0205c205908a410f00d66a04403030002003608412088400d48a5001556160001d446061414044c0380d811440303a03440100c1704801c01d41c05442c0c03100321a415600403a03962110001aa0603004480c1c03010b04c0001c000b005c00501140002e036102501044410322840d51403100002c90300c405489000850a43c400c20042260303503c50040144103074600d48050340c4443d000c008003814806107054000e03d112440c1c60304100811980715280c0280700071101140380c0040c03585c0d40510004010301c0c04050000104190750000c440000d8502840d038880d05940300c03a1090f140c5039010703007000d4070298002096292100c085090004050411541649444241d0ba02d420f040012108c851441142e04880a0001c1c40008104005011123001720300b20440da824202007000329003240e481c281e03601d8103003010b004800a4403081c08480c1840241080480c20741d031640046400250800002a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 95245135 1250 95243885 95243899
    0x8031506070c030c080c0108041b0b0705060103061404030f03050612010603032102090d200d060506030d180603020c031204030c1109160309050f01060b1e03010b0702130b 75
    0x140c108a49030641a043c0d81c41600d4030203609844060240c2c0d150381c3d4083c0f482c049803d03200072034003052440608604202500700b1164209464801c59007103504124012101a8401d40051080020901500034110600c0c01c0498580ca00354500400c0141410713004002d0541d90804591591030303100205803041020300003403190301d41d2403500400b51117500c840b003441d41c1d00458114060800900880b4580000103000f0303040c010720ba403a40f0350700c0012044100f5000c4a80c41d580210760701d60080420b242d500402001595103415000c0c5810040a1141603007000907003110f040c4c41480c8a0813070403c0d140686001a220a4007a003180c0c9148030700c600a401c80003003101000101640304d0020b5060502c6000c01503040e0300d080d014003500b00f41c2075800106070032107464200703e141d1007030380000f50443c05007003121000d103030b828603035400c443d02600500141038002a110b140042007802820b010301402c0b08036855985000c20010f21405103101c0248249440d00340455400200e41005d80490ba004103c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 95246385 1250 95245135 95245147
    0x9050d05040e010e090d110304180603123f0204080d02120a05040303052104060501080d050c071a0f120411010806010c080c1608061e07090308031506 66
    0x640203400610818004000e4900007244d0510302010503805040804000c105080e111070f0141ca1a43c60840e017181644424003000620404508040751014101200002c030704e4254240003a15050000144c02400600500140740515440542510100c588075111000c0b40e21464000d40d50190900c11404a0000c180800d8804020802d04900070442c0c003103d5400001194007007850081c60b0014002c100c1c140004c0010071f00810040c802e0b8020a16601802a5894903082c5c1211003074400307480300c9e5902c2c401407150400400c039844180c0a0b030f041090410400310085550741e140360007800da0008100b007004401e118075105641c1741202e0094429101d080007900e42c003503040101c078103940403403604110030391950061549500400049e5510300e808104c03030701c0b10006903002a803110b07202e02c01c046180300b0b00300d01c8040000142001001030446404c10014100c0c07100b0813100ea032551346881c0f0082c42484c0da003081c030700c008aa0f44610855201d68030f0440c0d0308021000010410f030804070000342 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 95247635 1250 95246385 95246387
    0x9051e060f030603250b1e0c0105060306130803061c0203061302010f0819091704030303021b0105060102100f0219170709062a0507030c0e0702060601080406020a0309050d 75
    0x950303c1a41c007603040700d00810f403150f2a10101030300c21042d07080f1031007030380300c188404454a0004c0440154054004010b102d6814010403a54440811a80140d549005008443c6018880f85400c4034042c40658103041c0c1d1a281c1c1074083c0300c044c0c41079114075100c0015242502400602c16503564004082d1542458202040411420382a03808c81c0000c104c2800610010b014400e464041c11005040e218200c405000010050007403940c10341e103003a05041182040341c00174000344041c51103582c0c0940c40f1108078074004450640c81d003071402039034100300401036548d07800565255140c00c641030104808a01e44d40c3c40000b481070310800401940000c482c103104603004481d407511841000034203015517944200071501a0064003070400060381054410600e149010391000c00d40d14400f1040100016540e030380c1d450110742d903004a82c1443c41c40410804143c051020300d81c444501d0029080500c0c04500082c1507060042004080c03aa0200303c400702c4d80e00c80d5014000d0780f035011007243c5280b890000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 95248885 1250 95247635 95247637
    0x30415050118052e0305011b0c1112061006020606040207170a031107030302041508100b13181b03050402030601030311190b0a06080c130e0f0604030906090905040309051e060f 77
    0x1003a201b56081139000540242241c000d219541c40320350341c6030240304140d5a511002610a500240c6c02003050030382d401c80000600610340190b00c011080b00400c0d00d0208060300380b2100500c00c500c907a01c18404600805c6041940008198814506599505a225082d001451411006034841402240400c2010303007641c0200195504140000040481c082044641e15011258014469050b203000c11200102c0000b4290002c0180003001d00c081d100d00e08101181140081c0c0c0301c00617282c0512602125100244c107080709450318060000b0300e040c0c0c010980c0d50f40e0610004080041d840403400c0060001e100301440005c0011401111414a0900c036918a9051740c030249518a41100000c500a000440e11128000540380081c3d124060030340900608400700301d540309000d0169000e842000c10300c26248900d01c03c1d1200c882d00303424164020003149246d00710315005450b00303040c803001c00c3d0015081c20440324200c3d2010070f102101c4040014070540b0200550f0044004154094000c01c104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 95250135 1250 95248885 95248889
    0x30f0612070803070201092405090d1e0b010501020d0905100504030f0f02040f02070f1709030706120f02040501200102130f09050f0601050307050901020c1005030415050118052e 78
    0x41e980407110750301c6e0148482d00e6044017549040f036801103268400300c11302840c081c02d030b528ac00600310046100213445034a50003601000c02001d440100110b18100710001850760f025140c284010714020707820b000d020f00429158058079214030703038100c6120001c5108008070303030203161700005841d0101503900d4031109085498400b2480b46042041e0044100281d1007541d80e219008003032100c02807131548400244604940c90821070f42d4041002d641161000c011601c000e0145030784100b00400a803188200311840310800182070341c0100010003107070781e0060804984900702c0510001070401e801c2064024860b81d400c41c02a450200c0300003134072002c541007500c211403810b4001d109950300c003030038001041012940c460103e04180089601c903032203840a00904203042c01120009600d034070000d1071000002401d1400110000100b00400c000c400c0d80c02240c204590090003d07506140700628100c008208503251941d0300d2001400c5c14880656900c07850b400c101744140920525202c6030f10480d014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 95251385 1250 95250135 95250137
    0x9050f0c0102010b0102070614040e04030215070c020d1e0b07092102010f081317090102100b0f0d06020f03010b0a090602060105090c07081207080114060c03030f0612070803070201 79
    0x2580d81880d994018000c00440c040144c1c0a0a0714500307010050f00d89080b0300f020841d05040c01e02000c20440050440280a140a50010014000f01b00100601c0d500c000b095402040400c40784980181c68074880b41c1002a40724441c501700408100900c2400300e07481c2000390048040b032092100803500803103528141e8021242d0320300d140480c40620900c0380300d82040240010ba0000d0310300c050900c07035081c240d0000802000c000071f0a03e0b0361a10410f0385416001140c0101c0d002854440a42e01004070000364100741078140f041d4540c442c000f0710000c2c008010303903000b0a9820603000800c03543c0e50496155402e40100983c40e961550640080c54025090000c049041a200414000d000103840c50486000518a52440d80c0b0142041d019070442e00302101c1210702440001c107900300541c1000d10811581c4d58540c0550303d490341180c05000d08a03070090003080e0400c41380341003580100c01c6a070300a0a4501c5003c0a44810010502c000019000010503000f05100491840c101000900c211b90007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 95252635 1250 95251385 95251393
    0x90602120f1503010911060c2505091f06080603030915090a080304181a13050604050604090f061d10050106120c0219020402040906080a05060109020c0304060806060d09050f 76
    0x22000f414201c40e141003000d041d00300f030300b50006141d1a00070000c241c441c0d0406c003980e11a0545809a8054004d00310160304110801082404a800d008219650081d41c00d8040302c004105500350170354481d9180144d1741002a428001150703900c0030000c96803040d001801a480118203404460031903081800c14500c50500c1c3c0200151201d40003054900303950354406041c9014024048290080050065250604111401d0301e503550381c07044640702c000600f00a000c40c140ca00300080104541e0003d110340e1041c0d140051240c0441d070703000c4c40761410581c40b050000356451200a50510750f81241c0f001040351048001c0c0011400650300000d04030b4500e078840004a40d0f001641800341c50362802034030300503440754035486a0708101480c0e0715040750015000501d85500e80b50a0f10540302d00340c02c1700000f6441034013a030301004420800d5a0042155141c11800e00590312250b40e240d01c41d6101d41c3c01005001004103995950341c2088800115204008001c0c00a003441d106888036070104021900307001d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 95253885 1250 95252635 95252671
    0x170604060b0109031205070c0911342004020307111605010509310c020609120f130905070c0203010c020c010203030a0c02120a022d0d03090602120f 65
    0x4003441000341503980c400e480503170030701826000300c45e04d40101800741c4464a00300720004c2c2c8003200340f080d04620891803005964030903180000014148002d040d4031188140980c80081da6440454818034041d0300595030010101c50b008044140940c500030f81d64414030000c01c0c020610b4000240345403500d08242901e140706004102e01c003a040440c404e40f800b08604000d4a8070724035015030134401c0c0c41e10311582e0070b0303508494001e00500305810544c400700d030658541c0304001040c2c0420072958004400c0005108000c581d0074098100d004e00385a01040d07000c0030480e58070394403482e1409006810581c2c0204035034644454006c20011105009034000c3d46030405107024079201146200721040107070000d500d1a1540b0b10180300510094603240118083c240c0264032006071407000b0308941c60305900034940440300da40c507511041103545a04491440c1c141180040400205000307201c0303061424001910070082c280000030b4400d80740040e071020107483c10070036245480880540110501643e402e8444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 95255135 1250 95253885 95253887
    0x1090c0b0f07020609130c0203030106301d0607180504050411010806041103100f060503010f030206070f0206070f05100b0604030b06010905060a0302040618052404170604060b01 78
    0x44a40d00e01c0c110300440811040c0003509001000f8480018040c0200e030b25030f41d034041c0341000c0310703c410580303c0180c000000411000750f02030160554a28041000c80002c034130050380c815411390120307041800c50385502c5190b41c0340a41d4494011f4035084c6106950403840c0c0710000400c42c00c01200089041300d100303000418030381040d2150a11070303a440380300c142ca84030180e0010340b03140100805250780151903140c03a4078111380010203140500503014410501e541000303c052803031603054010b001000801d10041001300e5104041c001107075010745490f40d0f1030303021303007800c003500d010140c4017940080c00082c502c030030400d100c402e610411380900c0c00da48008072141615020348808010160f0710800c1840140045145090340230f4014405040842d182580ca84c04a1072540018075514007180d030200b41000500c0c1c00c18401c484071054180c440c11164102070000f0500b4000c0007081147c02e45010405a1041c0c0f484216009800409480075400740e4241e200796542c5411036007140e640d81000c0b0440815 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 95256385 1250 95255135 95255137
    0x1092904060906030615020c0915131508010509030d0203250c051507093b0906010503030304080a08190608160902120402010c030c0b0a0b091e01120f021201090c0b 72
    0x40c0c25800b406001c09080100a45627401602c1c8042700b140460000c4030b640d40d550311559400850f2040441e41c00004003141c00d000405030b0100250f64100340c104180761002204641c64800340301e500503120b494010507080800c80c041c01c100480c0b9a03103144072001a4000a0055490380301c1c0d41283d841d60b900c02c921182e61074040e81c0d00804070b280c90300c0078000719034004164050420040d41d1403000030300007804210860a104800c10145800d40c0034003400000c20b01c642805440254001c51a5050980c0d0f0461580b1840e690b110410000b02d0104501300f4801242c2c04045542c0b040601102d0344a840d036684a680310300428a00240311200001e00c89100d000340c44014030102d4541400360380d980c0064440500c001400c500300008200e01200103000c00400501503d2420000030700b2000820620240050250444846640c810001d80c5030f251442c000309d06603550781c400030b00d9100306450302440788048040001e41c04242c0c5440e441000300154401460300e03015808411100f036991250b03501c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 95257635 1250 95256385 95256419
    0xb0412090503070504020d0906062606010806070e0d0b01081b0109080307031b0b1603110306030705010e01020a02030f0325150c09080a0507150e010929040609060306 73
    0x140d080560100403e15003580500100c9585a1004c10910032035a500404c41d001078004144281b4003d01c0d02030846802c080440480bc1e000c0c0007070112b541001c7e036140d940c1030300401c0f03602007044040d00341e43d0700d03122034503900c48003540404200803e503114030003980c541c900620340100440c0600c504103240d41c4108103d00882e42131001861400749607860841d0104030503a032851002e640b42400800085000700141d00c0b400d032905400e8004121440010240c0342540b01d0041d6489003031041c08107580e40454417404903071090912030b00b40d40d001030060781000c0307100c0780284d45400f4103081d0150303142001c80200080c0400303100d10804510241440041c041404801410300500086042244903640d40009031140c0079051003810243e840346000d01c0c1031b60003442210700360400201048002c0c070320200c403c02e485040c20310903610842c64000170200102880ba1034610f81015046244c451044100005a000034200c99950390b500d0b100060125406440346a00003460282c0c005025400c040e29514 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 95258885 1250 95257635 95257639
    0xd020c040612020d080405060406030b03010f060b2a0a0503031e010b0a03150b07060b030606040b152808070206070c03081810020c0a020a0801020c0c0d03030204050a030b04120905 79
    0x280c2e02e00c0354003804244002c80e030040b1007070032040201091554440b03001d40020051941c0204203142c1001c1894299441220008244c0741001402c0c00504111429590310322180d40e03030025006100f4681880c86072400b421034602d4003481400d4800d0100100003503200d41f4003038020050090059080044070103091142a41012040c048119041c0c480d4124086011031a0300005e0140c0d03e903002c4003035640c06403404039036443d0350300500400b504050208540c8204202d40410500011402180d03480103040d00c14070410303000181155041d0419085c500b41c08218900c101e0b0701482c4080050400e58050328020050b01c82c0078001040c1c280f01d0510074a4050381079036440030b940c490b00c80404560001c483e80d0b00b490b018902030591400160b1004d807800109810003045815654014050006501d0700301c600144d004104062043d000007c0070f102c0c20800381d51540e03a66440303090440090040360040d41d404408154000140f044024109005038000c8000341c4105d0960b00c000e8030411054400d0725 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 95260135 1250 95258885 95258909
    0x9050a080f0303130c080304060909050f0603030d0e011401030f21020a0b180105040305190c1e080705070308070605130b01140102071d07030c080705030105190302040e0d020c0406 79
    0x180700c3d44806413258415480742903411501da4449229a0035a00300da0003407400a4070102c02000b41e01c1380c500941d6001240101c410302a0b09100001c00e840344641c65210039203948511010110010075403121600c5a1000011001c070350b12440c00100d40ba072480300a0320001400d400803040a41d0350003481088100c1a00241401c10301941c501d5030581c0001c003036440b00720100081d45142c103001c0c080d49100700d02c6039480d2503584025403c90104140e080d080201000680d01d10300c0006143c40d1030702e003015868002c1c0c98400071082c0c130b80303a805442029001001801940000001c000c1080d0240042c1882544140a242e9075540c40403807060f010403015000041c10001002808614400520110030600c166a0b0203038891091403045001c104452900701d626070204109240c1c54440c505410580b4030349004241030a00c0004c041e80010301a45116441c05040e00242c1081c100d001c200460f4082c0043c890510074440e02510f80d2241e1211902600500d001200700303217000e01c61007060340c40b007141071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 95261385 1250 95260135 95260141
    0x2a091003020915030609010c0201060b0a08010e0a060503070806043e0112020c1b040c20030d110304030908060903071112160906081b01050d0908040609050a080f0303 73
    0x40381804002d840280b5502e40141c2c800c00f0394505102a601ca040128000718250001110090031529140d0145146803010b024101010b0f5000007074604540b20b0050216a61711404414001030007181c3c03000360705200f0702070001031030500407402500c2507004000f2400e1000c0d82252443d001e50740c0d000c0581c0048280011280e80440c0309403030b4100d1040601d001540420b40e81c1550080740c1c04200c803d5100d41c8004201032180c00200305040f0449825981800014602d110240603101c044480c0344004514150880025100b08241d400782d04040d42c046c82076555a01681d070f0160310594080d070010340d240034041500040003400c0f07402104468011858200140c0701d124080c0c1600840707070707400b908000d02080e19400402a000d880410880c40c1d540241c81d1190300c00c216851980030324500e03005680480c4441143d0b915140e601e01080c20100c0da12407e0500700d0b801001c5007080200803000c003140c04194554040c1d080ca050f12403c0e650b0701851368a448030303a6079a00c8000f191880980c010000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 95262635 1250 95261385 95261389
    0xb040b0d15110403150e0c040608010902090612060106230d1a0a03080d0b0109170c10020607020607080a09140106080706080108031614100203060a06030c0c080315032a09100302 78
    0x100c80051440311b0240d4500204100003e02602c1c615070003141e103691105400701c250725100c01e036203404c0481102c1c0004104140c0c08078980f113040520545c400d04c101d107142c12076800208404481c4440c520124255104d4805890f140101000000c1546115134980c09000c20709020f0600025680c00c0406103040c8a62140808050b1a54a40361410030030070440000e2818251040c141010a2500c042c2c011100c008040c80040700999141504650261080c003a103243c01244058025a091520161940c0d50b020410301408038070380700800068503035402509c952019809a025180503405445041d0b07507442044608400130b00514403a9003040055641c0103035600c030702c1c42d2403d2160759014044401581c06508084102104405c010380010820000f807410300c4a003030260942c0e040c10011810469801060ba0759142c4000b01a0200040070440328500301040b449210001411160b4116084140303191704415541c110b10070b44210f40f9540c0c0700c2d141c030410f01885400c0c2205c4a50740300c2d1442c3c007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 95263885 1250 95262635 95262641
    0x723070203060420120307062a140f0a030e060702030f1902010b0325050a06021c0201020d0614310c0507020603010603091506060f030b040b0d1511040315 68
    0x107102c01c01301003803154603501074407440941c0c4210a0b840c000346446040500f07001c4151645101c0601540201a40c03030001c243c07140e44c4d4613810358a14903140c001c103060303112144ea083c460140c1884d805c20011400b0201d40d81e050b0416058004000159600c0b6261a001613940340155020341c90080340911400d103079140100c000490920341480007141410009011a040a025100756440f402c1c560740b0108040301902040001420309950f9080c0d00d034a40301d4006c0d10354000745451305001d0700d54a9900700280c402d40554448848001d002c0101c40c0d511002c5420a0741310810082c0a00c14810720891009115284060126500002e2290b140a412903ca008040d2761201e1820711905100440150700c80c000554080d003500d4500082e200310501708072000c00003d0b51b900c01d0841c1014414040164400c005c58a2407500303040105003041f0800002c4c0150007030110b20364014000ca0301003c18411104507810b01c02c2e080c000100300c0c00c1000d46000001e0700c52030201030309129a500d15250f40c8030643e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 95265135 1250 95263885 95263913
    0x30a0c080717090c0d080d1b090302060306040e031902010b100206180102071205070311010605030309040b0409050109120906090608160509040507030c030606170a09020303040b0307230702030604 86
    0x20f02903600c010f94400000343c0c46000f0a806450003000840c0240c544481031042401403081c100c91148100c221800060862480340002030290b10040301140e21034540b03802100c1c0b6950f108080e070352070710344621941d0201406015490010b44c00c3c0080303203060b400c0c100100c2030a070410764003408a039542c4908507030344030715020400d454070740d0300701b100c603022513440e83c8000c0c01c0a9080c0d40d403668843d850308009006120a280b1620380f40d24040b020400381c0c0d03000040f200820b20a8802107002c20a038800a8001d20181d00003038040e508147c80002000100b1840040e031324481d80f120b01880c0d03190101103404465030b020b1140401c116202040300c5550056a4028a40c4c07545000d5240c003009401103001c1e100305948440c0401c5e119140311082a8160141d030000e00003a181c1100e00c0c42901820b208405005091072011907030f11020042503407018000c503400741001644d8140e032403c0640e0028400640c0c4050707040010402c925110f0306446802c1103d00080d0000c0c010600364907203480f800c00c120005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 95266385 1250 95265135 95265151
    0x703060e061c1b150f08100501140405300706021207020a03140c0103050108120913090506010e100501030c17070e0d03080a050709080a0b0a060b03010803030a0c080717 74
    0x14502d40c0e90041c0c42c1c000b50405090100700e454507070301003244c0250a405001e41c914051004590800070703140403220f2039004a4a0921b0a4040742d0b0714122800c805e03102d660032039a04030704221541d414101c3c42000109481001c0070806103207044080d1190b850303080c9802001d0060304421044128000c8101c00740c5011800240a00701c544c0e40da645100c601d090f012244801604451804075880d030301441454010312010015210000100121140500c5030380b1100e840b030200c101c00213607012502d902c91802075a21034111800c03940c55540040c001d8100300c422110741840741001180d2035109028007039128031281c441c0130280d811802d4064610307400070300b64001c000c000020381c102c7e039036101c2501c100c0c1c60280c0c96030040b5007000d0b5000c074150b40c0700400e06004e106621b401003003c0703000081c050205941040440d11a6251304143d00c014110341d0340843d009000100010403c0d510100085019418074601000311240707211080d14400000c441d03040209080010400789a900c400ca40c503441840c17 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 95267635 1250 95266385 95266403
    0x12090105040e0403031116030f030203010518040c03061104090c020d1b020f0306011203030f09020d03050307030608010c17130c0521031801020708030306030a060c05070f06050703060e061c 83
    0x550506d0503454006100c0001503401d000017100030300d600000000c228865500d015441d56060a000c60024894600818180a211400101400071240600e000f560748108107020451007103a00100680050140c000c5e01440d12041e021450300008903444030b00d1040c2ca81d121403d2007034581c2c52810996407030590304400d4280c0d28920035541885002d02030901594400c05208560400074101e452050420960901d40710994015a0301e45480504a03a410300e49640d80b9554864100c01a020341c0e400650150700701741c0352a010b6a00704c40d0301803075002006c50701c0c417140d80d40d01c40070156102c440f1006001c28241c800180520704100108400d100755440411144102100b903007440d41d4406865414054110b00f07150105690500405001300101c41c01141135040460000740c0728044000d000b407400b80d030303042e00d40d540c40c0c000d1041d00d26035038110600500c0b80300c850401501800d02142c00c100024075044001c2021444005854090400034003007244610904591281483c8281019182d580c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 95268885 1250 95267635 95267651
    0x216090213060e01030f0908040612110f030402180103050303040b070f0c021309020303070c080f0303040302101d06180118081b330a0e0606040b06090a0f0812090105040e040303 78
    0x14040c508110323204410040c0d031203140000003082c5054185188021b0350a04140c01c01603180c0300199030003680400c030469038039112880090000080000d800300c0f184c000000002c00e010000c005144103600030f0107108210780e80c4503030403100110ba41d0103480104504030046400341c144443d1581d140ba4184200141101c9181c0010b891343d080300d40e08a990302e00d988814091280709001507443d01c080c4800a509500702654041c2d21754102a83e000b004c65a911000381410003020580c0819910150035a0003604101a542c8503e1024903001034456081c111902118550711180d4604544c2184c462414004642c103082410007440d01da0691600c250717502c440c240f101c644880546564580c290304004030b5000c0b40301c0c05200b8010724a040d071f2450101d440b2030407000401c2d041e6011404550008940d294800024280d01548500503000301080c10b001c6880e1400380c1020b401e0380d0204003110b038114a010700c0e01d034051141f00032950000f0018042040340012111070650410311030700303020800b08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 95270135 1250 95268885 95268911
    0x91e01120216050c0306070c140703080c0a0302010b09070c030503150301050c040e0901090c031b0308030a0c0e0a0518070908010c030911010c021c03030f06060216090213060e0103 79
    0x780000b0b04454501c2186034080081080c2009080445034060303000c2d144d203141c0b2120190400c0c03542d2402409040305100d158600c100240504030246500051a9859415000c405c55440c3c0403110b08502640c40c0507034032110380c03500c503c1903441040302c2e540307400d8030070a1503504952680000e4494030580e4001c03130603000151b40c00c0c00307218800e111107082d0716141c134a420b803201c1c640240a40503000b942d05d4071a00748042458002c030001030340c1e0004100400014640c00359403042d0030590005d4001c080100038000e012a66422001e400b0303103680d540c1266802c8100421201c010309100b00c6031b000f0702c2d0100c4c0a400d000b402e04c4c0c4550042c210b0a080c48140d0760762078010700359170014112000003a0344845240400000c01c44408481d507007860034540c0a40030382e01043c40c80b03046003d07549001e5040c0102c0820140729801c0100c1d0302000f072005105070760795494065640d00300d440c2403c48201d104034010514240a109450040719000701500e400c92801c01e060380c111b240e04800c0c50400d03417524144030070300d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 95271385 1250 95270135 95270137
    0xb0a090e1602100605030606040e0309090a0e0d09050d020d020307031e15051b0306061605160b16020f1201090c140303071703070509120a0203060c091e011202 70
    0x101d2964800e030600d014581802070510030318846100074a450a0420321194400084840d84008180d4000a07041030200a01c0e280d40110402d0542c01000c00b803c000d602940ea402143d012001e0008650b04086190800e0380d03050070030700809422113201e5036104058075203460a56101c500140540782c0340c58a070b032124a810f47c0e094007540c00c1e00c00c1211040c070030818441074010700021424010095030400c40d0707880c001c680300310100700c0c901080440821a10b640e59822036028144011074907213004a50314000740c07905007810f8503a561140751a0700040744958041187c070381303200d80548081e9520056081105d0400654083e80e0442450b510920641030248582125140982e0300e00c0300c1175182c0110703020711141c0300d100a07000b034100b44a0400054843c9289481300c160102419032070b9560480200c4050003540034480d808194540703d410741c0c4c4004914800c45d240250141c0d9069a41c4451480040c4282060140c00c4494920b01c1e0302002c00020b2400091481450944841d8403a10740d55420303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 95272635 1250 95271385 95271391
    0x4080d0c020306010f060206040f0501060f0f0e0705030103020a030b0703090206070b040c0515040b160204060e04111503071d060423030a21090801060e1f030506010b0a090e 76
    0x1061030040e86405518041041e10b005118000002d1407450030100000e4a40c0e401610040801803030808140821500b900400c0141010100911400340c2d1400324054006841c8290241c1c00c40d52808a214244181c04882c1a80e030090031007007400c0d165a4a420740404018440c60802d80d8842c254130041e80d482c401462140e0046041c030304242024101601a00381da03038001ca101d01000d0b0204005913004605590407a8420803c09484e0007281e40150703e00346001c10000d600900e040c6004c0303980a4519400c034000d5000d058071030f500e150f1210501c03000e40c0b107a042c50501e4003414070015408e0741c400c0a040641c68444981a1012480500803904540041d0045201b8990a84640d1003030a280960208036100440c018004002a0f40303c902c41c3d50f1003204140c5140c1d25442c14510803d006409410042601d032000304200d903500e00003400398034801e6507844c0e4054580911480701c02691240042030303c0c0c010b00a4203107a441c007000b40d40702c1d50000030040300388440740f01c000410076580b081d0584 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 95273885 1250 95272635 95272637
    0xa030c061407090503010b09041212200417010209010509040b01052106040c020102070c0302010e06120103080a03050610020d0e0411040b09010315140105031305010c0905031c020606090c04080d 85
    0x248080c1041c01700b6095410304405140212845006c010204421280580c9081e14a013003a56841100341154800340c00c0511a011400129283e03011847c1c1c80d1400a008440c2407101d103000008040503154242d120301041c03207002039030a010903038592a05500c1041184014103005107000c4100c000c984041001c210a643c1c0c00703c030602003040c07034200740c0904102c0f860705200862034840250f645220f45a1280400b80c10069054940b040070b03110711044620f0030300e440d2940055580c1d2071030000040d5020003080c100280c00d00000c10360038185900d44074145101a000f4182240c0305180c00c403900a6040002940180c0715650f00401c48490070050014144a84400e0340e40d00c80f402c0090203030b507106010711289100d022000c1000403070b640c01e10070880c00c00b440d25964030707100c132100c0090320090728034082d0a035413070240c801a90a0300403041c00216842941500d480110400360a080131f155040c000c0d0158101e58000b410328030f407180c42150710400b2822424201621b45412520707000904403800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 95275135 1250 95273885 95273897
    0x30e040f270309050301020702091f031403030103260307120605060d0e0c010c08120a020910020a150204060f0305092b0e0603060f06030601020c0907090e16020a030c061407 76
    0x1c800d05038815400806054141c0c002d5191800550103da5004002014101c5250070003000901480c01801c22000850300305282812440300340c03400756107a0f44207100072112125002c0c02c1d20022500e02132810207100400f02d101d030441d035aa0005a071594080c1101100c1d05550705008641075468202628200e039000000144080d0361040c200d103400100340c88541440144c0c200c2c24005601e003c11111008050202040b02d034a234078400d4006806100c2c061070740040c4504200c0c800d140e00082c0304210030300944209490314200882c140480c803c42c001c000002d0108554018a41d00030303005240c0084546085801f41c0c402089640e00a014030400450189007580041100320303404100c01440b22000c84a0a1071824241c00007015400344448242c040c4501100244440c2c1c001d1100400004000e040602c1c107160a140042603105180580c0300d400d01200085400b014a600d011903890100750004c2000007542d0b24280d4043c04000411216180c5501e40c50000c20740380102c16000d4241c0352640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 95276385 1250 95275135 95275211
    0x12050703061707060206250c080f0d020903010b0904020901140102070509010806010503060a15030f031e0f030c080618130501060603050105130209090601050315030109051612030e040f 81
    0x6e08041018082e403241c903440d580060585071588003008500b00701d90400b80c81c421081d1408040902610f000090741030380105881100e40915001441c040004600070030100d45034400300b148040c010380b8041d402c5080c000051040780c6214000c00003d500500403601d49a40e1100043e1043c1c0303003608050b081e900302c000104003609003003050641000e0f80c020240403d50791401880080c918521020b0400b400203202642810b0081940880d00195000c201c4a0800c4640001d4454818141c50800003482d194490002d1f520450001e8010b00c401004e50401c484920300c502c3d0440f8001d0071509000003604101c0001072024460030b001441300b5100030410b985004108910001c4106000d450316004112000d22556030410182d0f0020090800c55100c0e1034085a1005030940c4501140c1c1640ca41001c010600c00c00241e2a88892000814154510303155800044451415000200400c2a41c17a00d4001403030243c000a008154680000075602e4100040f001800754941081202003141c201d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 95277635 1250 95276385 95276387
    0x100207050913060b0607032106080a0501061511061803130801090506100b0a0c08040b0a03051807080303010e090c090705030703110f0904020c0313270b011205070306170706 76
    0x80e4800c001005c90301c1038100001d980b005800c2d40352940e0016020351409440b03020000d09540914064030040c011165a42d02c40d107070050007049280240e0b000e43c10083d8048032050306c5241c80381880100c0d01d01030042501d80035401c1105200c02d0800030043e000c00e02031590101c0350901100c0082c0800c2e0004038040b00b160034000c0c20504050144500d4000341c030410701801c4005c90848031811071518220081d40901c0c00d19564500440e080060a14070000300114015496000359001c0c0d41c000c540e0096040602d24805d54070380981c480d01d079041d08140300401c8007a640700409940aa1018199014291000001000b03100201c407034030007151010042c0420750f6810300c81d8002080804203983d03c5c0882d082c20b071281600501042d60300c5140c00050200d038182092040d1101884261000542d85490300e05030f0300f08955032030030400c0c6400c3c05030461000a903540501101100103840c0c01c040569507070483d4010f0301c0010821010301d80c0f280c0c8001000c0c802441ca02a802403404041c2c02d4003814004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 95278885 1250 95277635 95277641
    0x1401060f030b06030711070504060906060318020306062404060302030103120e0a17011b091d0103080904090602070203060114040b01031418070b041202090109150510020705091306 79
    0xc402040500d0120500344540b02c0c101241d400107031a09001b11420032140c3d001e0325204103504510381050604400003141c41060b0000380035142541c80a021130f1030005160b0348030b600d000340040d5056001070045041c07800d2200b003020303d102082d14410340d01035010074003031080d074000d51022000030341c00401002800b01c64070140350044000e191402104c1301440000c4c00325606400ba03805000300c03210000da400b13902513020144918051070248000400500e001d042e551051280729800201010301e80000c10300c511500d810f8035400480c1a003040d03240418000100900f040480308030350300304155405613404014a81c002d0a943c0d8080700b010744800140416182c1d00c1d2040d0b414541081101c000c1810800b03d0355070f10000d14110180c00e00340c030904280c40d00000e03500c0407010400004005c14454055140300031f04500035207411071349036612680c2508841c0c41c1e103400b2000001c0030005120b24980f03660a5070b50032001d481110041925540001c0c4030711801e85a090307801030b1b400106010041540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 95280135 1250 95278885 95278907
    0x504050c07150e030d0509250605031506090303070c14040903020616170702070509070806060a0c0212070b031504020403030203030f061c050d12020418110706140106 73
    0x111403070070401d00d6500c0401011200440340740a40d1200c3c04054030800c00c1040e98040441c0c3c80c024051740c10501202529880314440d419040401d40300049209100180f2040480d4038543d1000d1440c0e4134507010098183c0b5484929038054010800f5080564041002d080307894050010481c00301c0c40c2000844015103e40c41250145080c40d29900102e900801c0860b84114107501000c4400c076100e00480b0354801080c0718518040c0940c042c4440164001076001c15100c05840348030481d1518141502d8940e01140c0840d8071040c10001c00b04102c0c89061f1a50101e8030141a14088090903814941401720300c0e0060364030f0041c04801c00403850504101165070300d0041c0c808619007030550f2802074a0f4400240618091001140803403081d0300c88078205440c00c403240304250075900c2d05180494451850358084800107242d80d500c9840346566208a5040b5045940420106040a10550050802000a11030301300051010303202240a502403c04d0038030020f4050541581045006421200c4031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 95281385 1250 95280135 95280151
    0x10311031e0a0f02060c15040b070203190507020102010f0513051218010c110303070809090609010b09101e020c09011203050706090f0f2303090d0602030c13030c050405 74
    0x490801c4514042000546142c1040c42d10703480401030300200e1194480c3c1d0940808900c00e0084041c0d007408909141c0e070042e0b101c3c8160070360702c6d20741090480c0e490081d2482e44d140750084c0200c0d486803501490080410602c103000102da00701c84a96400200c800445141c140880c0c0c40d6000c40403c0402c0c82085001d850400d00d90b424802e41c8008030680030360085155040c45a104c5d102000d00140051149a81000a084903988c6849107081d5900740c02850f541e0340601103540201e2818904a4490b60580b4481004503080071180020007912202c1b042094091100c00d200d134140070310841d0600d03503215030745800501d000c84039131091100540d4160300503c0c8045000b03107600f0000f40e0020032200d030942c121901040e0700440d402c01e044071007030b920070085c40060007862013020070401c4030b410004405200b00310401c86802c09426902d9101d042c407a60f50003003854401600284155004d1038000c050342028508111100f424001d084d416608160b60000591100304071034506030051560080e80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 95282635 1250 95281385 95281423
    0x506070e011205041509031b03020c0f03010c020c0103020f04050901030f0212070806070302071104180b010501030c080f04060908070b0405070515071101020c04090c0509061507120c0b01031103 85
    0x2254507500000000700307800845c402e8588115006243c0704010a08064041e414049254040e6240281da2a070807004002e000d8a61308180c00e41d20301d0184910003541086401502004035650011030081d803007a881540351580502012425846401d6814080c51060852407142d0b02a8010810700d06480d48000a5a500c40d54060203020b07000700c0c5032a006030300c3d4103016840360b0007841c09010a0044988d415042464052180d22036900c840b61010f05601810b00071815076290b40046040d100101700410108000e54041140d422003100c016901c1409503200142070310303442d07a51007810b034404071040d42e001100f40148410301c4801d000d0840184021904000701c0041944000301c28040c1b0f0304050203801080d6401407a1307074000d121510721420010300800c90441c081c50400d9003c08070b40982400f0b2281200010b20a0510b0b45107030800d103a40d001e0b0705061607015918501c6401070304040d42c00304510203451200091074034036071a0185101d07010740c040b002c0d050342c141407801507101c0d4000c200c000c0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 95283885 1250 95282635 95282641
    0x20d0e0d020d052d0d0f020c1b040e0321070207140103050411090129040609050d050f01050a0c0305160f0e190b070c0e01300506070e011205 62
    0x500065035032210030302d505100c2c0d160041c80e2030b060141d252071112280b0400c01c03032010b02c03d040407480041c000703c003410340100482001503002004900802040c074900d544040d020742d0b11341c03817607002d02040d201c0014004144211000200c0d03007160003828151000c030106501050340340c0d00b4107103000c0c0d204540d0b00c0200300c2c00e4a4000001c1c451040d041c83d1074140340d51000481e0500c4103006940c21500005000d648075540d40c1d1140d200c907031030000302d190314110361082d0a8440000c613604440848103a50b5420503100d0400081002c4400614001c03030343c0d48940705030903400710028003685116500400340003511309620340002e016104000c0c00440c000007500440400650072205401c928506884c000c42084c03e01c5004c40c48000c0c0303a20201d00440f002c11800540c00b0030420060603018030882c0c6110304260b0719108007100000078041c100c88641d0304500450060310408003442491140c0a25001d49065504c2d4242413850a1f0b4003070000604041c111a06560024001091602c040e50100058030f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 95285135 1250 95283885 95283887
    0x10f0c080c0a02190201032405010f02060606040501031d0d080a0507080603121312140708030301030f02060f07020d050f0c0303070c050409030207051f02060604090302060a0b1210020d0e0d 83
    0x130544403080c4906034801e80e81c02903922030352090072003c1d03482c000f01d42e54040d0400400352070700c203500c645400100d0100190140b1480400c482c9d00070741002c0c02a0b4202402c0000540c041e0200c50722280841000d03900c0100c3d221810400e42006161139110000e190a10041003c240d40c4c3c010204810300103441c2c103009840c0c03000030360300044003200341e200c0d5240c0100980708003007070b0030a0b4000c0481e100807410910601615200c030141e4440c50078200d960f1a546c550940341c07680000d2001901e40610f0300303402005030605c0f100600d104903104245d14a00f206a80c00a02d0800510106650a51100c107112044000070400010b400701c00300c004600b8045240c1e40c8110450f507902130580140c2d200c00e1010101802003002c8005400e0080a84441d4821808502c112108050614005105230008503046040501c6415080780e010340c0504510394032015494043d041c07a45500c0d401144281075201ca400302803040d004a00440c3d0b0015944902d4440010103845034080740503910b4101484042a031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 95286385 1250 95285135 95285143
    0x30604111206040533040f140106030e0c100203070506060405010b0912030906270603040b0c0a0908070605040305060c030105030a15090f0b010302090a05010b0a0509060705010f0c080c0a02 83
    0x4030b0400c40300400d50b5540c042482149400c822000b042029424040400f60440240022150350f800e0f10204031600d050828035007541c49400000d0096007944005100d07980c0b083d007212581c040c80c0d40464210001c04800320b410700d0191168100180c1000c034035401004400d003c0150403840440e401d20081d4140960101180315415446104051103020780401060620a5806814005080c50303284c40907114215074022580d9030800d082a0242d44680e4103190100070740c0d010ba80c00115488003582c402e242032540e0380c84111100709001500c400000c50040030130005002d001c10741d4480340c0f102d00c0d42ca821803a1140186c8881126001417005020030744000881c0058150000d604550381c0c42503c001d40010311103030b00040c0c0901c1c418160f203400c0c02050650325049a00c203540d140300a5448020342000c82c0c200327014141c0d40810801140d11864403c9014205044004044610386600b6a45050844004042c1d0121031515404010b20144e08100c071540d003e904402d01e00e240c904910802911 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 95287635 1250 95286385 95286391
    0x9100f200303071d04090f0210050a0f110a0f060204151e050f0d090b040c090b090402010f09121b0506070c09051306021b0609030405010215040302010e06010b0306041112 75
    0x30090f2400d801c0f07078900d034000c0113242d05210141042011481c141082c005610900a090303018554044502820520070002c86e44c0242981c0d50b060701078040900300310b6034003220220250007807042d42c501c0f9005c40d225840d0026560b00c241c10050703031a0314203540001341040b10000c040c02e010520703140321004c0e2881003000d0719200031480e00942d80c0c800c1240a9445010310394580c000c25140c080c43c4000c1110058545000d10300405402d0034207030752002181c003540d555420b020740240442001c03500550040c40000000d440500f00a00d0260b1510360020000d038020900382c4c1c0740314021152040781a10030a03480040d040c01e03910180b510220303841e0080d400c005803096400e0bd59503100041c451140b2444010030240d4814001d640e14159081c000f41d00410520300b1b103000d4007070f40001c00c25013200002200c4c11958103030094903041102c0c1c9080c0307c60910007002601555241c00d00d003504103109000300c501912070103803001d841e400c2540030300084071105c4c010740e2241903040040c0901c80c0b0912401c036074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 95288885 1250 95287635 95287637
    0x9140306060d0c0b03040507060909020f1204031e021606021515040207020d0b06090123040203040614010314060c072f0a0602010c03050c12011a09100f20030307 71
    0x16940c840c0c81c000d40300b25400e611a00410002005020411030042340380d5080b01e0b41a941c0407c0300380c81d182c1140482c03181507174940103030501300100302c0c16041c204180c550181c080c0c00e01052010544100024940b4607210140042e0084615502aa041e884049010304100e01c01002490b1201442603209100505202e1004045001c09500303582d07250100c0e0322035a03011f03120000b690300a10301142d141e401038805d00c1c41400000b0011078070000341585120140100169101c2003803c0d0b906120003580090310540f503403510740d4412030b207400705034481ca07000310701c202002d1540071040c0e60300e541000d5000c0c158142009040140700e020408951008000b4002c2207900011049440e4500d0031217a22840d982c0c1d000308042e0000507082c0c1d010340c00700300c1e01019501c0512940d03640d0068410584070303046007800c1d82c07960b44c801402405c4d80e0b002e0f20034407840d240094038036088000740022040024401c0d00c00000b8420100b52103965070010b44c1320142482d4844581c221420540c010746c69000061200e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 95290135 1250 95288885 95288899
    0x11406030402120c0a0b1b0a02010210151a0406090603020a09170f15090f010204050303070b130b090109060c020303060109150302070b0108010c09050a0b040306090c0302120604030914030606 84
    0x51140f400d210f040e01e8044010403400c862035482041440c02e8118500e0f0301140f00c01c00e82201c1581e02d004c940900f040340e0580c05840ca00350601c0c924001082c0c481000d4000e0b048510380851803051080140c10324003401c10025441d645013007030080038402c2c1c5801c8001018010701002d0005904a0030350f100341c9900f80c03800c80c0036007961030300070340303402e6a040c5042c486100d0304510f178400c01e1120850714000c2c4514015104030311040503980d800d034030035031250640691040041c0c1c00491080b07000c1540280928800000d00100c644a24801da28140d0304020140d544041701030800203e8071804003d01c1040c000b07582180340044c000b0b440182584544032455039420150b00c0704034172980c12504900d90125140349207503111001d003402844035880740c10100d8100f02c00899546040c0d01d0420440380344007000d914280c2142da4030390141c041c42c01e040391480b4600f41d0100059031007030186541d98808030003c11107031606003001007910072203520800090181d9107441196480c041041070740250252010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 95291385 1250 95290135 95290159
    0x7080d0506040902041a0306090708211b01020a0f080115030e120a08060901080f060c0d06120302011a040608070e1e01080a0c06090b0d0c0c080a030212011406030402 73
    0x700d0060910070728025845860002c155042e0b81140d80a446d84c0c407001d408940080c0d40c0c50500b55650042c6000316400d83c2e0041d0b03503180106d00c00c00c00c0e80244003601d00d03200741041c0c1403240070011071a4401020850344d4010507580703a5035901803014401c0f250585000e0f0740c55450084140c4601c8a140080010191130f4503a0b403100300d4042090321690041d003803840750388080c0040f004280800a40e0070714413a400031000001e981c2c100051941c0700340c00400c00780000791070b50f546a12590344107851594451780c840900189454080c901a20618080c0e000420303007407030704109407080c045502a003902c40d600d426800c0c04203401c0000c00c032055440070801d100c1c5035220f030f03049440701da11501d100170440004400049140c01020400e12001c6105981000d20760351241030940780c072500e60142d5404180c0a0010034110041500203031040c1c121780c10551100501c0c0d803030383c04640c0c1c444207482010079000100d40c040d0040300610741d4010241e0850040020401d0000540b0320f21014101130700c20904443c070b03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 95292635 1250 95291385 95291389
    0x30504030903081c0501080303060f1e060a050d050603010c1e030e0601090e1e06041212060906170105040c030212030c07030b041a130209190207060212090307080d0506 74
    0xe007402460300a0f06842c1c803024650184415002c50380c1c4110701007400c200002400100010980c1e0003000000d00d031003980c04400c0c0901907500e01c021000001c0308203502c0c102c01d140d100c01000b0104420f036aa50706540f22990000300041d1080640100e00981c54002e032046074035400f82e55a841c11440007184240c906189030210f000d04000c0002c601340707004e40300c0000f440c0d0700300d94001100407603a80d00b9280480d10a113408010401000265012a08410700040c0026110100c41015103034500341001a0701d2940494021507070940c00840c1004c1c1c0d00c88062000240445450380260b10391002401103103005da44500380c1d2103151200074066400c1d04158007040000744140e843c20350840d800c40340899680e0030002c1a2040c207480940c1d1b1180300740d40c0c440803031124042603881a40c0101014800007020313800d003d900180102040317901300c00c002c1d070140c1c084034600080c40550b004500240c0c41c1d006014403003543d010b01515511a582c4100708180001305584180c401860090000140c15662400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 95293885 1250 95292635 95292647
    0x102040306060e0a110c0307020d1401021605121c0b0402040506030403031a0402030c1603020c151909080a030c020303041a0315010f0203071b081606020d0906050a03050403 76
    0xd101e28140b29001c59860784803401d091007452505400c1c08084a21852844680310f55004a0119041085007a0141c20107205400e8000d10070360b20507038045108122b640c01ca13000306403009010030840940806100040111111075002803060070b2a202130409101a40b00d804407a900090b5252898080300d070396142c0c1900c008140140440f0756070702e0146001002450250440322154110100c0100b0a003054800c1d6841458110501c629080e00038410344a0001d402900b207003180b2a680c1d80c800680c4407090180f0030018018807150301c4128a038072100d80c440f4008124010440c2c221002c1040c407c0c0010403041054050404001608507800804e0851040360880c0d0b02000703012005031a4444031800440c4107024400d2130113143c07003184004440d032411448040c0016402071206030085050300c01703244c00c0500d0501c1d08025081c0e40300302140c10240543d410512401040004111443d014807210b1686020351401040d01d9017044400740c060300a006101d0101541c4034001030401d80244 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 95295135 1250 95293885 95293889
    0x409020d0b07050a03050c12060f0a050604090c26061504031b05010e0d0203100b0d0b01081c09030f1205121815010302090f04030203040b030c040906060c030f030e010204 75
    0x20700c4041081ca001100602641c2c4000002000a86003500013190000400e0641d0798121798241c20504a849040410603120f52407840194005121600012955a408002d00040c040e090b404640c170804130034098084540100e10b03070402816071100e40c101035041600340fa44154212501004003099400b81040c1d4011900014000c8400d19542e21862281c80042c2c4120741c42603884840b540030714002c0c804e03070002008000b074040d80403112411070541540c00840c00b9440140c9440311a800545414087e40300070380c0000925001200c52180e032a18600b51880554014103241c46014616030300d14404500e110000382c85401c07409001036000b0b11400c22207032404610041603d4600f01098002151700d8a4400c00c4420301c180d01c103800c10201c2c130004260480390004c1c142c0b4030303555403500c0c010184c0000400c118114001080007103140a0800059070141204899040d212801d000c010002ca8100360409014085000a07100001e94865140f0042c00010f1501041c01008034000c1ca0181c0556 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 95296385 1250 95295135 95295143
    0x90b04090903110114180f06150103020c0a080706050603030705030d02030709080d0e01020106170a11040e0607080103060507080f04200d08030a0c0906050f071a04120915020c0409020d 81
    0x41784c0c1010315151080300480c0200140200f4030a04035a00880594500300780001d02040e0b00080300145c51207045007a0b61078980010f04016150040f081c4410307060841540c0c1c11514035101080308014003c283c4074883c0d111b9400d030020341c584006600d500f5540c0c00341b2210280c400303800200144090b1b1082e91150014101003044500001c00d4140c00f5007c40c1107500380c035006610700440007230b90b207150040a81038844600080c184d00500364540038000c1c0258415280c2090312500c980c1d002c5401041002e10864483c2d86a860550541c41d04105549002c0c041d90104001903080c40780752540c22040310780295008102c825442d00300922010000088206c031070b40508140c003a0001e00c04c04000641c07141e0781111003080180078050050300c3c12103250113041d001441c1484113905e045e000c0c5009180d028040c69103414030010395000410740c10303800ca50442d0390161603d44000000d4100701100301038802d001052042120f0703007600030750b9241403088140c800c546402e45a025521440d240301040c50f04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 95297635 1250 95296385 95296391
    0x1106070812150109030314070803090616020307020a05010509030c0405070201090302010e191209050a090f0c17240402030906010303020d1e0f02032101050103060501090b040909031101 81
    0x15040ca4003040c0c00c404480081c4440ca100014070a4910300001000d44105845442c03145045441c1120311400d80c00e103002c4c0c1d142041024001140340e02000d03510520300e00004200520342098032091401614050405560090000ea00140e0703441b2185000d440c1c081c6400d940310054200040c1c5010301d00c0c1121600189000d0510440c01c0d07042d04803c85541c0250028000310b840b0810345592000e00000c044003801c1c14901000015240c50040d180394002c40c0f801001c20750b124030024500154540c80308120507034401904107070380d42c203000b140c840342c0c00e07818070440c0c00c02e82240800d0944e80c0200300003160400007503040059500390704504d500c0603029000f1910703494004e815685c3c030306080c0000e070050f1141a2003035810034800d88104001c29442064540581007502d0140c031780d2081c4080c904254002488400342c90404044440071400c03d07650f400c402ca516000000d01260450740040e0304010240d102403044a40340c0c003c4804070340004800003899141810700301d404d44060001c4400c1035007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 95298885 1250 95297635 95297647
    0xb06090d060614090f0606160507080d17190c051309021b0318060310080d0309061503020f06090409080d0606030507110d141903050f0a11070b041106 66
    0x80158416015940b40c0303003540002c82889010030402c4001241c20108005d80340c2d0015103541094000342c100301d0785c00c07a112015009183c0e1068100140c680282c806070b804280010301090b8007080111045600059201d160300301411050100c6804c2c51481144c03039180c621800320988240d044a101050500d615042da503100c030784070000307507010340d04003803451149000030400c8010100440d05045280e1f201003058140b90414480503810003001844030001c952400035603910184000310409041d9680041c4403111071030500c040b01c007402c9070b86010340c3c4210000d00060700ca0030b8010910340320449201c0c3c2c40703000c042c0c0003070003034103c0700300c01090081e001c201280c0c10045900b080080c3e800540781480940e4a0f85022074848a008150900980c805508a0302c468000c4440401c01e8210f402c4442c0303070000c110f00d400101c201c5450311030000f980c1e032820003090503604010305800030030b1640107100076880c2038003101040c0201c19010303100804d81d2021500300b005109800d003c5140181c01961540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 95300135 1250 95298885 95298893
    0x318080106091a010e060403060b03030d05090f1b0102030a031a060c0f0d0c020d02040513050f0f070b030106140d0b0d0b0f1b04060c0204020c010615090e070905040b06090d 76
    0x40c1d01818065030041510705900320f9806940c017400302070f002626050510745540c80c2c00019120480c07800b90180400c0040302c0d000070070b60084500c20100301004204030f107082d25031075260010500c0c0c1040801c0003982c120200da0303400b004540c40041c807803802082984080c2505c00e500c2107040501035104a0000b803100c90544003140100f840c43d4500140c2d16003c42e000b00aa9603200b190314000e500c1902c06490000610341544402e4014051403038200703641c0790581c1d86924101d070f1191070720510b034001404802004d00402400010f80344c0c02007041e065526003207014020001180e10325541c000e000c1404810300306903910130b5500031030041415554050504045c69a03074400e45041607209180030000d01904100390003590710104810b0304902d050300d001400c403019410044101e91047c1c0800440c90461001d0003240082c00e4007503050400b2040704100503001d40060341c01060860051000c200150390428a000100c460540740405c40d20800800181c00f8425507400680c410b203a500399000344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 95301385 1250 95300135 95300141
    0x90e1606210501061b0302010213060522030203060601030207050f0a030302041d2403010906090b060102190809040902060408010e1b0406080606280303020f010c03020c0a031808010609 81
    0x9008403490009400aa99a01c0d90559100740030301c1010030105240b04101c1c0d042e001030758001038020302c0018207003140c020401540c4003150b800344002990100d840c80c0120042810081c9802c083c840382c82e0058903590103c0d4035000e0003013555040c0f60740400d0400a100c82800b003001c00d900c449003035801030102c4bc640607009401038024000720403019541440302c01355009055003e40c00c07031150f508411241c1c5221900b0200060780958155480304d824100181060194034821440b40349420558503102000920744140e4000703210102c038264043c070001c40c40a000b03c4401d02c030259030119030551940041a0148501d600c170048941c030340841407444060106e800001d00000d00119403080061401f00029580306000e100c03501d07000140800c2e00341c60901c900440112000c80c18000d254082e51003e010140d55900c00c1c1c0141e0007002c21008090028030900094802506003182800f00000c100d90340c400340f5690003014001080e03060a107003007030740701c1e954001e01d001720080c44241d4a501d1030300e0203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 95302635 1250 95301385 95301407
    0x30703050a0215040809040c050c0d0e040b03030a09090c030908070303090201030501050306100b1b0d08040b0708010b0904180c17100e0c09040c09060603021b070807090e1606 77
    0x14054882c2402c0c0c0b42c0c0e800d41c85107004c4d42e004040903041c10040c100700402030070861060814410100444001a00e081c0502401201c00b034540c101c95840d500705000a48031041d1a0612035041044280c80c0d00d0380102c520300940b41c40c1203001440c0403021405a0042c1070110b07010f0112440800c00404059040c2c001150292007a80d040c40266078403001c1c50740c0c0b03c0e02030b039001d0004000420244140d50582c0041c00040c401010798200055006030300c50f080410a0f000040000d10410030407041c0001614a15040840751620040640c07406440241324003034004001e200c2e5444001415110459118008513960092081d0014a80d01d12283c03403060a1004006d610740241007140006a0042c8030380c0f111445084054981055900e041180c0b461006204036200d0781c000c3c80204107050303d445124003034600f644006070b859104c4040302d580b009804205030140d03070040f04140704045c00801c20b1011600e94941c04030b04109003485507030800954080244404010790300c0002c40c168005c41c8558 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 95303885 1250 95302635 95302637
    0x70305041a0c0c09011401260108010914030a020d0509041508010501060f0201050c04051507240e1606080606040923060102030a0903032f01090c08010e070306020d0e030703050a 78
    0x2d103c800350709020320b42a091042d070181d9041c103900d074402c0354011aa40114080c4162003148105041e030204050700a00ba0031002c2e040e9504c66809080101050302281c2620400004500301100850020f40d1240001c2800003002404a00380c40a03132116017103d103408015052460a0396190314406000300700901c07808000540b2001290410703801071054600458040311154130b40390410301400450442d660a40401000c20003540011070b182d1942245020110121f2506822580d11103c0c00d032a694030754140c0d150801d6141003040051a00d00b9412211300d4144002c8550320400095036134003c95000da900103081c0302031806219252810019520800903141e03a440d292040120b0303403805400000004900040404c0c00401d000d0140b80e01003e441c00725600e02014801074032039002485c1d98503000203a4441702107204002c0049061405848000020060606d4030703540715951314041d20019094550001c1d803405690040c0d0000d001a450103401c40b660354081e071600420603448424280 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 95305135 1250 95303885 95303893
    0xa0c0506010605070305040509070c050a0b100e0c0304060506031e0115120c21060e150703050c0f030402040e070b030a050a0510030636030311040602030f070305041a0c 74
    0x2190b440c1c001d00590b12482e40564541d0f08040c01c110510a2840018243d4014001002d11500005000700000c01c001403080052003482c0c1050500c801070340c0502e40000105104820821540c803080f0707401c0d03d50058001c00c0118907a1545c1000c01e040104901e0080c5003100c915221001c03c01e4150801d800c078001c03046102413000d40d0749403841060100c070f1800a000e150003500c01c0240b0f0500d094020b800404c2494a00040d5006035960011552410120480c1d030f0000070303481c000070710600c41749644031805007030510052034480c411110310310651699058440020022905540b41d5030701c4401c01300401c50843c3e120a07268288080190021100d02040c207003840001404651a8040c41d40034010020755242304904594800029141c0071407a100300c0010070824211842881d8008408203402c00003c0c10b042940b0f0500400381d84561843d140c82440c208001c010107580001210018804030545a48441203450100c900f81f149500001d600c5075460480605400c91200a121301c503c010221 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 95306385 1250 95305135 95305139
    0x1120513021918020306011407030215010909060b03010b0307092a02010b091003020310050402040219090503012304030807050c010f0b100305160305060607020d1211070e0a1a060a0c050601 83
    0x50164841110501c7c001038264511109428104000d801400c4c46401038420b504240d021040f0001c400b40c1c03000407082c0d00c94501400b4491584121000800c050b4024484a0f111101003651100c0070702c81c3c199030a0f0313102d000e8004454420f40301c085c004c0501d0140140b041c0d444900a02800e05503203018403c01580000c940c00358494a81403040300e078080c000c0c1074100201c0030a90001e00000784180d810075020071031103e006504214401d20604242c844000700d0341014280350840d070700f00e89012070203800004980d00d6188134001c3c66500951524120f0340790ba44e00c0104682e54001c0342e10790709140d0b081282d9411111803c0d00803220355030040d5005c11110b0100c40e011002d5030b1060320304084541900d18030b0700001f4030a40010794002c00c00346c0703124908071450340450a240d025010541e00a121140742d4181e07a41c0c0041c1040d9007160000062814038180309001c25000300280083c07040555807562860f036015150079018102100400090b203d6400403400b408035490541b080310580520000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 95307635 1250 95306385 95306429
    0xc01050a09090f0906181506140f031926040b090d050f0706120e010c050307030509151305070b160f05030906040f0e090309011205130219 61
    0x292003946909a40e04034031185040b1003000102454100b1103616a210180400815024022800061001d01c021041c0103d0343c100139400c0c01d4208118a0200d0500c1420003031119841d03140025440e00b111743d0091340210b0800207140c8910041088851447c64078010207000900c05400540b59081c03510b6441c254003603141c0c2e20319114134000d14103440d400b4041d1842d58103141070000503039845142261a000000cbe075070705161a00070740c015000290120054075894000c0c1c0208110030000c0710081c0032903911203e02800e2170000900c01070405907203200080c030a000401054000c00d48240903c0003600b803c00603c2c0c05010002000d82e52813041000000d0300200c2181181d20034841c034440d0018200352175443c0c80c14100340f41e2041e501803105008103801540d803a0b004000620080207551001c0d403500005c420702c2140240490038603042444030041f0741c2d800c40c40b000040d0074004400502640e91207401ea9801d1514030000e504001250482c0d10580e89086004090340c40c07d01000320a5194212 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 95308885 1250 95307635 95307637
    0x3010602011a0d06090f02091f0f0609031b0b0711031e06011802040306020c0303061009060210050c12010902030601090e1012030207090504050309150909060f1314010303020c0105 79
    0x650b05410507030400002c80402c0301503000d000e07010301c180c1c216003a00c84940c000400c0c00d80c06480d0042038042d01400143c2c0542668845001844245c1d8200f81c080d01d007140c050580c0d03915110241c0080c3c00038003280c00610302a220a4050140a60416250551410010018040400f40a00178810002d01a030000741088030100d0340c089030001441d15030308103407551386807440a90120354000d07001c1c000071000502a001610700c0010280081d40c4900d050420083c480c68022441030601c1008032061001c95808107104034641700d4a00c01050700d0315205c040c03442c0c52081060b050513070081c000000c02c0c08207260300258050f80f000d0380c51562890711500c071041180d4040e5250840b141a0140410007081c004440300c0c06d890081c010344000580e00c800c010f0039540d003200d00311259000010b140350b06250000c15040c17080310440c1c010b401d1800050120b0308100d4007900262007180c4440741070040daa560501640c459003504c0060040810040056500040130f000480140c054004021602e5204030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 95310135 1250 95308885 95308931
    0x20a06050705091003020f0705150601260601080402060d0507181e0e040501060f06090e0c0901020c130b031603150917030402030a020d050a0501060608090a03050f04090608030301060201 82
    0x1440c1038881c3c00310f0b1314140d000398402e600d0b0301c0e003000b03041c001d40e408a00103100404600d4585065048503162000c00100714a01020030f18440c9014203800960190f4115400c0c0c1e4406400e080c040710948460000603528042c0c1000052802c2c01c0c80e08002600d50b2002280a0b24100c4060460a5035251840c0001071807901d00000c2c0010315001c4108181c4185617134540d045030103003000260084d12840075200384002a0005030120b04060310070042c100802c0f6003950720250700c0e84490305051842000070340310704100e10018410307030a4041e55211200306078090b00e41d00100400f100d41080400c40b58214050481c841510201071440c01c1040281e450b0050004043d804010107188601e40402000e4a4201400990f01442901198001a144c5408118a0314040d074018000180076150007800d40704036810560400107454140b0441400014500010b03c1c1c2c03505080d900c802d11a04564194050365200c015003a05040c40001c03425000702c001d41c1614103550003400340080001145101803140c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 95311385 1250 95310135 95310139
    0xd020309040207140105040c08120403020a0b0a0201062105010b030a030c021306050405270c0906010c14010204121e0c230306091015080a080307050c0a03020a0605070509 75
    0x100305494452078603500602c0100d01c125a9801e0030b4524081407400c4842c11201164051140c1c101440311400400121618000c4501c80c2450700c0c1c2940d011070300b1060144520550b44401203203000c0214001e401c07010241070100e44408840c10000d014010385a0035281c195082d52822949070700c28200803680001940e0036803070704402d41c0c0c099400c0c131864888460403128034903640d5101040e2aa81c501800e4090b2000c00825540d0755164100800c0f00707a141f9025052992090358829810307100c252030590b010390b090920420510441c1815045a0704005481540354030015011501c920b007001c0a010303241c09442c010760300c000100944050072030401da029040004001e0200580e00500401d6007200c80a2212040f0a218000120385040d0f170035a28405103030001100054214110b21807062a101520640110103140c421420346031015808080c00e40c2000000042800f806003041f6480c2d000c49600311420300a4500700251500c4112404490460070000481c172118401d1003510201c02d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 95312635 1250 95311385 95311387
    0x1090b01050f0619110f07060804020423040b190e0609010c0f02061609080d0e03060901060501051204170703050d1802060a0e04060f0902030609070201050c03150a121101030e0d0203 80
    0x15420042d680e808100652551754818089144282c20f0300340038030401064541c40d400b00300e003420301c10007064074070004c1c28038400c0d0b08a840903611001400c078050341050300015454965191600f040c40d4600c01d10b0901d032001c1d410a01015005c0f940061032030f1198000000822644001c00000c42c1c85d0440000b400e00107900a6003c207500005102d6159210034503820b1000302d5541d195030103801d20180008001c08214404201c00050070184a10765120350002c008105950900e00041c2c0b085c050a0141c128003071180002408100640c2001c80d00041048a1662141000c1c40c0003403042d4480850074a48038108407600038a09404108206102c0e0b0040c00380e400e114209030b080383c0640780a01e54030303801074480300d0015142034800c440300003134807070100e025940b45098003d22881940250012381103a1600f020000c0382c0d10840140c1c3d8000211509003040d81000000052070070900e81c010002e00003011980c101040300140020382c04034000e0320248107101c003030f5081e103860306000454000503800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 95313885 1250 95312635 95312677
    0x105091b01020a17071a01060207060509040b0607051c02060c070201050c010b0907030c0e06030c040b0c0c060d02040e0f040c151407030c0507090b0d03030b01020f01090b01050f06 79
    0x60100c0140e10040c01841166010b00c0291118a81e10400c11070401c600703a80002c5180c2070090030800c03c0041144082100c240d5450404004e554011604c2a13408100b00031912032019501d942003d111640e008104e01e45804c014140302e91103c5150b55084040c3d40e0b00c074440c10082d4000b161041c031a0580da882c1c20700300f0f00c0070740043d2059484000c194840d0b541e21804242181d840380c010b280030360503d0b900040d0118248001030040440e150400e84105070900411000911a03012102aa55810b504a40303070034105201500d0940d5108146922920114056501c0145540500700703c071122140803481da10350311100781070301106440107048002074400601c082e4044106000102200b0b2601c89003044003154a02500c0d00020b100b03d000940034000e05061040410103a005403200310406c00c0b10140d2000007a8550182640c01014151580c242ca801030303000b031064181c8130031040e000b840501c0c82407401c40d00e0701c2c2090107034500c580e00804c0c80c65228100941a81c00c9401c80052400d0005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 95315135 1250 95313885 95313913
    0x8090703031403130606060e010306081609020a0909020a03090c0e060f060309070b0301080d030506100e010c030302091801050a140102030d151d0f180604120306080d05041403010509 80
    0x141c0000c007501603030034135078500c03c0c000745161090b100101031554501d55801701d56400101900c03940e6004c88030603030041004c280d018604694030300031156066801640c607800070f101680d161195034010b00d10b140c40400d09800c1260140c000007c4140700c3c88100140d1629504403601001003070343c099400c102002800f00080c100080110b8200ba000340032510010f60328080034071190700903008982c05411603c3c1c0c0304c40b900d41601505810120455010306941100301c0020310b840032034079006041044180e02582894003a41c1100ca4480d00034001c480c040c0b68640d003510f03120200b072181c580030301c000d2080003c0d200034280a031212001d050b40038503d042c880c040e0301c1e000741000b640710b20720303007201d942000a01d42d0001c2d500075a446041400380000d458078401c0c2d1844440020f1a064085030064445928000042a000e83c0b00343d21840005110a215000310020030305038020411030f2040d400700260302508600504210f445d190081340100034030000749800e0724400e0700c03103810545c041c0750410000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 95316385 1250 95315135 95315137
    0xf020711121024060c0f080f042612040b04090504080909070207080105100501050a03022802011401050d080304020105070f02091003150e071503060e09010507080907030314 76
    0x192080403140341d49040040b0307800319200001030707003030a0302000642901c9405464480005007020b0512611140c103948908400c2195010300400b1030b400094924100c2030700704252400b070541c0d5842c00c800c0c822000d100d42d55800d40341a583c0114402d0f0310400500d0007001003103d064a1210302d0b5a42440d103000c0c1d48034041c02010f0402c43c3c6840c000d100306911916640c0450344035007550750061503028505015582114030142c0380c1e44000d41e20070b030f06105a0760014221002c28005107001642c4000c0d0b40700859048100394107064000700349420501409034150409a240740c101e20352000c0310790b614401c1000410f900d0360010103c0c5003c0c40003402644c040c0c000303032407042e0040da02c000703c032101580056a100700481d082842e09203808010720500030071100084000c04014810001440c4542480d56101003900c9403800b44000350b002c40071130324031941041d0010207040341c181c2d9040c00c02d0144140a060101e6003100010440c1000030460031001400300c048940507143c0e4002d2422810803d041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 95317635 1250 95316385 95316409
    0x1080f06012111060708091309170a0e0a090c030c03021303030c0f0807050105010f05030d020c10090513020a030b030304060e0603041a0a0509010510061403090f03030106020c040f020711 82
    0x9821400a00050503269a402040124886c201140c0c5c0c654034182008401d010141ca4402030624210b6206e0008104c040c08603845686a90419140c240f400c8048031824114203400ea005001c001c0005019011504000c11840580d102031100001c0e40030118200d0050500140d000703207501000b000403174004d1214400380c90252280102e2000a51074010301540300b00c1046070241e544500402503840c5444448020f04011400742c10424910300f4000e61b118a0030b0a4903210700c0001400500c81402419144002c00010305030f1225950080d56820083d04152030100100f030a054400300305180120480e81502d00c107403120107500302e100301444100d170070087c800c81e00c50400d00d2a40041840b0180d2084c49203000c100d0106007131401054180c29903001a108903950303015540244010344e00005c18075010509000342c1c07a12a80e660050510303028807464254020b010010000c00e850303a0200304c01120b020180c070241310480302c50003050102d109408000e00712205a40b0601d056142528041d10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 95318885 1250 95317635 95317643
    0x121021e031e06010b04050d0212010e0d0c060507050a0207091e110703090605040f05120307021008100b1c091115040303030b030a020609010c1a070801080f060121 72
    0xe450100000440d14103925021107070800034041190311801da804019880c05804101341403400c0601d09404510704444800c8020711807288118410340c6003001354000f014402d8400708444600c40c943d1000350411420006c2660301904110000d030340035014800311072450481d03500504099140c00700c180010602034611903411003000308200e60041280c000d01e220350ba6080d490756541c911600e8007801c0b032a280e601000a01c141071100304901d240c1a00a4822101c0595880c020000a02000342c1503100340e4100a5122658020201c00342c0d0707209032011701c20744c2211080b1161350b80380c041c0b1f0702007400341e8488441a03030310080012021610503001812464802e40b295146c207801480019504000e0500c001a1300f00003083c10010b25038940124004242e095010704a006040e80108246101e0b2120240c148000e0901078010031182d803000040001c440480341002d070402c603400a000300002e00c10603803144118240d140d0b940d000810500d040b1404443c110b104140702660080c01d5103610306050b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 95320135 1250 95318885 95318929
    0x712021201141e0a060b04090e07120b091002070c14060c0a060b040c030902091308070f050a0b070f020619020408030d020304230c060304151802030105012102 70
    0x646002e060303141040c000c00303c54100c00d00292040c03440e00c050b044002c00724032400342880300c00c0145142403000c80741581c1c440000840c0d8983c000514500c2e2580716400340c0240921720420300140400741c4d9a05d03000d03d180c0b00945030144040c1c8854000d90054010207401e895000d032081140c51034410910090440140c9000d04001c10303400e42d1401d0a00c4000d06980342e035100d2141259900d000d00c0381d2401142c035401e080040f582c05402182c51990010700180b0703031290843c008030901c0031200a4070300e602d500115041002070f9616200b40c9504c2600f1040360040450404120302500412191085104a41c0100702595400c00304005140300c007440952040d030700b0400820711500a100420350168001005652420140b91103254114030640d413010f0024042c85010043c10003041020020b0011100c06132642c072541444d04484621604070b0301c18600d01142d00e020300c807107110070041c240c3c0214020440342c1ea07151802c00c40c190385422100c4050082c5541030005181219282d968508183c05032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 95321385 1250 95320135 95320151
    0x150b0109090c0801060e0312180102010207120201060f050603062419090305070b032205010b090a1e0e070905191503050105010602013b010c030605120712021201 71
    0x120704a40300000007200042640c80140013403a0081003a1241d20416030040000c008220b1190005000e80c000c0300d4910003038907403441d080d07070310035015200700a070000c0341e44000307a0741c10340b02038000e152b40d100b00345603000101c500241318a06107040d03a21844c40a03000144200d0140350001c00c25003007489106101c2014442c031f5200001c8440005001c000b5601d500b54024103606080e1b01d08002c6601c813411094080081004080c00b05140c203812103500d200f8800d0301e10080c0741003805401c1642d203240c1c100707010604100b04030a20390132026001c110000302850466080300e101003034407103055603454190302462041010071203075401158080020189241070500c000c034071000b5500903105482c1c0100f00800c003801400350a01c12a401440c5500080000e009e82d0307040d07034104051305141c40501c08081004452600350440048411003100002044248540d69000e8000c00240c0580ba010714001d505511a00d90000761200c25540070340c0006100708410b60030018180358040b000c150a54a503102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 95322635 1250 95321385 95321399
    0x40906020301090911100f0f02031207030605011e0207051c0b04140d090503060f061801091a03071a030c0d050403020d03180b0c03270a1e150b0109 65
    0x90750280080c00760114954056090141d036000c0d02031030051045140031034180740a030300101c0302000081035042c058080201c0300d6084e07085000d24503030b80007080350040800c03604540c91380c80003080d0b0b1800d0300d4046408144002485008016094407001760340141d406012a1520454030b101c503001e04a00d498070b00384a0f80c0c0d04003040030f042c0d40403951410f02401208400d0000c0c0514058210f4901d03002c10441e2511000990703a50014148942e2200c848010401c00c0d241e1103145000c95031606013611440d696404800020122200c1040d2603209005d01040e0030320340403901508075030004000b004100c2d150341c410035a0781d0001e8092081e020381005984401034440c002c041c81a03000350040c0824040c4080c1c081c041c0c42c20f9000034a1800c1840743e0100019407141005a0858151502207490790340c2d40c044600da078520f05000c2c0510143c04075844500131400100c01c1e849603ca2620050b140001504c103200c2d41d5680f03c0014009003c9904943c034507502c6601c100b01800052600d032201c0342d96120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 95323741 1106 95322635 95322637
    0xe01082406060a1103070f0201021207031413120305030a0f0203040b040308040c261608030301060c11130902042a050c0717030c060f010b07080904090602 68
    0x7034090303c251150b80210201c1c5912000c881c1d68510314202140a402028002c03030041c441d46070341c05007a036020400d071036240e80c0c5070f240e04891003019507141d40c0c280c100c0c1400c2c88160b00001e1002441020f410624442d02c1d0181e2680da5403800c0c0341e5040c0c019607101556070148107004005102c0017600c45500c00c1d5000f505468507885d46d486500c0c01c2c0c07101080d194041803058120281c12104c1a8281e10064001000310341120502d14031400044010070035481045104c2c1c00030b00041054070300072189200d0075440703202ea4810b1518484000b403401030b5094442400d0b1a5240420811420a0720942404651040b8000c0001441200d0392056182c0303111110100040424040d1410400b08240f1000c1d200000ca111034601c01181071301c0e525006441c154205115410201c0c0e0040c044550b6581a911860f150314030703044254076125101e62280381c40303540080e03507540f4a0000c0703240d0b88 = true := by decide +kernel

theorem cover : BRFrame.Cov 95143885 95323741 := by
  have h0 := BRFrame.cov_init 95143885
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95143885 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 95143885 ≤ n) (h2 : n < 95323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
