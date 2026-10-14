-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0266
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:51:23.385241+00:00
-- url     : https://prove2.me/submissions/5cf7e318-5899-402c-b070-82a3cc32a245

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 47661874 ≤ n < 47841730 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 47663124 1250 47661874 47661881
    0x5030f03010603050f0109052a0403050109080301090614010504050d050c0a0902121308160f020d06020316030c050a0c050c060c030306150708032e03060b010e010e0901030321 77
    0x800041e4599080c000c045d0311405d10280506000c2e942800b1910745112294000e09000302c15004180c1c0e1610301e480c85481072000d80b0003456101c0028403161495040000345a0828003811860f0f42c6000740000d0340d813200e00e0f881041070364180c50b101d0800d03281000b08040100ca4001c180d03150300848000c4202661400f1702000500321014005855803046080000407507001866010510805840a408148601c0940b40d40d40021400e102c2c0c103141c1490704014000004800a4004505504040030002c04d03401031807190900015601c0c1c1c002c400e080440070307917907078100030030110740d0400c26055014032034440000b105000303004540030340c0d1184000c65883d40c040408641181c001009014052400015001606d1002c842c642e06200e01615010460322025100c40c9080e07000e03030038551526580c1e01c090128902e44400203c0c516640f400d092000d440100800c40c009902d01c009861990302071450449440c10240c400c3c10141e08642d026545c00f60416120020321000d010700c07803d501c0c04c501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 47664374 1250 47663124 47663129
    0x507051c050c0c011d0d02150c15130c030602030a020408120a030507020307110f0a030212060f28050c0f0708120c040e2a04080705120d091205030f0301 67
    0x259502c1e5200842a03040d41000003022680d410441d11000301070f10945440810040180222100741c1c500c8010310010310020707041054581c0344103003c160304540d64030205201d44900c01d281e00d01e079216030b20303401a07081c90340c034152005007422444181030010410719070265a00204911005250070b898000c244e161841c8028190717003840c400141d01d101e0075418015a50030142c640011420091982e90768441e02540d200402c0c01100e002d400c1140341e03955401108010740d0058180b12080184070642901c2d9802186c4111081c00c01c50045810f03400c2c0c580440700445501d80006010b81d450480c0708010303000103040301d102e018041c04140061181c060092250398411801d1559500580e0002d14500c500242260162602400108000d40427002141e0344618090705100c0001540c4040d0081d51607404002140203e0116000c80c500800040d0001654030449a15044401c0810310985c0c0b030300240c0b10140010b0440408211989034000d001e10300d503128005a80c01c0501c84011b548071500260f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 47665624 1250 47664374 47664377
    0xa031d0a08060412080105060a0f030204050603070512060312070204050604140f04060501050303030c09060309071a041d09150903070503070b07120c0807120b0301050703060303020f0307020a05010507051c 90
    0x2c200b400100107004001c1484244c9904001c40c0e55890f0000103044c2c0d00952281c80144924202c0c0c82e1120391099044802a0030001d0105440c6c0c100f020703008180f50001c4000c481d50681d0b000204240c0e1600190070380090317014400841c5004040c1d0b0a100191901800568200352248424a0000d4245103801d00c41e030000300170242e40c1d00d041d0800070190781060740454042c0d00100f040c0032074020010203c544203002034503415580c1d200d43c03180d0b500e010384592080741071829044681451484440051044851903081519840c0124580780b01c2d082c8150391100c0c190780718070074094234035034104882a44041d082051720709000c885e0b21068150707400064103c5a0035518010020b105402c130800b01910f01d0f2121003005600f0841310080e207000742c0a0001414099483d40e00001c0304441e4000c40040c240185c028420b0b030a002d1800740141c0401e000840150042000f01c3d5010b03030b0000103941d1019002403002c00150320706801034030136a00c0340409882d140510481241c00d290307680041003202026 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 47666874 1250 47665624 47665633
    0xf020307030b090a06031208041103071e0506040b120c0408010504110a06050a0914221b23070f0503160507090606020303161b050304091103090a031d0a08 68
    0x802c1c0402c0810000101280c201928154041c0302040e060643c000c1d0120440c10103802c03540301c904040004841141110703a252150140c04650b0b0f40194201543d1200106242642552134008001c0701d03005601403450040c2d400d2200c00070040185501503082140c402802d0701c3c2c951501c00c01c0342514403c503000d0303400c0011000c02203a035040007540e0000501852402e9828100355050081501d502842200d07000d915a41d0290398983e2303103110303001088617548003e200e0b2100340c43c0b8113000361040042da80711003c0c5040b0702071500c80c0101806581d400c045280d6101e100f9412541c41d0b25500058000c2c2d03030320714160703444600103102003005000c0c2000303041800c00d03024020702e446482e01d40103401075046182002000c10007190008241d0b50000c0d124400603001c03c501300b908582c80d20000040d83c40b20201029043c00f4420044020003c0c1d4000200510800290014141c00c920007a903024143d580110192030101c0c1c82171080e14103c0305544005400c4402e840009500d610850b082400640c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 47668124 1250 47666874 47666891
    0xf0f1003061e06020307020f011e020a05011b140d020906040305030310080313030b0c0d06060f0905030d0906030504140d020c031902030a0f06110a0e011b02030303070e040f02030703 80
    0x11940642c01c42c0d41000e450201e400d0901e04025141e00881c0d0000780141007140d030001071130703010f21081da0750600c1c04003900401200c2080025556050004181c86951a00000d00d450004d04201e40c1c012160b5a190a00c0c0d080c00610000250b82c06201d15003030442c1d080c032030070140359a517000800095002d8401540c4901b00050781907612801c1d6400100f940d40108191018901400c0301101101e0700716580410565540101e00340622030b180c6046d061034902400031030126005001c444400710140e85003e541d0303440c1d009055443c0311511744000818002402003040903c030783c1203150701500c00da504540c1d02c00015489440c0a6403d04260003613001039502007803505003004102c44202e02200c05002c1c0c0d9240d500481d444401c41d0001900b0300c01402210810700c40f107074000c04604040b940c80c01e0380d1a20a00c90007844108030540150005140050440343c604c8020b15507260680c0040107145075841e900015070700034800140c040d80068944940000e00c42c0c0030702c0610310400300b80e02c0c086150308 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 47669374 1250 47668124 47668139
    0x602010e0a11040f020d0e060f01080d0917010902211005011223060709060e03030c101d0304031a0903120703020702010504030210090602100c020c0f0f100306 70
    0xd500245400181c0e005003185008629a41e180d255242c070150380c0001c0700c03641c2c0402400a803150801c4103003041d003042146125947c001401c2c5d4070a1135002c88420132030342c80d07000c180c1c1c5480d45039414100150788840180148000d0801043c001c05000000042c0d40d00164080b1340302c4a00744028000010301a41080c1d102403090110606885035140c04216a60500300b402c904000c048102401d100345440090011a0544080c0384460b00081d003103a00610300020000d0000d44907010307000001e02d0494401d03c0b103003000801e07145522889006800341103e1515000d00800d0300450340504c04505810120030020240001d00c0910302071200709001007500d190301300031640d01070f0420103503502c00c2008000340c024120741d140d0040c4543c81c02585d9059140012210350003282c10295001c614603903188003030b85e0407540303d03411901c4030f40942d800300c40d60307a100c04100c2d8120024000541c01c9108810118908211201c01059004011440080113100840c07070080c0406012000b2a6980342c1c180180c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 47670624 1250 47669374 47669381
    0x50703050a060501140a05041208030403120b01051e16051c18090510090e0c130c020a030c020d06020a02030a0e040b01120515060c010207030e09010b030106050a1101020f04060201 79
    0x20001c540103011003403070040000e01104901c044000c3d4a04040b5808245a200c0d000311002400c00040380080d440540c10448520b030f200b5102103020455480050007555040c2c0100c44000030141c40c0c407410000300c100000000c101001c4140c203910800c01003c030b00e19405012071808540204024004600c1c08a50503042042d80c0d0703041c000340300c10080250718041c9803c4005080c0c43d00c00c0804030365501c454040444801d00e0ba08420308240c103081ca9505842d200141107069490119503541c4000e03141d2000c0b80454400ba01c00b080141c00004072500468061403140d030b40144041c0c00380d44210040d451b45000c036044504001c005820006401714016840808021002000c03942040902e1103c4000b8080504001c001007510b610344001a08514039901010050f40d4042c055580d9020000503082c002c0d44007030021408982c800c0d118500c1400d04060f81c5040e15079503888180b560342402c0d802c0d0b8251300b00200001c1006000d6070680b8000600303001134002403400c0704800e82c0321030800e100a07095 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 47671874 1250 47670624 47670631
    0xa11060609060619020a020a090506040b010315170f0102030f040b07020d1707050c0a0308010611010501030b06060f0408010606080a0507050a020601140105040302031203040203060708090a1e020d0605070305 91
    0x912441c00600c1519515441160500b10384104204000000301c0d40070307400c1030841c0740c001c0e45c0b046240000240303400c440c0c1c20440c400c0c03108817410810b8100c05030040d8100c80c41800d4100341076003500401e008101c60000c0f040040340103002110191401c4150030307820382c2d00c03c9400350074090f005000c0c40b042055002d8010740107c1540080c01c40414440742c0280f002d410341d5144030b100800c1801160300b4500a42c110380300000508240c07026451541000b6058200a01c660000540c45c1d0050499810040c840c06050381d41c001c410001070380f980b504011203500001191554200f04200000300680e007445620010040c0c0e0b100c5078010b15000c0180300881c1c9005118074240001000b101188a40c042075040c10b443d2442c400404014451004032854000d540000390180f281d070b8420f0028510280156104620803400c85001c1d507901c5000721803900050f1038801f582e40c0200500300000346590240e40142079140405030581c401d980000e00000045e00c400d80f0029520300500c600e455041c068540d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 47673124 1250 47671874 47671879
    0x3060c0905010f0e010c15050f090c0301200a0e03030403060902010314060306071809020d0213061418061608071b050a05010305040c080a080d06050118120204110a110606 75
    0x2404144044040e0a101141300503c0c1002905c1d2001001c10420407001440f1500b00002004286011840300c0b07401c0409903081031280c810100c2404180c40c05008541d044c42e0174036031001e4803096002c84040242c002c40801c1050120510312b904050303c0410143c001107005003400b080c4c1e0480c0d0f000140845841c5603450040f5a0b102c0108000350302e001504075041000e600d01000d03205400e41c000500c4900c41c0d005094050700008080000e00c5841d0050481c80f100d00b0440341e1078a644034826a0f15002441c106c0b50450814407c7c51074007903e42d4203001300d602003c0c004624240800a514100c4c002d500000ca50305100031843c5814800380e004a0070100f142d00046c10002c50170200060384941c01e07486038904158458001030f00308900b94040000070b0507900110340c04800b29240030101c0b9002104c403030407403910b44039000625600c10b4034024030300100c600c0d03665070741402c00c01c2c5005080b04011f02660030903141c8182640c2e0b001d0100c002c1000180f1580c64407034120740303802082c0c10448041e040e50b2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 47674374 1250 47673124 47673137
    0xa081c030c0e060702060c0c0a06020a0b01090608060705030c0d090f1e08030a0f09120203120a110a0f020f060f090115030b0601050a2a03030b012309150403060c090501 74
    0x5080d503c0f00000c1302e8096404403466911580d102c411a0b20341120f03902c100e60030420300940020321a030001911804c59101e01070401a44c0c4e214000e41c81252003512545500d9803140001c2030b000d5002c0c200454101600034081441c004007919090151a00b0321400c691200403c041d0340305101324248142145014180318403c10174154654030050700000c2c0c48018240e568031030156010303d03684d10a111140c0e008844213844104108003940700d030044a55a5520000301d030020385508403a1041000051120034600d0508c1321240741244c07145480840c0509510444000c1d00070034904201451080b0b100c0d8aa80b2003034a044d19103079007911401001d80a4440521100740000f1710340094840d4040e03401e21b4029252044004101c80c0f4046090018080c0450720000444000e0201c0035030003168000d0b103051203654001001141c40303843c2c0303450b0010821411401c010705901400300908401500500601e994048041615120351040d4801c41d0348956420b01d24195940100c030b0032000346801d08119 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 47675624 1250 47674374 47674397
    0x80a0b010c060b04020903060a0902010f020a030f050a1103031003050f0a0305041202040b0d0b0406142214191e03080a0e0a140606120706050a08060a081c030c 70
    0x80d1450362034401c000d240907143d00d07904009442d00e5040d1515450010111080e5003000000c42c4028014080c007a800158071588a0324658000111111400c3e8165580400e1480b180b10403101c50f08000003d00400a001d94034000d82141003029500131009441d410711b100d403462402500d0070003201d007100126006000244082600102502c08440d41d112800c98900f0651001800400008070070350380c404614001101400101040300f48202c1c030602c41046107500c0d400301070660031803c40d80301c143c540e40307810911542c011001c882d00613144078050201c0f00e0180340c160315040003503050744203846061011100c01030090a10b00100300d000403103c40c0d07240004540b0000d251110060203d40e220340c881d45001050300c4200400c040c40c6802a10b2080101054040c0c107445000070346540f03104038402c012440070382c203000c10f01504480d2141ca5080c5000070315941501e01820040446510002400d0000b81c580b41c207004c0008a51420191860b00c1e4070700840140c100c8a0007480381d010400b018035070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 47676874 1250 47675624 47675627
    0x70206090304090f020702090403020601170105060f190f080d0206100e0402100203070803040807110406080615030109051006060f0504080307060e0a06110a0201060b0c0c04090c030c0f06080a0b01 86
    0x200d0781a20400e04004c501da80020200070068403c81d40002d422900e280104001d2690118410f816602003001c40d406044903032203140d0036180c01f0303181da96201c0d4180b80400c4192070405445100e891410003c2ea0b00950b40303c084411035010356018608680201541c0440d07940e044c00714139480000c80140e000342c2400c0c00784200310640000c1009021382c00544902d44428020070988684550280329941da078034140c500700400b038000d401c080300c14280c800310409591601c1c1c0204c0040c0c1d25040000c2c036440c0e5504c1e00b811040d020078003404e031b015580c40c901034010920500003680703200322541c0c01192980c44c2c42c400401181c129803071303001001014081407003520400b00807110b00741d0300030b1030103d28a00859110703030500780b441a008040501c0c0000b01019540d00c1c00140240c15a65002044800e588103820b407010700c19403110040c203270800e00189070a45055402190a0b90196041824580d103030f6075000904002500300500070f00c0c0100c010460580e00a2440350700c50900c140520905440200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 47678124 1250 47676874 47676877
    0xa0804050f0402070c270510060f03051302091b03040605150a030305041505040b07061406030a0209010308030c250b130201051c11121e090316060902040f050f0702060903 75
    0xd50744800c0010a43c0c0c145031b5441e8100c01054100f00c0c0410070190622080e403482662140c495003001c652142d514101c03e070700078403d0758880e556101c0700b20035410959013040b18107140245503403241109101c002180a9520015510943c0f14210015003400c3c20405c14185441d410380503441283c2808042c00000e922800703840856603d900900540810b001c3c09a03024000e5400c04201c040c0f000c50003a05025031034004209000d5400000c034501c1d2107113018181c59110f2001d000c1c1d04a044400100005800c1d40021940480078000c001e0805901001c04414a0009604225101d0030a1032800c00c1c400050551600840440d02800b44918168006010f41c041c040080011440040b141c12048125030401000d80d460a2065640c1d41e0514155a41030710b03090f15117205040010180013540c2c1d81402080740075100c0381000318100980c080846110728a000c0c2d08071a15510303201031100603101d0f07001c0c8403c0741000b520007040c6071030040d2080f0f00d0580000c1c1403d0455201d0014001028070100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 47679374 1250 47678124 47678129
    0x60b040510050304050703061a0406170d2604030801080106120b04150608030f0408010f02040302030a0f060b060403080c010b030a030807110c0907031e060b0a0c02120a0804050f0402070c 82
    0x62040d03d95840c4d0603c3c50514401e6030024103041d0030309552050040c0300d1071880c50058000c036400c22030140c4803013050a07500e480e0307039400006900c00340c85121864050710000c000000e01100f0303141520141035031600c0a00007945d040b0302081105d401070220076402c0c024903000c3c08005241c00c0744040030b07441c0c03515960720203080900301c6800c0203a403003500d030082e4005070040e200e042e040700d645186450520040f0350181c0301e0040359520346001242060380a000710343c02c50b80c000700145140492910340201100b4864000c468041d07543c4004c50090325110081d00046000340c201540700d103030000700e150039582c0495020b03110303401c411840c8000940045005410078040d14107a1019840740140919001e40002c401c1e901528420800002e04da060b0440b2580d24941640f103155110b0146548080d10f5540c02604108075003400140510740c42020482e0308540010f11700c4a068844401540c10010b080005230303445400040c0a010a0500c000e40203188201a9402c516104507a19224076000290 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 47680624 1250 47679374 47679377
    0xc110f011404020108040f06060803190801080616110f0307060606052812090803010503010605060406050d020a03020d0212010302091803040b0c120406090e0606030103030807080a2706060b040510 86
    0x2540030405000800091f00182a48801c08200890b1150075196994000d0648804d141e103204e03401000c1c4a2144030003034101c0f00d03848010701c45a161101c01c030000c007804240c0101001050f030484d500d8000200946c4040d40111400303166a842c05041100550750039130080414441d04205238130a409000038540003240300e2040074000524440c41c00c45520002407030704803841c0d09181524083c0010500214120b440c1100200a01c0b995403043c04202e01851285002194044c828110214013640043c403000d106480c00628008581003200300700e0304001d00d002d4000260500620841c202030300420b4001a410640040501e4020300c00c0341d49100c2c60061100072a004a440341d0b00e41c0c01004010310703200f4226800ca40300c40d100c020042803110300c2d00c680040d00110b000820a00d007055403c40341a250960798034600b5955840b4141c2d400c0b24003904100000e0398072424090070304501c030f4101010683c0a100380c0704151450500100b6110540c0080206101c1000100030a940d807442402c12140705 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 47681874 1250 47680624 47680637
    0x1204050603060d0303020d020a1707080f0a020a020a0f0b040605090105010b0405041125030e011b0209060a0f06020c120d020c130e06070509040c0f090501050f040305010c110f0114040201 82
    0x1e113411006402200e40000b41703d070010a06070305950300002e41d5500c1040c0c032840d0b02019a145034086032040ca0983c0d540008441c031102041d03044840b50000c000e188024011600650115a61041480c0c0b4800b03080c2c9000d07011009100404c08035000700d9810001001c02840309504104a00c201c91080d40305092140b80d07510101840d92690a0903078550504403420340d41c0d54480603507001d203038070301c0460100c001074920b4aa200a540c0121012259503000900c1c1a0f23140d07046a00b440b508001c060f000c02c0c1e000d14005000103255002c1d203c020080c00c4940e01910f01c0e909080b05108841c44140c442c80d00c590803444071203140d13541c0002c0c1e00030705078001c5070701d042a0089411150001c01107400412400c4c081c15081000142c0c01c40010813010310151001c1000f0005040700300d65514024143c1800100e000b2401c000301c0d8807400280c44610504139040f4074081e03a90b80e981d400c50380da40c042d100116a180341d01001c0f000e010701038901c820a1020090040c4e55124003c101c031044c0041000b41031203030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 47683124 1250 47681874 47681899
    0xd02010f0c0c1707030308010602030f0f160b07030204170303090d05090105070804031208011e14180109150506030c040608070306081911060a08041103010b030712020102120405060306 81
    0x180c681d03007001010b2440f0307116280a0b03400f0b5503075221281c9000643c086507c04000090180c800800c075030311102608121170a00f0705211170b8043d50f90100c150001000c07100040030300481c50701203100c2d02400003900d0050303032a4540590305404101030701d510600c5400601c2002140c40021896020240e058581150b490741e0b80c0c801656640130b2940003030000322022901108101c5d000100071513482150f1524002681c0e1085414000c1c481c00d40c2070016059420401c100803040c4254851030410000c101c112441860f1407145000d2f4001da208800b85900d445441080805510504000c3c0900303030b070600d2942c50422038907942880746124050810003407600281c42d0f41e200e64012006000030005540c068030310028003602c00d001ca0071066415000060340309610b032410200f110604019611501410703600c645030783d1a48030700343d03140b69019500c5811f0503116a500b48894000380130400808040e440c0117000085c540407048252200c810000c00c42030150b0f40c0d0b0103040e60f902c00411030307245c0304c03285 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 47684374 1250 47683124 47683133
    0xb07090e060907021516120525030f181a0c1204080f04030b0702010e01150504020d0f0e0303090105070806090606031803030a0204030219030201091a040302090109020a030b0d02010f0c 81
    0x500c80c540c5d031050400e08800748070b2121106a02d4240743d017650340d14540c06581d014801d00454106580d503400964540c8569828908004c500030800c98032810b0005078070308001c04903401d55242d6010151a43c410324040d104002034186900302c0142c41c16003082051800c110720b0800381c4079405050504400c102c00160405c05010212808038510034000c40c2c03600c1d44c07441d02d0500700d030f000c2c1d6640c0e0165091007940001044c0c148600d41640b12106400c1c1c20a900d86000e100084d40240780d41d0052684405484014000f82c0c0614480e01d5014002150381c3c1c9400d140c0b00b82140c001810000070030410b5003e103c12680d90640ca981c100d00304039240c0c1d0356519980d54581590034030201c1c01c60b8901002c000c10210110550240ac204d07802030310507420320120038422941c0c001c0180030082c00b04010000a020b0b043c20500541007440c039807000c5030700c1c0c191a5000204107410982c040091030b0340001d020401070354135008a02c003580f001d0310b243d0702c1c0d000c00b60300280160307110035600e100b0015840600410300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 47685624 1250 47684374 47684383
    0xd05010b0303070309050f0d0209071b080c0a02030601060c0503030708070c02040c090612020708041208130e0415090507030605060402070f1208100f030201120207060c09030b07090e06090702 84
    0x540c0282140d40d20b046a207005010306405104451151302001109103071404c1001101c40c0b035075401062a80942c4c0c40302c0043c1c1c2c2c0c0811107214021301c040189507090000d004100181a2424418000c0c248800b040c0704042c60018140c01010400800c0c405620025900109aa4010013181403450481d502c0050864825881c01c0010350f000303040094008049801011080a60303600e43c1d20300109040ca0344000e4160302c2800c00080185404020401020110104032440d46219001756403508c0d24501d0040c0045407190021107580f00c00d41c060200708110b8600d0310520112002062000940c16220a9150b000c58840505419202c900095041d95580d0444c2c134016401000302c0214040c80c00c03da00203d00c0d8084d004003003500c8a010802c01803030549180b00300c44040082000860944c2d004581d10201408135805c59602846240c0000c2c0340c0d800703110b0380c41d8455900d40784014694100340e08483c2c0050200d04c00d001507200c05009500300c0030411503000c1d50a0f26030010689601c80c1c22440c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 47686874 1250 47685624 47685641
    0x70507051c08030a05180307050a02040e03040b030f1006170708070302160302010b1003020310060507020a0e130c090c0c110a08010203011d010e0601200f0706020c0405010e070801050d0501 83
    0x52180c004104850b800c0f46900c0356001e1648007001c0c000241d00440143e90340d08c160200a4141d83c420f442c120014601a0869415121010b069a041c0703565184030040741d8005035400591744280600704003400013a00d00e00401040940340c0f1141210710708540c2c110b1580c0141910040020301d40000702c003240a901112010f407840c1c044c2510342a0301c0e0800034000c013410009a41b08843c0740140d542068842cec020f1700d0140001140c1031806070303c0e161090b90141c1c0601e000302d0700034810107400a00b011507201d680c1d21070b03030a140d8039120704102c0d071400300c041d002c190304183c1c0a1880c14900c200310350791000d807900703d46601c821032200250842000801c0c000e407603132040000e0740c000000400d1440c00c0400c82200001c1d20f21400000d641c840003428141901128550300207080541448018021070310407124449908082d030303030020040580306050031103075000700d4056844954042c41c1801c05224260040503c020000f415040c2294000d105940c107200f15446241c0003040d1105000081d801800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 47688124 1250 47686874 47686883
    0x307031a030f01020403060f060e011502122107020604171309020408010b150a140d0b0306040804050a0605090307150909020403031805061602060d140901060f060203070507051c 78
    0x14400c2c0070800700b0b0207540a0300044426905154011a80b01c805010b20425915200c134441e0a980c01c001440d80e030001090130f11411845186030160042c2d01900082111904c000212180440070400355240f1107406801c0108543c402001c010214402d0f90f0000152540c001c1d032241c0d2802d01c101c0300414401242c2256407464400580000c082c101580300c1c0c01701040640e042d620340c208445054030b00380079a080810218004046e5002041158001800c05206030000054450581310209203440000c80b012103606000042c184240d1400314208002490285001071030f2402400c086516083c0c0303485805650b00741d018910006600a69084010308070301d000843d00d42d55203040092501c611001d06500e40414804081080d05040b001c0709c41080070303401c08000290959003400f1079507015401da038107400d40d00c20780b5001081d400c24129015040100002c60b0003402c0040c400800d4100b9404801907500030801c14002a0000ca03560081b200200c80842ca241000d00d56240c51a101100c01072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 47689374 1250 47688124 47688133
    0x80603031308010b03010606020a0b0c070303140f0108010b04270507180f11041202010806030c1206041b0302010c08030903040f06031a060a05070b100e07020715080c0307031a03 78
    0x2034542c1056104150f0900c0440082c8180d40c0c3d00c20090341c880004000c0a000909100c00241e503140c407410041070510310901d0002050a02c0300c500854150081c2c40300343e10150554010001d9040034007401442080c2103a080004d4108014451109483d20440d4107290590400400c10b1140910208004100d82c03140c20b400b288078010113000921074940c079007000034501480300840800e5035080e40c040d1001d01b1600c840210840d001980c3c046002811260306114642041c2c0310fa807561024110804003a0b0020840345c105454a83c0f180f18807000c5040d90022400400c1001d40e034401c0a80b1815900841016501c0e1119000349040d4030550308030007140004000002010303a4180d0280c0504141c04040c80b0901d03a803442082401d00c25410050000f803018080e160100d28407081c25034200c500c030710404070050b558a10ba04074140040780c400d4096049440100040109c038021002a42c1c503134580643d841c03500c54210009404098507400c101950b801810300080d80448a48001400040896 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 47690624 1250 47689374 47689379
    0x804050a080c0607110a0804140d0c061d060906070f0302071208030106021006051014040513060503100506031e01090b010f1d041703130c0b070605010605090a05010806030313 77
    0x3950f90b580c0c1921400006030070100c60a01590011400d6880744c0d5000c2002e510b00303071a1081203041d8400c080030980d444130744070404c1c0b40081d50401303221008009544428080702516003003142e509103203081282c05a141041007071a242c0e18081142c00d002e9028080e8160fa080703904080f85003078026001056802d01410703060052101c03d0300550304890b01c81d42141c00003403c0b090341d4800d0f40d80c984141038100080340800c6260740c0c000d95a4030201005200c0c0c007802c00303036038400003504080c29007000d204207a0303039000c14015420b00780280703035142c40446004c0c03020707080050200b03a403540500c1246000118071081220452020f400c90301c42190000c9076040d85584900c41c0150fa40c8070b910072000c0035042e11005403100c808410109100d00d4204801c444210300c40a1a45843d9100074400c17019070030703881c0142000503110f01c0d00c10003400134800d2050b00d410792850b00b24119038040c3c10041c144503040c001d200840c0c4e25020300c40c0a8640a203808642e948a0310003003441d501a0003400603000e103400002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 47691874 1250 47690624 47690647
    0xf0c0512041403010b1f050d140105040b010c111e040f0b01120606021e1906020d06090b06030a0c030b060f030402031504151806020403050c0a21030804050a08 70
    0x103481038442c0a4915a000d4001c202018202c603050b180954000304805000880013200003d42c000059030703070928600e40828440705908846012068000300310400d40103000900340303481200751810003070034900311a4404e0744415420110b81c0030034900c10803105850109500749501c88284025010303000748148035218a48401512958802c240020010756000801c2803182c01070404880c010303005007a44880b2003021a6003400400300100c02403203044100d00650a04004450825005020058a0755000c0d00d001042d100300b41e0250080d1801c05c0c00d0000c0ca9940c81c0101d0b5001b94412200081c0c1c00030f80c4a0a0b00500144003000e58800408241c400d840c0aa0300001c500c154421015607540740b80c1e0a1400325201e03019100036002c115110501000b050007580f000851000c0d400200106105c035035035200a1fa8410381084441d90416803200025007003d400c0c81c8040c107005260320165625010089101403050340000d020018204045000d200c8180410044590484c030665590800c0411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 47693124 1250 47691874 47691877
    0x20d0305030f09030301150e03010b0a03050a120504060905011b050d0e090a020301060804020d0501150603060303030b0102070b0d02070c03020a030f0201020d08060105030f061f030501060e1c030f0c0512 89
    0x60300045102c003840000c09040c4080304582c165000c1c2142071881ca0b548040480709420402c002a815640c5c8550303c044660340c3d400c005d0015441640104803103c4140707804041100f11901c3c801c1401820b00007805407a070048003a805598080c40e04603440661030403451080c03500a207001e0114011085a032940590109004956078000d590000302a201c10380160704030f100910038500001d4080b8041401450b02071003159910b8010000072801d54642c0b032080c00070241580c803202c0883e5449004104043e0580107441c1120002d0003d016075130718003585012030f482032456800500344d0004082c410084880010f03400b40d50080c010860070354583c5060501100200030170307805449414903840845d4404c403a000d10980d410780d0703200d00311f80b04c0750f2030400b52840141805a101c0402c0010200303564001040384501c01041c0c0e008030f80e80d45040780240c04d0980d098a12070080995403074030340b40c600d51800c06600c59507040c5403049241c0f5542404846102c00a00014441c0c028032119500e101003910 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 47694374 1250 47693124 47693131
    0x90c0d0e1c020a020603040b04170d0207020f030a030c03032c010212060a0f03020d0204140907090510050901030803070219030905030d051224030706020106081507050f0d0603020d030503 82
    0x56400903090074032060766203294090000394414420000600000d452400385600240700c1e200f4101740e4021152549140d8128000e070b480340e0340e40400e148055180410580d540040c0903030107880101e000e600c00408481d841c01c8003400707041d103845469502e14510b4074454250035410089001031190111003c2c041e52001ca00200c051100b80045070703032441c081058808a03603454610094080c6142c0c00d00000102c5440180e074041c0d07a8444400300041c40c12040d52060304084e029081e56400c0070001c904841d40548010b2524000c0305081c407942c0c403108150750550750030098858495595160407031500a119030340c81900d05d42014807801300354101d0189410b03924110117079032803241d00310000ca40b50f004000541079520040d4001c1000d40c4492480811048a05281c005043d8000c00c04a481e100391a40180c0040c0c0d0b40390030400013181e05002d81240c01d1f1802c01c15028a0a141d1001000c0b80152450000d1420000541c0c85c12544558003800041d0350261484810401a05001d00b042d003045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 47695624 1250 47694374 47694403
    0x50409060602070e07110a0606090506120f0d0e030c150d05010e04020112020903150c0d050a0209030a2301050c030f0a1103011401030204090501150f03020711090c0d0e 74
    0x100d020071210700105105041e03800c0079200701c8107070b40e8000b4100c6609064081d116654010b503080107001c54854020800580b0a4190105050515006001270030000702d0640e00c4a4100302c48014921002103080e02c141030705c0d4501000d40424403c00a401c00a08503100c0d40e103c120b5034165130400c1c26480141170041d503480c84c204940d0f81c0c3c50303980303520203841281c0081c00952149000e400151035940034024040000d0100d91000c1c2800c9549004400140c400c05002d03000860080180b0440b0b00500b5404030304030b0001d6040101c1800440c2d90364203400c0009016a00840f49100204059007400908071280002840b6500304180c3c07400241d4030656a40a500e51910700081c0000c1060096401800c07501c08140c0c42c1d03a10f000740c1189480d1085a03d10b040540030400007514107000d00a040c080c0030100000f605c804445c131005410a2013042900c418140140b00c1c00e40480c0c030301c600c02e48000310203950803007803a030700c0010681d841d200320718140c0d0450345805611958260005101014810361 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 47696874 1250 47695624 47695631
    0xc0d02010905061305030405121903090503160f0e0711030f0703031103040b0c030c0c030d0506012705010c030c02030a03110c040204030c0b1605070e07030b0907081f0510050409 78
    0x18038003901c1c1e204135005400792a5610400041045051010160f048150510182d44400c405030004107003020b03512000354000b405d8508103101d0b0b850140080980180441482c0c035101c0e10300044008162558030402c4a100901d200044a1500510045105001540c107036a680c40c1d18100580084d0414401940002c2c138221046203400100f4003103a00031500300d6480981c642d1b906000050940c00181503405045003402050803500b0101b010301b41884030070f0320200e041d10303050000400c030f020031080360b0000b4030704542d001e003041450782100320941c2c6082ca4900c49000d207a060035202c6440f0312100940620800e0300c0c0c072080c036500640d40a00c050346181650181030001d010001130b070040d800043c1000000c0341082000f84c446030001c010309600c1c0750b4002241c02c1c3c01e40740e4a0816089520440021607007500f00704146c3d51600c904507007440125824441800e001c1da006008070002000f08410010b0f40401d600d203030402031801c2e00103100080c00c60300d00040008005006812500c86c40e51140d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 47698124 1250 47696874 47696881
    0x90604030f0519020616050c0d030203040905070309030c06050402030a0818130203060102030405040e0c0306010e0901050a060b12060a180902011205060f0603040f081602120624060c0d0201090506 86
    0x74581c0b00149440c4c0041c011800c10410381401200450040000c607614032a8030017460503a1250044044201d010340c02031525640352901100035910018000c004140c6032008600010b600180111030107a044100058690b5651020910f01103150b80f015080c80030200340401c0c4103c0d5a04c0c01440810180c1c1e00c0c0860030941e642801c280d0000740c1c0d01c10b0268005000500450502d64040036203200d02004a9900b8841c00c804070303050240a03003081c01d01d54402020040f0740780d4240603a0b50081e036444002c01c403c0e890000340d24440d0054010410f110301004020030745aa03250884280644081704001c51003c11aa503c60000c04011802b00d000c14a4848101d00d1220746214943c810000030f818000148078503010020507a0004008903010b4140d0341c01000801c81c078901801c2105030030740180c41c80c8200c40c0104201e040c000c1004130019071060082064014042d1849440100c51031410809a4039040000d03a290280b00440c3c5820310902c050310031166415040402440d0150041c0c50a075113 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 47699374 1250 47698124 47698153
    0x203091e1c080d090f06020a0201090308010b0406020304060509060c0d0203090a0e09070923070e130203100603020306030f010908040f0b040605030c0d1404030e03160609090b0105090604030f05 85
    0x40101010700b05503400d2220809032225034005214552168a20480304040e039590781080342c0001c3d0312000140c0d500e017400030815030800001d030301504030080480e04261a014009603284a140180010403002041d080107175100c1409894050307900d0303400d5805500310540000e640360403c030000e62254048a10001c1d8659480300d00500503a41c6201400c903007802d100c4200058041c0c001142290794920ba5000140d55907c2d401038013a08a0382c1d5481840c002030b800700102105034506003e600b42c810003c0c440c901c48421220011518142409038581c0d40b010006400c1c00781c2c2c207130950304030350a212401003003000740c80080060301c000700940c1c11207039161300300302d04030707020340c1c001d07940031541c00c0010414400030388003e03020403195036402103480d100400640300807441c2a50201c4c003142c09280c000030f80c1e14061201c61010300c0b45c285100910703407411500914640c0280318041210b03540d0b06030040942d1103101110000907010381455500e0b641c0e803400c207a0320781c080e0320250341a00550401c0315640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 47700624 1250 47699374 47699419
    0x10903020c010e180702030f070b0a0506121515060706020405040608120d052203020606152b09050f0f070b0a09051908010f1e2a0203091e 61
    0x400504138921000f08035120b4840810060064415848140101644075408800070300c00d240c0f24200c158803500742040c0101c185c0301e025203c14800e011416011500940c0004c551408541030702c40c50b681074840310040b51f20003414aa2141d081040010350200344600d035001081210016103003042855554000c1a0b261043d040002980e0314041004440302d034082d4204030303000200445244d8900700440071062010132819000c0713026070000820880c5a00d8070343d45425046940f60340c0385181030382c0310501211800c5e06402c901300443d4080360303406541e02c0d15070120117519840740480d822400c00c4585c01d6901e10506004c80703c2480780140108030b40f07404105841076004030f81c03541303c041804c00f420001101c03241403441000c08211140004e8441003401402403c841ca030340c4c001803107050507107510034000070703c40c80c6180d1a0130071845070054140704034601a0014006990002a60380034012401d521031101e06503400500f1620700800f08442002500c4080f404403a4042d141c00f49500f0040c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 47701874 1250 47700624 47700647
    0x204090203190c0e0601080f0a020c10050105010e09010b090105070f1e0212070b09010f020a060f0b0a08011107031107090c080703061d011406040503030336120a0311030405010903020c01 82
    0x2000b9502103028503c205502d203270807025032100076042283c0e8200d160f00e48100304404400154489004014130b5800c41d010030f051800581b01c11f4003940c100b220058081c810110f20381e0411400045203414000200034807081c11741d000c22480c106150816031700d120203c0300102684205420307030700c241d0120f400207480d03c101c42a1140c010300381943c00f070041d0707800078102c170700901540542e00d405000100f1a220b0681714040c1101c0000d80e40e131248041c00003141c443e41160b01160300d44400c0c80096024035007521045a410f180a09200450500050a06081c5d40c02404041e0605031048003040c0c000c00301c1480340166540030812550b40e40700d220136043c98140020a0001c02034014404115504d601e05c125000241202e407a0640e6036001c81e1551703000320b90100500381036030520680c0c0085007404a002c800c65841c0e8110341c40c600315500b170700e80245610b0603a000030f000a5414031640642c00c01000046002070b019100d160900300342c3e0191400c11742c120014001c40c034001640c0d60251142c0f802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 47703124 1250 47701874 47701877
    0xa080108031204020d08281b0209060405040c0b03010312020d030204050108060f060c030d0207020f010c0818030a06060e091c0e040207060e0d21020301120f0204090203190c0e0601 79
    0x901d40c0303c40d0280900c0b00c1e03400ca410b50b6044800c00c0000070351040d0301e148024150940f101d010021449503801010010358503030200355541801c0200026075031704e601080d00010304440000f480d4980c1d07e40803d0091096119517509400400000140000c407803460007440e81c00c2d000c0e6400e41c0080e43c1c00310100e200d503004190108504901150740e07410320403050140c07130801030151454503c0f0814080d2454000c3c6000c2e4038501d40000341c0200f141806400c02e10021401c0c03c01801c14041665100000c0c00754a61803010450002d0395544255000c0050055098020004110581e1540c4881082d80b900316000c0700c4602c10070820030301d0807400044c00c00560714650703242c0b05441418000c100280d44425016214244c9075205070904103030520031103041840c0303911400d0280c540080d000d861a802d03140242001c0d44188010480100940b00c0e94a1840e1300c080180c02c4900315100040061901040107500340c442d003414115110b8001003201b5a09005910950f0400e0f6242e0100003a41000c1301c4050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 47704374 1250 47703124 47703157
    0xf080307020601062d0309060216020114130b0a020a020d060b04141504180605070509100201060f050d0303020c01060e0109060506030417161b0303030b0402091503070203040b040b0a08010803 84
    0x3442c0f0302180c0c5171039601c1400b510b00454510a01d46a4030b003a43c1080d00116010106d03031080d5021981c120207802218505034014604000407001362601307221861240c0d00420000042d20045940300348010000507a0040c400349000c012410540002c05402d4034090086140c1402d40342d4038050503403c60f208403d2030205540c40c00300c280a02001d8002000c94044026889141e0400105c950041a10845155450645444210301040f1800009444c3c00c4c0c01d40e45008414440c02403003100301c000366841503641020003256807604a000b072150300309045d80b6519010307010400c241043d2000d41222031000301408200c0d250002c1140707610007501d000744083c1d1940300501c60b4500ba04003030003c4c101c4a00031035650308100d45070a0803c040000c4800034038007880205104158140c49900a20081901c2c00c41c01c20040401052442c406480030070200d91001c0001048103208008641c090540c03015a943c0392a0f444080010f0394000711f1183d404920741c0700010460304c80000c1503403048903a0781240c070f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 47705624 1250 47704374 47704427
    0x2120705091f0e03030d020c061f050d021f09030201031b080f150901030803091501030f1401060b0409020913020901090b0a03021b15070801050d060b0604030f08030702060106 77
    0x525002e210015801e0051400081c40a6602800036008030880c3c9140035955003481c80c8414101403004010040c86e080e003084100b040601da5900c0420342d00c0c2900e00c0340030442039000041d041c0783d00100e40d045005031500380000d545e9001040d941203030f1003038809002031040404000f40000c00e0075000000607284800191100c00d242551030307001800e000d1109000b01c0c02ca07001c1080c84d04e090700141e48034040002800b410b08000c0241d810b402a503003078078419a504560351608051107141000d07102881e0190300d000074040c213610203002030020a003002e98a0755924042000707500050a218031a110790340030304185016a000700c9803026016074481d1030244c101055515290000419007041650911130010241084011520404890001081e62595a0300c0c0311510840003442c200800c84401c00411503508d60b01c0d5039640b416404040464100210404200c00340255840680310503070114601e001d00a640f00150700a40c215400d4074201e0f0388402c1c0030385560254100701c60070414594002e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 47706874 1250 47705624 47705659
    0x4110711031c051c02130605030403090e01060c1b090e0c091005012c0d06050a0c02010902010e0f030f0303040b010602060108010501050604030605040203030d05010b040503070905040b010905090312010303030212070509 96
    0x5000040800c05001406c2401006130f0881c0c03a529030700510b000c200c0000c00d00c01450b8012420038010156200040415810a40020701c801708802c4c004222004034240d108400c0140464500540300d12001000301000e2004655a52040c8408060284000c00041242003034183c1c01c0b10305558041e110030034058184c0691803000844480327406111151038a0260481d6504020381002a0180d80041228106814580d08880c1910543d0040da807502000701c0050f41c10040320121850211180d801e110042d0f0042030902091480c00d08481c0000010801044140c2070018140e0b6031039403c685003a81c035580a642203603420700625520000074042080000c0709a01304070341c410300c040c1c1501d081446c2c9001483c00c3c2c2c2c4081c0c000401c0d81e0000300701400b15050401c1040d0040c807100c9021b000c1d5042030f80f528004040d040c000c03598400d4803800010100c0d0000c00440304814101c2d890b2a1403980c0d87d040080003900044084800c0889080c042552148070f00141c5900e444010100716096155402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 47708124 1250 47706874 47706907
    0x91e040309030816020a170703082101080a030f080f0109021e0c070509090102070b0f091c0905090f09100b01140c0102030103020f120a080904110711031c05 69
    0x422020046280d101100140d403030001303004d4076110444140440031a52042009580c940d4006503013010314410f809111541c00940c03a800c881c0c002d003501d80da80140c407183d291032052301d101c40d8681052150000804075400500f08038850301948d01e0325003403920150111041041550f240c1c0c0c0400d21000103000d48603066000740119214210840b0542d110000b0404440c1c00c010100101504100d00400a6047c0515842d034840307072404c02180f03003290f075a84503600c03c60043c00d840c50304c4407990005443c021040004c01c80d628503052003490360700100000107049122a02a050044003a400403915884440c4a0140180b04c520041c2002d038560880c04401000c45803620b50400011202010040c02100000c0082680c8480050380e00e42c11030044c04052640c070300c00a400b40544401c2d10150032408034041c80d003079500c2100b00790340705064400071b001303010071000c070070f1400c04002038450420980305501034204a080e0103803501c801943c0102c981d50000e08a203200401d004001ca03605100c002c94 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 47709374 1250 47708124 47708131
    0x1090b040612061a090115110d0f1d09010b1c060b030c0706090206031812030103020609100c0605010f061205040203061f03150c110309010905040b120f060a0b091e 72
    0x408220700091360b00003e02da02d2003c1c0c0c4606c070310b462403a10b01d2080b513a20031390349494010a480104004445034000402035071000f4940d07000c20a01c05120030304e0b000000c1034080e00d0a401044030301075503160203d0000703d1703105102d8400d520080002c1a02150014058102100c000c03000c081c0c20742e034503c25106c01550040030300300e90681c0d69031740c1440180e41d501d000e180a14085800c150b0340703940241046103054070510010b504a042800100010307070f54081241c10990003a1560781224140e00b5054560300c003c03420003000281050008900e01c3e000c03c410000312112950b924000103d500d241c02c0c1100d00070390300139406d508144001400f412000b900b905640c0da040303254040303290340e98580d411450040820464030a4440702d8a900041d0712000031065003044402652078540390500103812200b2900c6514099519114643e400390fa40d02c0c82d61210a5504064500410500c0612a110042111030765941498821021044e0806401c514400d8a042c460890001c044540c0c449600d80c008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 47710624 1250 47709374 47709401
    0x50f0409020306042d02060f1b0703060b15070b0a0b030307020904060c141c05100b0a0c1502092202160b070e040c0519031d0601090b04061206 63
    0x10411003006880402110384164000d0b01c240640045110104566040e040c8031128080300312280100540c3c1e9840403541098010500c1c9580c8481640720008811441c01410546015a0000005200e160b03041010100c00c00c0300c07070880c440c2c107405c1040780d41d0080c0d0601405105c99280024007841407644180e810050080c101c9080c100c00c0d5001450100b4110f408880c0301381c84540480301c0701e410182d0700c202038050320701031403c00310000403140c818258100310700b004e0341d16a00401e0070b000211015502070306440c030038165500320456000c0e0201680705401c54054001c50b0002400c0c80880c4295054880010b0184c801c4002d07080b408820b070520350a22960f0150b003005040c580c01c480da6401c520183c89011010100c3ca016074010300341110040e6810b000314281401d40101039400000c48061042c1e00c1c501c501103411240c000c4009203001c1102c10340740500000007410814000030024100c0b04084410702c8805251014402075030114411008020800489840000c019400c403a490340440c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 47711874 1250 47710624 47710631
    0x150c030e04020d0624020d080f060d080c0d0806030105060d030e30070501050906040923090c090105030346031b0309020f0114120106090807140901050f04 68
    0x60343e032801c1c01c4900c0e03640701400544003101c503460490b80e40444070101400f01d0015146c4805400005000398000030700d80701c031011300200011140c0d900d454441409a81000c0440d440d801800f00352540c9490b100080c1c2c1c0420181d6000684600e814022144102c002030100c603200149aa0142e5400c82c81600140d40708000e0400d0701d5194001c11802d05201c3c0849000e100924038902c1c0c00d900f03050451304001c1c10400204111061170b250070701124111045c01000103a40040c0340c904002c8000701191805a684043e000c0c09000000055915009002120069075990340c0e402015600e1050003081e508c1d802c505101d90303c1e10008003c110481514080a07040d0110300440b84a544c458101400c801103503941615000b04c0300c00d8440d0158606450508001042c010340002e10f0800d843d440040c10440b0722501031100340c4000c400e5901c280400e504080d65541c480401a1070000c0e04e00802a0601c140c5500081c00745c440001030b035000c1030140050f142e59080c80140085020b0054603240c02689 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 47713124 1250 47711874 47711887
    0x309060304030203120a0504080702090601030e0a0813080a0c150212070f060b04020306090408030a020c01020309060403020c0108010308030106030f1b020c01090515160c03020d080702040501150c030e0402 90
    0x19120021403240d4407a034041c503603d084c015042c1301100d0000e0401d24a203460282080005419401150780a58045810300f12a9513868012805040030080d44c0900b8040d1449003003c10440c400030301240c1c6a480141d030001c5858202190381e0b0300e0300000c0500b038105044002c00c0070b82102c0120804609041c030582c0c50303041c107020708200d0341e900408045a00b510420348003004d100b90f603c074580e13010754111020352950610b04005080c41501802c06088050000080b880354000d66046a0b07245503901c0c0255164680f81061940b1110110380580160094501c40042c030340c800d440079030503294000041c901b140d00f07001c02180200707104142d90040c250742e05041100b480481c3c409a968184079402072095510b80c0000401c002d607280e0141d401203e0351074518198643ca1425100b00000600310b01c211040d02d810315420408065001030b4111100044000900a00300d0051600600a440130f0140381d903503030b10014071303c04980324940000303d000c641400001d04c0380007046008400103001508084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 47714374 1250 47713124 47713129
    0x21030a060509071106060105040302010f08060105130f030b01052209051207080910090821070204050103080d0e0d0f230c07030203010e0f030a1101140f070e0d150c020309 75
    0x14090301c1e00f80218000783c15a9501c80020409aa445070302841d01600b418a10b60011f841c404085600d1006c0c04903010003d4a00e92240003941c11400b96000c0050420340d86901c080c400f10002d00054036209206000424541008a90f0078031241183c0b000c400030030501c41c4c42c2002003c5801c0300319654000c05144051410f5140d01500401e0f000e81042c42d5260226020442100003052510b401d02c000c40408004820300030034080740304141c40d0310501c017030030500101e5640303480741e018001d500507c0c000c00030043c0400c16025094042c07041200f044200c5c104809136940d449104106000141e14200b10350980388900c80909030140641070b400b40c01200c9202003e05078008000681c60759000245c00c109514003401451002165400501000c1030703401c2604c2d85034801c00c01c000080c0300d050744448a07041c41c02d51003540084052403904589044c10b840e007120742d503010341708000000d8140c2141800351410f0300340390001c5940519070300070140b10584840060412a43e001042d404203002454854 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 47715624 1250 47714374 47714389
    0x6030405030d151401020708060c0a020a02031204030506070825020a020d0b100f03082d0307030209120c011e110a0c06030e030c0a23030706050a0b010221030a0605 72
    0x1122241a400009030070300c0d00c42e581c088852504c00b4115880600100300700710b00031907403079000f003c002002a41d503203c0d1032050749010325105000b50507114070001c0e004a0900c4001800c26a0300c00c02c01d9800d0394030350f071404a42c6000251020b0025011010582410006204652280c84581d0040c0ca10428068002442100741c20300d05075142d440d0081008038003901c00c9035003805040c5109411402d00e0464895100341d000392002e0f132315007040703010348010391041c101c855a00e800c1d40d000c0d0082e03607490300b040001c001c2d4202c0714001e0700460290b04c99800d90b03840810440f0328100181e41d07a9240301380540d1510041e242080c914808d121382c41c50300e054411801d2003080819801a0f0000358100c1c07410750010202c610114140a81d0b4005000c1d000d4101404580030a1080d0040e4101d58140c0d20141503a0100401c180d19008620001410508000d42c0360421842642082001c0240300784850059840d5800e902036014141601400d00303400100100c040d40c0c101c0104c48002035829100d50125240303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 47716874 1250 47715624 47715641
    0x70b19120e15010503010911040e07050a0303090503010c0309050d1202040902070c0815010608011503110406020d030c02010b010203090d1401020c0a0c090c0806010c0303150f0f050a060c0206030405030d 89
    0x764210b00c800910307400340580c4442c010182a002080500031545408003d01583e8040758421901c0d081103c000010421140025140051442100c01d80d203180c0039114038003611409029500700f61091030064024483c0c0d5100390341041c0075001038862248101d41e14030314501b500c00c100c1d03400e210105140c1064805025424850400c83e0145810228110324000584410882812020005111041d48806040d045441132501c0b08001100440c083e0040c2c400346a04a10340d65010500044550b80001c2121000b4500d840401c0400c252074000c909030fa103040b440d90301507402000404050300340000c81e100c03010300482205500303040307124540342640d1140300000701c1980141412414803150240740c600600840d40304100641a80300d0140a140005080e10b0501c05403803180424180203030018200c0c01600c610b0381c8403e1752540045050f118072070182c904025008031380816113082062140054a1007621154102c10242e400c014095000034000c85e031350300090080303003008005801090b50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 47718124 1250 47716874 47716901
    0x30a06110406140304080a050706020f03040c030b0708010807060c03050c070602070e010801020405010806040f0b03070602030a17010803090d03120c09030b060306160e04060f090608010e070b1912 86
    0x9841d40b5040307005205070810365005400c00c03c01c0060000041480302203032907248a5007006074480309182010340082c010043c1c003460110b4000304000401100c402d5107400c0d130303120300f03006001500e5041080322424424003d0100962100000340700040c086c891a124452007032910510703280711580800e08090841d0b021a0142e481b140041c450500d4182405015020030310003182068a40b00000341081d01c06043d8a000c0c175514a41c698203035401d60000e040b107a07006401c03140c065a07590f40c02540c07075000c1452900022440b4000e03400681107e45002d0407140290f004505000c005020080c603d100d9107411401e0106402d050a0f000c50305000d0b075542d41465482c1c40d2001440c41c24680c042c0340b001803106120342c01c600200480f03c81554220a20048a4944900c9a45141010800408454002101e159102d1100041055484d003142003036603c441300034440a602c1c203401559402181c01060450138040c06000080c0e601030080c0404000030340f52808940030301d02e460f8411200040741044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 47719374 1250 47718124 47718127
    0x501031805070308120106051608130806040c03030e0d030938070c1a0a030506040612060905010c03060b0307110c04091103010506060a210212090a030207050f0a0303030209030a0611 80
    0x101d5184100212500421700350825274a86444030385401c00c91341c0303240c600400740301021541003030108005003e04040d2007100115159411b05050070241481c0c03502c821000111184a0641241041c40c101c0c1043d5038143c603170076903031424006403940181d1600c1c40c10702d06001070319540d643d0300300104011a600601126084d41d03040c0508204800700e0694010320301c580800540ae00c00400f0410403504006240d19000170181c41d114001409040690701c42203520400e941c031176050001c603a103c0c201d4144034000804c0b18402d00c82c4240c040c0c42151040c3c010300700c07003440014609401909440044610101901c7c503c50180c000101150122a410345600901e0718130b404503820248a065041101151820300708241c10b00010071500f1050b500003400c0c0c3c035180414418130003580565900158003608010740b49840440c0a64805800c54203a00500ca070800000d00350034060107503860302d800540410202411034400b58060b40c0f050805680510448060760301003402e038840d0090101b00400d449 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 47720624 1250 47719374 47719387
    0x605060607120f0e03070e060123040603060e130203030a05030403030906060308041805060303030a090f050a110a09060806040305160b042009060a09180c090b0a08010b0a0501031805070308 83
    0x13054552030505041c003981c40b102c41801012a4107100b180d000c0024038011100c035140240d61156141c40c0700028a2000002c43c02140064054104200f070710741c8075240c410295200a03581d040c2c3c48800c40043c0d00354000700701d94120588140001d541c01400b07418081050b002d5662141d0407200c40d075005031101038000c102070000e5001e46287e000c0340500700d0000e1182c3e007000303c0000d49034400644420315440c0d0305c801000070024448e05501322550084107903242000c6c5030410070401108401894071544007000b020903000860b00c540310a441100004001640d030300c1e9402c1d0703071a40c045860612182c1040344042c0000c0c803440c60081c8114171440b2902808001e0a84404198100034040392096418500b000303040d40350740030320408450a5200c0441d45500d01100d01240d03403214080540307004445500407170030340e000d03030801200d4900c2036410390800b07545c81c5242800c07245007504903540607443c044100702075842034021000440c0e140390807411402490752918a8000300e13520489483c140030811 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 47721874 1250 47720624 47720627
    0xb0d051c030e010506090601081e010e01090b030303010b09210a060b01020c030a0213022803020a0815010c060c031e0509061f0608101d15011b0605060607120f 70
    0x2482e00070b00c2d00c072000f032040b81130940000e48040c070000c05450410541e003000603296541d0950101002c0c061414a44840d42c64900c0d049001c5824002e01ca540d500b00a030081003801d0010480341201c02e480040c5041035810b42c01c03c1181910300c98980e2119009008401804c0b406001c1c008079148074402c0052206038200001e400c09460442c582e1103904418101e201503201d864225110448801005135690b40d181000c1e40f2204003100c00c1c500e495a98019485101d405a00034402081c0da51904002036441003144880c3c1c001c4107840500040c9216200d900164560300b10103100c2c6010f05000c1140309203c0d014106045a912030b01c4102d54a0700e052216802e42803244641100c40320b40d01039001d101c450000f80f039880342841100c00300240e0f48005811a01c1100400000c0d0001d00c0c5c001031007110414442040c580e09640c0c6804c40821101c142c0b01c250b01501e2106400000091000a07002c0286c4a2100400d0300901b41c5810900400603000090203135002032020141c1c54450b00303c1402507100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 47723124 1250 47721874 47721881
    0xc0302041a0f03030c10020f0c07060c03030509030a05070201030207110301050c1309180f030903080d020703080a060302010915020c12010c09060c0b060405060d02091005031605060304060b0d051c03 87
    0x42c403a02a030420010025400b50200d40c0402d100c140070710159403142518041002c0d442803c2001c2418004c40c4030114029512001505070b40d806660180565194030b03c01c15100c2c0b1424441c200850760802070100154025005004100e00031320040d02042c210a000c2401c6d2103040354a41e01607903002400104400c429480d5501918441108000c80f020728002d50007401401c0002410002002100d40200340c4134000d000003442d4009032a60b21800b004014401030b4011010490110324580700041d96003000d0300c64074040320340503914940c50618008084000c1c440c0740c078603c011401490451195502d440c01d0082a41913200000100d0f07240c50758005045281e075800540030000f00d1241b180115000ac0e1400d5040b06084074001210f0300d40070005511802610030094101c20154100f064114280005404440b0300350140c900340420b10f800b90041e5803160164552012060010031b0100d2102c0d0b01a004890000e800c02400990989500b1b14150f818602554002404026901c1e416814003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 47724374 1250 47723124 47723149
    0xd0510020c0d0c0b04020d0206070614100816031202120c0a020306070f12020901200606030c0d08040e0a06180b1005030402030a0f02040b06070318080610120c0302041a 74
    0x58100b10b6500f844d03071401d1391303036401a00103445221180c82e0041556031b65021181d145501980030490070035880b80700d482108048a10380c00508074031100040b005804100c151007100c4142c49000500d05654070018144140c81c0e1540852003940c0c00b0007c6421048020210458104001d04091240e48109890014001d0043e000c02055094150359590408440048054243e0000da2207600b8a4012510010403898007107240c00f601008480066005c1801402212305038103859208070040c1c24840030151802d0018a5031404000130040351240100040c2c101202f180d000c10599501e0010300ca00d4442c507141903a020b652600426001e1808082d002001c1b501070414604614158000070b88545900801034070b02c1c110384090380d0855507180d20080154100a1550f601d400b641c0c14014241d20284080c40324141aa03280030490030400200742c3e2041071071001030050f181c20080e42c2c4a001c42501821103070300340007242c0440181e480d400307001d40309084081394000c00314040e010400d00f8007080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 47725624 1250 47724374 47724377
    0x50403020907170112030215070e040e0105270c0306011d0105010906051b01060504051003050705120601031707080301031109060d030509061308010903030b0907030515010804020d0510020c0d 84
    0xc200301c0105011609503e0b0465900d08280c61100209040507810314a102c0e61500d03085582d00100907589400050700600c9a80075502003040c00008100349007210300036140e48084c11100e401014a80d840100f47c054020b081c0d800780c4440507049070100f0719100c0c00780c2040c5100184241803c254411900c2e1003030050409103800090540b07452406451803244011100710309008400d50301005609403c010020a40600200001e1034980d40d00800d050090004131114041c180780001d0900d0402c0682540c00c4000000c1e211030b9207503a4546205103103503144180d01c48410301442e4041500c050241d4005d40c0141c00340b808040318034040164800000349518410b00035140f0300b030046a8041c060300c96110301a0340d501d5860a40c0380d0f0010420078a503000582c5503003030144030f004055064002841182d42507072180001d4545034019800d4440841301c0780b000441c050a0200d00d0362240700507580003800504003a414800580350a82000311000703600550f280c001030b42048403081003200480b603140d076 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 47726874 1250 47725624 47725637
    0x210050712050711070b040501030c05040b09040203190203040b010302150c120c010f0e010b091308070201030b04020708030901091202030406051209010605090702010c03050604020c030a121b050403020907 90
    0x803200a844200e80411480900e40d94100103814240140300d50310090402201720390340e10341c0e50440211554014000c20380000e0804e420103413110f01420964042d03a48203001c0a08240400041c40000e4000078804c03499280b0740c4100d40104842c43c80214015806000f51058170741c114014403110b0f40300d00c102d01c2454501045002c15404000c1501a1484c610304102980e425800c04e1850142200400710700c40c0919041c5001e4000710150b000150380c80d0142c0307000711240c6d9524100b94901c0b45101000d03109070401c005090040d80b0960042d071201400410050401c84261981900c5820442e1000c14903959084ca00040c001411040c03440000f143c4029480c0504081e40103203c1d01510505505440e0481c0104117130b42429008070001c0e05001c1e00e0f481640c40c20301c40080c081c040501016011a251801080e03403810a402240c1540303400c1c1000714a461a40350045070b80c1102c072240c141d01d003541e480d5a40982c0d2095444941d540138941d4485842c2c500754010080413484c05002501440351 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 47728124 1250 47726874 47726881
    0x3020408010b1c030806010207180f0b01050a050414040204090501080a0605011e0302091009090b10060905010905010804111509030105150a03030f02100c111b0a05060c0f0601060807021005 83
    0x951420f0a41643e043c40d080300503844010041c1c2c9445140d4006000700103565a0000500c4050780c40303916109051902406681c4000b401950705124001603040000e008000a202d070b26400a9a101d00c1400607000526055550040e0411240281c00028140d000140054180f18560152034054206001c0340008080c0c591015030b407030070040c030000340a00002c20000e00f0144c102c019110040107100380501001c4140d180907140c0302c404841101030400429404030741107108007820b206546c4e068440c00110703410072006440d40600103008450b40701094418070300030386642c168818480400c0005d0b58941203002c0406003583c0c001015496105140c44800500f0760312051402e040380c0c0c050401c58405080f0300000c0b81884200d1401c5030886044c00c600b00e8141354400e191480e650b5100e415074a8132140c0c3c0c020a517103901c01544055000c0d80c54a002d0141e071621344018a806030501e411103116240071022941404026844100490310039403c00114680510180a030740d0b40c0510304000614 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 47729374 1250 47728124 47728159
    0x405090601030510140301020706020d02040501080114030a0308091615170f040b070203271201051504050709050a0e0103020f1903060f0212161e0912050a1203020408010b 75
    0x4e0310400c411500d81010907500b588082d4100c1d2900398005605541c0ca070000a0500040d5111b8030445001540c0c4500000b01c00750504025204000010040c0201c0b01c255142103402e40c0014154059a000b010407003207031200b9240c1002c1c010301c0303001400c05005072404009000342e5608140c2e00c0c0c505c4070400800c6107160b09000e0040c0c0c0194003c8401d83c2e0380e280e5074400c82c503501403400502d0303900c0c144a01d001000c414252098048080c2203030414900c0815400080c03e841058035222641007042040030560324040d003007164030000d145000148503130707100c0001740c1c00281170b030126003150b0010313005100f5070400e02400b81d40410247c071a20506d4002c001300200c180303564407000d000305a90f170f001c0c404500030301c0d0115440c1e10515140c403011350405203071680300d05003e1080c40d8040351b000082c0050072410f1101c0351902c41116282d51800903e400800b4042510403042100c01e802500365510010328000c40f07280300c44c940760b0b038010784031401c15a0203821900d1282140d071144201c000e6a00900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 47730624 1250 47729374 47729401
    0x1060810080a020d05070308030903190c02130c1206090209040606020d090b0a030b0d030806090f27030705010e0d03150e0105010309050f012301050904080702092a04050906010305 79
    0x164140d0300ca18a9107405e060050400420740c100800ca82e0001060281070040040980f4100e40745103001c03807450703003003030001d8600300c117aa84001d4001d1505078425a545c5184da00c021310b240010300308803401558034068441181c80ca900600da02a0380850b40a01a082911482c00074004500040c0303e4496103200280101a09120311103000400181901446200390850000c038100641181449021443e0180440f0821910b04d4010441034000032031135203442e02c0d501e0290100208001189040c43d601c001d070b420709800395031600d200030007880c1c1c001b4031709205414000025102a0034140e40403503005065031113152800311110203907801031185002251305141160000d0800145004880c81d10310700344020340c2d0700d4070342951030100344038400f400c642101d0210440c20040458517a80f50b50400c1198041614080c0c0b080009120310401420f00c0300e00190000c0142100002041d04a10503003800b402c0243c1c00e1410070000b1508101d01c1c1031889959130055000d007018032a6240c41820b02c0d02a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 47731874 1250 47730624 47730643
    0x1f0b120c03130606030b010602060601080c1603020a14010617030403050d0305041109011503060914010308031801061e14010804030509060c0105130b0c0a08040201030c09050603040b0106081008 85
    0x80d00c8000301040c0e00707801100000501991104060281a5583c1005501c1601c24070a96016004c0c610001b100d5601c210f00300f034403ca5000329014100301c58000d0b040e600307000c000d408406500c600c070440004a00146c0d180c01850581d00c00100b000d038209002800c01240480e02e21b045648140410710000f1000320b1a11094900c1e40f0300081c0726034640c205a0242c150302d8041c40e81060280d4008680a440d507150403c800c0300f5520180700107907854001d00c0441d407915030141281c02d0440e00500024581340300460f00808103001c0030144188024046085442e160301c8014034002411801c070f159400c10103441300a08518507440d940c94411000680340403c000c200800700036000840b0189070b512202920002c00504000300007500d01480b0340300c00c8580705001690f5860080000484503a0041b084800040e8a543c40b0701035915590300640c05840c2ca10203000a100031000007103115294103000c0c1d40710354005d080c0e40c04594035000001c0c102ca07101500411000440400920550300000b40d42d200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 47733124 1250 47731874 47731891
    0x803070c03050f0d050115090e061311031905060604150f2618060402030d050304050a020d030302070b01052b05010632060a0801050918061f0b12 64
    0x55050461a08507124810105805200f84020414001d81e41c00c03540001e05840c4034096030101c4c2c103a614801d40c7d03600703450301c1440307040704440000501c18107110000f9200c00620f0303000407888034072061410209800803600d420400d0382c400d4145503a018940590350b00320340151102482d00f0308200c884010103610301c11807014050604a1091283d101e0466204c40e00c02c44007a1134031001540081c201180c0c41030b500c0303221191418050110300708001c41e0207030066034014010807070540350b65002d40f0710350001401034070070b80030f00700c52540541c80c0c003405000014401d0b40d00607902d88061803c00c1c0740c00c2c0306030070090140510205075041c40c064412181681300c81c40c626030240001030b00e081d90240c0350350340050031004200707140c07002442020000300c01031041024091203029045010700902d0b01450a0003000200804010091400d1520181c1d400c007038064660b1079030741b807032400b1146810020741d008071030341850a1202d4180d02a50012001620002800c145015583e218014880394058400704 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 47734374 1250 47733124 47733137
    0x1809061b090906010e04050a150e0f011502010621020108100602070b0706020702120c0112020c0d0c060207022d09040803040605070c0b0906070f0e0d12090b030109090606060c080307 80
    0x1800c0d40e005da0144000d250300100280002d00d8440313a0a4080c1c0000c0c0144074594a29503c040340540c1daa203102d910403941020016900da1a00b4403181d40c100d00750300c803442595030780c000c00306411107a0300ca8909076841e08000d80048040900c0010422034004100c0343e6510503c18092045a601140740811501441c01d41a1210218185a0000c1c4030301d050080d4400300b0f00500001e01180480e086040007000d803202984461640e404805070b105010294155820118111945034000ca084009940c0505030050500b6219030102d98007811040303009000c4030908404044c0c5400b40211111048001c7d40e90711154101596211030030b000142c001040642c03601c1c0010780c6540301e02e0b41d039440950800071003245800c11201d12900e03950141d400c00c0004031600c40114546000d11900d6103c600084d0044940100d40e40350501c0c203000c15034440081180f501c0e000a1245001d5000d140a00419000010300007514030b044070881d5402d90201040c000707685000300101c2e00500c2900d0f4800c001e4240795 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 47735624 1250 47734374 47734381
    0x30309063002030a15030c05151813020403051504020a0501050c060c18100302121302030d0c0503040510030e0105010909020a0e0601090b1b151303050d02091809061b0909 75
    0x61000c5c102d409040740b040f4007a40000010701000b402d40340120780056441c49542c2e0b00107154400540b248140ca0b1078450085c2102108606001c1903000c0e2498622038018206522560741a040541c602038412020380c852090009615110842c04018082403c00f1850a040c040300c090b21143e0040545130000c3d13012440d0f00004401c0d8003a80110b4000400840c01c3c901d0600c400780c029008092810000907a8070001800700c40484891a1442d400900400d80300100000842c0c2e000505002118140001d03c8000340c55101c8145014000d41251800b0880060045d038090843d1416401605814201202c5501503110310a20400391051221090140e50350a8010b03942c01100c1e5011702c012010001341000140044241202403039008425203500c4180020343d04030401e8151100c40d204815119440c000a000394020140740390100009801c01e203031240012010050440351211921900d000c00c1180b90701800082c1d4010019181c2001d21108240c59100394024822414019030036079010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 47736874 1250 47735624 47735641
    0x6030108150a05070f0e03010b030304060206010e0a0603020604090b010e030d020703140303060a03020d0302030c07030c0312090810090c050d0308090d05030c1204030c020d06061a07050d0309020a090603030906300203 95
    0x40744041005402c42c4ccd550340e981c540081d41d40c0c8003440743ea1702445144003c5100d04e0650700840c4203ea800a049500341401d0540d890000c1410300c804905109801e041404a602c050003101c0740440950058090103145041419004040144180c00c80d081002000760380e654090900068a8043d207901c1c040300d910380b170180d1842c800d80d882d41d2954400ca0343e001040110b036075108810750f0b22801940f003000003941819980006c5034040d210345c0382c028006540c08000207511a80404e8080d04001001c1030b600c03004206614513a000540018524a0400c00000010407003003c401d401440c00300d2035440e100c1ca86080c2402a4585811059640c00c04101454800c600c0b080c605600242803809001ca10301d0500000c016070703c0354611100d0440c08010031031026006540080b90004007030200c1842c000c4084000f401c600e14103d9104880040224031000c0600c81c01c0003452098858180250400b80064003c110881168a00c00c60000c054200c04004628a606c802c401c0d00300540c076526510103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 47738124 1250 47736874 47736881
    0xd0f05030c0609160b130e06151b071a03070f0311031302011103040f090207031e270302101409041806140103020607030e01030b06030108150a05070f0e0301 69
    0xe103a0792030320442040c852800c0003c40d4568426100403021000782da55110307010940c4c000c07a240207941014000d01040800b03080040c09610120013001c0010030056141a5047c0740c05c10b48040100c5004909040d030300d03070300400807030020740402d4040c08508001c0340c0c200c0b503032880018049010070007800404c0072240d001e0f41000200b004c001034420780381e1403c140c0e804512104008142d000840036028240d60a1000c42210280c401203a02c1030b10150818034a48080d61000b20220204007080c404101f1500e80041e5820b000d60b2240e07500000e040d044000d564020304803400c0000f10043d211400c0005a5030f0404000c501c003008c0c2400c4581c12030b59144001c49015031848a50403506203200d0451501d03005209000b4a4030400b0108440b4a03075000c02d25031a0000d00000390004010420702001c240661341000100e80140350114240c5100342c0810f46d0764000b0b911525081e40312049813004460b19200c02a4402807241c4204420700e04550000c0008186400e000140802460a40380d261020740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 47739374 1250 47738124 47738137
    0x2092404120807030315060912081e040e0604110714070b0409090501050108030a050f13030609060504060c080c0901030905190c0501180806060609040216030203180406050d0f0503 79
    0x40c00c07031a10101401d014880d035024400840002c1e14154142c1a1000005441e405450150380e4a20b842820840803000e00d00c0d01c54420b440c076500a00000c0e035080c809541001ca2514003809158940d8540300d1041c59442000d080349218500b4040c0d070702091010701043e9a103041e0041c01d07555980e940550b545051914641260030950b000080218805620b85c0024124034800c0c0000c000136130341c42043c6c90f102d002c2d40415800040e01042382c8680741000801a100e02990b04c0c4100300301315901e544901c200c41404000311003507070319107041105204040c85204c8006000d403c000c00145001c421004c01e0340300e16800036040c180d40b01c4509092120410919442c2c1c1e0b83d4140119a042541c1441c81e140c804502c6400d0009a610507468038106485813030700122099480203218940b01d0030b00b0405c054000b210f555030095400e021500c400e041409460384203074040d4024503902d070b00d10080207500181180001d80220f0800390708000075100c20081c5140e80e80c014000c2c40070f030055850550b08511608 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 47740624 1250 47739374 47739389
    0xd060b12011416020708030307050705030c0319030605010c02090f090f0a0b010302040b0613060503060112090606060e0414040b04060e030307021b0d0305030a0e030d1109040b0402092404 82
    0x10700c02c0e15004214994441c0a2141c807480c0d4000c0c189240003c9949001c0c41c0905180741e001400884c507154042c0000d01099881542a0707410208003207115840d41d04400313501007803007038400032545c1c9080c1c040c810203015190a103000880b05d01550007140c024a40a4010b052207603000000030324615091006c0003100000703800fa6405400742c1c0c105194a035400307010907845549040c1013812030b031500c08115664410300006c80d960700ca02e8108281c0e0709410003070119051104000d50105111fa462140e031241c0c52203250005002070030300100610710b241204505000d01c2c608a148041d08135212070142d4090b9215485103015601c2c2c0c50440050705000c10b46180520010061025071900880c1d4050702d8100451042c0b0a100e000c0c040100d4a084240094041101040030030702500c40303500042803070806c40c412a45003d13039043c000c1040300c0c82d2902c5d01e400c03140301180056180c038141c0035603850540101c43c154200007403030001545010040d505014107411842a107200c08901105807002017000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 47741874 1250 47740624 47740631
    0x20c0322080304060c0c1502060a050403180303080f070306080a060203040501021e0a02010f050c04060804051f0e060a061a071a0406090302010e070e01050d031709071a07020d060b1201 81
    0x486201402000705480c0441e8045010321b0040b500b5265901910135042490340181641c5e220010400f0080802610580802140741300010b1015010313450480114440e82c2d41c0d450503e010207100f90344410140c00f210403d41401c00c2007080c807000040d107441040e041000160b44e1389403443d041d030080c40b6020b815010000c0c01c081e42108103d1703140c082e1009200f1500207204052101e8403140499508460b48001c0070020700040c40018800c098059101d03125200b01c410b1460307461270082200e662034404034042c0303807100b50703460007601e090140c10b4000308424810301041c0c2c2800844100d01c442a04039410020000ca800400e2102003032103508000c1180010f025070341403900f800000b82c040c100065001d50300b0702c11b13042583d9000043e02002c88034468a04001642030004108060700308000590070031011161744501c95001c40f003914007440c0d9080c01010344518010350a0460003078400780c129410780c00c0c030403032000d85c550300c1d550011503070f106100050070401b44002a4032100009180d110f258039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 47743124 1250 47741874 47741879
    0x506071119060e0f03040522020d0906020a1b150b010516050a1a1302010302031504060e01030506090d020d050702130e010b190b040b0706091703010302090a020c0322080304 76
    0x2800e0f844502d4110841007a624514030b00504283d07a40319503c11560084501503440003100d5012104564034022914013502c1c4c0b0703e45104510641d0f0324054143d0740d043e8000355200e02550040505880b9a041d84190b841e410f1180d1203602e240c2d001c03400603d84003a02c45800140076807180c002c540099001110b010000d080c0c0342401d50340d40c06a05400c0341c01d0304da9050720480000303206199a10404610822810f10f149590044020b508050405400110f0103d0400c10907650360058001801051449003030344d602d1800c2c0301b0320789603000e4055002500314800c0410380c1a0f011a000426090038200107035621001d1000c50b8440117048011700d100e515094070001d582106401c58013071084c0031a4500c00540382c1213800c0f01001ea0601c40c0441100d0104000c101620300c0e0005881d000d8098940001c409a640c0c0741c40031041c1045404840d0301400000600c02c514100f940d8542203502008114200b4458007650307a42c920400c000240c5400305035800c003d040001a440001604403d815240c0300c65 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 47744374 1250 47743124 47743133
    0x9060902031f181e0213090f060b0402030702100c12021215040c1b02060417030301030506150a18060312091404020a0c0b1f150f020a0506071119 64
    0x6007040300c02820981400c101640c000c0c1207001c2543c165410001e0704810100341e4000190800392104102c0e0002002600003010480c188502c260207401884403500207078281c94401e0454034a1210540300394414400c4c002c00300d03030000ea1003da51524220008000030310140942d1031011803200c11880c0307400000c52161400d800384549015018100c603141c8032441d01402c000c2658050f580180005000030011407807910510305c0d0044040c00500307401d00c3c0c5501c485001110801600e40090745900c00001003003007210403c0520740c00180b40c6082113a07035054030005510b00e80c06206a480b80c800702032401401e10001d601800085a01044031480072681e07034800b800d902840d200d03031102444400d6404c980b0341414002ca440c40d095581c0d550140344519a900d185460001d0400c0490140c0b882155040b024084481400740c000b4101001c0040b4440000070451640740c1003440441d08400a9107002500c0002e18542140881c00e00c03620040342107403007519200990501450130601000c2c18028070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 47745624 1250 47744374 47744413
    0xc2a020423070906080c0a030e16050108070c020a03030e060910030b2706060a02030f0a03050612240a0e0109080702150a1d010309080304060b03010f09050c040906090203 75
    0x2144140010110b0b95560000f50346650f0140715590100307440700001200c84600744024010744a403410002011042e41444500c0c109150900000d070205044048c0601d40c2c0010660390300880514012a00010075070100300c01d0700c001d01c002810700810348105c51b0716a84200964900c0d50020704020947c02c29800b0060203407130f030000700a000385286503804502c2d031151032640c02d50101510b041c2071a521090248002588808905021030109000c3d0752407145030301c001004502e01550f00810f15080c01e0040041c81c00da60038010350a944810f582c044421480c1c0c1d0b6041181120010159187d60307850070382d00203040c072040c40f10040d503e030052038400c1060805c050030003103000345e0701071442d641156840080c501c10b0308800c002003054050351152203c045880114512010714000c00d0003882580d8402007508162411100d180c0ca0707109510103802e09200701a0138140f00d10040c0320f80c2e119511450b882d0010000c006000320780750303a0741405004094002e1901140d0203001c0341c420341c4400400d811130 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 47746874 1250 47745624 47745671
    0x60315120c0105031302060403050d030f0c050405010c060902060405030a05100b0a06080c0702012d14030105060f030604020415020a0312051e090705040c0302040611010c2a0204 78
    0x14a121010361510280009071640071000181c41c0c051664950182c0102980d41318542213a001ca403c0101100055041c0300201034a80b9036100400d1a40c0340c040a40b0551304d00540c000b0400a080c04200b0003607074004c2c020121150043ca0021b43c5103594008140b243c4690740089405101c1c02d02000c0402c000014594280c0701004800c02c00c8400807010071407003802503c14500007610140208280540504c02006000d10505100c0b000c28904892802c129030034421100704402c000c04e008280325044051140c0109002e00300501d550705000004102e0700410040a50440d00800040c0c495100c0f41d044602074903804001c101c102c007015400955030550020203c00180c1d03441c09075280d80d190350254078050403410502e0b80003c550403000c0c10089100900ca0101d61190503400a402c0d1198840e42840d24110745c0c0241e40d40c0d0500801030204814140a200301d130f80b40200440745c041e030101c00041d4081842c90300588100504143c00d4030310800481c040e40c01403030b0406aa0036004c080303407503612 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 47748124 1250 47746874 47746879
    0xa0b0d0618060b04060e0613090b0708060102190302030d0c09031a01170708060112020102100606050a02071706060d020310110702040c030e06070522080a14120414040605060315 78
    0x43d0441c407400d00040c0c0d9090f11030300d4000341501c0c1c0400d1461614010310751041404d40d00015040b5000d454001030340005030345030b102007180b0000780011568180001c882204200803455034100c0c88ad0340081d600e1103180c2500c45850b40e51038404d03180b14440c04c07145006540184803800d0311002d04018005240082c450402d02200f07000c0f2400c51b83c0380101c1c0e00c50864141c0c502905580e03207850a03546103480d1010303040741140280b1080081d02100c621444000d00740c83d945590726180d1100c00607250a16503041000a4046520a83d0882c0000036842e81d105c181680d8008282100e480440c1c07500d99164410442541417080b001c110a00324000f134100c40e030003200c05202c040d9482400b982225000c1c1003000c526004000090700450003040280052502100303502c240302500c60001115900e1070708070b20070940000d42c201c000e1003180384403842a8031203080500340103403101340b59080c0c0388110f108411200c000c3c600d021540e0342c1d441e4002c10040002903d2668cda243c04052036041004821280c0d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 47749374 1250 47748124 47748131
    0x90a020a0305010609050912091507020415060201050601031802060d09080d0b01020c09070206040b09070506041d01050108130b100f170d030203010b040e040c080307030518090402090a0b0d061806 86
    0x6047c1c04001840b07101e080000c8081c030f03103000c000c0ca05010000304019031410718910f007006a01c0068803144034111000d044005401451418a040282540e5000d40380504060820040083d02c0340c200f002c00e5008d0b03504442d002da1310304201480302d0140011312405840020003007500c58507400c4a410540c03032004c00340d00392084544c2100400101030410354a42e0b0044c2d11000003d400241e42c010030395000180c01040b02c0009649800159555000e5002005c0c071403d12440d2003500c0f402d081cac0700c5c0c1c094002420030044600e0300440e080e100801e61a8040c007620320180c045482c604998003401d0150200a204c051010b031500c0d41c490506502c5c000c00740322071040f120460030640c402d1080c0d80c1a00c0b030682940c0d141c9031070f144181204603000f80c02a520f04201c03040000391a10304100802e00d0600c43e45480d41c95401d003402d056040b090f00c40e1030034003e40f00e035810040165246420140d000d0010600000d88030206c0c1d0104441f0407410000820661400c0c4040b1032020183c0544c1c8403852103850b090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 47750624 1250 47749374 47749381
    0xc0609060201110a03020307020a0c1e051203030705070f0204180302060a06060906120204050a030b040c06020609280f03050c0f03210603032104021008100e090a020a030501060905 79
    0x403403c881c41e1811111014405010641c1514443e400564006805104499109000d62a8014603075426840b02d20743c5c040001ca40181151000e44820041400b21000340c400041031a0309a01c2c3d100040c011000c20000046560030000306504990340c07030f03801501c20040e40b01811440a50f41858050540c054811040029084111401154203440d803d0307031140812440c0036000e072201d164000b2040c0701d1540174080403e15071512003140c0015409019082401e040a0901001024241e0450000c54001004100381002e0000e4426038030421042074130311400c21250750b500d111109500c014001d8840c031100b103041c07680c440d0142c05400000380a035012525015041650780c0b141031400310120700d4a030448040180d41e001401d622020250550b032800c0a10940d014540034101c2200004d0300e40700051000394240303c54116004d009500f802600ca0502042c50b0060181c1407180809030316074040014003000081c00b40c40c01e0240d0250008040c00e4a9240450281c402ca0081070b81302c0e403500b07000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 47751874 1250 47750624 47750627
    0x1707031205070e1003060e090a11010f080c0d0b040903120c030e0c060304080c0601031b0b0304230f12030a0509070b0406030c020c12033a0504110301090c060906 71
    0x10140500c0711a00c0f502500c1c1000020710440c008415132101c28550740ba0f1000aa060701000414403501000020f444600c0c840c1c54100d4502ca111075015042141d04a071803050310b9040783c0b21981110200c0c0380140c44042158100c2c000d40081c41d14250803d08103404d80702015040320024480329070a88043c451010060801c500316a401d00c00c1c094154017182d000c1d404c600b001001181c002e4018815070307260113008c90b01e0924041c001c1e4030440740c810b60310a14054514500030f42c07801401d903080c80c551550506840c1d04400300402080b100c1500c40c4401d071808285010800d050186800200b9180e484038186a40040e90b001102c2200500c1d04000000781040c1c404648072003501d58110784103090500b014003c9004005104520041d4400d0700d803400c00e140c3d2407003980381003281e100005680e10104000c40e103507100ca110729000108102d04880c19015014803c10000d4030318150800107160380c850800d400c1406070f0035038443e01540703454035070b01c03d01a03074890800540e070007a140d903d03025580b000f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 47753124 1250 47751874 47751881
    0x60201090b1b0901080402060912070314060708150f0907090503070503010207030f050d0603080310060215070f0c0c12050106030b0f0601050a0c0302030910020c03070906050901060c030c17070312 86
    0x5000c44444410400f8a00c50342c05140007607000343c00a0306035406c0c100a0408102c1c0000c541d04080501d034841d1404104000e02d424520000c1d400502c0900b50504003150080d10f51040070700440282c1110021001e40b5490b400034021902c6002001030700142810342000d0450003d0f0b0240c0d6000f40540c0c075000c10141014000c851403594141d440e2014100070707000c100c8a40d044080da1851007510780d42c0000110700300301d0155000380c00030055810180d140280103850855040c54090140305200108030016402a1141142c45084c1c00c111f100076480f032030503054070300c0b95401c500a5140c2e0096100113102c1d0540c0220f0070b803807050b00e07202c551f03880f103581c03000003894101c481a00240d010040685510311401112028902c02e0040b01d01b809841ea000803c600c54101d51440140d00c8007610303507040d00d010420309005100d02a01040001e0414000c038412050500030203052100ea33008000400d8411107006051542048501035014100c0b142c2034101c2d481100107a0001e003205585004840f400d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 47754374 1250 47753124 47753161
    0x1b0102070807181e0c050d27031d060d1a010516060207060b09040f0203120a02030d1a0307080303041205090f04050c0f04080708070e010315020f040906060201090b 72
    0x203403040c440f1440b2840805440381040b5504540c3c504003c0401d000b41c140142e00d500c081035220745484950510510080316650902c08140300e00499043c0121111711003403540035030305031a00d0132081100502160144076440032054002000154000303080b0050b601031520324601c50b5020041d01da944004489074095111407100150084154100150165006006003845807a0215601d0190b000084141904803002d0b64a140c1c4060f48408624050040760242d203103021400341000c3d03802d18007c0d0340b0f004200c0c086c82c00c03a95801025641d04ca0304005120040001000c8904082d00c0302441d80e03ca41003074504a8003030305643c6414038402d00070401c0d2281240041c101e102c00308111810480a42005403000c900120104100c50101012600410192404030020050645003001c11031904450340c0c01200c1c03036120b9800510003e40381c0112603a00300048000541c0352002c0180d03070407180c45580c2c0f04048440c54200006512a019001408414000d0800324250354403105081201c00400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 47755624 1250 47754374 47754389
    0x30605010206180a0204020a050d0b0108070c0204020912060103140d140a0c0c0e0c04030b0604020a0807140412060c0809010911010302070807050303090a12020a050606211b0102070807 81
    0x20b0018922001d2200c0f080f00c881414411190030710015000702e412030f071108a2250000f06c000440d0040718a4034012126800401e2070000480c1c075042c00000e0850224403002445180c0000d0b250115903503d0a205451000307100c20f4500950392450403408208154400700010b0041400341100c8500a500c40c02c0d01603072701c1d640c07030745050310f00300c81215a000c600200711408450103c0c0031038501c080c010041e2140980d250f07440e5840c1e00390708085500704c0c00246100c1c8914010010061415880100306170440400d08061107408041030201185014580002c43c00c040031840300c0d000c0c0103d54100246802c05a100e00c100c6444130103d540c207070b94038600050f00808201c13614403565407285d402880e0507030007044898103001450359014110f600646045100f940b046054009000c02004015009820382c001810b00041036075409486040c01001c0622603a0540d241d04484901400c11840301d034a80d1080c0d48008500583c030140b12014840e03202e0042c401c102d07001c118240d0010740b140559041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 47756874 1250 47755624 47755633
    0x3080403080d020c0f030c15190c110d02070509070206060a03140102071a090c0613060e01050d0903020a0309090c080c0d0608060c090f0603040f02090703060f0806060405070306050102 81
    0x441d110340ea03940e4400449006010360800c1500d00f5582c2c107103c0d00c0701e12002440034580c0c40b845180340c2c40c074004800c2210340540ca15031041c031002045040c4400c0d010b4107001d001282c4940742010030f840c5e4440c00c0c8100c0140f40200c81110001640c046841c505840045821030481d0315880400c1341e482c407040340e00c01e4020240c5c2d44113201007596aa01d8200c1d09040600141c94140c00c0c1d0b03143c414030ba0f6500d08841807440880b061000180341403103c0c01c0f00e01d10956040703040102a40190489815510603601402510340a140b1aa44550308841d55055029014000c00240e807500079540c41010340181c00090b20b507140442c02840c0d500810001240c15590000103458140c04a4240d42c0000781c81e101458ae50880069010f800b4400a4443c4111030841500e802c440c0083c07101d07241c07a4603c130710310402040081100040c090004c0903115501901d0308030995903040010703030060105402000c030324056503a001403210800204580b04038800e0354140b080303031a880400c1d421340e4414001e03e8050f800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 47758124 1250 47756874 47756879
    0xe0c0d0c1e080406110c010615030203130f0f0c030f020a0504022106120a0302070906050301360503030c0403031202070203071a12010609030302010b1e1201110d050619030804 77
    0x10402c9015040781c007034180000e821100c0d000c60003880d0710031070b11041a0b94440e10104802141802c6840020310141800e40c82d51500a12000b000c481e4207800801507507001644a0034072117017030032074951b550380134821010351740c0c40e4104a076101d00c51213400c912034001c501010a41d81842d000f52114002c41c030314556a441c168949103400c00b07500416090300078864850403c101c110030820711020301d00980280903201e04101c211400d0742c007150400c0b400f9030b040c01da80505c05c89024150180d00c102c200c1003051a45040c04002900c2441c90310050705920021061140d0300001900910440348203480f81d205481c1219128416800303203440181d07051f08088410010048150001e5480014044c4000c0c43c2c02c4a00070341c0407005500ba0000d030b00091a14805008140e02407040500c407400c1143c9840b0038500344801e90b0101010500d0060290000502f5070f150703200c007500070074590018200c240b40c4404480b1000802028110350062040c080350f0b500702100151030394200181c0c4d0300802154074003030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 47759374 1250 47758124 47758127
    0xa06050f04020d0e060f160503060d080a1b050309010306090b0306131514060a0503150109021e0c0a020a0b03010e060402030601110a12030509030a08130206040e0c0d0c1e 75
    0x100a03081c1070303890603250344c1d0f0100041300070f000366881000c881d40005c0711403c01e40c01c180340102c2c025000d41c0c20b10008009003e4a43d8a20381103c442c242e001880300d6a510b004501110302e080011444040c0500c2100108104000440603082c1d2a40a076401c01800355110b6496080d208491556074142c0c0204000c0790b10991000c043d80300c00c9014080e090400e1680100c11421580c0c240c00e800400300300d28041c840145081c0c131420008100450003003540403240070344501c2d03a14061041c102d00642c005080f42c01d0586034041c01c0200c0c1c0440c00c010740c48034000117585468000e159003ca200c0d03040700300081081a01403041e64144c1c0d50308000c0c80300303a5844d00c0504c0006d5001500365030502c600c0001500c070380c000400003807a034180314680603c00751031039101c0a802e881c8080c1071401c25070000c3c032500c28000d5000c6d0400e40e0003421a020503200c51001d0020075002e1040750003d1034511034035410030001c7e1160600400031500041000c000011a04808940e10111410503500600101e81d4910185 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 47760624 1250 47759374 47759377
    0x30f020609180406050702012901030b01091701050108070b0a090306020a09150c05010e0706020a030c020d140304080c0103090c0608061504140a092315030d0e090a06050f0402 77
    0x26400303002c0c0812507070b400d004080c04030801c440071207420b91104200180c044e0b080c003925141a244c87d2104403000c1c40344400c105040380528220b03041581d1818541640d80c480c411450040040d4441b00c520440b234111454080c120074052501e461117207540c00244608000f044070b41070441780e6610041a81180d591030040e42c080600e00040000d40b4001060040b44240b00f032200b10400d0b1260001e0320f01c945401401d5485460041146402220302000705980210703500420350351600d0700200d8174240d480001e0703003010080c001400f2031900c10556515040008014070564540324100ea01e46864903004405480c0c50000041a08814040800265010b6006203401810040c0381102041d00416012135030740182c0e0013026124ac2c0010002001c2c104000b1400c05055030080030b00c4000581e9040f80f03c5024402503018204207000000ba05a602d0b150518400c181c1c0241980c40c40250b0040040c08410842c0c3c80b0343c442c8540d0404a50846402c1c85110125640075010010400162080200a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 47761874 1250 47760624 47760637
    0x405070b0c030f04060906030b040e030306120109060f2007050c10020c090408040501030e010b0d0311030c24090c0906010f090e010902030906010e012102010e090f0a0510030f0206 79
    0x9840b0520200241200d9040030300044c0280350303540c201c500d2500400400307a80380401424011846d040c02049000808001c503940b0103403d4070148043d03801c21580b01d005000c1d1880c081d0004d46000868084524160480c0f4200c3c0c00078401d0503070055800643c100c086c03103025030081081d03004480000441c20000400d40241500c0e00555104224410200d1500e042c125411910800006400e001941c1c00d13214a0740000400b4008211140c032500104e9003a140f00c0c54041d05200c03408500d07101c900c104004442441c0b4034003040e188000d40000141c54111985901e802403100007400180500500080c0d00761440b500500c0e05400c2d0b00c8260040d41c11246248002c0200684d228020851080c2030300c0d50f07170081610102c0180d80c0e28101140500b0920103070080e0040c0d049031030040090104e8544854101003200044000c410500e10044c2ca10321040300a45802c680d003402002400103049007031a10030309191b001401180d640b903512015410300350000520702c0fa502c08409000d0300300329018011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 47763124 1250 47761874 47761897
    0x7020f060717040c08010c030e16080c06070204020f0408100c080601020d0e1f0e040609060b121005040e0c04151503050a0e01051311010806010804060c0201110c01020a080f0405070b 80
    0x4c140c1c2c4454080342903816071024480440d4407108020b0183e01c04218001c540070314100da54800c241003d2281e605c032008140c21500c82d94001c501c003800e564465049803000c00c2011106940ca1782c0d1280c071980c82e540107403c1480310929200070601b246006040e05485000160301900c3e04c50001c650954800004041590708207040b13402d00c0c0c0a09102c200d50005804003500c4020581896004000a440c4250041c22000c0d0070080c040051803d402c0903985001c1445429458a03a612007080c941004968010366009040031041f0307032a034002007800d0175428030556061003859200c0f100800260414031901829041808654003510f10940c0480d401c00300341c8102107070025100b1860303402c0d03510580c1c1d001c500c490080c41d02d104000307031110000010002820701802d1450a840040c0c010320b40240040d00346d40c0c0700e0b080c40280030f00c00e41c00104124041440c064654407a403030194000e400c207803400c0d0003150210011540c40b4a009401c5480396a108005000582c100307803501660750801402c0300b030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 47764374 1250 47763124 47763143
    0x51c12031503080c011b020114061206010b03040305071b03110a050609010302090a1203050c06220f0302030c0610050f030705090406020c0703151505120c09061305040b07020f06071704 81
    0x441d800d406005480c606c00070355001241240d2644181071030603034081d2441c0d1040032958170028000f40040745d0981120881c0d01c0d40d81d22942c0e0f81c00e00390303842d20800c0c4000b800501c101c0c040240a000c01036528054070301a88042c801071f01c48606124100d5410701a06501a00034040d43d18503603c6274008200340880030306200420365071072a00c0c08060051200c1100030540100d43c1c8840081c0030021240d2010925940c940c80d80f4007c551100050f640d82c0d000f0382100440030665081c50b00800486018a040c40100d50349490a0a020b850b011031b5030046600c552128020203516180016171a0f080d240014402c2f04a40c8440d99020000c0d0b11086501100340070308280040401e102c021144d4005080c0c02010480401c50030f1041c2102c0416045680b1550020002900051000030300d107c010310b00b910208060380b9000002200080803178014041a41410200403c22510128060207100b89400712084544c205445607100d9100304e550300d000480003070409900106807034000d500240100c9052 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 47765624 1250 47764374 47764391
    0x907030b0901140f01050301141903051009050c0f03060609060a0b030c0a09050901030807030c0309150302040503010b2b0606030209040b041101050a0504180204051c12031503080c01 80
    0x5505031009030300043d0310000b0071500c03014905004d000a4803402c001d00c0c06526640c1040701e0300c9401b1114001403400745101c5403030b462840d025030355480051030b044402c6070f031740c0a210641701000d8408603504942c58010721020950f9418020507956010b180240078080c0f6690b803030203008101200070003242c0e0001c100f510019070101101c2c01940255552501a552107142c40301c0a00903902c264070180c040e0071504010000318050710141d89045916281c10110319125050844404202e90445007002d80b0403007101804503010760081c422102c1c00c2d0003d0202959010801034a94240c60150030040d420760041044115000002c02090b80304507400241a03849402241441100b11400c9810076682c4081c0030a0040c1540f003c5079202c0b017440d0003450911082c81c0240705005900c20340c0354001c05942000b01094054041c0c03405480058030307180103c0031144403401603c01c4103806079200000700c0f800c0303e0040d04c02d001d1144907211902549003c0780c650341e036410082d8070800d070855007956a030b12036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 47766874 1250 47765624 47765629
    0x605090114120108030a0801080604020108070c0201090f120510050903070f030302040906090f2a0c060603021005070b070c020a230a08010e0d0c0b0105010804080c01020c070f080a0308060907030b 86
    0x203400790241d100250307110158400091f00800c4180c0120086500500030440140ea21006d115885201d03458007000068092005840c0c0b041c040d0400e8107080100180803c043d031035803101800b480e0242c01200d03100b1642402c801d04540050311040380940042000138040790445141100c0300d486450018503040d0b4420b1040110703826500b01c031030035540355100746940782000c0c020340c48401441c207071204002e8079803907860740e0018803880c8034010f112116800ea401e210840d409400119009414000a46415440144135a101d02002c03111901c01c5408510110b1103840c0450300190f000c0c18108025090136185611104880c00e00004101c4c3c00c84040c03196194822580f00600c0b8600c00450a03060300c144846c1002030011880702000000700c103500110b445030503c0c0d81102c100b0700740520651a20b007040e0301a80b00c1c00c4a4139407158000552040d46002c0010050111000e8654203650382d038803403400303c2d00e078a81c440b80038000580f0381c4040340366454410106a00b003c0d80d420b0000354210040003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 47768124 1250 47766874 47766907
    0x518060703050708161202031303030809071a0903010606080f0604050a0e1606030e01090206030a0507030e030703020c09010b0c150c040f180507050301030c0608040206070c03060905070f0605090114 87
    0xd002d40d0f180222403103400300000c403d510281b00a65001a40c02c021a07800207030820202880701804110110000c150504000e00084007c3d0039144078090302800d1841c04402150f0000040c180698682040028414450402d441c05007601c0900c04040307454480421024200c0940707014601e940e614003814410300c040110502000210440031446841c02802908036800c0d941000c060764100095140107a50700340c1125404040c0c0c820009090b00c404004500404461604080510000400d0014190002140308220f08102d592050030307130b00d0308604007540c026400c0688103a80300e03034403042e00b40c82204071072580403295403c0c203070503d6500c18140c1c8502c41c1304e6000380403002044000e50009a0b0900600d54401401d0401603d1545142d0b202c03641030004d4400c8804011100c0007040842d5a00782c11540b5803508180720070300058a23403d001000780100d0008854070705c03500000180101a1241c207a040f501c07292641400c02d0869001540e207140350320004060668100103041a4000302d04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 47769374 1250 47768124 47768137
    0x91504110103060603050c0f0d0204030c0f090c0201060b0d0f1b030204091d0a030809030f03041118060303040501030b0a0306060305010b01020f070b03070302070204140708090d0518060703050708 86
    0x215803050928020000d01216440c0c1c028804140c10441085403112000080360540740304482c2c82503941341c20034140c3d0024012500002e1084d101e1a1000407034007003071450074003651403082040000c04811350b4240c2c22180d42e4444c01260b06001d1100d901340340400da01400484400170b8011503454420300070390f107002460501c2100820350214091180540520903d6811010218071030524a650400d007070b601c3c807402c0310090400114200254400800b03206030340015107500005903c030f0a080c58244480f4244400c402c2c090a0746d40f03a4504400100c020503030041c80064091460309040c04011005406800c1006410403403020002000401d1881898004c6000740c000140800789000024242804a9088182580052028010741816100b100c0c3c01c24258200140d1300e146c03c0c404034020701400c004010341816410100070140e41c1003440540306990744404c1c0c9142c02021407003641e95006088910700d007031941150010460a000d00103002d282c2c028144182015010756481d5a55030214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 47770624 1250 47769374 47769383
    0x160501050a0c1404030803100902040803180301140115030b0310090614010312030510090218130e060105060d09050a050a15050705030609150a060903110a06120203091504 75
    0x400822198991511601540700304601d082110a10210601d40f01030040e804094411180040030440d403884d081a1200100b242c1e64080d51074039980d03038142c1d882c4d8200b98038440384a8000c02c088161494188034030144001e03400303041041c590801c481c20b65131400c1d42c0c4555042c980e4502a01c0c0e2540d0702000b03080301d40c5010000215281c2d6071407170b018003270b61503c81c645120030fa0300310018000030704060150f41e16034000d481e0000300e0b56103034550742c00318582d0b03980880f24541c40000d0448401b1100341c0c9071980600240c07120340044034000c0049045030182e2099103240e4200000600c035504d0b0600081184450101010a401b10a40c03107407824044141421501d40c0d121108210030031801d107182c4184840701b22000c02071458800c0010b0260f20000700447e1113440703450300145540d0505041c8036140c2c3c0c000703050200e0040d103504014141c00d40c00d000507104004100783c10340300c0c3d28119051005035091581d40d44d80c0340c001200810080d400140640380e4074082c8584d40007130384002356507242c4a00e01a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 47771874 1250 47770624 47770631
    0x30c0201111803071a07111516031106092a040e030c0f0a020108010504090f0b07110c030316030c0c08030d05060418050c010509060d1503170703170a02160501 70
    0x107a008052600d41107501056040803139071004403172004c2c1201030303440440c2c011081d044004030141c002110321b262a112030009050204003000e4a0700c0909480450b24425201e5240380100403a1855032028100e544002560000382c15614607070503a0850303550703050034000340a1003504590005041d5051300d405d00099900c08106009d40d01010441610b1050401c0c01070429410350350002090110140944e5000f142c5400c0d25100300301e40b9180c180c40d0f45800c60101074003400c003014000c1580031205205d0707817148546030308021a460f011007210b1350044840050880d040255405440ca031201320806c0d00c000360794600004065400344024050040c11400018040c076011040004807422400200600102a540c84c800114001007160003024242029929860100009007107486030130005100d0780d00703107490002c1030400c05101c5020740f4810585220080c01c80b0844400c58013621202600050303515215813200081300d82c1c0c0c190020001c10b170151400143d02180c050300811540115907030f070b55 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 47773124 1250 47771874 47771917
    0x70f0f090b041e08030a0f090f03020913030203071a0a15081b030709091a13020d08091203190807020a050c090a090501020a020d1b150f1503050a06060906080d030c020111 75
    0x10f1142d040b0011340090b03d03010022768219000304090800050500150499902031031050600820684101940c0a00740010411400e059010704040030b41d5001e01450a155000c94055100060101500c0e40030000300034210080c289241624a208001609800392210214122503d4050259100d01035108041406442c0c0c0015020301002002c904460319007118485c0103a0300d42007030790351454004271640d441d1b1088200280c0d0301401d0042a030103a2000150304c2d0b004400c21003411031f041046446c0d18800780c1e14254103907102c4803480e800401641121380e4a095a1421060903500325000800000300203e507651190b00b2070f4468010170b40903900804400100035841018203040404011382c0e91060706080da11328040f560016200365100b070b2504c401083daa8590380c40304499102c0e482c10301b400c241d03032400c0035500d51a1006080c0c445500f0100e001c00e101d900341c0030741c0f41201d010000604a884520100b1402494441c49100440d500d600c1d207c061000c40d24060f02641d4103541500c1c81850 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 47774374 1250 47773124 47773127
    0x1030506090d0302090f010e03071809051c09090507090b04030b060906190902030606070203010207030c0b070801030c03020f01030e0304090f20250506070f0f090b041e08030a0f 78
    0x24002102e410425004206440c41d0b600d0303840a07034422003420b003401c17132410004c0c4000a04000f1550030180c1d003001c0b8600600740074901034010341540c50090007507405003102980d4010f40c83e03a4015401010481d43c403c00c00010700c0701d5125540c040c44510382071840b036445610440069009070f100f0358900c1c9100702880081c1c607110034400d4100c0c3e41103458045c1e0007021050344000869a00c900f510301a07006c070000c2c40c80d80b58041241d85484e0300800840d42c98482e032038060217100840c50141c034010103100c00104120301601c0b056060340d4010600c000b5452441c0d0800c820020000c802d9070405440d0042c3d03030305400041003d000500320069000c60700c0742c7d801091604580d03d1051130443d00e40548007503450942d441080300d84c06219203100c07907500700d488901c6c50040c9035880001031a40c46240d0800c0b898607030104541e42d0a52903540d62080c8d1141145088800094900880390105810441085100c803410031034000c3e40340080e0020740580e9681201c60030b64100704081d6020071140992100d445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 47775624 1250 47774374 47774383
    0x3050c030c042913170c012109210807030203060d080901031401030c0501020d08041e02150408060f06090708150102010e0f03030a1b09180e0a0606030213061a0a09030b0103050609 79
    0x514008001e0006c0c1e00c180c00001c01d48006c0003800440a58035000c004204c1e04544c102c14011074001100000340610942c1c0b880d0010000c050710800a43c05034085407420307110b4000c4a0140d6030007492130150b61029141c0c0c91980c4e11140b4160306069403461410015162581d607103008600030b029880d20589082e0029043c462a910118204680c840404c0002601c2e24820030345e000601000c585041c0c114404035900300b00f40c10200c14200404140082c0501000806a00c901d18814966540f921248184803501e0415940c07000820b6000000030200480601d514040e00814400814903142c407900c0281440741122801d401030704000104204034100b4028496403035001546640c4bc1120b050004040d140e15001700c0c0c24000c845d100041d071103d4150448a115000380061b41d042d200d05140810040c81b80348001c038085c800000540d031140c0b07040d1003400c00302c0300484a0304010340600c03415408198400c82c034141c14080081804000705401c00d40f20390203140f1800051240d400c02c8814645030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 47776874 1250 47775624 47775659
    0x306030b16030c050f12040206070807050c0f010306050619090b160b130203060c031e010803190e2b0c0b0703020c03070b040501110f0f030403020103050c030c042913 73
    0x1e204003048404969941c110440f601c01c1c07190134a06406444238400260980b14591010380300303002c0130888400744103020805001c184c0040b204130340460940300c0158241d0307038684141a07204805208881034810242e01610800f078552030a58800c544441d115100b03604441140791944680704841c80c2003104d225501c0d6003088885200a000d006140d00181c0d640f280280503080209010007c00c003407403200c80c0c0741400320300c01505800f05903840c3c1614656036004140e042c6803100c5800c0328090311601500002003502c0024010f03010300d604400d00b007000c00c000f01c0207402004490307119000c0418401e03420f40b80074203075940701e5aa465100d401e00900e003143c0e454840c0d00c03e4000100401c41d80019100b1182299803e00b0702d80200c002a201803070409080686840c428010700855140401000c8010419203200340c804215640b03074001c2ea250a0701040316149100b2600f0001403080031034144140c1005494003691280c01101000882029045400544840111000f09101c800c0603030b40402c41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 47778124 1250 47776874 47776877
    0x18040203010b030115020c0301050106030c02060f01030b070e060904020711090c0906030402010e03030c010507050a110f03030c0f040b0a0306090501050402031b090a0503030c0303070306080a030c0b070306030b16030c 95
    0x565040c020000441c3c4018425014441c0c1810303040b1000038001d0066889404000b4020081503a60360809805084020f596800600940c0006580703a00d07104200d0f070507260000a104180d5a0b200340c259020090681010b5000c0382c284600300c50343e030350f6000900c80c992084e4810359802000d00107002e07034401c01400e2410801414000600749845280a681d030080d024070b0030b45d44034120103000c20704502c50361445090035400d2008110030760780c0000c000c02180743d80e41d94019031500080095a19511001402040f0340c0040021a0444402c1c2c8003038107140d50038443d45440c4c40d0f0b42d1500000e180c4d000100c94000301b034440100304886000e0344966401040700361025882c41c98a174101c160410249648003500311404160154261070b01c070b02c0c000c050400038003140c5da40c8442e44109617070390b04221040e000103404c0038000b00c1c2811012926102c1542c0c50b0700c4028107900165030714a180301c4001c02c1c1d0003c0654074040000495500c001141c0200122200c2d00c0c0c00d65403c50004082ea014010b4910 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 47779374 1250 47778124 47778127
    0x11a0103051e0712090605040c050f03010b09040b040302030f12091b030a060f0f020703030e070602010c14030415020711031b0a050603040213090506090c0a030201050406050a020705040e03180402 86
    0x2c854000b545035500101d945072040351202c0302d00d81000100946000a0300f014600b104210411242a031143c040d52000c9920f400110b10131410103003a00c414440207908541d4000206000903620a00940c10620a0050b28200b800600d15001d064100344080307911020000140203818071300f84110751044104203405404003201001081d6106944c040c010002d81d41c0b0144030304100c411358000111400030ba0f034159554125418000d001e04000d0711018040e0140c2880045c02c0c50051080350800411b5480341d9200c010751110704099a00020006d407000c001c1400b0104695600e403006050f12072244e0240141154032174245841c02e02c001c0502040c038818040380c42040c2c1e0b55001918101d4000b1130f0304903900e41c1c03140301140f000e104000e00c68464900301950a010002d010509900c108043c50031100c414003d04104000d503034a80c80b0103030100703100b00001d000003445030380100810074003401241e000c1503a483c0800d0407140b10500007041030b00045500440303625109090a00e10108580030b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 47780624 1250 47779374 47779411
    0x40c0e0c04030c06110f0f1506030d02120f0c0d0504090c02150c0c0c030109030c05150f0408070620030106030605010306080705061e0f030a05010b030403020c040c050903011a010305 80
    0x200000c10940544c000f44101030044074000306081262940b888401001d48102020480e2880d0b80c0b400326146040e08844107600192450400060241f0082e00310b600a1081b90080c16a422180e40f1141016a204504204003856003400300042c610484007541c81075540c515201c20b443c1280d140c80311a0046401110b000e060301000520402c1d00100200c03005643c941407031032014030b01006032040b07540650074006d401c000e2540108c003101b8640d00030819034015514076400c800b80c4000440d50840031455101c04540482d6054001e0560300703103e1480019100012422480c0c4615040f007000540d4000100510002c0d62600664005007000c0c06d0601000b8140101140c07220005e001e550f00510300841d13031141610344449110403505005658a54440c0e0038228200c0b142e200710b814011590070440002050014441100d00c59038041d8050000b12069100708401780010340110800c0107424041c01e840ca540c284150300007520b407506240b6145002c000090155403006256628400c10740151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 47781874 1250 47780624 47780633
    0x60f030a03090302060906041e0303020106080a031b020607060f0c0f17040803040501021b07080105070c2102072303070e010501120b0a030f080904051f03080d0207020405040c0e0c0403 81
    0x900b030550360304540c03003525001c000010483e980181c3c0d21030150409826600d4944100703030032000090b40d000703500900441b6150101180d44d2a48910000c001800c0302a01125a02480e2060900e9901c0180914902191611941e05440d41c0031036210b08a81e4403500703c5445034212900000400c41810300502e2500e1542c100066410700138000382c841c4000000003020030400303504403505528000030541140d04648036980d40c9640c03d0041d80308541c60100413400050080d8014450190b102c2030501040800b80700c64a5200c0400b56440254802e107500843d011048254043d40001c00003841028000c00004043c5040c603658080c03d11801e02c1c5005000c166404440c104a030391032602d01041000740c84001c01c050300100d51000d00b14040c8002e0500c01c001616004003070701c6030105c40034002038030360410007000c00f980412080310702d4111020800c000703050b44020748140ca101c40001810a051030f0085426510111400c0719400200713101030001102c003100c002e40020103407000500309429030f40c0d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 47783124 1250 47781874 47781887
    0x102030403030e03030c060702060103140303010506040603020a17071106160503130c05090a1d1b040f02120406060609080d020d200a050102033309131a060f030a03 72
    0x8042d041151060100205880c1082254001c2040e0300440d4494508410001c1d2201400e0008540c442008880c0c840c0c2c040000068a06a030381c0181401e20302481c1600c08e5009521280603c4240140b1210042c1c5801100210b40d20404040d12401d500100c40016141424001030000007800035414001d6a243d070711205583c0d014150241b595640c406504000c02d8200c290350280307a000c01182d04010b074a1100f41c1103402d0712008040d90403e4490074880301ba41710010303581801686107000c0300302e2170103107801e0b040b030b11403403400e02401442d103545640c0701090300f03a044034143c82c0ea549500c81000060b0307004100c800100b0680001c0c0c6222503403814000e4848061007400c8080142d040c0e035000510b1001205501d401036104100c0d004c9070301c0c503e0300324040e400c21a09140319000c2441010100000440700d034034122641564460500c032402d04011910f1006004074060100d1040c14800040c1800304140c0c3c03000500401a10a00d046010080380f0200310303a282d03000c0c7d00400c42580000b600410b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 47784374 1250 47783124 47783129
    0x10b030612030c0a0302100c110a1b0503060109020703090f0f0b0702120316060b0a0602070e070201150e150109081005070e060403110906030115090c09050901060503100801060501020304 82
    0x55450071090802004140746001e12103d40d035a5001c0e481c403003020580c000030010207500e41030030240700d004402d4000303a6144494941458450704018107041c000f030840318015060f03203c19245500210744907008286000b000743c00101204c1c1c0d0008545042c19081800d9400a0040089540b4090704103164030400300308500c11103803003070307008169502150786e59440d102901e80e20000f1a91a0140382c800d40e14403240891055440910300000348006003812000e010685610350001d10060703103000d003100c4082800600902c215565240005036114840320120b009044d8055180c5050a003503003480c0000d1500701d0054180031601404004942c03012406100d02c0309403160010b1199200032003510402c9078040b8a82d400140000d0220030000e4042495103107900580b40c03440c89584a0782454200ca403c001d403800391000181d02004000f00c0c40d002030800c00c419103800c80307440e0343e02c1012800c003000070782044e0040764002c000c010b04000404400002044020000d005075450040003035141d20560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 47785624 1250 47784374 47784379
    0xb1005100e030a020603130c080106120b0901110a09031a0421020a060509010f0f0507022a061b010b240901031107030201060e0709030c0b0c0f071403010c08010b0306 73
    0x101c185807807a80e410f00c880f030009900600815a41c1c0b800c902c1c1c101614041501c11903004141c001d0104948070b0520506003030f82e80c8100c0200300942d00d520b802c2ca00d64001400780d0000c0d03403100e40c2d84c44a0900756028100e1481c41e920394101070740c203614004050070b104280c103039454a2a8001c1001181d2071022030f84a170055452a008040740b4000d00301c2c203100300440d02400f10307400c00041c406408415404180405c3e40d540e010013466040c0895a4265002500c5510040c4d005098510002145210b018440e8104c560f6400280b8a40000703c1c126400c0588003040400002c40c500b951b052007070040c0740c020300e412502101003119101c43c0c0d852581807940d44620030320020524912590203580f001c42c0d41c131465001d9039100d50041ca8000e018010a001d9007002c2d801c01c0d00403940040c01a418142600d50020b42880c0813410407070f03960f4040c0c115004000c104e110b10071000c81803202c2801208044d1454031002d4030007002c400c3c1450f00b51641c5070580c00800207031000421405881100380e03900020308 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 47786874 1250 47785624 47785637
    0x909090206030c28090612020304021e0111100209100c0b0103150e0708010605210607050f12090a170f090910050310150b04031203150915030b100510 66
    0xd0241c40854400c181e42002030421140d4501340941e40c0240c0c403407084070303042e07650901601b03291101841a40416074009400080c100303d0511009051b054010481c901031620209500194401d01e00e010519462030200503030009042c80c0600384510199141191411305403840d40e026660715010740380501c4007900043e00700d4030311800c0a456800c58003504244000f00d602558550101c20700034441445254800d220b04540d83c001009200c10150000190300040d041c5070fa0303840019149648031188841039030104105031040c54001128050088410500625008505151008080c48076800c40021060107100a62010b1030f07920032240352050680307905c90a612040100000001590001070341070144005000424900d5808181c20040c0404168145a80e40410409911403400050110060050501c107103034029040305101000c9030501034402540d5006050444291a29503d600001003000b0018022203404454000402d445014545460714002815003145c041d05402031000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 47788124 1250 47786874 47786887
    0x203010b060708030a14070207030b130818030d0302160f0c0b040b03100f05060301030204020a0e0a15030f02090102070e190219120603150e03090d11010909090206030c 74
    0x10290010444204040d11481c0c8480c61071420410302d0b0011125101c25501c4c00d5000c488000200c40c1c1c250003002d880c1c0190081c1401c5454000041c0710040600c1c90a00100000500044800340106010188211500c01018402d4101800c100503c40b00a04040c014069015585c14448880d40c50b698020b1400d0340407106840d0140220010b0740c0810b046d200301007400a86840c82c100114030802001c030b90302c1c04458407018802e6000400b8060590000f2041c401400103013010760040110140d142010000c0740c021a00007a801130294012507602c880760300e0704402c11a0180601301c421030703449c2020f6080040c8580001e58408081c891140c0c2500c5002c042084c0140d1211100580910314005544da101c400e00e20307440c064202456500000c4901d21880000165442403c003aa6401099860318482c201003c40c05060b41c403000b00042d02080110344d409a40f1134103040b40e864032a240e800444204040050f2001a02d0340c4040a1a400c1001e08001680e650707007101d6009a0b100301c441e44075039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 47789374 1250 47788124 47788129
    0xf030a03091e050306040813080a0f03082701020409060e0402180601140a030c0906030203090c0915090a0617030f04030206131d010302040f140a020a020a08030a0e0d0f1b02 76
    0x40742030f0712094050151a00740000e01050000801d680081200405095036407409115a90306448801a140450014500d0006441101c01c076402035a01d0803840708000140050201228012413140c041e030b03500040070002117001d8040c0c000185044a13591102c0d01c1c10380c010840d030410300141031021288000c00076000c2d81c001c2440c140301c00380013020691030302c40caa07201400520302c0d00c20a202180d90340742c0c0050f840c3c3c464000c0364811041d03100940a4000c10405106040301b0107401b4281c51140e0350303441078088e210161518032601521201140362481e00b140700c9464101409481d2140d0010000c5412100115041303404896058035441d80d501e00300e000c02a0714441640084c8440e0014009022003190300b101e40f40d060b01d0080303c040120f4440120040101c071011481105041d10716000115219825406414620705a00580c1c0c0d81481e01e58540056500449061a502c1d980d10035107041e50008100e5a00c0c5d202e001d003440f00780040210340c043c040700d4866491035003403a400003c090854 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 47790624 1250 47789374 47789429
    0x2031c0314040501050a060b2a100f020409050a0e030a0c060603060e0604020f0402041d06030f0105090703050708010b0d0605060307030b07020f0f0606100f110604060603020f030a0309 81
    0x204903448428a140c2083d182c22400b0b0030301070342e45c4a491030400390046042500b107401c4a0b4824810300c1440b004503415600050007007402d4516a005010300d0407010b4070085240156010520030f100010b0782c882c00c00c0380c0c4500721007000e000b040c409841d00f808160300c4003000044405607240f81c10120981400e904c1d21101501c0c582c0c000401c55410015140d4415100250740c500891080300d1840c0b01c070500d80c00784401c900603442900041395000c40c000310007482c03220072a5040304015044e10780c8030740003100c0f1034203680c02951500116400304c101001400802c0c8820805000350340024011184c14000150f4940e24141000d40038940c2c0b0004030b400f030355082006c1401507520180000d004d28240f41d01940310035000e0b010b0403c501030416907040821001c19145d1003450001c04041e00244000e504a610300f0030103428030140204021100d118840c10043c00e44030b548070300c01c0450360398210b20501c243c90802400150190344940d000300d00280c0c01400000540d82e001844024020102e184054030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 47791874 1250 47790624 47790641
    0x1e080c1e0a0c020f04050609060103020c0a062415020c090a020c0d081e0421020703170a090b0310090c09050a1403071203020606011805030d080a06080a02031c03 71
    0x108000012106001c1e03030042070b2189120300854011407000080020711064030707412100c242c2d02141c94000200c40c1c1d8002e23400f40020061010840f0030071116640e80100701e80b01d075041074802c1c0b28801c0c007919850160200d014054400700c0c10490b04032039a208040e55900da00c2506c00d1146030711a0002c0d152220640c1550030415004003114040051200c0181c01c00c101600c1c40c01e40c282007100c1100c0210600d5107024011a40004a812100e242401040b000702c000e500040440c019a50b0000100303581049110303006c583d0406003641c52000c030a0140206100344d00100d00010180100164010740b10b59000441d41240004038441d172515a0031100c406058000c141d004000e00320101c4c80c1402151010070081040c0d00711507281f520761b4100e83c955100008010010b0f842480001d200e540300f501100c115152400c81b1003442d5464400081c28100f401a000000030045001c2080541980c01581c006000e801c1c042c00035107806401103030319004141039a03200300300182c0c0b401081c01e1280d440140c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 47793124 1250 47791874 47791927
    0x1110303010509280c030605010e0105070b0606041e15090311010c050f010608010207050705041811030106090204090906050f01060903060e0f060c0703020d09060804061503060c020307031e080c 85
    0x40d42d21130802054014840810444002132030414045002d5005500800d42804161a010f04052156541a00c1c1c0d210051000e900104240300004251000c5a100e0309001c00c402c0c48001141e0610034050586a8000440020851048010800701e410014010384c0d240003860a130426504034100b842c90541645101c144940c604040015440e070194090159548500c09840b60180d903902004103440c40180f9070f410300322060032404001140e0315001301c0745031005000071a00c6559064418100d030000d90100403015100c4488504214051003401e5015500422a103415414118018425842400014420f5980d040d44480c400e800b001000c41c40c031003240c21203105190550000501e5045144202c0140c447c201d05208124042d4201400f40d80300b90ba64640c1503615502e03404094404148410380c40c284860010004c1000c0340a00820717084103030015559051540380003043c00c09076001c0303030341440c0e01c85041e1464070f079105004540005140050341c4e21140f2034545030b556046000103880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 47794374 1250 47793124 47793181
    0x11040e0a0b01080f06010510020d0f020a051b0f090c090d02010207030c0f0303020d0201050603060621010c03020903100b1f11060403020d0f0503190203070203070206040f080c01110303010509 84
    0x5140500000c506120000b45005d40d8281c3e40e0311011b00c10300b190183c6240016070081822626040e1144516040780d407014811240c07001035a4a0b600e051540740c0c8a0440c004a04c80d1404005040c11035812400c2c000c1503c2e6a0a20b01e003c1c1e13071070700140c00780d0340d64144a44414960755066a10030001500515000344030b00500650340c00c0582c0d41d8000f14881140540512500d8140340d40c010b20a41d8440e49014019004583c3d82e40c003040040d030302e201058131328459140c4401140001c2441034103414501900d0050b6200c1c2207004062030150445d04440c0c0040c1441c2620f0301603180c1c010300d09110410602e5450343d0441c0c1e03000c103442110750804030040070310904c0100000e165001801c0c060700300c0030780c691610762080585c04440c00d200c21125040b480103031403525203204000e94000c640c031003c07510540341005c0c034503400600c0f540d1184c2e029480044200c81e0900a1170801c0c4101401107900b400d2000e61740c1c092404941c2c823400705100c0c241c86480e0007000160400c07040b50f045030805440d807800700c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 47795624 1250 47794374 47794379
    0x70b010e06040221071e170601030e011b021009050a060f020405090408030a1503082d0c01060f0801090209180118050607080606090303071502040302030102040303051e030411040e0a0b01 82
    0x15402d40d0115071600004404141c0c02140c0080944100d41110543d5111f86548244408030103075428003410107810550b03612110080c00400388159071803800c81002d41024982e42c030500078640701030307101000d681c0c92070300e12804005400080c82c00300003540080080f4201d00a0448007000713000b242d100315000949102080308201140d8001c600c42d6000c2c0f40d04201d90301d203c08104100041c40c0c00700520803542000034540f2803d040182601203505070011040340a9000d0150150b500844100e203030680d1114414807502a0201403480a09000303002000908056000600440300251100031343c4032000300d0748003211100b90410b96203007444a1400c000011949441690b6000c00c903102000606180007040044c60305400311540508000e0007582131a0940c5c4690142100781c0e07600c00d410560030400040141c03030a00180c402140a5201d2540713030008003048110708445500c6220b280780081040100040b03031a1a0350b4059001920700007484c0c04402c003403e00d444480701e8003804e58036801000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 47796874 1250 47795624 47795677
    0x1060b16170c070f1a0a0503041104061d0f090c060f0c010203010303090806090a0b070e010315080303040c0b09010c030c06090f0c090c0512060904151401060f05070b010e060402 78
    0x5241280c84c1d03442d8031040e055550a00d0140c4012540320b485107502d08100d075480b811b100300b02654002d805142414801580c1d0000a4200e500d01e074002560916000c44e103150204000080315407001c03840b0000b500307514000c20200c2c0c41da00149600b504c1100c2c007080c1c00c1c0c55020381d08207484c0f4a260303110003103580c2e507140d01703000c4c0003000c051081d0b0010b8411040061641480414582c91455000d110040c0a885d1034000340c0d880d4440603589810943d81e1038691910380c940c030300c0c02d000600d91900610340d41e081504100986040c40e4000380890201080003203d584d900c0328a0300c603800d416103420002240e00380307052000350202ca0b801610104803105c04100340301049410b201182d811010400a03020701c030500713884500490820203062031040c00090494209081000d0384948075407010101d2040510840b41160500041d01e4001d0740030300b0041c000140c000101d03030030b01c128908086040c8902a664a0b1601c0c80c14001c000d9a241c014010801c0d0b512181c05a592528052440241c01c4410f100e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 47798124 1250 47796874 47796883
    0x70c060509101a0a09110c01050c031005090c07080f121e06010201090b0a0917120708070c0f1412070807050d0305060603010303080402011205070201150801060b16170c 74
    0x440c41207443c0c8002c0c201c0c101060310300300503845800b030001020075152607007410007440c00b036621502007041049000114a001e03c0f03858807841e02c1c1219142c59081900301d0400071b607000e0300603501414088080c0000e030b510a1040d00c0c284c50380600141c0d40c0c1d00c511690703a10345001d44003860900e00161000c1c80001d02c00b007070f150181c04490106c0d20700290b881400490a8480c9000045c00504a10340401c2c0c0c0d2401580098003814081c3c80c0110800f02c000c0e08110b280d900c00319880092aa1031014040200c1e400300c040354100b0401c2c035107444000c1494035012414086070070000c10304081c8440d200d0300d1140130b22201241200c501c8030540c03540e0803820800740650011b0002c642d03074005c850b03920401a00901c00c0501881024060606507030840c3d6090b81c46c10f102400a0707051150000f81c107880d5003020f00440b40b0890441e400410003501300048690008040d4000a202d07905000c41800742d8140030007035035003005280032a60308000640c1410621719400024405104c3c00004017840e44040004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 47799374 1250 47798124 47798143
    0xd090302061e10030303020c0703020a180b01020309060f2206200105250909020d02090418080a0e01050d11030907080d0801030b04062d111e03070c060509 68
    0x20641407900300c445190000c24904440e43c610000c0c40c0081880441d21035400352411049210861300010b071039400013a4010600d030b0090300c1d8001034104050104541d401001c9421000707000440c10f003045540040c01500a50b40c02c00d11441000c0b84091561040a80d02000c00c105803240d00e00c01c45d19424010b14007028051850020300440b20802020001480707085c0c480c107460070a00c03018404140c000804038010101500420102250100703580185c3d100500000d884400016540c1601000b884151001c0ba20100c400c40ca4014201c0045060042290410340c230310324050500c0700509005903403500810030441c640e549800f8071078040510f2940114000c004260460f019203584140440d9120b070590010380003e10b61f50b004000081c0125051500240304280c0030070581400b180e81e006240002006600e4400c031000c2d251186141c51007942060210724803c1454946580c04640c00301c82c001610030b2a43c1000000184094482e00740c01c03015035441502405241080c83c006559030318402e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 47800624 1250 47799374 47799391
    0x41e060209100e06190527011b03090905060303040308030a02030108070b070507090b0a0b1204030905121c0c080304060c0905090f0a0903090801060f0e09060709090207080d09030206 80
    0xb032030000c4902a0002140d5210000c00903407504600d12001c0b00410721060080c41801001d02c5100700c240044410b5030019441502041c5105084400050204542d030407100c403c10340c400742480c04640e014456800b6148040008030b041e89400300802d140d44641e501c043e1080101105126182401360000d50489e000365044602d540e4440d01500d2003407081c0c1c20024081d40c4100c0080205a8154020140e031542c010a14810695144480105c6610080902004150300c800b00310805070482000030241c941074030a00d22a80075641a80e0f0765194151904170703000700d0081c10084240c8590000c20203940c2c803140040d2607003880c1c540007018285e42c200c44000700d01d81c0d240101c0d85042040c0646d10501d08003442d03051a440300c40b000d0740213180c030352416000c11105410203c0d0060742400341d280100580134801100da45401c0000c06a031502400c4050550000d00c02d000e4034540c045110701c2980d80081d00180c2d601c0d824a4520b44511840101420041c1011490401c3c16004078080e446802030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 47801874 1250 47800624 47800639
    0x50c03010f0b12010c0203030f10050a03050a0312020426011503080a080a11031303020a0203160906050a03081c0b030d0c0501051e070c030201060306020c01020318010e07030308041e060209 83
    0x4051055085c2c4104814034001644240001580880c0c0c1d0031001d6004003013504151032098403940840c0e0031025681058403181d20400200007015030151103001b03991038000c021418030382050303050324040b214080c0140980345041100b8500e041b085d40401c1e80b0800018008139038998a1822002a03007044e044400403e0b105000120390850314001c40d00b0072203882448620355a580812001e1007015144107400314403030f520401005850400090310307040c00c1c5c03028080c6c00394a01110481600c10a1300040d004845c4854100300180403c019501d100700e0b1032800c89928090851854000e1078410116075040c42031114049070643c2002498001500440083c0324554445200d010b0b810644268654258107801c001440c0500c01c43e0350010f42c0e0b10910010451a030340b0740359003050780c000006078000c503540003050003c0f0303e800c1c41c5101c50b070203202d07070080c040e00540610003515100184409001d101c2080700242c2000940402088504100c055040106e005420303d00001c0d00b21401d001d004040303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 47803124 1250 47801874 47801899
    0x50601090606120507020c030a080c01230103030e0310020f03010303030b01051303170f04090b0901060206011a030c040b18041d1e010b030d051306050315010c050c03010f0b 76
    0x4540a03510a0b10718688801d41d05101c481590002007900805c075000310301640c01442081c0d0750520846100d68001c00e1450307103406441214a08540c12101c1030301031104081c0d5000201c4101d140d80d50304407505814007100c48801040401c0c248942daa070070384900d40c40040d95000031550344010314142c0b4060741d4200440c1c00404015180c5202d0b00d116401d081d040990308100150061514298035a03505180504002404080c1c1d40160000c0d0401c0040d2030311045008041c2c10100201401004c46100507d155458540c075001e024110000d0b07014840b400000040154900000721030081820400356a80c51180504894880d41d090044620a0742040310391000d2002500d032904042d034802e00500110310340340d5840408515250318090b03007952222218050b982c0c0910410a42ca4190380398a65101c0c4600801210130325280c11070010b0000500174403203d0740d030316040e00500c2c0c5005e00b040040d511140c10300703501d00404140115071660915400260021041d00010703810602510300340d2243e40e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 47804374 1250 47803124 47803139
    0x60c07032003100e01061701021206060306010503180c060309060601020d0e011b060b03030f03090105060103060609050108041703010609170303040b040206030a0f06090506130614060d020904021303050601 90
    0x40041c10142d81070f404190400150241944514209086038000113091951003107030194a0801c0c040c920603595011032401c04405800364903503440541120a18554941540060039601014259815880e10010507030b4400030100480f000195004290759103908e080c4a48650310782c0100c6465006004e1403c45050142c0188081541c202050f1a034401340c031341410000b010310a0742d0405484560303c030105031003941c41c00e000800005502c0060f0b036075a45440510302c0e0940701d0203031010741014500034080040da548080d10405880013407030002d54544650510181c140d24101035841e40400000000500c541c0006681d0119003040007005104240024915100c8c0021075018000c1284580010300514100005603409030310307000e00245003031048482900b00c542c10780000755040d98032030510500b840c180b0708001c04203200510905c0b1240c20000c50b9614070410fa9a001d01030325010a8901140340c2e20b405417008840040c0045484400d00b04507900d40492901c429035150203090004034014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 47805624 1250 47804374 47804423
    0xd14031c0b120c010207140102160b0304021c02031203070c020a080d1403040803061203070602030106050306010305090f0d03020d0603020915040606080c0304030e0f030d080405010f0221060102010605060c0703 92
    0x1c0016006030006c2850003210044000c100c1c8400c074114015034003284a440282900d00c0090316981c4425a105c0c64076106008407013003200949c1201c54006010800142d400140306030400d480303055003a0722070f2603100c01605e01c500c3c40c900080d8020030200740414010f000281d002d05050f44d50390b44003140454100c600015210544020781246000c1002072070034204940305110304080603048074a0100580c4035a01241c0080e0400300000c0d20010a02c4840e47e0b16011b115044103074540a0715071124007a83c40c91b45e40c8022000308041c50340226106180c015140d1001c402540c0180840742d41d417903d18510003643c008070030700351b20852410001003181c85c810102144031300c00081c0313400e03d10707111900c042e10803620300d080d10ba03400881c0a031440030340e880a01021000500c940c4400801e07050600d041425aa8207076941281c0c0b034418488880d81302d40000603400d404250141802c0309444600040307025140b550801c0d0340002000405a401820001d140c0007103d000d84402c0341051251045030084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 47806874 1250 47805624 47805643
    0x1e05070305091e0109141c0314070c080106051002060f07050c070e0603011506080c0702030307080408030307020f0f0c040b060409180506010e010501120507030f05010602011a0a050d14031c0b12 85
    0x102003141401f110400c60054900100c0c0e00a0410707028a00c07000702080385030307844000110f60840f00e481003040350003003d02800000d050200c42c0103900084502009503220002414905841048408070300f80c54000c1046504e40034004068030503054861800e40c242c008160ba202c0c6c029842e00d40501d21404280c094032003074515070394908500b5200c4c50840d8049400116040c2e91500040003070b040001d54650051000303241000141d900c0f0701e080c10001e420607220060414140d00b105080d010f007160b0210b032108103070a040350002400f21444001c10001d0080ba00700b10b203203904e0090351040d20943c07002e41d001d220f4031800890b98140e032101c031322185048003072082d20301180d02a900c81103491680d4000c19070107501da1900103402c107240e201c80c0e0160b030070a07840080942d6480e84000741030158800480300b9281c0594500b20403d103041c01082004620344000f8042c49039081c104156084d041c021101c00b01c1c020b05040c4910207001010000402c0d01c452a248501018118003807165008a0074401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 47808124 1250 47806874 47806879
    0x60f1d010302030601051e0d0303061d0114041802030303070324060906050c0f0706080601021015120206070807080306100305070c030305071b060614011e05070305091e010914 77
    0x110342d00e070501f84030002e4425004200c40c520710243e4021aa01c61071124a000c41c02035501081d5180b50101d81210550140416104c0310300440050003d09814892500010015100091091401048558032803d0908025814003000040c054440d80c96005a000c070305504060100507000010b071019005042d203d100701242040c6403c00c00c8034014809048401d611506441007001401030305810101d0981110780031030502418003051307582c10041401840c2203424204103201440c6403003120100d4a00c1041d83c2c480b503800040c011074543c6020750f00550b41c0030407070fa9151001440c00d540b01d45c0040f0b034041c0c056550b8a01640b0210311034011a0301440907519440d9442280c1c0c0c404402a100040611080c0510350150021202c0602d4040c0f0f00301e80202e10018941c0d007041c402070f1050264a440504110050003014803082801000081100060421556400711890140c409028400d1807582c41030b4101d4440c040d02c1c49450103e203611409a0f140b130483c580b1280346400b420f0400d1411034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 47809374 1250 47808124 47808133
    0x504080d0c110a080706060b0c010e0f01200702220504020310110304110a0f03050604210504150e040501080f01150b07110f04021903050c040e07050a030906060f1d01030203 76
    0xf020400700f0300244051070081c0004104651588950035141c0c1c0101c0754808503a541e44a0fa058092042c0190130890b0411402400801a0700080c0003461809241c06603880f0703400140c8108550382c607141c180104014600c500510b410b1039544078001c00c401c0b90f0076030190003600784030b600304c3c03095100326400c0000309100c070382c1961116101c0511110300c0340c05458001c240040007040c0c4c00302d0a1028401180b0480c01417000e4581850001081c0103100787c42c902c001c041c620a80780d42504075064070103840c0c001c1c01103014505008421a141d10403140c8032034200785880e001040b48040401c000048811503402804202005040c10403404164400c0c0e5401e440d041c800c01001540e0120b0048110000412605c0c1c01240d150018089a221204148142c200020000c8481da014056258002400f4911508061074503c0148002030010035010812000080c40800c0b140298082130710307190854820400c594840700700301c3e8290b015002e184441c0c081040f044c0c0b03c070134602c540f0030705980c0c1c050041d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 47810624 1250 47809374 47809393
    0x7030c150f050744040609050d0602090411030106180b0301050103020f040e0708040b0705030408070602160b010306020a02100207111212030c07150b0904020907120504080d0c11 78
    0x45400d40c00c0040200c40b1380000e03a2440f041000f00300900c5651301095030182c2e0096150241441000d10110810311400800740700402038141c01403042801c46100351041000c0c086d60740341100c000d2080c81070300b0343c5c082d29150b03039000d0b8a8150f10185058440e644c4076180865411b00c0c0b030b110165014030990aa01c4400c000500c955446030300075200400c4c0c452103840c1001d41380c500320800d08a0444001002584030020801807090203000f894001c140ca0500382d02c3c60405403251400c910407601c01a0015400040c03103c03030304506e12030300041c0603000781c048881ca507101e18029007c0d6204000040041c458244ca691a00d030542c402c40b45029444000c05aa8a061009010724040c10006801c681e00559034282c0f0300380200401148200b41e400b48003580d80c2e0161078004002d13400015204603080c41d142c0602c03144d03114459a180c00036011900301500b0b503540c000c101d485080d8004c005071010b0812041c4020410341d240586005246514284031000010f2030458510b5001c7e11020060707441116038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 47811874 1250 47810624 47810627
    0xa03030f020106080f0f011103010311011407060c0f0e0301110702040906061215141e0901020c0d0306050901080f0601060e031c050a02010501050603090a03030e1c0207030c150f 78
    0x1031414040050002164190f0f45401c09801d1030300040840700c080c1c0008660611820b002e00c0344944004e05a806182994155120000d00364041d1056a050028100daa5507500040d0410341ba40207520071000e20040c084100d0003400d000480003100e01090101484066a10303040c0140c000300301c055400c4500f46415038081202500342108169a1190343d4040440c101503142d00d0300d0312482c007030214880d810268500306021292041196140103103110240407580402c480b0544800414416102c004d460b15a03949009100d52004035600c1d114001c001c000d1240c240d000007040740e100321912500c90b0703640c6980a8407a5140703019288942c21400041c003043c2e00400007901c09240213070032110110f4010403103240801140042d91b0100b440441e02011441d424000e00303024240c190703201030a6080c40c040c15682c40031126401010700d929058103001d4104100140c03101c001d5450716050100340c440c20040d4840e0341e503020035188121032a00106000c08140c2c4443e103030194950fa1902c00b0030010b0070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 47813124 1250 47811874 47811887
    0x30f03020a0213060506070b101a030915010b09040c030b0406092f0703180b070303091b0305120d020d050109050403140c060112030c0606061812020603060409020607170307030b030105060a0303 85
    0x914801c927040c0a00c0455014032140f4031003207a50301c030004140d4a0030700d031858a15016a00381c00188072441c810062045c00003050a54031710f030f4030a0380c001c2811156150103501500c0c040c003003960014034080740002c003124503411214000013200c040189150380703100190119132100081c4038402c4000c100000003c0e2003800c3c0c1c044c850074424056030000d901c405003000b80d0ba05c001400e80c00603032039200290a1011581c002d098246000d10008511441c1d0364171151920081120ba00b24010301048802105059804403206811041803c000700e40e1100c49190040405a400345c002410207400e0b0711089505c0320071200a080120f0080c1201d03032030801d841c04126150b8008400708030180700484c0006403640103c001902c80d035120407018000300040c02c01c81a0303040c1c0c401c0e81d254010400140160b22031500304e81e008003080d08c000c10310090394000316982d8450035078000c7c024681217550840049801001c3e50048040381c0e0144450100310040600783c60080d145e45602600392102040064000c56 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 47814374 1250 47813124 47813131
    0x70f030c02031203090a02040608160504020a0302091525030503060d03110a060c02060603070f031b05030a0c090f060b030f0402031f05040212070806011e030f03020a0213060506070b 80
    0x1001c0390340c1c00b00d900c9203180c3c49800989680e42d032903205c259039804501e418082c01010f85506002411803291a11400b031108500d4420f00d0701459000451180251080c4c045440c41f401c00b0341101004042c0c0c4144400503403201d10081c4074090340b114600000072103403003100305082d0150f0b152070964544208100c50f40004180480a01601031582012044140a80308045010b4540002c0243d041200a8240f40b402050708d8400d4000240500c51080b40300c000c401540e0308100c40b045120403440381110640d966800255140c443c0d45108000c2000565565007070b91000704050014600b03940030101660aa401000e00703803142840041e484c00300000b10b495100740010110b03440070b50b8101604409000c514000f0880b903481d14100415410700d09030740c4d13030201c160130003d01d1440d14000f00b081d111541070103039081902c80c0048080e20107040b010031401850b00720010b10060020340c81d0103940e1725103a86080740503540000d0129003905840c458441101d00241c081450010140d03160801050003c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 47815624 1250 47814374 47814379
    0x80403030e101e060f050310240e0106031404020d0b04050705060d0b0f03030310060c0302120d0212090d02030a0e01050418060e180a12050c0607120c05070f030c02 72
    0x2c500ca500d0b100468011079081c9098070100d50f02420715a41c1c4502601c0880e0082d19030010300e84800c000c1620001a86182c2c00c580800014144882c80304150038000610300141a441d143d400c041a031643c06e01d101412511203407810442210361014500381c0040807980039600c500301808070b002003290b58440b80e034058800e00996085648a0000485d00d41004a200005540d0ba81e405ca00500780300c2d03005021a00308500850551800c0300c028a40541a80601c2c000c02c008403c0322410140204603000b200c1e50540306041d1901502d19804e8000c0d0071003202e0800d14501d2001081c03141401240e4040034000590107146013a0036840242c513500300b40a81c80d4100036040000040004400c26403121080700c0003c0812090718003445106803000241171170200701c3c840ca5a08a40311000149808429400300b03034015021500582a2041e01a658041d91240114030070000300e640e008441c030f40707400c580340000c1040c036101d45400c940790302176100024070703041c07920b18040c2c0482c2c010303504a641c03103200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 47816874 1250 47815624 47815633
    0x20a1401020d050403030b12011503080705070902030f1b031003030311070c081507050301080d081305010507020a0c150503150a030f06020403151109120106080d08090607030507080403030e 83
    0x100c0050b0402c0701e90484d02900004e54803164000280742c00394126541101c4940240b240c001c3c41004028024254800104221000034542c005c0140c140500720041c084100119204c0c6080c00100d404000c040b43c49000880c451305c2c00d500c460900005072801118460050070b441415541c00360018940c0c41000154001d0502c504c000180d01100e000f006050508050554188480503070501d00d40701a14080030300105000510064800141000c03201c0c0f11880c1810090301d4501c0507400340348119401a043e17500341805c00401c20780010302402c1d514403035148186010390303504030050b90341c581c8031403800066800c2021070a0341410700c0d43c80300c54007001030070886c40503901d5940b80101c03985007900312007003900402c0801c01e01c992201413002c1010100010702040380d2f04d500c1c0c0826813054008041c800e84d40d40d5010201c29000750702103800b070401001210000c5c80c04200292543e0741c00c41d00c40180344104030002e02054464040d01e40100542d1b211407041e034646a40990151600010381d0400744034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 47818124 1250 47816874 47816887
    0x212060f03190807050c0a0b070314090406080c010f020f0c040b120304031b140a0501200f0102040e0903070b010e1e0117150103020604050f030703060e030c07090c020a140102 77
    0x50b0b1000002c4010b02c41c40750a66980418600345092200e2050121710484940400f046030810200849808592605d01005441d4008154130394034080e0510b1b007034019103421808900d102d800240d499a489090b29071144200603140c2c206c2c0da61890500b0041e05070407070b1303070044014200354104103003484006012454606594480604d1a0402d50080e030352200c84207014480b24855030381550180202500d10034004401002042019140703100342810401e905501c0c00e5500c00703045081800402400c00d550f100380604495501079005406856552007640c001700c0d540c150000100c810255100000d0021a031a00c180c81440b464010030b000c8503600e46001d0890420944492076029003020031a8060700c0e081d02c030300700d868074008203083d414030346c07003800140003580d80d4a00351412540102d07120f110031141c0e00007280c1802d800703500080000c4c0c1400302c14030744900c010010780906230744e88044440c855a40d030302020543d017688020b03101580080320020b001c07844451002d810785210354005490540c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 47819374 1250 47818124 47818153
    0xf061b0a0203030a020717070531110301050a1d040f080d0f0510090203070207050f03030906030f04060e03070c050409020612090f0106081f0207030e0904060905010b040212060f03 79
    0x84c042140c0a0050300301401c107000350310100340358200c007030801401401c0080c00c20010801804064000468140d86284810300b40107074918468400c6581400074494203c0921500516800030301480c2e10403111900041040100d2a030640400240b1420701c0e4101e48a0381c844445000c030a2100f0744614208105000401c00d0601a41c1c1c601c0308110800501d83c50107104004803258a030f00200c80260041045c06101d607800074802e41540d104076841644007203000c00182c594825152019001040481003010303072184120b8451250f0700495017031110005030660140c0313900c151600104440b5218200b844a4200b50313004510b0984090b00071450002c0c108900d980e4250110703111021684050345500c0c208800307006101c0204030750001401d02c0128464442060300076103050112443d808610b4400f8948284003440c4d90341c90280500559050a081070703400b818107030000f6142036080011104241c00e0034400c5074009401007130304000300d4442c0020414000b040740901507251003026400e40405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 47820624 1250 47819374 47819377
    0x70501090c0f03060f0c0e01140d06170d0e030303070302030a060302090a05091c0903020904022806021204150e0d02040c02010b0109090b0d0206030c04090207080c0c0f061b0a020303 80
    0x4060409059500c2c40c5540b400800ba9441500312070034803420031050030841600002081002d00742420540309022030281200d56900030140f0002d50141803c0000031924031000a03242d44c07010307000c195007004003c2203050b2030409403648520b805920130400210384500c01e50140d0380110070780c10f01080d074039a82c2d00011107402046d281d6001c41591740091001c030030b000304101c42669200c0804078503d0046141c003d04455068840a8028803c0600190131940d0b440e2526035244d80b0300b061640e00351b206071013464000046008000161144481e25505203000600b40c0c0c0407114180b0382c0c0340c1141001f00d41210703590450076481e50043c94010002c2c00582d118085c02e03078010495800056525600800102508501d80c0400b10243c980107207000f25850301c00040b6402d98060f03400c1583c2b03807591940480180b14030b0b4040c8403003d1000c15400c0c10012400d000f00205d80c0440d04481b52030f031030b503020403040b1944100c10941c0503004001140c00061441354024031020a01c2c02da0305003c0c06900440d045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 47821874 1250 47820624 47820629
    0x30b0d030905100c08040603110c1c1101050103050304090f0b030105040506150607020a0302010302030903070f080703090e0f01180902030114010302040606020714010305100315050406110c030f070501090c 90
    0x205001490034000c50400d0400500f0021080c680096190101d8031074400d40e02ca1801703680308054943e0050300e03214100400701e4040034184012a100002401d603940c2c41540b10340440c1001405007640071034100014060740b8140e85d080b001961402c1c0c50502004000c02503400c114201540f07030300f004c3c64035030350a00c40c1620442c0035101070314261915120040341c000e955025540300d0001880028003684590a1000940340d082c00e006a5940b038520030145503025801c0010440381c0e0300a44001040061806041d4091080d158034100381d0302d41c400e0844419003100c4007149040700303400420910242402000c42c00800d4036000a0840709a008130303081d20aa034100b008021655001041141003074884c0400070005880038005c1a03003494829000494011000303410183c9850110703c110258015401c02180d0100507140e120307010200c0d031320140108403000d44e451440d010307040c188a50f50b00119015044200003075441c1c01000024403025400503202038a040d9610300c1e41000140040400b40d02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 47823124 1250 47821874 47821877
    0xb0f03010507120b0301020a08010b18090705070318050904020d080d0212041502070203070b180909010c030c0206060a030b0a0204050316140a0506190201090b1e0108070e0f07030b0d03 81
    0x46121402c1c0f1840b043c0c480b4080140e0085e07104021041a89503c20b822506684200b030402d0b40d907801e160810550006c00c54800c9134040d582d081800322580c1c10000401c90300d44030791290080501d503401c0e103030a02038031885030681102c1c0d0394000800501c0d0510018107000e20402400c1c0c1000040e62003101282c012141414411016409100c140500100c2012580c01c0c00c400030742c81c0a81c2035000ca621900e00744502d140445001c100050b45212015281541c6c00c0060048422880c02e50b003818080c2c603200c910b0b040443e1800a01c0c1010610219000c0d115000c0507205a091038656130340c0f28006d01c3c004190860b025400d02000c00d00355002d21031484482003402d019000b4a0400d41107814940300021814030540c0302c2002000503864140554015024107035114103a1079890b0300c01e0f400351641100040100a0100402120140740040e141800b82c280315510841e07a2100c2215540310070302c2c059030403403042c0c400008610038160303019294410981c4c41d010a642c00080c02140303200c01803980840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 47824374 1250 47823124 47823137
    0x9010c1e0312050108031b03040306090b01060806030f0706050d020c070609170715030f140708010f09050c1207090b04030515070c020d08090409170903060702150105040b0f03010507 80
    0x1414907501445002c007050003840d0400c515407600000b150b40e8400d800054044114880c660070700c2c1c082c240250f600454001c2810301c007080880c81c1074035084409006200103c1c4400d0040bc1c55801c0008510b0002d0011a00600409007451815900b5402250100604030b40804c200700f10100144240c0004008584038000d5403400c3c840c6a840d440300a46201040390320cc048100461000840340b41d40c0d5000303609001520920751208076014182508101d420903006200f400203551340020a2412924003a8000640c90b841d0b604a0f400c0c2d417400d8030845003090381800500c05051022a440350000400c0c28143c0295681e9070720368825421981c41501c05401c002c1a0086044c1e045e500c5641c0031015103013000a4800c507900268209919290150409502180250302a103565200d0103010307801084010b040011103180280f241d00440555000707007c0c003c085a079160000500a00480a030030303001d00079038201828400248203a49545501c04110582480b20b61000c0c412540038184950702c84 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 47825624 1250 47824374 47824433
    0xd02040320030c100804030e0409120914060738040303020310060c080a11010b0406080304050f010c02010c0b040f081804060b0f0a050f040f0605030a0c0305010308070201030209010c 80
    0x5400c0150303402e040c40c040c4840c421091a0300358080e005e075900070740c1803d01004801803070f008100100800d00004140c0743d0040400c0c40c00c00c1c0c00c4501d10040715050751140c2c10380c0055205000c228000d85000800e54110020782032000400d40900183d2100601640807100952081c0c1103120301080d64181c001c03035130000900c4807045004100303402905850030b0102007480240d8130080d85200c0e40c92584100440050401c40c41c040a402141114500070b01c1480041d8440c80c0c40c644a41c050b2283c0ba1161940b2001c101d0f40d07500614051268580584410511100646815010b6040144100c407400510481f85001078010000340c41c424030f04005c1c0c130250b001210188012503205401c0400380c02418041c80840e400c010088505443d01890041d0701c400d100d500c001d038540265081504440c2104d080410707056400000b442c0b00c3c048901c6c05214580c0640d005030110741081c040034041020410580700954025001000d900906151689004801e0707101d203020304208455a00001001c0140d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 47826874 1250 47825624 47825629
    0x4080d0b0406060e0409060e06010f090e010b090c0f0f0a050405030607030603150207020a0305060f040b13020a120206070204050901230f0a0e150a0213090e0705060d02040320 77
    0x300201628266420414030b420440003030200111202030a102e241c698925508001c810780000c425503030034001319086547c440c1850b003404940c07402003101c0c46241c10110290000305000303c003200400a001a50b40c0e8131006c8000e640d40c2d00050184410840c208038420794001840010000407886507034903500e5a003040105824080007404c610b01f0581021014008030b92340c0310085003041422800143d441500744081007151801380c0c0003274458001d860810420020382080540700382c1c0f1038070033540710343c1c3c1e0039500d00c010b04e21138000a908110289000d10224006e80822101540010a21407c0090310f81c002415a0000c0750203103466511041d080084400c102070b88500c641d40300040d880246001448000c04040080140450a03141d00d11482110710a120034138124429260001d00e601c0c1404a070000395118202c0740e040700340c404030002514034091141c81d00104403040500340c1035140404103d01a0005182118040d600700000170000d1484080e241d090300c1c980b0401e00008481008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 47828124 1250 47826874 47826881
    0x2001110d030606030c0216050f18010905180d050a032019080705070201051c0e060411100806090f06010302090a030501050108010c05030f070507030c0609060e160605040e18010504080d 81
    0x4009081d944050400000690303101f07001020390f00b00b90ba59502d80800040017822b0413200f8454005881030171400440c40c0e05560304200c5c03184041603106182e600015154a5854241c1c0608900144060240b020200d11a03004501d1119503091140c20002c2910085400769100c00a28041c0d15481d0f010580c41d40c1d0130207815036110040342411070902031581c00190140c41101c50304810624108603105800c01c40f680000900c0400e101200c0c00c516142c9008040080701880407880744a1280320032001900c50500d451094801070155803c81d242c100301500b82c2ca8010301140c0c18103800344905500c43d1a9074100d0343c0210301440001c5a207500d451919400c541d140307802c400070048200104a6901d9100c0251500210140340081d9129000e04003142c60801994005103424142000f8105115880e0015244113000000b905e003100074040c0607000d901060301c200c0001c44d03403d1104008245041c100158043c4202e000b03241400c14180340b8508603102100c00300c2d101f10700452219480d126610 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 47829374 1250 47828124 47828141
    0x170a0807030501051c05011803090905010e13080d0608100c0e030f0a0201050d06050d0c030201020c0904051b060408030a090e18070302060a1107150e0d2001110d03060603 75
    0x1000c2201d5414940491030220a01050b03140341700c1d81800f0401040001d5000401822246c1c2c4100c040081a18008000c40c01c0c0384070740c2c2c0d02141004004184400006101ea000d464510801c10742200c039540c400503183c005070081c020700d641d250740001d5040000e04c40409078048251000070062070b28603014101d0259144004d0081d40003412540d075400340055031941c2c0c0e540900308903403036012103e6003401070070340c5800c2184c010444408010402641e22403200c262803013602a21040c44820040c0b04140d00b04981c09403a540c450041c40c020117080703210721914007400ac2c1515182c19220841340d4030b95030100d8041e0002817070340c010400c490024505083c2d003000610a60341c0d0410b5914100039034a0b103c601010b445240000750101166000c3e00c15400c004482c0e500b5541c000340c0e9048403124000c03061030014080b640b00c0d186224a841c11028021100754012010000004400300301000071070750000712818800b0450203a1015541086210000540d070340e40450a2404c06400405581c05c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 47830624 1250 47829374 47829377
    0x9010507030e120304020904150f09021216140126040203070501170a0507030902040e100f06120609140303130c05040e0d14040b04080721030c1707170a0807 69
    0x4150002c00c603c500f40071250055011910f810300750311141440300c445601c00e0142800e042c54141c162500903055045078040d54021144230306040484c0d002c441d21403440040d41092000074060a1160140000303a04503103800c10b1401b07070000113401e110100c1c20001082e00f003648094003000c10085140411908000e850286000d09251104491441d0410070162403425070a85650018a80318032a40c0f2034030503141c00403c180040f5440c5000d140c2c58071302000b145100d490074060031079000301c03244c011181100c42400d6070501015082e2500170040800c400104d500d004003100c8000d81000400c00355000c2c03041003064014152540c40c24002c00034860784424019800c0a500341c40a2801050b0000b403c41141401c413042c00448070703425082e00c200e070040e01483e080401c012841072030001d83c40302a5203240c0ca500c80d45100030340105802e144114801400610340f40c1580c40090017488820040c880d00480036414001c480e5180100c2500100d00702042500209201c186030b80d000315501d41047d078030f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 47831874 1250 47830624 47830633
    0xf100e010f0204230102280c05010809030a050c03040905010f061101091a04020d080a050c010e03040f0b0f0c060106030209030c1002061612020c01150f0b09040b0f0909010507030e 79
    0x10b1450b00e1500c04d114a480d00c41c00c070308100207050716034000d001d910460b040d1001113080b070284e40688020b10540c0c07450160b540c00507a90010480b54001c456950003003001d00019402c00c00781400c100c80c1d139884946603281500061100046500d268000c0c140a405c015640c616480e05111000349010200305200c2c105038140448070010448000701002400802030038000a03036142d002150591012000040000000084100440354000702414001742c122000b80135035021024a143e0384c8c0194002d508200b61460300420021103810300406100e94500d00940c140b8a45d41e040c20304104003644140042600092210309519050140880c505801c98101080c88200319000b5a11600107101500c40a81c11480d400d40c50701030f4402a81c500c00e0200b0039503489007080082e9000c0e0045005450085070b42e8070020424035020303031052054640402070282006c80820030000a03115030300b441c60300981044101042601c42c05405072240304024001320700c07810030b403000a0440d02d0740003403110141c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 47833124 1250 47831874 47831879
    0xb040e13080304020423070503150d15020a12060f0603320612101a030307031e0c020316030b10030203070b030c0c0607080109050c090d12020f100e010f0204 69
    0x584190703508660141c80c0055004d10b070a0149112041e09109146c00e01042c000304010141e01030300440c0b040a035010742c0041c000030032061110320350800b04024a184440f40c1e4100b1444039681c05812100c031a46803800c6a6440b80c0009011036600340c0000c4071000c880762003404031a82501030b0101030b038001e2042c46182090080000d04c15050810194642e49680000c20703510f81e600702c00001c01003100300503500e0030402494080010510b0b007201d0701c0c0101340c44846061501d000300030b407440182c15842d0a03c954441914a00000d140a0100000d005102403000090f0700c04122010007001c0c61401d030780015003903040c4140c0d0440000c0003801c0d42a0180b80900041e00c000c1102e0013140c81d6500e03600c0d125125204100c04501812300560030070b1107240f0800031502e0740002142e04841d810007082069807a031030304480c0244240b0880940240d00b50f0117010000310007009200b00c0b0100d0f8030540d646000059641c40c10809580800340c212900d41c1d4a0000070030080c130501c2d01603106000114030303051 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 47834374 1250 47833124 47833133
    0x3020d0201080604020d020409050f0c07051509070f0303030c0905060a05040b0f04030501050f18010614061e04150e04020a020d0c0807050a150c030606120e070b03010b040e13 77
    0x84400000303040010a0000c254603842e1601600e1840421071003c0d07485a4980c0fa81c10001c041c120758110351150b080020070151408501110704254028018100300106408400008000034003c26054410b4910024041d5606100400594820369011440244010004015500d1508141e2040c0000c0203a050300580120407181260380b800d030310a4903000a10b04100050113164800740840d4203040400451101d017160360707845281105503d02d0b0101401c03440600325055409850001c1c0d0b00b0400354800ca00c2c000002c0d1034010038461a5681d131341c0d480207444000d03400650014404041d11550359014503000420030143c00400c5d1804c45c2020b490307a0f0002e641d09064001c00007070140d0315000c0c0090260701000c5030052030300401110f51001e01072800b9080290703c260342c0d00240340380c6040723544260321902441c004c44987e1342da514088890380e403105d4001c1044565030030251042040014125020402460003000440901c50710385240c0a200c0300010b100902c40c98404600700b00040028 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 47835624 1250 47834374 47834389
    0x20711010824060708070503040602060a02070c050405091009110a0603020316050a1e080105150c0601030605060d0606030b0106091502100b0a0806180d020d0e04050703150807030c06090302 83
    0x120b41d8500300e0500c0c0403886010901ca4400c030034010b00a1600010703002c007072000004c010000c0301ca050b400c0360361070ba5801c131414007203010350000241080c00381c40c070070032540c5851f0708100d80100320b07030301994644101c0111174021101c9110040340c100c0c401502425540c500782d90341100401490030154a0340c40c0560700071080040440c2d4400600c10089408000503205820264210004024481444945840240c1040400d1040c20310406100003484003041c4045e058690f4070307822400170a041d908540c0c0300c1003c2c0c100101803d0304200e0303101c0380d00040b0700c00380200001580200440105941803070001001c01d031942d04000c0036000c1103e103180010760f00151884d90010b84000009641d10383e0000101c26200c2a4031a0260344194014400804000c015402503005000c00304c580120087c80266102d031680203560b00840c06169419000d81000d400c1103500900914000461541d4a552240703000f030305801900c00c1d41e001c0710040c010400600000c03030141c41e1a0074100708581c916400103810307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 47836874 1250 47835624 47835661
    0x1e040f0c020613030c0c0801020c190f0f020f030109030306080d050405031b06040b190f080108030d09020307050306040f0506090a0c030609110a090b010201060f0b07080c070503060a0207110108 85
    0x24480d10703c2e5440140342c49a0a1500318543c407104d8682c03020b654044a178041c0d0480000a03100d03000f182c042007052080200102c03a00c581c1300000300500f0f49140c0b41c201c20300c6a100c070706070713040740640c5844200360f03800307102e440ca550740f1a842c001078141c286404146032603d01c50100c1c081c0901000188065a40004c400d00b58160050036180e8429001000c0352450103264410940c12501003500b000120f005c0401404140555031803000c500034003141250030074402e201d00139290300100220996444070390407201050380040c0c110b500140d41e039004640381080c2200c00b5550210074282c1d00c010440244a01500f00d69000d0050031428042e8079441d01d440e0342c0348401003056648295030010020400d40c000490308005000c090303050b9503004040c010700001d81900d4015440c0040126425084028101c107a640e8003103001d044c04156036a60010758010800110244251040041d841d0303000c00541d817061542c8031f00581c46400c549020080d10901d442d18505102c070b41c0c001c001140520016a004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 47838124 1250 47836874 47836891
    0x60305070e041406070815010f050a0302130305060406051801050618060f031f0c02010501210201050f0307120c020105060907080a090c081507020318090a0b1e040f0c0206 75
    0x1102d8907980707011000308285407603003541c0340900e60400041680141080380701d036031004014110f0141c8080111002c1c40b80c02c21820202d0f1051048140c510f210303170302600002c0003070034444580c1c030707103e80f143d91815400312000c4603566200c03010081004030034210b2086401d180b0009102d86c1c1050000a103098141d070010b601051201c1e000180c880c1c3e02d850481080c840090107951901403024444880c90507a84007602c10305080101189003d0b10500c80d0504841c14000c2442c011101c1e14180c8041000f080d03c1030381000814448640400d50000045001e01c046440d8001105c08004c0140281c90110711500d05591400c0100103241d1200701c0420303404040c03440c003002c003030b80c0c2c04008400400d00450041d0410305802c0e001f02c0d512500048440c140c50141c4c108945581d41d09200b243c0d28072441501c000301840c080025107d034207101e880f0310341000e41003030082080100d031804580140142084018014140c02c445c090300d051901c61241c580d002543c1c00d101d20013110402964038500030f8076000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 47839374 1250 47838124 47838149
    0x3030a02100218100306090e030909010311031501060801050301060902030f0f060619020f07050d0c03060e0309150901110607050702091003020409030c0c0b0a0903080d0f0e010c0e0406030507 84
    0x5011900c0141003500c80b55000f482d480800203810340045c0108100d015102d6001e19002e03c0188000002082d038915210041030402103a080d07603903502514003610309480d0940300b0301541c41440d41002c4806400703403410340e48501c45503251108040c2510240d5115001141c41003042c00740094008040b26800800884510650385034000030480c5846004003d40328400324400800c4203550101300407003d000d00710225003404d9101d40c01c010b6052102c80b0010041007000c1420400240b05811000c200341c921000e50f4103000c1140e0105250365002030b0400c48d90107001405107400d40e001250f1401d03401000006101ca0b1400490280591084a41c007078070a00b0b4000000354504031400c25040074590161042c840428186030150500841d41000c8400403a80080410359030800f2040d02d40c1aa003a0740d42c4030a0f14510f86031000680c3c04130203d100d0203a283c1c1400c2506c0007890081c003164120700c034000118001006001421080551006031069080030b908202061001604005a503042d0742c648 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 47840624 1250 47839374 47839387
    0x5030408030609060f040f02040e062e030b1008011e0506040501030e0c13020c0d020a0209070f1808070f1e0306050717090601050114030402010206040b070c050304150e03030a021002 80
    0x145c2425802c1e190254010704003040b007485032485070080c1040f1003810034001e00d03549842042060900b44101a05540e1829001c101e894010901c10300386091018107001996940d1040800ca0500d000e0700c3c100046590f290040100340108206120720030490549101c265040c680041d156118030301c2418100750300c9000603451020b087c40fa508502c2d00040c446071019125403079401c083d4118007403010785401900800030940d07001040034910307180d00800c030030034039914844256488103000c441c1008000311019003041d80011142050081d11104004104003407030009200d0b413101781500102540c00030345103003d4803540c040c51481c2c2500d9000c080800e003a0780303402040350748010f0f0b6984400c919002100740a51140c0201e4614181d0b40700b0390b910341a11a4000c0c40d8a114801540d0083c0140d000d400001e012031404201d15400c440f080c42c0c2007806404940310f8a2841e04180c20031052001c42040c4400c4460b0804604c24018009402650074680c4902001e500ea08040b6080da25154001511 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 47841730 1106 47840624 47840629
    0x20f010212030103020105030c070803040302010b03010501060903052a06030c09040f0b01050712090506070b0603011508070902090409060c1d12030d0f02070804060c0c060503040803060906 83
    0x282c5075901e560b00464035503000030048141210144644000218000011070040340207a001044c650030100425085402c1a4410801e01640450400c000784001c10049214100880000c4483d0b401c0da5941c101c1e43c02119030aa40024004100401e0540c0440680000441540c00700043d40c0140c4e000421140e91441c054080340e414010400003400d00c84070546880c0c21440c0a500c0070750b0354808250303503812000048035020303884000c01000b401c0912850160b028884c004c0d040c0c1710300d81060644c94044600611a0b403640002e044007064641d03400403002244c2c0081c08004800d86c480000b00fa070103808038100c00002207004c103101c01e49444080d0792214420400554540078003401d07104001d1410a8680600c65000d101490101c0c440c3c1010380b000b403015840d030070000001440c14405426041e008041440010b10034000070480807400c3d039600c0142580c075101141c481e0f100 = true := by decide +kernel

theorem cover : BRFrame.Cov 47661874 47841730 := by
  have h0 := BRFrame.cov_init 47661874
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47661874 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 47661874 ≤ n) (h2 : n < 47841730) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
