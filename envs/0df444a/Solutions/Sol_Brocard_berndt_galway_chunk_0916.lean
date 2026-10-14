-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0916
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:55:53.387146+00:00
-- url     : https://prove2.me/submissions/f7e84f66-372c-449a-bc2e-a0765a2a7073

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 164568345 ≤ n < 164748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 164569595 1250 164568345 164568403
    0x30605060306060c010f0f0207110907051207170103060618090c06030e1006030503121803180102030715061401050702090703150f0e04030f0302030f060907050c060f010503 76
    0x507a5080740b422a2100d685640440c440d80c014000601100b02c078a043c491591081d2166030301400c1d1142c010800036080d034142c00100001c02c00c040321260081403090042401c00c100108049600980a017800c1918040d42c420903c13002c03c0990003242d5040e103640050249183c9012081d039600300101d0f050050700815a650300c104a160b000d4081099030300c1204401a1404000b240c80c880c008403000c04ca080c2c0c80b4200f650301e070381c8504c102540d1000150041000204c01c0301460300080c442c40c0155050040003000c04248810007019541103120510a003000b0078403c4444c03420208211000107221454800c040203002c0082600c9414000113100c42005030b16201005544400306280000700c03070a8407001166990001e410020180c60f450402240940d41c0d0308806001d00d00a8480c05001d1296140c210140d11048410f10300d100e5140011452a081c07169105030083d8040c00c082d41003041e503c42d81c0745800c504a5422245400310310040040741001d0000c4101c00c426400350f20348400c02448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 164570845 1250 164569595 164569597
    0x6040209011505041211011103040f050904080702090a0f0e030f03010317040b0c0109020a0b04050d121b060506090604090b0f0a02040e0408030a050a0204060905010305130605010b041503060506 85
    0x40380300c400308a048401011140b040d4111400b51034210072001e045c0341070b8108680150409074515001c1503007580c0c4003c2d040303000401d50342204c101c00e101440e031504140902814400250040300c9214080c0108001a620020628850a07a0400004000f26044000d03016030f4080d40c500041ea40040195004c00d820034406c99056030740000f402d1b02000788001c003201032032045074001003120230b010030503140100d011f4000341181c9000b102e054030840e848420340f030a24415489441c1d404101502d110b000511340581030014840a802d14020802006210500b0030324602000c40c8c0c0b2580d0b482c20440146400d8088a81240701039130704001d209840c1d510440c03c0031016081d43c3c08165071500080801c89550100d0700941080350000381e03182460300c0c0024040e0010703520b103e02d181c00c03e00084c3d9410441e1003a1404c40340641e1320142c0b41840d0800640050038040c100c0c008100d220119100495070500a41c1d0003883c01036225980e492603c40709000d420501d40f105030400d8180b5504000710754401c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 164572095 1250 164570845 164570849
    0x10501140703081e070908010b0402091e03010908030a0f11031003031407020a0e0a05070c05070510030e010501060507150c020706050c010e0607020607020c0603041e050a1a180604020901 82
    0x400c08804a4440091980780045207013002c0d40390100c10707010030461550181c4010704132044103000740a0403440c0f008201c1a0300401038001d401050040c20281004c40300d0b400c9044462000d000081c00c8904e030340300e240081d44202c0340307910640d03102d030090035007081c0c540304034050000c4a000d0b1500b14105072004480310482444050100a4a1942880c00c2629101292400c5900414516119070b5500746069526800c03919401058904000503d1044c05569400f40c016440406010301d04d0403e070801070754200103200501050398920f521035440b4800d1280b17078040c02440d100c0356200e014a10f0000715864403000c5181e1280c1c10001c020100130b8000030140181e95140c24655190485012107900500c2c082c0c00000603403065105000081d80c010031031601031050ba03401d82e41c2411183d000e00c030300e51009540081050b064007602303040d80550302405611441c8150180ca404500b02d403280032004404028279403e11880c0400e0144e070148041080b0161507210f4040e01280c07425800188000c0014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 164573345 1250 164572095 164572097
    0x903120501080c15270a0b0a0201051b03070c0b27010b0301060f030b041101110109031805030f03190302070f0305040905010e090c040c09170c19150c020d0605010617010501140703 79
    0xf85c0c442c1a2136036601178450007400340c0440d0070780c4501c101e941c0240030f040161007400d0000c001c80c5008983c1c0c0002d40c101c1c1d1017103000b43c846c0703507071544280d40c4e84c5055600280f40303948554156003440036050700c1c8442c5402901c2143e00206000b0400703001c2600b140c010b81d000c4101a00740031010000503010b1550a6842031300822540141031200d001a2500103070200d21131070315440c00a19008042c2c010008041511460200810740f9850700181b640c0c5590303031500e100c0d20760300512841c0007601c01d0006080200c840c034540941840c04541d507881a44100390700c118003040c80428180724400b85882258010502c10300c01610f03c1c1800700450791039081081e161402103482e03d01ea030b01c0720790140d0718081c004c20241c00c2c103800b60118000328507114403015400364814101400300320306560f481007000094072003c081c015250405884195240300f8988002c0780c100003072003040008240c1c1445118001c2802c1d456400021950340c2c1c00080825050308014144030100c580134110074041d00a075030768a641 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 164574595 1250 164573345 164573407
    0x5010c020310020c0111040b03040b010b0f1e0408030703090806090307030903030f0e101d1002070e040f0803070c0302010f0e120906120901020702030d11060601030903120501080c15 80
    0x6412900d015105414680810500020b1f00040606002e80114400c9004810b98601a41c840d01ca0400c81c1c420030070480c02002052180c4041e0b00703407042c20026070615811115161a81d5540218215002000143c1c003096010004002504040c40317500c0d0312a071481c024501e40599590003520015041c0005004c018480714003500d400c1c05444035a9501d0780080030b0164442c4e460a0050224101c00701c0402c9c0da0f600c2c030754141c400303041043c20001402c4564016040c400d0401d00e414100e071741c00500544001c5003c00ca40f802081e000c400a5000d0304171551500d021b9041d82c10064203442e00b21a4960b4118a03000b0800811880840c1d008014030f4080d00c07850ba2102d8620001e441030052400080d44060820280034100b0015401032010500c00d0702a1620b42c81b01c1e0405544a03601c61031426419008000000c4241d84285d0002c0c1c501b512a0405040c40601c603443d10301102c1d02600140980d5000c244561740e0303850807070300460070702d000d00d10003d00c1d0031618000d0f82040403440c80c18903003040f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 164575845 1250 164574595 164574607
    0x2030a0f051c0e150402061e0d180b09061603020c01060905010f1e0f03060b0d0b041101081f3b01050901060903020f1e03030a0201050a0605010c02031002 68
    0x1108a04440d04141560151900301d6000d55003000102020032004401d481412440132400807a034140520460700280070509000c80040280050051015403d283c002e0802c04200c1d00b6143d0301c035041c40c1c684d0048180d640300300549000d05201c100a050400568040c5040003980c6100c0080740c00590340d186409030f115244520502e02410031500504441c0d42000e0011400c001c4205860044403421030220240020381d01342c04210b81a540202d9103420414a010b00118059030444404640f001c2c1590703003442d03c10b80382c0c1c4985100941c7c0842d003d080d000d44000c00c82da8000d81494000314554000002a41d50014054060700c5611600c0161502080c6001c0820701800d41c5854161408203001c0c99140c01d0000c0311700c2c01400f4010301d44540f01c001e00102704c0034420b98214040c1e95001d4040b00182e0b000d102000342c0031030701060711909151915034a0249440c144058035041400c1d800104850400c9100c0d03034166000750708010b0400410000400151f500060b013203004030a100c00040e80e8007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 164577095 1250 164575845 164575847
    0xc1203040504110c011a0105070303180f030201140f010518040611040e10060504030c0e040606050333090309100e060316030f060b090f0d02030114240102030a0f 71
    0x400340707500095200789040c115041070b8550500030b0544039003a400802c040c15284e0044681c0c0001b0300000c0d0700091081c4a10340c000713070081e4850b01490603a82000300340e9807590355a910244a160000f100140d441d00300303007441658846045034000b1020740886000750304190120317010601d502011701d000c94511020900303115080e0303c5520407101010000c2c0d034a580312030f808280003070141d40013040c082c0300c5500041d20504c654103440c140e80d809407846030b20f40c1c905810494150800b6205035201c0f5a82d40001620741e03810000150714810b176000786040c119485942030381d40b000900c00c0403104d50b15402040100e110200403140c0c92401128000130b280c10800342229802c1556075030703580201d000424040010071a4000105060340c50742c082c00409a019510000e46032107114058140d0011701a04ca4285041c1c0c0b060341940001821081000c0d00030340000f803e4801010741d124042c0c0c0041c0c24000c40c2105100905240e4803001060010f68000400003540c903c10400c140b000c0240607942c0030642 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 164578345 1250 164577095 164577097
    0x203100b190914011d060f060c0105150a080109020904020607031209110406060f020d03020a020a020415030b090a030e013f05100b0403060e0102040f0311010207090902030c1203 78
    0x2403101c10005010300d525516910010072100d1420001c20751001c00025151400280b140041049184040103648030101800601040c07154280c0c0d11003803d004810004d0024230a00b44a000302207516100c1d5010942401030012490b0003a00f81e0303905000404000d61102c084080d0810342c191481c1d0381d680c1e1203085c02c0310f81e036083c030005200c024101440c00084c40400b0741110080e1034101d4003000826903c410685883d0a0f41141c40056089101c0d0004a140a680a0718410045006030340012400703600050807030354200c0180d106803000707580610520014850403070348825074030010700b9240010744014150801c00c0040c6810841d804441c82104980c03080c031350301d55607811f60411020295180c0309070001d0b0705807105204154508400108041840300b004021100380e001c0c50303850281113450b010302801040b0004c1039903640801c00050410390311031401000703502132405181c000d0711910009050441036408200c5c00c60030400d400c0c026035408222000d204c103044030a0340c07041070180ea6180c25 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 164579595 1250 164578345 164578369
    0x20d0f0e012f070308190c02031b01031d03041401170a090501110712030f1104030f320f010c09090203070903050f0c030106050910060f090801060609031209030203100b 74
    0x818060300000204012021010301804000c1ea070181c6500c0a5280c41100d01f644802c0e4040d5040d800f8010313202d0340d00424005084881e1040c1340204070f007000310030901c2d00340c6281010b080e50f035400000d0030030624050843c0550701e04400d2a02c5904584105407490702b03240082c2414030155568808801000002d41c00b040c0d9480804100c10344480f00b500745220740b00c03040c01e48000841d040c480e40005128072445031064400c04480514141415503c030002140311001d81168070b440e4036a028150001c80386102c1e1ba108103032100f100b01d500c001803861400c0c0f5040b030003601c0c52a8109407400c500990040074813001c0e0707680e0000040e229a5654011981e0069a500180c454010000310700a502d00200704014020410b600902400c0d0b0380354184007803640112602152024201e40c140f0145100e14034042c2401094508813601c0c0340c07940e10075800c5440b00d900c8100440d100ca03000f00200241901002d120108506081d0465072454003c641c03500039040d040d01045a440c105501c1a075204164540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 164580845 1250 164579595 164579687
    0x1d0901140103030302070201170c040911070212210c0703110f1503010f0608130206160816030905091308030c0d050a05150d0c2102060a020d0f0e01 65
    0x100d196581c0c100076000b1340c0251801c0c2d00081c0440d0420119a01c0321960310301500321281090300d494034140d14440281b0242800c40d0b04080700300580400341e80e0b44a203203941c00c10700c0006081180c03580c0403a94854001544450010381c028031482c0c480304c0010540400300c0342c020a00080e013040d4000040c82c0900c45404ae282d000c48000071034a0200c0d40040914181c0301d05102d070704036940c1c80b9101503d06c000200c4001e111080c61105080040c20440040c3c00f03540308041c01414820745a03039074520b0300d0308590301d5025003400ca42e400c201810313840703c00c0000030141501d205c03010b0705282c82150042c484011002c1c05503e070001c007142898007460200e90911100d58403c00075418034000c00000ba210964014000d11801c8004400d5072070905011100d007a840f032190300400e8900f5881207150390303418030035120f100c0008490101680f1144000c01c00d0109660281480f076050f1100600b9140405c6901c500300640c031500400583d8100c208c0c030541c0110560080b021909406804c1440030560002d08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 164582095 1250 164580845 164580881
    0xb040305070c180b01020708030711150c030301090b100c0203061b0c010e03040305010f0b091b25020102250308030907080d08092103070302090d080301080717071d0901 74
    0x65100045071300c01262a0000d901b580d00c9685d44280725a41c0780034a08000e4101200564080345a141901010141760315504100741059410b4007031a00b580c000740d0040c11480e8582d480a28607190000072410144803508141c9803021260300403e5640c6402085108503180c02400404520080d509a50484da2030000a0000c0d00c0310008030b03a207035002131208440c2582001359100c1d4400309401aa1101000944481d82c0b070f1703440c91078140702e154800700e002c2c41c40d81c010804400f075607400712001c0348800000c001406160b0380f40d00c002443e00100380b081c0176220008429030030420f0680f8544104803600540c0d0140c91b03890303a2071154200b4250754424140c0323105288444a60759001515903100c0c510340000d8604a5100d03120406640c5483c10700d5001060081000030b90142c026400780c418003d000c0c002c0c4107018815901c0c0f024541c402e0b0000a910303403248008000030381031826a10312140c4900301804607645420320010042c0440070039903003030050841c0040d1801c0800d51004d4a0f1000e0500c000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 164583345 1250 164582095 164582129
    0xf04141b040e010203150607030c05030f032203020c0103150b040f1703040302011b030e28061b0b0405150406020a03050114030d26010305010b1c0b040305070c 70
    0x145080c1100420a1401141807040d40b00034680c0602c00d5a00c00e2000f00403208101400c0002c0015a0340070000440500c19a1f529440114400304094402d100c100070945503641042d00311040840c0b00d040040481c0c0414880c03007070010346d01103103102a20100307083c0482c0c00f240204135990180841e4115000e50080442c0c0000c41e032051500e41c0701261440095202c20058034501503460348118000a8040b07207080d00708121900400090007480d030b001b413900481c140d100c3c00010342c00318543c0c8144040005144001520715001050b00c1004141504000c030b54010100104000e50758110310141c0a1040c010001e000e100080c40001c1e4005980d240d080c0c0180340626000d0001e4000846910000f0701c0d01c0004540d46400c12192503401d407000b001000102520b170030440c1e81d040c0b0103044480ca5221580d0407500f204030062054003a52040001003105000c110602c40181c42184100302040901d03a40e4a011a5401041c0c941054040c030746950361300d4460414807003040b0154007020704000c2d08415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 164584595 1250 164583345 164583373
    0x10c0207050108151c290103020918060a1b020123060f060a02060406060506040e0412020f0109060b0301050f01051f020118030e090901020414090a0608011506030b0303070b0f0414 79
    0x61403011720702c500c0e4008015071021404c01d824a0b99100c0402040c03085034014000352400100940d0b010008a8608100c55902a01c140c2410401e980c1400c1d06901d9140c254085408403080b06d0741079003148020071148011801c410000303000f100e6410207030741c440c0c4040384039500c0d00c50180c0f0004c2c9025004542c0d80c8004035000b03544d01400ca60540d02c451400c840418a880c01700119003c8a580829085242c2c840e600d41c030b40342c1a01051031034290b101d5404008170f44c8a00b80624586140114400550b64000e2800d15080d143c004200e080c2c1d403000000144020340c0c0b90b0492064a9140500310030014000d0710040e80100744150500541c40700c0b0440d43e03010580d000303c0035000c511080d107240d10781d07803140103069007030f40228000c88294981100d03040c0403504002e104580c0c0a0303071345640454095600c60720740742143c508078442d014a031a50403083c0034441d00741c0581400314100764010742c50410940c85400c0c8155002c0c01c00e5500e0503c003004a000c3c441000d0420f5074030308940c2e09442440309a810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 164585845 1250 164584595 164584639
    0x2a030a0c050d0203070213020d060503100213050a0305191a0c090f190603091506080304061124060402190e0f0307120f1b06030506010e03010c020705010815 69
    0xc4031240310b0701402c140d1061011003a00c028941c090a9256603076440a0360710040d4010f680900c0c5202d0f526440000c06903801c20820b2417900e6a44e42c0169100d02e40d0100903107603034158003d00c0c02500c0c03240d4100001800018900040039051400c2c000d14840b5142c0654200c1800710360103104290102448440040340700201201081112061207110101007070018510a00540500407007250004100306030080d004a24601d11551074a8200d546c1c98105a003118155084011b196102181c01e000b03e58002d00015007405003180104250401c48013172124a4035404401e10703032081c15801180c03c0c1c0d22680c0546000101548034900083d54450000340060a4400154411403040c551803440381070116070300040c1c4040c066004e4910b1015120a1007070701039a01d00303d03013981c0b080310082d03c20040c0e9081200980340035680030903a801d142d000108900e20010310907100e6450101030481d607940000c0c405045442c2828901c203e41e5601c0d0584a62601220b04aa0001c03111142034401e244111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 164587095 1250 164585845 164585867
    0x140603012c07051c14010905180307050607080105150d0b041122091e090203030c030a1d0427050304080a0309030c0b070b01060c0615080307030914062a030a 69
    0x815908141d0383c0300200c01c0aa54104a0b1217145100900040c000110b10780c000c0d580c031050a45a01e1560010081220b15540c0301c100183c3d03c91b04100140402c01d980680080d004020407503c3c8111400c14031107140d00c6111303554031286210781c1c401da10355007030301c482e001900c202d43c10320003158540d000314070103241c00340440700c450300c0c000960207003c61154018881d10039441c032001100c040b441034040d064401002000303c01d0b82d15100900c084a50324108000400c219240f40e0b90300b00780d0310f07044030184500002c180c0a0510950900c00e10f00701d440c00d0707000b0340d8120312040120605404680e0810f0750452103284c1040b9114090b80c0e10000c2030540195802048910074003564190711390310007200389140100c400c01050101994010030100d40b1689400000c0350090000042000b020604515040c155030b220240c0d9410101d00383c4c0a054000341004000c00c585003019101c07121010000d030840c410102c9046002490f55206000601c0122800115200b19812a03130740349001f50700540348071440c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 164588345 1250 164587095 164587117
    0x1507020d082805060d0605010315050717060f01091a1b0c030705060319090b091006081207240e1b030705010806040e0106030605070207140603012c0705 67
    0x41c0850a860707408032001900e900c0000340d058009001c10759940c0906006411310791300c800304114510114904c0e01c5200d000754460036801041e4110030007010240e0344000c01d02024024602c82c001460510000015400308048600082444200f001600c240185400c40d0501001c01818080180000d0307000b400707560f6212441e0081440c000c400c0b10342e82c0801c50702c05078040d000300c00c00300b003641031510165401580300540e503c55022110306000c111035080c0b4040c0d6a038a0202c0078405448400c0c042c01c0b250450240c0248001e03414182c040342d482200109450401000160013001c0c080c001d041040389008141c130441500080c500d060000e010b90391030300d072610f0040000c540c0c3e0300c030740c0005004291100500034084451502006648507000140266001904c41c03192500085080c81414040c41c03140b840042e082c01d20b60402071518031950400d0b01046840c0c03440d0461a0364883c243e034111440804025001180030301e01000d0341c440c4191358030402041038140480903401c080a02105014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 164589595 1250 164588345 164588357
    0x150e030903010b0f130507360506030609191404140705010c1203050a1b120b0d1109040f0f0507051302030c1b070f030602030402040b01091a0c1507020d 67
    0xc036070400100300fa03c80b295951007450030000074917411898000c2d40e481842401c00481010095003141d030414140c44506c2d00178101c1a08070980341d0701c0c52480a0241005035082d904625092011035200ca10191001d0300212243c1c012040010651f00580d40c9034007440120742850916250408500c201840f101d05140140719001c1a00c0d480751100300c00ca036401c5010031684040015042d00104000b9020814160b22050704040003015042d402070000c070300c0c4c0c2d0b4081080c605405030108032018941201d20410208542c4030105180d1011844800b408446407112b5803601d00e403558560b05895001050b49807403040f040c0900801040c01c2040320000d0f140b003038004680c0741580d030032840115640b82d10359509101e59502c00086001f02070701100014121151242c40741003010440d07045604c110f5030107400100300000c50030700d4000c5a0002c0420300300140c000c1d08200c40c0e49180d0707000e4100c01e10400c00119403c664075030200040603514183c15a0812541440440252160f008160326000300e42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 164590845 1250 164589595 164589611
    0x70c05090405060a05060a050d0506060a081b090c0904060b19020a1a0403120509010c090e07020a0201050d0f020d020705060601020d02030d09080903120903070602010203010f030f150e03090301 85
    0xd000030141e1041d5030010281103240e03140040000103000c0504429002100810003040b81d031503181c103040030140141c00900c40340c0340000c1040840ea055400c2405582c0003013060a4114009a0b09002c50344811500118140e9400000708030f1070088203542030340541482c40014480348940f0080041003288102060f036254108802d99484d104140014907100101000b09020754050000315003103442460108000d55944a6072802c2c2c0d031094030f11900c265075440030b00c508142c1280c0014010401c103407422a0902e00800d01a4541c3c04088000e4148000021514240703422603103d42101815581d003151241c000c840008000d401c00b900c100c50500c02d01000c03d8056000260402c100c2d9900e0340158508464001128003500c0d4620080314048014000700c0107565040c00f6444103c1030101000d41c54580340c2e8101403070030081741c1c440c0f0196441000140442c90201900005507600b2180050b8440c520349020b62521880c00e071b6100000d464481185d5518401000074442c048084009100140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 164592095 1250 164590845 164590849
    0x204031b09150308030601020307050d0207051206010803120c0d0c021e1504020103111201030b0f010f0b0d1d0312010503070b09030616020c0d12090b0304020f0f0a0f0b070c05 77
    0xa08258007115400064650820000c0c0c04c50009690100301841540d0401c0f606641d030030705d011514100f0a015030000181807100e8204001c8440080049400914055250000a030340740d203c1e0314002003103046041c0c0044c0c4680c01e52030032594000d0303642c80c0c1004114004940252920b040d0807c02c1c684405c44019016408000a28501c8031081c4072001c142d90344071940150010300c0e1941d4000300385402070100e90600400c043d0154029170044020014501c0c001d44071003548030058100c07184419107e90240302d85c0c000e4400396882c481008000188030111403003a503074007072030b1003ca4000c2c601c0006424002d90079403012150403142c1c1541103401032a100c0c102ca4201e402400e032a59099841080080c07a4100d90600302c903071564060045d51000f0301080d01003000e085040e081914288a800800114188e0007100c95006041c0c4035030480c00e60034207a000842800340095039a120b000110031141680c2c1e21050780e40020524039103050401c0380d1300d904c410550780040c00107035051403032080000741034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 164593345 1250 164592095 164592101
    0x90d020a0e09031c090803061003110705070312030606080c03060a0f06030c02101b0e0d0204050f07080f060a05060711090106030f14130b07031b0c02030105060d080a0e01120204031b09 81
    0x3583c0415914156548e62052000708400300ca16a02055140c40300c0c0e041052400000744902c0e402071018050003070035400c0400002004410100825107004010050706910412450b00a640c00c000181c3e65140e007070005952404c00d82018000c3da100850004e0b03c42e070168030180188a0f0754081d6644070310079041c06412038812a402c3e0456849051040910780c0c45400508002c071002008494000c1c1d0a4010500b00d800480b000481d4401000034403c4494100d0713819607202d8241100300e4158608680030584030100361083c50700569007c500c1000b080301d0000681040380024210131241d40e5500c6004020f01110260800918540300c40d48040041d80442144540e40005016148183c075540c0d030010700100508040402d6070b10441c010402c40e5005075041c0300221541d450703408000b41d004040c211403020704007a10525202d40c01000184106041d520701c0105401d11240c854490001a900e0034400d19004600360710010300401040694140180742003a40c19103120032a4a8089640c11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 164594595 1250 164593345 164593361
    0x319080a0c1d130c0327151a0d030203040f090b09060d0503120f0105040b01020309030c0f0a031e060510140d080405040f0e0f0d05090d020a0e09031c 66
    0x82c80303400c2e1107820600c0d104410484142d0107800341c0709000100040d00d08030350941401d40d00181e198148000c40440036600d41401005d800d5183c40e00d000310b56505418981c04d14402c1d428261581500c5440300c2c60343c683c0380c44c6d108000c1c2286a5240c402d02d00252aa8058081c1102e0240301c10004240d83c8010f22030108000740c082e0886000b81c50740002c002c281100c64104940300c4c4002c100305c001c0c2c00c10234980180541042e030281c080950510381044103507041a41d015045520510000c1850b65000401c91240c032016a401040002005e01080d1010340343d80003d030421300390804041e03503204102c03100000c1a024038003c0140b03032581c01c18100e0311070003031240c00001c0a100000140714a484c09080501c5481030466510b0103030307910049015501c6808520b9200c80ea03c040507440c0d5107040c042110805034210140214480d5082c004d001070241c050703001e0003110040700e1001152a88107094015040c91002e8910a207040041c80e07645e6880703002d0349007498055201408511406013301c1203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 164595845 1250 164594595 164594597
    0x11042304061811130e030a0309030210180b0603071203080906070906020a030323090109020f04020a14130b07050a110a030b0412140f070506011418090a050319080a0c 73
    0x40da000141d004c100051241607007441e043c55907250501601d080400c000c20202c90b00340c0300490f03000007606002e820442184a000142818124424589000f130300d02c603d4807980c01504880c894441d480801d2801c0d2854100e4844052082c04a8051541100b084c521440c0b0b04001c50b1300c2036403281d8089400c1c507028464000903070301240604001030b01030f40084c1040002c200707104040c0c0203d920b0201038503074140c801904903503541c0c040c002542040402030310001c500b40c0d425450081e042c0402800100340c60a803294107980401e085000142007200400204a42000725458141c5800c0198507202078100440f01d038410343c88009001d0412845c1030f801c03a88c11203440384c21a9520303101d5141c2c40002031080c40070001110688070714900c5140241c101040c0100600c1c0c0c840741946402860710506800c00000c4400404a0340c42e0303640d805110302e05c0c800e51040c0c2c140c0f03144c640126551030010030001c010410300020074441c50034090a0384101c3c407031480e40d41c1c0601039110030000710f04613854a1043c81c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 164597095 1250 164595845 164595863
    0x10f0321020c09040f050a1a09160501121104030305120115020d030203040302160305010f0c1b060e07230414090c0f15040b0c0106060504080a110423040618 69
    0x143d160120000d640301c2e00803411030445188550f5214100000d0000c2200d0032000404414100e454144000c0c0c0d1240344000101410301112408110914280c0300f402e0400038460911004421280c002c4004411014605903c1c1d41e00c91401400c581c21012050114a1a072030001071009810400c000110085401910f03c01814a41c203d010b948010010b4041d441854043c08022070002c0380c01000f180034100000d607001400c00d00d4020364000501110402c0000a40c84400035503d00fa20b001131544a000050b4004851076a1420903040380d002403508501001d4000c0302021071840c41100820403101040b40341289541c0324042c0380140e8400e41070340c4c421000000142004030000910004c011f105c55100e1f14070b801c001e03d031076029801042814801040740c00584509000da100a031000d81842400d2906200e0310f15911340c04034901610000720810201402d450710340c8080741f07005104a00a940c81b03188103203038401c00700c25142211164900388100d0b8822440d02001d04403264400925 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 164598345 1250 164597095 164597113
    0xd05040f090b0a030b040317090d050921060103060e010b06160b07030209030d02010e010c0207050105190309020604032105090f040b060c0712120906090501030207110603010f032102 80
    0x6a40140380b100c0246030018402180880400c0000780c0c400d02c40c0d8400e13170303030130708002504034922002d558040d04000803980b01e24090030354583c00c030007510565030b400e9071220048080c030013483c200003c81603c0880c00340142c0c0300100c140003046d0004d0001c003044400078009141c01206100300c81c400c440400ca80358641c92080300000d414200200e400640034500503060030130000010341010101c410300c1016039501c40000641d040c003800780401e071600300d00250420743c0c40c2c240041d00300d1041c00e101750404070280ca00c40306e2050080d8003c0c0c044540250405889507140c0c81c0015014900200c004401c4071144c041c001c08502c01c0081715400000604010400c561202c180b0014285a2060716449071044c8010702c4100410001200140f4058484103a00c0c5001c0c148800d00c030700741d0707440002080440c1c00e0610405821400c11401c54a080c40c0050752251a414030180d00441c80c0030981d88894000000100c810301941c1d03400c1502d020302c4d034260444600e16000304034100c4038958400560807481c48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 164599595 1250 164598345 164598359
    0x112060b01021f02130e0705160615060c1a0c090d0c050405090604150507051209100515100203090904021504090207051506101d0a030c0e06030d05040f 67
    0x8084950042c0110740720060b00c5202848940f49841500b0641980420300c4d141c040c0a0010f100000c0480741540714050a003824000d126100b107441181c005ca50036400602080550750155403a60b84290444a00c10b44821000f4044030007914140c03101c40350240d00480c10303100045840e000d80a80320025203080403600602c140308060711001d54000901100001c0c0356122402120301c91143e020280400349010b00c0c05107031048501740283c2a41d40340408004205030000c0c212441c9810500544207259550761041d40340480b12138104400c2424402802014990689801b02d0040219200200764070703000710072681d80c091042c1c07050744407881d1300100340941401844400140c041320070365441d250b103c142010590303201d00c8048403035078004094403013019000448030340c0000c0d04035500ca60382196031000508140c0200c03030842c0740b402d59100c041415a80e030300d111b6000310f034000041d09a40d551510346064012003140c080e80079014500d40e207030881d17200e0401c0354162a144045d2841d16820421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 164600845 1250 164599595 164599601
    0x81c110c03010f060f0815040b04060209180609090c0a17070302120703050610180b030c0a030605090715021b010210020d05060f090106020a021e0d03020f010c0206011206 75
    0x140105802090303040ea4881d1020700031810125601a80450b08070301d4461800c140c0300c1150320941c4242c2181c51041550310054000c20703001500100007038016100c17410301000901c00d110800d0781c00000d400c103420907c1881290144200011142058255180258140c4036940d1006c04ca512010054003803001522803a80740341801002c40c01ca48110380c4aa002c1090010342d81c4c62540c69a10100041080010030030945030b0200020800c1e4000317515140c2c4a00c040e60380f03d082c0030354580d210395998401d910200b1a12040d0400180840340207981c90074000002c01c1c064400400ca8012100042484c1e040d110000c03100b1456540281000001010700480d100c008800d1300c2d0460080d07a01c40090120180080c02c80001d48400010303c1d801c0000400074400300b174400c1940603014190040240c95000b048000300c244d015103810080b0541241a1010500140b0344540e00c9440c1c82c4601c03041c141d00180c016010f6220310020031042580790026a40c801d000d201340324880001c601140c0000c2d607560 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 164602095 1250 164600845 164600867
    0x204020705010e150a06060e13051e1006031404020a0e070c020a09050702060702070f09020d0f0e03030405102706091a0601020d031a1210050103060c0801081c 70
    0x70000007603007403107441400e0410000000b0300d034580300b81d0403d000d00542680304107002420a41054141d40c0825400301e01040745181c0014241592003001407110740c0d1107400f4141c0351051404d6a401c41ca405040f102d100521400b80b04000707441d10880c11a0b0066280d141802950001c048907410341c81c0c42084151100d00170981000c01206090040042c1c82c0d04c80140050b10041201045510305010024034148004000b10115440b078141005030020016109040e0707200604050703980d04004c5c01d0348016041a24551700107901d00300307500d140381c01e02102850007030f0301c11b10030340d030620036406120b0080d00c00440358120102c07091122007100007806085946200d00c2210041084241c5454001e2a41224480c1103c041c0750348080200300d60781400418a10344050604011034011506083d001052005805d0302400c032180030504c80c64000c10589661450a4509100310341c2c6038a0008040d2104054400102d09100c0011440e200c0c04034070040d40c405503080d0490024882e41c1c04480c3c6074880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 164603345 1250 164602095 164602103
    0x20c1b150a090b03070504090b01080708180109020d080c01050c12070509010309140705010207050102030406090b0a020a020d0602090f061204030c11100804050d0203040e0c0f12071701050405011202040207 90
    0x10718000141600f0400c0034500c24501d44e2a610b84491419440f83e05541c5103801941c1003110f824100543c2e160004c100c40e400180f505545240c145100d0a07a900406a44401a5118005000c10740400c20800c0c02001c1c43c880b05402406030b03450300a103c0302e0b14054045200c1000701c0341c0e000200294441c00c0900341e5a40145804201c1804640390a00b8404044050240319049480280040e503010032035000148020700c02949014030b42040102403001c14000e0b110301000c0010f00d19a80c901c2000b540c420941c0051240400c0c0c4090b00c0c02000035801250141d00944441c145101280303400002c4d1a04030740104001c0c0b040d41d6070f51b94100c807038501c0013100300c0d0086110455401141c8602d00725440b98811500d0b1100c860030701b8100705161840715858138045510400c41032054542c0004910f402407140d20080380c80384d03840c091201d814002c1014280302d50000000b0000384650010400546100011354205241d0b01c0340c040c401510824054402c54001c3c4240b0310300142400c0d07004104032401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 164604595 1250 164603345 164603357
    0x1401020702060f0702091b0a03110717030a0b01030b01080703050a06030605090307031418060319020a031b1103041a0f0d05040b1509040b0414070306020c1b150a 71
    0x4a60000d00d00703401281100f0001000800c540c0d0442c20407503096a0070184107180410f80c1135450b0207107036040c401c10540a042603100e000764403c000e036583c140e91015920441c40e080c000184840e0300c1c00ca40045400b4000f680c28a4490302c8503500a00c940789201750b045c3e544a50940d122a000d078080e1030054003aa80c0c03581e6803040000400c0c02481900e0003884550301442e5a49914100144001000680c2c9106500204078a080e5440c00d807459002c001d0058442545036030f0344400900080e250444079054803400050400441c69060b4446000843d202c01050300107981c0680855681642c4a054080317a4800c10007030051902000c116081c94401c000c90320f03c0c1041d0207109040980080c001803042e1a00c1e10148000c0012801006038068500640080c241c041c08001902114001c0c0014203007010b60000303e001e00401405e05090308044404985c4015a42d2422034000d6204010305126030084c40c43c0c12200522106541c403d80034003c00111103584000020311644c0c1c400c2400c00300b8410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 164605845 1250 164604595 164604607
    0x1207170103031b06060b0a02100509070e0c070b041110180608090f0f010f1410051903050d0c12050a05040b0d0207050a14070603020702030624062b050106020a140102 73
    0xb03070040c840641b00c1030070540c0e1a40040d03c0d020f864480d00c0d200540300c0074101000c00a180f64000f4541d41150485c61036003400340c03543c46e1060f815104080001d02901c8403d010801442902480e0b0a051202646c0d160100440e0520480314100c0d0803000d001043c1d84101c1c10000d43c1d00c100d45440e046400c007000d0362004020f0100c89880c00510030441200c1ea5140d685002c00c4040611a0149003021420510030505c1c0218038a40340050341d002c0d451041010865800204804551352005507902204960500404003005444000017000807101d0703d101050441c1000d01c11400d41d044201151241c9050500b49060b00e15243c1010a50108040e4240100400300b1020007442002c0c07030041280618908814900c1414008903810840c24140104a0540185c9001036841e030f128100f003001044510790303c5440349584c114000402d510240c00300c0d01d458042e8040c80e0a450003509070b4184004010780000c0441034480c00d209100150b04581e0301c0d0790224060701031400341802c060b000189004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 164607095 1250 164605845 164605853
    0x10c03081914010e10051003050705130e15100c1410111c0c0806040b04060312050a020106150804080a0e0405100504050a06030803010515120c1207170103031b 70
    0x19501e0b141c10440e0098580100803240d503c0f03266603004049005100700da41d003007001256a0706800305007041016502c200040c0403c0c410001e5a00c03c1c00d0760034503801090350301e00c55a903082c08150703038011041c00c0d03101c25081d1a1406008280c25001581c0327441b030603112680c4904a40d003e140e84030320002d0169030000d41801085110300840020092480c0340c13541210035030301c112080c100c141758041c50320300840c9041854204010541c48241100d021943d0501d140202e400b030941980024920540382c0020440f05410002030803a82d00700b40d008000c1c2664a403041284008040107501c00f150120b404180400c0d141c500500b215269030500146109170b840c080b604640c01100c5000718049400740c184064036007400b03990703005542a101400542d0070b40d11014818401031080e0b610918900b03040c049464541800d840c05800344041400d641d16240c02c40d1415540f10312420034480c43c0000008802038018000115071803032240c04036100d40c0c07c40c0c3e0251003201d200d402e070128040d41510544001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 164608345 1250 164607095 164607101
    0x3150e070c0f0b0702070305150403050306060c100608010b0f1c02060f070c06081008030c100e0f03030a06140102030301140d0c0302030a060903090609080a0b040206040b041203120209010c030819 86
    0xd155550003010000c7c50340c2001e90505a8402c0c0c0010800c00c4a420310000c650300000782c039007289007152011b41d100400d81d45d991600074488a030322881405c0c1900015042d40642c88901903440c1584e2820030b00326000208900b600d08901d00e1002161012183e6001d0705051003c1c045202d008100d441c94861252102d0062540540c0218000349548080003000b801250111009040400066040440c00100e50b5100d40c0341100420f0321a50b12010580c81b50010400880380302c0c408004d07240d0341d061480051001e440c29000c0e1a404074000c0460310b00551000003124101d03800d9010007441c40616404110b075000b4848000d91b45408180d10104c0540d8082c44640b0f4003034443c1c040003c041c4039514003d411411154015824000e9520003044000000b00f071030944140d11020b80030700c582e20351002602c0d600980d000b002c042003000c500840e01560120207100500c2c041d8071907000705004141034409a00c681441280010001c8526000003405040c1980e002548e00c8800c0081e030030403104020817 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 164609595 1250 164608345 164608351
    0x20708040b032802190e03240603190b0a050a0906020c0a11040b0a0501050705070b0c070806010b041410030b06030901020d0b0a0308190903080409020301050103150e070c0f0b 77
    0xf640d400300c0d00ea00700181440080c0484448410010342c20100e41540c00351103181216442c2044c4404481d013101c4a0b40e007440211504071100c0c0700070403286c40030003078600c0010085509a009100e07002000d01250054800070702415071000300341030281c5d51645142d000d00380107000d03402000c1e2241d151034002001400a00720300174003032001307041e032035a10305181000c405440440360003185447d00300c0480d622000c3c1100c06941c803e0900d00c1e5a041c007450140e240c2141c5900040d000c0c400800c1c09130803a00301252500c01c645128003100d520ba602c0d07441c8400395100c0c41c480c0740d480e8080711068001c1410720880c0d4461440c1541800100d0700c4a55000c50225841125015107507540040e00d00c0303010f191031003038041481040d00c403101028215903640c0c43c3c9105690f0364034501e000106074011003a100c2c407010f03000756910003400b17034840d59990380e1540a9042802038502190070904a00b8080c410302000030101c0c1c1c1034510144941e01c1d02d88090707801d03880000082d0350a10300c940d0400d000c903181c20b5007180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 164610845 1250 164609595 164609611
    0xf0601060807031410150e040624050a0e150904090602250f03030203060d0503040603050709050609010c030302181206070201050612030405010e0a03140105010503060a090312020708040b03 83
    0x48902c1c0c2190014101c88141442c05400040903092100d00e401a01085017554008200603888112600301900c420312030740101c590003400d01c0c41c04200c440030880d401c03248400c00081030300850388030041511103005005100000452004d04d9030014581144c0c0e421012040c1002c10349002d0760880481c096940c1140c05480301c503000114a000610103084403254042c290f282400304038519911070041d0060241c010b01010740110208903250f8070f0700105220b460303006007101d5403169155005030203001e00715188000700f20740003030000300c0d41005001c80300c4043e2f05945076070b4100d106680950080d0003101042d0280341203580d41c203015803940548048801e81440042c0302c98a00b0b00c00003401e407280105540c1c0504aa8a03e0f00d000000010555050f1082400d00b00c00c642011f0340400c03c45a1300394000307001000410b40312015500194000c0d41a5402071301a500b403030b92486985030658640081c010005200e039500d404801c00c40303078050101144201013181c6050703541c40445d2401c1d041031b07031000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 164612095 1250 164610845 164610857
    0x903031d130e0d090603020a0509090a060807030f1214070b07090504180b06101d030120210c04090b040605030a0c0602070906050a09050402010e1c0b010b031006050a020f060106 78
    0x444407a00481084e00419240c41d00b5403a104c0f0300310001300b045c010a40070350f02401441d0b022518200700b0307030070520240850380100d5280035500d00340355400c01da0317000c41070740d202c01050368001c3d04a110b14203e190940c0e0324600d003440c01d0515a20030741c0008000342280d080000d120400314107650f0348d00421182041c036003148860210581844c0d51161409000184551030055a0821a0380c01502400305150071320f25440c002481c00000c2405040141c038001d0801640003601c4005640e810702030300d5013480b01469000e2426480c141d241c030300303042621a0171074000c0500c01000440100d0b0030040c1002c5015102140059840340031034584007420100710744030948008184582941040080c0c0105908a020720a407458440442d41c0714625019410311691100005419640a07000e107180700c001c06041c490f580590340c1c02941413241e04e1501125140f040324000141111600d094a001d03082c0203000d444030707901d031000603a2190f210110240550060075440308c1c9000b01072001500800c503a0702c42c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 164613345 1250 164612095 164612113
    0x3020a02120c13150b1602040c0302040e070309111c0b01060302121006051801050912061006050c060703090317090c01080903070b04110f0901120605070903031d130e 73
    0x801640700f041c1000ca2149000e6500c0703021044441540c044940082c0220707617800d90407085112074500c915002c0e4105080281c20100541c0c50f034010710440d68006200c800f940c840c031800b05d095504400e80500702c0910901841061700c3d2440408000c210b141181d085651520791322103e10b101c0c02d0740103d01007580464240d00700141d0319452640202311f81000040c5c54280f540c0030f0170324040e2110794900001c0c040c07088101a4040c00880c1e8192400030800008501001c024583e00c0a0031540e00c00d51000c04080020810300803011303541074406240251945e80c1d2010021030041c404188290200709152003a8041c044046140c00d004016a002520341241044005400c00030081c0015444d035108200c44000f00340b1014016801a0744000c0122610805500003262001c0004040d40c2c0448084000503241c03001c3c254450307000c0d208540a000691b41c0c00400d90720b5058521014006c2031440c13084c80c82e1200c0209020103422070007040c200c907140704140d140049900801d2440345a500c80010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 164614595 1250 164613345 164613349
    0x90109170a1106011a07030e090a060510030c09031407050d060c02010b100c1b050301020a17251b0c06020f0f01051506030a0207060207080a03060504020f090d03020a02120c 76
    0x4803610b49414001021194548a884109003416001c0d204d80100c010a18100b0140303e0000402c00c0d50000b001307040e290400c501c003000141400d1181921641441e4481c0514a001c8d0103007400c0c0382a5a228a40b50f540340d49c80e0f012222035815442d034885d005d001e80110b152382c0e6802460b1141030040c8400504880c1c0000080d0845450710801d07882100008035201c841940303c1030104900383d210354001000b1017550000c2000c0102034101c2c5074194000714000d00701e80c0c0d00a12256841507601030882c0035484401c40b014003d52108401d403010300703000c89914040c90050140c00c3d01c024190b01c1056a03250291960080e40700640c0143c00140c01600500c208040d041094000406030440200b1190030613400f8200100280201c01e806904080009154486c103581916076103600151f056540f101c95103000c2d101648402542c0d00070174641440419641082e200b6203414404c0190a40d1804d181c2e08200711030340c803600300c0840840c411016200c1c01621284010521441e0807001020b0480001c41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 164615845 1250 164614595 164614607
    0x60c0201120b0604030f11042a092115090302030405091b03010b0301080105062209020609030709061502070806010918061514010806100810030611030103060c0c0b0a0203090109170a 80
    0xf4003248101e041050301c0c0144040c08010003070035910307208009d07280f150307075281954400c040394003004074034690103501c80007071202c0c01c800c584451240c003040b50100c107811030100031101c045402400582c018003003401582001030710150007095829510b640301e8800e42a070216617009030001003a142010004110901c030034056035420101c116244036004c00314429000030702504d47d440030074454039102c0c8107065483d24000c0303078514100901030711078054558910780050710580c810a4681115150001c14851010983c00d007618002d5000e03002030303403034110345001a01c00f00701e0fa56010324804681034006100d51245540080c0c500300d030558424a0108481c07180344444041a05000000081140550f1000050701215005d81422101070300c2d01000b594030988240c2008000b645010f009050010002d40610704913841514180000c064610040b240210286001800b40c000040801c282031304035000b035544006100000150355146072541c0280e0505c45840703101c01030002840c50412a8040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 164617095 1250 164615845 164615873
    0x180109080604030c080f0c1006171911060f0c0703020901090b06070209070203070c06021f2a02010b10030f1a130504030309020d1103070f060c0201120b0604030f 71
    0x14140c1c520701034402410b0408030600081c01035100003801c180d054000030664031308032070402c110362546000310207440050403140594861520252044455a1000189219101c0e901410840d0162a50b5a0032001e100c02142d419401032007408182c203600403040240c0034901c51b00c40200b24040c6075006002d43d40f14181c008440c142e04002021031305813240000c4600c0d10343e05541a10300f959540348124214007661900034070f40c6419040002e1103c0c3d001a402c44040c00d840300c044845a84d2440340d008031941c019122860800b151120383c003004103c9070a06440080d800046017074184040054078040c0744196800200350f40d9a000c0982c09011705ca008078400c3c3c100c2c034441360b03030042e10001203959900c40400c0c00007036100c0001408140c4260408148075602800f0300d1410710381840c0c9000e41d01d410fa01c1960091150707580000b2600051402d1b0800c9079015110403c8248403600112000e2460040c5180ea45448103001b07001a1515002000251b0003025800019005403400c1c510b080300b28 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 164618345 1250 164617095 164617109
    0x20a120813050319110a1208040905060418030e01170a0e060c0f070807080c0102040b03040201080901060f050d0201050c0f030403120f140306241804050c030624180109 74
    0x8503003080c81380d120003607a40840e82003100035542c90740c02030016070140300302d41043c0d072650040410b03102089142da0161069a100f04000c0c0101d9840009000448483c9016002030000c4550b821000c24020305280ca0508010301d0720038490491029040d6a050b001e544c400b6200c0c2d80c4185a0355842403e1001d290041c0c4007005040c40e15101c05000c1d0f000b4060690050b0a03080001082820002a0300c1111300016201e0001c0d501d8640c2c1301d0424000790412030f4140d000ca142140001d2101506102d2441510000e911040242e4109014002d190003044412414802c0800c44113009600800072004000b1400008581d5a0305520b4541c002c01d00d444200c006010307215107940481d45d040510884500041412a604c0c0d80d03400001030900b001080c624844410382c0c6440d000ba44100400400300c9821400352004d40180079420300044500480b400640000b007803012480d07910b460480001c002d8008414a41403038906522404983c0c400c181003085400e10703618414003942c014032020002c01035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 164619595 1250 164618345 164618353
    0x160c170c030601030320190b06010503040f121412070e01110c06030709090c0c02010305061203030f04020402071a16110316240617010204081009020a1208130503 71
    0x2204011030b0780c8460600008041c0f00b1220b08102c194141190342808040700d0304d085854000070000503003600c4008080a0b02c01c140074000082255004070226401558000c100d00714884890321a000c05082910942d01001200c40c846644040ba40b0081c0c06071800b041034880180c241010042c044001004050f41482800d0170101c01c1120045100c542102044d581a542c1eaa107048003110022195003144240919006c1821007103a401420503102c10300c02e0b00c0070022612030508025000c5000780c0705100d254400c100290751509d10f01d408503089440a0720146c14a0081e66420f01ea0550342c050100c404174011080181c04050000204803140b400e0914810001590204a4a031303c84c601d07040c0b40b0540d02c1c1a811040240030340e034840119403100c0d1030007904104800031b2405000035200381407258021440102500e0410720840b4100c40c0c12000503c00c002d007800d0010003808541740c081e40c1c840c1c11200c00148140344100d503121090b10641a180e55190940e00140e120501508028001c1e40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 164620845 1250 164619595 164619613
    0x204170f0a21020a080d020d05090316061107020d050307050c0405010f0e040f1e030909060806061c150203060909011506050d021902010221100306050c160c17 70
    0xb014010040c407010090308020100400400c0503458203020340c60040100000188070301c42e013809a4007402c0081e2040c036061011b5110381408550384d0184c405804140b601a0f41c10782c0000c0c86a0740724008140140d210f460900c00c0ba030b00004c0e80011307140800c0d00c0b246c200058080411100b031090340c1c81d5400c115000c110650504100c2c1c0710100c8180943d86071805000302140034000c2c0303100c083e00069072125846a45641e285030356120b402003801e0440c0440c8a030300011540240c07500560003610b61003002000d06680c0c0b04100011101c8188550702420307031440403080030070342c120200200c0e01c0c001030001d6982c0c10500280240e2040007403983c10b03d03925250003640c0c920101c0e020700c004c5890354034100d5200e048140c0544028410740b41c400c00034410100c500860b40750190003130714010101c004500c0b00b04903494942e038006e6808880d03c00c88051030700400e000250700340e13112039040071705083c040c0e0920703803840810100c1c0c458181d4240c0306d0303606841040041326484261000c0c00094840070300030307540c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 164622095 1250 164620845 164620853
    0x11811090d0201020c0d0507172406060d020c0133090506010e0306010f060f0f0e011b39061d030c1f0801120320030d0204170f0a 57
    0x3000345500584109581900d0070190380c4204201c441400740104404034802c500c0c900319580346898495100d070074800e0540c03520f0288020400710400d4840e0400c01d65950181c0c410005901c000914080c0d21074000d000017107140c0c5440c4040d146401d00c0d2400010760041c860004400580040c0e08044461502405450404140039031031046504426010a041c0c64180042c0c650094080c512501441000000143e00328150464000c90b605034072000c000c10419803003100c8400700807102c03001041c00d0007500c4030b030365100f103c2c1111803807001040c801410802d81d0707a509280d4440d04030041c84032848140c0206412607400301c00c040b07007107086000481c0b51034000d02500e050300801c103105c007619846001ca41d00e0380302441010351509004210801400300101000304010055809400041308a400403030500c01012142400c29095152581c641c40e03403c41c400600d007040306030f40040b13000620001003840214005040903102040b100e540c6805411401c03480c10150035031041c0302d0b1344000000303404a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 164623345 1250 164622095 164622097
    0x11203020309040902120102070b01170f0714130c39020402030406110301061d04050c030109050a0f06080d0e0307061403090f030706020a030b0f0102060a15150305011811 75
    0x18207000d83d00402c80c821240000350040c00707243c003400a25400000c2c3c010402100d400e16074180c0c0c0318400500c00c0d40d980300d1011550790750040f5601402d03134030491040c01703403000003d9520402c0c10010850b09809925070780c0c04047c0c81050f1103180104510b44076130000f418902232407844000c8000c481640300311101045200201d020700020740a03d40c0000428107004054000680c40803401105643d01d59680300000d0200160190072010300210903504809490709026480c00742c00300c100941d0443e42481d98800c0246005052600720569810b220300f03000b640d40c090345009001e0b50700038000340118054050440340100c0c0346144a5048032030244076198000d24101e01d441602d002503903c0340d0350f2904041c602003102c1c00c1c40701035220100d020360420003260010f0000c81c9055400307100110441040c000c81c01800c0d100280980c2100002072881030b030070360115248420b2180440f4019507500b071070704100414030311843c000a440d400144040003e0420800c0d4502d00304004000c0800b40e4110422a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 164624595 1250 164623345 164623357
    0x6270302060105150c0a080301050a0803090603010e0a09050715030609110313020a09090c14010c1a0a230f010510020c1507151b020c030705150f0d140112030203 71
    0x1180083c20b000c841c4c038030624000d40740c89400f010210307004818241051040c0d034000b403085034031843c4107840104041c000802603c107404d5019041e5403d60342003400c8101b01a0f402402800103a540b940c02901103101000701200520b840c0448284098000000806960460b00100c0034070307051600c8035007418141001c40e580b0207029584040c00804510004140003095031100001c941019414000e020860005070100e031345884110a142c110f000044d1080940441f01510846208100203604412a451654014201480020560405502c0d02200241803082240c0310072000100b12580310b4213418680984021640010812115000250f03500c02c130001c4103008171090300070441105000c005441e4126484000f800c0307614070107070740c0354028070940d111000701d160f1a00c00d600800b40041040b01e0700074005000f6044546c206014803080a03000542280705400811502500960310f1010300b4100d5041c103000300e030142c0c440d2802d060b00081070300b100d223801003840d00060000e50000100e50b2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 164625845 1250 164624595 164624599
    0xb041a0f060705070308070f1a0106021603020918030c0307060506040635070512010e010c05040f17070e040507060207051903060e07050310020904110705070e04081606270302060105 80
    0x213647c80039480d200341c0c502003230f400040013424207107503c00c80419124a0036046c0d66a0368211a010b401c1c000b6003504403a420b210280d0070441400c00309a15001a0002c00d401401003812646071120075010186180d0200341d09513402c580d14014040d80e03140c94082c0314001c00e00366444090b2418541911001c29041d01d40c400c080300e4840083c0b44030140e00340003000050100400c64100341d0031503c0000d02900c484214050f140d403800c1200030034a0300070820340c1c058505062001d50300702e00342002d1501c0300f00701c982c054035036116440c1c00050103a0b105090b1881580b1aa015000c010b01c0c00001914054090300140d1151f00552562030146251040c0c2c6002c032a000480480c1c035415428016040c400c030f540040f90140079510901e910810250010000c0e03c2065500300b10301d400f182c40b01281d90182400040a0ba04100b20400000b0740d0001216041401022801e1a1501c0d402c41d50014008078141261410386842780ca000004144018044032030b900c41340144483d003d036800940760101402024 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 164627095 1250 164625845 164625847
    0x22a0d110c0609010c05210304050607030c0e060f12012c0c03060616171902030903070e04080d0501180b030c100f090302040203010b0c06090f0319030b041a0f060705070308 76
    0xa046c03140410544003440031603440d220400c0380c040c62143c025841202d0a403014843c05003c58071030751180c0b0903d003020400b80e9402102800c004100072007503001141d0a0001c400c240081c07103010300510750b060b00802030540c040c000031618410040404112010880e8424030342030030400e078a4620b81c02c1700c0e480740044940e039030b489040441c0f034a1840591580505042030b02408282d2501c0e060303006060845848444481801003894104d942e4401e04982c55059000040d08000558000d260290410b2040620504000380b404d0b140c404c40d8002d034013217002840804250ac2c002001446030328521320342a0050403041e401d0801080b8944052592582042603a0087c041c0042c072500b80c9030302840d80100b081d07507a941e40307000c1c1e5003540e04120b4143e070705400354a0108039103000c005481480448500083d6061214441107031002c0c003c1c3c01548e905140d22000da18407d9a074606c50881000e00f2031403540500c4e0705100900640c0480404500c0c0191b4041000301e02051001a0200480781c0c40b100306 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 164628345 1250 164627095 164627117
    0xb0a050304060f1d0f0f0a15020f07060b0a0e040b0411062101030b07020304080a1419030c0302010c180315021902151006050d022a0d110c060901 64
    0x8440200780c4a621048400d140c07084038091211042015130040c3c00100c1100c49211103903180c0c5840341c614201d6010350780e10440180c0001047c49090b0a00a16003110040c144121400580840e90000e03408039a101c1d0365107104010741c0782120001c03019052a1f054240b00703107031694418617035010140c005040303065a000b45200c296241030496030400702c0807d444400400309031a41007038010a01088440506400010341302034400029941120b040c1c50007010501465120342c101083d141c4264501805070300e07074900264401c0e003c0081d200d84aa40c60440e140c509040081c2183d80d504030101c100944040d00700152140140010141c0345c100c04001c1c0080012070b101c000034030070b86445221002911524104081e0003090f00f810181038446100051b65618400000d002054051040405da00b442520314645180d405031800400c8201100740f003101d02468800710317089000b01c0d440e00d5031040344142066a8400003c8480d01b0001009101701e40701000010054001c03d904541088294184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 164629595 1250 164628345 164628353
    0xf0903070906090207200f10021c11060604050610120b1806010f030b1305060d0b011e0605040503100504020d15060e060612041b0803040b041e0b0a050304 68
    0x4240000c0501c048204900c541d982d10290180d004000141d52030340003555419001d120030f40211004a20042a1400d281c140c10100000420919005021407282c96a40c07200400c41250401c103040f442c3d165071403100082c600052a0840c000c00040c040d50401c0c040c0152a100d510301004d10039040d08091120400c081a110000c1039540745031076001423034003003020440e07a240715442d00807982030703903280c40c2100b080c1e5064099801c480d189981007040c0c080400104a442d5102c250010b40040c03000070700d130015440300003070000281c0024140801c5e600c5000640f480500400e8002c014900b4964102450880017a032a01c540c2005009065200d00000d811542d07140000d09240f0b82c420b40591103800c507a69041d0003003031140540352020f40d4880c041205460240181d03400d00f51103400f0b040d05503585a076a15000000c0948410321101ca000e004140d00c0d1040c40030700041c1c01c0303011000ba01c803844c0c91071104609412042e0464094030720041804190a100221204e210850512503036984461070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 164630845 1250 164629595 164629603
    0x60f0c0c0105160906020712020d0804080d0e030d0c030212030601020f030a08010e100b0a0e1302070501200f04090b06040e010b0726160602040806130b09060c0f0903 73
    0xc0c260350394030780001c20010030505012100b00b000e4039a9050f101e9a200c44082e40d4845c0d041c00303503c4050441c440e1820062500035400110030342b1522129003415620546149002e02800100b0042010380d030100400d414200001c2c2d5103000180b07805c42c0d2405003500c000c0d4070340e04004192070408800000103201a4003c00c211040f1540310811a80e80701c1ca8024001c042440c04e00408450702e10310f41c003107862000d01a0514050360390303440f94103203008d920800960314403c0000700160003913144400c0900c9841c44e840034141d91f600640011807581021030104c05002681c6148510240b000d0144c5496200907038155070945209000c0003600c0d40101d00019014000c0381d000c45060615030001040801e004005441d07440d10860006068091004002d108040f0182000c22612014810100d010556200111582d03005540040c540b45d1921070f402e0408200715400c3c2c410400b442c1c1c040e030401c0070455001e640001e18001800240c20440d19904c4207204100c0c60500181010500200958041c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 164632095 1250 164630845 164630857
    0xa05030411090c03010e090303041101050705070e10080c1009061407060501091e060b03070c080403080705071a0304050a0b040302100606090503160e0a0e0a060c020102030a0501120203060f0c 84
    0x410100907407400f403800e11050341c800d000306905001d110000c65100700b000401e42c0c1c003496010342d050410703144450046030b841d00480820764281c03003070300030000b16580071101c500d02810030341c80140105420420070350310342001c07412268003030301c03c3ca4880a00c030340d40300c9002015501c0c20318000400a5511129190501601c1c42c0540a6440c10b0000180a4110b030720007244100b02481d1046940c8101c40040201c031418070030071001e9041000050101e9108401c140c003418811700340141055144e848540858100c0e2070304460950050b0300a110403081c0403125054008401202c9255282581d80d9980b107030b100d040000c2c4980e03448408501094002c0c884040880040702041100b02c0c4c5e80e4400400070400d91040500900400a502e5142241c07a007841081d99008104c03145152520180240100028542d00c0100d0140801c80700c0004c07030500440034002416400581c4900b002c20188045640690140c1c0801e07940b0b07005100140c50104143d40c0c400003030400441c0ea81e5540c070210320240300341 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 164633345 1250 164632095 164632099
    0x106050307031a37060b0a08040b190e03040311091006050717190809010606020601050f0f1203090906040203040b040f05011d0f070e10031e08161a0c0a05030411 71
    0x140d07000340c43c44d0030204c566084140c1da410148405507680c00c504030188200f140010003e5000000540440c94021030543c00031011003045c2c80861410044008680e0903d0300001c00381c01c002010006d21019004aa650f0541142c5c0c0010500380140041d40f000326074400d44040c8032002c50464140720352715401c580074a60f0261015a2103001c0501103030300a00303480c1680d01141c0f41d0401b240030310105100c1d65041c0c0302560010440c507401c1c074040111a88580c840580e0058110038008810b07210784e00f15640da41401c2000795122541c08081000740480244a0380c0114814030070480840c0100c00c01c90f42041d00300d004041c2c030311400c0c10f22901404148003e01004d111040b01c0b618490780c0080d4004445d11104203071060b480d15a450784140740b400783c40540400e84d059100b440868055080b0182d610100c81341021250703101d07030314103006400c02c00f2442c84009404120f541400102c0164041745084440c001510f40b03041700b11207060707000307000c074034001c1150202c000740c00c000408403c80b07007580c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 164634595 1250 164633345 164633401
    0x612031c06030206040b0c060106050c0a0b0c1303120801050d08160f0501060b12060607020f01140d0f0e010c0c0203060c0d06050402070f030f0903030e060304080d0e01060501020106050307031a 85
    0x1e48406c1c45451307102440c0541c452040d400000b840c14031800648112408200c05055654010388680191801c064480602c98900b0003c4403140040c0190366002144201440140b1040c030550140259005074801400788460108140004a03010202d074600001410345c016280104d0410942c2d26800141c010002d600e000c0020401008400c090980c031107034038810340c0c40b50b40da550500246018854000303401c8246600e418080e503000b5150f201d05850142034150034401d4601b1844162010301c2040c52499507903610800c440c41081c0940d01d00c0b1001c0341414410101f507a404a43d4801c80100004015031022906100b040380035001413000384402001551203101700d0070917141000a6005c12001301d00800d0503107020702c1c083c102c450202c90301500d8001c001c05002c400d108155000410803600d1090070454001d2400042c8291b50094410100005440c0d0900002a013111040d42203103100f603000031402c00008200c040c22101261031b0540c020340d02d0300c91908890511083c101482c450302c00f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 164635845 1250 164634595 164634599
    0xa0e030a1131051905100e070201090c06030b01020304170601090e060f061c05010903080601030e070e0408070203010b030d08061c15090212120706050612031c0603020604 75
    0x4010006000d1051044400074410110101d00c070a0240b184903120400340403102c100030603151190b000c42c1d4094102030010b04222418020310044920881d0351001203030382034409008605000b4070700d9910001c00e000130080d00020780c5400003a144144101420941c40d660411681d91082c000d4a0081404450079010b41e0300402099445d61024064130303640034a00041d1030031506002416500030888400132404680321101400103007a62450b40c8800340103d02c8003080040c40034880c40c40c80d40e0096841402504042c00010f05450b15148000410780c845503090151809800001c0d40069101c0000d56a541d454804280901040d2240c0ba905002d0f6000c588003083d00a109079118950803a29008940c018415520003c0d80381c6601802c102200065a1001f14680d440048100d0009107984094440360040521b461140741591141e002c02240d81c0f01001100e024240d00040e045910000354904a00e680b0781d0383c0110042c00e00740c001d500800d10840c0c070b12540603001554014080319540c035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 164637095 1250 164635845 164635853
    0x30e04090809100207052b0f050d020d08070e012003030f0709060f050318011e0903090f1413020f0315090a0501031e020102010b120c180c07080a0e030a 67
    0x741110444030b019400444100c503c07244081818400d0300c00041c1620906441800032030620249028001140d6107484071800124607800c01c0d82c6001d622400c020920091107640007410702c0145840003040c0240807041c084000c3c3c200d00c0369070501e03070280381c04d1588500c000c2c1c0e80f02031200701e4488502a40000424804d00c40a040e40c2c1921641058803006a101d5640804580e6014003003217640000f40c0c280b0108031380301184070a140d0b844400c0340000c100c10b000c1100080b030300d94156030820348440c4e6890600c07003055007259a0303800030160145001415482c001030440900e421a0105114603405004855680401da054404100440e80c205840380307003001c0c0170500c0c074038203080300b6100760055030000c3c007021361034007a0a0590707600004540c90f0b030300c0200402009c860203130401c0b07042d5500c40203002030300d84445c50311840e4080d1540050044082f440c00b4407807071180302010901040e94030410031244892030400c4408040d48411040e50355180c141085480e0050184600e42c1406907100c01c0d000e00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 164638345 1250 164637095 164637097
    0x4030306050114040303090e0421020304050a0906080604060c120e0703030909050601120b0409050105130209010b1204030f14070b09060a200a0912080706060605090d0f030e040908 79
    0x24607000c2e2241454641028104451030207039100043c005251103c003880380b4000c00e02c00e5504a44201003a4800e0180f081100342d1020b180200c80c40180d101040402261030400c8820b030003064510300420102c1e007000d0072662a81c02c001c0c80501200e40b13a1043c11036542c40b4400034021002250b00c10410100344088070b40e2070705220f00c4140c000807050107002c100c10302a4800c090240340140c4490244c02407a1641002500360780d01c01700d520039618548000404c0007070281c40d10802c0c5891307101030006403d00c1080045a4103030802c1c1c0b00d06d02c050104d0500800b0380c00c2d81e242c01c02c0d018240341c0318034003500200303d0360340312044a600003004011139075108100c004458640a02d4011050352016512030316400129201084401180c0c0c850724030700c80c02e00e15444020050101e49207841380c072140d12400c450190300d0200780c00321060040000e450003400340d14070891000e0412403400603c3c0c80044070020b00d0501421001038881110030600b542058003640042c041d128010303200b03100500c0300b42800601 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 164639595 1250 164638345 164638349
    0x109080a050c18090a0b0402040608030a020708070803030606030705030c040b0d021b0f03070209040c080d0210061203091809140a1109010b071b0f030b07200c1c020904030306 77
    0x5400c2d000c00d80800034040024144502c0842c002004100110703142c0030406d5401900903600140d03500b03008982d90382c080c0b0041c00040444c0e0003c1c1b00782c5180500140c50220076902c03000003500240140480c0355220341c01c407500f000741e501d0255204d860300390740078507140700316403001c00165030000d6071500c1080f098014158404d4400865a080b00c2503240454650100c006506004c2e00200110030041c0341c245042d580150050740e50003031654942603000d05c3c114540c0c210300003680c000c0c04040082409802001d01810100d0a0080c54100d9980c0c050709401090152030300b5084c02e0841003e492095078882000c2030780000020308003c0c00076452985a40710410f040e101c5170000c80c0d0710300c0642051882241207030a40701d180c82c80c0902d5500d4140b40b02c1c00d402034100842d0400800018a260014000009503000e606040058100007801910f55914206600c043d03034a203c00e1555038003400305014044102c2516804500c100c1c12040704084102903100940c401503036002e03c41816459808181 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 164640845 1250 164639595 164639599
    0x12090c0406092304150f0e06040f02120c01080c0706020903061005041116060902010c08030a1b08040f0204020f1b0d03180b060d1707110310020403110405060109080a050c 75
    0x403240826141c400014002203c01501000c4404610340e10200d003a4802d0240b40e03011b01001a00c02100030b4811b041c00010343d000d81c2d8055200c0c501d0300541c940000d28921092010005180b802448000a40b800764000d000021803003000c68284140300305601114000a00103041c3e611524251b44a542c0048003405101c1c0141e180405000130343c0300c03040c21110019000010305480d41402d0799040301909103c02c1c00c0781081500c0d030100c400214011302460091002c52808140f030089611607446507d2203441c401c08110591061001140313070340012074082070b011384016076641103c3e1002d030410701ca00612000001d901d0041e0a00004002ca10710440342c45a41e001e0000d0705442d00c40044411840c2c0c4007400030356002c8041801441c0c403901c17056100784200700907841e00210010b1170505030041d00d4281c5400940003404040c0e46000e011820000504400c21030400d805c58440b08018020114040d01607555080401c0c81caa02590981008000303440841d58506102e00c0c2094480c41c121507024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 164642095 1250 164640845 164640881
    0x8011503030905101209140703050307020906091504111903060f06020a02010503010e070306090905030702240a05091f050c0106050a0e0f040f120e03070b0301080312090c040609 78
    0x128042c42c02d101413a0341881030f583d07190040d031016981280201940300d0102c0d20340030400c640982032481407000500540c06040615240c4000740144052032800601e150b10074858442044501b9203042000805540e007502e00188204e0640c000007007501c18281544030462008241c138907042e6250300030303005a840080084e100d040c0e4070310082c3e985c2d5000c240b009000c03404c02d000500689010112440e480f06c0141340100301c0c03594480556044625201c1c068400343c10000c1c80300b056060001d4884201100d00303100d20440548140050b925001d89480328042050016401c5e006981c1c030f40d4050403641a00041d03803900380d420300b00540b80364000346041d60b047d401d05070300082c64070784402150101e030100e41c0000e06d10780d24811040c40b1554020701c21101095580503082c0891020207102d0b00303034072241d1210013071700311103c0815281400d298000c4002c000200700600c420080402501c0208040200c034000d5034075118046400c4c4461350320265042460038100190600c0f030382d0865504590600061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 164643345 1250 164642095 164642099
    0xc0317090703060e121902101d011505060f09030a02030d08070813050c040c12060f0911090307030b0402060d020a030c031a030a080a0302070219050405090303160c0309080115030309 80
    0x180c0d02d400c010100f8200080c1d09100c030f1810346e00f001d80200728003030303891040c0c0f400c01503020491011039109068001c500c03d0306441100c0003040900c130f007203100d0700300c03500d103000940c90400092540d1041007200f509400f004180741c1c445480401260148035801426074a5075140500f0007019000201e40b09000102c10308082140c0c030541c00140d2101d00d410101400580c80c80350f007800042e0000301560310400544c0c02c84072a4940140c400da501400140c091000c002d40381c03030100740a84030301f5030748007070b2060341000580d07140d6030700148400840f90300004140440d604d0f8000a6100d00030703078120056050000500030149645a0b10843c40500f03545c44c00c22000f1004903900c40c12541268655405510112001000c2580c10024220039480c0345005480c1c803860380e0104210f1034140400d07958100c0d9141040c019071070715016180c0d12000340c0c4011419031401e41d01301c1c4003100b8210011401d102c01c4004410074144560401c00c060007000000b402041a0000c01604649045c801074000850380500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 164644595 1250 164643345 164643371
    0xb0d050f04080f0a090510120b1801120204060b13050a0e0705030a110f13051507080313150501031b06020102033304050906070e06040f060c031709070306 68
    0x441e00941d0030000490411900c00e190f50641e030f00045070b48040c030606800c0041c20303507250030712050b104499503980ca11120304403285d681600c2c2c803e07108522802c6404240038268050206050449050110803508281f071800458018686900a105042c1d000034640c250400314410080031158207603900b42031640e40320b0780a0080c45080d1a4040080e4040012445038503c0303410801d1502c0741c641400b0b150012452008103903501c01984101c001000800800081c07130900041180c601281000a280038402d82c0c0d03038040d501c402000007182a0a030702040003800403100c00c40d000039450300000c21113940c4a040c40204011a146c800a00c0d03804240080b4441d031060090302e02807408442d00d020007004000880a02400c00e0041c01803540030f481c1011081c1d503613801528010031f03e4002404403400c01c040010f0a9441c108103140c000c240800040043c051125003400c2150f401d4900360440507102c0ca0221840040c10b41500300c0140800203022a10b0720110b440070480e4800d440801100b680860 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 164645845 1250 164644595 164644621
    0x8040b0a0504030f051305130c0207170316050c0a0b030402041a03071703090409060b0a291c060b040518010e06010507050f060c0702040614101103090a0b0d05 70
    0xb50003000902d148402c481003600810241104c140f51052000e03c940d107840c0072542e200140c01181115035150920950302c07a4051000c071018103240e1070f100305107824070101a5568403458450000c0e5081c1c4aa810041c01801c0c4a0380070201802400001030b540e540b052031405d40c005407020b9200d1403503c450400c0c0e851406031407045d20703140a03002d03003601d0345042d240401018a56044140900040021a051740c3d0745100f441e1b4100d2007008000b40038038450303092040d0b4000c640c00c0a00042c00c507806104000b9100032101c4070880503e02d1166842000245136500303600c80d0380019000c20b007841c501107180310a01c0c02802c2503910503039030707402402180b0f5420310880f0000e12480b20300c0d0307501d500480c48a5106200030811140200210b41c03590038451081403529104440100740450b01260b03001c11460310b4045d0300018aa1001000c00d00c040400c00502d1891002030304009100b69000d00b11280d00050042d54610840149030011a0380d4900d0700d405564082e14441813071601c0e05000884050317140c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 164647095 1250 164645845 164645851
    0x70519051c0506040b040227060403050319050d090c1a040b030a09080c0d02010e070608070e01120b0a06080114040216030f02070f1701050f1501050702060d090308040b0a05 76
    0x31045807035109164000300000d1001525864125071034040d58045615680020441501c220ba48003030400000126024900d002000d640d100d10030401041000c85d4000058500c940713101d490400c0b0001445109890500c98546444502805c104100c818040300fa200c03d412921901115002c001c2592119900361107580501186400c0134408192114640d034006159203209050051034420200103540c5099280c813007100050391130303403000d0900c0390050044000414640c2800b0000703050090000d480315281c200c845041150001090402a025030801605030b0005002e150446d03803244d400400b440c000340603a84121045e410f800403142018400c4076041010081c5603401240342d40d85c102d8503240081e03442e0017103105865000c070340d13110640c1c0c9090042c4450058418100070076111582504c0004060603010062202000001006242c4900c12441d0918086a565001d44002502030040d8545030716110725160b805020107801018141c060f038000e46c80001161b0790150048241e031012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 164648345 1250 164647095 164647117
    0x1506170609060a14030307020a080609010c030c050703110a020603070f0801080304030503041206061d0108011514190e010e0105030f0307030e0f04090203010504061b0206100303141207051905 84
    0x1503c204204101c602103248140070040a407481d1103070ba50000f07110454150403604050308076005000810109109099007074025003414800300707500840c060058010050090203219620100e4015504241304107a0501d0380182002e49030304008a009046044030110b0340d006c18107040c000324001200100350f0b4101c81d4080010740c41d003402c11803061b03000440b038001210030a1700d400c408141454401604500624180004101503160003030040c01c0d00d200c01110b0302d0a0b03090703c1c4103010b000010030f000703c0e82070000d481c001d034111028035181d100040d4580c840e08030500050b0000c1560741d24284064100c4034103c0032200c1c402c40344000d00c0d4403485803d0005002c210584000c030b0150030b00303484c0040311110041002422010b02e070046420350307400700c50884103039540d005480c46d4242c0e800ca94121112043c4010705440c604981500da8501440c00040c061000100c0303841c51813a8140300321b800c1d2302c0004002c1c41c0a81403540703002c1d2080e0001c2e04040302452165116030010303445a000d5a0b50340d040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 164649595 1250 164648345 164648359
    0x4050d0306172e0f020703142107050c0a050105040b1f0504110403021207061b0f0f05070320040f1107171303080403020907260a150617060906 63
    0x79407003800b030900400c0c0d45402002035409084101050140701e44c1c0e110003201c00025a880780300d440c00514071510b403032000030000c100380602129078508a0076440f03c9500c00108170aa0780798010140d4103800b07103440300b0409219075840ca5003004019004640194441e40a044881e110103607110280c844501d82c020000e0341c04981000946407640142140a21000b0b1441c0380039180e0300403c00c200403000703410809078030000040004940c01000d05003e281c50100d503107006801da0342c41e140020100c0302c0c054113440740d503910300303040c040c0510010004552140301d03e00203040c1ea101179a100303151201178a12a41c41e00c1a02c0c03074904031034001e4280e807829041c410b520b41400750355000310844240c0104d180b0001c003446080d410108164410f0080c6004400e020384072484c43c030400110078030080c0410100030002400d4040c1c80d0414007504040440076090b01d40070703070342c51105000a11400092240865060b00000b94031504000f400c1003140110100113100e40da10024003a0b0030704207545040e0400c034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 164650845 1250 164649595 164649613
    0x703050d0b130c050a0207050307080705094c030b010605070f0b1005030c030d05030112051207060903030b03120405040f0f02130f06030b0607020f01030b040504050d030617 76
    0x1101c0d03100000e4518028260b42e0704a01407142d010031a0f140000210114100080b00e44004d50100000ca00a05e01100100840740c20f0181183d2502c0e4203109040c050311440c40401d0007007c07000d400c0310280910000c1c403070301c071045c40c3d115110b44400050805e41c2c02c203030a4006880c80c0b14010198080d280c10004950003a481e2800484140c0d104000c2a030b89810700488040000d03104014042c02401800200954a824481098209065401000c0c0310342d21448000340751642006c10f8a0440700e0500f200034440d600350401904004050007000215640061042c0420606034007048819002e41e404010303802180d001d256179074541760001c49950600344420001864a60040300b0000c207080b801142e0b2000c1c0c80030410136071700881a1145002780d54901032100704518800c50707000300450b1405015903a4480c000c19520312400030080e01510a1183c2048140d0081d00000f03a4910b0140040001d0302d0642041c44d114000c4040c0040080c0c2810320010381422030718007080c41510101c0250041213 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 164652095 1250 164650845 164650867
    0x21201051003061203050a121401080705011812050a1203050a0e03070f1203151503050c030106080406020708070f0f0606051e09040309030206030106020f01060e010605070b190207050a020f06070305 87
    0x500002000010440321103a05444800c2303d00818051980c020403849041d41000f014a080442d6508042d04201009201c888034400c83c3c0302d0301003115407000e0540d00004450034800e040c0702c4030000191041cac0c0d05500c1c0303516040d0f060340968421442524100420502402c139a0346920500314041d0245402881d46000b00d01e40c00d55a40c229522401d00040020301e000ea252407a401c90b910400f040d08185c485030710040d800d4042d0f40d911150f400140d0740b031503050507006030191002420141400e40d01007411000c002286084805903a00007800020034041d074688480f81c01c1940c44110703600d60403c5800141420040001811070500303410401c400740061060185281d401401a07041194000f40040503868030740041d40648950b40c00303400050200980720b425151290f0054185094a07001080010340c031100303988500707030312002c0c1d4401070321880c00800c1900d8132410001c031118800210b03c400c1102c001502c105961080c4d43c03110242540704200881800703445005008118204001c890103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 164653345 1250 164652095 164652097
    0xc061f0906081b0a120302060603060c03010f0b0c150f04150b0d030e1302040303260708041211070602010209010305090d0c021c1205122a0d02070602120105100306120305 75
    0x48180506200711143e52025100c0c40170050407000e9004d40c00010502c0260304040c00003e0740032180c0300407285076514200003103461000710b04c90008952400f052a500844040c4050120013480041c0004d00d4203210041c00904a41501c0c100d40d42c594101601d06038031200d00404640140082404080c180c80c0d84094842d0003454500740d600400f400072288002e511803001e0700285001350340e2085903a4a80b9650782c568940180060440ca0744d00c4204071001d94007012841d07206510134020f80305a0f008a9064442a0b010a08003100e800303020800f1480c80d0b0f055000e07014051090b40d06201d151920441c0340d41b5001c0140c0084000348440a51401609003401c51106c210805002c0d03001f0054542c481c0d08100000d40200f4001920026100c000301a25a501580245640c420f0303072510030010f42e481c154240d0320ba5200312801408030b03c4c0c00c078003021941074503031158004605658968004051900c7d401003405140d10076103645908100442c441d03c1600c0640b420f01481e013041101c0c41c0c5043d241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 164654595 1250 164653345 164653393
    0x61207080102040803040608130c14060d0c0f030f0e1b030a050d080109060b090f010e0a17070306061707060509060912060a0f020903030304170c061f090608 69
    0x4522400a0010329100244002c00040c14000041c0da00c1c3c03400c11074018100100030307210715119450009040c010403a0f224102c030440780c890b651962030002e14004181da50040f24002c0340d80710b00d40703800b84240070781059040d100172f2290b550401101100039801e4007203c4d46201c0d0400264411140c03480c10b90409200680c10342070003030498040c4001507884078078056011425400045412004124401c401e000f840301819403000c01c6420140000042402c11034107003070140c100104040c01d803020b0f4a591a10308041c00e68500b00030704000c00c3c6000155a03c28500c804c035809031a00c40d000908449910342c0d001c0002e06c0da00542900782c03801a0403a25500082e8105922003020030101c0d095648480c130b24000312040102500042c505143c40300304a40d501c0e00340c915454010000442c896034080200d90b4020740c0416403040440c0881d2804c00c15010750768285215110f44401e004c3c1b015070780c40030034111040300807000c0505625400d080003500d15521603440e4580c0040c070b143c44401a11202c20031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 164655845 1250 164654595 164654629
    0x2070f0b0606040e090c0f040501080c1513080109150e07030b070207090516090803092803060921090b030c090f061801021614100216060e0f041406 65
    0x4109904ca184503214403c1c1550070038a950b10440c2e14410f1420f040c105208030550807502044103614007203c3e9502c0d03011f1154058071400e10292610070415500084c2ca10007000003910800c110745030400c0a000b00f501100540c0ca9019165000003082c03a00d004044030039440d500a0700d0001c0c55984d5400300c0030b5003d00801c0960103804000304040d10b4a1190b680700d80d8141610358004229060007410714220351704801282d070810005e10485072241004400641480c6c0c068212101c00e01c1c403e580e4100e225000100214101605402801a0000a2450701d2020000300504d212031000641e001c00142c402c03080b2821081c400107081258100c0a0300030960050f0411a201d50000d00041c12a401740f4a41d051800081d801c440041d68100a01d240a90a9031030700b007007950602c01c42c00e05501d0300708460341c4121030034061684441e01c244402203898091802b02c0580f280c40c0c800c0902982e0000c590329000321180c8800c581c4903d0503004010f50b50a251600310421740f01d580c00e00070396104c5644148 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 164657095 1250 164655845 164655847
    0x91b110114040c031505060a06120b0a0b09031603031704021207080d110303040c03060c021e0c100203030f07031a130b10020a08030f060409080304050606040f02070f0b0606 76
    0x210001000785042d00ca070340318900ca0341800b4150f1400664282610080004051a010070005242c03500d01c090019114582001c1d40300c0e81d0003184800140c4841c10407d40c105c40203040c00241d540d40355020f0b01c0c00c100c0440c161088543c0f048860b440082d11480007030001805581003018502c100d17107082c1c4c3c0041c0003400950298070040140c42ca0f002180e401400c040c0c0c08685184107042e40000320301c50200a0700f02441c40c6003003640710700d000304600380806800e26603641041302c1241c0c000c100c0f49807034045074080c0500c101040d0350380e283c07a0301802c18a18001c0f00c620340c3c0d480c070552020040b00d1207544040508038240c0c40e02c0314100e00070240d41a50310b02a004100d0700e50141e40c0c0e072141440300e0300e4a280f0301180514612041c850b92699400714501958001c00040b1300082090b8180c9034040c10f507010078402550398600240c0a441018800381c20858000140414414007080181c07150030250b40520502001a8a1400302e11036410040e01c0d0210700769070840064002103415400c01d10082c189 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 164658345 1250 164657095 164657111
    0x603160311091c03020607020c13020c0f070b180d0b15030106180f14040f03080a090609050609070b1305040b0402070219030506010506130603020a020f0708010c09091b1101 76
    0x10850f5200c2c0180f007070340c145421444103020194104012580020144040c0025034461000b203410340b00d0401c001d802c01e60700414110300900702005140c1442040c102121080c5036110080144d95201400c0107103010540c0103a2001802d240031244400c0e640210030507441d0303032402d8400d42964418403119a040d5200e040c0014140c10040680541010807100001d2560885d00c0e40011030b51303503402105501c0e0002c420840031618248080c50940d8160078600040d075071300848400107092605005051502e00a1000180000002d84038820b40d1403500701c401d000d031200038680701070113511103560903038400c00303003e0210f8185a0410946840054400750514600b40c1c001134a404110300c5c51051514106020420300c1400c0040c1d40c0101802c0d070740e907442c2410b40c01c2c0c94902120b81c1e02460090540004100c00c1c12403080010420b054501d1080d10340050b150300529010301401100100084d054040125100d840c510a9145040c000a00504030041c0c1c1d020545400c04040d0807003105550368400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 164659595 1250 164658345 164658349
    0xb0d0204060611190203120c120403030801080d1d04090206160b090706031b031a090405010b030709020c0303041e0c03050a0b0705030f01140a0801060f050f060316031109 75
    0x400300600b40c980c803041d450b5032040000f50b02d40202803000c00c28000c8540180000b6840c08105100512044803065907240e502240481c540050084524104040001c001007810790180102e03061314441001c0c1e07000b0310940c0108031010358210900b0105000c5c0540c010155107011b80c40b03002e04c0e0b03101811003402c1c2825144c8030007036003030400b400b603c4189000c0104a940301d4244129130240c00716003820040c200b00f00b24100d01c100b03407503212802415918a070510348409c0c02d900c0d021241800400c100703010702d840d1900318064107804650900902c12040045050042d5000343c2d074074200030b88001d5003156900d071181d007040e1f041d0089120380180449840c5010170441804000610700036002048982c49515209103156001005542040b0b000d0080c082d144e00c00c9030610b0b0440703040f031a6100440f4000000103000403503e82c4181c4440d86010400903185080540da2000c860088680720340070780c1d407201445000e02c805c40b801c680080c1d4090342041103e0103941303d070300c9580c1d8180c030050a00c0c04240c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 164660845 1250 164659595 164659601
    0x2071208090601090e2e050f0c03012306280507020d0b0c0903070605040311010e0d06050402031204140901050d080f070606030c0e0f010503030406021203060609151b0d120b0d0204 79
    0xe580140d800e507410306006e10780740c02e010740c5402001d10403c1229914081c82ca0800d030740018061800c00e090710f100001201a01c24603140c406450040046075a0000d02c0b0401c0300c401c4500030007103602125610740d120150300600076250a40d4010b01800c0701d6094a54560303e00e03c10041100c5205441407100383e950392010030501d0042c01168480729940c500710b00784814203004140d0b26504010f0390031a1141152144500c10901070381c4020045543d4603540b0000782000f402c904020b41d02d0801040020300f40303040850303203003807048241e44181c026600c500501c040e008445401808208080151468241c80540103190441c00b03450b0001d0f240740c803030381c606030704c616030b0340c040c0d00d44103684c0b01400b4110103543c41c00c50051008400444c0b03001d2500c08040e4803141c20010090900401000064581d200c1004481d54404020004211440203100c450051380125414103103624a03c00440307a145000210600321035040d4a03080c1c640144201c2c01c801030200bc0342001d03045905a00301c40d0040e20707240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 164662095 1250 164660845 164660893
    0xd050d021303081603110106032315160908060c12100801020708030a1a090601050a030e07080102030f0a020705060f091e011b0504050901050d021203040902071208090601090e 77
    0x344e0350301040758040c200100383c20400020440143d151042c100006525030001004019840c080d031010403079166141801c08814034000c00d424480314003080034a030904401c444204040340c84042c1065220806030356200d500b1103440003061300411421082c4920f00340d0003a030001044800360126900c03000b4a0b401e98002c3c02c811a4154804014008100910f00a0054003818000f100707041514110004000c220b01034500b41c18080005103a8120354441c0d0401e0301441c0309039088811840d620340c0f40c0e41c001d5008075030f02e114502c011408201d0300c01c924000c803406107410a0090000341c68a140081c81484003500d9005603228030b1901103240a01401080d49441c005030000030b00b28580007144280e40c121320450310812100308018000e0365601e11305e56065400a907042a0300114034408181c0581c00d03451400190320002c0740001c1c0200c0c41c2d40061152a11400c60203680d880701c2313001540c241c2010b231200c801035003000c4014080504a41d011220307499640702100c00d0001d44c1c1901004000c421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 164663345 1250 164662095 164662117
    0x90f0b1c140a1404020904140a0204021c06060504080307060209120d09150306080601090b0a0803030c1c050402030307120504090e100c02060601080103110d060f090606080d050d02130308 82
    0x1a1041009900e820303c54451124007001c2203805034070382580000c0d100e5100804c0240f40800700c88480e00c2c0c51400b0082d040aa55000d00119514902c01c038466507204103030071203040140c2c145030001c5403451107181901c00725903461000710b051011030b58600011713410009000390031010510144a201c0400c004c82400c1c91400e8481c0c0182d14105610801196180c0c4401c105060414904104a1800260890441d9500340303001601c50700002c00240d1488566000e5035040c4004810f01055440080080c1094000f00164041c603070440c0c40b0640507150101c4019505400c24060030002c60030000f0021141c00880c5480f42c50700f5251700100085888000d8040c049034062000e48000c02c030f09100e00101710705d050000300503614280c80001c0c0b004405010041c200180140302d410552250002c1d038000c1caa12120500000d07495031890402042c1020090340c0c0c0d2801c010b8006052980420480c142090301e0742c80600c0d061914000c2d0019501030b002107070180340381c0180000402e0b00304024041a00348 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 164664595 1250 164663345 164663381
    0x60d080a03090611031e090d0c06090c081606020120030103080d11040603020403020f0904020f1003060b2808040308010b07140303090109052109013e0d090f0b1c 71
    0x80c0d41c04006c00d0050080c0060318036031000703110141080d0445005d040450788558042420407003407410904a200a5220703500a10a880c0e140e012048000144810756801d075000b040062004111100e90135401e13800140c440400b00014408102d10500030302d41346009200100f0340b503414114045c6d041d8401c2d4000c07400aa400b04d03062003103151040c0c0c2600088011900c1d18943c1c1047e40010343da8010318144144280b1544210040071800380c0c01040050001e40d1401d601d400c120714001401081c1e11082d890940c0c0c45d9290351652500034080c49001ea601075941c2e0855a003407100022480d40200301c00c1d50080d03026610702d201038204200943c0300d404200000300305030300355141c81c903c1e101d4070b60015a02c0d24004201c1c003241302401070a4941045092030240c1c18140d042214108400607090f02c0c032940030750704112180603404446540e146c0c0701503c040316140500c403002100d418007203000720301070840c0c810300400103140110701800e269180c101102111203002041d81003218400400b0b40c13540d40c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 164665845 1250 164664595 164664631
    0x1b0604150e031c090605030c030a090f05030703232b06050d05070306061203020c0603040c0e04120908010b060316090b0a030501030506071d3007080105060d080a0309061103 76
    0x240c0130401d0402041c0504051381503007000320500c1003500000300742c04d04042c1d6640c100f80038400708100c3c003c52150440c0540e5602d0f05a42002091080301e6a018400b10b800264408100a105c004840c2e007410420758003140c104140382c0c040140c0e90502e841d003280545820f00442e842c0d03100407002d080705200e80e00500f00907103140303401030580b101e44c0d109d64210035003142c80c074021980100c0c4c14074400808880e40c070f40daa501d41c80c20754107020181e0004070784070b55414100b00030001418183c040c080781c191038000740c40d03950b004107a00303944c1c81c01145500540144040f840280c59012201686103160606402413502c0741d0414459420110041c00081e4454004209100c0d01b4002d041d08407010f40351165003841d8070074088102d40301203000e243c050710404007041c3e0705038401e0310111f5040c000c05d42c03e003440c0c8540b41801903a403800d130301074a5025407804011500d94544a1150402d1990142c0340b03504100c0fa0303d80036001070401e0715047c0c45403501c40749800000e0240c800250f1280741c00e070b500d06000c51 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 164667095 1250 164665845 164665847
    0x30a09090606091a090a09050702010b090c030106020705010503090a12120b0118050f030109080d1a0a050a1a040509040c180606120b0609100e031b0604150e031c 71
    0x7400560241d800d00010640c280114582d8401c019150b201d084003556581c1d004a001c2001c50201e540b0043c0e91502d07202c1030000040e41900300c06400b4004880c94001501d403800401014802032140c2c3c0c0241c0c0c042d0104011030f502510156030700c00c40003c1561001c189a0700d0b4000a0070307000303030b21340c0000310401000300c102c182c1841404c034541000c0c601021040d540840e0030303103280d2450003094801c16401404185658003500007190f001d9120414546981520700d1040c080c2910341d0b1006040c120740c03507003003440d41031800558003120001040e0b440d003980341506d1540751003070204007821400d00421010400d03484440c68180564030a0000c2d000149c82c10340745034854408940d068240798107100d41000f110b80d1200c030140c13050070300c0d102c002600f0380040e001440c50300c610601c0030b400085080340703101c1940d005490b21945c0c9074242e060b103106103400280c15684040d808001d540c8a80b00380414030020503040e001d02c090007842d0903c0034510000d100041e2400306001456001c009108079078007001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 164668345 1250 164667095 164667101
    0x70209160f03090507120f060e010b12280203190b01031502181c1a01080607050f0f03060109050d140d09032402070b0c0309060f0f07080402060c030a0909 68
    0x4112076280400041026550352502c4038000e20580c0d074410f824604100511000d884d610300c00503031280c41040520349002156001e0011004000c1c801d4140b07103d0182d0f007000114a40007045c41d04000b401c1309841c00340304200524a070300c400360381500c02d01007024000b65000800d0101103000b041903448a61451400c910705c00c1041c040148200d0040c40400204003881c4512951414201c0e454030340344858448041e180041034034090846c2ca8040c26000e00c03c0d58107004541600c01000546940f940c440509484c50b109841c0c0303d0420a00400c905114041c900018542000052403c5440190386900150b02d0000860701564038500203801080010303810007039942d440c00c40b424503c190501e96142c95019a544c030107031640c2405043c2450700c5090320369045030701d4141e111007034200350f09001e95405442c0e041241c04140d40d1182002048000081c2c16020348109170180e5900d01c95511a08111401d4102030b01c200d0304140c06000c0140545001e00107007052050075551a080e81c1e141c442d480b010703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 164669595 1250 164668345 164668367
    0xc0405090403170a020c0d0f1101060b07020a060207050303120a09140d09090b010e06130909051e01140a02070212030c010c090b07030807110a021f080f0606090111010207020916 78
    0x1400b48100500781b0041c1000c035480038010001d0030810b10f2100d4409040d02d00752032048981e5015443c2071400f0443c001048041e1921754001d49486018036159601a80d80b003442e4001d0070750507030003803145000c03554600f90025030003c0c00e02d40c0071035801000c1d924800a040c80072140d440c0358104140100e40554419030706030041c0f403040c005000c503003105400a00031814803910310780100e0b0002101c0107091f00c000b414100401240908118218003820415141d036044981000318000110f2902e004110500400c540129403030031001c02038071a244070034002d52251100300e03040504010101036154052000d00305040300500003081880080c4c0d001403043c5250340207070541c124184940c60100ea80404501c2d40585203080401c0036100c0200351520f00710b0500d00003584400804a40c0d41240c06d0044800c1c1c8441d4283c49a500946a0300225503500310120742a03500000140024181584140d40881581d05148001451322405401051800030b080301c650740600340d110409450140d1103410550 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 164670845 1250 164669595 164669611
    0x10302010e181303090312050301051002011401150c0c1710051501050c210d0f0b010c030302030c0d0908030405060105090903070201030b1804050c041a01020c04050c040509040317 79
    0x51501d4422070007402d00034054080d400060901c01680d003010301a020074805550000501189540d2641c401400756100b401918095114817000c040c1c114014028180403140021080c1e0150707003090240d01c5c0c4002840301c00300401940c0c0500c01d020800e080044400fa007020381c07441c40e6462030b58a19070f1034411060b00308007000d890001041060030001cad401000007002440d04680d034040341d08030760303180050021000480c20100c41820b003a42c07031044000c00c0003480c552010b20540c20103c48100c111600e1603241400f00c1d0f64201e850380080d00c40e034020350340241c5500c0e00d1030602541c0d00002007203c940e080115200035002040c8818810100030355401040c040b01d90049034600640c40d02e81780d00032a00001d060644a081d03010301039840c0c0410b2400c003040b140d04403c01c0e190500f42107680d0700e103210300ca5004503e0a013448913880780c0c10b0a0340b400a401a00140340c420050700070701004200c0105103000140b02448041440d540716045a40254002e555008181203000c20340200c80b03001909180b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 164672095 1250 164670845 164670859
    0xb090f071517040501090b0901020703080105120616050d020429090d1b21120e0d170d0c08010806010f14010509011101060f0311030714120f06070305010302010e 71
    0xd2015031104102d0011905208203255035210b0b0b2402074050a003090004024401d40030411101070415030242c21042c0c000d035134000d42c40e41c4c0e03501440001d0045d280c011016401c141c0010f18101809000401c11060510304180f83c80c8951000004903040b9811100a400c8801100500090320324608580d0784910840c0510382010400000c0400b07503160002044648000d440907000040d6514800042c43c000100400b1440c14900c8901702036401001150807503201c02101450a02c100d401320000700000c1e11803250003281d07441d840e40c2d129400c078007421948410001c0d1400d0000da401529555211034a40804950401c08403d04140e016000108038400180041003d40000d0320f0b000c034840000e0900c1560703880b059004880550b001c2c407902416600703080c000105040344c0c1001000f180d006002d6807800f8203840013010f0701d500b200c0c810500c1001030007601000620748a68030300034510b1030300112101c2100501c8001d08041c0100c5800000c00d03510030040065503000032000500c031104503095 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 164673345 1250 164672095 164672129
    0xc0903060a1b0c03020309030706051b07050108060d140304060201090b070311041a0931020f0910020f01090503040608012103230304060c0e0604121106070b090f07 72
    0xc03000000e0050001c0060f00703a1080c00381402401164401800a8103654004d62030705009021907100d0078451208101d9487e520100f14000f05066068a0050b9144846621100c040040d200d443c2407054400600584c04042c0c1c404007040103100400c415000401e1100050501a104841c01050740051506200c607142d05801500300301c0e4140ea0361001c2428a02450790300c0c8009501440079036907042849800c940e00c07038281031116038443e2204502c8941d036801c40c7ca4141426401024903440035824148541c9040d07180401360b0404010f03aa2048446101c51001d00d00e003500d50100c001c1d03c098100050901400d0740c0220781c90b01405182c858210560100081c08c40d05015800000e0104030445100d8a186054103400e0410943c2150400d52281040e00f031040c02080c80540840c04119817200d030f0082e0f4104a0f041da000c481e00f1207980c100c0c521140e120200d0407800c000c0c0c03c0d40c0c070400c1000b02000040b04000031501030781860000307180d41005500c042d46008019001185aa0380102e25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 164674595 1250 164673345 164673371
    0x51f0e15010207030c0b07030e03030c07050a1401090b0a0c050d0804020102060c0a02210904060e011d0103020a0b0c0c0a090c020606061c0f180b040c1203050403020105090f090c0903060a 82
    0x221034215945021b0b144d50300d090310f0a0884107000e030140030940c0340c0400035000283d040001964001ea400071103182c43d40d60b56800d48180d41d515120300e220301040002c8410401211000c001c2c1c84411400d05110080358400d5451038181100c140c00000450000b600784025540c0c1000215403102c910403041749040c00300540a59507040c003611a58a00075807000307070303c01609102c051f96070400d40600b060007099154001202c00340c900b4001c0120030305c00c41d03800051550700789544604980d00580302446c12414529070701440d900040400e86a172041d1026902d50392a030003008030050500010001f12a81e131584024100780000c0c000074440c040c244000e00383c4c6140304040d00044007002000240c2e86041d080c80c200070f03020031070150007401c1c5240340003000e0000d1424101d100d180b181c0c001262660702c41d02920304412200d0f80c058000390341800140015401000140038082c1c0003001c0c0400c02a8650010b000c901c0111411807040c40c010a00c1178140c241000744a8101ca8128814802c207549406 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 164675845 1250 164674595 164674613
    0x2102060705031914090109050105090607050702120321010918080d0b030a0501060305070608010b0f0307030506010e030d02071d0f0403050702181005151309051f0e1501020703 77
    0x5008208a49940b6103d480d0406900000ca036090079209480e062071301c2c0680718005e2042c80d006555035401d01c0002042c410003c00d0aa2080c0700f10380703c1e241013824079001d02c0343c181c00d8581402400d10040000c81c070707445094558401440d00c071320041c0e021503060076035030320544080c6d21110600006d011800c01c0026008030940d440c51074150320001c4e40710f44c0600040d2400f8481c1c080506194a000300101c1071090101e1190281c803016203650043c0d0340e036400c40000d02d00ca044040311844509101042410380310303801054021005140900c00ca03a196000a400e008240801c1e9000d640310b0f900401008800301141d0450000c80d07000d0f0007103440c00c01c0e400d240c1035100a10040400a001450808655503070340c1c405144c0c4005005085070346020f450b0024201e940f8080c4034440c21185149000041c4240120f8180001001946035414900742140010703000183c107005104804481d2000f00d084250f030803100400303418910720400d00303103c00ba071404409030000450440d00585000d01c08180154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 164677095 1250 164675845 164675851
    0x1406060f091504180b0f0f040b060a080f2125020102011103042406320d050606040f090206190504090606020f0706230c0a02040207210206070503 64
    0x594440301c180c1d1a00c0c049081a1603000e4100d502910702a0f412245012540545070000e100301107240d03036600c40000301150080125000411055030000003000168240c03102a040072016000074491510b40000d40e0400030020b040c481d00e43d20003441c00031101e08004200f884401980c0c06146402d00664400e0380340743c4030014002c0310794080c80403001164030035400b9010501d49840c10355200c1c10685012418201c004494108200f900703144501907a03801d1080380112141544e203801c1a54100046035000c041103c0f581a03805024142070410740c42d01007031800041c0c81140500114540441000112000e495000c403500c1d1502ca820b0005855120803240c20b4026039003c04a50b251610b4201e91501c1203401151700b81d82000e00006039560001400700c40700700a02d050380c05a0b40c460004441000c44460050b902c4840c1c0100450120401e200900c490b1105900b03484102900c0d8000c40d040e0b901500046994001e00103494403140412082614240100d1014000505003250010441d000107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 164678345 1250 164677095 164677099
    0x506090709120218010b0406080609221a0901020c06090325060609020a0f020f01090b061011010606052203080d020f07060519230c030c0c060a02071406060f 69
    0x40c400e03400544d5640036504407403400600b801c0c0700307568445009030803582041c86044007003810b0720702240c4940307000e071100c901c20030341741c1c940c45014800000314110b004902c400030340e80808464002c0e400e40101400d0a4402d410210015a079404030340754007480c0c03800003840889143c000344211016500c05550041e90a040301280d0764910761070b81044002403115501240120348001101c2003603a4125001400c40d038104d8098844c212201d298090070b8400000b4028114104080016150b140c0100140c2d845162450300c8109107498490840c00c541c3c694001c500443e82c0450b0910314404444016010300c400501450035071881c50341d540742d00b401285060159a9000b0a0402c2010068003d5078010b640100c130a0005040000080e03400408101c4d9141c50701d401c01110012034007078041c420746940c903131103005101503a41000c4106181c001902171040131608000040300c586040011501958169030010303a540b0a07450a9500e4241086102815070429000c00c5090b55503500e401034840c400b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 164679595 1250 164678345 164678369
    0xc030d05072324011401030b101d06030a05010f05011404090b0d0f0308100f0503030904020a030e0a0c050415050102030d0917070f06060602010e1b0d0819030506090709 74
    0x1c8000c00e1402c1a000d2030110800d088081c40f000084186000201d0480d10210000c2100303a40e104c00440940e5030320300034180c120013080403040c0b4a80c450000000c1e07881034054031445225022000507080d60040d2030070780031700307840300300610450031a50f16441c0100000d0801207000c090060303a0020758041c82c45100601c40c0e0b194207200294903080f00c0d01807403682c08182c0f0400d941c441d140181a03084145c4442052560505002c02c2e03c2818122902c00d48038020010750034141001c04000207584000c80d40d03410951030388003d0343c11007010081d40e0001d0b485080304074907007424031091108840d031040b00002c400140810401c40c6176004402c50391100022880864003030074605121588540d464800c41c0d808800044034410710000a41031450f0350f10490703040c4505913840c00201e00b61110301c14030f820303107401c040d040748200d0384804c00c030341100c0c00301801e43c0340710041507100c810440e006010154000300c10f4441010000c1d070300d807040991140003151080010304002c1d400900421860003130a01c0900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 164680845 1250 164679595 164679653
    0x50103050f0a0b0f1b0a050a0e01030606050d0b040b090c0717040e070503090109050f250b041205070306020a08040201020c01020703110d06020d05040302010207050d0201021206130e0d020c030d0507 87
    0x102000344c0b85e500d104c01000a998854000320300401c1980011660300c00a0346202418074250b21a0160340121040341ea6400d00b8100000b420100034143c0940180d80103990704208001500e82c035201764820390450200584802e203d08100310111004410842d50101c100703c2401413030030220407a50071010324502583c0302c1d55500247d0740104110800035180b4812910100c0340c0550004043da019170002031404140c01d41074204000c011414090002ca20406100602500401d414507503034540c010401c0315121566600c0f040126441070420900081c5d080c0100415540c04101c20841d41800b8401000303140d1564036100319405400d440c445c814180b14400c2c500307002080d019a10f0494034000c2c100150f04040c980a030003075011002c1240c00d03024104c103000006006100345c894131010290314070750a507544003c0060340f03001c2e182c110002d10790f01c01d110550310320108044145041290010f0845030740820070985442124401c10b810031a003009101c3c0050401840c81d102401404002c3c01500d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 164682095 1250 164680845 164680861
    0x601021501032015160318080105011a0703020a1e06110702010206091501030206071e11040b120309041517010c030b040204050d032a06050103050f0a0b0f 68
    0xc1000451642450410001c42442125000200200d007a1001000200303c00c0d02884290200030a01c481000420b111a1000204180c5130043c414401c4c948031091138464130b420165003116400c0a00260340d110014400442400d036500d00c50001188501e04115447c0d4000b0740c0c03448503020050040b1800c800b83c00038801d00094000003168840742c103001071a143c0442c1122a042550180e0040c4582d41c04290802008145416a18030902c4041c5940c0c0c21030302407180c1a448071104480b244481d803c120404032140300c00c0d1483c070303101e9603040707001c03503e08403c00c0700b5642c04584040c4030303140040465030380b0b0100104075501000159004101d0040200c0c00385002d0015034021844444110000801c40c1d106611510b0302c0c4030340b91402c100090084050000303c0c0940d016403900803070020045004a401401241d0710030380111180c01c60f204102c0d80b1841c200b41200400c491036501c0314014010030600380300301821205500000c18000c1c0e02e544038581a502c003d0070901e260484036000c41c03001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 164683345 1250 164682095 164682103
    0x10c03110d0f020904060b030405060705190f0203040308030a09020a060203030702030412020406051002161a04060c0c17030403060f090816060209061803060609100b0904150617070302070203060f060102 89
    0x4ca0340043c000c10405999180a8040c1d601c21075040f11a8000c0000140c22a40204103995101410f600100c41c580020141528158080071500042d480103000002c005050b8400840c880c2e40d034540e010800402500c140701e401580346e0401025500207104000303844d40c1c0082a24100c4801080008440c00f85002080044c2800d070030581d0001e04880c0039032021a00000c2440a44c2d07030700001015101e90712280c0c04042c4a880c004007109050422007040030350f100f1028002c2041c040c1001e50030441da102090b02e90b030051816038203e15000803404200344101c0307101e8042009081e000038441031145544900c1d65219200f814070314541c280000c0c40510010b40d05440d12038102a2440d95101101da00b0200031400c0800500c1c820b124400000e010781c100041100e02402152400d41201c50501c10b82001c9030b0020f00c200350700b1981e90300402c1003284056402400410303058a80f0707200e0110800038200b004000030010001c0c1401080120016107000407803643c06080040d100c0b081d901c600c00101d081c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 164684595 1250 164683345 164683357
    0x60a0b0d0206040306090c09020a05030a021b060708070f1103030a020a1116030b0a18020609030109020a090c0201051003030e0d0c23090a18291602010c03110d0f02 72
    0x2d020402100f005500e80c04120690b0091410040c0e039036940039140b090380f21f4202004001403050000c111040200d4000c1c124100070203800c40d000c0080305027440d191002c100d0f900341c0001c0040d801c1c054119080009469400140d251500c400400a0318040e50703403002400f107800c002d500040d00300541c0e01c1013000d402014a01000ea400f51030203020403a0b9075048a0000b0b9030820107603000301c3c260b140244510983c00550031019004400e640c1c00700149600030b040c4507074165407500c0c2c0681c0169141411003010302400000011507844900780242181c80061440c50300400c0c1c0841030000c00c2c0c00040e41080340c0c00844030080da4010742d15055144030103a07800102c4220700f1000a5014144054035407440c04030a030760050f41655010b00721002e4031100d400b5010355070582c59442d800700c0c000d032a416030310f6141080d6400c20b114581c6241c0c0088181280d00c4419402d0148007031100d0b5a0a0103142c1f0458410f1070700707018144180c1c40d0308130a07104851040b02d00b00d0382c0342c00b9602100510340686503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 164685845 1250 164684595 164684599
    0x9050415051207080a2a06031b030216020d020a050a030303050a14070c0b0712090f03020c01050a17090127200a0e06030a020a08010b03060a050903070206180406140f01080702060a0b0d02 82
    0xc055580c4e00c7d0081d01900014502c030310101d003926948055a48280300f40c40b00c010401c8882d0004e8800e64082c06204881c101d0b09980007200084041143c0e06d030114120002d5110380d40004d41031800701c0050040302e009124800c1010110001c0c40407080c4e1011446405940140c4d1408458850110035104071506208d00184a82400c0150b401c0c014030380e0820b170419010f50252803034803404000450b4107104c1c1b05200c4000c907022280d400740180d00d4403905a4806104000055501c0010b0341c0411540746110f9001030195a5210440820046030341c03480c0b079071940750100c521444041f0300040c1c0618440c0609140c02020000007030075680d082103a20030407500500802075035512500424060022880d00c1802403045002280c0700e04020301ca0140b060201030013450420000b542004116030007083c0ca104600000409070000f99900e00c6006c004094081c2400c004d10b401e801072000840b000403505041c09100b10401c09041c0d00484c04c01d030311400042c0c00040302c00c0058009200c1c8080c03560042c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 164687095 1250 164685845 164685923
    0x12010605040303021509070902070f05160f0603060302060315030a0f0c2610151701060f050609010905010f020a06020706020903070b07080a05030709050415051207080a 74
    0x100103810100500c10b480c042d07800e441140f1840008810103010a03200800d00303a20664040101e0344441e806003080030310a113404800c40482da203580303190000c01410084030381c82c400400c1002ca000b1034141c4000f0030427400c0a0100526580002d2414000204a4401400c0780c22401c50315540c140060041158070081c04031043d2424140040141c80303501810030000c240c0400400c09502045484500d2440000281040c070045202c8001034440d010b5050400410071801140d20380244441681c1082001d00002e4054609221404600940da01040c0111001c1000c401c059034003006101c02d030703002802e00103140070003120201d15210a903903000c0e24461000ca0300f082044100d800030103840030201d013164482c2d0786a251080340340c891490003d1400b48100500c0d40118014000b4640c0f0520074100440d0150351080401e056038070100a4500106071300710140114500900b28145c1512440000c00700380307081191080d612410840c010781140750103151840d001c141c1d05103412030920364030529 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 164688345 1250 164687095 164687099
    0x40509132001020c0111030f0711152502131e0e06100f2709060608060603011401080a02010818032b0c1707030e06010b2205011e051201 60
    0x8111107403503100100e401400382c000701400640c840c009881341301400901540c40c2c5800399105001070b0b07002d08411145032010003c14849556510020002448501982903480d071945034030000982c0e0003407064040317480e9099114096100d11103240c101c284204000a0300c0f0354694032000c10030303404a805200341d60a014560842c550013045003802904940b80c626252170b1104604072480307405000c0c050000a041c1c4a001110b08006031000071076070440400a51110b550321041c0560300c803604903200b035612100c24802e280c10f003485070040a6002034030780c52455041c4a4903907141c05070303464003a04100102c00403642c04a100d0380700180c8018000304407655034903015080203255441d41d40903981207551000c8601d01e9141400380c840005510348d650310300045c404545000c1c0060140c0301c0320070035a840b07022019204082141c0c50181a24861282e1103a1114500c032141910310145c0d0394080482200c20070a0303036007010300030803160071080c002c0711082d0003040b048850b8000e81d0484090503c110b000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 164689595 1250 164688345 164688383
    0x80109112505061003050f0601120b0a090506130b06010c0809041e140f0702010504020a171501030303150f0f0501140f0f040306050c09090f0c0f040f060e030604030504050913 77
    0x113000d00f181c1c414030590b00d469070b2095425840300710902c6010084203c10030098009000300c440e45074010580040082e4580716034480c3d0b031410784200c1e00c50381d60741c00240d00e8100f4442200d40684e8040024644404208195a182d1066018079415a40aa40c640c180c40840400000341a08822015081001041050010f13181e80010907107694410105a0020900c442e1040c061a4400d580291000a060b880e00b00307204040740c40c45406502038003451a01091320100750449174000c5000b40d9010481c3c4e461003c18031001100c6a2107000103881080c1d04215141400e0240821500c007420722001010751240390380800d21540140d0406a00d00040d0b80c04c0c0302d25084003a10a0780d008031401c0006665100240c803642c810001030a91103040c800001e04680b648900d0342e5409440c020201c2c0c100032000b281400140c0241d0030140c41e8603640501800702c2503001a4414010700200c00410103410709481c0508a80f195010380340c040c60000c0d0000300341c904446941c0c03503d40d501644451070409611a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 164690845 1250 164689595 164689621
    0xd11011503030f030b0306040f02040c0c0803011202060c060f011509030b01290c030c12030f060915040f20120a020c03040b160606080c0307120c0e040305070308010911250506 77
    0x200b22f10661612920305200c910840503002c0d0f0b1a030054005155908044148481100785841264006400c20044450304d4040c0400f0740180703444140d542141d41400d81a070000171280c0721800c01c02032264402c101041e2480845030440e59014555007050141c1c1c014140311a550a4800c5c8001e5000110b070341c0f22060010007401282034201c01d45001d094060042c2c02940f100340e5104004c4034004001c035806182490006400c42c190a044001a1280002203001c2c2d03218011054030084d605c06003c2e07080c5c4840c24280d10f083e80d207422240e00c3c000cac0c503600d034107802140a0400e60480307601180c204041c550400c11078025020302c0cad480507221380040c48465100e4030a500d045408074203108002a00103c0044e0000340c0c01e0008002d0070005003000c0001c0030362038003000e0030346001260540003c1c618482075045c900660090f5a181c0d0354a4580c01c002d00081d01c103910a5682c685444032100717404100e00143c4080b2841c0041202d10b1940e0304d03000c400401050000900300d4010f010074440040030b071070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 164692095 1250 164690845 164690873
    0x28020304090608010504080d020a020709051503010b101710030204020d1b031e0c1b0b040311060720010f0f0e07060815010c050a080406020d11011503030f030b030604 73
    0xe0050200c10303103c510b41c0b82030364801d0b0f8005200c40c805000401c4801a10b80107000621045d10440e0f1000e03a55010940079100140d41c250280c0344000c0080c1c0d0142400e01a010140c4010f1382c211501c00b58805000305a0342072040d500c0c00320740c1110003140c08804205103400045800034402e40d110218465900018901d151030781c040000d10840019406009000c0e02500111001c92908002d2214201d04054202107840b5000c000319204440300707243c40c0b8414985500e0050500202d6854a0300d0003908401410300441030603800312040100c803540c000300c1c030040708110341404620001c900720014050104801c0700c070010344c00e1000b030075110380c010b60003440c40c8800c0c1d01c1110b540303550340c0c4c406440507001031b1403060049414006000a9501485070504103d109104445000f05c40d501d03062440e41003500481d0043e0420040002c400750301403c03504000c114000204000a020200c07000d00040f244001828010103a0488282e01d010341c1c012400d084018094030740340c0c903161600c0d0032004411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 164693345 1250 164692095 164692109
    0x7120b010608010815010e13060f090302010b1507080a05070f050c010801171207020a150c031823010e2e020c0d080c03070206040608040501111c0228020304 69
    0x20b000000d0001000544103407195201c03804081590801001611490303008011103441c0d050000294009203240c46410030b004845500055190510314009081d101825156072203082c1e04030b02c14901c0c1090f64202c507403846c1d211a02c3c941d00c100c0e044040e507080c021941c0203041c40c0c0741c5c21108070a00c42d0224030615003100903030b80d4080603a2201c808120551745100c030090b0315484070b21810048041c2c00010002980002c04e070306a2281d91344144404041c51400712000a00000c0c40c02c4101508800320b03103184181c03203c60300100ba0802c07400442660301e1030700e076a0740d541000488006590103951444c1c0240310141402001411540585030300390b0000a0082d807610720100514400c910103c0c0780d07040500000d1000000000b161282ca12a0b001030f03019464602003001100c0059032510001c000a1002c0c3e2190443da01e440c1c20304a08440070b49640c2030f0110400c000c40c0c80c3c9a842c072514103018800c51380d0b0042c1ca520360034108680780c0784501d03801c0340c000c1c03c41c0303054040803900080544200d07594 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 164694595 1250 164693345 164693357
    0xd0b01230903010e03180d0f050f0d030c0302070201140307210218030708061812120603150f060d2303031006020c090610180f090c03140105090907120b0106 69
    0xb044c22200e95a2040110f0000c12500500e101c59061038042c5203000441c1c0500715444540e0996215581446880092020700c1c0d40107000000d5a1601809450b0204c101401c0c00c60078001f040d00080c001a041d4204c4107a140c1c800400101ca69005d803841000021149e40c80039003042c01e9000520080d0300c440c1c0d04889155108410460601e03000582e0001e80d40c0c100b01600b22a241d010208003c03150808000711203000304482402c916070340801a140743c0c21000c003a413503182800f038241424400210103003282c0000c001c0c2081001046c3c100a42d40041c03007591100303480c040070f08094a1140440c4d0401040b50f0320302c4c01c0715900c8071001004d5402910b0381c039000e075201541c0304016039881000d001500d40084080b000640503280003c55201421050700705070071031001e054403407030146042d5005003c14200310041842160b07414880c0c51281802410104402c00a1194120b1031240510500e84100c00100024a280a041c04a80028505804002000e9070035152030400524240190400610 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 164695845 1250 164694595 164694611
    0x240406020709020304080703080405030c0a050120130e130b040b04020108100e07031a10090306050106050a020a02041d030a031e1b030903020f030706060806010902030c0d0b0123090301 81
    0x1500c04c8030b000365403001c03000380b4003400c542d23065450700304c02801a038090005101f1804015001d10000c20500d100d40d000088659108000c10b41590010309400e10103201841542d0303003080344280c1c0300709807151039203480c58039542c1503401c0c00000202e0200900106110080c40200a003030022036010b240300342c070b81c2d603802e648802c4000e041c51642c0c800c0c14000010040031688950081c1e0004160b02402d140c3c44d06220030721808511b01c1d8102400c010f00040c451001001448481d03c5128054002807502c01c0c42d099014900959491038503001901c250b99859101a5001c0740711804c1240103402e43c01c0c0c036100c103442c94001c1d00402d00c0200f1460040c054400c13180c5007030240d104040c02044403001d406c00044200e0821001068040000c41c15441900e08a103c0800c2c20405080002d1140d0404a0001e007401076030390401c4010ba001d4651701d801801400032051a910607101085041040040e4000c40c80004940c910081682c800c04540d01400b001c6604c55150024040045d00b5802403084203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 164697095 1250 164695845 164695859
    0x60a0506060a1d0f041407081503070302090603160f0303090504020405100c1a190b030606090105010c1b030309051e0f04020a0306092310060804030e2404060207 71
    0x2c8100c0000e030b00024202e049010080640b450310712072950018002e5201244503e02003800c443c114403004401d25019803c00010716882040668445910f51105030610028000700f55540200d0000a00c41e4a07254001246070310f00304400944840c550a500341d94950f64004a5640101c81c0825000224580c0001c95241810700860741203031409001c0007180d602505044a0260303070307020100c60803128000013200503400d586a090103101c00601a07003042c1e00d5101300404031510f0b1100c503802034120508020050703031421079080c11100d0070308181e500c0d40500c0c6008030003520320f1140c02a0341c9102c400003000741a44840102c09544068400411300500b8049081a4003080b00c0480d0f4858014035001810b4145a0040e040001160a0115050752180052401d481a40003210310014030420401d81950055000031742040303c00755100881030403c1c10003041210000c1020301440b82d03680d540e14040d150b1051400c1781400c0072a01d1b1551041c0d80f9906481c0390b20502c1b480006100741d02001c1664 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 164698345 1250 164697095 164697097
    0xd03020301082e1b090806060303070b04020109080f06040b22022404031103070501050a020d231c060918020d05070314010605090106051c0e030c0f060a050606 70
    0x2882410000f8070320020302082c000e40d12452404103181800d043c070040405041c1502920403402050709220781d81039620400140030501030740c0b0016041d401031003803202075200401100c005940016560341180d40703600045e9031200e080c0d03000c1038680c402c20b085039550480108440340100c1c40740308140120b8680303520b51280c2113103d01c54a80d800361481400c10061070000f01007590035122900040d4001810b201683d0700c1d800c103a00c25241e994900003d804c4514003071055401900e002d082240c00c1000d5500025a1068407013406018840d5003881058207128450b0741042016401c6c0c03641e591001410f8810b807a41d0150007003205103c4c01c0030800f00d07480c5118010b0100300c01ca0400415a81c4070a5003c1000c1d0140f00c80e41076a541c0900034001c004122004100e1104550000000c94800c0c0b811041c0704141c3c01c1640003030108002404240340078a4206c0203002e0090402c400481ca200e080d0801c2d81c11480390340c41011091080300d0b22280c1103440466440e205043e242401c200c00d03980c40e001e00c012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 164699595 1250 164698345 164698349
    0x30c090601021506010216060c0213140c030c090409120306050a06050f0f09041b0e010824030c1002070503011104050901030b0709150e1e030c0d210806030d03020301 73
    0x76801400c3c0000e4440000c1c900c440c1d000d0b01c14412100d825030700c0811200c2440c0315070043d20015034462030070002d5040502c501005034042c0d040c10032561b401d0202c8004218009826000700342800804501a000308a00b03490101c0d000400802a02c4032500e00804951501007007500400e0805200140615001c10410110341c4c0d0768442c1450180040d038501040c0d48801101c904071070301481000354a03201c9124807981d052074150600307645d00d60084080c0c40e00e222050000d04009505040000c540036510b200981c40303401c01d074800050400200080e041008100603c1e804c83c0d01e20004006040d4005201412035100307600801c10300000d40000825441140a510340040c4800010800151700f044000d50045107481c2088155448400c02c007075074032a102d030725800159040344040c03052500d2070f40075101860403a403214900c168900400d0303c4281c0380b0280c51050008500203070038002d803000c3e504601d408088000581c0456039502400c42c6034180c4186000b48644006800640d0003032007104c0c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 164700845 1250 164699595 164699597
    0x10501030b0705070c0e100806010e01061b02040e0d05040f0605030f0609040302071203031a01052106030705121c0c0503160201050d1506020105070207030f080d0b0a030303020702030c090601 84
    0x9140c2c2d202802a40c1030382c043d100454820288002c0010a0542019240e0080510480300005246010340c0a8074014042c0c00c40e5086a101c0c41c01000800d81200b8440307181e59030710040d54400041800080e004040c40201300b0514058500c0c000708544c0d00200400503a00d600010318400f50311544100c6490000300c2d1800005c40049002c81c00d0b45c0b606007441359000380310f44100c8040c00e46500c1d4024584902c0ca00407000b10b91942c408000c03c04080c10032059410003840e100341002100324602031400001c0100c02e9080f0f0321003000c900d40b40c07424094400641005422141c4007211510720301c0c2d44d64000341740d060740142901d40d50400c580c855042c810b50701e50020300440c10040c000302c04450004115804074107018040020645441081c061903030040002c1c200e038030041e403a250010342520750040050045410041c01400001d49062482c0b5150360446115a1204801c0070808010080c0420031a4010000c40c800003c040c0e04d0740041041920a4080c1c598040348441800f8000c0c406a031024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 164702095 1250 164700845 164700863
    0x303020708010b011403040f0c030f02090f09030a030e0c10170a02070201140a0c12080601090806070210020f090a030c090c0c020916030f06230904080f03040f06141801050103 77
    0x58041e0071000245410a025106800c070f9407009030340e0030039541c10700e41c0224bd9070a0072024a606518040f03403c80d61010000f42040a02c1c0f070086025601e03803044803d40000c0c16520081c1c60550321040000c190f08404c040c100001441e0000d00150071500103174000f90901c00ea2100166004029000f07642241740e040c2c49403072900c05295146001c80e049218004100700340c41003104041501202c04201c1d100c001d4507448001d041002c0014a00754803500a9807041d8099814091520350005460203900c007542c90050310303040d44041030300081c03082070301c0207610902840000c01881303e01521201110991403080003520840001031b0340407040510080e6010a8030800034581004242c8040381c1c411307051074001401c4000b005c00408403103058108104003880c000c4c0c10f4580300c0d000001030303807250002c84190755185040c1d40d8400c0b00d4480c00400d040703805000710104082256100001c032a6a611000c2804181e0a2140071800440c044944a000680c01800288613940612400e4140c03500701e1550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 164703345 1250 164702095 164702117
    0x16090501110c0910080d09080c01050703020a0b011517100303030e0c0d05010b0a0512060402010c14151b070201090b03060609120304051f080402010e0112020d05010303020708010b01 80
    0x640740c0409101d11141a8080c20300251203641d80e460740e55215441810310048181e0a000c22030307192620803005141840f040c0302d8180000000011380ca002a282403070710ba0354031031592508078100910604001d165549900001c40c102100000c15040340300700b651191482440d1520707058508e007064800300540403640d6410f10219100b030300824000c0d00e41508458008000340041551004c5511056a0380e95481c000100540380041190000349001ca441940c0382c50000956600c8042c0031344002d042c003003800159410811903804c0a1088013144040d1000780901d460100079902003101c8410700c3d105050038046a84422805681207183c06940710300d040d0382441280c4091b0703400540910b91140c0c0603c0308200a99400e03003142651062a00910f40312850081070000f01004601f05408400c444041c51151075404000d6030392060702440c0280405a980005869242c10724082848080c00011010020807a80e0000c5040341c3c401d40c01c03140c44a07998804542224850903400c1d0002c0d020840c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 164704595 1250 164703345 164703347
    0x6051608130812090d030510050f04090c0b0d0603110109080307030e0f060a0e0906150a050a0516060b130608120c03040b0a0801140409030504090203090106030c060c060516090501 79
    0x486100288600c0142d403a10107010b01c000320040084400100c3e40d44903100c0780482c0d551600419402c0f900c902c2c45030301c01c00d007400001045005c080740201e019617515011082030042d1120003c0c010001000181d551700c0d0802018005000907000c1074a07014041e841000d0f2551084030700c201226107440103142404100d80d8210b500300719510040340d015480030704841455556034000c000524650300c90880f444048002d0004440d0001d1549115100c24890360b003000c0d04100c1140c2812030140741440c2d54441c094000e803140c1c0203c11204850b011002080f900b0080c042d4000c10300307035100701c0304040904101c0c840307001a0f9445004030100e81d0800310011200c8454580a01429000701c010303681415101d070758000f141c3d00040da8820000d044500104032200070b4441003c1590010b5900b805640025217001c6d15600c11132050100040d800800910310890070340c02907000c0c5901c500007030f0a081d81c0d841c00800d0100da0720410745c1e5141c903100125403429451104402070713a0441c1c445649403498040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 164705845 1250 164704595 164704621
    0x6050312032a0a0c15090206090108040812010b07020315040305190c061406090c04061d120109061d1b0904020a0803220510120203090106030203031606051608 70
    0x1000801c4401c402c0c0e002c024000d00c00c005410796005980e9002c001c0003450904102d055140b62018482c03916100850000d42c03540002c03581440400c0c00c01c000d20b1723220361404981c1da11031002c0803503100c0324400011441e1341140e4000d01545000f2802c94980b46050454202042026100240894420010716455102804946020241c0c43c141000c1220275522108140c800b4060402105071460042015030701d005452070341c10131001d5001900b80381c1041006007201d20407a40b4565145244071102c00c082d6124180c0c4070558a149009100070445071900001500d4402d00340c1941150a000c0114849070006040b0b2100f08900008480c80070144280f05101c0b00180c016a0003106803103010030090002c0008001a03420b1890030100c1000d0102424050089600420f104810501100c1d03e00c5501185000c1202440c01c00141d890304c0341c107155401000700f0b500003505400045101e01150741c4001ea102d803644d0040c0000e22440e0b0b142c040d044507d1000100b0312001c96041070200d01d81e002811 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 164707095 1250 164705845 164705881
    0xe1807090308070804080706050a09090506130c020a0506071115040305130602070612060b12070201060f0602030d0501050901120609050321091c0917070302150304060605031203 78
    0x8200321090399140e0325010700a51040d00b084e281c1c040c001404200d010f10410054008100525002c0d042c00400c00f4000c00140d054072680006a4892010911035951040982c41d0341c14007400401041c0c006020280d00c9082d062015161405458005900540124101040071402001400c8100d81500c1d54048030b120140c81682080300900011862404140060020708800d400403c04a490000c000f80384c001e45d021000407841c2440010494115400241c0d00310340da200d11203a4441d507541d40c0482c0149000d5001642000d42d40d200001c10a40220040c000104901e1083c00b490703032954103000811038288a100d5074a40c049c0d10010118403d40d1040803900d01c00d205403450840000ba02c0b0400300b0750100b840b11103020b00e1050240808080245415001404c000b44658542246024001d4000340c41400325030011007101a445080901640018541c010101e1100c402504440d8500c0e8000320b4044696600e0b017130000c00c80c1e140028090326203052044d1074030302e035a40b880c0362201c0080d00e507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 164708345 1250 164707095 164707097
    0x4110915070c03080301030618020f04050717011503061a0717040e071223012114060612030405030a03030b0d02041a01030c090506040e0c040b0d060e070e1807 70
    0xd100c1000080c1c034800402c00214002c021440e180e5055080000407110420924900c030002e6400890050b00c6031070f4020b00030001118001440d96a4010948911034014042c40d25000800000f0507141c00f80340c2100c100040c159002c010751600c0e01d02d1768580001c101040c0f4480c08003881070b170002a0b06c2e042c4100c0d01c60380b5031203103c1c00d0035500c01703960740a844c0544401f4007160b140039040e03400345400c0c45551007000010000c400180700030b060000321800d0600411606905800040c038594071003070044601c90707500181c1c0e00600e003d401071280d02c0d100155841e41c03180e055023030308940e131107000404d843c2640c0000b401f03040c05404030340d41039000f022100081900904402c1103507015980760b10400e54034401e1b0303043d8480c140045100040440d410a00c4070310178001c102e2400e11990b01c030542650242c820070028480c840d02c544080311198042c5074000104d07240005980a001c820340c0e0001c07000c1740c0c0c8031010341c541500c50403001c0d038522000c10b16103604030801048040c82d90484202e15900900d907 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 164709595 1250 164708345 164708347
    0xf060a180c0609050103051e040206090102030c0304030f11030a080a0c060f05040506220305040504110903071401090905160c21180602120d0504061e051504110915 72
    0x32540d20781c4200c1c000c80d402200072520107001008556090700074603a00c10b100d449020031041d42182c00305d11006000e07101034010880401e0001240e4000c0049984c1c0c81a8401141e440d00e94a10303010340c1c41009050101c1d1380030f00042ca010614240015420724080e4030440803400c0c807802003070444910000c40425200c440c0c6502d12007060b40d401c2d104250082c3e00800c00b810701403400031501281d4814540c070f0105101115803014001c0790b0f0280540301500c10445010840410b58540440b0500514100355858000c6100014483c0f5042d174800c600c2c0c60080e21180540c80c0ea4507c07450440340708490b0304001400c02d2070380c80d2541b80b04162020480c0c1c8508150ba1440c00300010201c0703100e0203225039002190700c1c203002a682d2403417000c44d0310050025100601034044660002ca009000d081c0e03a2140290300d0b00c0114081044540003031100e211074032400020000030680c050094101543c0c103080c0b40d803070910350490a041c079028070300c105c985082c5001d00e080b403010140701c0e080c283c40c0c000da0a0104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 164710845 1250 164709595 164709641
    0xc0307050f030a17691f170c0108040c15110d0201020a020f0307030c02061b120702040f06032604081c12060f0527040309080f0f060a 59
    0xb030111021860030802480212445001c0c0d040d002c003072141c540d13841080421085240f4801314004c072000c08404a44540c035035094030307100da0309010000c40d000b04000c0c14640100201e4070049160324001f140c0710384001c0394510000c030801518580d4003900c01500407030210790140039074202507003011a40040c40c50056070b61041108014180310160f401c1c40c0040c0d400080d02e07280716504101d031942d514200c20207140b030401c145e5070103040041002e00080c000e00011400b560015294288980c45080070819130701003207804030603800d4642c41114101d110318071b0f0941d007180900c010722401049c0c1c1da10540d82da100c01c0e10502d210104038910707820321104020400010071381403418404803032a40c0c0f045000c1803190302c4501000d48a040b40b03200d5021110304d0040c003045000ea55014000443d182504d0603c0349485800109841c5c3c100404030326584000c0ca800d00041650118202d4200c440309029070322801c014100941e15680107000711080c83d4040780118581c10f00550200d9180000c908412618034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 164712095 1250 164710845 164710891
    0x810020a0e03061807050a150f180f0501090e0714030c1b070314160614040510090311040e0312070207030506040507060306050616030809010605060c0307050f030a17 73
    0x14116400462050003044c10070b003503842000300401510089446000d010f040c060790b07d680300516040002000b600222104219014a06500d900e45042e410000300d141ca4103000104d921207449624001201d06070005189001c043c0e03110f020726425a901554040503141070103950b0400b602c007480ca000b00b0420410001200d410515465058074050446645181844101d084500780c0c441c1d02d50308250342612003030150944074002e4a1050600c1c08049021130322081543c082d641140d600140351404461500c4e40049c3d20604883c46505240c520200600030300090f05c10140241c4425801401400c00820201140300d600035168412a089107031340c0e880f84c03464a00b003a40d0540e1550071540c400e1020307940c1801600e000d4181507955501d817501921506480410a02d805000c1140040c00f0580849080d00120001e20000b0072443c0c56046c000c817002c1c0c032548084000c80d00c0e489140c6118808102c040113803264101c1d02d40b01c42011458400001554140c02009111441e0604503041249 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 164713345 1250 164712095 164712103
    0xb060904090b04150204060906081f091b0f09050108090f0d05031005010201051302010309060b040227090402011b1a0a0c1d150c070305030d140a060810020a0e03 71
    0x218010b0100c0012402c013070900c42c003040c13580300941c02024010401131040941103c500d104813402407034010b840b540d0f42c3d50701003140f101c0c44662815104501c231000904007000e80040480694a088006012a0740b00f01510034000c0c0209603c041040c540080000f50300035901c96030700c9079011040d40c802c0017403003046604010091107004c01040713003c0240200b201e4480c03840b0026100a0000700300030700380360562101c01600c410000741007544609000c000c208072500b02408041e0043c00c15922040d00580036081c04a104404400600c144045441c06280994481e0b0103141c06031900b03400505916042d444016844000355094a10080018000984121142e109d012444e0001940c2103013801c004254074645600400012a0317241c0000580e40d07400d40d1006000c441584c0141c0e034882074803603a420290030f60701c042e0940c04049a150804145600708903207028003652695803d66501c0c030a20304440341c5008803140303a400303684180d94404050b80108006051401e040d07103070110070b0f40000e10b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 164714595 1250 164713345 164713361
    0x310207050114090a0309090e030d09050a020a060f030c020102031b0a0504080a0308041110021509071703040f0806040507030204020a1407050703210815060405030f01050906071d040b060904 83
    0x1c164044c010541c14568404800742c06030030b41c51014084a10807120342a504e0040200d19070f01c15a41d12a0300003000300802070070758559405019092000e95030078010b040546030030b01304004a1f00340301c8851a028418400c0300d10903c1452a585110785031160740d060366410900154051040800020850240801c890840b007440ba54405603280340510b088411008111000781c000c0c2e03e046044844503801040049010310b840a90180c103a541c169039501d080c2103a404804500c0c082921000b803680040018030a86858014a944941d038881c0304603070303030700b001c440141860300000d005100515045c1c00a24900819240c180b000c0441d403100d082c11903008190854680c1e0101c42d0400030005241a50b80a110440c0901c0c03965449106014040610080200690032040000f015080c0c1c2c0e880c05550203450f001c0c04440d0f0340ca21596403513008202c00c3d00c480800e845050300042280d48070764aa038207903c1c180a821a1500104401d0001900c0401e4560307030b00104c1804242d5160300c0d14811141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 164715845 1250 164714595 164714611
    0xc080f091212040606090501030302060609100f0902090a080c0a151419020607020706051204080408030705030d0b091b0d091e0611130521060a0902310207050114 71
    0x10b01420141380c804100d03200d540c0400301803810003004201080e0041a03580d4416801c1d03c0c51303003c81e0707151a80c01300400346640080211418660300400d19102039070141000710710a55500301d2031a10307003075059503660010280a51211000009000042031941d800b282040241094003001c526814806102d800c6200110303084100b40c50440102c035810415580c0140c458005040c0180c02c0c078000804500ca0303840d00c80c1101c20707078401140030041c000701260020409c540070360752600d041385050350310395004902d1501d0645c10584007014503d0050003090048543c407203e9a15151192522001504a82d00314614180d071039040c01d0105071455441011070000112580c0c0003401450100101c4600c0b018540980c84c0900c0b01c25100000d0040140a80e201114550035000d030035907000f10180e001011a00007401054148066031116400c08685103100721400320085004800510184075800d514295245408284d1b42c2c8801507a40100b651070b01680000c00c4000346007031300e10b17405001500d080c0c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 164717095 1250 164715845 164715877
    0x2030a0b07120507080c090303040905040c03050d02060603060f1f08010618020c07052803060903082401180305030403140c0613030204110d0c0201060503010f0c080f0912 75
    0x481402d0740828042c082814208040141d401c24142c000c000090081c05918031200015465030a940d080042c2c0e40285024081480705e8a000e10300117114050303a02c002c0742c0351710841e038424480500100b0342503c40d2002030020004d82e540d4a0030410410b001a010039078250380d0302e4954034140c403040c0340e020286c8030318000860602d20301030140020900f1506102c201c00e1060141d00d0000501143c20002c513039044a46103d40e0301d4940c800070003881800c003400c004e0044614000100209908984a10b50003611008003580d6111200c00d0322200840b41000c2d0407929030322066140d0300451024001e00728140403042e1458403070740d8103851a801b0b90025a901600300920341c900c15810049100020002c0e80c045003040c5602900d900403000703600000b8031a43c0c072a1002c0d280f616058040d0307240c942030b2440911007901c1100019000b4001ca0107180c0c043e500300386815241400782d00480c000c01d00b031640d5024070340d074490600007847e010182c1000114010780d9105e032900341c0b44101030010090400c0c084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 164718345 1250 164717095 164717101
    0xc02010e060a1a0607080c03180103050105040c0503040b07050c1914030c060403030b0418060504030807030203090d03020d1b0206100e04030807050a020c0402040b1c060e06060d060302030a0b 84
    0x546041c0008020001c120700f003e000e80b42004000b01e4022542c01e060311003541314512890107114038000c503652060740344004503000455021070070084d41c3c1030000303032000c1040341d0300c5009100503510140a0600421000c00c0401d000039a082c3c80c2c154402460301c0c1440c2404c294420840c01d0806907496840c10540c074043d440305100080b1000c40020b01101d004500e49080203c0058031048010f102130180359559031901026222504a100d802442c2c0d109448481030b68038080000b02010380341500094a0440029180c0b4024801c0300e0182210900620030002c42d01e202310041e5201070454200551147c01c000300f0748403d01e0364440e650f405600a460f071031602a0070122816819030000840b151660709000100703400400c040d80007051ba103800e5641d8072a290090f4500b2090114441d0040c1c400200000c040c00755002801c0d1165040c141d0040400c244c80c00c40c01980c61314000c0405200440c0041465480c0c1240105070b00044c0c000049601c503580d80002c6c0c1020044401900d51990304410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 164719595 1250 164718345 164718371
    0x2307050901090e1f080a0201020c1315091b18140103060308040f03120509101115010b0306011101020f0a1b17030a050609130305090409140d020705060c06040615090c0201 75
    0x84c007801c107074070040c1940d1481780c0000790f44401d2203c03100d0041c40001401000c0c140990044066440d0802001c1c6445554031441c070024050111201600c3c0b030303001c0000382514480c1e681c6c40e00714040203143c04440c0341011402001c00d5868407002e41031680d108400000503034074001400040c4800034101e400070340b4600b4101c1c001c41e400c003140e034100700c0c0400c61440d2681d6002e030400e5030074507107107800b0290a140c10141482c1034641410024a05505000010b5003803525004600c2280d0070fa85142100724058400703800d0f4001d49141900c904418800c0091081c0304003500480d0b05111241807980d502180c540310341202c80090030000b035140000400c0550112400b459401c08402d0381c2011280c43d00030501001140c102c00d000302000030000d43c0458135690354010302e0362990800080b48802c00d51101e090342e101244001007001d1700503040001881c3ca801d405889a03004440d015242998a5607a8000200201114103840ba030540d040850108002d10030480e54281907000026080c01c4074070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 164720845 1250 164719595 164719651
    0xe060406050f010e0108091e0f0f0304030818040603140703050c010c05061602031c020a0305071b020409061122050103020c070b0a020102042409050a080d0305060d0b040f062307050901090e 83
    0x300301122f0360081008100003140502110000301042c0d8092105662080016000d06026400a01b21440c1c40d8200032201d800030843d8402c0320700c254101c0e2290310f03000c2c0064a0340e0034980300c0a05a60404030004400d50000168580c00e164544180e07490224030070b521140380d0701078101488900d640851319181b81034061003080c0c1c2000240c24003842040d90175449858408000740020301494a880c01203040141075000a580c00305d038102d9154030751154807912603204d943d50320a000081c400140004903540a4400c5a5101c54207402030828070381040302c8040554003214214007159800c12000429003c5034004030419403420500e94407891180c02d000b46100c2450300254891828041c0402c0040e100040703e1504042ca801d0110b060381e00c05002540c1802003100c00f9100e105000100030400046a144403003041c0f281c1401c00603c442641c19134044107403008191381c22400d0b080400c415034040c801800741d082052400301c0d41c5d603448088191a80d50103903820115406c0d42e000f40d1804a01c404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 164722095 1250 164720845 164720863
    0x3190f08031e0f01121101090306020319050c03060306060d080408030f04080c011103041401110d020a0201020f1b010806190b030709081209060903160e060406050f010e0108091e0f 79
    0x4008902d0fa03504106035280030581426000341408804040f868107039005540c000c000310f41000e011902c80c6071500c2c002c00302038507103410b5468191038100000c2c86080ea50041d2409158080c0003020590f81c0c0c2c40c1440b140e030304124029150361105100000799140100003c000350240594625115441c000005151110007142507051003400100d105c0700d003400205880441da24074800b10500000c110050b5010130103007402c0d10150062004001000380c00140c802d80b101d100781d01721040c0700c601c06e15150300c1c0c00080b1503082e140c04403480b00e1002c0b58071401500390000401480c3c1c0c60010b001820203c1901902d40c132140300d6080100411121580240b5401c00924044010380000341c1800d8210403180314050045200c1c41000c5540301c101c1d1000c20074074542042010020130003603250b42107800320002c2112001e1045080c900e0114a600300381100391510356043e12055000640c00d801556040b000070b100600501c1201d0300d003030030f205180001e1050074101001030468103203100c0d000c5080c00010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 164723345 1250 164722095 164722111
    0x30f0304050c040b01051e0d020408030f0408210304081b061305160602072c0708100b1903091401060303170c030c030c070f0228060201060503190f08031e 68
    0x144202a944902c7e1010808203c0d0303007640495444030620f100c04000c0c05140c0042d1041c0c800400d65001c085440344c000d10554105d030044503804d111808030b10282c104050880d0241d00c005002040000d07001f40082c00a000307000d00800c604041d490002841c2213021100c400c03080e4114205103041c82418403400211480c0c00b00390242c4c072410301202a42d5031495218070785005030540707034040c80003084429040101403d034111034990f0900c20401020b01c08181c414061486070488001641040801160420700620340081d4010750541026030007032080140a844019070703051071003010346081c03150b60051031081d140e4142942080000d850740ca04001c00e40440003c0c2007040c80500000202030b01d03400b40f036601e41c0a03034403070710303880c00c1d00004c484030318029007011004030395440b1084003040b8181c803041500e04845030795035031314030803800c0c0c0c0d03400e1140680681040c1d40c2400802515441e01c00300501a0740303601074076170455850b1a041d074412a010b5081c0461319520401036102da4090541191356 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 164724595 1250 164723345 164723347
    0x5030d05070f091a07020a0806010f050a12020607061104091e0e1513051c031422020a050a06020a02011206030809060a110105010b090f030106180c02030f0304050c040b0105 76
    0x110b00350243c0011201d00070745100000310000300600c1405070045402441c0d015140088013903960424a0b5551403c0c060303051305144468010441d4202025500d04486600700c50300780c550055000e00503990721200c0300740c85594a9000b410085982040207000600c0440400034250b00c6544040007001c1680003000b88030703414103020441141d40001d16101e103041030701088000362281f9503401c1c030141c1c050384010b1050041c5c2000100307100d17080d0f4145004103460b850a00107150750b0f510440821030200d070a400166100d40803403d407140b02c103100c16100382c40502560000c03512180062a03032142503008034010b9004180310b1046507400344209952001c0d801080c8601421965003014038000c0c0180a40145808154030300c0e0310317205081103040310760008001c0001d540c4890300c615083d84031034605809100c10b0b11407580075080510440d070845400d10301d4165a254101e81c03d00140503045034480452000784850555880030b40025401180301780300074072240448105100c2a034070800c00081c18010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 164725845 1250 164724595 164724617
    0x605040e03030a020c031c060f081507030f020c0133030f06090303020909040f030801060908060a0905010e060f0603070905130f061b05180d020109060c0215030405030d0507 76
    0x140000a03250819007480c009629103030781c1c201712031942c01070520380381c4c2c503407502c030b18a8034100e07840d5100d02d00b90b44a2111030000d49440b140308941c0c91202140080b040402c5000040c000c83c030a6010280d03010403e44d01514003412003940ca429900c100b0608400d2189a000901c2c446030b11301c4418103d010042e0400491900d141c0340c000742010360f490090482501c8620180030584603034102ca982c0c0710010b00500c0e040c02c26041411004000c0102140492001000480d00d9030080b00c0c520103c5800c9030040025940d0540002c0180c155440221410340d00d6281801d29641300b0301107141b040c01401000d60b243d15010b0100b61a2444030fa0009040d00d20b49030038040618040e424555002c0e4002030a031040c0d840c0340c80c0c07480040101c50b002d035200342802406200c032540c0c4a0014620b190403080306101ca8071510302041050140580000c0c040303103d1043c100080d900a801906100b40000c0021060684280544c13906a1089400302c0784c5420008400740c009045105591b0045060701c0c000044072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 164727095 1250 164725845 164725871
    0x41203081503150415021306020c040c03050615070c17100c0c020603340c05060105040c020715030f09080c1b1c0501060b0a09080d0804020141030a060504 68
    0x110090005485a42046406401700d19103030116007001301030503942982c09907103c0001351924480500d85206a05007503103541032501c6401020f00074030b8001d109001c0b00c0540512010258002601140d0407203c48030002482c1402d0400c00582c0700b0500003034898a0a00d5511000711001c4170340342011300403445600303005a21010162503104c410944000001c4a07004011081c03904030680110700140380403185501c2e50340c0702c020612440c1c0320b4030032a82c15903200e01c2080143d03000b180203140182c0c0550010890b0000010341492500124140045c04800c128400b1066030440c0c20706641c19071000070f804c40c640c07100b080b450310b0251504026141c3c5200c4480000d204a40d10206007407103640c1c440d0314409026081d0f0200700244aa200b40541d035424801020300001c907607104280b03071406002540b00109024034552032056905075210101101261076902d00220444044026030706140d00c5c0308411500d401e442d401d840013003141b050301d901e0308090410660301c29412036401541407400041c40e82c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 164728345 1250 164727095 164727133
    0x10f03020a0e400b090105030a020108070c17071a1b091302040306150608010e043c060b03030c0c06030a0207080403060e0c0d1a0903041203081503 65
    0x400003101c038448039025660201103d030401c05444002c0c56161042c500400f0300b11a01030201c980c0303000007440185241c600f003000201007480f0719078040e04154a59001580b041100e141e2040190510301880440d54485034078400211520038484440025568240143c0603c488407a07401a80030600d280303404103400c17021023100c1180740c50241001c00e00c3c40b0142d981c21841c8000c00c00c00041151901d640381401405084d010780c1d62010b058461101061745842280c407181a42c2c1010a9480b050b02e8641d2585110240008804000c0c2c20072682c2169400081c01e01c10108a000303111403204040600300001154215200b1a00c0395004228641c10024040358102c82510125001c503280d5882e000c00c800030740f041c070000400e141d00c0000e01100b04255684410646c00085040383c001d410107100b840306000d00c00b01c0142083c83c0703800c420358018030354900540d032103035900b03054038100303951850041041b214540c800c501084011081000c2d4800004500c4400314049006000350300e140144901c039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 164729595 1250 164728345 164728367
    0x90b06070519080c01110d0c050405090103030c020a050405090604050d030b010909090c050d0f03020c150702090a060306020c01060e1506120a0603080721110d030c0e041406010f03020a 81
    0x441081c680c8030701072002c0c0f107040d103689091040007400030081c540740f111001d034011411042054500644511710b1481101a94240d032800342405d4040d03421914155060505494126484401e154001c0350740d4031203008890145e05004014119030409180c4542010104001070040519007001408542c0e4450303200000c0310400540062805000c1c10007001010040e00610f030031101002036402001850740c0ea0704a0107020b03030f003a200450659800c105004551701c82c0180e0031501400b06001501d4101c01040e040414100001441c940e0b0384c1e144016a0090001e41d802ea035981d2008110f24204840126844407541ca0718aa2000e070400003c0e00134010428454520140000000e0100c5020b0b400800a15000009140c941301780b0b01e00240880b4a00d40082c00c03a40014401c3c00c0c0042c000c000d440328511000000d040c407180b042000710002c1180f40c018800308181c0709405401a101d0f80318401036900c200c1034480c00340c5010300001d00144c0c41f003190030080510400c500b0303014541c44408659 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 164730845 1250 164729595 164729623
    0x609110a0323061c050609030901021b0a03020f0301020c07140a050402040b1b1f02041802030601090501050306010c060f020703022104150c050d080601030e07030201050418020c030307020601090b060705 89
    0x10b04c181c04410b41489000c01c840e004001e4807551050002000e400030291030310000076070071101441c1c004800580021000742d00036400c00c0c014201440107140034032040319003900c0074000505101d013a5010914000143d07020511005110004015600300310740c3c1100608000d07502540340c94038000301007217184200800c006002181402c01845001d09000902000695054080d01910b81084100c001d5106101360000b4031341e2920991403a45160080d00e105200c1611211607c0d403401c1e00558042e40b0082181e07040006d0707006030500085071441841501c07061a54011307141e01c44e0386800391900029402c00c09400702c0004001c0400f001400417101600c0d440c1c24051b528040c2910203071074814141d48010b16030301034040c05005c540d500035685482a1426038050007801310b140801600c030211800068000b841c10042400741d141c400c135407a00707840740e030030b200514014500000fa400d41d0020344003440182c118400402c6a642140034400825208461946c0f400307895550b401d540d102e01198920b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 164732095 1250 164730845 164730859
    0x3070c05090c04030213020c07060c0201020d0c031206030f0506310f0b070314010e0601090e060a03080c100f020f03040210020c04060f1d01030b0c0c010609110a032306 74
    0x900705008a5043d140299406015940020360a01220f4040d40021460000e41d200700d600004074180300304c1007551281e4040c1c014003d801e800d050704a03030000d090302c4e0a40510200303240b1030070110828420b40d00110701918403214070703000b1441e249040400c0034180c0c4401011060031405055110900310509827105087d409214601d8038046003400004800034100c1c40f490070420624940540041840d0906203800400580e200c643c0018203060a440c02070008440510906c480380ba000401e54002c0740041008290590301d64a0701c0780da61208100c0d28040e00300d210905801101401031068021590f8019400c0c01c1d242d401289207800010006486151481145640a03000380b0186135541000303030041c070072262101d000071020144d6120700e035907103640c039415902804545000c40e4166540b00d013805c8029100c482c0001c6c141d8010480c018186e558524000442c407206103d0000e4003c1040b407155100d62580d03074050121116021003d5215030384110003088541302d45200c0b68040c804882c24 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 164733345 1250 164732095 164732101
    0x30d0c03020c0d0b060f040c080c07060b0307120b0106020c0f040c0c1401020a090602011b0c02030f06161101090506010504110708031014061e1e0d1a0303070c0509 72
    0x22441d0210b09a03403035801c02c46801d0024188008500210320545082d281341c24403108100500c4111000302d5035040001d0484004128119441001000480c2c040c1c0800b241c1e04003001c00003414094a0350107041585100412803003000080200c2c1070040c40b4a001604c1c24821342c030701058002046100c02072280d9580d4240d807504c180204008248290025454100100c1c2030304828000d6000c4104100802d003403001c0013a0582c414040e000e54030808000320341c542a0501e8060741d4280f44404200d905010b50500070743c035900100400351245c17000807954040000b2815014040d580c0660031005240d040c00c0c00311020503c0011098119001660b0014119132450120794050040ca90001c0c10044000144807500300b41950f4007040c1d402c007401c4032044800c0343c400c0010b00e10581080308104620807911080c214002806000c0881e07101c810034885070036040d5040036590150f0488034140d40c1e901c000e080d92040d41124100610000d80040d46000e0060312050b01840162045511410002c800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 164734595 1250 164733345 164733347
    0x4020301180804060c1703090c01030f020a1d040204031b0f0e013c030602031605121b16230d0212220303050a03050a0c090504021303050d11011a030d0c03 68
    0x5042211140e03180415140c1c100308070603527110811101074034002030804010b044588114821610f200c5403035203a244460123600c04e80800107841da00c80c203a100358244030000c00320b4080500320740d1185001800d0345181c0c0c10000340101c61291608910707a001348110040c032640200160002048101c5a1103494205c4080007200c5c0c0200c0c400c00742c2c5044280c000d400002c01405801440c090015040841424070314102e04035003500408229481d0f8820302004a640300e242004100f040e82e505c65600f0346000e8402100110060b501c1400b11015442e940c0c2c0ba070200f1070640c0c0307502074912921b07024000590503003c009540302100c003081440c0860000b43c90644044081d42c45000e641040908490281d50781000780031a0082d001101c04607007440300094155155200c2c80800f025a51101180c80d810101800700035045040b84110b420450080800400c0080020074400b1174a607460a81c400b80b094000c80c03d450108560040c0c002042c0d00c00c194036603001c609100a8402c0340b030813103c0c141003814 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 164735845 1250 164734595 164734613
    0xf0c071119030507150903031107050415140f0609010e0109090c08090f030903100903050c2a090f070c020109090c09030614092a04050c0304020301180804060c 70
    0xe2080e848201040a541c0401001c07511504680c01207007902c85aa0755001c3d0510b41c1c403003034041d030302c00031710441c405000181c0107103607020424034141e08070f41000740c607240450219014408030f40360482801c41e08100950081201100030f01041d02d050066070b180001050703103030041d421281c1c1809048540c454003079210f100c042000308141350003400311020700040a0101b41017501d8803206ca014109200903c40000411500d081501600a0003c083e01e0301c2a17900400c400402141007007020846021000010803000c0d50210895102c4080c4d001c1004c7c803142d0b52461000c515004c0d841050400c40128121700401d42d00c0075030340c1040d1505076007034401210088440c2d048094064500055200e18550008190081e24401d8808205a407035071038480e01007800c02c0b62603441c20342c0b05030386202510b951034041520017294110030902420743c0500080c265035080f00d19048031400482004298130f0309014150804044036000150440eaa465030309252090740614020311070711075000c5080110340c00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 164737095 1250 164735845 164735873
    0xb130503010c0e3c01020705061c0c09050d111908060a0209040902120106030c12110103090311100207150c091502190f02030105010b0c07180e01110c150f0c07 70
    0x1342c00c181240c0014155800c0e41d900030b000050041c4124000440d007802e12200302c3d03422035035101854400c0e121050f548005050604140000c12141400004041d00c8100c1c00484031449805009030344061841030281c40f1008204035580451540420410800d000c18003d4110910103405a82c6d070402c1c9021402038080c0703000c02900140031049040c0082419484501920b200d01c4c8540c01d02941e8410682c5d1500700d80303101030708595505460405a40c0664007440e0080c0c401c0c01c3c001c1310401514403941c00c0144030400701c40c0b05900092010100b0000701d6214040a48082c401c0101c04c130180307001040c41805000310280300400305d81c80111035008114001e6507011482001740708105601e020f841113000442c2c128003175800d00002141d400c400009486110b07c5d40c02c0240308180c6007d2014100481902d0303818105a070b50260840900402e00845042a2281e00c0903075483c0000400e440c070300350540113802c0d1610900402e009040351038010300e64203e4a00d012a6482c2c20013800c00b00c91408000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 164738345 1250 164737095 164737159
    0x40902031f0315050601020606010e0906030a06060f06030516050f0f0d02031302030606370e01063203010603091401050a050702070e04081207090b040b130503010c0e 73
    0x3100c000400c0180c0f854807143c8188a074101440141c8030040103990f101020344072a404903064080001c014207213a00e09a81c0583d008048802c160003d403030383d40486120350840e505d880100070040c000340b034040c01070300e401040c00c1950108440104600500794000d085000300d480ca0b00040c03026601600f07005035130003a22016402c540d01e080051140700e013603450070002c9010740980340003d403951412030160003608030380c1e50075140030700480c0e0f0b00a0300180301c0a14410012a1100300854107407082498117020700a140c41c0e0011008480e0140061010409070540c5d604c600455030566076241c00c000d41b030454031241404901260546011805040c0342c46003042950720341000c002600100390080341c0103124580a83c1c0c80c032504e82c0e504442e040411540600041c0041250380f20541c504408580d02ca501864280d84858441049040a038410f9220807203521020a80c1c0904010300340b4a03c0041c5001c90080050b0514000c01400c1801510581d41c440e00c0b011303804003441950004108159040b0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 164739595 1250 164738345 164738401
    0x150c0801030f4e0318080c03070c152d030b0a0510030c1d0303090d05030903070803031605090d061d0109060f1104031703040230010c03060b04090203 66
    0x40031440300e98040c050b0084036a0303800e05900c154985004c0d00c50b0015240c503100900c2d0030b410741621004003543c0800c1e80300d407a611007005081c0c0071941d6140803401420816000078810f1344034203402005010994500040e000355008107103001ca0291006180c01d6106041c0031800200f02c00005840c0003043d84515000003149410906c4668180e11005c02c84036551982041e1440001d04404c01d9891081d04a4041d44200400441c51030310824041c5503c3c07140c1c00300ca00d41000b4001090400390550b00811042d44003009025a014200d0160711074401c03d8540700e400d100500700040c1d444000b04002500c01079881d88050740c10003d130b00006150441100007840920907614201c0c0082124055075030009181c8001d002c10101007608407030480350071400c003090820031000e1144041d0300141c400c03039002c101034008906420000114800d00c000d0243c0400f0340b5050340c403d1600b0b49118602c174034105803410205102070400d04082d42c0a890a00302d005031282e480311030059a01d00030709800c000c5410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 164740845 1250 164739595 164739683
    0xb04030509030d05090f0d0f020d080d0c022e0e0303090c0a0b070f080c210a11010504080417030c070801020c100b0904020d03030f09150c0801030f 65
    0x40c00500422614100b941150403c1050703030022138a0b80a078201d0aa849500044000301c02c1c54514808a034442c0654900e401d101a140c3c0010701000039410201c131541e00105111968007018801d080000071180013500b020841340658050441280a030209400c10000c40c080546801d580b05e10014902d100841c1e0b41c03410903170886d6503280e1010b000f05205102080c004035400d00e4203070558942541c4440c01e014500070555800140b90841d0040c0a178038803d21062585210400c0d180c0102000c80180e0582e403682c1c0210010700c1d09842100c8418241e05060600000481c0341003141d045070205000c4090300d8810343c144c1c2e400c620407010040040d1041c2d030b201103542601903004040300409401254030307416a0410900c2590341d076415541e8088400400034001d814200d4030940703100e2080c900041d43c4141103020703104039070780c0100079900c0403400b9210780003403140c0d8860380c3d40d80075280c10000b440d0344c59541c0e00070304090070450080801d80948200c04207406041040c00c1d8926600c280654885 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 164742095 1250 164740845 164740847
    0xb1303031d0406062a05031602011b03030501060e040b0a06030209040213030b010806180a12110307030905030706030605060d0c020f0604061a0105040501050a0c030530011a041e030b0403 82
    0x2418001c041010784400481d002d5031042c20050349520143e0080c003a50620000c4040c0c0281c1c0c5500c008c0030390600481c05e04003040400c1c42240400c043d0300c80d80f4005025410701d0001400f46160900040c0220710340003010340d943ea00d0740c440100301e60042c40c025076140141c0c000301d40a80588107040340b184210f41808000c204140c4500c41c103a4040c001100c0c640d0361180406140032010a8920b0300384c1e08400620008a10740140590035500d5508044206032a4030070b09914503408031034280c001580d4604140321520b010700200c4020700c414541440b007107045c4400505180300e600c00d5040913595420524030340900a120015041030000f01f03480541c82d003414100701801e81c0c44000c1c10680c100350520141580a4419a81030300c1041e91812700300144203070141c0300144122000c0c0e0078081c061040903450b0b420001440003205500c4071000c0c0001c2c241000c160440f40680100614603600d0114000c10318110042ea02190740180005003600c03640c0d641038903c8002900302a00c0111003500b000181 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 164743345 1250 164742095 164742107
    0x171c12020a0c1202010b0a0314210d0b03030301060504090b040905030703080403020715080a090c1a0d0f06120206030a0e0618150702061602030c07090b0102070b1303031d040606 78
    0x141d010300030050f00c16456100407400c80701c3d185550381d4880780880d414000702c0d0b52002c05001282d042800c0f18560004c4d500a0142c1d03002c25040c281c2413510008020304881c0d0240105440107809034021400c650500030301524600076030044e0a1406e60b40e102c2c500d07946d0350340d4000c1c815482d00482075a51b21880d07030400900d001e000b02c500341c1c094420007000051140740c0340c0800030042902e0ba43c5401c3c580f01d0412040103010110310a6590070191170307012548401250340000c594400d44201951404038078101016180341181010f4100c3c80e00c40204200c800d0340b2084074a140c1d04950117540e07540d82d42c4946e802000f5900d035620340e034420780040220700c1d00351018442d0b045517401d04460252038a481d80403200d40d01281c1c40001600464003150405001c8040c40030b4204060050701e0130302c2d000c40f070f0140c0f5001d110384c072920301c080d140c520168a81d40c06020901c0640f07100d000c0a45800710b09501d403131200e03007a4800142080303983c119003000282035131100d9141d000001d00c2032001030768074003000b040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 164744595 1250 164743345 164743367
    0x50106022506021b040e010c0521130602160503040909140a02150c070e1006110a1208060a0b03090c090105330403020a09050a0501171c12020a 63
    0x12800c8441003180591107001000e50480b441c540c01007480d80360b41d0650b50b058405030700b5050317005501c450480c03410500a00502c940022141c0d02c80b03031180c1070140c41c410b0081b50300c6400e5540b42450010300c28000e5803074030b1841c50250010310250f510280070410040d41b500e4284007802d64000800d01040c45003130303a0425403003107025408442481d96246a40c0b5265203c070200203520496114001d10480e500e0000f40805009040644850036502c00000001183c121030350070509441400034440030b508056942e0703c0f00d24031401040d10f0100399403030903013400030010004203010601000560035641c215021000d850202150742d242c0c140001140c1e0355100f40c00049200f48000d000101c1c090502c3c0c03065450098422000c80c000c1060042501a440ca84061174085428200004000b580f5039040300f20040182c1503001032180351140c60b0764200c910603004081100343c3c0c9000103102400015a02c0881048034819101501c0040400e44982d1176900381d025040b030010851b40e0b1426001220074031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 164745845 1250 164744595 164744623
    0x603090213020423060d090b060a08010504030f05030c041502010c3f14130303050106020a0308010905061906050913050c04060c08070204062c040b0604020f04030605010602 76
    0x241d01034059100401e901450244900502d001c403441d0151113400c0c0b001c01c20035540580030300d20300018001c4501c1551038000d0306844081c2070905100c11400c00304518401043c0000080244d41802d96004282004840d85481041000300104403400c3d007840881e40142244c0c506101c4507010000082d0282100000403000300341c1e03100d01c554174089201d5000b4800003040084079452040001e05030107910100108621a9588039400548151080c0070140520014000200803841500d402007c8c3d8205810031421500680506c3c000a5042a0414151122280e0201e021365601c4041001200d00707030203450240c844071200186494200c0d004240f100e40507188520100381c070b100d00005482040e01c81d09240ca408000c1080124840c1c3c400f00030706c034480e0300c030a0301c0c21240780c0004099a00f103810001da032528141c0c462880b0703041c10714030510761580c001c8503030103070b28050311440428500101124011a00020080c00407949001145e02840d4081e07420006035844010003591266500c00080c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 164747095 1250 164745845 164745859
    0x6051c060e06090d120209041517031c05181c02011505150901051201031104050f04050604020411090a0b030106020c010207080a02240304110f01110615060f030106030902 75
    0x1850307500000c1a854415641c1c41d00078203450305940780468900c03482c08915081c0d5a401c1c0300c144040c1d07031a80070304920418a141580f95007420b011404104000c13240f81c0603459032007041200108100b1004c000206c0b201100c0015046d035412001091415800450065900460201009040a40085100d400d0055000f004280100d8003000599291802116030144041000c0c801d5841000000d00703c805040c0b62a904020f1444901c06414100381c004403800070030f001c40102a0f051901c0f4869220103c0c00080c40681050b4460a4664802510190050351a00e400000d0740318030004a03205440f0191a8480346992201c5820f0711350028024800113000c2d58a0b071954030346c400258101980c0e002e90103001c5903c025804c204540001e0000d03072000f004a001541c41c00400100038520130350190503c248800101d8040142180799030030002c3c1840f00c03100c8508007400000900d2a8000e401011a00519008200060050081d07140c40e1010007400000442c406a06030060304541d0303c02e0f0343d80303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 164748201 1106 164747095 164747111
    0x1a040c050904111b0c0907081e060a150203031e0105130b0109030609050f16080309150702030105180d09180203100305030408070618050604030206070606051c06 71
    0x100714290001000000d040c280034503011f80c814028500552185441451416500750315070100d00d4030a8048001130032030b101c841d05440a0840700c0303030200040480401c001d50303030380c011240381c116916002402c040304081411107034144c0f003000b45000b04107590308000034010701c1810542410021050000008070303405120b5412440d020750060210700907013040742ca00d89000c8080c0302881d007001c10001c100415002c0152162144200d41c020030044065901c0d080304c2c0a51480698154a0101030180000b00090400342e00310f254402e48102216070041510801c00307501c21130703032520b080342c0c5440f007901915401140d01c038400c584680701c1c480c1c507519080c0c950340041e0041501e6900030542440b4294200302c424150b000b1072081d42c3c000e80d04010210300d05000f18440240552400700d86d4408004254001201921025181c81500c1c0c05001d42a001440e017004160f9099180080c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 164568345 164748201 := by
  have h0 := BRFrame.cov_init 164568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 164568345 ≤ n) (h2 : n < 164748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
