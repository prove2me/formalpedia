-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0626
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:48:24.674105+00:00
-- url     : https://prove2.me/submissions/027d0555-4205-4a5e-91a1-45f3d854c3c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 112410071 ≤ n < 112589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 112411321 1250 112410071 112410079
    0x23040b0711030706110f03040b0708070213140109060510020d030209030c221107050613031106090c120304030c091505060706090b34091502060f160503010b0a03020702180402 77
    0x708086e11091504e0f48600c2c060740c6100201081014086101140200403261026108c0c0300070000f08500c081c101c80070070541c111040a01801000814114003034140030300300413209402141080803000c0e5440e038203003120744281074010070041c01c40d55041c040e61141c0c1c600500718140d282c19015031010088100500038070f07803030310302980a201466807a0640300403950150042119480c0c54001d200b401110010450400600c0966050351040c2800514080d0b103051000304403090501e82000a40d080c0d07480343e03152660040c8004c001090b01c3c8044001240c060803000138480300111201d1115050580105401c4100000d00900704841c903801034000c01d0290b17540908a4544980443d1220181d4510804041c5018101c042c1190078440d0344041e07000c28180855020303610100817440300090181c60f00982c00003030411192180700d0040b654002801d86260100344481d0714060a01e01042c0038054441801180020754a030084e8111004a50010204825008207401c601a44281241c3c12801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 112412571 1250 112411321 112411333
    0x315050702010219081306021602090702011104050d02030c090414060c0a1403060f0405010b120c040302010f081306110c2a220c0f23040b071103070611 67
    0x26610610980d0b6500004003084c5070714624880c002c542c803d4020303080301080d00c11a101c0703800140d240c2c801049401d15008071200f03811007900410203069002070402e019641018800b11003a0312010443d02600e008840c440c00615803400807919011006c242540c2090750035040c8010f100c8410901c3ca064011503040318099519206541d0003070140d0b6034004081885000c0303c0d991f0b0f0f03410303401540d4000e038081c00c40d5501d01d007c80c0006055960a074421040035400180c0780108000311707940c00342e00c0785c403a0f40703914030b06440c660000700003111500089040001e03450101e0140d091081c13110f03032125001801403107075442140d5081d40078ac1c08100c42d0102032140760001e81a6600080d02618240c05020401c0c1c51145c00d80e0a1040b5440d2410301842c070102042c0400c0c1d10301c0c0700d6100380c0701c810403155280784c1c0b007070502000642003000d6965002040e007580c44e5001c4855404008036025141004040d03034550b01c0c1d9240c25010070403003005003a418066094080345403984002403510f41c504e11401c681d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 112413821 1250 112412571 112412581
    0xe190f020a140102030f0a12091b0b0304080702040b0102100e15010611061b0708030c0706180c140d060c0809060a06080606060f0c070608010e060913030305100b04031505 75
    0x1902c02c642c41c5400342e0010f100c400c0e004070242025141404050030144016480d03640c3d01d80459042c0b00084613207030303c2c00050102034500a200113014061625045107181400e846060090060a200038480d640f1400c51000710b034070911a01c49400513500781440300e1a200041c2070388980306e212480e404907560314000a0070078407500d150036409001d0809881c40e52510340c1c400c494000e00030304215542d141004640e0018013000c2c0154854041d55190a499049a2074008155800a40326031031200d1201d44c404080b80f04810303050111b07104058402d5a03150220042007922014038406442c007031500640c0100075070459040d03441003014106940ba030361391340321100084174924040e404041e440100094854240f28000b4014101402605401d0081004980349011a603400c12000140c10400400481a4812400d904140200c50708001c0d0324203803418441d4090600d50207401c05440e50007113190b0001454030407000c1c00c50454484c0c1da554990400c1d81030b940907a020000d071640351030000b071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 112415071 1250 112413821 112413839
    0x190f03110f1c032f0609010603200118080a021206131401021210031a0103020d03080406060315090b091603030c0804051c02040c0801180e190f020a 65
    0x800c150040600907001c0d11186007046800b085031007242488405404c018141c10482003d5034003481442d00a948074040318029810041d02510342c1c0010303070500505100240004130044400766484400810400c250340040b103203440b004103038000c5103201c9000440da41c5001b05109084900944e107440030708010f4101c0c1555000215100300d1a081c107407c10070001484a8006213100390713507100160404940b03101c0d040100302e0540c0c6542d40ba06413210200704001e9040a00110213918a1501d040c561458000c070b40030300c0c0001d200608010f1071f04005820445554408409590090110060303222020170303030340081418441c10307240c4003a4400080c441900c009110a058001445128074843c40d580d01600c101c41c1160301205e50308810b0102082c2a110b4a1205594040c0303800040b5281c45940184411116068026130030800540014000c00444145206550347d0030307100040d0007203184a0583c2850355180c84807038400c9032342c0510418045114840f4411600813281004416950341c902 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 112416321 1250 112415071 112415089
    0xa21050609061f0309020301020d050702010905071e051203120103030306050112050c070f0c031205070c0b0c0a170903060a02030f130f0803070e0306041209120c05040506190f0311 79
    0x12080014518144400d03c0b4481d400c0413140c544007030000340c20180064200c00c1600e0044550b040140c1d505d90170003080c03240c00c01440d402884c4d2108034585a422500b204c5001c0300444c028079028107043c0700a5040040d080049a49200402a00d201503503140d1400402070300c01441400d00188200100c01c444505510480f8011080000101c0c50208581c0e03620308139442d202400e45030b10b1032000d0b000000c19000c95080200703215550780c0540d03454841c90682000190740e0000c043e298018000c900001740001140c1d10680e4104480003101c01d03440081c0348030741c820391406a40500404092011400740d80e006540140c2d0b580c040110f041e543d181c42142100030305030300034017501520000000410a840300840c0c00104614020145585030320109142c07075010386d002c9072030881285502c2c4003c1c0c2e00803908406401880e000540d0104151a503070050010b034014180728903a03d1001c41d800b40c0d141c1c20b50303070051103c0090242e2047c0d59070300300c070a0004d03c610007540d240c50400c582c0407103032415200b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 112417571 1250 112416321 112416349
    0x405100e070f090f0b030a05010b0907030e0c0d02060d1514030c0a030b041b030f05160501090302060c030c010c05070b0105090c0403080a090504020c0304030317010312050a2105060906 81
    0x20035100c00e160810340e03c05072410716014840599178070048402170303d050250f4484180540000f04441d1110f006020422100801501c1014640034105084003000305070b60905500842c0c10180007152400014400d209404c2800b111910705000e040016094001990444140802c4441140f59480a041c1c461209085042d0b100401c22014800100010701d0150418080c440740480b078540d8240001c4403860744d0300183c480040b000001020803404120780c01203501e1182d00e000080d031400c000a0f0003c84c01b808028855400400c0c281e4012108100f80d82d03002d91001c00074015507060710300140041d404110300365000f40f4403200201d55400d00c2d03c0c190303000b0030a0300c040c2d07442c091858945143c1504203c40c040204441c0050008080e603071070025100002c03042014607620361652401402d080d907030103c0c1d0f1915020003001040407404c946500400c00400d400c1041c0d90700410358040790001c009404c0c06c044c1000c001d00c4e8034529145c030b500c403c1c0b1902e4207455114054440d002009221142c000f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 112418821 1250 112417571 112417589
    0xc0b040e06060d020f030a020301031b0f05041e06150206160c06021b070b030109200d020c120a031e0b030a02040e10020d0f0605010809060f0712050405100e07 70
    0x1c6840e42c2814401403c49004559005080c1140c02600e002280d00940d1502200c1c1c2e008070043c414000303524131084a041040a041c400c2d6442c1819208030300c1b0107485030074451390b5220400000004c0c40005829245942071003001007640340c00000c000e01e41c260714010010310401d000120074036480018115010311070748a81d46400010340d05c0380040d62240c056410014020025903141d40010040040500040c00213203813a98109511042103440f030071009504160110440800301000c8811141c0e100001000543e0307510b65081614a4800c4410f41c003a142c400014004040652561001171041403c41c03c4201d4030909075240301c00d42d100c454880394140c02021042c8014070303296010124810204080d24018450b50102e00c089800842d0814611a228158100408050710078500a00001d0801e041e40342011f804156850b80001d00450810606002141c1e20328024520605500950101445a850140342864031200c010400349038483c20180b900b0003e80f000300d802c1c410344d0001e034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 112420071 1250 112418821 112418849
    0x20703080609012907060e0d0f0c110f0a0f090209011b111003110403050109021003090b16022a03010b01092702041d0702190b060121060801090c0b04 66
    0x50500304660741c43c04044e041c80c040c1040004001585406024000c401502c09005d11243d80c10f8041e040c28525003040040000000701c0e0f20000703039030385040d0000200541d903a441c1606a480415070441103038006034180b100128002030b41100740e80007000140c43c00eaa401d00c69440320360180c80c0009480e04d0007002d03020403100015060800382540e9030f0f2001d03549004221203100b480842d0817039000e038105031070994590703030400c05500b0602c01941d86030101d40b030104140011034649079a0b003d8003810502d1489100c01c00b004c00303180300b0010100599040b219000701c0c03141040729100d00801d0811842d009500340b40720152a0360180c1240400c54840038400c80103801080312175001810070b6242e90351020340c2400041149140c032102003001c140003200d08002030801c01406071034410b88840c06800c0c2c80400c041e150006e0039510010380c1000d400c3c01c103504000c220396260182c0c8040b2042915500c0d10703107503000030101c00c15000805858054034550103c0d5442d505080074910890286820008500e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 112421321 1250 112420071 112420109
    0x901030b060109030c0f08300a02120a030e010f050f1815010303260c04030201030203071209080a110303130b070c0b010b04050a050301090c14040e07080102070308060901 75
    0x151415074440340500d84800110f440b5510020b0401d0b85030894440350300090428400b07c041040700c4204460200c22541104042a03805000141b8820301c1004005010039404c82c040d00820004044102c00103105495054401c0000c0007480d856802c450340e03609008405c0460720140c81490301600348c0140840360f0760b0b164100c0c0c10b280721525541400a1203a1004140303c6a4005401c5018511940d505100c400702684030745042c10020480741c1c80d101e55142031000c05a203080403070f0201c0e075087c00c0150316075071850b00503140e4030030458a01d1070743d03401d01250608210030174004000358406502c450741c0903401103104540c1c03400211080188400e03402c000742c02081c8051801c40e8010494035029201e030440d5a0759510004081e40446504180030509020300d107481d580c1e210182005030001c002d5092580c0741e01118101511035440039a401c04801e0a0342d40f1190443d90f8074081c1c2104846205540c5e104c214000c2d0322050b400d400149040021448514002d03009a04954006410003618811 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 112422571 1250 112421321 112421333
    0x10090b012c0d0b0739060b090a06060311040f170c0d0308090c01112a0613050906010c33060e07080f01060203120a0204031a07120902090103 62
    0x100391410007004007041542003207592541600402d2511501e06182242420b0801401303030a01d0202107054007602541411100100450f441c8480001c0c90325982122101e042241c000c12509051a410020590800c2070003055600700004a4445941c100584010ba140481060080c0d0040007840d1001d400c04002000c00d05121801d402e15910503104408500c9000551400e0140300481c0070030190410068183d00c1804090703446035003800d05890300952480921780307820f004000c203011948401d140c062003851084203505014005031225540301c1d580341c601c40044006214840c4100081000184554490307846d58565981c0220089059951500540700c4141a4a0400980104448401d5108401d4080d05004104100b500005410803c0700284440f6008020741d81207003215004014840d40001100c0c1004000e42c010031300f42c1c0312103002c10084d22a84c0d101900c81d602503021000d90007803688989005541d10348800000b08403400d0403e05490700707582e0103540804498010070101310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 112423821 1250 112422571 112422617
    0x6010801050c0a03020d0e07061805010c1203050915190f061409090a080f09031e031911060c1b0705010e0108060118030c0503010b120606060f0f03090610090b01 71
    0x10301c0c160100f0840381700756447d458101250b12503030000d504031a01c050110412084580a8102840d07e9010501140c1b40da1800e407003140303000c208042e51000081c92001e010300000d90700031071141452200781403d6100002040e2100b103814460340c640079601c10110700c0c03842135034222955421142c480c12001c408010710150028410a050702840c40303107000107001c240c02015a000f201d40d4881e200c00202003070510b001c004490591035941880c080d140030f038a001058640c00812010b0300a600403142d0012200ca05030458024414880d04040c040e0068004020705181845000c07842a041019a4001c0e0313107202c640315441c003244880e2082034165214040d15540010181017000804500010300f1040d4142c1f80d000b5600030f868888180681d20f070030b0003223104140c01264100c0300c2c0140b0b052059150701003c0d14981c4100c1c00003405298120202095514120301b068280c1d44034a4000416501c8140490300c0890a00c1d0600d0f0101c1c054489110316400c1d4a41a510940e110035030302440c8441d42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 112425071 1250 112423821 112423837
    0x60c0c1509101509091a06030102090d020f010e040f020702030c091006030b0d02061b120f0d05062701050a0611030a080402060c100b0f0603130b040213060b090306010801050c0a0302 80
    0x11200315000c20031034214000e17000007501c41c1302581c070740d0341c1d00004c103000100300079004a1003030b401001030780c06981c1e8a51000d48600e804075140c0120004110058610b4184c80400e9900182891000100300101e940135040a900075010760b45190805010003261200c01c441c040f03580c402126080c8000c2d403090740b00640120000c2d080d5100b01d0038a8001407081c0d0010489038a0170b5008000904c1842800d000341c0c1d01c00c454500b4841e0510312462480c103024060700270107a07078076595007001501640d00c2418a603e40044100380e22448042c800c0c0c45501c1c10000d0190074000d40d442c1c44001a02480746c0c0240f02a071301100051402d008503040c04607140d2a0250041e644048180302c40d8600d060140042c211741c00000c100082d007054110184401c00f00110040344c400c0c4000c1c81001280000891880b603030b5507100c003410759680c1e544c0c0300084503d0460501d108249140181c00b058a82d4038800500c2c2404d022822111160b0382c81020600b6240211100925a00140004080107002e600542501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 112426321 1250 112425071 112425101
    0xd06090203010605060403050105160207060203040b130b041e0506030c03010504050712020d0e010f020c030a050d02040306110c0f010e1c03020424140a020607050d0b03060c0c150910 80
    0xf055650000540640081e042641c250b59180306010038030402e0307065440301c040240082e161311440d281001c6d44a000714890b82c1d01e040c4000541f01140d40441c09510007400f040712406440f562101000303107034508540c00d00000c0f000b030164046103601c2d042003034078441d8460f40d04091450b0301302401d000151034064014400d21504a10800d05107a060000d4180b00701c086000003811000356241c0c50030351751940340d4000c0d030728810028074803e08000b0086400e104000d04045648802200c1c01d83c5c0248282d03800544031074a070131803020b000c3d02c502d030003041c00ca0344607021501042e24500c100b900b02c51000300305036683c0e0b1003041a00101003a401a4480c81d46840c100181429500c004180c01c04c2c80c0c2c0740d1740ca004e462400c10f0100406400a01c2041c4003c2c82000090900350318007006135031900003801d06810b0000200e418400035031550011160158080e0544490342400001084c1c1600703c0c04420b410390089481c0308a111681140e828441ca86c0350b0000d125200c1000204d10090100c00d020042d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 112427571 1250 112426321 112426331
    0x6064a040209030f01050a06050609060a0f180311040609290111011505090714090d080d0f05010e01051903140307050601060c120306060e010e01030204080d030509100504020d0609020301 82
    0x45036400c1c0814a0000203113000410241f82c5030199004072071085e0000d61080740140076080d0140c41e54815200d140c02c0d1420035001016003404251a1900c01203540b407414a1902e0010041000c04032200400c42d800ba2800e000e0251189a0881903403920407800c106245014418a91128040c6c98000c0350078043c18020740000c03c000e8240e080d00c00d0726108021640084030100264100f1300d0495500c0715051802d00c410310b02201b8204118464401103503c9507000c101c86c4020312568104071841803030360b074034100a450b42d03039030003000500303000d22907600c500001ca4000551030800d030010350030540c0444042d0412904666860545201000d0068958403040c0303c040c0000b4400c00c1110302070701c1c06445d00d8209141030303e8003c01e421104804c1004240c01c08004100a41e00079203510915071007420b2025401c2d1643e00124024060790740848401c0c4221180c000b503072505540118000d161b50400c1c0c40f081c180b80f48640043d12030035074000750030001c09040e40780443c400c1c0c0d02405040c0d20007400450 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 112428821 1250 112427571 112427587
    0x504050c09010c0c090204080a0506010902091315090c031514030307030503040804081207110a1a070501090b0106030905012003010303050304050111030a0e06071809020705030d06064a0402 83
    0x1041342c01030b4200c40c0c5503500ca27807009000d00004004807070040524100541c644040c86004c03624a010f400d480c441201d46842500203c428120301304400350440c10000c101da1490444001c02070b0801c0c6070000d030307075400600c404203207050601c0e0000c401c820054011882c0200c0b0b95000c440a500c0200181c03418502444041140f40c014009010349005212101e0f03201d2040d4106042c014001110b80c92142c882c0c00b508100041c0d6000494080328101200c3c5034540e00c250405502500d82d940d8001c04510400d0004502650903a10800d0440d01440007042040a84525a41d201c00c1030294021400002d0004000080c480e00056a109110301d00101d034000030205486260740040e1003451040d80c449a5085143e90b00308140c07a071044581c0b400340b04485c600c03040d403d4880418001c2e10703011a000a00101031000c200107c1b9400c4000f45401c00082e981c842008001e1509100300c4229505c1345404481c0704e4008001040c0d2034202003101000c0c056030f8808214130000800f1000343c100b502842041c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 112430071 1250 112428821 112428839
    0xc190207051905030d08010e0103080922060609060c08120402010909021204020f06070f12090833070909020a0c0b0414060610050d0b03150901150504050c09010c0c 72
    0x42942c403001c40030701c58800e0422040504011010070442c0400002e000100040b81307007401c9040c1102e0300a0210340d80c440d8220007040d03528214500d5000e103029940382c0c03190688003650052049502c65a280c000c01a110314040301c0d04480c608020780050385c1404080030100304c1001440d0001d20505200e00515642c2c02e42c60181e0f08021080e42006050303404101c19420b103e90310890039030302141c480786032051590320300940c4441500082c041c03001c2c04140318505801030340040050101c1100b20b6a031202c026542c18002c4c42d03010106034005541482c980c1e504166100594001e04294845011984c1040074500c001d4112200500401102d4a89200890140c181e009d0107070740901404401400384030041c40c0342500107821180201c4020390702012556211080d10140d61021101003803440c140c1c000289041040f8401100d007204403c03d00558020540c0030030040428901450362582c2d441c0100030072200100c80407040c4180401c62030b403d41d8490700802d03c019108420710304e481e54582c4551 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 112431321 1250 112430071 112430089
    0x3090a0602061f291b0a060f05010e0c0702131b020d020d02070e090307020312030f0a0605062209390509101e05040312080c19020705 59
    0x440903812200a000f86080c41245080c2401401d01d008000d041ca00102c1019000c8404901030740c4144109800700303030040600440c3c1d41031340103c1594507a0050b01c181591a42c2039050100d804501e4a404400081c8041c002d05049484400b51a01950f0345c2030200c0000f544038950880c0d001d10a070170500f40013000c51080301180000c09038210540202c01700c3c082e1404049151080565000f130000e401e10f141d001a07144140d9007040140810398540c030000900c0c44c080d215000358940076111464103c131000101640c440c0c00340d03144480c007a8403560780c41d004407440760045075041807003000880791143c6294a5081e00100310802070b00c00700d82d204402c5044403600001150b480100c44402da909910007070305281c0003003005d842070b0100042e022018206100c4c1000b003074007650900d00d041038118001c04541c54040c108608802c001d08440034000c105501500080700d40c003182a07041044113210b00c46542c071802642c2d02d50b515001210504c2001000300c00342843c11407080c0800466561520209 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 112432571 1250 112431321 112431329
    0x13120c0615090504022706100c0c29040b16050a02100203090a0902040e0a0903020304182009030a06150f030c1502190609170720120a021203090a 64
    0x300054909203881041078140c00302ca810b054170016010109034800240640071f4100008030761044514400704000d6807240c0c01c0d1b903000340c0801107040b40000c1600300385e005910046032a4144821010340e0078100c0c516400b890064502a440c10b101c9802c0030f034480b240440ca100d0143c0d08481d06641103600250074010035900c0040180c0002c1846280381c02c1501c4d164001d000c910b9810340c106400d02d01003100640d4002c2503010810340740c01940041c540284203c0300039001d400078084600303001c8000341d006824040c2000d103201c3c42203030f00030924801c01011ba0b80f90031401006441d80e2120313505e034080500101d2a01541c2103011150000700c82d00c04542050040d48240c9680c0340380c51902c0c84a4260f1903100a00900b0354202c4000c1d410320b82108110100c1107540300c0000030f1a041d80d401c01030001050383c03400841d803140004450303040c0126106056020707620078500c007105840318414410146800c4118400315131004200000520b01480e4001c480310120302103e007031003e090300103440880145d00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 112433821 1250 112432571 112432589
    0x601090f140907030203100e12090103091218050a0501020a0f0602090307080f01051302150c100c0512010503030405010507061e050705040f080705010801090c030e0304150813120c0615 81
    0x6070030811800c0900822001500307d0300700304241080c08010720385544201804001ca07000008000c44070b680a0342c40003003e00c1e0001070040c007a248180006c1d151342c80c0c2e005030569904806c0030004261030100c7c0481d0640d601039002c0c14a411281e81c2d00d40d4540c1c1140c60842c0c03061740921a080c9640c604025000c01011301c00300400007626580e095500b1200c005e01003840c00b8042c0080700707001d62124100d509030140d0342c84410ba520004640703110b007001004148030a81d582000c00d240d80321580600503001c041c0b001501c0c0a4241d036250f0415540f48903070b104a44c08104140203410105110340c2c480c8003111042005010309800311924001124412240c00300411400314043c440c0400d00780e9148090010700004180c4181000c0002e400b05d141407280a02a0351983d0510409900c01d40280021440c400b0440e81c9503510f84842c0c2180080400340200013505200c000b0380c0c1ca05480d100402c000340c0005007118021030824040354500640b41c41a1262a110362034409000c00c1c40003a4001001c80c48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 112435071 1250 112433821 112433833
    0x20d05010c0e12010b100f2304030b1f1802070501050a140a061a1602030a03030c021203011d0606040e100e0c0a0806121203040503040519080601090f1409 68
    0xc08203c0f0040c01d202001c02184e03d400c0c00c0003002e44600950921000c5241002c120742c54124000711840050000f0800e4500b0384111407a428119000240c02580c2c810411038101c4d90b140c800c05000684c40d0080c6023000501d10300c04000507401c0e000c666081100c502c2002d07103000e07103649507075094400036030b0034550155a9000000054101c2d0b2130450b0400800340b81440401d280c407a19030601108599034140825001540605800310b031400e0405a640c080c0a4600d14542c41c00c0c06002440c0c82d50560006d4061000c141c40c95050070001c07079040e50540c2da00c2414a01c0a05070b900011080144a40d070407280030003004c5900703045212124404c0c80362414148020342820207a500004000d0920106c0000511100800c2c6070001481e69000005407200132449048110142c60211280002e50040c1400002c0c0014002e000c80108192181590880d0300c0c003000e07010001d1080c88501c180110341d0800401480104640c0e046003107110f198240110304804000a01d031100e020a81f80106194020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 112436321 1250 112435071 112435097
    0x50a180b04060e010c1a060a12150b010207050105031f050303160521030402090405030d0906060503070f030b010306050603030706020d020a080601030b03070e130516031502071707020d05010c 84
    0x4206071642000a18100c030f030a0790320765100b119001b01da07070046011440c500001081600d41c107201c200100000388007940403c4c136a05001c140340c481900c03a15903460a0101130082540002091000c40700103075034080c9140e660322a440c1c961252400305410340c130702c080b40003e6036583c204044c111942048a80c00440700052600e03c0ca404039003412580d414022250100c6044214010f60741d01036016100d140c201c0d80c45250581c1075114100c0400481894603280b20184540c6602401c00c5d0b54043e8111a80719842c1c0030003d45001082c03200500c20505800180f001520903000a41c1020021741180d0034140709544240c140d8215554500405501141c03c0356203c0c0e012185035041030007030a04110300044040480d46643d061700030a802c8140440c04100c044014940c1c40802035040720039106005c0d03d0030540041d0074020f101c2620f418409404200419086200712200c1c1a88409128041192440e403544250810740d8240e900442201c86400400c0c03003800307800c60810060380d510748c9030500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 112437571 1250 112436321 112436327
    0x12040503120717041e151508060105030d11010e0d0503090105070806130b130509030a1103090105090f0f030708030c12070c0b0318070b0a1103120601050a180b0406 72
    0x10948002c10980c005994003141403d110507400c15049404051080c0e842c110004141300b282c4001014450345c0f080c5881400c1d45544078441c200d039000082c141c00c0e40d652200a503140001c3c010b07964507401030780f00c604d03809000350200c1e641c0d0b42c0804000306006460075105030914030300400040200f44004100071780ca500038030441e40d00040d50700340741c0705905101002c20088400c1482002d001542e0701041c15540da03413040682075038100c00100f0b1100b0300e4403040c1076899400c540100c40c040345501c081556400d0707011003a14542601a035549003041c10309400c02032000c1441000035009141241c21580d55201403190b040a490780c44015075403210030004103880d00003011100c101c0b54509110b00300000340321181e072b10100c0c0c5580031b0a644981740c8803991009040b5106609810b44139042c00020803600040c080c0100414a0300c03140d130000124247d481d10783c49040e1002d0f50108001000075415801100075084200c2c0d03134603081c0d110544010340c865501c2c619421607040c82c0c00119042001c654 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 112438821 1250 112437571 112437607
    0xf1509140604030c080d06050301051005040509060103170307090b03040c0608060109030302070b0c1e0a051b09130303020f0c060103020a0603110406050a0c150207060b1906050705010212040503 85
    0x41850003001e452415031001041ca080c002001070500200050903422500b1316040f07c4060400240204100d00f0031a410000d200801d200b400c0c002c50500000520f01d0310301180e024101e82d00980c2006490065981c408240c1d0f03c020224002d01060390000708140c0f04c4003025500c41e80c802c070291800d0508050380079040540007083e5a0422850a1003480000c1d0301043c81c0044940c0c049403683c4a01071400d0450500c1801001180301c2802080143d000c51000281710740128003c00c19115181880310241c0d07008102e0340d00c2a5003003044070000c2201120744000340e0107614020b160040c10724110000c10044c1e41d0115000640700c1d03126000500a515118414800901c02400e0401a05000c1c3c071100711306020310700c140800d00801046144025008000f4400343c9607200034500502400d69284000035040100e09680003071511212007a2824108103105006820340c0c2c0044860b860290202c50513442050100c40d01d54081c4142d2505803640204640141e00c034a019507218004c000c3c0e0240800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 112440071 1250 112438821 112438853
    0x2040605040204050616110603090601180207030e130b0604181d0604120c05100204090509150105041505061305010f020304030f08070303020c073b130f1509 69
    0x648100001c11070760317690f5011600007490030201540301d00070300e00348070446220600c00580c1200700002004480d5402240d801c0c10b07280c61001c1c8000341902009250128001c00760010046184030108807024a402081c03000341c9034480c0c1000c5502070400c1c000c030703019030041d600403a615206100425100300d107900421801426072038007031452090340f800e043d5807014040c1015086005018030700c055140304115004803144c00c60304440e824081c0030308440080d40140300d0b80d0b110b1458100403500501001c158508046070b5010b40b01440d0742400c081100034507028503c0e003240c0200b8400000c558483d640075080b081c0700300c1134003504980350100150540007603a40314011904200001d0000881a01d1041d8109810140042e03c41c21149410307070091180d061540c00610407031070001070956040c60082e82040da040700048280c00010046204100c0a400034005c1804010018400c410045084070025000300c0c2d949614050645504454030a840b11360031605440e0b4141006004402640d24545 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 112441321 1250 112440071 112440079
    0xf0605010f05030f0615210402010305060d0b04170c0f0703030917060103030c1106030a0b030c0103090803060607061e05060114030105010503041b210b0702010606091206180f02040605 81
    0x343c80d00415119041304000d01c020301c03c2c0e41310003081200900c0c0f00140c807400f400c00300c00000244190031346050346620840e001ca0020b4100300010301d8a04005580040c000e07072108880b011a221503030b03115070146103103203a1012043d041c00b0302d0640c0b060402038440706505480103400190708600740100070303210f5600244204040b030400505d001100040041c1140e41500e001020241d103032030100f8905a041034502c2e4420008010312000348403e60000100c0001102111103c4100400640642e046881d0123400b541c02400003940a081000c010a10a4414030000407400744940001d41c07000048100d1813282030b510820054a960000030800700c1c01e0304c00b02114195854000002c201e0300c0004d000420741c01c00c06500280302c003060701081016100b00c90032444000c03001071000e102a8411a0300b80e4080354144c2c04154501d0062148a05480a81d6a0342038418103040b584542d4101001e0308940d0613960b00f03144402e81f0b01c024000f000f1544140c030080000b44440c010401543c40c640c02040c03007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 112442571 1250 112441321 112441327
    0x1602030111040324020c0d05130b031501020c040c0f0305060303040801021201060e0303070807080904060902030106051e0405010206130314030a0b03150c03190204031a060901060201060e0a1109040f0605010f05 92
    0x3e03000040c7e1382c045240d49103440703999000600954015480030741d20400b1820000f00c10320205281d040e03050b11540c002a4211030001c80200200000d50b29030300110703404108038030b2484440c0c03403282d0022580200094112407400c1d83d1a011a802caa0000b0f039091140c408080c014002e15070300c4a140a280340040b8015400d043d21a02d4030940384c071420704001c044a20002c1c503026aa01e403508018024540003804548945e950540506079902c50810340420340e0700b10518007090b40d1a0810341e401d036801a4028803065407101d40b040f07404810304000b9000d0107903401c080c8490700c05980003540314104143c80429400c14400030f051a0080c010f840c055008900d07030030061018140d1054a42c040d40c1d03a0345040c0c81c0c40060500000034842c540014005840c0d1000f0809404080c92a440c05070200340c40044c3c65070303070310340040b07080f9040d5008030b0b01c000c801c0303502182024074203030400c00c8581010480359140640c2800008c048170003034181442a1622100100306540c2c01101d2601000514201181303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 112443821 1250 112442571 112442587
    0x111121e07121a0d030f020705011e0c050a050d0c0b0c0711060a03060f09020406080c040b03070e01050405030105180708010b06091c0f1b050a0308160203011104032402 74
    0x603154045102d111a195101100f03642940c0d100010510144042c0100248001c1d0b4140184420002d510802c0903101d064800542035101e964810000f1540030f4007030300007451654044560205445040e12240304006114001c01d10501006260244980710201e81c031a09140071030065600605034504018184802c0010941c200d0301010a41c0d01107800d19510f00f101c18069000705620340212050088070000480c1c00c00c00e039801041501c2050b1580e451640d122203807610184214020990b00300c0c01400403401c4103024241900f140d80050500c6e85c20700d621900441c0c00c490040b64a5080c401c0311404204034008180940070180000c031000b8000d110030000802d12510a0004103030162024480702d65280b902560782041244d0321060041c446038003403c100c8400010031002c40106041c1007800202440c040302d0040c2101d50201c2c034582800101665003201101c1400b080e60995252414100152141c0f0f0003032001d54424060181407102d0300140380c3d14442c070181040074507481049800c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 112445071 1250 112443821 112443827
    0x504050702210d0b0103020a050304060c200606030105100807060c0c051206160e0102070b0906040819140d0c150f0f020705010b040908030105090403050910120509210901020111121e07 81
    0x6542f01c2d42140d0003241503801c0f84c030105d0306412010381c1039007003403078060078000c1c0c150f800f0629a00605c004c400a0000380c4a20f042000c0d4420141308003400c40e481401c00f041068043d9800310059400b07a240c010380c0b560740b040441c6240100c0321811a171500810b0800c4680d83c5a5010603d02c618280f900191400241c40080e603503144600601c81c0300c4c0d20201e14041940d40301403c407809004103005441d601400800c6903030078a04140c0c011905140c40703a0032a03150203000280d000440007603a641104545094950400341c00069448607000745c0c4841d09140c1e0300c804e0307005800c44075403141001641c0714401d081950840c0c0909038401c1c401ca0814000802040001082e00e05407941290b100e4a5a12070745801e54441c401c50030000e8006841446a00405400155460103284509014046035a4400c0c2c2680c41d80f4600301c004401e120415080c0305240305440203854906410300000410203080030a1500784d410440b0168072400d4040c007003040c0b5a1010884a040f80200c40300e05150742070982c006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 112446321 1250 112445071 112445077
    0x50702040c0e0315010f05120a060e07170f030a031802090103030206181f020306032803030c0e0d030e040204120b0a0e03030915061c0b0a05090703020a0504050702210d0b0103020a05 80
    0x700e01c0b41d814a030000e220442c0912440c0c5640768861800c021020f0860070042c0c580c0464032841e0500014503d180c1d90300c05012480d00880800a80590b26200350080240c0c0146110280842e4812d402192000107884201c4024042d501980050460b032030030b0b1030000716844a02000c51100d8008d4040108035210540c1e80942031008800d0168580d0345840c0464540340c080900c1d4401c010b161183d12100b40c07110001d0814060007a90140070350795884a0079641140041c8405402801c200054404a4840c0d820b081c0308040091000d46400c0c0c0d555030103040b00301078482c1a125288600280b204060407489074241e404a07000281d800c601c1e01320a25600d40a44108804000c8079810001e480c1c0c0d0f903008c140300e400c0204100109210340007818002d1000b03004807080684030385040d000c18200000014400704503940103041040c900e04040c24032014040c050500000d51041410406034440400d001900d48403e1030051500c4400c0c11051000b0794048040c0c3c54103152041001c800185e90002c12 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 112447571 1250 112446321 112446329
    0x20406020601050d020f03060103110f0603011409180706090801140903040603051b0a0c0c080111070f05070b0408030d0b090403080105060a0e0301020c0f1213060807050702040c0e0315010f 83
    0x400c400c0c4c8030f01400461110605241c0c0c417540750049000110420641581c0080440320545c4c1c41002e10031300d881804002e00c030070b0041c00d0b20303180b070000701d401c10340b074850b03640d65001c8920007192003181004005203207041d815812601c0450055042031001400900c101c10074021607008030300c42030074203544440d01c80c03040f07006001c00c0540f524001111085001056101c0f20242d0355083ea0b034403d503100092044c8030380c1504403400743ea00c3c000001d05503014069108070f0300c00000b40e20b103401180c0c2e940303a048100c0740c0340803101405010400203158800c400500024142440590b03964003002401c4c01c11150729500c0c551040c007094091001096101c1d440a040d6101550000d03590f5800340d50642d41d882800e030519605600000d1807522030b820200340070100c42c1d20003040303810001c000e42c2040650300440800441c1003e15960030030480c0d100b84440307608076400d03040ca0343c41c0002c1c44d0003050603a912100d0b0300c00881d50346940b00300141400c02c107002d000e10903000c109000d54185589802a25003d1203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 112448821 1250 112447571 112447579
    0x3040e01152304030b160e01030b1306060905010f031806020c01152702070203030d0b180f15010f0e04020906090a0801050f010e04080403030c0c03050d020708010c0302040602060105 80
    0xe440d0107014003034000c203030b08940c03a684807000c01849200800c016500034003003100c0040170503003c503c02d2803405000008141d83c40d121b10540c1202400118010078441d104a5884003241d9002107041c07000340b0400f8080c00595644084e5581001d0000d00b1290041a00d58101450301c0d903040302003038041d4802543c0c503600c11030250f522500f0f4803506005d081161072001310f1050403039000480e100c042350b0300348200c8113124200c0103440b40341082008a00480d0f00c082d405410410508e6403540941c1d01c00c80070341c0c1004128595035030441e640b40300402004c4034545988101c1005114030b1440c0c16078040e0b0201c1091800030000200840700400a140c0c07945031901951700412280300d1aa00c0030140c0e4007558002c1c00c00d148856490402d140030b00025210508038005900c0041003810941ca80180700d20340102540346400d241d9601195008604d4506031041e03444207001000080041c07145004003d10b42c0d005042c203038244421a403c554000c016901410720402040102580101e120390448608031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 112450071 1250 112448821 112448849
    0x10c050d1202070506130210051305041812170a0501080d08100803160c150c0b090c180604050114130e100207080705010b010801260f160501020f03040e01 68
    0x1990001c0030f8050550010f11600401082020003800c409040401d40c2c02203520390740b52075040000b036545215510101410b080d90b40811b02c40344c100381d009100240e020515211020a16849032101d8200040c21400015242c00c00c1c622200c0900c1d8007030b6013140c00302d1020001c40d454481c40556851440a068083c00049000140c60721000200c04005240a20541e50340303100135520310206205c070110494060094401c0429404840c0da445007206140f512194022411500c9a4a0f2420000c1007010346101c0c1507800300e01078a800b005000f103072903008c0d80000c443c28003000b044181c0e0700c16003120525244855003092a40d80e140048000e03114000b07400540004101401c6007440d0303204410040040c00003c10700100704211008011044c001c5000304130350b22040d0b00444000d407081c4104481200c1c0c001584044880c9048028210982c0e04101c07a410042282214144000358142e0308800501ca0801c1215503018042c0b8441c14480740d02071031500f410090fa20103080810b028206805d1008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 112451321 1250 112450071 112450097
    0x140603060d0c0806150405010806010e040f050f010c0302030901051501020c0607020a0b070c06020708061501050a17270307050307030e0a080a111513090b04090605010b030405010506010c050d 84
    0x700c007040000d403d001050701c000c1e203480401082500940311007980a203140000000300c4070004180141602d034a10701054003602d682e1514a19011242425a41da000f4111418846102445042030040e1562800340e16494106c2c401821a440200312115041712812803d8840c0e9010408401029084410742e8072681540086040030720700c3c0d0810a482c12000900303c081c0b048902d100c0b0101c481c1e41d8204c4050640b2040802c0c1c8502c070545000c0610809041044100e60107200900082030311803400c2d800c4400344030120550301d5002d442d440860800400504002d903000d1500d580d000700c141004610344500ca60305c10341c0d24410700340701074200704001d1610b03c16591046190360042580d0350440d8240e0281d410701c219110003400560b480380d0091103040c58a11410401c0d124921a2030318902070075403500d00484040c040010503141d0103656000c90800044040c4200c1d0b020701200f04000d6141d140c54130f0200c1c21200003030045410700c180e001c0010000b407000180680240c01610b412101c407044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 112452571 1250 112451321 112451333
    0x60501020307030f0813060603050a051903080606070303021c090c0503210c0f0604110102010b0f060d111902010b1504030c141302030411240a08090a06020708030f01140603060d 78
    0x103180700510071030800c00c8c00070a014000455404603401a401d460244141d5951007032004620500240800d00c2500000e4051606c8001340441c140a801c000d40350400c20700851803010050300c03051074101d60f81d9442e1011310969540202c05044240d0040011288501c80d00000412060611000007030024803000640e6007804409001070700c030340c00c0341d8140c2810b250000714025500107890044d1319041044081c0d00d003245444030a4400603090b0382c0f81400e94200440038103009c1c6504050003904006150340545840241a000d900d542e00024010b000201008015509050071482d450720a10061000c40c403081180130840d402c50002c08404590800861020013010b116125054401320070007050103501209003000d0b0200712a414a1010076861004100c0032801902200120030b0003034480b868040c4003680d810003101d40c200c6840003070556940c401c2c2e0b4402d1200702c0f4200e5011092000030100c0f044414003602144007081c0e4080b000d0b01c0410264000102018454180d8249460038014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 112453821 1250 112452571 112452601
    0x10507200f030a09030512120402040f09050316050f070b091210060b1207110d0c0309080706210e0a1101170c0a020f01150b1b0d080109060501020307030f08 69
    0x11900c000c1d00d8503000f49041c094000c0d241c504c8103649030f01500d1102e143d0300305081d00315100003c8840126100d5142c41c1c00b4840202620714220305025640c0e11100007140d4104051b0001c28000714140c0300c54035803450110f04010310b40104a105501c403181c18040e245490080d03500380c1d103080d1303820a0100b21803848070b1320b00807c41e0418107560b4a8880045811030110000b800204021245000705850740321080300d00510510f80362100307400ca01c6500c0d0b1144d2258a09420160103072500024043d2a25156828034415a00403004035425840d41408011944d05850300030000700e40c20444060500304164542121460050920111580180c180e078000c0c100080070940300300f52041c003850f291200800590001c0310f96809846408942d01000005014a58003800d410001482d02d500c0c01481c1107003034009920010320350741000c14802400504208182c220490b0b56110034840d450112400200d0b00349422460440d00104072440100740c0105014a14001d207140945071551a0b003d0700207109 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 112455071 1250 112453821 112453843
    0x31e0a060e0312090a120c11060903010902090a0605012d050901030e0f06060406050409050c0405060103020c10060519030b06130f06030b0f060a050d1202030909010806040c0801050720 81
    0x8018820700c41c50134000074240c5040d521aa9811140443c2c0e4407081e101110003100c000c01400d05039400c031040b0306000014090f040c2001d4000f04103030305583e0008416401c101c600700e5080b80c0e5001c04001a40c1e1209403202903890f6410403483c2001641240c180c502c014600e1304003070000c00290b91005074440da00190141021206862087e100c031500542c540ca01920b00d148540d0910101040341c3c9890b00c250640340746d0180090103032000039018000070380001005a0b050590034042d08514640a00c504813000310315100004d281030401e001c000c038082d0302030079132000c4022004c014800203404030801600003030f0480d400c040c46907406a4040c09810441131140b05141450000401c1100030401e080c001c8090015907a6103544810600c0b100044c1031150690182d00000c060002c14108811012404850310640b031038403141c1c40104105c000283e2005c07950303074002c004220600010940300c0010f031524000a02240c100035100030b0502c010300210500b0044d00d010280b64811040040c2c2142c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 112456321 1250 112455071 112455097
    0x150603070509010e07090602030910030902040902120610090504020906040e0a060c0905011e090509181f0e01052403031903020a09060207050102031b0a0f11031e0a060e03 75
    0x1568413007104011690080e00c030328010031500b11012030418004016210045806040c02c5941843c851045024142c48078091703800030740d46c4030f07003070050f846620086000801000050100b818000030074929141e40d03500c9402c50300d00e0032081c4030040e038440510740d4110500311004603103282c040ea000341c00e02c8410301d4000d155900e400481028250044109001c0310800d886001c03845a00714a1110141c084042041c000b410410781488503140080040d50444540010090700e83d00c13254006140220311007620031a42e03022815000b00746840e00410b022880840300034000b0707007803140d0b11810141015240d285140c40503000c6031010386003001035889907a66425841013900350720308060001d40c800c0b00700d403000a403500404140c1c540000b40620403240182e00562030007200c01d08041182085a01145803802040369000c041541c03c100841403e0054822600f01030120007014075200188207031864060540074962456080410070205139500581c000c0b8003899001c001f075003544541c100e40300b0380c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 112457571 1250 112456321 112456339
    0x70b06040e03210a0b01020703020a09020f0409020c0102131403060a0c0201142a031006180503030d2a05070602130e0f010614030c0901031a2107060806031506030705 73
    0x250014402c480384c0036440d0058104000714a08004a80340e4080d03010194100e2245503040040f04100d80c001c0c080703182e401880c141003d803502c035480207aa0160003a00101e070740104008a1041e5001801801400b07041d10a250801038130f004251680c4000b00400480d80da5030640c090014002c0d000110300740d03008005c040980c90900c0004030110b1800c01410480c5d54510503807442e4112080449000e0180c1c0345c10303500720928200b000c8460704010941080700303822100c0005580d0710300300040c1042c050b1512010a4002c8000307081c4485400c000e00c218041d040c51041c2004c803035045000c03551807640052002d82e540c0712004101e22503003e5503000c0b264070a000420481c1080d000d1003918144c0302c85503100c15146c1200d04560341240000e482c0010f0780f100030000c603c0c8540c000d070302184848031203d0020340740315010800280c1d001c020401c482542d02c4010709902c003214041c021a40a0300303903403c04000b00c0c00c040021039903c101209c242141464485d01050b016581004080c00a02c402800000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 112458821 1250 112457571 112457617
    0x40902070b0129160507050402120603010b0105040506090108150a0303020715030203041a130501020f0c010b06070812150d08180109181a060703050717070b06040e03 73
    0xc00200034410f4030307801e12014a450403034990ba08400d14042c1c14566205041540a8204001005044c00c0c2114684030b0342c880001d07a516107002070980001c82030780014051400d00c0602d800e450b00c1e01075081c10000f0400090001e5030f164000d03540042800e1a00c0055692900d0140c030101c1d014041a980c440b030000c0000081644c000b5100741600e48491a015244400c802d080d01613000c2070300d00500301007105451500e0311101030100380c0d01941c0034440d40ba001c03059031101404c80c0d100b8660131920358000624000c8100003400b82d00c400c0941992000c4c03074100c558403007a00d58000c000e84844810b50910105201c20b00901a0320720010f0300a2200c54042c0852910700003c2e4090742010802c0b804010b175200303856008096010480301582d1641406039405102d580003010391510f80d81c02072217040c0e80d401054a8441c00392500b24401d455150b80e0f400300782045c03505868030045641c4442c10030040c2030000f4156160082d04110199004504504032036003e0b41140030b01802e0b5901d111804041c12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 112460071 1250 112458821 112458833
    0x30e0f06011503021c050405070b04030c0608041a072303191e05100f050d110f030f070e060108010b040b0405010f0c020d0c05120f12031312090801291504090207 71
    0x51f00442c032030f2080b0360701c282e503405549085018030722024015075030f400c0042100500071044964428450200e0324178840e099095480411b1058070824006420a25440504c424482c0d11400c1441444e801074150714080003034800340c841150718412640d84950484800d020700c901d03180742156110900740090724009603641d0007858a480f80078108801e8a0001405061031900700c00381c181c01c04c80c070b8035104145400340325a00100c558000d80510907a0040050f0000c1030203110b0181803c030304451070b5030030310500040c054070042e00110401c1a040008102556491080b01c013214400e0030209041224460190356061001130080d4000952906860030811006c959100341c580c03c5804c0c144d808000240300e40d0302c84e0a800c0011032940180427581c0107086000103541d010001816640030140959111a000035221080002140d04014248100e010a0148410070094040e0588a04990813205800d200b102d08405000d9400103003410202c80840d001c490141250500555440c5080e10f801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 112461321 1250 112460071 112460081
    0x4170721021c080906180a02010c14030d060e0f010608011205210a110d020c0f04110a110106060e06032a0f0a0201060f05090c1621030e0f06011503021c 67
    0xc5860350045c0b200188039040d84554000301040003a0003072008501341c0d4015038440c1071080e03095402d8800d140103200c095208100030042c8142a0002161961a101c10008400e030081c141c1d0700380c1440b05005002030350340302c989141120008078501000c020642815418403000707036100d08030b9203044400032004080c83d0000742030300d200036540d103640440c0f02074174940c03265580304d036030001600000c010464a160580800f81e075a48001d2000a10b01a181680c0c001c6520402a80700400e00116814482850a02c542c41c01400141403200400e40020700185841c800140307032500400c180d4600400281f0300d0010708180704180d404035592005401c1484605800c803d411000560030290085001c0300141d4101040320409042080207480301c1265607119000403000038628410300070294041402c8216111f800326020388501c6400221900041c1074a0003480e0807000359000f01c0c00000c480700002429411100c1844001d082d000345000110042d2207a41c60a1001c0640c0014030340018100da406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 112462571 1250 112461321 112461331
    0x30103060b120703030e04021317011e110d091e0803270a0f05030c0d08011d090c0907030603080d05070801051e090705040e040b04170721021c08 64
    0xe1001402c42000e1120b5440c02540401000030b8452010042642800d80180c03005c0002c0c014100c1002d511001101064401510502841e079101d403c015180215000b800e504240c0807201481000b00c44203a150844c4240040000c43c05e50314190f01d000e0081c0302042c1542c41031101003070090000c0034240703503009030820750b024a203c43c00103171100920080641941d64001500e0060a107000781629140e0031500060016946400100300300c0003080024003403041410425211000c0c554108000111080314175200604c10002c0d16080c000c000f040040c40007038626046500b5140c03581c2d400320840162910b40c0c00285001c90100c0d084c617240c4c1c0c4980110740700e0025a6505003a070381e6540d0400450300c0000d842034506da0200404001d56050802038035901c0030315420700302c0c07406549400103201e4103001c440584111200c5000c3c0400c002c99112040d441e8220082e4143c01d090b942d4403210031a44105101c41d0031505640043c0207228003d0101400713141004004a8840b2102e01000c0c0c545101125 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 112463821 1250 112462571 112462579
    0x41a031b0307020a020310090c120203070e01060306080c010306030203150a020d021215031504200a03080702010212090f04052730030408130f090606081305030f1806030103060b 78
    0xd20f2803408150302c07600c80d144d49c003d541610b110b0f182c0120000154601d21050340c150041000203d54842059005402850140d07400200c41d480c084905041105226109041606009041000da540014005821341c0160520101d9071240544a40207100c0d809130305010030b00202d43d45c60441000101c19120302c80311f20a00590b105c1c404101610340c0441d06039165000f80480c081804600b403c3d890349842005031520304102280d11000501d100003a51007102c0d803e200090042c11960b06000c80400e00105040d05424000510000790111034140e08241c015076031000020f100391001c2c02c25120300100f801400c2010341400702d0070390b11400c01034030070716010f00001c00880402071803540c030010040c080c003040d908640300e5036601e961680c00700704460502d80e00e1040115000240c03c4d00c2000a0281000002d41c01e40ba1205c00707010700c10001d00c1d00c440a40001d01c01000304130301104440721300b1602d940e451780d43c444000410207080c00e420240d64122601100200420100d41d02c41120031104503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 112465071 1250 112463821 112463833
    0x3060f050303070305040b0309070521010f1e2304230c0603040f0614010902030a0608010504050c01260408040f081f05060109080109081905041a031b0307020a0203 72
    0x503050650343c0c42800070050000c0d00800041000e020000c002d19007041241c030690300100d594100007100d2490712840b01c1c104001c0d06210740a424024440c0702e52512400c2c1c028002e0010303103070b0766030003c40c05034181040301e03900c541c40940c1c140d1005030002101031103000080e5250420f410706050741140180082c00c00080007106c41c4a03403400050703034080d482005100600e566965a81c40b0b145035072580c0d04548080d1110b1101041800b0450b810b40071340400f00005860b8900b4180000c15101c0d20703402101543d160506003c0824008581045640000e08140044905101540a404172031841101c0004081c0c41400b0400c201c0d60010012251039005007101e271500c60b030034542ca88903403020185081c480c0202e100c1001d03605400c4558817010505000460079034614250b420344258220459007540300141c020f055121080034107461011500d400360400f418846203140c405400a45100603100120004d902034114010034020900032110594030b034288450080d507940c0e1085400c80c4280190 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 112466321 1250 112465071 112465079
    0x816050708070918080306060d060e0f0f010f0602031209030f030702070305070e010b07150b040903021501060504030f03030b1c03021c050310050f0f0303071208010f060923090703060f 81
    0x2038061307034070542d801c03203050b600c2c607101d94042041590101a00004240e00e50b0400a0703000504060300d4401c0c0d88086a0404601d44a0844501e81c101600300504080d148071040c401036034004203030307005000d4154200c400c0e629018140c500e103000701050303459041800030401c6280f41e4045491000c0303c1c401e000321000c16454145040284000740100c000410b4140065404200c521007801c4124088140c00030780c2c8141d007004103065500c2400280c015922969807079807902c40760b140c00c500601c0c3c14940141018219502d0422035042d080d80541095200d41c00c800c46540d6036000300848918a4085d41c501c0642d91034065100d1442c0c2e040079903419600b01242d80428003407412244111221265070103424145010130424010202e940740d0440c181000070060b68504000402107640203031201001c0e140055001040b414058204100c00d16503200100300e80c1c1d40010541061f1003e03100b804031040c890303031010342080d0540c00701d10b540924403009000348560558000d0040e40c4107000d602c000c06443d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 112467571 1250 112466321 112466351
    0x60702030306010c060914071d09010504050619060b040627050a1a0d050f04020a060e0f04050603030d050c04050102010605180408030601090b04030c09050a050702070308160507080709 81
    0x400c64615000c552a200302d00c0c0051101e612a8806c6031090701ca00220700a8002c0040ca44011504204003070807041d404510440705031300303071680d00c000e0f480d0003070045141c1a40d03256221b40300070b13028905400300541c40038481c1103a5004013000e080e044102e2519180d4600000700b07000004540d48590352007070030805110420440d465803e03508007528400c05585002501851021407442000c0e03291010b00804140d0185070048030f0040540c060203a0080c181801040b500a0346944080c081c8032022580a02c1034803001c07004040614111030000b5a035a468010a04511982c00b0907081d651a0000b0441022041c402400640c0c500f039008011080c2c841c6d00f03100c81024030000b003144019034400003400141c071403c021a84401c040c0b520804282d45d886041403260019001100c064030200070a1007600b034075100c1c1d582c0c0319603144400d104070309003014083d40300c0c0317414000030300481400111540144084401c003000280e2180484610382e9507590b005442d104240a0b80d40d00c60b0a0114039004154 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 112468821 1250 112467571 112467577
    0x60906030606010c080d0b06190e18160e0603100906080f0307060b06070812010e0a060e060f010302210907090203070f03051005060a05031f12030e0301020c190506070203 75
    0x1d810303184c07485918450340b03403202180c0003440d500301c0e0705869468440843c2c5540000d0018480c5040f44d11075012072040c4080c28181c070f1140d07900c2c05481100310500710301000c0000b0b1038019001220f13201c40c1855a64003201d045201c0c0221382d0b0007602c000f00b8441002400c0303200e001181c48101041000c00d885030840350f2290b1f000d0700c440000f80c0c000d21502010031020361062018010041c01d092400c0d10a554120341500000c40410610000c4001000700f110901d400c80c0c1d106000071410001c49040504504000c50064a450b000c1d4242e0544442d0503402075046991070030410b400540c060007110080c40303002d1000c40301340400b030164810001c0d0480d034034000e0364026101a141c18110064650b011401050700a20611800006031000203464440c04002d00c0a03800d156915070b520724000010075840a0440c9c00c003414691030100400003141c1400322402080e61510f801411840401c0000340680180d002c4402140540751241554980d1080302461042c03042040c4c0350190781e0a00b050f03840340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 112470071 1250 112468821 112468831
    0xb0c0708030c030706150e10060311040f0e060f1c060f09050618032709090f06060409170f031e01030f03110a0b1602070801060b07080c0a0b0408030609060306 70
    0x740c0280080c40005d02d49402200303c0030780e0684910200b0303944d0341134440181015a8412416200e9103400d000c003650500649800301e031a5144540351515004a40c50390000b24441c0911801c1c0200c042000b0740d95a48800d524540d000b4074000c1030800300485203440032a00701c02155528589a000c0b84940b000d0300401100300d8006014080ca0307034400c13218a01e5034507042d0070326160380003c02c4904180810071007001400041500f82d03803a0b102940701446003502c0081c0c44c0706070650024a100700e955000290f0f01d41c1c07242c0706940108000d5010703d4040101c407500c030402c1d0b001d4000450801080741d81d590103188141a0b5051b0985802d114801d03a4070081000e0001810242403d030400002c40d02030b01d00e6084210015044801c0c001c070700e0310342c0c1a41032400da07540c011814603009400e044541c1080081d000d003c0f60320003000554502041c0d06a988525040144183c1c0041640102039505202e00300903540c20030120780039440c0c2483d1640e1a0b0344211500d5215130980703404a00d00381000200c0511035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 112471321 1250 112470071 112470073
    0xf0c260613110f070302010617030c0d0f030204080f01090303060501080c03061005070206031015020d020c10020c0904050106030615270216030e090c030f0a0c030609060b0c0708030c 80
    0x40205140d90009030840782103604a0380d02c20055103401015400040a0b03031030103a4000501a810264844105024001000e460307070b00601403280800c20104450311441058100108000e031204d4095020380a95840780c032241c01040300a40344020190002144103200380d90811419450300b005584002060300c0010310785a00780300003004c5007003441c04040c0d020b4581c00c1c00d9042031030950001d011075100f2102440312605400c0c0400c01d40001b044060b094191038009424101f41c8540029604c0416030303462f40c441c134120740034581c0550003030003070b2400c90700041c1601030145084d042c83d03800782031b0340e100403110203140070020446a2500b8800c802610603107081070240c42c039200208203224148a20310100036900300003904120340c0c4520003038031061090311195046881d410800040540c001c0a0748000c0104204120740c07a143c800c00c4540c095182040000c0c00303c94944100c1c010720807500b0650200b440d10101054a4284401078400660f800c4101c800729a184c0b101507489008842d40042c103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 112472571 1250 112471321 112471339
    0x801020f0729090a06060e090c0d11030f0303090c01050f03010603150806090a0b0a0504030c023715030603150b030c0a12050607090503030d0f0f0c2606 67
    0x100514003146082c41c40b114900354a00c0d01026801518005444031a500e922901840b42000403600441000703018654200859141034488140c54004403d103161003000344107861130400c001c05070a650440000340407100c14980511394296668015a854160303441012100d401c11f41c41401220303408130035a00f80e2400d6910b0003a0543c060080d80c2041c41000818000204104404120b000d2080c17090321300409210781181402009040301070505100181004104030200f41c02401c0603450780d070b0550301c05160040e0f00300c1150700888510080c000d1010f0411816045017400a415004e8884c11a202440390920890940480d0002d110051030021071201a503880c0c145a4805d0750119030140555882c010f9220000f40d1000749500011411142020248117001e810802c05601004605000b00e94070b007001c000980c0c9025103420203d401b07444000b0703c51a005d094125001c1c0840c030071424841c0c2021520007415a02d003903031400c0240d1070580680001d0428920b01e00d07000301000341000038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 112473821 1250 112472571 112472573
    0x602150c0a0503090f0a12090b041d060607050105090d111501051c0f0501060608090a15020307110a0b010303110705090a0c17040303020c010f06030818040e030a050c01060801020f07 80
    0x4040d04000d044c250140980354180505050600007203044a1141004010042d07145201400c80a55600200200315090009000c0344480b0044415031410f6451310111990702c20340000c84c60712034050010859401c5c0400e000203124002007204802c106902d41010340400904c8103580c1d1280100b4100401030004010011401c140c100c409165008440102403002d00c0e840321981003403840c0d400c4966a659503800c00c92982d00c440ca0607003040300c59028201c4002c09444200444c3c00004466090560000104140500944078601c40e4002d0009a070b4550300300342004904804244000e80214444481d030b45000d400c0403400000b40d0b000241030410584039003041c440100b030102e01d564280641e4580f080c011f0310703030072060a218074880c2c1c4d030243c0c1d19501c980c90306082d1540303588200b0701142802401d100013041141558080700000c0c580c101229003840000d409407410070f0350180345010018a5070400c035403240c01020705004c2031000380009076603455070031f0803407080d40b0401c1010002404048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 112475071 1250 112473821 112473827
    0x504080304061d0f03040905060102150a11091c0302010509030a140d09140a0c0501030506060a05090a050616060b0906010f0c0305040504021303030f0e01090b090111030d02040602150c0a 82
    0x124038107503510404807640040801034a80b00991001d84c5040d403000c981040340a80e180141b550148080c4080c12002003817040c4020305010103003c4080d010344071503140401483e03103000d64941030002060b0007401e03035903070600e803150b000b10712000d5005500b490002503240a00008540700040d1540c0d401740c0035005100c40c0c04558002e202e00803c0d81c3d45402d24440400d580036404580307405a94083d21900d811481c000c0e1a00629a2050303051604080400046a90b80001c0c4c596801c041d041c0f041d50707100c0c550005040856160800303580714402180c0303626450718503406e000a80380304d0442040320000440812646040c201d500900190354428914440c0c0e20032051120f01d5880b034280135082a44840002e01641c004103005009103927080010024103a0080c0c50001a41036810140b01204682300001c00e0040640600321004030002a000350517489004080c2c920307001d50040c1ca4903182402c001e103020b90301511400005101301204504401074000841e4062058000418506800c0c0740d415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 112476321 1250 112475071 112475081
    0x6091a060a14030c04060e25090e0a0e0604031d0303070206070204150e07050304020a1403071a07060603080405090903180f1203280309020307030f0c031403031504050408030406 78
    0x541e010f0141111513400c84d241c500030302c0041c04150142c0855071500e03540018806541d800040000d50804844c01a800d0b00304409500341d9140c0c500c0903040e40e0f500e0518401424031040d041125109107001c102c141548050b020200001200d408c080301d8080c842003680c0c074000c00d0000396228400b04415030040c90164040c01d541c0c4006a0f8091040341e942c07000340001c0404981520214034004200001c51514071502c40203000d00800e07010310045e4460110350b5403003190007a41c916280c40b010540707020100c00103440d646544104280011030b128540012690054030a450149903c0c1000c11022103011090b03071a005c601210507200707240c03802c04211038114104c103119041031250070071100f245800d20080c541100c08060300302010f20b40c2492f03410441011108203003010718041c80c110050781c1c04241710701101d070004004040d0a4031414001103d203103660004082c0f51149040400491010020f9031003510b8600d80700b4100406c01040c80306481d401c43d0001c2c4a07803410800100040d2455100e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 112477571 1250 112476321 112476359
    0x6090807121407080a050105061c110301060b0c010b030d050319090804050907050a0e01090605071403090904030f0e0a05010e10270806090f03070b0a0f0906091a060a 73
    0x1103604a0075441c0d40310343c14114184c01c094200d400004810080c003009004150304960107541404010701007060380c0413003401c0b0038002000180d117400c10300d88030f40c0d0941140300504100c01c21982c0e90403e522070503001300494411140203001c1c0c0401e0300c240c54050400d407449480c0413403602da0713000305d0340c42c181c0004d01e2602c80c2111007103024070010030340307440d40c0140b20f02c5030616849113552901d8207140548010316071540581084149801841307040e910505031080c103540903142c440400c00400545045010310b84d600c64120700020200014103900c0030058284c3c0240d501c0d404641c840c0d10051140c0501c05009007400f0500000c4101c01ca4180314140c181584600c0c036040c00004914108012600d409000070002285040010b0200040c01d000d42c1c0e8000310400000c00c1175054000d0429102c8c018002c0160940310701380c0004103800c02039000b221012402c0d91003082009402d2401c5002800c0100c001d135030b800081001220040420040140a1580201300c1c9150b18607018098003c1140c000c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 112478821 1250 112477571 112477583
    0xa021c2102010f060e0411040e03191b0b040b0906060a031709040c0e0414090d08060117070c0b010b031509070201091b0303020c030613060c0e03160905010609080712 73
    0x600040300c03450b14801d14015005401003a40d5030700707003030506112400c071100f0014456894000f0803407000700c001003180c40f454000c41d9841121201c0c00d1094865414804807100f00a40b0041801d0030003440d0320394dd03842503100300500e00f15603c81d016025640c800813243c141d0030244003079040c000b06200d130300c1c0081c4107220090103031728000416000c1303009e8411204e070800124110100700e05103494103024040307032543c07041c0546140b03207450000c25650789030715192002480303208408601141d00c81c181320302c0040114a1100c5007802c2000c1c0003003080360190b0301503d06449500021400745255005c9900a1030710603002c0b0503c0c5150010001c01c0000a03200b0300c2599030300c804520004011140c103401c00b416040e41c1918651841c00c0c0039080130609002d45102e60010004c00c481680d0781308000843d20b0708020005100d401c2d446003038991011400503590f1502c03030a084201803000503d104000c0e0341c40b11905100b940d0341c45800f13541c202058011000d541c0c020344800c0c0900c070400541000c82d240140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 112480071 1250 112478821 112478831
    0x14011b060e01090606050402070201050304020415030c060e0901060c12110f0703060b09090601060503040b0402010314090109022404090f09020a180c08130f03030b120a021c210201 79
    0xda00d5104907100c8a0000540e070751105820024004140701d0b0f02c0041c8020703201580b81c42c000b580000c00920004000074880e9540310780c84000c8000e0307060b512000e161b00c50901c0100640b03036500a130800c06045181846070351694008503c040c803a40c1c11441c0300360b000c5418410300441c01f40a803825080510312080c6842101f60550b1007101c104502e60003140180300010380b01404105020207044028524030f03c550064004018140d481400c990707200c0d411030100001d94880f4401200070300000400419000d1500b018404c072840e040d03010904035031003101c415480340e2000c40040b00000b01c211040f002c3c141d0a002c10080d4040940020100740c81031300d00055072241607800140c03000f038aa00031156a071303111811103400d030441c1c3c41420700003481c0e8248605e2910300300280042810200000030005241092111f00b0035008e41c0090500d000000d00d070f2003000d040b0074034107982ea10081134207920500103c142c28120800c98032403520f8894100711440601822107400c0381c1000c818044d00001c5650356 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 112481321 1250 112480071 112480073
    0x909050603250501031508060601051e0403110f0301140a0902120a06020406090801021305061c090803060112020304020618150a03050106080a150509060409080f030906070914011b 79
    0x5100d10011201820b294045081400040465201e0012840360700078114060129800014102e0b0340841c00f440c1042d0307140b007885006c2880303502c00701024084010101d80030040012001c900440c8403801c0d80e0319101207540d02c04041c26145044605040c41c0002804146c0c106001c0d0000c10b000c1d4000b62840b0810107807000c01d50726200039840d0036200950f022a040c0000d940c000e082d8802040b803403000f54140003a504400c044070349c1c0c45c42510701c505400103032201886101d07011b442c03494907110810007440d141418034200e160320482d0b40742d000600000d9480072449461090740c2c05a80c016028600708034054100c550900300701030446a214406c2d030030380b41360141c050780105078550090b507002c122949405000341a51002600076500e1a08000106c0050100344c0900801c6400407500c42e03080e0303110707030002c900104060140980025000111000507511580045005440c9441107544542c5e41d082c085403400c007140110029000000c046040d00e40c803544110403c0c0f03c914a442075000d0403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 112482571 1250 112481321 112481353
    0x230711030408060c070204050112050c04021b01050a14060105071e02040207081605060c0702131505061323060f0307021f091208090309090c0c0a08040306050c09010909050603 77
    0x21104d10600400019410f01141881e000e81b500400c0b5410b2204451000c641c0ca21391101c1d918007100b4040da41c0400d052102c42c3e000c4101031800d034000e5008001d0f81c2000744580c001340c4078440510300400c111602059203548a001207605003504140e1a00d0712442540c3c8503104424003410036a4059001c0c4010b00c0400c035540020b04c116500208170060710644d91030513500340740c0300400880d4402000e011f1325000d038850000340d40d0000404800098075010044181402c00c0d001d40200e030700300e100441c0c40d43c1e604001498900c00d580303c40000003000840c103000000003449045489810082c24400c0e21018940007000d5a0425010700641d4680585440f1040d844044403601c040e20b90b031540260810300c1144203070b001860000303142a16070b9140c0071600e140c0d2032184400441c001c8603000001507807400564255100700000c041034a80c080c0450405c1003154009000503200300d850400840d0a04091008039180b0f4503060b100c041c0002c4c07420722000011b0900518694050089804503490400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 112483821 1250 112482571 112482583
    0x20c0a1b030b0105010305010e0720030a020114160504061103070803040b06120c060405011119030206090706050705060402040203070509090f0a0b030a0b0610050415020a06230711030408 82
    0x104030064000da1070740c185541c0c04541a40441c0c1814500700c0140f03c150101c40f0426071107115410904261040c81b810041140d10600c1c1d03000071400046801c40102e503040d004034004002c041c01c6100580c58900c41c6000d860a95519000030480030041000050700541c40e41140d15000c0c42901d00340b902c2c9843d1010140c1c000c0310300b03d5554030b8081c1041241e14101d200c501603410704034014030b03400d5000008201b65200754002c940c10b20881c4600301d0410ba000300719083d0410242c81e1950340c480801d20f00650f0f901010303070f0548a00c2c0904040070640741c4c031130415200d90b16044402001c00d03444540a00009600103451082005030400078040581c4400c5000e60240365041da0035411031510580a5088a00d18500c1078860b403c00f603441c07030114544400c481d4014104940414004003020019591881194010308211040c2150710ba02c0d20340100303590500d18040e42c414054044030510038000c02d40c10700c035580071104440d000710300000d11411803404082c03030f4101100d140c00e072955250740c9008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 112485071 1250 112483821 112483853
    0x110102030a0c1209020a090b0303040504090b0406060b03130303020a11160608060d080708030a09122604120c03210b041d060a1109120c04060b040f0603020c0a 70
    0x6a02c9445900003160322035068200c0300829201088241d00650020b40d48811511483c02c1a41d101c4410307004035501407044030000c100041040240c40f02d640b80c0700401c0305044600780d44242c64400c000408111007812a882030b00041c0c881109640c890758140c00940012000ac0d0402c0101002032503403000801c100001000c0f01e01c48070521500c0d01c200180242e5000f40040d01652180202e0800100300000395010254072910b00e0b0f031243c0d540c402150091188080181005140070001c07030b042500a11040e49000303c550881c0080c2a00074160326540b40152801021007001c1c0620510b418490b00a02d0260bc1c403915004021000004056108140021045481c5565410361402c02e14191084800400d03040b0003030070152080405803611814000d00351081d00d40c8a128885408401000701c600c0540c00800742c4070911758403202e0035500c4032186011405903282500106591900b5815101100d00700460981c41d241810360880203504040c00356150b0340f080c101000c00040308440c0d446520 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 112486321 1250 112485071 112485091
    0x160b010611010b01030b10050c15040b04030e19060f02070e07051305030106060c12090302180601030b0d0b011a0403060216021305010f0b03061c11030f01230711010203 74
    0x804050400c240c21906500360a44c1454585001207801d6180e242c55040a040b05041143c0c85180440115040001c40c82c0000342040306401048200841c80b5410b0b0301450096a07400d66086401052240e07040d095264240341400e201400c12009200b00032128900c940c9205844900e80d0711030640040782000d42e0080003244000ca06207001c100503008420003000700b14020320210740741c0034011f84148000d00014215031800e07205600a140954031180c01164007500f664000c80d001d80110b1403402042d02d009001a05209030000b02c2e261218001c0900c0782c004c07000c024164a0103220510034208020081200322003804004041840d030b00c041c04d44c07900384089500d1340400341e104001c000c200d1030302c20740702c41494a0018080118006584401d48600c0076481d6501e403165000504000c901c82d200c0018080340701c41007070421403225a500d10b448402d8040303501640c2e60b1404942a69070b444d200a40e451141d901101801070111091030b003001d01418060303041e50002c0c21a0342680c4c070480d245086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 112487571 1250 112486321 112486337
    0x102070204050903090f0316090b010c050a03030c080a09151a120a0b0105060c0303060f0609120d030513032109174609050301090b090d03050714160b0106 68
    0x500d0400169200340300e2811005040301c9800000070200c0480c950052114040d0744507480360315640161800c078103864204084ed001e5440ba890001c01800c01240310000007460030020031403a5840c1d0148800c125803054800c03c01c0340558228100401166120b26100c01000203400901d45501c0204660070404201918106800c2d051116403094103034841d50085004000c41401d0840210661f900800d0403a42505031010050006106008400540380d00010041d403640c2a54000180e00c20700611a0b10f044c0803035a07441a0001000c1401840540850440c1c07220825a00e40080e1561030210880e80016828441c2d44507401c0e04007a001881c1c41506000945078070131942c03109054101c01060003030710f6488a00303a600c50203c0100300000b034403401c1c64181a503290740c001c0100a000d028058001c02c0005160704000c0d090034420b54001c8140c1c002c503071101c96090301c41c0c01054885c0307280d07413030f1b560020200034001d44e8140d004003550b80000b50440313040b5000410703001c3e4007402002c0a0352940701d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 112488821 1250 112487571 112487587
    0x2190c051c0212030310032004020a030f05070f09050d081e030403111c050703020a17070201030b030a02060a0c0c03020409030e0f04050f1605040f08010204080f010209210102070204050903 83
    0x100c280210005070f0ba503070384184100b0001c0340c10508200d003030341d0f4010300202000c2100700685540761804d50702981d2142c00418010081c4c0e500d5403110110819142d418445034640c1d140903100c3d401010714040009441c40390034001070510440128126206e441d043c0d1419140c1d0704811291b60312003181d1842010000140014145d0041c00a42c072030310200003030012880f02131840c03001c00720a0514501401408210391007410f000384100d604c4541c000c0c0c04941c031440451013294075a40b100e1400c0780860301d03042040c0e206040000c0d08815140d805401d0901e072152000c0180c91515094100311004003e01c44048010780355806400c45082c440d07261000704034032039000c000700d10a000c03500d18050742c0303000c04100301c9010001c102034000a250070600c0743d00a40300801c0760140f2640e0000c1090501154002800560540c000c0c4121000c940031383d8000e0309038020482c242c1c03050711803003503000031003004042c4290505040f05407000b1a0800042c40c044140e808101902c00440755907a064101242441c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 112490071 1250 112488821 112488829
    0x101431061419030f0207020306040c06020f0730060e07061403091b010c05120408241501121a0301060501110613020301060302030703060903030b1002190c051c02 71
    0x1a0046007141c01041c100703041d18101c03182e40d8002d0350300201010b07203802218200e8032040c3d040300c0032160040c058480034a03146c00c1403c0b2903900d034403801006105100b80d0940340d0f40c0c0400c0c41420b990703c0500740c1c1681f0041d2448580c3c058000d04d00c1c14070341c60081d800715000036010321032040c0e007040050107400c5c00e51034620301410140e00074000313150641007002042100a00410318910000200d045c00c1c00c81c8207101e004031025007249074002e1551042244080c2c02850101c040c03c115903214044480100307800c42e040303201408600c040c01e080f40c500004100182c54070904078141143c18507080300b00c004908500070507201c40e29090b0014420010001c01075041c00e02540001e071000382458020701140002c5503a41c0c00004000ca01800540d140304402c558080d0003e40055800400311281a912400d001c1d00400c881902200400d05d032894004c1e0505220681011100b07042e0040d00704031140150700484802c0c0c1e12811141c0300d01d07011010510b80e80d2484c0080b004070002c1480145400d00b4410300c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 112491321 1250 112490071 112490087
    0x105061504030b0a0f02040f0315050601020c0a060e04150e0402100e130b18010303120c0c120f1403090c03070819081605150702010b10143106 63
    0x140350200c10810007480424000803100b40c0007407420200107101004200a40c009004541000020b060905000402d01062211140090080000c2041507444484c0161780c4c680745040c005400000c500e0007004181e004135024040541c0141c00414a8403040c8443c820100c010341107d0180c04174407080c0b0095040034465030b0181040da0a00c5030a03440c0c90300005d01c4080d0009050b01c202d61b11030303a004109031102001c2e04440343c1088040c40306940c4a2a01134130700740d8408501e59040341b07841103d007445889208203000c49034003c1c04076580e00c54400011200100384d0060a0140310080d8480b14010262000039481001c400c40508469103030201050b080000c29031003500154410384804401781e24010311000d002d940080c500c2e5030b44e074441c404002040081c01d4084c146005032100380b041d0b0801c11481034810801075000b04003120403401044901040080c0800000e01481400f0703500400d00301c0100300309015a070540714603a281c2c00c0e4026921400103110004490002400c0040540015507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 112492571 1250 112491321 112491349
    0x230405010f060806330c0f0a021e010507110402090a030c17031c1e050705070209070206042001030914010606080108060c18040204031e0201080901021201030209041a0108010506 78
    0x50394640300050481d10200136144002c000507240c0072510f8000174240d100403280411150070a9034140010030003502e884086005081c1d0050021810740e0303040200c4c08000c80200d0805071100d600700102a184c1d035901511a00800b600a50b0800c4168550340e140d90002d0f008605c241d058031826814600084101c8403c0020b07003031103a00a02c641c940303402080c41c00c0c00c4003207401d03480021800004c0450050030140d09107010109031425044c040c65a50082c01824218002e40d000e60464480040403a0f4501c021a0094030b41d290601c8080c01070b20301902291701e03943d030500d40454401074540782d03281c001520b41207a154903135440004011558101d10201d0045c4a5000505400c1c07928081a0015101d403a039850404480d5420040d03c0c0c4c0d682e5810b80c0c0217941c0142c140070107207801c1a02084a4400c4001c04c1c0e020811a038001034003980d050084031000401c3c0e10a03140c20b40d20315400c1c03000300c27040070780219031030f10764051001c000041011203d80281915400810305081c110103000e0844801c0f20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 112493821 1250 112492571 112492579
    0xf010b0103020915070303061d1b040b0d0e0102190509100201060612020d1509140c13050f03010f0c05071b0b030f07020c03030a0203040303031d0601230405010f060806 74
    0x100000c140c1c2d03a2107007601c072600c4d10014004c1d5540d401d0300c0c044000700001d41081601500401440b08982001c81030f50344038003455003510a8850031980951441e00481c824401000c4003001503038801406604039a80d04a14030700007605001a138407850b403c40c005803200000046010400785014985129100c4040c0128002040b466043c00304c010003e101d000e2820030403540000d41d181d003440540c6e0204020124804410075080e4842d01010068040750050240e8100200041554191020100d400c2c0c2a12031000c401402d00d08020700c62200b00d0398000a9255603621010360021120340903c01000003542c4c2c0d00c030b581d01c00c20302d00f408442490303000001842452800901c1a91110401c0300d41001a0042c00185942c2d80d5200700e02d0b04140c6451a41c040c000800d03d405843d40020150007a01e01c81d84052200c82c903503854000b0030441b040c40108141d0700c0304004010300c6a80d05c894030b910144202204415805040104007554020381c04545a244400010080554420b104c1500408225 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 112495071 1250 112493821 112493827
    0xf03060902040308030103030c08070b01170f070b1c0207080406030203161407020f041b0203031005030f0307170f070b040b16080103020103050601052215020f0601030f140a050f010b010302 83
    0x184601a13a40014040102444401c0034981d05002c003010a45600f10f0303103e40900c4456842d10365140d00100705111a0520b8450002440704240010801006441000b9981402e060000d40340b43c0b00c0199030f80101e14601c0c0d00300604804954080c0041c405440da40d00d001d079481c140310b0704140b50454005507500402c9100180c01d124280b034517040303600d2650100d85106000080200060091600c030824000400c1c902407030040064010000d14070596821850722080740e41e507024075440340304903102a03c1350b40041241c50b0000340e215660030440ca140364046401c0041304040e22070958480307070055440b10888010441042072394800c2a03404071410b009002100401c0d44003624103401800000c1c10301d5240ca0001d007080c1d00c1070090351203414804c06000101200000360254440060054900541650b4030341144c440c00012289480d1011000a091503840c540f6034090240c9040c0c03048854400c1d90051580700c40c01004122985801032000c1c2c031394140344250b10750840f03041410484c181070046c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 112496321 1250 112495071 112495073
    0x3010510110d050318010e0a05010c140301120c05030a0609060b0105120f0612010c0518030307020303040b0c01200a02011d15040503070605090a0c0e1b0703020a050d0f030609020403 80
    0x407602d00ca8032401800c0c041d803251640000b0520011a0301d405600342d45ca4007800344c580320400948917020502880013040b90341d0030b8220440324017110414506413024104010001902d403a0000801036001e0b850340e00b40aa00c8000007800c10b642040240c0b100c5441d2040324003800350b1841252680341007420b10926000810700c80e08140000104101e8844c00081d00050030ba0b20303900002c806d020041e4008201181c10108090100c1e0130104c20ba406661001444606500703000049a10300c0383c0040003103003002d140c5108882550b01c541c041010035501d901c0c24a500b0306480860000c244840d43c1d2454541d9014a4000d08403924019002c80d1108801026003035a84085200114000c0c481d4014005035114103000f441c511414000801082c5010b003001107850300800c10340b40344c52081605008242d50750301000e0352030005584910b200c80501d8101d02020b00007600078a0981d1090042d01c201c50095200e440c1489803001d680780202c0e003242e01450345a80d052003030b813018096141c0114102821 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 112497571 1250 112496321 112496323
    0x31c080c0a090611210d0e010507020c28060807020c03160b0a090308040f0303090b09010f031d060a05060114071101180902030a0204260c010f050418020301051011 72
    0x42e034481c0d0f500340306020940c4851840d041c000d4205030304803092022642d0390201d1004030150302a012202c1003074036140f110700b00383da0107001d014090b01c0319500500301e0004040400c880b0f22088981c25000031070f1031402c2280c0c0c4001d2080a03000b0300c0c00351104900e0303240150010f4180360301040d40070720039005241c551030301640142d07100302661381215401d501c038a940304003642c0b0048c5642015047c480013003400203000c015251481d050700c0c440c0c0d46038900950b0b41c004900090046c02415404228008942a02c44d44640d100c206241c84100301c030364581c04151201801e000090302c202d115151200c0400c105942c0103035640141d503402e204060328040c16520340140c4402101c2d111810488283c00d445810140d400020020341a050401c5540782000c580342802135216200702d81d003c2000490038004c2a1307404581e44a400424000f61941c08581c0c00112a49488003070402d00303101042c840401d00d1403a0320341103803001070540c00042c0c0d2035051104103c0500240300315501042080d0740c0d81c1604400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 112498821 1250 112497571 112497587
    0x13120201082a07080c0c0603010311091306050f04110a03020310020d1d07080105070c0b310b0108060108060405100c0203040e0702010f1406030c090a0b031c080c0a 72
    0x484903503200100c001c18210440106500c030910700e112000c990002480241da000704a0100d1440071500110511b90900c14540401d00c009016940800c802c00c1407403d15088041d4000b5801162141d11403a540d642d500b151030544081d22150511001c00c801c20000206000709041c1c1210800d125074519800259220340b0150b010502c0c680101e841c9240101503081710f5040e04843d50901c120a0410403001c0c2d40780010b1289032003540c240008264258050000403a40ca44c000500100550384c00541000d8581d010348061601100c0c070542070300711072204401a40c554800c558032002549401441c0e868008181c1060b01c0070342081c018407000400000342611600b00e030b01d00210700008241340580c118000c4e5408001c502c0340100030001d00c00c2d07040d4054074620400981c104003583e500300c201c1900000c04c0300c085805600103003080c0340d01d1030001c1d1000c1d03000c044400c0101d54441c2031800301e414a1003001144c1101100305c11031002a542107090030b6401501151100d080000010000b04101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 112500071 1250 112498821 112498831
    0xa0507050f0d2f071214070602031b0313030206060907020d080c04030c14011e02030a0c11100c021e0a1a120106020c01030606020f0d141c021312020108 67
    0xd83e10b00051018000c440b007a11078511240c0d1072044100f441d480b995159920001c0100c4040d0f01d07460340d16020500401c185240c00b4030401810741082d61580c3c420009600103000c001007001c00f80f449140070180000114410f40c000c41844100c18075a1130301074600792000d845144070b031213038a04015140c1d0f400100968140081c2c0341c6110b154640c0b801c220000d00c5103404c06441240c1e04035001c102880070030250080700c2e000703a950540000340b80c019000c4501d0028004130040c4c02c20420081c0b82c40c41000c44800f901d00401514004200c5203000648407109814540045940080da81040d440c01011104040d850022060780345440b0074002600e1071400d01400c02c00d5001c041c00750941340402d005940d440d81003011190749079611080042e64940c542c00615000a00382140070642d0303440464070001c0d0f8440c620046c007040c0c001c0c003025100e040b0405e0006802001c1488183c84c1c5043c003001b00660040d60b9100140e907000c07040e0f000031000141d0b42080506441d040881d000503688001120303801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 112501321 1250 112500071 112500097
    0x6050d080901051908061f0212090a230301150f1203050903010203070c1b030302031b03090603011e050f0603070f0905040911041406150901020a0204050f0a0507050f 73
    0x10320707054001a41d86000c1c084c40c6040ca0002c407074203444166044000503004000484000012851086000e40d001c80070a400c40010b82145400ca444021110043c211030540180f0b61101c0c1912050104d10f145010340c0504140c0301d5201401500b03041c28414882c124500c1344c2c0c101c1100b0709142121a01720305600c138500080320011041d0301414800d2b81039819074a8001c00965032400c04510007049a20f201e0340076075410000405054800702a00d4030304003143d60540207182020040c40c1c4203940a00030240fa41c40c03a00041140b50129034034403000718081d00c41300031520b4061140c036144020f44460390300040d018074000d401c00d04032079985c0c2058a0b0311060500d00680d00700c0c08620100c405180720b510064010b03007804402000c000b1056000b201da00001d540420034030111a0302044150710580340c2540040060300203034103591103403008019844060048483c100c0e0076601042c01ca40742154211706141c40541404010b1400d0300071150007240c1c034034000d414241c41003080100d0380300b40c1c40c4130904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 112502571 1250 112501321 112501327
    0x31208040c21020a1418160e030a0212250608010b0714070603020a08090303060114070602070803070306060e0a050108180f060a02090102100908090105031905240406050d08 76
    0x101001e10340310b0900694090200c4082076544c134035602e260510400d0a520801041e650800d901c080701140e01c4c802c04000010b49149071070540c0540d0b801c8440403c0303d8143c084c20440001503100c854100110250442c0105406483c820819280d90346046030660b4041c040c8004000749a446544541503075400311301c25030f03100901d19114030f120420305014802401aa9000100590141e000d00180403140c0c640300c4407070b69000380d0640c42c0d200484806000c900b03450405018000c0610140013082c0c460742c0300501e0003641c0d444840194000300d0390b460000307840d4003050011a0340100c8420a002c8240e5000d950241004000392501400402c038606406200c1c2d0003203410502044842c0014040c88140c900c981084254000607601c03080480740503105180328040f000c4050f00c640300609402c00340241c1059003c000440e804ea00140103000400450030710102840c002c2e2142070f004103003418183c4110440000c8484070a0042811248501d01c0c0150802050712141000000641e0000c0ca00765 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 112503821 1250 112502571 112502609
    0x31609030f060b120d02030408070504050c030109090f0f0c050a0b030405060a0f1404050106030212061003030c03030209120705010809010b06180d05030406090e0609060303090103050403020715020304031208040c 93
    0x241c4203490100c118492290700c01e0406801000405c2615095001c0d56602501c86081c0330907540d0945820307030002c0003000104040c2e00c00b644049003941c424907000e8400d5502c1d44030306840c01c407800d205940b0001e4a202c00c2000349041035000c030081006c591002d04626041e00c6150701c455004020408044e00c07400045440700d41a4050f00c5a00440707800e038440387c02c041c00d25034001c01c02030000724003502c00c03400304c080741d4440040ca07140b0506d02250461191801c55502300e90b5038010100840c1415028002c040b40c82d561100d00740050422800200700046c6844001080100c015040b02d07444d0b40b4000c045160342e2601c00441d503114a90783d801d29045085076000c06c0040c0d481e01e0300030700315010120307001c10115070003a010000c03510342e55110302c8a03440e000100500524190350040e89540700300003206040d4002c0d0005544107000f030040e00c2d00b0555514000c05640c1c1407242040040c0c000141c14000c204094982200480c4149003101d103602c0c2a56410151121600a4603c03030050320729410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 112505071 1250 112503821 112503829
    0x180c02100e030418020405041109100c03051204030509040f051314070f0b0c011a06041e050405160908060709050909120403140c0103140a020c0106050312031609030f060b 75
    0x150050201130781040101c0407440400300250058041ca078460b5042080540503000031005440030050001d02880c5106001c407002e88105001060840510a080c49045001c400c1050030610490081c4c40d80340d80e500c651340c2003100700c6545807400714107070f8078084c180410750320040d024000c034035404600f5131014440c0300303586803134103030164030908220451000101e88071080d94040d0111185180007400a81164103401e003e03500c0320003101d50010700500c020083e00d01d14040c7c3c124150078a04410b120350384c40e44041802d82c0e81c11101081c8554003414008842c41d449117403035000b00818005030416060003030004102090610643e842a0380030800b20324800700601c501c40c101c4e02070760744071940e884da245864103c080c20854898094080d692404100354042c1c0240c03054501d140e6a468020340d14840729000941040c0303060b248540da990004101903c08014440e031075000100c0098491404103c411b90000060200c003003004404001000000d00140340b01340c0c901c1d030004000c6502480c0e0404a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 112506321 1250 112505071 112505077
    0x40513152303060403090501181a090103020d14010609050901050a0302040203090f0a0c050103291903170c06070c0503070201030203220c15050f041404150b0301180c02100e03 77
    0x49030b414083da0081c00101074000034820120f480c281c84012100004801c403000d5940203200b050201a4088010541550420014076800c4014140181080c20769080e900458083d603600f103d160004c44014401540c00c402e5200003404202d500c03400542c14032000c5840d409036444000d0089030048080384003400203020610070390160804581a2070b61500b050440040c00c0c0c40340e540800d150a110041c0c0c0c1304441300451103241c000404816210310f0000b071080700b0100d14150902c0400c1c90101000041d0340e0600c02040045144400d80c6a88901781c5075030500901521010a004507182d9042c00203401005403803a40c0c0e02401c005031070b0ba0300c660440300f10907c4170003070390804134510f00880700304500c0005d040c05880031000ba01c5071034010100c041e98103100d004c950a14001051004100080072545000185200070381f0201d014001d0b122090802c614503089540e0009010006001140c602a074200805950740024132070f0220b0002d000e501c95100c441002d103015122100b20181c0741e820421 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 112507571 1250 112506321 112506389
    0x9010507080d1d07140a080607140d060602070306110301030c0614070f140f06060303090d06060b0c0307060b0312070f051e010b0901080a03050a1107180204051315 72
    0x1541035012034954a80d41c1303616403070290145144003c04104401e003407000075041642c0b61040100708540320104190b8442400e410030016028040000003c1c08443d401450010001a001004005d041d45024816a1a04280c1c0c08020005000400200f44400070400c111001c0e0700f8060351a22404003c450302c0d1003500009440e8513800300707a0030308100c41c086480c40042d0350304094a28a040b560001500c0d032000b40e0790203074568014441300c41da618149512070802c0f4407990000603000d943d0a04100b035a0410112409990404101602840710034040c0741200380c42140500790244440c0100a41e90081c0d0401070401100651030504004007000040441880d43d0700c0c50030458a0200568040c1c4006038819000301031400000400d0500001d40041c1e960b855200c043c01e02e12814030440c1c62100300e40035032900e4400c8520004420001c401010b074070824424016a5603801e1100b0701c49110752150b030500e0400e107020140c0b040e01c00d190b009182036850b8068125224091001c0c0d031b8044a0000c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 112508821 1250 112507571 112507601
    0x3010e18010c08060909060103030207060f2006040213050c040911130b04150801030b1f030c080604030e0303280c1502030601021504121803060207030206070207090209010507080d 79
    0x7240300d070b1080c3c00c0b121451007460202c9400e1401d80e9106840c0340c407401d0a02c002009a404070390280106402048200c091156514207000c00a802c2e81c00c0011854210400040e682c002400b0701c410b60034003011301a01d2541074030060200c0e040c640e1284000384194415142e0700c1356240b4034102801c03107010480300829000640d5507803c549400c03000105500c81e205000c0c2200d13000f1659080f243c002c441d0981241c0d00101030008030b5403000e01d400f882c81c24040e07460340d5a008049021000030240001034000d814001c0013080d2501d013510340a40100040c0c3c00c2c0d14401d91050041000404103d03502140e21040034501c49039202808000f03464403404001d00a2202c0c00821400d5251002940691b200d00c109900301c0e07a00740003109040248020589010301303142c13400c0071900303072290003410045c80741c0c000007150b042c00d25034030344071034007240c105101c224016003119041c49100d540c1000032602a1080c8801146490b800800182942c07140720401045000c001ca150303588400d00380d0144541e03100c001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 112510071 1250 112508821 112508831
    0x807081207020714010918060503030a08040516051309060b03010f090501050a02040605030c070206160515061002032502040e150a0603020907030203190c090f080d0503010e1801 78
    0x81803560001011910310006100d44040010112203201c2481c501e00d4060b1507180500307003000c0c030b40f80300d00824a0054000c1c5884041c00110f0383c504000903c203828035940c8090f42ea05191038114205540601820001211624140701035130b21814a410511a102d0001401500520b0700c1c0e40545001340380302d075140d40380c60041070030003c00380c102540c5140308100030061a6502d82c4400c00700c2c0220b0041500040c001d20001380040c1a00e001010780d640000c0000e424980c4a00c0d0003007900700410000c40e040d411018540ca40e600c100298a070304000c08403101d01c049001c5400082d80c034000c01420f400f003a0001c016280710744400105441109070041d02c00c0c88140c442e17007001da41e51003070351064a40462004002903511030325482081d00780d9500038518a00b44e00c5c0d07180b048010f03400103490000c40c140144040c01d80502184903229141a05450f1041d01d81d290103012900070300158081c03501908141010041250b05c10216419108401d98100490b00d0b10003128403509042100c2003e40c1d840c1c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 112511321 1250 112510071 112510087
    0x5120a17040302090f07080c0f041802040920160309050603130b180d080403030f090b09071e050108070c06090c0e0601020c0a0303050a0309020604030c15050a020604030c080708 78
    0x104001c006980c0240d42c0c248180d00c4c0c1c02c0d214175100d201241c480c800035003107001080b041402c1000600b0b560740401c0742242401e07244d42c82160f13443e240000111081354006806c002d19603040c010360006038080c4100c5041a103849101c1001031240ca400000c09514000d04001014002d03017000d005400003074401c039200d240c41400100007078880a0140c9d1104103480004a644a8420550359407008213005441981c84004003520f210342c1c050303c210140345d10b0310703001d01400840d0321640b00c4a03400b90500307550604054020034285880358218100004562a840c4190701c51030118408545c001c1c6450405a564040115101c02c0e0000c40100901d04029080e0280314015020340c055400070100c0c0b880c40c0c1c495100680c1d480f4030710740c0c8580d00116030403803c001182c01100a00301040c45410041303075280e45940000d02c03e40c0300e41c20455407420751580600030720742c00760305d242c803012403d0421032724200326550003a5840a00400041c100b020186030341d001c00660106030392640d580a034545841d0801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 112512571 1250 112511321 112511363
    0x902030f070305061c06020307050d0203040629060702120a0503030406020306042a0f050d06031401050705070c1202131404020f030d05160206040e010602070f050f01050405120a 78
    0x10707518100000c0c2004041009480c1200e41040326008001c4201d5109010fa40e582c00a90001001d203018002c0500068020080600045101d180704082c0010042034841010441800c0c1034000075405042a01521306a280d000803122003a4044803451106c00c040c120503403038405036610082007804040301744010040150040d5005580481e024085601c001981c00044110b0354004514130b200c06480061590041520303090f04815490102d241543e030102e000140c039403a0740125040150550b8507202c0c010b080c0b0482d6004401c601c2c1681c5465001d84a06100c048039000340c8482c1c1208102a8003103584604e000c0180030a06030082c414141c4c402c40d42810101d044030180d01400156014921b03e00d40031a40a0300e021240d190075007800c4490050b66003107d40c00348101c0e04003900300300208100149540303e41c002c0216a00400e1301d94200802c106008200c1d0703026601070414a82004116a0054161001e444c0b059403411101c0c2200c000182c0303010750040d40170f010030a00503410844192 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 112513821 1250 112512571 112512601
    0x1020921240402121213030314030606040302060d06120c050913051b01020309130c090b0909010302090424020301080c0105030f0f06220207020114070327090203 71
    0x10041529804505070694441c2001c0c0954801c1000940c54001030040c070742903840c0c01490b2020000c0303c806030451031289a2a0b444140c07000c01c0700720080303020000c01d0b50040c102003c3d5001401400c0c00c5040460200301107000f01d000007440713a000800e4603a010b400560000b4000c0c000020b040305c070100e460900840002d0640100b501a00030140058050542116000c2c03515500400030180f001e01121000c4080070700b4000035045000801044000d07503140d103c0300c0d40c1d04e4900c00000030201c1e10103c1c098032060003540f2003e461041446440c50560310810a18112034040c2c450345000d136071f9450300d0310a1010542c0003185c2004010703200c220f1800a940035506983c103c500301e403103030840302d0010764083c001115010b00002d03c901c009000288011110b80c2c0014024001964840e100c180318200300c030041c89243d401caa40807400500b5580e2003034008043e03800196000e8035103076007618010106481801481d4400015504503817041a07010b28000050cc500b410440d101c0c140b41c4504440c0031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 112515071 1250 112513821 112513879
    0x70f03022403191410050603090a081305030d0807051e04270c0309080315030f0607020a051009080d0c021c030f0e01050610030c03021603051b07050d03030b03010209 73
    0xc0d144c00c00d02d2002a00c40d06005024142c0c460031600883d01e41000c1021940c0010b201c10a20b000301e11b40640012011000381a481c0e01110007004501e042800f8140340110100b050803c202c02d03002480354158001040343c3c0b48140c0d400c0558400301000c050094a44a960700c02d145540c00070801c5105814035034982e00700001061410700420705010012001e035848000d01600302c400c100301142c0400d00d90412445408006410b550a81425001041c14004100c40c0c03000541c0010700729100f0018284400d014101910004120300700c0b403600c039030445009072904511090f039926401039803e80200410401604400145040700d01c0110004001e03041140f500702c45e00c0d042400142d0700c000107000d00391146a010300700c1401c1e030004800480242070090080710615070f08100800c000e03500d000700c00c1c06180c001c0c2c40e01603940d21103401c40740d40208500c500c1c04503030b04070344414401d560b42d4080300c0012940515002c0f4801400701c000900912541c10b801c0c0e03100b450005500381000f16030169124030717 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 112516321 1250 112515071 112515121
    0x303050406151a0c070f030515070212030115020a060c0201020a0905030106030201080c030711060a02030f1323010e01051807120b180c0a030809040b03070f03022403 73
    0x30500c404241c81a900a9041d0f12061806a1507030021030406020807042d0481101c0c0c115540e400c031440001103d07042900d041c6c01a120000580c1c2c11a04242e07000782d501d20080c440c1001ea002402954081802801d001c2c08000800742400c0340700304614203109401c400104060040d04001900030f511540ca61008142903e10025907480e061184104480d0180c54880c4240d0b56464940c0d101c0e80024a14010700201c460f500140c5a02000348a10032100d40740016900d0511001d00758441600400c0040c0001c1c40348144000200095240e224910b402c4003d19180240040e10130b01404006c2c40c562031541c40c1c44100a4000c88801e114020205100f003580c18041d1500750f84016400780d0321014048555800202e100c85801c101003909405180302921003840001c1d00044111242c0e80c8240e55012000c61001501d1815204240038584100c0c01408894a00701600c0850112071001a1242182030780400513280707031038010f6440d54003000c2800c1d500c0c9480320f45240f104038001c440041c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 112517571 1250 112516321 112516331
    0x2090a021e0c060a020306030a0503070b0708180c06030c211006020f07060e012a022b0b07020a020909071d0c07060e0c04020409050a0516050d0203220303050406 71
    0x7851070481182e4034a0300c2c84000d09030650b180c00700e803c0070b0340c00503095035014030a240150700880d030140007030300d41d05105816580300c9041c850401062403102a043e65084513250721508011440007803041c41c440c205498035522076a030312104a241d4060360407140c10850b9505203d91615002075a250304c00c0701d0248000590b252240022070f92400300c6800034a040e8004001070140601604451490100c145080207910360b0541040d0000300e800007002001400c1101820210300e00144e140c400e020040c10440d164050f60001466100031406010313085440c2c0d440030800c59842400990580f6402a00c4085281401c19001c0c0d5030700b4403407049100050700b00300d4141c0c0894180d045e55004070f210000041c1410601d84801000f4480411940d00501c10706900c62902d84482c00640024201900e00082c6440c009503448144c03640144454803507906680fa20380140d4101d8244c40903441c0e461001031302d81e40c5403440c5807144507815658000408448c0741071410140e06801052146d4400d02040c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 112518821 1250 112517571 112517617
    0x120b061b0f0d0203030f130804030809030d02030c0304050105071b0e01080118020d0206130305061003150b010801291612090b161e06020a02150f0109050a0902090a02 73
    0x501c0b18008081d800068000300b000c1007219403070440c440d411107a07056520000580d035554440c17030703a44154030480e1186000300e6480941d03d4240a0403884104074006540783c42c8400d01c020b502e0b445540115412f011021942e00280300c0b400042c10a9218520340440d072007500c50f00c1c0942140c2092054814030741c2481080041119030142303914550f035005d0500001003c0c25820000142c00c14842440d807603a00c03140001c0031682c1042918040d680485050b01d0103411410f1459141c40e03150440b8041508001030340702d440e40d00842c1141141d1a0001c01d0700070755403240e82100c0704100505400301c4010f01041840e681007000042c40f22031031081e182c071f50042e05500310507142c90700e0900c00d1200c1a042030042d0704c4030700c1e441e800c854113041c49480a1124240c10281c0a0b481903040c4000341c9155901007038501c15285c040140203081002c030029882d6619000f1f1494981c400140500000d05499001145100e896030f08810a4103500820f04e40c45131804c0c080c1d002c000e4002d18030703801120303244c1c3d1800c607 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 112520071 1250 112518821 112518823
    0x102030118090507060503090c18191b110718020310140a09020c01020412050a0311070f03110d080d0b040606050702090f04170a030c170c0a120b061b0f 67
    0xb003525030280c080c00001349400c0c01070741c2c0340c1c000601005690217081044070491380c0c0c91000314001090310a0b140c55905010580240e041509a24031010030700c3c01c24a001d43d00d0151400c0c400700b8801d0b10b00f503004100c041c4030b441d0802d0260fa1040885103031030780043e42c41000a0300914030400c842842c011189076603642c40d840c14a550781d00550045051241802424510340003059001e40c118001342c6013a80d100c0101100707007110f80301510340340c200c00703d40301c1095402213510b008800900028450070b420140c0c0002002000e1000a158440961f80a00320791558160006441c0e00200215228501480080301805001481504c01c0c2d10f4448080b407154090015605072a030003a042da0095581c802c149545558040d0007550304003c0300380000ea11403c0c0000030003400400d50303004200c20780200d0025151007990b5400315001d04210081241c010302c4082544c40d00203072441d004410401c2c0180c02d00007043c034020ba554028000081a1440015003010701000c6002c00e42207503050fa01b828905 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 112521321 1250 112520071 112520081
    0x102705040506220b0f0a061106070824011e0809010b010201050702030d0902120726011a04020703031508030711030d0801051521040203011404031218020d050102030118 74
    0x540c0350840011451a144505074028584c1a4000d810385600282480014446080a030302c241c0004068501e80442070400703011194108402d820311800c541081c2c51100d02c0b24410350342800400c086400001100d030b100703540481011007801281c0040704603001c0018910716086400030800d60905510b110306502c1441103522800c00b0354095414603070801156806002004020707640701c0c1b146001144452020b0005100401c0c0c2c252402010144031102200c210743c0340c980a000c03d900d01401c20314610503801d03c40c07484590880380141d03210140d10b010381c0200303080c45981d00580850710000c41e40f07800000041080d58021190305840450101c1055a1042a034082c0800500c1d014010003035030420503102a1a4007030f100c00300c1d00b012080d003203a03255164050b0010404400d004140400d5040a00c03a03054505c0c10003805004500e040d0300e010b07040f0b0340103100340106240d80b0b02010311011128400d5983d0540e000700309110351400c03420114040e4001380036298042c03076003d4040200c0f0980d031040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 112522571 1250 112521321 112521349
    0xd0b1609060e130b03010203310302150a02070b010f08160b09040e03040905040c0f0b1204020f01210203070906020d020705010e0a090509010c08060618102705040506 73
    0x100605442e0040038000300d100c601455018140c0c98a141500300d543c28009144034040883c00041002c0c0140c01c00c174045044800c4050303245a0b04030b62640800c0d40402c20010030065102c2c4c2c0b034070685031685083c000748900c05c8042c0410001c034001160080d0034001c0a02154031031030440b540101c00404002e503c00152150b41c400ca0802c0040c10360604140c0c10001c841d6948406072030078955a1410300050301e10407181240d800e2620041030101441054440000e0b00d42200f00710b050418480080150301c1004e000a1310504242c004121036a2050040c0039103011008030980720b211580b0200d40c003941040c0c40c00c4010034004040481e00501c009649a1881840da0041119038907040042d9103002d4818a603a8004030100780105d080586030280714022031b0918000034250f16075140040c00000b01078112031080c0c034100101d540c81c0003944021080010211500003000714592000e03074281340c6841c000c0240740400d140c600d0b60800b440320005c007202c809032020300160303a4400c104851214040f075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 112523821 1250 112522571 112522577
    0x8060a060815010203040b0c06010f0e040f030c150905030c0105061017041506060e09010506090a0b0f0c12040608010e010e0f07020a0512130f080d08070c020d0b160906 74
    0x80080e46a40054000205201060058030f00d00340c7c8a4400c0046980704050016060348080700411201b429442c01d070000380040c411120160400c1da03075030006149444070240c100300314140000c080c443c8000100c0a9818031123400c019561091818a85035040000405041d5280c4070000700c0d0b0f0309100618021005847d96005221aa80c41c0c208142038070242064403840064080c909a11a480c071400c80034140a8540f654034844e040100f1a030110160421800b400050056440b40c0d250a039004040e10030000409449510705060b0103c140070340c807400c407581d206030380c0d00154039980203000b0010ba42c455642c000c80d503a03d51700d4400aa100030301c1a400300703030105c1c00042c1e004202446110342000d800d04c1560b9210031191a601c4c98102e0144440d414814001450800c12081180d803400030b01461019805051806101a0702d80503d6400700b010b2107969000111658400c1e051404125401006610416030505010082c200201d4602c11403402d0703c00e80040e01402035803440111501aa = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 112525071 1250 112523821 112523837
    0x31f360615021e06060a03030c06020706050f09010c0201111602010e0d080715020c0604030f020c090a0c030609050606040b0901050f040e0103020405090105060f010f121d0610060e0f130e0d08060a06 87
    0x48d03000c440022440b041555890350034001100024000d001e200e011b11100420809c26041400c1220b08640350141041d040d0382c0b40c040505201c20025041d65840c1000401f240315030005400180c580c820503000c800c0e0b0003041180718408001028000e44203031401044d2022142c1c2d1080c60450803889607800c0c0300502d502040000380000d2107410311060030740c05031056034490200040442d004160560315220040d031109264460306d0340c10700c0389100a0855020034070640c20040040760b1746210300e0040800c0100009586407a99000703501700e0754190903131510603540c1da41c3c4101d24140b548081c00200c2c400d90038040410310f0700307005000d01401840f0041078064801d80c40700041da1000c26611030501130004552070003110425510810250640d84003e01c0307424030130303581454104030005200c0d14003582c180300b0078455107902c4000303d02030303000a84d40a19010842c0303001542942c00002c160443e00d04151070075014000104074138144950980300c0155a0300c84400300200841c0301e0040000203a008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 112526321 1250 112525071 112525073
    0x30503040315060e04060b0111070506041502010b13140106090b120a061806030210050a05271e0301050f16080a020f031f360615021e06060a03 63
    0x107800d40d0900010b90b80300090b03c503525641c442d00d42100300e070156040d030365070921400903580042c4040100101e0502030300c5114141b0000071346030f00560107018410a00c02c846180014000d500030041007900a000248180c0400b005c0009480303010f0040c00801c151368000600310740a10401c0e001d4604004081d814480c02d03c021504d4010f00410300648551142c0c0000303480310441400419144c82080046040381c1580103000b4840104003403502004030400c6940c0303860b544142502e40c0b44100301d0f90101145180e074500c141c259443c020f0319a10a64a5200c0e0890114030031100c0c0518000394002e016940e16000741c0d0341d14000860740c2e50035105400d100c0303a01b001e114810b070507440759110718010300f080c00c410302d2014660402c44841c40d02d41c0c994450328400d940c1ca00c02941c018410b115080040081200d2810741901d20b10b60021b503992540031041c0e0f600442a00024003030804803030114035203500c1280086d558161100380c1c1102e841003a40c5580328003c0890010300c6110041c0c844641c4074030b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 112527571 1250 112526321 112526333
    0x18030602071b06030e06011211010f020c060a030606030b01020703111c17070203060a18140c090709050a05030118110112110a08090615190306060e0a0b01090305030403 74
    0xa101d08541800d5600303488640500c4082c4003038081c00b8107603400542000c1101c007961401031306030450030325400310500c2480044d11104102c005900b0030320b0b02c85402440604217a140c4405610030303c0d4020b00208034029031b194954402e8040ba0560b0b501401010002001641c40c1e0000c0c1c00040d00c1403100540142a505113200450b424910440c407541c020042903c402d503000140b100f40070380f0240c00094100c29880c0c10045030b60840e848460401c1303500c40f007001540d04011100002407000901800c2005207a40c280300d03e540035007004d441c40e03007585011a4024a8000507001c0c05101e002500808141402d0520444144410403c11104844003588550300d415264824041c104200c05103140040182ca01038400509000c11140e40c07103504589018018081c01804202d880d0b004004010408041c000b00d004202810b40705503040c90811080e030442100141c101910a60a15100045000310194807600c0303056048001c0118542107001111108007510024000e54018002440400c1d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 112528821 1250 112527571 112527577
    0x50a0504020a15020709050a09030908030414190e0403080405061803251704080706050306060a0e0609060403110a0b070c090507090513050403090f12060203090304092a18030602 78
    0x503ea0048617482035503108a43c0c02da030720444e600c0c0c504903180d1610400301900040d084018001c0034001d1801c10781854021401c43c0308020641c1e1240c510a51003800c2045411410005401280e03501c1c0c0c514540380c10058210700042d54121024840c81c1c0008000120ba1000e140340c100b950f41c0607521b82013100601c5030200d0446030782095042030803a1b00000140400755034030724140400b0413841c1c4a03440c2c100381e603050901650069040c85002c2042214030355030b900450f50701d0581c2e410102c081480c0d0502184980c0142550b00e40c201c04009004020b104c3c00d200300046e4007200b164602d0243c0e4541c0c60700702242c01100e100805040d0b28480c1841404483c0d00300c942d000c190341c509081e07a240d4540024039180010094200301c07603a0340e0f003031005150340a10114090003000103010034191410300c1c1d1046c038241500d0040e1400342d002c00850000c404c284100c80003002c41d20824441c1405031401c00c41300360000348941c5600003c00c95200c84a0b40100e4400407072110361051901c60500c0c43d11a08080c0d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 112530071 1250 112528821 112528859
    0x1030b0915071b210908010c08070c02011206030804090b12030c0706211a03010506010c02030c06090a0e01080607021b031906091a060102010b1806010c020d0f15050a0504020a 77
    0x101440c2c92004c2220350003080415410081c0d65031301ca514600344890703017141c0c02340c840300c0d007080719001c100122243c10110a19925a0a292882400405c6c0342000020304e07850f000104100030004000600c840550400e402c200d50031940c800e01c01c042c1100361580da1144008850761900116803c001c224091905003082c1c1c00400da0a000d226038040080b41220001c81c10b000d00d502c10901106501c2c03d09228081c0d100300282418600853b440c0c001a40d00c0f183c15514601c1264001414101031b05c40d10610001030100d07202d00c041c05c0d611202c1c00c0b0b84400e0708030f40381001403150118048107142510006003400c0d80241c05420390860341104803040d124840e800342c40041d01c1d081c1c5500090080c0e40050480d24040203904a982042d100090a440072003a00720302c10b4030080020390354510140d1307410742c21450900307003c0d8000f01d81e4400301c3c002c145080c001400d01070714500d40000740b042d45000001c207149a00c00401c110380c1c83c000140c00b21042540c001e9040403412206000d0084088100f0600d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 112531321 1250 112530071 112530083
    0xd0605040305120403080a0b0306060a0e0a09020a0b03070e0d0c090902040e1c0f1d0f010c0b010b0406080a0203010308070209250203070c06050405010c03230301030b0915071b 77
    0x21201d45210200f42c40400d41d012000200b1410030004101030074030031014414000c802501c41070410300005083c160003802075540003202a808620011300690102200603400703856410020303902c4880584a400489484001c0303a99258004244e107003107031058041c80d51009602c103440c0d00344031031303000100903420003260829540c4440c9074003080c0400105107000f200e542c11034207001002030300070b12055659508200f070050091541441206a101b000c0313000605860420300450f005004031030265075070201820740c401203000440c22500c0f840080040d11a01d0b22400b007103868444500c401c07071100f44009880d0100900c44900149030152040340c00041d425800c004603100c50100b481c2480060000e48050f03480001e0020800c54400d280300000e21090409504040ca88400a0000c0c408038000404101125800400f0303d214111052204071000780026120341c0c5070300e0318000240d01624002031a01c141680441400ea880d102c0d940700380f2941e074441242d1008100030b2503608003081c00490305 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 112532571 1250 112531321 112531327
    0x120f031d0a03060b040c020111070f0221160b090105040e040606030204050c040e0c0c060c07081e0c010b03121e1207030504120f050f07081909050307090207020d0605040305 76
    0x369540301100e80a10f014101c0001c4c008020f6080000300d400000c004401d69040413501105a400c41041d10501900b02807180070f90601031001a00d42c10001400507042940382e20100d00101e00003890705400b150007200c0860064461241040d1806862100e0340050780401060040e400d00f4644160010701c00d41011450540301c1d030020703044e6070048a1500c07894002080400c0358011451120340c000742c240d8038861402d6005068941c07115801800c0355544040042c14a042044e6001102e80c690382c1c0b110440e00400581c010100182e0004070f03103e5682d0b080ca03103401210310700031880e100d10078030440b1064500301c440c0c004d01490108000355900e416805125030b44414000b8410248284c0c210350300054075140034507040c00b50403d801d030f48004106080c64a883c840e074016046881c02c4d00c1c1d203e60135844500610301f10f06a4420990001094020840c1c2001e81941240d10700042c1d540c1201580c844c0d81e01c03100d416040b0b008820010b5403080c0c20034000d0021445e150b00803908a80a403500501d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 112533821 1250 112532571 112532627
    0x3190e01060e060109050114030c07150e07140402121501030603050a0510050108070605030105060315101718100207020f1c02040609140a2c16120f03 66
    0x308440040d480010a40780c2c120030046a0740c1e000401d00058102401c0c22a060011308c8120f0105020080500c4a9510b00041020a0114004c05e160b2004200c2000b8007601d682c209009840b125584a50358104c08a40c10503819450240260b981605001021440359903801c1c3c1e0500c428110b444401d0b05040d5035a001101046007408440044d50069000300000312036696440101c03141640300140300d030071a44060102541c000c0461b030454200711030303003600d0303444821002102c20010b07490b107944418408881c0000903003055042004a8814101d142c280d40c0d2800b000351212003450503510581c0050440d0b9418035031550103440054000b5215031003480d8004c010600070a03a828045c040f904034880c1c02b50031171800c1c0c0580005498284c106220400c055400100d044070041c1003101020f0300d03813000c42041582801e000e24005000c441c40c840c0001c504c00410344a80c484040c0099001c43c00c140450f40d0030041e06464900c40c0e00c480307111403c80803511700706da22810b0382003620900c82245040340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 112535071 1250 112533821 112533823
    0x6120c040c0e06070b0609071404060e21060f180a0311030d021204050c0604060c02061c062606090a0b0702100911030c04051902090f04050f22020603190e 68
    0xc90f013680b24042503115801d00170108606444000c041d5000c1190b6102445168041c04064904030780c09810003c400c002d151001442c08036605c0c80c1c006140512a4556020450028070540107401c0152181e203142c07100b0100d8400459800e4003d07203035500402c18040024030070140c0c030540c40c103c001a642001c410030203c0c2c0a03640104510f081010182080c8410b208003806203400d504c4044410910305481c101c00508110002500a4822440441d040e441101401e151002d56842000200001d07a10b07446040d03420070000980005001409504c0090024000391640c00340000c0c00041041e036040e40c0c0c4070020500000c000908601407140d10765000d0007a03010f00307030050348201d40405210074210203040c503106005c0101480741341000c0c24000f80038003c0d40034203170f11702e0030704405607940c0044008100c0000034410003a800524000404c1a0302d00c504481d503001e09841003c00200900c007081c006040452440040d5105608001040c001c01000c1103407600413814203000302d50101c0c0e909181d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 112536321 1250 112535071 112535077
    0xd0e070305070e09060403120903020114041203060801060b0415020a12051903020901120b0307081e0c03070b03070305060a0503100f110a02100b0102011404061406120c040c0e06 78
    0x8070380c00d074001402405640001582070782d008620f100149040d1605850081c412940075507a003085503034481500d41418402c3d0001a001d0b10750300d246006600b001d20b0090241c0f1152840000001d0bd01400410242c4040c0100302c1120399201400d810503042c8a4401100387c0003040d00c1080d48900081300700020310818842c0c0c3c10f010952146501c6032107003106001d2641c0003010341c004252041028800ba6a040b058450742180e803c2400200301d0b03100700110303252600e00e42081026228002e00c070340d4100c4600100078800603204c0c003554152051b200515944401c0f80c0501303128000b0520001e44072510941c04980d00420080031000e015980700082402c0c52002c81b12042001d4565203100900c20725402b80d6007072245003900981c680120720000035142c0b03401e2003d840b0040c4c2ca55580c002e444e032023501b00c00c0d50603000c1102a600740c207040c5441c0005014080042076011b1481c400981e00d0b00d09549403e8140510001400c82c00701220204401401c45803400010b00107204620380c10390b00c440c005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 112537571 1250 112536321 112536323
    0x2130914030301030201020c0406121218230108010302010503011e05060a030203240a03080c070503010c17010e040f08070c090c0c060b0d0f081b011104060e090603030a050d0e0703 79
    0x207140d070303941507000090130b044000511038040c500b0100100010001c03031061904403504540c884010f0841d5a104072400c3d46003401c0d00c8019200f445000c94203500d1041f040c0c015044047d04c1e0700c0308454001c0103462409091201a010401c240010080e4554640c0049020340c5140d400001c4162030310005085030300031fa20400c6c00641c0c0401000312040400c042c09003001e52040501227001d4a540000d0000c0c405800010070321000480c2c101c0c1a43c101f081044040d250050007402402c0c800200100481d00044590900e103c030034000040c032103030352040385003d181c001d1640c0c1c84010140d1100011903007c0302d0102c0d400c444407034002a582c4013a10a0101001c3d02da929600103200f5414808269505d41c807440d40700d80c0c602c2c51900001091009010b40e0250302c000c2c170301e403221340d00002000c1d00781c401810314403554285001241c00242000042090b285180c9604000b81010342c280700000780f0031160140c25503c10000c02001d540100c01074814000020f40200f80000b0300c106041c10304030181c3c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 112538821 1250 112537571 112537573
    0x50a15140c16091d0318010201020904180309060305160c0311100b1e0d060b03120307090603050903130306110d0906270804090b01120e0c030c010212030402130914 72
    0x10248103600b80341c01100703040340090050704c1084410103411a164840c0151070300345030104102880141e4000c0d0143c40109000401c1000713014030042e0a44810000d4207002c03400502552004034002d8000e11505001d0100007040e4a00c08400761001c2d60364038402501a000d110044200a194880c10000600c200c04454401304a003101c0c0018007030b1400a40c0e40140c030b0522403980342005500c900d040f200182d030b0044400305400402401180c2000004407103001800c000008001025400010610803030341107582c20402e44d591000142d403680201c199400740303c90800c1042022800c0394002288866041081c41d00d4026070041c0c1100311202090b08460590305c655110190b004c64034210421604101610324280f041c41c2e5554056100d240984008113581e1804001c242e44a01c01440b24190104010021107035114400f940c0e90300d004c0c1c0007030312910664541104951021420b64102c00c141ca00709425501c5d075508010f6507040082004910a5589240c000820403d4002000c0da44000c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 112540071 1250 112538821 112538863
    0x140a0b03070803090105030a0f06050d1202070f03020d02010c0c0b0c0106051e0a170705060a0302070b01050604060c060e0a06110409050a06030b04060c1404080d09050a15140c 77
    0x51600307008050348000201c0c1c03c140003d80340341c1d80140031640c1c0a08104030008007460b410f850706d402041e041d00150f07080000108002d04100074901c0d241403030380c260b400311403880760344100c0b2402c0c20300107000c000d401581c0c03050748000550050980008962040f003260645540f10071803642d00390000c84820055070f45400701007209003441c6401904891001c81d060440d0a0740001081044140b071040b281e003405095130100c0f1588003801000d0143c140100360a03555000c071000103010b504545001d42d1140344400c000139407403604038115011103486484030101c001d00f42e12410020501d03ca03000b0100c0c080c44803040d0020380c05104100c4a05400c80e09a6240d90030280d80a04544009141203000c6141510900100d6100780160b90700c076a00450103d10f4911000c41116094610300c4549150040481c0102c0c0e0b1790004900032a2880c2c50307607250b4010558803020869a084140f10790a20014144030540315948110700d415441d0600901482c81e05158070002403800203d8214000d0661042c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 112541321 1250 112540071 112540091
    0x904030f21110904110c120c07050a03030503151f03020d0e030406030e0d08042d0c0e0603150c19020f030d0204060306080a110910050904060c1103120c030a140a 71
    0x103440344d5407451412079038142c00e24003034034400c5640d440c1d04102c0700075110010900c124906d08c1040b241c0c4c05840080c0c0342d126856600d18003e822a00b00780c404690600400b4445042410301c07000240d8080016001484144048441034000f5404441019245501d4841103031095138200010700080090359000244130b01d48000090910300110708240c00c02080344140320104e10620000340205e46460120252114070031031081004030380d40d500038003269080791b0008000c0d08645110b80f1403a0250240c2d11529010400d01a40410031035450326504000d2050725060003d90303866444901c4180110740342180d0114040f8659000f4150400c990394000800303200269142c040d82000b44443d0004000c0c0d41c5d010b5039440028000489018002c401c1c004c0010708540c880c010200040c100a000c10341c4908042c144a07004c0c00c82d840a22002c01e40b20a03003881c04c0300002080b1400754894842580032501c856640301c009600180c400e0350903a458100c4d081d001c3c07080250b52401000c406000003030225030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 112542571 1250 112541321 112541329
    0x612030f031509070801060203030739060e01330b03040b06010e220c0302210a0b010801031203020d0b0a0602010c0909060f0b1c0c090e060904030f211109 68
    0x40151040112540c0108501600000ad0301e8010855040c0040351007400001a655840381349141001e903100000780b03214000400c1c0c0354060160288005010183c0810b00c1107003030360440d200596401602a40b0300d442813400807500307030155800c2e045032885940d0304d01c0003442a030400e550994030701000d041409229a0008055142d405054801061a032480344c010548103040e0b05030441e405171220b641810452082d81210104140401c101e194001049200f20400d001100c018030704626100a02200d0341c06412124100e95204280302c2c2201e00c5014200c0c065000035144e03400098076003c08000c42c1d9580c4030300d9400b030200c5600000b0340042c0204010641c15aa174051018149008014002c41800820a03c203403100c00d1a01c5544003407418072600303d00307044035139910300c00e00d00700010a401d83c0c0a100310b412529442940b000e580c882c030301001507501007901c000340403c03001c8000d46031240c02000f8110103a01c070081110800b044802269040e41d405d000454600300300000c0300e20b0507280c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 112543821 1250 112542571 112542589
    0x61803010501031a010609050d0b071403010603020c071406160c03022706010c02100309020d1401140a0e030403150e0d0203030106020d020f0c010c0c08120301090f140612030f0315 79
    0x50389140400410f460240424458180027001400825819000408950061804412840340022038a07600c2d1380d030b00b4000340290050541030001e4004d900740042d0120680c144141c071000020441490001400020030f01038020140456503164903043c0000540d50740c0c1211069560444148264200d40c00354004030310200400c0a414003040f0010b100141c2c0710100c4a80701d17a01541130000f6240c0a50000071502c2403c141d00502844c00b000c5c545084070700640214010848800464030b45845d1a80c13141d0030346210003070200326a0700a00c0100040360584050020640100c0000034460003c0122141401c0d02c14000c1d002580c000001081030681c1040243d0041c12188040c0540340d1a81041e66190503404801e1030400603a20031020520514440c144002c0c0300d4841280c0c0c1e441e10701da031400c50b65042441100e40c0c0b10729020345510300c0b41c1d0300c0c0683c4103003e94004c28040700755103440800c48280556192a255488284020320081c20000c004500400028400c43c124014020402180303031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 112545071 1250 112543821 112543829
    0xd0c02010213050906030a0501051005040c020a050604110a03021306061d03100c0318060911040905030d0504140f07090609020702030607080702010902090c0306030f07050f061803010501031a01 85
    0x181c410003400e400d10400b2100c9a003540c404445215080d01c0d0030000134500380840c40040c1443d481c010a02c14019003c2450030116041510140806404004241d0310f0b00340001000d09550000000140051302d22111084202da00800714a412034983c2c02007550220400d45510015549000070300203a50401600c0d13180340051080c6000406d83c03400400d1300c4280c00080d85018036119125000c02601035040381e40d5000d10120313111900401070400c107025041000d0107840c130704d0903080186034600b0311340503001009412000451900c400b400b000c0c0700900c40100103076044402c81071189400c180a000310300003c8007450050113003a050104c030318101c40481d0b200009081c0304003e0f80c0016113000c101d02e540311b00d02d410700b809030b030769403080580c0504025680290310a15410800400c650544003940c00b42c0001d800b19280c140c05000025683d0b002c0e40038041e4005900d0000041d41e01d0104010655140443c114050203090800403909442c401c0c3c200b2281d21510080c1c2210103400c40300203078010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 112546321 1250 112545071 112545073
    0x702011a0405060d020906060f031003030f0203030c03070e0307050a08100e03090f010c0f0f030309110406210311160518040c05040b030a050d02030d0605040501030804050907090801060b0d0c02 85
    0x14100f0a0002c1e14504007a00001d000b408a00000381482d51003100785c40111142080c02030f0741e464174091216500c85d907400114007140321420086004e41c400030541e80b140c0140c1120f54650384071503109440707620046c00115030502c1074ac4c9000c42d243e22600a094000e104400c01400d407640c2c0c186910040c5c505416501969a00030b03c81c0b40d14079582e03ca8141d0702c51800b820300071925401030a0400340402700c2400a401d062403160380800b0580e01d0340c050445107006c2c246020080305240d00b00001d51745640300380c1c94659820182c4003490309440c60791800440c400c2c1003418003040b03920841070410a47e0b11280011044540c0d041001d405c14144040c191140519036004525003603881030b0b44650a0b0168602840d43c41c8640429624101301c44061540c00404554034104d007150020355a51003c40e0100049003001000541400c040c081d050603284e020900c01e003402c0c00c150500140000051414042040745500041c42080a04c520341c060a0320380f0030700c1d41d14100c41180b2800d41c4c9003500c00c5c1c421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 112547571 1250 112546321 112546331
    0x7050a12090e0c030103030e12070605070b0601030b090406050a020903010e071e0303050406030203150d050a06060f050d06020d0902090108071d01061d0307090c051209030c060f0a0908030702011a04 87
    0x43c4a00d0078103da0540354182004c125040b030140c0400c2820010420f00300686c4550358020594bc0c0c0c018004d010080d03c90b040a1081c3d0341d03120300441c152084034517000e0f00700c04508007040c00070b0841e03008240d004d03000c24801414420755030006400e44031070906c109060340007240240725411008446010040308441101003ca04d180d900801600c45c1d0310902080642c0800800c1032151901603240904a00900652034903403942000768039651102c03c1101c0141c0741c108000f030b00b41e01400c256800c03501d0041c0419020b00282d11010041d50003c03481c010045e644102a5006a032045405406801d5000040500354142640302e4494510600e0200310b60391802d00400c0700070390208241c25450a40740741c0340d81c1200c41d02c0100b0b19146164000e400340c1814240c03c030ba0455400320160100d40081100500940c072443c542c241c0381d10904142c00c0c9650010300c00105508d041030512604402c5044000403507948079140e600141d0400e45061006075141c0e4200c5910100881120105040031501045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 112548821 1250 112547571 112547581
    0xe0402010c1e080a05090a090e0a11060408060709030302060a15121502040602010e1b06030732071103071404090501060e0c130902070305030f09010207050a12090e 72
    0x4040d0410420040114540110188a90300e040465070410790380f280000d901d13510b2110000c0d04035000024454000c1403201c000103000c0100d4020180500301d01c0c00980f2401c2c0050700c0c0c551010120403041a004442000f0016030b40008102a6106089580d502400103003036160003818038102034002d55a003070070f00303031f200341e8100a0102000031a19194424541d0444500c0d00070101c0c0d8900130f110401c03d01c00303d80054529010740010181c10140000e50b0070078101140308410314a814800a600514240b000420b454025404402502e42c40c1c0d02c0690051282d10b0300711b60380c901b40b110003030341c0d00f001103880da04011042c803080c82008800c030302504e4054144952102c0075048984114812034481c22170b442071003000e42c0002c1c060600260151010f280412840b50503500292408150741643c03071000075a084107109540f8000c0d030582d0384a1a54441025000116a0182070100255400c101120020b401002003034200391081c0c0416811241048000c1e00051703040d840192003140d0303001040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 112550071 1250 112548821 112548827
    0x3020310240311040b010e042408070e010b03190905010902011713200d12021c080a0b01110307030e0306010b040605120702010b06041706060609010f0c02280305070e040201 76
    0x1c00b0502030703c002885030210401295103104100401e0781261034401d41101014072050341c5402410907a0f1303051004ae9031200b005589141c0b41c400c524000010100501c0f450001900443d00100010904002d203d10051103008a0b07808101c126070b2a90344200c56011960440710840184010041d1410603241044440840c0d00c0075010050500031900b41442014113002e948266001000c4c10f0819103180d0340c500414034504400303806000d889a410344403414102401705200200c440c2d0b503140042c0c1c0b101200c042c050703d08400d12078140400e2000d6042c0506080000d4840540680d88100c000c400c080e040c1401c002060b0030000c031400c0100024407500d07400030210f0340c1d481c9203c5140c4140d6629030388102c0c01001c540c1030042d44140e0000e400694002e1403030000c100403881030f054600e10345958040084500c10b002c8410301055001000000050041c0010890140080e2a544d00d0501d44043c0c0160880d440c40f03403500511041310107005100c800c0080401405071140b0325074090826800107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 112551321 1250 112550071 112550093
    0x8060a02131205100c140a091a04152303090307120201061211041d0307150603031e0e09090d021002040b07080a03020705060c0d0b0108010501050a050c0106030203102403 75
    0x44c4103e80c0c407090f0503008244074941c3d04030301c044052203031900c450207a140242640c80b140706041c074107401080010014113403001107500b116050034aa40c0011b5540c07106803010701000c030b00c2d4204181103074038500000041c03800542c420754458001d140d549a2520303082c07811401c1e01d01d000d411680351075420300810307a182c800810100e400c2050a0400603401000a000d42006070700c1004402000f00385041c0c1210010207410514810096200340c0c1825810000c100c41142c40080d00290011207a41d80128801030113040c0500d061070040802c903910004500624400c0c1c7d62121690700a880b555401c80c2c1c10301504640c9032803407805501d0284bc00300c22031468081c0a0018091030301c009001031005009a0444006940c440b007500c81d14540344018a80a800070b0818500d803608150103010f49602c40c1e000d071416034005840d01410194115011216500300c01d500780e20665813180040050b0750100701d520912615001d000c2b65a00e8546c10310a0720304d9100c031034460f00c40305506092001038042005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 112552571 1250 112551321 112551343
    0xe0609130b070309060b0301060308070b0c0f09010c0f050a050309040c1704110a09090b010312050c060705250b09070b040f0b030601090905040501060f06020a020a03140708060a02131205 82
    0x82207100e11420014018203c0d1b0103515410361901b00e00100300300001000d0a41640a01141020340c1d6032008100180c0c8504e5101c0d020309401008144540d602544240020901a0454403102e6045070795241c50603c0046040e01e40341e0012030500454546405510541000383c0341230780169000c00b070790080c1c0c1d07000a04000d001c0c0304182030b01426030320b800380040d004240b0200107201065041c01e1581040d1402c0c001510020b10b0310b060344840d14011821559071803014030081010307543d400000c95240d003015118100940c01000e11002454500400050541c02082c2004950500020712807405400360f0010f40c03d0b0900780401c1066407604c0d1000d23402c0ba03039001c02d001da9030707991500100c0c6c810034a0b1700f00003109407405061106001c0154410002d0300c00c80300d0701c00241c5071147c4003130341d84e00b0f10781200035801140c0007001d10014142e140001000d00ba001c080f5202c091303e03003e4840c1014011030314006843c0d80031a642488806a8403003500605640011101e04911911404e440c0c0d011005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 112553821 1250 112552571 112552577
    0x63308070b0d020c120a020c04020a082715190501050d060c02121815030118020f071a091b0901030308060a0906060306061211070b04030212040e0609130b07 69
    0x1003501c0b416800d90110b402140b0a1000d0702e5a00030640544116500141c2032440103206182c900a1141010302c2290001041a102e1614641d5005101000180d4070404d0030701c25400780030441c04102c030030000c00501d02414450081c1c0d518007051815280c042c409600401c060078200100055100e518901075500d42003400401c00c4085004181d103008441240c0c102d16442c0000c480d5280c40b1b40c1040ca00715420b0032101c030410420051151140e40c0401e000d1440c051000c0000d00310300c5031720b603801030165950142045013001c1c2c00d43c031407895003402059175400c0d00c55004104a14000c061103000510791035171028410900030f60001c52210306c1c05010082c1405180804946640c0d14410440001c000c0d02c9014400640c603054000c01424540c414140400e208040143c61106580644204a01b00200341070a10300a0b442e0046900e4001d4008c3e0158099850909250307041100204080c015100c0d04034042d003002c0003404403100004000104c0d000100d2503110000c0c890500403900989146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 112555071 1250 112553821 112553827
    0x12020f030109022128021809030f090117070302030f070801120f0203010b0d2303280c060e01051006020105060112150e01150e01020a08070b0a0207063308070b 70
    0x41c4595162403410708242c2c0b84880341c034129422101a174800e032040c00e4801d4440008041240c0c411418508050301e2400342d90b00103110b40840b000400d00a40a0314030149400c40d44420700c50100c0a0f00c04042e036a00002036000410400c1484c601c04103d90080444d1400701c0c07096140000510303144000000042400c4403c144417010b5640c25040040d401c40700500c4098095101d1501100c0c0c10202c0c440c25101c170ba833401903040104e5002c0283c882d1600041c9924175000003143c611025007141d4046541404102403406c8040340e1244103442d1081e241c803000003450304041203085c410300f242da0b00c01021a810801000401d90340041014482064040c022039512201818540028403503000b00345010128000000c4030390007440350044586883d290444200d020900490b10b41c620014050840b01080203080c001451782c022050780071000c480d0040c2802c12582d211800d81e00400c4a166000342441302900910074002c238121141e031030f0600c0c000908c918105a0302e8807000c55201d6800b89000c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 112556321 1250 112555071 112555129
    0x6050d03090e06060f030708090d020d020705040207051207050a03030f090809091005040e01050f0f0c070b07021e0303090c0105090a121b03050d1b032010050112020f03010902 77
    0x64041c1d0310541102c00090303841e4a0032000050582d00e089500041c98810ad2000305816400031625041c0800a940640040c46c18441407001942c40480121800e120f11801485450b045401801c03450f4483e50240c41c4043c41414010155801002c48018603494017002100091050049590b40d1805860084141c0d03110758400c203555826500003a006410244e002d0b0304a10103502a0344947c101c0c2080046039112504440141c440c2258222110381d420029500807132018000b15a110440d88121f0301e0321090081d02c4480754a9040c000440b83e8404400d0202c03105d4140030503880c070303103007840c0050030001d4480019441e44c40364070940300c040c00104000d406204203400c84141080d081955026503503980c1c5070440d524030002c100c8400003000103a40207601d142508580c0300140d01503650400040358040c00c452040724400d016802c910425052075440111400303401d00a0030810f2080318419400d005000600f20070041c1544079901d0200c40704010f0f61040c113055907400c5480c40000d105002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 112557571 1250 112556321 112556329
    0x60804060906060305160315020301030b1909081207080703050c1b010f151805060a03060b03030706110a0e03031207030c14070c0513050f0411190b03070306050d03090e06 75
    0x8980c00140c031742d00440c80344c15401001001e02c0c81c11a031141420022551a010390602280401c1c04014803444070480445c2c1916250003611032031010740c4c000000c480c0c0c02682c03165801c0d84003d60501c00e440c0620100b000480c3c0001040340d026010381410b1001e8a0102564102803049070000d84544003911300030000e4107000d51116440c4191001e08100c035a04450724405041e00a00c516800c0c0e41c950355441c80390b5002130080034000c50b000b500d1440000c0c1550340d0a0082c04880c0d074021703054401885441c011030128000e001c6003003d402c154582d00c0c40455401840c1c1e902030300c00705020380d0041115944041e0a000016030040d914600003400044410044400d0f031200f070900350071500042000c0d0b043c801e94141110032200100d5a59542e2030804c1c03241025200111001c1000801c840000350105c0c1b016050440b5071324005115121111214001c2c0010070390740e0304444034140d0301004004200360944901d0001e00f20464441165015030303640101200c116003e111402a1000040382164031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 112558821 1250 112557571 112557581
    0x10315080102030a020c070515190e19030209010501090303090e060a0503030c010608060109050c0a0822050f0607020f060a0903090302040c360b07260703030e030301060804060906 79
    0x14503100a558900303140d06800d0203900710b400c103030709140501c110000786881c01010301e191095010011505043c010862402902c0c2d000701408107006c00428140810b9440c4600c0032079a5000740b041d13010460842c01409040d80c0c1c140c2002d41484611941840404d80080b11030080b40c46a829800d5070340e0b28000800c144016a0344460781511000c0f907948010101034004500b074a501c0340c111101c603030783d544200e400e54100351070300c0440b14001c01103404054402d03d006580320000c040031a03411403290f10024260b2480d04419560f47d0804d40c001e6100f48402c1c0b0900d50841c22034070041180081100c041a01c0b110044c0280706015640c0e4141c03410140100c08010040d0b40040080050110701c000c05010b10b50901d1401c244102401d00c24240150241d4038807690462990308481164101129020316500c01e401c00d84089651002d0740075540007a007040103001c403143d1886038075000989009026120031528810381904240f00500510364403151950780943c004002103103250090409100a003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 112560071 1250 112558821 112558829
    0x80c0f070b040602010b0102010902060f0703021e0f070e06010f1d030303040303020909100e01060c060905010c0e01021005010806040f02060706050f01180b06040306020c1204090c0e030a0b0402010315 88
    0xc05024000100c0d200e030080504200c07400e42d0002c1c080f500340710004908030751031140c0c004d521600c18003031101c44034030310f03400b601495119004072591030708180c1d981441e110000500912661013605c2030b1840383c20601a04e0024641c05669a82074203104001801c1c04d0010150070701007000c1203614544615082c400f0240352403001e02602e58900741801c00902135401443d5050003002d280001c250411030b403202c0355048848415420605900f80801103c50341400603003038581c00e8031800d041020a4003031050410342400368464803480a0340b00d00190501004180394102c661400300104803881c0c0216041d5800703580000d00405910062000545d24010b220303001e4031244c070b08070070860240803072415281038980012039891072514000d04102520011141150803190500082000603096006403000c000c2c5e09099a254014904041105d0f41041c0d0041b5200c640310301d81c1c8a81d07540c03c8041e50320100410b4000d803080030000c1d200c020300454040c01c000d04141e600c040300426030104013803040240c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 112561321 1250 112560071 112560073
    0x1509020705030d0b0d051203060d060f020315090906040210050c1603030e1203120903040e09030703030f090809010e0604090c020c09090f0a08180a06120608030a0c080c0f 75
    0x40025052282d0b5a820140905920501d8000c1030365036441e081d510549226801b10041596003107100c0b1140b680d40001c0c0100350132401c050300e4100022511b004500c20007459a5005807203240049140100968400c4034038000c0d4800c505005100c800070a80700d42c000e4041d2843c5890440d4004115801c1c81282d01201c060300841c40414110030001c00040b00310307802a9520741d0b41e00220010004104205d103890111540108095a815411400d45941c410200070646e401c2c1550b41741d5506040c1001c46025101d41c0002039500308042d0180b16110040d0401d00007003100c40c00c5981c0d02c260300d11606270130318140705500001d6605070313a1316400c85001c0c0600210034070440d610814003a60399145109407034803c80700c03030001607190240017600c119540481c000a10760740740641c50302d03080d0b07501805100c1642c1f442d0010144071520303005107102c010b00d1969039110413030800410583c00c580c45034128004176002080200d40165000c9000081c0c41e800041003039032121040220340c5841103014100700c0c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 112562571 1250 112561321 112561327
    0x15060f0a0305091207110d08030405060907080a1101031509150503060a050402030604080c0102040b031006110703020a05130b0a08030306130b060f07141b0f04090b0604150902 77
    0x210204101511400c40ca40d10244265160482c5950316813402500e4515912000c0c04503502283d20800e50004114020b008400850b106498030a400d52080301c0c10b03030319a401b030800c0c481d0340041000360b100181030440103003002c02503da44010400303240340301c3c10b8101074844092044410340210000000c051080d41080703031085002d000b004d080014484c55200380105000110856803c1c01450f104640c02006850190340d207540e01800c40d00705001c09800c942d070a000109107074211350300031405401040d1920020a140500c020301c8050903e185440c2504101000c00060315000d02035000c0e030300c049926103149500030740c03100000c0c241200d0459101151480001d0015000300c000d41c0100c00a5a6080d285030010011074150b0703410b030b074240d5000070041000765028100301e800ba224040c400d107820540009030f0360810380307000103107008440e060401000621062410103610444444107503003e1003251780b140c55024407c0f00c0145094069526045540c86601240d444800540101d240c2151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 112563821 1250 112562571 112562587
    0x102100c1b0b0a0612020f040504080c0109030306030b070f020d12020903030301090218030303041a13060905100e0c010507020607030e03100902040507030608030a18050a08010e010f0e03070303051506 88
    0x2000b042d554486980c4c034001c0b0200320610400142000190080d00c20178030110040144002011300401c01c1d24503100501c0840b100240a010322106d55001e0f544c003060b4103045041005144401400c003005006203203200c81e65254000c14000074482250410083e0740d00c000800c90041c0c41601c01c0513903d400700100100b80401954054001000030568070640fa94805c0181035580c0f2083d42c2c00b42440004074280c043c0440d08944443e8019032103410890802e44030380da0541500c6c80c40300221415004000b003030780320842c03d11808803d80c95036402803003504240030000c1d01520135500080d000d035000080b181c00b07060203440544072403132016085400103814051010700801044000700e20aa0400020a617120300c00e005120a6805005c040c41c680041c1c1c0030190354142190300031110250346414006032940c0c6110000d00105901c6001146018410300c5885c00c580780c4013001c07100fa0b03282c036100851055000040d1006643c0c141000102c5d40c41c1c0c05003aa2007203146100042c0e000c0e41c0040d602c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 112565071 1250 112563821 112563833
    0xa030305160504031707060b040207031706040203071d210703140304050603010b090406170a051009050304030215040e04080a030c0206010e060418050102071103060c04050102100c1b 80
    0xd40300704252500065100600041100e40d0302c614840980105066203805884a20600003460030b07a104040006170351400c00041020b82c3c05c481c0e020750203e0125030300c140d4100d500070505c41c0d004408403004c40c994600004007401500e0b105070441000703400c420426145480340c0b100600042d10480f5241d12084070340d12201c1e0fa485007800f080742c002115004680341603400105a0307040c0c8200414035400d50707003414403001c055004001c0040d80240c440a000406000411100c11440c9049d0f01600c500c040700d0505900d050901410110014900400d010100f480801075409990f8100d422801900001103008040d010300d0304102103c03501c581c103000400407a6801003005500d141c8050154010010050b46c407008240310f0b0b42d061181400004e405450207501103001848094030410020b80ea0361102401c90b00150760490340c070003014a0002e00c0d4a410040d90fa03000000c1140c20740f0341410440000e440b2070b803503900e5001080d2102420140740d1b0080d021030750850300d1070b07403001204210b905250b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 112566321 1250 112565071 112565081
    0x201020309130b10020109110906040f0c1211130515040e010e041a070806120a0b2d072a050609060f162001180f03020106050108090a11120a0303 64
    0x584c0b103007110b0b8a03681c61450040c05007110030f6800601040c8150102c0f400d009003104020100c5600c255141150343c900c410611460301842d510ba91014000c0f40407070040c0013282c032484201e55a40c80d00b030080d00b040b0b420005140741503601c1900c003802440800039a600c1d0398011a0817950200000800200380c0092621a40f80701d18010103440d4103110b01c0d02099484044d090b60f42000140186000446d1030400c40917110001190340115221140d168039604011a829100841c011302664039103102001c40e150f9511861505503680c1c000c1e41000c0c50042c209101c1c80c4045480c244040780b11b90084840b01c022110416000800c3c1c603400d10b02a040749803140030807103032a030309403000c4070200d8003400440c0d0718400070540e1529002c0407002c6200303c4085000c90b424502c01e50f592203c1032200c0b0403100c482c001c1c5405100b00c18000200392645406801e40d04070360000d90400100c0d0080040d100c8001482039811508512102450006400440c03044d0440040c507601c54420605400304042d499801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 112567571 1250 112566321 112566341
    0x20403120c0b0709080d0c05070f080a0203070e061008040807020402040e07110708031209070b16030806013b030f03180f060f0c07030c03030e030d08041707020102030913 75
    0x52041183d0300c441c02600c108240e4000c00c000b0340c0c8a084050307003072405285181600c41c041c03c1240d0754255140d01e0200740460703a402c502c4050304141007010071405d0070852107000c1c0100f9210034020340b908030f02041a20fa400140d9508016607003010800b0300103944100d03039101e40c000e4025036031780b03464920725982600103441840c001010308454108030440402c120341510190006140b6003198110803d00102024200785045e002e007100c0020a046428000c1c091451905000325243c040c0e4140502441001400503050110701201c0e0814030200d544840d004184400c1c150000c104080068402c44050202454140c8504040e1407001c041c00005016084c01090fa060341102ca00b0003030244e070040404485400010038407200c0c1450320708401500d600700300d030780c21506070a07626218441032403203d41c8203501244403a11065514101400524010442810088200c0c10700d59503102d03003d10000e440c0302030bc0d140484c4140c01c42e80300f417085900442e8010701e11121141980301481c0144200c040d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 112568821 1250 112567571 112567583
    0x909150705070606050a092903100c1814120c0102030d0e0309090c0405030c040b1003020a1404120303050c0a020a120905040501090203090105130b0f04032d09090209060702040c03020403120c 84
    0x5041002344c0d291300740a081800c054043e000c00d401030007205002e0000d0804410500c1400807008285203684071805008114082e0107a90b070079240001c2c090306459030290b80d01c4070340021044d0f850f10792f000001c5404000303503043c00007042410002c4003402c502403110040e07402440301c410b00000e41141d00c080d00c01c0d80c1c801c81c25521215016010401101c1c038103020503070090042c5070700300000c81c0a640580010341503404c0c102088400381c5802c405a030320035001608900d02404480e814141d0620500345d0104c03040103000e1410905800c0139564400d1412b00914080c140c1801c01c007007900c81e440e10790040038060424800365854460040c0607410407101490a0b61030f12002801114144c0c1d510108680c000703462081e80d45482c916031000c1b0100620640a005007503a40082d04004400b03ea2000c890940c0801c000e0076400030000d00c6101c0079400304000c1401400201000ea6540045916040d4100da0000305011140810f07006801039502c090030520740f0b01c0001e02d8140d088000b0b8500b80744903107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 112570071 1250 112568821 112568861
    0x3060b0301090c03020906190801020304061d0604170f070507030203251e03080f07030e0a05061206031606020709140c09220f0b0909150705070606050a09 68
    0x10605088a80c802c00241125406007402c01c00346c10070f041d0540e0420307009030450258142850704510320070500c1c0c0c88104680e50000c00c02003400303030f144205941024807100e0b540480b80ca20802350398405002e00003801c0c0e83c80c105c580002c0040e000b001c0f22002c0c81e1440000b516000d032814030580740e03070083c030081e8002e000c0d880001c01c1d1500104424141060b06c40907a417085400c01c0003180e0141c4444001034910048580c0101c00328070b04002401d002d02c030111074980c2c0c5500c2490010200340d05400352500030303021070200340425624807003a1120032280307a20b10b0040d55110f000080c6411044c0d6510703100c980300a000031036259404a03400080d41c03da46400d01140c40305102078016084203d031403090b01078080c448416580f0b070081844012000c01400c5000c1d50f5a0301140608490101d0440c0020994039008501e40c3d06042450f15030100710440034140703052480c0007131020618002c0006080100014480c0f08100842d44082c02a00002e4400e00c00710b0385840e628401814035549c1441000984 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 112571321 1250 112570071 112570091
    0xb0301060905361c030902030102030a0603061a0108180a0206070516080f030703080406092a05011d090601091e0e090d090303050a11060f0105040b06070309050f0d06020a08010306 79
    0x41c00f045403250001100800c1d40d03140100c5031885400c0d9203049801010344800303400d405660240091409001c8505000030b149140d854101c0850344244410901d50f070f95800c181900d0781c0c01607107582c0d002c036602d00602d241c901004405030811149450080d401031010600d4020f200740094113600000c0301101c0d18043c2920392404540d0b07a070031000b03a840c13958810020302d030009206032803240d00244a001c000c10284441e07a00d030000008011190f03592005807890009590704110b9040c2c00400b0300b0300b4058130071544000c40002e5515a900c06070b000c3e08048001c28a141d01c03511049006101007194000042c581700034140b0003002d03e1180c501c5c10031000001c1030075004040b82c0f4201c0b000883d11446a0035255a03410754103070b00200300c81800e00a880c6401d18031a0750500c2514070031855480c181ea01581010200300844680616941c055174040c0b041d88002074103c0c89132020340760219215400844007100144a002d000d10b0010401800454403a81e600e4008910a040c1c921801c02072080e1015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 112572571 1250 112571321 112571401
    0xc0b0909010e09030423102309060f090a03080705060103020102120a210e0106080709050a20090303091201090c060822140f060403170c030403030b0301060905 70
    0x240c1e40100f4a41041000700111080c5d02c200c40071520f002140220540d561038001003801c8000380e200c00104020000c07803126400740400c1c4d00820502d0701817007820183c1f81008503e850084085610350000005a4284240d0701c001a490080d50300c442c0b140e075240514038000b41c03200020300c0100d0141c4105038808810514038004c3d2136400d000c550720506840d020081003443e0807030303031420040d5040d40c0d1100011b01071400c3c02000003804040d401070003d10714146944003114001006407003500d290080481641c0d00c0340c035907650791080900f000d54558081a00103030031071140e605699401050b0803660320301e00030b040d040071600034010010388511039603628050790303801d1044a83c0300e965045e01c4025001081030100c44985a402214562620002002032501d0164010369004203a40302034200b004144c0d12503001110700c004000480e410382420303000b0901c00e00010f80000d05154403013941c01a075480941c0280010026424207020a0900300c2c0d9080542d5401e1241e9041c00c031880c0c180c0030342620 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 112573821 1250 112572571 112572599
    0x606030c0d0308040c030c0b0a02070503030a05040302060a0207091506030c0309020105040603090f06140f010b090105030a18050a0b0105030c0a0509010b0c1606030506040b09041205030903070c0b090901 89
    0x4090484000705415540c11a07140d580207208a07035003485c4040120106580d20000310181070f8400301c45a6461213054042d181508035402540300e0760040103601c6003d83e124090b1811294191a080d40300c0c6d040d00801d03410710103503810100006180950b4602846003e014071400c44285480c00c01c0030000b400812000d075840ca080103404520200002c102840c071a41c40480f0050117034112039400c1c0560b03550101600c0321911015444010481840406c00d03102c00d01034010314050a680b85440c01950000c0c00c6404010083c0940ca9610005144060f40d80c01c40f018850341d012083d03a10f0b46500740740030412a5004c1c000e007401b0b8841c520a1541c00d003413290041c002e4881c01025111540c0c41c02c100d91206521007400000c2070700400c040c480403204040c68043c040c0030145c4000c6824030b040340c244000c8901d0b03a12070038450003040f001c0c8400f240c03241c0da19210580c01807600340e9481c1d0312590442d2a510450200401c840641080080d240400310060035a0a4040300d42002e03d0f45c1e40d0300901d824407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 112575071 1250 112573821 112573843
    0x605030102182b0804170303090604031809020a032405060304060b040902060d0b011202071e020301060513090b0f04120e1309030e10050c070501111005010303050c060603 75
    0x10b501c0e9440d10200d280c914030a1201a1a440215511012a0303110010445040d40c044510050206050000303800f882003040c3c084007404011740c01c1d840d054407416610071014101905000040402607031315842d9007000c4003d0301d4801402c1d5625000060020020b06116010710150a8401d41c0c0c411001d40b9205081c0071920001e107458207503102c0303484040c014148415200c1d4096502c41102c801610707600040c0602154615001505800e1540050940440b52000107501441080741200250050b004003220f0442c0c0547e4a5000c80c851001c24010403064000503800040d10044000ca10340d5508507541603446515903000a8585c0802e50042d04400d650090480499407240d502c0d00740315007130300340000c0c02c020300455128510610081c1191240e01099001401146440d0003030306215240c04003002030b40c40c009140c41441a2038075201c06650080364100890314001111849080008603000030f9a800c0c100304950796440c028219600c01ca98034004c81c0070340c0b00058410314002ca07102d0090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 112576321 1250 112575071 112575097
    0x1a04082a0a1506030f080c0d0206040209150d0501061e050f011704060b09010311120d080118060305030a09061101020306150304060e010603080d0608060c07062f040303030605030102 80
    0x401400d41e1070100d030100710700c2c10600d896941d000c00404a0a00c04070f040c3d000f805444a50303510a82c0c00c0c015414a5410100882594001800e000c01a102e032004070703034041100f0320154807100440000801c2c81e0005c1d03101a08560074142c1c0402c104644008808003603c0440705845001d0340d4a06118561a0320540e035404a90b07007603114900c0c41484041a07030300c0362051800083c1d5044c02000655240d0080e04166210043c181301c2640a060850042181640d41c074020400302c40b900300001c1484005005500341418944845102d490030b0750442c0c1d02a580c00130540c0c1d2580740100000301800640e10800c0002002d895005484039410710880b4000d000240c400c0d401c59180740115031440c0c1c00904100e030903d40d00c950701d100f410000e2003488043e61080f6410340da10b1030481c1c81c3c3e0003601d60035007084000f900803c1c11700078030300d2015003106c07240ea50003000401e8407804100c00603071940c0c0c0803051000900c1114a40c902e03a8030b1484c014010390f8820744003003052a03290b50900d030807402074050450b55 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 112577571 1250 112576321 112576333
    0x606080108060106110f0316030306140f01110a050f0f060c0406050f0f16320a060504020f0904140706050a051806130b040305060906130602071a04082a 67
    0x40e64800c005d0b185240e00e1150131181048405030303205195a003ca038003154514150000c5004065050281c64010302d1040300d4070b107480300303100300042c660482110700398140611045030f885401c0d02803005252098000051700c640c017402c43c0c0a540c4401c00340f0382e64006d5010380b000203060010000180c170305480c42c40d40d406040c208180c140c469241d100d038010000300704040c407085000041c8107218402c0700b4401d00500d4800c89541881800c54204100f503102c48034840408070095960000c1d41030310f802e0700420041520344403800444c0b0b010a06010b8550801c0b51401040300f40240301c0ca00b03002c1078503014103c40c00c1d1581c4070030443d13007400781d48103400000d0780400141200e0600401c3c40d00180354024111072511040030190500342c6103551040c80210307000319081051080a000c0140d01410100141207503140049507008000e03026a4010140b50380480c58500340008503000b2074810500c03400030b5230141030a0500e5030b0250400ca41c0081c0101c42d084000e188041030010144140040e0b40080c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 112578821 1250 112577571 112577579
    0x30111070f0c09020415020708012d060308072109030b1906090c030911030606030d050c0c090118050a2d0209040906021210140f120115060306060801080601 69
    0x4880c642072402620800c94a50012a14800d64030082005010403c01c2d1407102e0501100a42040155801001a81d16280f80078005d000c458070310a00f80003280c0310f4403102341031044120000f480b164001030080480032070340c1010044101543c003840050200749507400c1e500c41d0400c0350700c40741c24040105562641c801142102418450407140c42d80e4080707000c1142a03e40c00d000c01101c0004059400103a12096480c060100840045c64420820381c0540b44514100c004250307200910707107107082080400110030810741c400380441c4410401c010b01c0f044841d40e45e40d200306541a00f45503003116003860140804d200c6a01031098072800580c031400d0085c601c500f407442040080e03040001c920015000c07c4200c003295130711711482c5034447c41400010380700c8910300e511790381d143d2000b800c03081112400b1005101101c01c0c0207011805200807100344011140400200d040e41381e403040b661410f1340c2803020703101d6036950f80700d142c50594942d0341d02008440d584501c00c0310508000c0c400c2030b03465002440184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 112580071 1250 112578821 112578833
    0x9030e01180302060417030c010f1505040608120c030409060803090109120c06050a090503061314060106142b06081b0f10030905030a0c0b010e060f13110d021803011107 74
    0x5001130703402401d40c1d00303003070f08c070f100032803c0d02c40031146c00c1c02c596a0b0f807000248240c0944d031003502074001682d04128043c00e0907a42030b555004425810300403840070039005030401e02081250003030004010305200030340d910380000da5240c011814090105031500404500c00d4440c0100090080d007020a801186260ac28291190b40c001d100f0081080701c030300c00c0401d69403410480d807130049006070301548504015050100b80358140416100f2a9008500104005544654402c1c41500741b800c0c00d981d201101c500343d00d00300c54110060190059256040c540d0014243c0c07000040703560280a94010003070340101c2c0e42c0c10002d002e041544c01440c00d4900405c0e4204151450f40b1009581000205c401c0d03541c80c2c041c13560304010181c0000039481d103503640c200204403555a00400b4800c1c01c1c014030f401c20300009507a50810700c0751903005d506120904403200341d10f41c006130102c4a8508a02d540e9400e0b285001020f9400341c100c2c40e655544400c4212554141403140c1a0045a2403140e40e0800d2110b6681c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 112581321 1250 112580071 112580099
    0x1e060f0b010e1e24070203060601090f0312050d0e030a030b1f03020304050c0607081b0115120c0e070e010314010303081801020405180103030e0f0121060909030e011803020604 77
    0x8103402c000070800184c85a50452030748814100300201d890381350310703241c41054a40f402c010417807030401290310340c10401038501c01c40140580341c0c0130100c1d50490504480c01c075824066840b002c1040d03030074202c900c04060000b00050050380260365052044a40c2d030340034041680880c8078a4020503480d00c41d206080741c420740c059500588100107460f4144440700004256801c03407034003514101d10010f140000500942d020142d03a20802c0024808402000e05041c03460342d59220323404240f40703042c5621080103454103100c4050004171300d00e4695420028402403100d2040c0581c540402c2c0341041118110000000c00c904a80d4075540f0b00e10b040d40c41d400c1c44c1034180600034000a041d0340910000c6100d41e6600318000c89403080c3c560b0740a40b03624500780100b018659041345402019440044035481c3da02c002845800d0400e40c0004920b680d5206000008005550101805500c1d1503031100070140e1104a503521000260f0b6014a4a044121854024002480f00a520540800c8200180803d91541e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 112582571 1250 112581321 112581379
    0x81b03014122020f03060a1a030106050705010b030106080708070816141c030314180c01110a0203060405031308071503050403030605122b05161e060f0b010e 69
    0x21055a482c0e82e402d080040c1c1c0c12070040c81c0f0200c1c00120030050541894900c3d400201850f0080007032080c2d814803104458030041c0125420414009021014040c09402c9921f1504002e0000c0150340d030380b401540d80300c148071f00503108140502d00000070702800019007072100c19800340617900154607102036807130031038030041034290003180b160980344521040305844e203143c0f406524040303003a0340c0816800100d1035008041d105803910101c0444c41008000441c186810ba0130300b031400301031a000503000d00c0c110500f480258144107541c10402041001f201a10058001e0158802010f449040c69500e64042d0b000e811429003240c91131004161180e000140c0050203400e001071a00d840d200801c0300900d1161080c03d841d4001e1881c03500320b841c1c003c1d410041c01c2c2d5030480d180e210400818000d040c2c2c40790040e0b91040c9405204800d040c409200f13940306400b82c030603011840c941c0c03280c0b400001910341c1c80c3d5586002e5141690a24603940284007820101c10010300404200032504d0b02500e2089035101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 112583821 1250 112582571 112582609
    0xa050f010c170903150103030f0c060204090207140606010c0203061b0d0504050c030d0201060b0909090c03032a060403050d0c03110406050c0c040603080a081b030141 73
    0x30106000c61000040d021451201c69481903030f0f03d06030800d040c03501d44a001c1d142c2c05038089400400101c1c0e800100460031000c2890561032000141c24458041c0c055034105012840c80000c0540c02c10a08441d4003500910071130980d0516030f02d810040d1454802014040d40503000324000a18450400c4000e0756003024001489040501c4c440c1648112003040b0740440d9140d2003c1207182e11803070200040f03450480075100034880203040c041c0c004414000c103120f19000302124800700300c000c40c00b4844446850405001c036900c0701c2c541c80d081542040c407002800c02c030586440a52240380b07008a155407045400d03464591401c1c400c081084010000304402408160350f580b000503410755003000410023440b540d5910340d110f2050744411800c0441070505e06216a207001000c00003d5807038020780707160701302c1410306180650380c007103c1240c2c0c04840302035020141000030000c104084e180c055044020f4218200c1610242a00c2034140714140410f20f090348500020f8040089180c01e02c0d45042c2861004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 112585071 1250 112583821 112583837
    0xc0d030c0c0f0617060a051203090306101d0103030804080307110f0d090b160609080d0608070e07031a100c06051602010e030a0503010302010e1809010f11090a050f01 73
    0x601e0303403254a1040c1c1c00c807039052807400070204012640b095500184a030308450903003c80c01c20b00009040d4070106e02c1054041c6030303003940ca109249000d00a03a1843d080103019900d1070311b8205881204d260b040d005a00301c10304012020300e0b1040c422420a0b040c0c03940758460811584803500c6090f2150401070180080100148070326460130000d01c03a07070728021025001824000d00040380904540c0c01034100041410080c030a50781e1500000134415045500502c0002c0d4030906030400102c103200340390710703500781a08040001660001c00030303c40701100c84d81d480c8103075141c40d0341d2801c905032551200c010b00c1c1240040048421442c01d04900321520440f400c05c94080681c42da03452040e608111441c0c407049081c508100c0e1410340a004508205503842d000c0d500d000125030002d07045020600000c1c2c1000000f01c209042512108d50000c00c0055100c54082240740c184501d40c080c09185d29034000c3c0034103042c08c9440c10032292090b161280401044200d0560030041400220302c01e0300c40190400c00c0b8032f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 112586321 1250 112585071 112585073
    0xe0a0209060c0c040c0c0f02040509190c05040c0e1f020705030f0303090d020a120e06070f05030310090b030703061808071202060606040b1606060e090d110c030c0d030c 74
    0x5840189580d8603110040c050782c280490400c011590403200504c14403405054210009071050700b2500c00707072341c12140014580c07600d81e400d52614450b00c2d4402129680354464a05006d041c032008011500308403424030185042c61001c81701c02840e40038003a003003030030082c50140746541c406500103046042e20440d12010b9403000001c1c9048010300700030045c2d81000003400110102400048900070042c0018030f541100342e80d40d00c4960820a601d07c0400c42840210b980564910080358201030700404001d00302c124900b00180c8950081e10b50100d0000c0840b000900340c0c58500a110b03143c2001000350000601c0c42d103a0002800588a10754854868494907a0001d00c1c0b4002500d0010700420f02c441d035a080c0a40040e14000001e0310051081500340402c0010295050072541d10700c4a00003112000c007002e140c01c4010380200e80041c2c0f2614003200400c0020000022070001e1002142e5650b4030401c4402001ea8840f1010705286815401c800030890181c180740d40320000303184c0f10b85080003010707140d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 112587571 1250 112586321 112586329
    0xd050a08040902040e060307030305030f2e080f0f0d0c060902040908040e010e160f17010b03061905060a0c030c0b070206073b011202030a0504030306080303040803010e0a0209 77
    0x41600302c8681181d02240500001c003201204d540d000806030020007070079007552405060703070000600103d00b240300440012031a0350b140111901c954003081440214201c1d074030aa030160702c081d00400d0000e2040b041c42c00101e0300001081e80580300d207940505505034401e07804a88601c14510203480050300ea0754006c0050b15644540340201d4003c0000948450038215000518a4181c3c4880c0055255106201201444880d1600e8401880c01c01c2c45144880d0351003a04c01050b503400702030428580c0e00000429804000046104e12422600c48105034005201e041c0c6080041c0207150308600140000c0510720301482048400c13038024100511641c01c0d82d5201c1c001c80e08200c0f9140e0050b00f100c0288030000360820541449210101424984074040d03030100c000b440c15020218411226007601c4414a9010302006000c0001460081d0354910340400808042c3c502540c04400203407400c0c000040624011040c2c0303005951001f060761a40c2d2034480a60800c0c0c001074032403c0750907820840c01c11547c2d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 112588821 1250 112587571 112587577
    0xc2306041103150f01260a06050a0e0703080409020a090b0406050406020705060c0a0f14160503070b030103080f07023105100f090e030405030d0804050115050d020d050a08 75
    0x721078030540c003000d5140001e040c103109a00701d04040359294081031000d004080b240550550740e5000c1030150b0380480c0c0461000c2c00d0f2841c1d0019146001d40341011082c00119041540702d202420f4082c00f49040110540f23944c0d01c03241c80080c0490f081400140058141c036001072501daa000e16048482640741c01c0c920304945d01c25400000400c40010341000a6501400360340c0040100b10b984600f0308040c0c0c00180d45801c00d11000401e03860b04540f0740350410420754800f91140c00c0380812210800811403550100600601606200f4030914400080d5401d0000440c2d0507030b980000030070f00b400c8942807200c4e801d4014048c2260300494503200c086088100b8121406480d00c1d961003ca2801c44100c540300c110b400140c20901401c110f002d0500c8250018291181103a505540c0010016420180e1038190300031600003551500403080c40c26880c13a402003400e801240036a00070080d465819043c2c1074a42c3c07082c07040d1b94205403003500100252030120302488016000300151407207640a6aa268003e40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 112589928 1107 112588821 112588823
    0x3090b030406091b08060105151e0702090a020a032f09040e060f041a010303020a0308270715050f03040b09030403080c011a100c230604 60
    0x705642c0c3c400e0308007a8000090341e2650648640c450601841071044014520030b4000110b003d14042030150554032440c041d01d4904043d4110408400720508000c504100b414070085d005611104015072240b80e440f83c005944681807a00071301110340034410f03422030b0710001d803011801d81d045084001e0171a43c10303045503031103109000024002c1c1048030140611805410f007030211141c2c0c2103580c5400340b803081400100300f0400e80b4000000b030000348001781c0141d20080325200864018a8403907000415080506011034000d61101d6145148021449896120050400581c1000d00502031031076060302e011403030030003010103a00d2940006880034002e0200ba2002c110121410021140155030051589454800f807100050003081140301c4480c44001c0400b505503680750401100240d510fa580300c4244250b017a45800032a20018983e0800710180400c8903c0d1f130840400c0050321072 = true := by decide +kernel

theorem cover : BRFrame.Cov 112410071 112589928 := by
  have h0 := BRFrame.cov_init 112410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 112410071 ≤ n) (h2 : n < 112589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
