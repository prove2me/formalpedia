-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3224
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:01:40.188311+00:00
-- url     : https://prove2.me/submissions/e6c58b92-439e-4b11-a8e4-c7bf6c303385

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 579676258 ≤ n < 579856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 579677508 1250 579676258 579676261
    0x90f180103050d020102040602030d0c14030907140d02210316150c080c0a0c1e03170604180206370806060405180601270603180308070c1103030a030203 67
    0x40051500c078850f1a40d00541e031040105104c6250000141ca2081c00061000310750000c00e41d20458400d0320001d050010080c0100030300c041c494000c20700d481a0f40740784c2c00004141002c0404c02ca181c0b1401d14000c2e401003082c0b9455001000a205003046801c00e007811a481c1c48107040c007046003260a1202a103400700b0085407900c0d54482c2d800b5030708d4000b13224a80079040e130901c0388078a2550b01c41c5403091414032400b1000401007042090754400d00c03041350240107613003c1c15400d020384805102d1100d401007141c02e01c006880d0386010b100351640807001c0c4241c03240c0c1103080c0d1b00740301003680040552100704460b00c804503040303000f07c0000c1140310801e0500e031001c44900d0602402028010b45038a204602c14001130025445500c0030691f101c2132500070b032800341c465900503100480380d6024180c013020781c01300030a540885203140d08205c07140c50342d040024102c0c8003a42d162400401400800050a80c030106211030b1140342d14803a500d0086500d2401d02445400007807465002504140c0869000300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 579678758 1250 579677508 579677513
    0xa0204050609041109090f011505040c020a0c051309020604171614060f19030209030c030102030606030f1e09060a0b060304053007111c0506060402090f180103 70
    0x800740c000034207903880e4003241440e948000c0c00c014410181c41c003c160038400640d1544d410006280c495046400810000b11000d28a1024140c6e50141c1c0d80242d0900c19040b8240744002601224030f40c00090061046040500300801d4038401c12a03c100944c48040c2c510150f510100104001c0c41c000981d0000c80d140c0d101d005081c0500d61a19a07205007400710100040d0300d10180300202a001155140e035540c1c0101110500d901030074500c7c1c040e00c3c460000d0007090b05c2d0168000c0507a85800c500302c0e05002110300816090b8842140d80d5600032400f4400b0440c1407884002050304014080e9034600c02603c0001450205002224000e4031b66010700240311210304140310f4209402405d03216580f840c070f419107a00e41c0e500307000d418049130881006021641e404550f150842400804400385543e0041810140c51554035810715030320455442d459020705800d01400f1204903035108000c3c1c1019070b43d0404210094110170035081e04441c03c1640c54850b40c1d00c160210b402c0207006c605440c101d50660 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 579680008 1250 579678758 579678761
    0x17120c1212061801030302100c12181401060b041403071d0a0501150e120c1801031a0717130206162112150306050705030106020d020c010503011203031407020a0204 72
    0x241040c0f62070354007000500200e070340800c040c0d0401a00c1d50010030007450043c0d04490303540e80000500381e4189007103d5040b100708806000c00a15014807a07203009035491124140c2261030310f2003040b1030038204110400c07040400024203c02090020b05441e66150713159440440d40800d82440107000d42ca1200b0010003410074428035000d01000c03003200640d422191009400200444583c4e032046580c000008181c402c100300c00c0780e402c0d00180c103865107841064100c00a941c030030301048508540c90840a0500311414080794030510341036440040f2414880180e507403500700904100b4a007a0005181000b688440004001d03815580d0992104261941444400c4510300030506825520702a19400d10315400381140000d45580b12001031260081d40c0902c0462409034001800242810204503401e90004060b5040b500d0176001c0e9506101c0c1a0000c03038407120461012400300d0710070b10043c0540010074056036815842400c00085505000182000030301c01200d041006910070b0501c03a003141800d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 579681258 1250 579680008 579680029
    0x1b0801022b06060e0d0203010605040c02100506030604020d0f030e03010507110f06010e010902130e0c1e03010b04090b0d0c0806070f0305130605070516120917120c121206 75
    0x4607030003002500e0074064010011542c55072091303c00c009003460003040d0740c0c2c2940000001c040040003000b0500440b28081d4962000000c035501c0545003d001510f5800d010a29a01c41c1e5030080910f4580d071029520341d0b11080c01d0f4401036040043d045405441a2424440c5900400d0503440e10319040c46503103001450031070095101c041c02e0f0099801080000342c1d00c0c16840c15941401000342e29219680c071002051030a9510891680d03030644140501103400700002c120700d1170403106d620280a00c100c1c43d0100d80c4801c0c450000c00b00710410080207135440d550711400c83c5c1c1c41700400d0b0700100d0703415460300d0180c4400e9410075502a0001401d01c005643c0050b10010140381600341031186203070a240e805004006c10b000076004030313141c10010315500c3c8200c049583d1160499400c01c43e008680c24803400700c044a455140104060520100b4845880314220225566070700003042410200200c2d4050764010404288291043c138015441804012000d810720a4a50100b00030b540340030001c004001d81e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 579682508 1250 579681258 579681337
    0x405120f0a081314090103170c01140603070506030103031b0609080a080f010f1a160b0a0203070e040e1b060d020403060b100f0221070b04080901080901060501020a1b080102 76
    0x840e05801c0741e0303515412529411250403012322011500e071001d401010744034001808400d9440c01c0000c18460710040d8a0310f00480c0c0c26004c441c402504d50040c84041e21007800058003095a800c154048901c11540f080d003014850b07580403620039096a00c5080503000b001c000808280c480007008110410030095900401d40003410b220040e26220a003200141c292081180c1135070005111121118115444190590300444440f0149803554140d402500706a4100000a44032290034003a0326142c0907240725420000d0180403d0700541c103450f80c0e10700180803031a82210303042c420b104000c0c01302e1001c0d100943c00b404012a2158114041083c2446040c038040103002d0040b40b22003030b00d540040c02c511681c81c11380b034002000806040c003100343d0007200300040c480480d0310704110400050201500d41d0b84020380340c03401a52620200c80e401d070b84150080320b006034000c022883c042000745c2d040054060382d8001051400fa16400f405080e41c0c05482000000210b054803036101c41c0780400d00049810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 579683758 1250 579682508 579682529
    0xa0b09130b0406020c16090e2a0f040524060a080121020402130603050612100903050909090d140307082d0a0f1d030405120f0a0813 58
    0x90004940c03201200e24840160403100204002410014158116140341c2150811501661510512454205141e0048262140c2807410020304000001600300503181c508280c2c0340710400840708004024a00a40c2c03941c0000240d60200b0607072590310840c2d014441395100b814003000011880101c650003800183d004d814204076201000b42e05c480351906441003c907206c0054170003a80060201d8400c1d08010354040c2c030004602c01d06d0400802d03c082190016141400302c8e543c0c19080200300c550303499044000380c00011100318100d90310b505c00104a44071341481801c00380301c2c201140c0044030441e003030001d540c00041a44829508450655003c2410344da02900d54035084400811103c2c002c0c0c6103030380880103c003040f140e00c120445207146001c0401d600304144d141c5412070f50042d0026130741510a0f1403070303d24140b40000e001d03d043c250f000c8503c80110b280c50314000c24084580d882c0031179082d079405414003040b003644040c08500c80443c0241001600c3c1c00ca542507a06107070300b10703910010545 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 579685008 1250 579683758 579683761
    0x40b0603070501021506090414030d06031707150e1e07080705060336030304030f03150f030b270a1502030f070e01110f0601170d2a06020a05030a0b09 66
    0x8107031485101b54040000e85000c410760b241c515042c801100c039410b0b0001c043c040451400019030040e406042124020b0340c0c041450821a28409071511175110007500d1007038001c0058100328059000100c010048000702e5a08829886809203400031445180d042500041020005403500308240800b070b11084540510314208a19100c1c4030700c424100c3c6c440903030201c594582c0e184802e0242004c0640419090325035a107440e01d0021b00080b00d5081240c0842d20b0005580c1e401d108504840d0281c405031400f0100140c00c5466401d1110300040c99070240f050643c11015010480f4a00c0b212841c400e8401490981060310b000300b6540402d030001810544140200040003d2001c115a003040c43d90802c40c203160702100040316914440347d007146080c070074415030754020100010914121002c22841087c8240d15840250b00c828129035590f000500618002d554413001c0c80800c0050701d0015401c20f55030a10b6034500c8182e070442c50000c00860008010400d4034000c502980005440880e21190903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 579686258 1250 579685008 579685033
    0xa08060f2e08240f07090e07050c15071205060604051018050d020603040807030e0934080f07030615050a0810080303010b070221160603060e0a1a0405040b060307050102 74
    0x101600610340040901008082502103011b041c001010380300e488016042c1c1d15281101401a034003000c082c130010f00c512103407034054441c8483c01c80d014190359074540000d20700d400d03040c1d005484003902c080d030301c000704000020381540ea592014120b8000c9440f0048080400f0140d09100c0d0450780c0700310302030000c50340c003580141d607414100ea03031040d80010f0141e00d903c001e044c1103d031409051071041d0010a02c40600150140f8030a40c01d4040c0287c02d1080e035081d41c201d0101076480301021200010031020760101d94000305189d52154405445c1c900060040e50310a0b446200c0f062036251400450400114180075a03404075800794803900c10b060702c9400b0341c40c08043c035949100510452400300e9010805501319510141eaa0303240c0309002064030f0201e00c000b206d01c0c5e00c1d0382c0d880818420501c5030741e100082c101d01900802d800c651200d000b40b40255250b120540c094019a10200c80100c00181481c0861340d4910400b8000c60107006210131510b81102403501e00b8009800c6a03065500602210a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 579687508 1250 579686258 579686323
    0x10803031302150d060e131505090114040c26030d05090f010504080d1b14180303030a050702010b03070f0315110a0822050703110d0b090a0506060a08060f2e08 70
    0x5031398008d11000500703540c50400e940e0050010380100608201a001800144503a80a841d0151070401c4a04480038002080100c02c281001282081d150403e00c500f0340d139100d4592109501c181d19500355000d1040c281c0100342101c070101c9040345c124402180c035619206840c4207440084200c10101084868141800f81c060154200d040411a40004c1d803c07002070180013440c191003d0150440723441e811300e10110b0018103030440f0f11000540c82c001b100032480c42c0010b4541c00b11441c000e01911880d0542d240e24004204203441810700913260b84403019203001e064000d081040580e0b4031072065040403007180901c1e00046803e080c00c840f00c4090300c404a00c010900c64222030307200403080d030080d8511010540d0640c240c80d010f01003c0300340042101140022a0b26041c1a2140081d031304a503840b20104440a405130207000040c1d44050009402c441400c50130b541c000b24400e900d41c50110f40e02000c080c41140108000c074141d9446003080011040400c114205940011356140103c401e0885400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 579688758 1250 579687508 579687533
    0xc0f0105030a0f110c0a11042c12030a05040c05040e0309040e0109050303190e0106180504030e100203070204141b070c03060501060905090f010803031302150d060e13 73
    0x110b2595944903103000101180d2006100c0001503c0d03040c0c4405180313030100c3e210a0f8580c01501c0751240e50345281c01900c0c0520420310040208041202c0e0b8080c204540c01400c805210088054414801c2c0d40130380c3c1c0e05810240d84141152070001c1403d01d0716140080e01c040c1d643c2d2100d401a0b081c560ba580103001301005070340d0042c00607600015200302205217140034048010003e011800300000384080d0401c0d400c111220215001014401e410f156510103080b90340c244103040c80c8071110340c1a070382101070036001103030003501a141c2400840b043d14001101100010818000b5900000d8070404500b02030148039180881c0e007610808a2130501100c506a4450050b00419603000051410820801540300720255801240407c100c0d0f03110700780642102c42c6401164415048400014424062541c4003030584602c030001c0c5041d5100c0001d114540070042d030040343d000752041d20600c5a01800000f900403840002c802040350ba14003003112041034009803110130105100b88440011a0350800d040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 579690008 1250 579688758 579688771
    0x12105071208040b0f03071b0c030326070201020306130504050c19031202070302130e0d05130506030a0f05131220010f0f0515090a020a050712050703020c0f010503 72
    0x7442215071074100381e81d00c22900042c03c01315010a1184021201401844c803414503900c842c194415814441e101e46543d124004103200072000062000920a00c1d9041e10b105144417800194414841d42e8044a81c08841c8900140c2d404010000d140c03511400c1040300142e003180c208031604050710b440e030720340040d00909030040944201104004c0c41039050b5800640d04448213000b4040f5001009485000901c0164031a40852020020b070701114490310507003500500c02081c041801140a07152078200350010b109000380e40c100000d0a4403010021446000b0407800050a540a21404421142c0252548503040500010400024207588401004002c2d0b424a42d8110343c9202500c1044180001c20742c0d0154240624481c01607520382001d1410401c5c0d031070a0003d603580c8042e90702401c0702c40c09216444419500070170313403c80d500e43c01002c11000519120786411000d071114000310349060a0400010030029402042c9035044c0702c4d001044208640410482c0b101c100003c1c01d500028059 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 579691258 1250 579690008 579690029
    0x203100c021b13200408011401050603071b110310020301050a0f15112109100e130209150304030c0b090102030c19020705030d030c020c061918050a090501210507 71
    0xc0ca000000344442c00130381081c10100303a5a55889001c2075020308022442c0d601c0c3d5900d50000440c0310f01e00002030701d2203010b2a540d1202402070306000ea54080940c550b056031200080d807104052504e090105002c2062096001b60f80d9500d450180b004040d100e9009010080c04c0e580140011110014004455070481c90200305a1001891040c1810340020414041d4000c54140c20210700d00c42e40070340a21039089a0344443c0540e42501624803101400c00c155100840100a808103032440d4003400c5000700c00740100f04a60300c105510b0b55244c1c01602e058022500050001e0b080040c0b2113001648412414025425400c1c620f0103040c0900408101c0302c081c2004000981886108100d264010f104c02000c90b11034036041c2e24080d0041c2201e00d078160050244990007241c604050088403203c0300050524109400c43d80401c60309040e0a1041c43e409602c11000002d403540da07418050b001d0030518a00144c2540b40c969501c0d4980c8540750904200000420114081140402c0e80c00844035003086 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 579692508 1250 579691258 579691271
    0x70206030402090c0d050103030e120106030203062706090616050c06060d050307051209010e2b05150c13080105070c020f010509120303040c0509010b0d0c0c0203100c021b13 76
    0x20400f60f00441060396170041c03130305000000340f41c1c0c80b085111401206880c600ca15030583e0307501c0c50036141c0310f0002035007503032201001c50b103484a1224040324540022012031860360f2500d000383e040a200741d900c02c1203680070000b4040e6144d60f42255600d000140e0914a00d005020620703540c4032200185481e2040b00e03141612030a000e018070848103001d5011017a920080882c04600c220b80c1c02c484101800036510410050b00350808031003004400c0c0308802007006051580200c00400d0504034402c94203402405e242424103441301c4542409440e003178200b192911484010201c11402a500090032603041c0418032410940102d0b90454040c4c0503510702d1b841d590441d0050781e1078401d4441076078100d01c3d0041003006414021010314017443c400c1502445080d40c8600b0810401020300130410211410841d8640d80030340d540c0034150303407000c41c00c00c81c0f08403009400181c203080840710380d10510740c2c45410000c01740358184255200084820b0441e04000ca444021402003807106403501101c0b951004c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 579693758 1250 579692508 579692521
    0x507090c170f0403140a09121b0806040506100e0a0e030f070b01050906010e01080a0b031504080705011419050a0b0a0f0f1418060d0b180601080307020603040209 71
    0xc075001062401481c41e2a040d00b00707111407580d110011079050b130009180008201c44000b00c0421a4010140f80e51410041418040c080900c9020800b0844904240c00e41e881050040075901c80c004000700005480720386032605141b400c0c0407000701804a111180750080c45035102c5154070720340090020100150761218509224558843e61484445d41500030555204218810a84505880d0250340c10181070b103610005544107026110aa17010460b0303000040c030307400e056074800003066900800325803000b05100da00816000b001d881c255142880041c100c0300384202405500303404c20002c506070006180444058100e103400c3d405184281c0e49a9010400c0d85a09420a1000c1f0000400c8040c1003079491013010781e090820b02c141202c0c03052025000822034401442c07100d03007031005800f51409a0f02100e0900c0d40d13203002400030b98403582194200c0d011a00e038440d80743c8550400c0035042401400c8000d01e921b8518140e002c044242d0040000c00016243c0100340c85e0865419101c1140907269007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 579695008 1250 579693758 579693767
    0x303080615040b070201090b0901080c031302130b030d080c0d0e0708070b0a09120c0b09040f0e010507020c03031309110c01020a0804030305060409170906070f0b060f0d0507090c 78
    0x10310000c0d0001e400718022400c058504001c10300385200762204000150b8a1703a00d68005c1c015800c840780032035100740c0041c480c4594000255406110200385d040c0d0740205a0014000031604030322814150365892506010f41030400005d0a049007505002038240f409602065140c4a0302117030300001d507218110000c016504006031009070100e2010344405c2a100d489800c1260420f46d14400010390624000860342c40410300d001c08950081c034400c00543c1403030b090301d440b03500c107a0410f03403c103640e0460a00d075103d0620801b0003407143c2c0f20010825040a8034024908410030032114402d0f04104200c82c29019866518011144540d0002c1a640c1c0704108005072802070482182065000241c0b8210090788441c449108a00c00d890810041d260907050000b180c1100100031305500028100b1203140b917007c0003900c040380009040625080c031580e1014607800084e4000c4a00001040a121143c501080e28140710314003664029074050b080d4441c9a502c4419100c0d803001c00da580d0500c01c2005106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 579696258 1250 579695008 579695029
    0x9140306070516020a1203140c0a0618020603070306090c2105041e05030a0215070509090a1d150a02030c07030e0d0206042301090f26010c02060a0509030301050a03030806 75
    0x2030544500300c0da10418440c280d001b95804a00040b15900142050503000742038400706c8100e200100209070071350303031200002c200c0c07401c120758400c140640c20401030391050700861003103455075400b09505250205141c190b415603420302080c054082c41d1a1a580f020041c044a5100c1043d4007190f50740311030400b4810000060104040e43e031a01591401b800000002000c0004040d03080b164480000400b19010810503103040c000100c04016404051a1880040c0d400c80380e4000000b440203c854410008003030191030343e4030150010000703901c0c650020844240d000d07120300d009500d980341c881d502084c03520401c03800601740941041c2c3c800f49034540c100c031006460f034081d14056440b521000e1134101104040c0326440811180c40c48031105510400340039003103945c403d2804095901b00300710540592000c90ba41c003d56581c8003002e108401090280e02e211b001c03640c01034003890403c0c22220342513510041018005520400040041d40c40c1d8507080c1046035010300c1c1441140d100e010010b00c95202 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 579697508 1250 579696258 579696263
    0x60628080d052206080103030503041a090109020f27100312050304061b0f030f290310050105030307080304020f030d030605030c010816030509030d05040309050109140306070516 78
    0x24000059891034000006080d040e00f4070494240280700090601a21800f901510340018594001003000074001c4001d16000351040000180000c89034810560050040347ca8103010fa45440a1500303500704030140c3c0f00b11510550b00e01064030004d00b800c1121482100c0700d00c1042000000180b040d55903078403e80040c540c0694004088112140001e09a810581e803c2d101203141a610a4030141208160b58140140d0f44540403c103400c2102070303000303003c40c1440503161380e16036044604020340b40282c039541c003840040102e604c0c50712720103141c07408500d100314141052904006102039074002082d0386090350b00c022501c3d62075440d4404548006010102c258140c4034401e8106502c981681010b410340c3ca095040342c04d42c6559800445400006488908800a40544010901e4460340081c0c0d4040882c0080301e2a1501d030804101c120740046030160000741c4892003d01641da4488003000080c44503810404213001d00c900020344070080542a038062050000d80300d50b004a0802e00125801e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 579698758 1250 579697508 579697513
    0x714011224260a03110f01180c050d051c02011d070602060f09100507030605060d0609050603030901120c0e10091809031b0c080f010209150327010f020d0b0109050306062808 76
    0x442e8903500234044421001224114070390324004c90300b4149000040c01054025005103001411101901414400d10031600219500c0d03043c10001c146e14900c14107000c50203803005220403460458000e0803c03001400151420284400340309400d28005080300403081e400d0170010305030711040320a500600195104a801100119080d10045940c1e0710910460394004014051030341d90b1010140c07244034070403e850100d1902014020881800d41c4600c0103d5601d04200b25580070b0a0002204102c44101010001d948808140158007100c0001e9042e4017450a040c48260810780c2c5c042c00b14000c41842c202c0e2000000c0c81141807042038141c042c0180004801d842c0c80b180003202d25400313540320b5030819014030780100c500f02d01e020b0504120386c414034040c2c41c00c40340b1582a0804001d4948031540482c10b039900c4050000034085075100400c005640714200182e03c483c2c0c640003404081c45035006a2083d0000f070b080185948541d403580a41d4540b40b000d4012404103180e40c2420305030305400047c00352 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 579700008 1250 579698758 579698771
    0x304090c1e0f08070305130b09120708070c08072d15020106050a0e09032a0105010f0e0a0e190303020d020409020a110714011224260a03110f01 63
    0x180d001820b900e1259190359942e0101d03920241c098042d244240d407054041d59502d01081e000c1210f901401c2d070170841c400b050b101d00c080103e542030210340019000742c4420130002803400c104400030f10010001c048000207440c00a14007607a007064080204400100440048040f41e040c02401e8031850240045905000600e00b00c4c86000f402000c050064501500e0201004210701814203286031003a00c0e144000e520f040c0341081c0c0c040c405c21543c03c6d01e403c044034540c80070040c0c2d142030140c1e60203000e0160b25110381c4d5140100e61072041a004c1c109000c5c035403504044040c00003000c80c1ca50310300329a403d25207126003010305c2c0850092040515140300070788082030200d102c001c10f0300100310a03001e0303035154641d000104605079260f083d0b80c401c07600d89640c6001e4400c3c0650040c403404405e00e400134800034101d1225201c140c10b046074014100399841c807000003400590700034a0b4004d0540202004003151040068400d81e9034000008094180212035444048020042010300300140c0183c0080c07014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 579701258 1250 579700008 579700067
    0x307110a081b0c1c0f06110307030506192d08060108160b070609151503060e07081b12070e0114090f0a1a0607200406080304090c 57
    0x40e4000e40b80403a08582c1c1e903054091085400914501d030f00000034050704a85601940640101d103c3c0c0c541280c16000030320060022440d03134400c840241d050318802690783c2c40c003902c0c01800ca030001031546204964a41c2d40545802c5032407100400d64000174143c03807a0074041190101c0c403192803840040f28607202080442c0d1003001150650407110218122800c05800c800d000710341e440385019116a100091180c28003007049030308001d00711070144071a0514880e5120385402601d102e0002030310038a21440b8100700300411842000880d1030050040d100003405c1185080d114400c0c103075083c1020790f0b034004050b110340d210801070484d00801c6044540860b50341403491020314092046641240000c2c030740c0c0c092428808443d40c811110400c0c1c048140d036030003034040000d203044404c050b00d060501522184035280c40c00100003d82c080c520b0308607030480c0002c0c0c003042500b4443c00316004d14140041001421340c00000d40c0c040d112140c400ac5200c41110400700d51401c6010080144035603405400e07410b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 579702508 1250 579701258 579701273
    0x20d23030c0607050f0d0c0e13330303050702040e010501031b06050319151e05040f09022101020909102d050d02190905090d09031203020307110a 64
    0x5140a101c16645240d40c0d810301a00c1078007644900940c0a28104030043c40c4c8180c2e6800309000c10303128144020540c9180c4041401e00f1111419030444a80c0c480040c07110900b40c0c07640c80c100c00c42520341d0064a82c81da403402c081842061000405100010410000f156159000f030541103001000030080c0e903035031303040003081c2014542011f807095081c4203010802038801c4044038410303005401c0024243d000400e80000803ea000d20243c0618003580e0f0100b060b00401c180300b940f00f45030341030304c9034014182000c2108880301d01198580040c0351244102c01030b140c00149500f03a844c60081e0014004071340307100c0c41c0a4810010015030110030b01c0f0401c22184440385078903007507030440071003a45489030f40a8000e0f6207016403d00c0800e440e11520042101c1d1402142c82480c15101078804d00f0748049040c0e5004542c3c100380c1000c00c0305500c9404100040d43c04014113240296a86441d41d08a495500c5445101820440b0b100400d5000000074403100c2c0220401601c060804085521814040c1000742 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 579703758 1250 579702508 579702517
    0x50313060507030e09040f02040c0201020c0f34080109032003070201021b040f02030a0906150e01050103050c041d060f10020c0907170405031305010503070804020d2303 74
    0x180624544100400c106100e5001d80300307055415100c40030516141d908002400100402c00c0341d0300640c0751194801a20f81c3c1c06004c2d000241d0790009a1203212022000703040440507045c0e091130364054240d098400801700441c0c0301040d20000c0394000c14201d600404181c1105402c880c07110741c02c224030f5801300756125030b400d01059481d4210340100340004000036207920400f1b03070281c016480b0b03213240102c448034144013107602034008100140c48014070780304000b6a0022208004041d94a0100b80c1c1806114043c9054503104190401c40c90b134146800b4890f40c000c1801803d041690300c00002d40488801001c503405040c3c080121040d14507034840c070340703000c0c101291803030300420743c0d13898441050800d520706081d900a030f40c000c1e2248894a909114250000829560421113002d94138000b40a16100a40c0114002d4000c2d40e514544400c0d40c10707035403c260340700b80c0c10403404204100010358080c0c1c01540059040724070074050f10b1142816940d5100b10940d06403000d0449047d0003041d60000300030f1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 579705008 1250 579703758 579703777
    0x30a210b100c1b0302181504090b2d0f150604080c1f0e1216030312140112140c06040f05030705040b090412141207021c1e050f070503 59
    0x15441c0b0f620301081c82c2e1100140e1100a400c159480d221422100701c51151592100c1291035030f440c0ca03001c04002a040c0c1c0c006581c10b88003180c202090000d120400d0440a019070301c0388a603804941151807a5000b0010010000300c0d42020700310101e540096064111005040020132154903503445410003030701c501c2220f0310b5030320400605210550500440404d010034109544036200385c1c241c42c0050200c843c0800c40290841d02a602908001c0d40244401d10051b40c0282d507001d4104000030f101004685108121200c07481c100c0c03004204039480032440704020381d804a054164919942041480e02006c03a141c40c0c5d100c8800b24000c120340100520f40790031500120125019103946000b031204940a140031241c11030307613400004000c25100e8024400c41002460619038081051000a4442c0c04c10700c1040881c100800600018540c1040f410820040ca1500804d20b98429400680540990002c2d404840305070315450308a60b003c0ca0030348181c1c4036054281a6107200a18100c0d899905c883c621 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 579706258 1250 579705008 579705023
    0x6090415020706052e050d060207020910031506030c060c0206070506070216090203010311061e0313030e01020c0102060109050a15120506011203091404090602120702010c02030a210b100c 82
    0xc80001119007405c4420821000040c034170301d6410001848400203400030280c41441c1c0811104005856800240e44603409040110181c0740c298601a20111521410003804a041240c144003080c0d13400c0041085410a017043d02031031010744041a0702d0b014243c400382030f601540e01000501a008140c11664451502c190010151141c00d070704100e010a010180c00c0407220038202405040c000014481c58041204c0341003600741195240107a42d0084501600c0d400710400f1040815400048601e00c0d91001d0000e40408502c100c0000e585030814480c00e411540c0b070310f0104818501940c0618043e20700c6002c010407068880e80841e00310614a10211340e1480303114000a000380c842201141400e905a0352112824031700340503007401c4d46001c0000742e4020350b80c80494000540e103100500300c8074450100501c8070300c1c08450290841e5400c25441c5c0a54108200f807000c016400141580e05918540c1200c03042c001c0c1e08a900001d094080502e500301d2500384034090a160440b0140346120300c82c850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 579707508 1250 579706258 579706291
    0x5010e0702010e120c03040302130902090c03130308070504080a082208031b011b030f0606111002070c050603040b0103061121072d03060801140609041502070605 71
    0x1203080b034422140d11003082c1c0100413201d205180f03800040013000000c400306c03400c060316a0006500d07811909041103080e950b03500240c1c00c600785103a91075844401241440c0c118a082c801e0701c2040e80c0ca0740f03402001c00c2130702000074002d0f238003401c1030703401810382c480845942c507640f4a0101d2140e071003d008401001c0c40120610300005820480b031060b0b86030700000d107040611300320ad210300860b03400d01d03d0f031415502d68090121002d96116040480c4440359004074150890318080d0003107600580200b010000884000907030300000207544980c0390408640183c0d00c00c55801c0c00400e18041e6000075a1000000080c401171000740d0b5030300d6068a00400c0100700e0158072485807201c82c854121110800c62188680044d850501040d040e0b000c600d50400c02541c000d140d400a840f00701c264003400b09003d54007000e031401c65140c41100c3c0903003000002041240c04102c1101d9401c0703402810184500034240000b403c000032081000440668150150349402ca549400005000b0413501084481c0e000344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 579708758 1250 579707508 579707521
    0x2d040617040201020a08070c080610091a03060123030613020117040309091a0a030c080c03062a0c120403060b0102061b030a180606080d140405061c0c0305010e 70
    0x1140390149078140c00501c0c510030076070740b55600c90b0010300f4213072400303180040c0c00100d030301c401d000b100d109581d14600c1c022030320700f48070045d400c690415200c0207110346500342c028542d440006500303042d510482d884030b0391210b084a40d002e19110070709403560180a20420301450b02481102d40711203d1003603c0d0017040f0408901c51000c0800c0869000e00004d440b1a410007588286611210011007400d429842241c020001700b80b401c0c2c9180e000b2115100c00881c2000809804c4c001d444120104401400075400c1080c14030403130700806107101c44c45102e40381c01c100d0302a038808201d4400c8144282980d242d001004d10f1007200b50064442520130342e04181c10b4006543c808a01c4a03c102d400c42d02018036410506110586604014295100103a44955400c8080760b82c044031a105446104042400c5042101d8030342865403441109062200113101c120b400842c030026601610707000c0e100e19803a10380c500b050503603180c07034600a03207a20380c5040c3c840000325901d508994140c52000c01404034a4491a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 579710008 1250 579708758 579708797
    0x30f010e0906271501060305010902161202010e1906051608040f02040608031b070b0c15041a15040615050d1d060711100207020f062d0406 61
    0x4444114081d040180051401c0811681c949032414030590f00442090b04207400c186040703015000046403103500304c0104012075142c05014058481d0820035420414804080440750b07031448801030000e05006031418070039200750b00034400080903100b02c4585c1500c0490300b04401103142c4051f560a400c20000481010040050790490b546940d284101580c4645803003542d40e0701e00004992081e01c4080006034490104058070004803400c039100c00c42c030b0404268601d0401030b0307840742c9404501802402d404420201c0c1403044000c0000f03800020341d03030380e28011181e101040100c004d95041003046c0b0126010400c0c2010102c0030503103080101e01c0c3c4402188004003c0b8400e58400a4010854103203480060f402a040b5004100c807411114144445458241001140d00740d00144a4002c450f058546c2005900a01e8124500452501140d90085056890314101c4680240d0001408122654100c0ca0030040104001907034058144901c501d08444c4d4494400e070030010302901030704440380590 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 579711258 1250 579710008 579710011
    0x80f0f040e011a0a0801030b1801052d010305120c030d060f14091504020904140c090312040503030a0f180605030615090a030f081b060117010507090b0d110f030f010e 73
    0x202c0d00e074034401340c1c40c0d51388070108982c0041c001c9e25651010a0300e480c84000c2409242d006080c010700251031b101d801a940d040c41d401d00c11102c484c07000d4501c01040482d002203074501e20711a50f055241d40d544034602000707284d4442d268500d5000d0b40b40200c0005c42840303481109040c1d81c034080400381390400d002c0c100850502c0503236402070300004610b415001e925284d4014400000040d00204590b1213000c060644064102c50b80700d960440081c04e94607a1405011001044540d100901d09003414034010aa031380c0518040001070000303945d010f0035600d005e44441555116841c498027115505c401c0d00030190b0f001560103a000329204a01d00c902410070805423200a000039010886051440d241c110070b0b003d000f00c040d01d46000400c08100280c6801507005000c0483c3c43c0100030f254580981c1441c140101c4030080026494503041c40700141d070100084d13048690103000941c84600e41181c41c0020f002e611540c0c443c03800c00062030501d035a0040080d502c82c400c002c06501850fa070fa403140820b40d880 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 579712508 1250 579711258 579711277
    0x111002030901201204090218030304081207140a03030e0607110c0d110901140a14010c030e0f04020726130605070312060801050f0702010c0c080f0f040e011a 69
    0x700c02003103c0e0303441c440c10351400c0c400c1c4140d048814103441016032081035841600008009500007a262011481d900c6555000c1102580250303e0580b6001846441c0c512254140103842c000003561414880700396212040ca175458015102d42e40c2d4a071801030020070074290001c10034001c0d0700018081c140150527000d0103908450281c900800108100410704d440c1c010200c480501e50b100d02c0c0c4141d100e08102c94007070100440c0ca1219420041d0821000008950280000c03074079144094101d41d03440f80142c01c2c4a58141400800d0107403080c00601801280084150040d06c0403840001340070000390180421001002449d808680000e6400ba40c0c0c40303824840f46802d1307103085040105910440003084902d003c1d19040c00300020554000301620855400342c42a69155410301c11082040c510580d045030040c0000c00c040d003204103010f40002c2c5050f901071306107000411b103100e1801c06c44c401c0f14200480090042d5580c1e4aa02662182c4042800f6100390300705000e8050b10710705462000c40c1c44100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 579713758 1250 579712508 579712517
    0xe15430e1f111e0d02010e0102280c0b0a060f0b070201021e0a1e03030b010c0b0a0b0f10030c090603060e0609040203030702130c140906070602070519111002030901 72
    0x58088825298881c1c1001909440d03c50110303200d25000603940091902c110550141a0103003241c0002804d4400960400c0804d900c10007000000c01e080c0851007100e030ba8090040c1000380c40b054000d80b07419280361401362040d8011801c1081c80e140c0c3e40c0c09001510340e40144504140c0e21144508800d00400c20028050380c4550084031005407484405c0000c40540408c44003a11001d9541811018140049500d90729148420030101a014010052003442c00c1c60104034100e4140c940d00400c0368050b00e5118516aa234440036401d0b21601180c001c02178002d814100b203030104810050081c1090442031001a000c0480411618400e0141d40202c5417412035980458856504100210b40d0280040f40c6c103200c01c000400060b2a42003030720f841d02a4417078000030a0840d8400280c0b40c0d05a09401050020b410080190a42c2d2185e09842c3c449801c654010703180e484500c2e0203460806001c19000080b0a00512407007002070441800300c20304000c0d101c52607043c001a50981e628002c4180306070114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 579715008 1250 579713758 579713809
    0x10c050702062d07030207090b120703120909050c2802070905130b0f010e0615030c0904060302030f0c041802010206130606270e15430e 60
    0x56505240b000c0e0040280c3d000c03110900384044000c1c0242e40a030404401603000700c07404005075020740c460340310407100c2581c1002c904c80544000540f504003902004100855243c40c0c1c0b440c1e42d110f00480c0010f0315403100c04004a00741103448200d07a400060707a0200e08070140c00100a42007a00340d40a110201d10740040890b03c0c10300d10140b002c4c00f4014481c20b00d1100202e464404240d04410150140e007401c2c040c14400c0d414440d80e6800c0c500e00622460144000c0e8902500012020040300d03845100c00c2820f584482c0c2600004010304610340c4007079411b11580d080c1c501c818101141d654100c2c0d400311400c2145000c0585103201d035020b1100040c1c056000f440000712030f0304121143c1002113102d90300c0021a42e4665580031265141d880c8201c4448c0348100c030312640a0028810041c4a2102d40c0050030440c10342701e00f2117482140146120201400c2d04c1002c2c3ca889085c8089861070141423030031040c0040c560028013094103010003884005031112881d1441418602080c40010703070000c2401402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 579716258 1250 579715008 579715027
    0x3020102093316080d0b1f0f11070b0d020405040204060f03141312030b1207030b0603060103170a030f020d140f041101030c0228050f060106050301090e0f0d0809010c05070206 77
    0xe600b080c0c5a0717840c40c0e500c0351149031140c0d4588500c5860300d0000034540c004c1450200700148450040c9a500042c003400300004e0001400000b050412940f924281541c0e92001e04007a2010b40120b6008941280c000300740071800d03d8010301e400781408030039502044024482404102c03100b00540d10020702d209045141c00120740160340c00149d907151400e001c140c441d40d100c0400c40c10200d0203030800e025000079500344200003160880c141c00401c00c8008160550540e00c0e2200c01d0780c1480c0c24101d1a03880000d0700f008050094208c1c08400032105030441d210000070790080080c001554040700313500b420740c00150341d031790300f10112500454000c4942424021928015401040c01d80f1030703030007588901c92440501c9000c1240521402184108598034024185403081ca0300c0ba069030060b5175900050300510500740e00c18103903411208400300c00b0548201013211b090400380203d43c0fa10803409540d6a15000304d4100600c40c0c0a0441c4400801503a88440000c0302c10b4064003000941c410400c01410305d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 579717508 1250 579716258 579716273
    0x4270c120c0e09011707060c150e10110307090501050a020c010f0315030609030806060403200103061503051005010306030803040f140f0a050105060418020d03020102093316 76
    0x150700982040305010b082040000c18501c401d80c01080f05000d2030b034004018243c18080440103041c00e06011140c81d90617655418a107841c6061051255942c1e86c81c0c000c0f003202007049000b03010960304108000c66409066449980c4202c07040004583c401d0400640b65208208a8000c4255075000d004041c510740011107a5890700f0b28903c08241e160004180d035491107000480045104071400141040d181c98043c24170403000313104912400e0107100c10000b040d42c0c2410303001e201041c2c6076501184030b400001a0014211908806400c03a003a0b545016202c0c3c00d40d010a01911840400030301c10b030303a20001141a03401c2c50000805120084c070105d0001b030200118449580d218403070b407420181140c0c50151425481900c030b12115400400100d007440401e100c1c66400140a84044c440c00002d2400c856103844802c1d0001c0c00b44150b400a0010301d8400c0d41541c1300d40c0b100510b107480315914900c0d004003005007a00840301e00301d10140190515200e40c0d0440e003600c10a45084100c2c41c1c0a81c4a108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 579718758 1250 579717508 579717521
    0xf0915150a0f2105180d03020309010c0e03030304030e041415010212040f05060903100e24041a07031506050d060e091e030910171308031609080304270c12 68
    0x1e00c0018a90171000c44c120280a056020105c5507001a1a03141035003c0e182540c0104200ca014041410743c00b001c13a445c0070003226481601428030b92443d0f4240c1002c1401090144082030f095102e0201f40704011100150f0810140c40990031100030300000c2da2076170b64602c5540305440d20f0740304590f002c00440c03c00e00040e00c202c40f4018103460b00c95044241c01f0342503a80303d0b100c0440c25080120242c0304a0b52480550b11039031560350443c12545403659903000d003809070241490000b0988000a900284a03400171200c0090030007107100255650000a4415000310b40200c0d0200c3c10400040341f10054015150b2084008000400f000c00c584c00c8511644c0d1000c071210715481c003080210b40ca00344ca5a05003038241c10700d26607401c03004100f903044100401b1000f408864800310f82c0c03079901c8041502807054079000080d0107409801100d0402c000d407520001903000b0209800081400105003409445040c105044a40c5c0c05d081135444280550482d800c8004000c04122001d20000d1182c229a0099 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 579720008 1250 579718758 579718771
    0x21e100e0604030b010f0f06020f120f090d0b192a11060c030402040c0503040c05060c0106050a03060b1c03020616030b12010c02010e0c0f0915150a0f2105 68
    0x240c0380c6500c3c1d450708082036030260082480ba078050801000180700303d440c0500102603901c09019414101c0a5540d122a0205800406481c1c08110f600300d0001e08800c46100c400002c0502da548616458407010f43c0408550a070b48034002c54805c0300c40ca1500d4021400c00400c6d158a00520586401d6841d807110a810202001c01c5400074016503400d1007040300e180519000717200c8540324900f5104000c03d50f1100d0142c0e0301005018001d01c0000355103803503000c0a5440c2200c00548075003102604034010003141d17102a9008181c4500081030001c076510000c00958242c64080c0c5500d4206010000000090340040040e0300c82c200080e01030692090304900e00d0b02c2c5146c0428240c0e503031000903080c2d003c14140da0045940d00c0005d04030668092148a001081c24806030402140d00700000300080304000c851030003071100d240000c44054458242042150004100c07140e200c0c5030405407910b41e08074403a0f00020807d200207110083d0302817807803c0c41e44c00b0942c120440c1001d030306100f4406403138040e148 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 579721258 1250 579720008 579720019
    0x27010902040b031909080315130606021c1211091302030f01150903020a08060603281506050d0f1b030b0a0e011d10050a05010602030910050913020304021e100e 70
    0x81d080010303001d41c000d41c068500e041ca0640760302815420441800c03002c2500041c200e29152b802c10480340c0104a40d0b410b1084a90a01c41c4c07420004400e8520340000c0740f81c40c60700d5203002c7d03d030f81e8526900710152403801030568540d0201e04a01c1500e0701288800d0310301d12003425900004000030914580e101b08800b500345000781c0120b80d00d502045151032680c001c0542c1b038110380c0c10400c00e070908000c0010300c6c0344098400c0800c00c04459000e100c50620000107088150f05012a01c1150450b800c004010031010380180d040800074104004080620b41d0229910002c070881c80d00880c003881a40341c10b50b83c01c030720740e8040398695822050041ca000360803840a0354882c1000c401c54014242a00c03c0310070314802400e14045080301c900103c80000701880711842c80e000052101550000070344268090a45944036030801100c82500c20f8019044e515500880c00721051540c844c250b006580124030070361b207110189511034103250289910388911034200d50011101d0350654458584904182c0c0701919 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 579722508 1250 579721258 579721271
    0x40b04030b040f05070f05010f3e0f0106051201060e07081905042001031509020c0f0f0c0a080109020108060f04060e090c0a06080c031501090527010902040b0319 71
    0x491504098865001c890806d00402c4100502c0d60040721101c2040c1d80703840c1c40b0940d121245889602c54055000c14640c2d0072003012501c00c501002d0009c0b03c1e550080400315100d4511200550b4080c22460080034000c404010a4803a00c803030500484040e1903c41c1481c0c04650369241080b2100c0400600b9003504a44401034698083c085110741e078020741c01442c90425142c90600c1c80c510a03080c807002103040614158010040203ca0401101910b180b4000941e44100e00b106040c503101d040340c01c0c201680910a100c03c103440002803154481030090315901d504660310303141d00d42210303010180039001c01c0340310000400f00c1c50103091400d21a00300406c0040d950b61a44022804030000b00e80412803540108013160252410030b5580e801400a45800c0d1004d2610b62003866050002506100d82c24102d5201020300d07a014108401c00347c4000b52030100e0342c0c58108990469000070216800d81000d8030400840c000310f080c02150300307170742c0c03845038a500d1510307140c00240340313802038001003421a95544e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 579723758 1250 579722508 579722513
    0x1080d030c0e1c030806060f0403110d120504030b01091b030b0406150c170703050a030f18060207140d050906610f050c090703020d050c040b04030b040f 67
    0x520500301403c02c0c21214620a081d14014100740c10207030907280306039000d0281440d4802d030713103046030240d903400702c2d030909014522000710304445502c82d00285031480d00652070030310f02d920401400450b4083c2d9031000b070170f0341c0c0c0b852800100d68220ba5000340733002d41e0b5001d0103c298001c2d0085c00031103201800001c0e005a0b10090440403585644840c070018100040040c01e0100150180040c0b00d00100521326000084d50040c0191280b0b4030b4503824551140414240c00e1500c1c1d00ca07061041c0c50798180c451008035840c3c010300035801075000f01c0c0d40d03010112007162464000140d41c8180071407030712200e141103051b10030003031140c110740d40355201c44489541905066400c2a1724103c1494443e01d0808101e0001d04141d00c1c0c02c18401c00c1020071004120364404016000440c112096040364140480d00310720700304a402c0008200c00c7e1074010042c00c0a04c10003a515500414408208203001c22403500c03151141e40d50340c8224400d00380b0701c4070280828800300b0a00c0310580e400c241300300d02890708456180d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 579725008 1250 579723758 579723769
    0x120f0c05010c0f02010e191b09050a05070809070513110c01021810020a022101020d0e0601060306060206011508070c1a07080109050405100b0301020c0601121a01080d030c0e 76
    0x4005601c0055000108503d210b90240500c14207040e035040070b4410038914011090100350150401fa04007200101c04088071000100131002610b2480c009011514184004402404080c0ca11400065004c40081c0e44142c0103c0d154040d0381008000c1c812141c000d0780c2d0200900305004260b4140c0004000c0380d400e05809100610209034a50789410100c0c1d0040c2c1000206442d444a55043d134010003540001a40d4564901481f06440101c001c0307820354208540380280070b4000042180391421400301024400060400d04035102d40d6001d1005507242c1c801262290420310500880100a2110382840f50040d40a240d00100c1c91138640075a280503110b2800700c40304421103080c60340d1880d041c00035940e4082c1515014208420003031101c1d0406981f401d5884501c1d8050030300d000d6450f4035445c8244d0303003901102c800102410446000f56150000c90b2150403500b08200c070f10319101546203a410101404990403035000c0c078040c000c0009900c07000e8001d402880500d0081020f9690a540d16554a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 579726258 1250 579725008 579725021
    0x30a1202190b01050a08070e06041505030316050c0a1d1f0303050703020105180a0201031a0d08030f070f080708130b070f0f02010e030a1d091e0c07120f0c0501 70
    0x40040803020f5160006209040d41d072504401c013641c02c0384406002c40c690507031140750481d206907000103045013648449215401c031360300802c0d45800700142c10240801001c402e07801041c05901a110703000c0000d0100240b9581343c7c45545083c7c44128803607104c7c0e00b89503040302c0ccd000190390520030a001ea032580c90b054041b05a00114081070001c902c20040c140d09120f0242d000103c211000d14180341045174591700c95503244002d04040d100c4d2050b203402c40d15000c96000e0300b080909104807250f42494841c805802c11101401041c108800140482c2d2150f144a1104411502c5000258940c24000c42c0c8a00c0d0040071031040425140e8507000180d00c4004080c0f0484007075881c1151907480003402450303990403103004811a030510111860500010084401078002410104185407540d2001c0a0182050000b80c0c0e10101005c104692520000780e000000300050744480e02e81e649000001c0198045c00d0409045000c58400084040780640b10140342da082908040e46820059078596095481 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 579727508 1250 579726258 579726263
    0x6010f061209082710320d061806030809090901020c2406010e06030c0c0a0c0f181424040c09050102120c0d03020304080d02031509060d02030a120219 66
    0x140504042c0c522000490824200740b805c5136840722400100c60020820038070001c002441d4400e0314250203040c0c40484080c0700c9401054001c40d11005101006c4000701203622035a180c81ca110101d407240000b1920516056a50011200f8101000a01808003e00006001009942d0708110081d25540100501256040095402420203011401c00c5110707103405003c0384d06202404d6015900c1e030342d0b000140d0340e000d403a281a65446558900c105481c2842015001e003c028004101044c0640c2104c034010550f8035018000341c800300f4142c0c06404840c480c01c1d940f2001e00044021410f560010407402580e1402d50595070f809030300c004009001ca540c101a0f030804a915001c040081d5601400101644103000303c6860420780408401c81e02c0340c4035610031004055000000404001c20081911400c104400d0210345918144c0b0485e40120103101c1003034819000d82c1c00040e002e240105500080d103a014005d484400c0b01a601c440084e406041d080056005200d00310008201e4900000c1d074070750 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 579728758 1250 579727508 579727537
    0x307051005250819090f08041a070f022419120c0903020d1a07050301140609030c0d03120c0c0605090123070201110c060402100206010f06120908 64
    0x50254003580080700710314082d565104007100d0180c28070703000f01400350320026990840250030080d400030001049410030041101d10454899020f0010342405042070320440307040d500d643d010640142c41d0038040d00000401010f500142c110050928003828201d400581f242e04214495074001d002c001d4101982c041002500b403c46034a0160b403050817600d21b55041e410400140b00605401030103102c45000203070040000c810301d0030400c0116481402a1000945048081d06000c00e00500d168801c2c441d0603d40d20954030300c2001441e104040340c103c000c005006022a841a00620013907000040c4d0940074001400c1e901c0d2480e030914040c41000c90095030f40c003410304d840c5181400807100041c2a51100ea80b602c03465000034114500f913084898401d107030140780e82d82c9280c0101e001d0164408081c500b004041804003002c0300001c0e800b40100e2084a20103e889030404040b80d5900c02442660700400c403120003085407902461a42401c142d6a180109100d68a0f0312500b103282d1045e088004a017 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 579730008 1250 579728758 579728761
    0x20d020403080c070b0307200309120307050c030c010f0e0102010e01020a050702031203040b01330c0201080f04050309060906040518040c0902040f061103070f052a150a020307051005 80
    0x1a10f090004d20061714040b90f005045052858000b080c0309590341890300d1001c001151410324843c10829101c2500c402030043c40b07001140300315580c80b50000342d002c540900c00da100388216442c0220b0000c002a0301a52060500403203000c0803503050940c02160303030655680e07048004034148280014200402d06455669450300103205051030a802c1100701c0e140c0802c184203201c00949100d19141c112005e10300b80c50821101540d98240164030b0f02000700362103407091540050710340c01801d0110340318000d0300e40c40d0350703552141d00440d850041103c004100c0d07001080480c04914004005d0003000b10b001c1e00140c00c16440c0c80220b0f500c0c06100401841d80350488041000300080f105440002d402c0c000e00039402c0a01e451070085030b0351454044d400078090300900049113458100705440205800c41e480036506c02c45030801c5900e0310a05541c80790800c0c05480924100001c1c04002c1c1510071014040d50082201a03040400d07681244000c1c41c1180410802e0b4000301e4000c01c0001c01c1e0543c0c0141c006000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 579731258 1250 579730008 579730027
    0x3140405011a010e100c15060f15020a0f060e07090f0b0307080715030207031b03030e0c0f0a0b0c16060f09050f03060f0a0b0a0b1918030303020d020d02040308 70
    0xd09008009810481e4002441d001511611400241501a4100015a12150703e0030007182c52100460840a41c64408000b03001c9d4400000e0000315009045d02210410008134126140d125009028000b0040c0494040000314660300506418551405454200fa1281415416aa000c10391500c106440ba00c0820061405000010040108100030300405141c5000482418260140346040c140d001c2030381ca06150090f21600d68481a81d4966101c511080c40d000e030090070041d040a00920600d446581c0d14202a001c000210800030a04840d0307038030b0194001039550040d0f500385441d0142c0b5401c068408002d5040d180544850b840e149401c0c4c0180038010b00c050340641c00f480c8034410400c0c172a0002c0e1008140d090b008407400d070380d00f9140c0d600d1824032009013104251554203d100f000c400036072000301e2001340c601d603208600004ea0038038100b40e0888032000041290108201e04a0b42040005d0103a401440301c01c00c04840542010003108240c1c04a030415402540c0550b40014030008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 579732508 1250 579731258 579731291
    0x5180a12110906090103030215090c060c1c0504051c1a181501212d030917060f1302041107050d020706080c0a02070801050c190c020609010f0314040501 67
    0x148070b01d081d04d810340c00b0b600d144c50080d42c41c0e100c1565600da1b100c0711030100346142d9003442070750780580d405040c40b03540b0703131a084006603541400c03898440850701c002c0c8002c042c00e10034411101140d20082c10281c20035030003030300410100b038150350807244d08221141c0d1186d1080c2080805200301a424000d04140c00303040052030800c3c888a2500c482d918070340340148900b1294181550200507200f0201503070002d00d00d406814a94150000d00c2290200086420486d6081114071003092003aa240c225081d035500c0c10200c03071000c501d00403d480d0843e1000803410815003041d16030000740c9210a1301d80c0c8405801042c1114000ca00c40d903040100010b6100c2800800c000003004031019100403d465890548001c0c4111005060b0fa04801c4000a8400c0c06501c00c000150107031030500d000704003608007041e4000d8254401a005000701848401000406000e040030039882900a00346a2401146500450340c40701d01c121742000f0300d40e07902111440031a000c1000e1344514070981c0000380c0100007007042d03407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 579733758 1250 579732508 579732511
    0x40603020a02070306141b090607120e09010801060906060c0f020607020d080406080a24180e190201030c050c10090212060f150409030c02060f0906030405071802040605180a121109 79
    0x2c514107c100b181c5c00554940500b1204a180c020000301c500c1c41c01d00404a404500e0826103a52042d04000082000c60044d4010003c5030026002080401d580e007070305035609064118044c0814428103044005820074100816200d84014a00303071041c64641c0c2d46c0c000d9a0000c0e0094400944010b003002a1410b1903c11070700d0700c4800c507580298240302c8080411440c403540c021707507520818150710841120050b80003290040705503c19210714030b5403004484e002102244081c8c0c0000e040c030003000c400320b005504840c01d520006001d004600c000d88441000340200c00e6040760816850360b07c2c42512a41440018001d0700c404200c4001820100010701c0d03141005a0224800e602c0e062520000070381000e0141901e0ba410348440303484010040c0040628000e017004075800c90000400c0100700703d008500030301030300c2500040000414856600c18100e0041c1e019510110700c00304007426511404869054818500038507102c0826194074143d5000010100c0845062085240c10403071440c0c14a42d49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 579735008 1250 579733758 579733801
    0x1f0b0a0e060f16031404080a0c150206160c0b0703150509060109050f060c121306050f1605010608250801180b13080703110c010c0305040603020a0207030614 69
    0xc0c186040c403210707a0064030880c0308400200b6007003000d003c00c0500404401d1294500c0d2045103845035aa0301ca41c9894503150138080300c600e40b04100c00300e10119140003a44034000300c1e900400310f99540220240300320141054240038442e2200f5043d0000d1440307007020307214400958010804e5200d10302c4a41c0814166005540700b07445840070480340340d1b801701044003180c2d42101d0941c141c1c0c0840300070986c948519202c0c00498041e000c8201c010401714002490b05001d00c14010508aaa4103000c5070136000341d1a095044036020445403183c041e04540040815001c2c000005160303980e10b144615002955500c2c0c0000b1440c99000007181d608801c0080007410400002c0c4041503d2288400d0085002c5070b000700358059000105e42e94640081712980303200d503c46840c55480000781400381c41e50510740d0310003a80e8462060702e500302d9441389003200b072000d5260f121107003090b0405074241c019410000c1600d04601c02c2e0b680010204046000c5c0342ca041d41e480717800701a103050041c4909013448210402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 579736258 1250 579735008 579735019
    0x9140a05030309190308070302070302030d021c0c02031507080a1415010c0507090e010506040f0c0801291b010b01050301230609040207060c030b0a06171f0b0a0e 71
    0x42040e80c9021040f900c610b00d0403180e640784001000d01201071440280c001411891000c141103003010b400080c1e207020f49000b00c3c1255034107030080000b26902d07080840d40c01c0400910000d01504940134908051080d44000e041c1c44407100c0105c3e4011140c0d03411524400010901000c1c0542c0d4200e610501444041200c1c1140759071074510780c10004078505100c02d504219128000005009052104002400e0025018042c42c030107910264060300061303401501c100e180c9040c840e11856144540802186a41c94002c550f071b01c0c080001107900b45c841c01420507164000407035400c0d02001c2d00200114054010040350041040b4007890865400d81022410310000700014040c040c18200c109603520b42103a9601d045024210105655000f600322044e005030010900104004d01504060120400c6039800c001408130081048404419403080b00c0c003082c0c0550780310742e542880810b00c6500000c0c0c0c1e6210230205031030700ea100415a0103580688118036011580301c081e154088540a1003d004981 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 579737508 1250 579736258 579736279
    0x1b0c09010504151a04050303030a0204231309020f1c06060611330a0905010b100e010e0f03030403080712020102180613030b0a0b040e01140f04050a080403030914 71
    0x4642c4000d102d80160303240c0e86801034241e40480240c03000c4174040c04020b000d81c1d85a04000201c0c1c0d020390030034011706081c80c4024000d140003a1000455070201000248403059080c03012071403e004090164041e60404011070a44440741c4804510968206640d4800d00350700515080550032110b4a4000341c04000c00c40003e2214910001040050a0301050f401c190030811001c00c0001e403403100c07406c20078140d516010071004101a034081d20205c0c1c010002803082c0a142d2040010202400c1c06220119051a1940502d03502c5800300a01c2d801c80504540c100140f818006071441e003099004640d01500040c0e000d04000c2c1c00f0003801103a940c280001d50405104080c9400c104084c2403d8500954001c101d02d40042d844801c0b020040d5003280840e1410305051080c00f02909900c035602d40180c0c28941c01c001e40650503ca010640d000e120030304809a2030f1002a00205040a00160780034801c03c0740e501c2c0031950800080000714400d0711000c2c6d12034501240340a040110200282c42508410f8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 579738758 1250 579737508 579737531
    0xd020a03060f0f060f380a2304050f0a0b181503040b0403201921110d051201150903120c020109050609030d0315080a050c01080c0324061b0c09010504 66
    0x304040001b14400c41d49505c070403071000115410000b803e10860900c00c00c0682c101d17000c07a060b000300280c80b826038480340b000d1007100030711150080b0343c813070b214040070100010707000724007800c5200080d850000d0112500410401c1c412010f07401c156002e44802098405110403d500040c00d80080034a801d80700726204103001d0242e40ba00111085821802e03544405401084081c000380100c20b8094001c0070401c45600000510003101e000b00500036110390700301c1408460142e07064031001c0c0d02e2200c1094840c0e09161089c00c049902c2d0302c03000c041c014074100c04000199217070321441c9012000d540e4483d8818003400010701c03c3c0c3e071030b920150045134200f141110302d0b1800b003225a54010075040103e042480500c00754681c4903242d100044034000c410004041003000b060030800c0400c02d80e2244500e40314920012b289100649a400e030020141410811280110030300c8508000c004009504250355282000b2180c207400710355541075041803074440e04da071400c03154040c00741205940810480c0f1912 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 579740008 1250 579738758 579738839
    0x100201021201051021470409060c08092a0609030718091b08030a0c0c05030f100614240d0204170609030a0c030e120d0f020c0d020a03060f0f060f 64
    0x1031b0b510a20f0807010062500c02034035030750411014560f1040042007086031619000304a150140c81444160003101103e2916150860120201038030b00b0411000901c0c0003030401007070b54071040d030441e05400384a07000130f040101c0d446465501c50007014040350000452604d2080101c802111555072182810300b4480b8103000000e540c0c44007841c1c06d2218603a00c180c02c29154004055200642c10311603040340f0410350801082c2411070a55220301032000940b00c50905c91100c2c0b5030402d1642100c465014400400c2194200c540c2000c95420300305e15042501d400031041c0d9010b6040146861050388504486090410101d6882524032001c0c5042c0309401c4401400b490020002500f08060102c0c0500c2c01c0d51008800b03001c2e1645d000032500b0700c080420010f0f010304480e003031110260242080810183c10304800c031220381507000700303001e200500310341e00e40d001860308901440c0c800b40d4070440b0050b4002c10f841400043d05105441c0d0803e02e240c503584c800070141c82c0e803107a120101c10a0319a0100801b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 579741258 1250 579740008 579740111
    0x3041503020f0d02160b13060e01110f03150307060c2a090b03010f0f0b010206010b031b0c1011041802070c030201031e06090b100201021201051021 65
    0x1260400343c2d8880032071130041c80410f1a505d0240405003802d09100b48900754401201d900c510900c4107001c0c021b05000d007a402c8540d21000d28810010030068500303402041d2000b540e00903d41c01c3d5003070078184a000032038a0f06403250440008150741e103000e407040c0480744080c07680302084c14030b690040a044802d00840040c5a226400c507a40d140d02c00c1320419075080d00228a10701241c802080781003910003112020740300b07030309889015000c3c02002040440e100c000302c0384181420242c03503103c28207041c0d01003101d61007400100c015004243c107a140c80705043c010080c04004241441d502d684c02c2c0301d0540544854040e26405103481000000c0029800b1030014080b241c0908001403003440810040c0703000710007044407c502c5c1d0302e0035601060300701c0c07145d214104002c001da500c4501414090816803c034412641381d644003402c00e00040000d03252498074910818540d14142910780310b400c01c4407411018890302504030940303902e40410f807100074480266880d0139002030814000c440503100d0055691 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 579742508 1250 579741258 579741277
    0x12180a06022d0304060608070308370f0306080318060705030f1c0501150518030c0a0803120a09020109090b0a050607030f0e0123070f0b0903041503020f 67
    0x4000c1400e03145850721001d81d403401c11102c042d000724144450b60355000790388101c90484e801c41c5046004520a0400210001920380c4402c0c074034500400c50f0340c002490707200449941044100d0919800c40e40480310955282c41d03401d0707112944038001c1d665013701a01c01e6a000360038541d20074030010341d1100c8900f4400810322401e640042c1d4440300d03400c0440c15031281031003030345419a0015054444c0441e010800d04100200c07001002207903211400341d484018a080810000358083c00007101205403480c1c98412040010308075190540d9003008990b403600307141d10856068201291022055002004180c0d012004020420003d015580060111070b95802550b59a90303075070690094948602c030000c009010000c1040303890360300f9490000c0181c5005d4010000180300c04c807000a02d940500710300d83e1050400f07884044045074418a10520b0303004020b0903190581c621a0b6200424000c180c07107030046120102841e0342e241000403640035207880202c1d41007018810805455000e42070000d81c1c10060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 579743758 1250 579742508 579742511
    0x70509010809100c050d0e070f050f04060510020a14030a020d0503070210061512050603120903010f020c01060305250e0a020706110a1103130308070203071a12180a06 73
    0x102d803626410320389a0000c00c0b00040d031340f400d031014040c16044005410446003141c0140015142115455110f58280c45103e00446403c8810321491074240d681c0c1000b07000140c80003401c2071750740001030600b20a1031180c402580015080c6014850742d41c45252481c600480111b2030900c2040c4020b42d1007600409560400c02e000c0003007507141e4030a11040e0041071f017102040c48159100c09001c004001d020f40c0c0340d404a0301d40300c1030009940710f60044500c1104002d010700300c0c008403c42054190f522003400b15a15561b40c3e03106804080c1c0c2407000d0110900441d000250740790451030200d240003181e03020199002e035119a000760307142102400b1816103007500700481080c0c541c0003840000c1c0c040c480005111034180400c0000e4818084007400c0d052040756100000421120082a22031081c880d560360080c01c45441440426800310007000510302c080c0c00c5619031360343c640003031070101c9000340540201d4800041c04c1ea075010420824603008440606000c1e039552a24522a40d42c8485010007499207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 579745008 1250 579743758 579743761
    0x6030610090f0902120901181b030b150108071106041e051c0f09050117070e090106080708070801050f013506030f011401030f110a0902070308010602060705090108 72
    0x251140e40c244008000320055901c046480f40c4810020f500700c985816400e9031401c0000f43d0200c1c0500891011504004801c884a103030780d250b107a00e030b0014a200a00c5540e003035170b00200241014400601c0342c00c40041044900d01c6140c001032440d40094070b081d0401c440383c0300500980c0004240960401ea01c8110103107a20003044102c00c0d4540900d0b800780140c0206203100b681002843c2c0c01800e01c82469607101c111a40210060310180c205004581c0050002c0010045504140c0b207010740000390742c10f0030710000d0451800201890800d070400b400103500c140901841ea43c0000703000742c00160508044017150705110202d0204070b900150b640c100203001e41d0b601c11107446042d0030b0054010740b0300002a603034500c045c5002510415a10309001e845240081426103d040c400c04100303c0c044010000d03075901c1d6865944640c418903100f51840100313400101d805e039480001250090481040140c1c940c410f80c1000762000c1c005910400564018000b0080300c40e40c00003c90340c0c11082400c001185 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 579746258 1250 579745008 579745039
    0x114030901110d020a1103030106020a1e081308010b01090b0a050a0e0306270102070b19060b04090b04050906190906020d110c071d0105330d0b04020702060306 70
    0x1d03050780c1002d24010040000c215180c1406a001458180516240c00e000e010244c60360940d40c0c0b00c00d1007040010781007a10418001303492008a2130001003281907144101005403160341c84c0e6800b07603010400c0c1c075480e52410084814207002d1808810304c02d00303151100d40e140110020107441007080140c00c2000009200c0d03900ea000f40640d1045680141c101c403103034a4208401000c802c68104000d548010341e604d60200301f4414021950080d610024201c2280c030b5010b03004488140041d051801e00d6102c50000c42c028460102600c01001801070100e858804201480111000900801800e0b0800070810001880d5208081d03250b054401303000407a1411810400c00070300a44001c14403403030401e032048002e00c480c0d0014000710756518041d580425501d040e502c4a2030042c09950700702105d03c40c0100300601d80042150190701c0d034401c442190200c40b02000c41002442d00c600b00c2504404034416811080c03510890030400300584007180b500c00c1c281c00265443c040200f0b0709108180402c1e040740d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 579747508 1250 579746258 579746261
    0x5040b07021c140705040911040e0312040b07031b0c032604060207030f020307031e050f03100f08071208180303120a050a090f1506080f1501080109020114030901 71
    0x1030b604802e0b4200c00140782d9240284102104070800b01c0d16101c0c0791800b150616180c400d10148540c8a60044003684000c805d0202030155000328010300d02081c80441a460313a60a4501c1c0704502c01c0000780300500d040f00c070140440b01a280707141180c00c43c0b10508001c0700d4202404503d0385805d810800c010074028102c2000c146501000400880a0f038000d00c810400a0380140151a02c203440b49074101c42d840b94100c2c0c2d40d0044900207400118404003502c000f24000d002136014024610707201345400091088080707030f0750007030740c540101340d070388010404c5460b99103420a00501602d102a040d420324010399500d41c0551408058910000020103136035001050010b07891450f0003409490722140c1a07000c5130b81c4c250044171504c030b807103041800095000d007441c0729940c01903500540360b802c10100da0300d4001e042c010740480807003100c5e0b8600020407414002c03c980340760340c18060020700d56031940c6000407200a406030f002112980c145040f9000503078101000945009207081040d80344d50724580e1050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 579748758 1250 579747508 579747529
    0xb01052802061302220f0f1a0d05030304321b1005040e0604181511070b07081003022101060e0c0a0f0509040f1a010c050606010f141318050705040b0702 67
    0x10900703143c030407c2c000d00406500945a4a2824080300b864038020209015100c0300750340d4002d1041d08100000380019588802d03000201c84c00c100da410854000285405201c1d06001c0140200d070b1006c002d02001103000c0203002e4603446c0540b0298140741c2d00134070113081c03406603001d04400000400c0c0000c10603101d946c401221402400c2c0d00d21032642d02e509109400350050484094240c1c00c01031001150116601101d5460f6440080078516035900007040b038460001410952405042074000000740ea84c1892100c000b1007144180c01d00c400540c0e0815084802907403040c00f91643c2c1408000c1d40416000640d0360716115400c100d008080840d40c2101c0e00d00c542c0040660040c904464240000c403998811a400303801501601500782051005441c0c100040030300500e59405030307000a030745510454010038886503030f0400380d0900071645650a03180c1c1214090460311010003100b0414041d0b510060b082d00003440c43d0401c01810003403001130403403140c1d0181588140000940c60115281c3d01c4010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 579750008 1250 579748758 579748781
    0x27030c01170117150a02040519050319030e0306010305030d0e0c030c0f130c0c060609020711041113030b04031e080f1909060609051f090b0105280206130222 69
    0x242c484d4680310940800030340141c040e0303d001c0c5400c005035801428405281a085c0c801c000d0041006200844e0014904d19242c1c40440030068440100c1440303072400c02a16010b584214095500c44441d081030310100c401c0b030804210580d0107000e40c032546882c003007402c0070312500c180c03024032003802c1c894082041d010000c05030060b00c0e4581480ca9924030b03481110100c4981c4260006c0c00171a644070442816402440ba003d45a40e880c41c202114074641741e8084020702d015541c00c5402d1020507151800407400c0c50340b055075910386202c100010558440c8204500c0d00000802c070385803040d02000100801c0b07000b41442100e010200124403941d030b1640e41c151515840c00000d0000c0c00d414900f01001d0711107440f805030b00030b09107004140318001e903401907119001c40000c42030032640f6010714800507002c03007449181440010040308141e007290105034182068030031440d622070300f40d070580245081c90040c0395550100140c05041c0061b80c1d4074020714403060301d007500e0ed41201000c00e4800002c10070001030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 579751258 1250 579750008 579750043
    0x6050a020702100c0512030c0306040c031b020703140304030c03060c09051f0210020a02030a180e18190b27070f030c0504051312020327030c01170117 66
    0x105010950301c049840a10352145c0c0585010341c188051014085c0400c0d00c01070300c40a0141300107030360fa0520303a000341e001010034500428010240c000e0f2111201300d00007a01c005800145050091107007400b41c4030000c3ca0480000c51601e03240d91550b0040c0b40d0749010040c01c0544516800d02d1051140301e20341c01800000340b0051a01c20286d650303c41070b0341c03242282005801205024040c0620f2842902c4115145801445c50000280381c2140c1038010038074106010300c4a5034000c21205c544080292060a0300094500594050802d0364036121208642294000f5103900090014200440d11034210540002c981c010f40800003104100c0500a034050440b44078413400020002130503030358101201e000f010710140300c545420610064401c11240700c1910142c800000000500d00a10b401d8081d11502c186e03410f00c103405080306401d01101c1604000d18a5480e4841c07842e103000d1101d0121640d003402c1401c10414118500c003400c000c144a00c80d80c8400700b01510810380800d01c40d03480728182c1d0010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 579752508 1250 579751258 579751279
    0x90402130204081c0f020105060f010c06020d020c1608031305040203041e060f06050a050306040b0709270e150a0b01091a040305160b0f0d0f0f0f05060a050d06050a020702 75
    0x360f22020604d40c1c4c40b0000342a01005801c075030040c032556024880241c45150340c0101e010040d110f00010060032640ca560800811801a240d44054808070313441001510b01500d07032a2a070302d000541508a04031030f8008026513504022804142030880e03900780c0c1c015889680780d061010322070b281c442c0254a8000070360710000802103039030300030500c14000d1201000750544840c1403200544050107140d030150b000c400410f001c50071035034100380e010460745408951151590036048800420140c0452080c0b150640003680c481c2600500f100080c001c8002c0003008041c001c030a505085c045c0031940c0e40c80d43c44140d40400d91148000d140904100d01000c0f5400c2c034906158080350303109101c10350b403600615030014038020090a0700800c4460700440ca40c1080e509607046003072648203149020407603548800c120111815400350b0107074911217000004001ea003041910f030503610014030341880740c88103d20520007591503070306c07800c82c850300000c0009050f52402c005400030b1065210181d4003802086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 579753758 1250 579752508 579752533
    0x30e0303070b1012080d09080c0d0504080601170c0112060b12090609030c030f09010c020a0312031119030f02040528080c010c0f051e010605011103070209040213020408 74
    0x6005900a81035012040d0402d0b640c3c03245806086410f04e0001e21781700342041502d4110855810162250340a1307400b0354548408070900c503240c28105444c0101050002c6010081030606100c02401002c40344140b01d4074a4031204065140d10b242c21600e814000c290200e0784008150307502000c040e08144004035620545500035a600940440e04410340340706400000304448000f00983d821180010300650420341142c5004105400c60204d039030400603501642409650b40308004001035018100b154140b401d40e8400405403400c18546008841040008542c503020500041c1e25030a038518002441c2c1c106100501d0113841345500c1198413021545140140149446070710140d4901000c80d80596075641c1b02d1180c6030074040e01c907140032070300702c1c80704501046900d90b000410134450300548064146004441600c00054103a01d00180c0d5180010700c1203580000004950420303141c002c40c2000e50560000d00804001000240103944031051a1080c000c107070140d40246c00c2c0d42041da501030340010b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 579755008 1250 579753758 579753773
    0x120e0709020c120a170a0e01020a0c0201111b0d050c1002010c171b0304050a06050709081e070b16060906020d0b0607050c100c0507030b040b011d13030e030307 70
    0x40e240d1802c2d4024540c070003510f060301c0800c541416106885050342c010040280d542c03c19001040c42004079200e20b050188a00d00788028120b0384036645401725149030364000100802107600c011f5460750300c154414012a00d21900307454803403a081362007c440012900e0706a00741f280b001d014541007020f440d0001c440c141c0641108200005940d81c40c6543c2d08400070f1301ea2040020f503080352401900f9000310492441302d03c0110703401405082103a00e501074642e0740078100c0720100d0340040061341e03001c0144641d51040c40707600c40b0002144140f01c20031420880c070310388600c41ca104141803208005020842ca44510001848064020004001d08681800c4c018080c1d4002c8040402152414145125520340403042c2c1e07001f10f070404010292a50814184410200d41102600034014000b00c2c0000050382040b40710041d40c03095504020504162130000300911068000300168803900001ca14110180980981d00515280c9602e14161040c00c0540e201c0992100450b0140000a00715041c1303c02c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 579756258 1250 579755008 579755017
    0xc0405090a021203030c0d020a051207120e0a0203190f021f08010504060b070f02010e1512010501020d0203071101050f03070815030d0c0204151203170609070f120e070902 75
    0x240c80c2021990030440f52680c0320720048411a092100500016507002110350180610500038117201e80780c42252140c070603800c4400c07144440046e0000c14080c101003668080c203c0d000c1c05c48001811107884503030000e40c4501600754803a0584c0031002d51542403041c080ea203510341da074014090b10042e503895850416a618120f80000100301c00000000d00350030700f41702e504112600103e10b81d0504509903101c9a00f5035400c0300c1030341007000c00d01c064849907a80b00710300e0b000b050307a46a40c1c0d41d035058046c0150b002d500059220505540210740107407000364020040b9101c4039403001442000c0340c1200f005a83c14044c084421850080200401c002590007220450084003014101401c0341d403046c0406941e81030b608180400940d11000900c01401d0580040c07200004058100c20156180d40720400380c82c14025040c1d00048208158843c0f2130b40e2807581301c0c0c000b40c00755101a00da00e8a042c01809000c60380070300710100040c102505100003e103074843e030114a0903005640503240d031079420101a410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 579757508 1250 579756258 579756263
    0x20a03080601140d020315030f03090901140a1a07080f03014202010905010f0b1008010f12030509030d030515041b030504080d0e1b18060f030c0405090a 67
    0x5003100030544642c0600284070150b075007501d14518040461107004040d41028192070003034807686510b590b140e50180180d8444600440c000c586440b080382c1001180c46040e8084610311800c4001070800707480d40c103001401d481c10020000d48144032440291a0b52092050107000d15a0201e004140c03020384000650492303100f52039072402d0074401224450580a00e249840003401000142801c0111034045894002660700000601001680f01c03242900c1812412446881c0e40c0c500c242200c0ca4401c0d20340c138882c5030b24501440e49605050084032094142e000d0140d210070310003000010548a102224940800030313041c1d07080c80701c490740c0140107054199080a0b125030358080201c05800c180c441e00041114043e101c600c0408898804e40041002a105568440042041405040c458010241400081c0b401442c480081d00d06550b1500d01448210344a40040404d80c0851b074024007441da0401421a035078800035020200081c9400b801e1030765117400034104402c025a080c0081044910300d0b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 579758758 1250 579757508 579757517
    0xf05030f071401050601020a031112190f05030115031806090f060f021602040525050a1803150c05040918050d02060921130b070309170705040b041b020a03 68
    0x2e11026106080c2d0b0005c03035a06005074010781da0280840c1c4503030509030075141e80000303994460a004071200400d07480082034859800c4018480c2d01200d61107103a007002c080e180d00c0d14608550420803c04605144441c510041545a2500c600705410028540c3d0003980e001c0c2d810400c08100340381044024a2460003540c48030314110001c18102d01c1402201c3e0203480d40c40c3c020307900d400e10344c0c00c000c018480540809042c0702200554400c040b2800000750344d00a59464954482c01e20a0000703288801e4040d040603d074404040420002d04a100044540b0320810707004100c000c03100504407000c0c0500c0d07000c4201341e41000014501e4003401b8041070070090040c4261941520070100c1603030750712030545500d40268484011408034403a441d03441f404203400895600d03d01081e5140031120003000e904900c3c070128002945038100364000811400400e18034500c50744001003201100d849010511816008a44400e60310066603030b1540070242413881c40b14082d0399600741400082d0b91f82d2181004a0114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 579760008 1250 579758758 579758783
    0xa180312030507020318060c0a020603090745110d0f0f1503170c01020703170907080d0f030902041a010809010b0d060b010e0a0305211201050d0f05030f07 68
    0x440c40842140c0782d00100e11300d07028074182e920047c00102c1c0e000c82116101e90040e082d418006903150402035014002090080c04007a082c00440070030150241146101c0138030420079007181c520002c500032245480103441c078006059620015025107190b02c00461855000a00514188a071748d000e0109840c03120410040c0c4024007104008844400694040c8500c089204000081c4041b040725032100490045600301020300002d542660408101100481d0007034016100a4248844466225141c0390060506a10300250070303440350312988000d0108070f0f50407400c078881e0740030b50010060144c1c0500b0130014402800c90b44902803ea80c50301e9800203500001141c0758410500581100d0a0b000341010b141045c1640c40c50000c06211a016040c000940740144042c1c1d11358140c80c00840c001c002500f114040c0303d9804294444101c0c5120420005000c00902006410b08441c151503040d5000c000340c0c80c0504040e0012444080002c0040c400003a0780d40040356000b020388002c52103100001040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 579761258 1250 579760008 579760021
    0x1404050f010c0e130513080f040302010807031b03051e0a0b09011d0604020904060b120115050a0801052709031c0c02031804180b04020f0103050702030f0a1803120305 73
    0x1c400444400650044c14001d1030f0203c100c0d40c0c0d00950308492035030717110f0a0403440c40e95110b141d500840d10359005090085010019942c014580c1d40e4040d0091904006000da41c45000c4403411301c03c42d1000c1003540d1440040d01016030381d042028107196102c00390f400791800103400c1c030103045c0c2031a22070301440c6030000004201e6105903942c9a41603c218a84425503204800e000094009070340c4250300c0303601c0e0440002d403400d030000100005040a62045103030340c1040110b82c0c48051209442c070400808205802490758000323581c80c191902100d01c028604012140c0d0203c9601c150400b102201030030003401500300001000b8000d40d502d000d030011550482c0c1d2602c00844034044446170150b0030821408001681e060407000840d03200410008017610045002ca48058070f40208031001c40114080c801585404c1c40141600c0400346410301c654030705214004c5d100d00407101e204600c01c0c0080307480003c40f80199031042c426103032500c0c0b00b44202c1d40c0782010054035600081c880c2c013180c0307400d010411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 579762508 1250 579761258 579761267
    0xe0315061c0b041e06021810081b030405120417060705030411040e0f030d150803040506190528110114070c020f03070611060f0708060607061404050f010c 68
    0x420a800c28164140b030b070b0f100d4440203c038507038040d0040591a100c8070608005021880548001c003114100c02c40c00090050a00c4a6030b2409020b590034449c910080094124446510383c00a05a208480c0c0c2ca80d10b9074544149402c01d820f0300f0081000c400704010900c0081d1554021514a100c41210300548400c48240d80070320050b00c0150107032840303424100d002c2c01c06402400b13810b2940000c540315101c414400a007150030620206e9002e51301c0e1150f00540400f2102c04001900d2000080d52400d850000019010710030054a4408910703181c040081090080094605540907400d20901e4000c880c01c180d8070000c0754044000200d20b60310840c4441e00b4051050000030050542604c116454610041e10500070300c50003268000000345039110301d0340701071103200001c2015490786c3e01d500e100501c0307103414001c00070903105440d240e10041040303650307104040c250466001e803521035845c80a418824080c1c03400245405981081e101844208100002e0741c61111011038020440c5c100b810b07034120f8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 579763758 1250 579762508 579762559
    0x9041103040507090c0503071d12030c070611030711010903150209040e03090a1a13080607031d03070b0a0f0e1e2b0e03060702010207020301060509060d060c0e031506 73
    0x60000e1014000a14240c0c0610100c04076000c25460f14400114089c1c0010700c034800b0b1881501c05a0000309540a03c0901009610040e000340d04202e220040c0c00c0c0036060383e81c05000001f03894102c861108201590007030007507002444e004842804011010f064a00c041d50028808900444c0f809070141131826001c0107881c0e0b030b040000c0600d272040d8075204408540c003415280c8040100e004000d040900d54000c145500107004060161089152145002d0b003200e0034070320b4080b011600b072044440e04400100031100c0c00e50340010703401100e40f1041030520007042a8104980c60910b05441e03c0c1e1001000115100e01d00300702903000d401e100d2a505016280c0b00c50110a240c11402c1920840c0c400582610b480780901551400d03a2182c0203480c00207150000c283c50250248c3d44c000750031001d6040a00903080504010b03905801c20381400c0b0081080d41410301005050207a40d0007091800da4861002c0480200d002400c84140f16500814450381030410341d111072040c98a142d042d0b0074210443c0360039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 579765008 1250 579763758 579763781
    0x606090a32100305060f040914071508010b0a03150b220b0d050a180c0f06080f010312020a0203030f040f12020603070c03020c03060f0a0f0e0309060901050904110304050709 76
    0x4102e0040c101105501522001c0c0040d07a0104c5802d0f02401d041d111841400706c0107000b0b084032901c954492070b4070313803c3c15400c0c2c20504144440c0c0510b40642900402400e04651400044656503001c1399400c500074240c9200c000f152b1200382c400040c1c0e003101603024041e8445040882c45c44074204480c102880300e800c0c032698200d0a400d01c01003001d003440b070f03018590050205034003103902c0c03440c0c600041400c041e15030101c40c101c1c414001840b0307260072481e00d10007a1489092090481c1800e06180031224030502c0018441c454001c071b5018410710034440408290390180840392a403009440d020480d40203405aa42006001c1200088a611700d003007204205801400035032864540c5001100c0034000604194154425001078640300e8a0030400f03a441664420185000c50502d614008152070050400c01203181c20002c030582ca8601c040111400101c040b41c0c0300c0e9075401103400684590140c590919441440c08403441c4d540404400150b1003148145d042d21f00c10703902c2d070701100c0864582c003c030f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 579766258 1250 579765008 579765019
    0x1a090f1f181a130207030c020310060e0903250602070606151b0f031419022803020c10020c04020c0c0109330e04020d06081c0c0b0606090a32 62
    0x12103040125580c02064006c0c080e1815100b21107080e008245007505110074601e16541d103100400048616100041e000020400034516080d49404d07034025801c0c890442608640000c445001000003607411030b10b8013584440207004456803804003c80c082842004e400201d0741c4111719607180c0b100c140d001540c4c04d90000514a040206403001c80e80c2c0040c0c0c807040109000100311038958001d10b501e040c412489994000c191007842020715841c0c001d00014103c03030b02c0d020754058100094020403060359031041a80c616800a80c0c4010407458034281600b0181c105100080f40c0c07803c00300210b166820440284c8840c6500c59071010702510041c01c05a100340c00c00b038403c0c441e56206046c0300451410013030f81e25080c4480c05a500024007240d000e5400701c5541540d403401044280400e0201801c0e82c0d07481c1101d0050a0000c44016004450502c0b00403e01c40d020340000e4216901d02d81914a201d601800384c52220307480e6145043c034108454100311030a50340c2620b005117020110010455200003511 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 579767508 1250 579766258 579766279
    0x8030c070c0b0d0506040b0a0b09010f020106120c0815010602030a0e010c020a0b070b0907080a03030e07080f06040c050303090109050405060d0b0a0f1a090f1f181a 72
    0x2040180c20085088600e240c6407100081c4040d00c070300152181c0c6611030400141405c014040100302e4038840d02e180e001d0743c038465042102509440a03554055428200380300070408001c800c03401000c80760081564081207403041da05000000302c001003904c00000458013100b420742013001c91200700740308110050b40200407880707485206102e040d90407441818030f000390310154ac3c0001d00c2d4403840d401c0240c000c5d5021840000b0300030140f03081c0360802c400030003a28401d410300081d2070b05c500c9002c001900340358541c0d559101e10201001b089004051000a07204445044402315845003410f40d003c0d14045036240c0e01081d0761031302108407401b40e031050b113615546618100910001c1c00c802400343e980100c49440c202e0109054480881c41130006904c0055802070000e901e00840b200d0402c40941380c1c2d14542c15101030f89550f440690407846400e82801790b40e6501142da00c5003103881b0300921580d602000f000852410380140155100441c900600140f4841000701d083e40000c49499070b0710118040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 579768758 1250 579767508 579767521
    0x1030b0103030c03020a0506160e0d0b01172d06010614030601030e010e0d03020405011101051504051b0d0b0901060e031c12060f08010c11030306010f0c1e0c050105070803 75
    0x1040e0104504c0307801550307102c95a68440380e003860801c68084e411009000803004141c0d07440f2408422040b4211115003140505440d0b030100402d0500440c55075529502c000703802c20100b00038404004800351080128220300b0003049d1652420f2252039240c9110f04000403880b980035104603242c20940d007060714156950f060046001c1c1440c42c1e0b410f0855541c50f55401920b0205018169064406440150f42c4501e06000140203c55044645000ba403411091003c00c0d2190196a134401108840c0410642c8588080e80680a81c0c40300003504542c0000d0710b000c103062607400c6040c014000f1940e40340706a03620034043c1c0d4194003405c089070b490342156401c2810b021080c4501405030080c4d04d010319503031141d44003000895456070401c0f032190791442c40400a01c0024002c5d036501400c2491302001c060310340644c40e9601c1c08090079a030705100903400e18000b054400c01c19404151f4015103000841c480707105940c070b0120301c50003055401c03d076854804107180d4010822a032220b640311003d81c0c9150b50701c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 579770008 1250 579768758 579768767
    0x9050c040e040b04020604081915020a08040f030203160606180b030309120115030303020d0e0f1c140f070b010b0901090e0402030a0c0305060121020603010603021c0c0c02031501030b010303 83
    0x60081ba0301100501003c240681d04001000201800481d411420b44032420a04c2c4a1022402c00c00c3e681e41c01003100c206015400792000360000d0740700c2c0c036541c10550741e85010b03421809000364030002000300e04c0e0032000740080e58004c1c1d000c50b41c590221142c500401007132202550040c40080750941e04c200f103840c4103810f03e1441034040080003400025502c41c010070481000b002a030003500040e801041a020b88103051103001c0544007014000c010007992003924a484500e071a0032030110342c64910002882c0342c0924800d403c865616000d00b55210000c131010500c40c1c00041d01031312480d40d004000300388100410200e035035254050f1038a03140c0610701030082d420544000c0c000c81c2c060007003580b8000042d003009501400340d40b192010b000d4a6040c1800010301841d11500444000e00211402026803241e2080341c0c1514024a0090303030b45c1c4440c501d030380d51074030300d05d4403c0d42001c1c035080711541c03c036910440c680700403031088050b03880f01d0520780001398104100b03001c0507141c9613412004000182c0035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 579771258 1250 579770008 579770011
    0x809090a060801050a090b1f0b07240207050d0206010308040911190c03020f0c1503220c060306060e0901261c081609090507030905010e030409050c040e040b 69
    0x200340011640e81c1d140c141043c00e482c0180d4004410303d4a603a5078104000c010fa0081368048409841c1c2d030108403c0c20b802807220041d0344945a003a42c07001601600b070200c50100d5044030501c0c503507060403180390030f40030800070f40c09282d05036018004d8105811401d0700c04501035049940048803542045e0410740010300800d480d01c140700145004210f104d540c105c480c070440f004100191924003200b6000c0c1000b0f814905181580e80154004041d030301c80d1642d400700b0440d0800d15080d011512a5181c0b150012200d0070005440c0c110901c14500504000e45c2041420603074040c1c2d0380600070141c0e2088150f03010084d0040f46580151000c2c014401d0001d00c1400107170901c46110410001c00100361194108140300042048101a0800c00141540c2012503690441500c07010110b03400088900100748032480d0041c03010103901d070008070b202c2901c0381c1c001c0301c01c0a8004c4001c01c0b04600f0000035583d294424800c20030f64034201030010f1200d8000c90240c404a0321201c03840382c000c2ea00ca541d81000e0b000e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 579772508 1250 579771258 579771271
    0x340e060d0b0d141e0a030c1e120e0a030f170f04080304050301050711100c120f02120610050a08100e07050702040b0406060c020f150a080a060909080909 67
    0x648600e081c805540701d00b99008014002d041c2d814280190020582c2803644486420042c40350078501c0031110400060b240301c42d00d4140c40c00c904c64070010b140400340040c0004d00121000000071841c818810b0891042c202d440a5444001c0c0d012112001c3c010100798522015100e2040c4408145c04114030a1400403011b8025a4452529252104c0030320719420035000031419900201d018015400c0910509030400180e091507807104412245090f5a40604c1c6101c4402d1900da100e1010440c0c001e5100c80c21000c003411082c4000301030b020504000b500801001034001c0145000b20b031071414001c240c9820240259612032038455030000503540d003c0003130000d40c500031012344001040c46403140c3c158058541c80c1d548035038408a0740104800d4500c0d881003540314500d0182c04026841d0070a6002040c1030741941d48101030300c071003800141403180745485407a0b101070000e6a882c0c8507600c10f000311700c1039074016401c100d4241c171810944100c54001000500180c020801c003401d41c50a440182d60021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 579773758 1250 579772508 579772511
    0x1080304090504150915050a05150d0309080f0a020f33040b1605010c0305092112040c08070812040902030901021b030307141e1c05340e060d 62
    0x2104c4681220440e00849030a072112180056140f03040d40d054007600340c00149540080c4445d0030811122680c4072080d0380081d01c105007002107401018003980c03441e00105811019905c0e072030033030031000e0388800045104a01c58004082d14506610344840072842112a8000425084850a4403007040c0c4400344540c4100380400d200000794184641d0040c41d0040030924003e404da14945002401d44405031640f006043c104000c01a00d00000074088075440f020a12004c2d42d440c1068030090303903121300c10010b200f40c0c4100c0208000c1c007148001600407200708200f241e41c859a6000030b11b40342d05003252030451034541040200700c40c0d200c503000345801a100d8800149030000c081d0110418101c90042c070865600b000c0301f045a815040240c92020400c44031080745400c03041c0c4000020821031545008848102050326501e0134100100e00c01c1000c00351104100609001011005a8403020a940309180b18884004c04c04c034154074043c180b5010607251486001458010440780c0e400000019085a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 579775008 1250 579773758 579773783
    0xa15030b04230303090c09060f0a03060b030c060c030301050d150e0f0111040b031605042705070c020d150e07090b0406060f090303111c03020d0605030601080304090504 74
    0xc0803100481e014034402d0041d050540b81406221000d000c080781c455099030400d004000c0001004a0512003500c000c440900041e6246000240003084100c0ca080d00101a036001004100b0181d010038100201101111010007012007001840c1c440c042c100d6204d604240700404c2141040b541d8140001e1044035500007110202d075111080306c030030700c00942c529403080c2d0341601c4400080c0301d00301a940e001e40216140c142800700400e480d103c054880000719174041140b241d80d81c402c2055070013914031015130070340b02d080c400c000c144241d810003600070100d454013010a015038056620407507105d502411451107850284c6516603154200351919100703d40750710030128100810310401e8043d00c034804001500c862240c05000071151395400030000e000c00521b07024020398215001e002100e03031510740281081c44020065007002913800c0c40c1c030076000b15003500308001d6805401600c0003400d500000c000c015070300c00815686003802e02c40c0003110f800400080c0000100780d00306e2a80070f030140f0b80b4440034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 579776258 1250 579775008 579775013
    0x20d060b13020309010f0b0a0b0a080c04050612041a041a070e030f0d020c030d051b01060e01090903030510141009030b07020601180e0706211a1302120a1503 69
    0x140d0740104c80c0e07140945d54800307045069000c0d91046c01c0341c00205952299140d0704001c80c121480c440c0c0c030310314418090400c00088030140c20b4022100900300c003401c01794a41c0304030410340300ca801041d203003102e480141030340c2200c58a0110503140d11554204416002c070341001540c41c281240701070013031420414400c84c0c10100751000c000414484d505440140b18000c0d048070004d082028000540c0c3c03280e00020b43c05040d265014080e14001c0c01480015074105d104120700c60700501c51076100040c00f0b0303408000021219055840000940c3c00f0761001e1141da03482d441d0408030100d00d8000c40b6101c0b4030b504000999400c0100b1526000e40180c113100c1019510307a140c0c010344e075800b140c400005900c03000041c0041c03486162050b80360481b140007401404494400f058444034507000302d40400012112413818405009a80d001800341c0680c1000600f021030407080d9031240310005a8000d038204083c20303000d0581d138401c480d000040c083c044002901e030140300402a00b02d0070060b6000c1440440c02101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 579777508 1250 579776258 579776261
    0xe011d09010b0c2b031518051602150403050a0c0203060112031e1428020a11060f0304060f0e07090203100e0103050a2607060e060f0103020d060b13 65
    0xc2c00b4026202c0d9268880c1100312441e00105405000034000082c1c2c84001403000d050b42071507800710605002c118100e400400707070030204480c0c1c8401e103180e1040070381040c0504158041c1d03008908c4d02016091462030f40d2800c1c0d9860f40507440b8107011051550000c3d011a00c540b01070030038040140b4042c0b103043c11070b80000f807911400780c01109903a003e8040010406401041009114110305004100804601800b4190301c090880d05600300030000307106c0c0c6148448800410030100855051400300c64200c9000395501c1040c5c03012118141c0349a09041d09140c04000d0f00c180500400b002c500c1c0d941c0c1c81d91307000d018054040000400c585c07609446100580c003444260f01601c0903a40c01603c0b403074017030024580302c091940300000c101c0c1214014000320b0300220350742c40440d42210070420184140300c040c05000d00f01083c80021844085071002c100043d070b4101080307102c100300407209603441d1052030385042e180a220003540000200e00e004002505e81d0891103034035030010040c14101001e18113120 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 579778758 1250 579777508 579777511
    0x4141911040c030605090c071110030507020d0513180e01061d150f1c050d050c011407090515070204020301060c12030b130b030c0d0507030b0a0c0e011d09 68
    0x440c00500005500d4990500d07100382d40786580c40b860140700e11442c00d008140c0310340c00505007448103e00060488140201d8141003211094040e000c07403014016500010014071040da00000180202c000e45020b0600c10f1090320b072180b000309641540c0d1440c040090740010844e0f9412540a500c890380300990600c01c0c85004c000b000c1c4141c1c40000f02002c10400002000c008041a12400302c02030700d134000703803101320b150743c598901558045a10880202e0401926043c101d00a210303100b0a080060300540c0003004d010003600d900001c2c0304080b42e8091410b400c040483d401000964044800c1141e40f404e210b005c012262034403403441c9003515a8010805036402604440e02141e01c4580c940308001c140c040b20000100517103400c0000c4a407540019441c20003139208091910780311602c010a6940034441d0813080304004081c0030030031055190960711b514107444281d90381c90004001510341d101c94001c0494140c00c5a540c4ca1403900f2100c0195450314000c40400d034802c0e031b030450802d11a04c0c5c000d68603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 579780008 1250 579778758 579778763
    0x1030803010f0605040e07080402190f05040b0d020f0f2103040f06020f0d0809031324020708070315020405042306010c110907021c0c0c060f0206041419 67
    0x440e03503076040c8035090300c0010003039010300c0030007108000810040d11981a290307000039103850024690344031400081c8d03c180c00f01e1070704a0303102882800060f8648107110700310203c807400d440c20b00c810014107040180d401c0000300c0c069040721459010509074541a00401c0e40f00f040200070141c10403000400003103100c1310710140e85281e0701c001010b00c6525804000180109410310041000700000d81c0351300c1d00c0e204030750084820b0017141004039080401c10f00a480c0c100c03502c603641034141c50390744084689080355030800202d007182c201841c2c0051071000c6184030a860f0100000d0000c60300c1e503a240f4011010003820a00116400d000c003064503661400f55000414441580f04082c0f144c40d0b0455000050151110303040c01450303000d2030001030306094410030b410b100300d440701e2040d41c451109170f040500450300e1541c40341c11200c003503007e560403220107140711b806003102140329905c0e010255126100464020050b0f4004000240000d8240c140b09003176415010640e50160b0040042c9501200c07540c204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 579781258 1250 579780008 579780023
    0x80c03071212020408030915310f0305061803070204050f0702070602012f0d1d06060102010b13200d0c0e030a0305070f0512030123010309081603090506030103 70
    0x5181d0158460a150002082c1d22400c41c502840c10300c40c00e0f43ea100f40300c0e4660164065904503804251101c0c05e5983c0b8001a010042e4840c405001601d032146407800003100340e4280380c20204105800410004c140e0b41c0c8407008040c140c880c0810380c0d2080d03505040762001403104016000050b00c0d980201c82c02102c82e00401c0703159081581001c0e091280c680c208008580c0b401007801d02d45400c05078a406103c60b02d981c45100c1d04a0550590300b80e100c1c00001c6c1e2207043c10719050340b240004080f9107403040812f0205441881d11654012401d84141d0740759140d000840040790a01c0f00d00c968414140c117a000c40c0390440340b04000710580344640106596680310ba50700c034202034400b030304581d441c50300300411406003000403002e42c2c01914a0151407409408401c0490b400420084104050710070480d11035807150700d0350f030348882404114600c1d5402a4a501d8074803101d5186501034001e1040c02a8814886030401a654800175032115a080054081202400000030161124401103010718000c190 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 579782508 1250 579781258 579781283
    0x20d1b0609060606020c12060c0a030f020c06041505150603060409021e041401030b131a0112020a06180927060c0e1002120a140c06060f041e0207080c0307 68
    0x4080c5c2094070300340711b6901540554294510944012922550000402106684402c101e0401314020001518110b201a1001540c0e402502c0d000401c0e81c4290303c69400e5445440c0c45400380780030b5130070079180020205102c1c1e074443c00d2443c14402442d40880e01a2002420a015030005000e110407003920301840b80d10003125580074105406001303010158060303134101075403541e07440004603003001301034045243c1d40c04030041c00c2040e0000e01c1c50341c280078003900410950311400316070200d50700000104e01c100120400010010302800004400a4030040a0300c1c169203014034001c01303003c8074007030320842c44040103081c40f004c100402c45900b014010b50780042c0e610f00031000074012000055505224450013010880d00507030019508024883c42c540c090b444542c0d02c9810740301c140840c0c003e240c01c4032000c95840c0801d0000503510b4801d04046802c0000100c4120030301049401581e04004030352841252030070341e01c981d07030010301002d171050001901e840d2008410b10b041d90041c16080300c1c403000c281c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 579783758 1250 579782508 579782519
    0x512070f030510030201020a0b0402040221010608010608012303030c01060909140a0f03031a061c0522033509010b03160501030510030c0609081606020d1b06090606 72
    0xb0803030b9400111090a248001d0650f0000b03507030b4511000303000f800c039200300d8009003c540741c607015110020700c0c50f4034080703000391307902010502c00400340110320008a4000000613043e20500d0458100c4500c001e04204d0f04007440d000890041c52100d0480d05444208445c10100c0804d10900d4010032001c2c1e40000d000c803003440c00d045104a22090101c80d035206540da40003207421110042e00d4030342d05080002d003210002090301c000022100340c55900040210b4005446840748201c1d800500400d0000c0105030340319280c0e00002e110345000050442c43c47d4078840300003030003070b0312801001c54001c00703290740030940c00c101811508001c0441d0600c10048401d103c14540f0901400081410480c0070340f80d21804403580085c0c030b00c3c05202d0b04e0304054556003c58405e43c0810040380c01345401c0720743d4016403074660318040e01c8d203050743c07040703000c0b61055640940100003464400800d9a002d94040c0c001684000f5048618110b216540c81c45004014442d01c0066520311420070180d10451003c5201c61418 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 579785008 1250 579783758 579783761
    0xa05070b0d06050301091703130f060b240405010f021c090f1d060f040f0c0504080705030f0a03030e0f0a1208010e0f01181104090911010518100512070f03 68
    0x2a03000f28042d030f043c110150005022401541c03401139075540ca075510303641c1c0d02407191000180c00d40050140c41d9860740c80d00c144000360300603c4a011050380c24006c010007007002008000300c0300d14404500e4405100510403584144207442c1d40419070304c103c0e42180c00320b81d00c0d100c11000040100d000f080d2480317801c11141e40c1c1d01e00800d009000c03180140680356010205c145024000030613a9105240c0307030852510f150b0b9190311506040703800c45820002c03115280c07405401c40d0301c0b13405508124400d03900002103529000840280d03617101c40700609030641065034143c002d448003050500140c000c0b400f480d40d0b1100104007614000307005160041122040c60f00141c845403068000d0460587c1220070001c0403032a6505003030441d03014030340c1021180e00b0442d0314801003111180c4410402000200061b460307400c0d8010341d0b600350050002c070100c4155a001900c251040360070400d488800a40403407d18a00750500c094245113600f0030078981005100a00c5101c1401c40704c41d40031840d503191010f800c0381d05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 579786258 1250 579785008 579785021
    0x3210d0c02031315030906020a17060d032708030d1416231303060b27070f02100c02010f0507021f0f06030501020703050d0c090e01050603090a05070b0d 67
    0xc1c0055898070400c61940300c400c1031036000e0803482c08081c5204c400f00920035881983c01c180c00c070004640b1000f8802000342110004030088924644443c0845d100c0d28209841d00282030f45034503400210742e0b558a6a40d6210341e88a5100300b0301c400b10000140c8507109000411440b4a120070003d000d0300711819900c004400075150006a000c0884130500090704004540c03414054508010030200f82d40307011402e40d101d140c1240e4090088120008100806604220304030700c422182117004c140c04a24121420419400f240c0c5481c01c0c40c0d000c64402d40c06040c22448041161040d5480032001000c034030142c0700e4020484006039941d415541084910380300d9950800560b2028002c0000074a0310309604170343c0b110315803070000d64503000f60300d61045590100b4001c640c808020340d01d4603004d04020701140c120302c420b4a600c0781004440c280007845811000c09030b5841e007076622482d0342000c0900442c2e0300024950449481144d40b540b010450070400701001f40010945256100c400030040c000b518034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 579787508 1250 579786258 579786281
    0xc060403270303120f021815090a0b030a060b0a0e1804150c0302130306150e0c0703110102130e010510050309030301050d1a07020c1f090504050603210d 67
    0x10000d2203801e0003480c0c80106002c5a070585400981d5050b003240b0900200302c8255602c880501c0051036444000340c447e600440e40700215104032075171020074006001445112a0759600005404044c007a2100c0300004c0e54105510010000e0400d8a900c658003940d40408000004641c803640f916040b444c02416201e01641c290400d5690780c00d043d6a12010100300585550f40c00b910b50410007122807207030741911035080c0244c00c2c001c13480ba82d0382042c0004200b03011000101165051011500c0c090110509000702c40d2228424a0902292001c0b40d0b40a03da40d100034465400300501215008500e40b07100160041c00f4a0f4041c9516180c104101c0e03031960b860038001d10405100308401c5d4074000c000d9a045400948050403c489140340c840040621481ba00001d003545c1400e10500c40d50005a45039a0704040e6600c10100d1000418034052074440c0140d02c00140c5101d10501103414244c000741d0700564054207da03e140101823501540c41c1c1181c610f5002c0c10000720b150000f6070054050100e080c0c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 579788758 1250 579787508 579787547
    0x30c060c021b040507020f0312041419060f020417070e0106030c08180a0203070810050109142403030c01360f021305070e040b0a0602030a08040809060c060403 70
    0x103a03010280796941e1412181c0b81c42580da820000305c41c14000e1081d100080d602401713a9960761070107601004205000d0700d0542d07280c12075134a005d828840c0082c00444d00c1e1403510980d01d10210980d03400c8058000740e00706580c0d454081c0000110380c0c00440070040d01001e0000039058041c14110584540c101c1640090304060808a88804007070f00455019000300301e88441c0c01c5c02640e048a01403034000040002501031082c9d200c0000c3c400804100c0280d1181d00c28028006640c0e9091030600b6244c2d13110342500c0300324480c8040344c452180d0f00100b04811401e441001510614800080e0654003c1c3d81c6040259440300c1400e030750302d010b10110105240441c1e00e115400c00d282c84800078410145a0010004948910f00900355910240d00680340035a5020500c45443c1c8503000905241e50741c041c03e800b03603080041900c0703a41341100001003641c0c420b034000c504090b02e05400302c5d101e840251040d01c0c0310000300501c007611b841c0e150040510b0303c50180181a142014a00108040c4107942c8500030030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 579790008 1250 579788758 579788773
    0x19120903031a22050c040b03190e0c01050a03150801180c171c020f06040c03110114030a0b010c06060306060e011a07021215010e071d0310020f0c0109030c060c02 71
    0x804088800c05039071010341c0000d00307545c4603080d10005108035000200913040100802820080c851aa0418801c074400184150a800e07502c441d5100302010015010030414000f044821784070764800da100b0088111b02200c2c86030b031340c0b0000b400c44c2e80c0400001c8a0b00129031590040c070101901d004002d040745060140304c4030051203140c0d15000c4254000b0020500e031112903850a100b0008c545e101824401600d000c0d0a0500c3c01030049100c030700c401c465108946450858541c040c0103900a01d03140d941d1010318550710544000005c01e01d690741141803084034000031011691030b20a410185124800000e079a0f420040c0103168420140c0c0164103070420400429412500d000c19200c1041d8107031003442e012581001c455040508400c0441d05880e1213000005003207070b403101414014a60303a15a803150081011481011241a00b895905980405603040d4031a40b5035000700440a60103002da820a80309a502c142590350440701640003a15100b00300c020700000388250783c4400071030300052051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 579791258 1250 579790008 579790039
    0x20118151406030a1b0e0108070501030c030507170910020f03070306050604030c0b18040c02060711031201050d051203090307110f0d0b0615040e04050c0a060519120903031a 76
    0x10780b03204041c002c2c80881c150803100c2d04004540c005c903000d842c0c0088100055a10fa0b00c0e2207603160020320420340000d04100010341c04038024400e10707005280a83c0c900101003103051000340100f03c06010045680314080880e6030a0780d4078400f501d041c50341071007050f560f801c29040040a866441d044144215400c02c0104005000c1148520855075940c8009407244810151100d084001d2104a03420906100c02804565130100e0154440d47c10390f25072000f040755a086c00c41d640c4c001d100141500e01c0401d40180300320f2810240080b02544114210340110403845d244489a0b0010b0300c43c3c40340e5a10200d00181001781040c08c82400c40300640b850092211100009200311264410180941110780c010a42a40741d9640042601894018071561650760f100a0900c100c41110240d82c0e90003910018107031840c028080404440b213554070b15081c201c01d6402401c3c90f803884c0c2c0c0c240c014004000501d000803413103805085201d5019840014569001c90300340d929149008a40e41d00c00c0d080182802103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 579792508 1250 579791258 579791263
    0x80601020a0b10090e031e1327090b0412050307050f070f1b1703040302090610052203122109020103022a0f0f0a1202011815140603 58
    0x30b038200c0d2480d486501c415100142c0b051003504410302050a200452412060004c010078901042500192401804a02004131801003107040f2a110300d07411410405e2000c0008c00c08039008000b040b61a030445c01032001d0007202c21f003101c01c481d400061002c01051150100c03050b0200380050500b98910b01d40074000a002d40b140c1881001710b800042080c105200d14180c041d800e442d0300c10201510303c0a401803510016407580f25841c0048a6400c5000320b000021003550103c1e5806400ca0004d9100c4008002498002514040400c04280700b604104201c400040b460014100301c812966821414284140204120342c1414011041180c501085008103c030000c02107071440020f031a40c141c40100d0203841803403110103d001768110185561104940c0089a110940c0102e648503490100055220315162280c440c480d044003e8810100d12561501401210786100000f40400b042d0b80f200502c0a12000554000e01010b024815030a802d12400d10791a0010808111610300800082c0d13 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 579793758 1250 579792508 579792523
    0x2030c0d0c050a150203580b100507021507061a0102010207020d0201080a060801020c01020c07060c03050708030604060302041409010b01030911120102040e16080a05040f140c06071b0608060102 85
    0x2240d04410401e50144640004029040034558040c200e0904130200c0411855800c01f401d404101420100c600d01e0703038480d1003220b0500e00d000d40780c602085052001512030b6004001c040e60000014201d070b14441d03901c03c1c014503d003485030000149081d40c1e850403000800141c041d00b4150f80c8104070000151f680c0c5c0303c0282c0d02c0c1e58246070030651035032040000d6000d043d8541c4018140e42c000702c0d140b04988819000362582500b21030031288401d41c0c0b10011141d201c1c85a2000e07000c1601007180b000031480400003180c1c8050003610200c1d00303650b00c4d40418112215249021140140e502c00d2152a140038043d9290700c1209107014415610300341c8801000002c0e80c0001c610a070401210002c0b804029010b8034001c080001c0c43c02440d1501c85e84030102d0001010f40e850016032100002070071240380b481060f0050f5040300300e00500c261a41c0d50f074a0300c0540c0d0b84049105e88201c580d0360720300d5601c03000100a2188aa40340110701c0e8a009107524440c0000d80100c0180306810081010b039036400039034074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 579795008 1250 579793758 579793777
    0x203060a0b011206060c1416060e0103090b0103050d031d07121523100f03080702030f010510031a070e0d061b050c060f15060702030c0d0c050a150203 66
    0x9251640c0c0740059901d0b100760464200400e08160b00002c2c055044144644c5072401104508000803042007850340b660740c088030890301101041001d2000500c902c080f00b0a005060400044000c0310381c0710110341010990007211513510020420300e80a40c50b004040c403106050b011945600700e100713041350304c80b03140b4004c218042c00040e0a0006000006802c001d50340e00b11042000707500c202e01d941d1042e108003035840b581510b107107401003080754155001601c221040400c102003213038115900c00615601413001a039051060009100031942c0c20f1258030700400300d00d01034010441c40c51034940c00e0034920b15804950010200100540560003a01104103150100c0354010030f0b60083c91b082c00282020303c844914400c20360500400c242d0010014601d4100c20700072201295596030803d0300313803003040301c0902004040d54070303482c9642010805400c8152000b000d1b1a034032410b02010078455481000e023503030001004e034400c0103581001141600505042a00ac00261a034450040e58a01c5000203a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 579796258 1250 579795008 579795011
    0x7240906051804111603110304030c210c060905041802180c0f0316080a05060d020111070b030408041502071a0901141c11040609030b0601020c1201140f01030203060a 73
    0x51402a82e81c4d901024040e00d250701c50588030003c00c074031140c0920701c00384224082400c903a40640501e000005a030f00300c0e5409500120000c0c28891000a0109245040c254049110340b01100145200701c1d224003410456a4a490039840c1404010a64282c82c3e10a90708043e104102c0c3c0250b01c0308403c01c60f410400c900c00350742ea600c0f00e007400c40c5640301d18943c00b44001400f00600c12560358040c8110301129840d668480503803500170002c0b04441c0c064840f1035115004010300c00065014248001c10b8500701e80036102040c2da95041da42c6154022501191610000a8140320664011710041055012032008104a0b41010120049401c03980b40c4848029000b29a0561982c81078210f6402d1044060225417161005104400c1440c12101203c078114100804249040c031880d0a4800316844d5540324078556203544c0300d0861901c0003504160440c0100031400b0350303540390003940a82909078130000081d00c607061210360325a91070103040300802e03450104c010800350390000f80b255040136015a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 579797508 1250 579796258 579796297
    0x240703022a01121802010c020a0f0e010519051309020a051c0c05150904230112140c130209010e0a091e02070317100302030724090605 59
    0x202a440d0016040c0d41418050400340490080c1ea0140550541c0900c20389580c003400c2511880a416242c05036942682c0c22403418a180241d031090f0640805140003414648441d80c43c0c4003194400340c404c0e00540c00b20312a000040100313040c45c94000311720351401c000780b624030382c20075000509004018041e01421526004202c040d50740e0900b80600825005054500042c2c0b1021014007486179000c040d1003120010500090b00e08240507095450050b5103181e42c5420407440030000140704031403c200303110400c0311703c00e000031441013071440c082c11220003451940902e0345040f4980c0c45c0c4110070380c0200e40159403a11a1516a400405690555a2800b58a07000d000b001203908040c908841540031102c58000100030172103a00075400d004540c51003001c0c000f80e039a1010300741d22400c100240060000265512480e9580c1d40b1a908040521808010b80c2d5a940000e8505912608040000300401c480d0700c0d900c40c0500741d40b007220151800c013100d03010705d40305002d0158041e2000f00c11121400c401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 579798758 1250 579797508 579797513
    0x1e0b0f0408041503060302010f09180e12031509070f02030a0c03030e07030c1706060906040506060412080909180a06050711070915290f070f05010902030c2407 70
    0x10582c1c0281c11840101e0668400300c810040c0945107a1000fa800b050220110156580c0b250941c071056441200c40c1d80d061500e00e2403030320020301d0721802c82917150081040c11103245003481d00460003021000d99071061802c0507001c100078030303d0240c480030a0000c3e00d06030001158010058411308490f50400b000c1140007410150043d000d07281790852503003d40d0340302004005000201e10151a644070700c0003c0e1400f280d04240c0d403200151803165210b4203080004940c1e1405420180d44413401521940c24561360714920412415039010460310100b005c5070342203140c10041e4131182d0010642014091000c1c83c00703419501d4042c01c4a0103000f803601e07000001d46440c01881124900d20054003280ca4080d550304061000b0207103003414400d00c00b0840c00000d0001024010030a20b200003402c1e1000500c4403045403080c1764000c4070091a03580050040d0f10216084007012054140a00004076280c2503520401d800c064400b03614501c41d02d0100c0030b4440080c010810340b400c0ca2441c078280e0b40e40c2c642030b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 579800008 1250 579798758 579798773
    0x20a08070c05030609060901050c0c1906090b0a02030a0b0a0e0406090309050d0c0801060e0106091502010914060901060b030c0a08090c04020c071509030b0c09010c1b031e0b0f04 78
    0x2d41000d80c02d0311444003070103245540050a5440f40811800070001c944846004042c50b00c108880120a5440190641d8038007105259612289100340000a5031011654581e51050710840d5900c0b01c096000c020410324034074a00510751480011100050554100b559220010201400180c080340c1d5a58418041500840c0000c0c0608001422140001800c0c941420701610b50f0042c4004c55090683c00201c80c01e004c42c40c3ca050740c86544900460314103003030150791104c000e2081c140456403034441031404507103842e00d0220300c9003a41c00034290360301c3c1044000d400d69100b0351151010403010410054042d5814081e90492a090329100700c490311410314041c500000210303050b9000d840005c01107102007000031948221405041b030180760840c0c498065a11003590311000e040d40b61a1000140c642d0060f070020104207005040001c1c158815443c0c004c4020403092024441114462060050254400714850041041804030342c0b0600d155aa04514140280081c0c4a0a032610041010003e00c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 579801258 1250 579800008 579800033
    0x60f0e0102030c0a090f0b0f0c070918050c0a0b031f15050c15190f15060e240a08190c090608060118050f0609130b1c03020a0807 57
    0x1490000d540340e06120034401503e500101368180480c0000782c000440c1014549100d0888640d007980e2810403110900b850b8044d4002e8946c100103004940e004a5050068450360002c0506403281881c01ca4003460001e141070700905000b44155102c83c0100107102002c002c890b400000c4480f600038030700bd88842d021081c48180c000000380360304501c51039045607015010b4040e2065a50850f5a440e440c1d07030a14030f203c2c1f0f00b0380d00159450b081c05010340c03c00d03031180c006140f40c0007a1540020703480c9011042d08040c407001d070400400290203103955601d13450003843d914031500244180f07108400f10350038001c50500c5524030311400d0204903000201e500e110350121000d038407108603060041e103d80440040c212400d5001340d40c0411396840200b96254820750202c00c0c0801d02c20002c4224074202020400781d451803402c0d81d0742c403203c100310b081001d0721141040300007642c11010200f00344038020200244400c18440e00c0c175200140307250314004254000707041001d85410041690f80d94101d810408044c044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 579802508 1250 579801258 579801281
    0x61206080111280e0d1415090106061103041e0308040308040f0e060306150a181a18010603050417030103120206060901060917070f0e0103050708031204060f 69
    0xc1c00440b01028250240203205101c9090b80801a580039420320b20300483c1c51008181c001454010349041505010a000915078050080c2528024500301842d14003514840c894005009520501851080034010400604002c2c2000400b0061484502d9640e00580c401c0c0403100701c0c0722051500c3d40030f400421401454003e1080c030740c0c135074990812090035070241c400d0741c04000d40f0a40001c2c0c29041680014014035004000c0c00403601e4507210710901002c0c00e08656032102d00080001749607020800125002c00502c5400b25208030b00303d100b608a040c10004c20f0303002c0c0c00381f4100710405031401d82444d07056590380c5c20005040c0d151800c0100c117941315507000a0070040000008021320a0f03035048001090515800c403000366603041c041c40400380c000c0c03050300003041c810b00040c400d00c03406103600003120304200100d4450b181e07034a030400c85501080e401030143e0423800c0018030521005111103005001d00c40001e51078602540c0006082d0704008002414060340e4044134a641003654200c1c011020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 579803758 1250 579802508 579802511
    0x1321021e0604061d04050403050d0b03120d0c0219080a1b080d05060906010c0c09021602040516110a0c050d0305090a0602031305030a020303031b0403051516020102090a0612060801 79
    0x50303c900c005048200782c004081e8441a500880d4070307162a00b400f03aa0b1040c0c2e4580e07503076414941401821406400803202440e030600441d0903480c0e204441c1c4016010406210780d021424440340000070741803280201508580031140807032180802c0342d46d002c41c0e900908520300b100d00820784c00d1140303c2403200c00000501ca8940052814148102504000e000b00012120441c0a0b2038403030054490500c241c000800d11a41c480040050754a240d025003582c1c18a890746502d640941d90002c1c041790b000301c80f40c10900012801408686600c410300d20703000060000100022411030315403481800c168404c1600c6009410701c00410544604295101040050610301007d901c070301000e0348a8000e6121003030f04522610000905140000706803200c0f5130090099803a50700d820514610071400092049a221000c01c40000094400c0080d80f42c1280e01662012480c00d085d04601d11031300b2440984021a030040c08565030503680c91070b09604030350140c01d0150446030304d010000c01500d40c1e54411039055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 579805008 1250 579803758 579803767
    0x80f0a031112160c050d02030d03020a0201090c09020a03050c0a1d0a05130e0d0203070803130804050d05030a12060602150405120d1b09060909020c12040b1321021e06 73
    0x40058644500303d1a120710f40301281107407501c2c203200151054240103035047d8003a0030741805171800390740101000c604510010988501649961000c2007641c1d10400d00942c0c0043c02d43d100329030501c2001d400c0001c4524040c81c002014900070090144e8181c140014080b140304081295103880c801c40c010207006d400669101c02c00d0800c100140240300704158140540d00b03010b12124404003c0f5440304c0ea21240c6a0f0440e2a40c0c0c010309480901d03401d0450340e0b0701c410000410240d984080c0715000c1c41c8110002d550350314418100902c2e07404801200941e903402c2210074400541c003c0345040d0041c1c010300420800e5940c43c03d040b40f4000d1405608a54500300003803125404800d50040c0c03904070080d51080040c0003010804a820204a21031071000850450f4117025000281c0c0041002d07001c81d1041300d0403444415034600059119078048403200300d00007401511040035211220003008100f00304580c130040100460054420482e0003407150342c1141e0307203a510068804040503443c90190580740c50303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 579806258 1250 579805008 579805027
    0x6080f06030a170d060503060105031b040209150307090b03040f020d03030f0507090e0c041d0411040f02090405060301050c0406030e07120c06021203090c102c0a080f0a031112 77
    0x1a6130085089045150401e140800d4505001035014100c4001500402419042c100c40f802c404540030155584030390200100c1100d603030f40105100c07400d5841c284480d03890030200c00c0540304050790343c005649020140100800300749035140c2c0c1c00200b038045e100662400e6203454210010000c011259122a00e041c0a1009456208000c80c0a6a200400102603522407501d011068040c81c0305000400268044c080504102402250307003082c401e180700894030308440001829258041c0701000d0150f40032803040100d140074058141c01c1003054000304007609000f8003d1880388030b5809644d041c5070b190390041214090422054009000e084030070021903010340382c20215094140308d07810041c895030901c000c629101034112401640d446005181c0101c04400340101408041e84200910401e6808580840d010098910720000000e0345600007400d0b400c10040004500c0d0042015948050190070844000003441c0c02c08682500b4606860443c000300035150401020030b0958210300421003920 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 579807508 1250 579806258 579806303
    0x102011e02030910091e031205010303080f010b1608090621070305070503241201051602070b04030f0204020904090212010e01140c0306100e060a02100c0906080f06030a 74
    0x3800110044c2d40314000d0920000050700e00d0700f903010f86003200321004101c03204502c41c2c0b81003003144a410a0011070130303200b0024080750002da1007130700842e038880100300f880315000440a000d000c01024203402c02d02c1c507848406030741e14000c170300404003903001a401446940314001d03580f02e401a5030b044007843e09050b40c4400d007008107a801c48042801d18011810480c0104156485000300e404070ba0035440008000300c1c00c60b1900c8005540000d521235814000c640b0a025082c03282074171007585207151509500081ca01100b9604c402d400e41002e02042c00000d400c040b003642030a804940260301c604040001400074400100000c0d4499405c461800e00150107405c88950030244030020014001401803130cc0900034212030a0190074020400207545240020040d2000b11003480c0c031003400b0f814000410b034158012249840582e1115070101e00021850080551510f540e25000c0d0b042481d1140140c0250009084c110b810500c2e10000f840c90303113040210524440c0c100c0b4070b0381824020a0f2076a031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 579808758 1250 579807508 579807511
    0x9050312120127020a0e0d11010e1f0302071509050703060e0c01080708151c0c0f0605091c0b040c0302090a060b030703151e17071a090102011e0203 65
    0x101d400c1801d0000800c00740d6041e0519401c440c400c9010891006a86500000e41c0060310143c1800041d1041d07070083d445510b0080501d0744542c00c88411524090005044403100003c003031b1055842c201d58500c40c100c50103a14180b40c045040c0980c440d00325280001c00c150901e95180b122038034104402d4140140004d840007124001c040402071101e880c0d2a043c1c540d032044e2035050100744a0350200314030310310035420360340e010841499448000c000000056010b12205c0e10f41010381c010701054105021050000f40e000301008548403040d02e2030800702801e07a01810382014860041c403d0507010201c01514203062143d4402c0020000c3d15045c54030225054181c08281d0041080c0c82c00654400714a2181c4015942654a0b10b8110756400302c04070090200d01c5103903080c00350750860008040c032200408083c3d00e541d40555107000c07820840303001040888070304202c00640c00041c04114100180f80140c04d0b401500790b1040d600e4104100507405090480c902c644480c40c29026002194807960165 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 579810008 1250 579808758 579808777
    0x18081e0c0f03132907030315030602031501082203020a0506010603050a0e0a0f29040602030627040803150316050127090c09081006050301180803150109050312 70
    0x10f01e40d5580b10b00394800e8440041220341009a11803050703050101c4500082d01c1c2d514820f03d804100f811002800310000201540101e85031034001c0144081c6090706c00150b085400b003840d120039507180c4402c0424400c2c4d643c840c05506503d91108c4481494800c1c03008940298025048a0246d40d403030300010300904c0120f5040c142d0a25040405100d8103003c81d551201c250004200d0700ea14885403209000e00e0745420015612a0040b0b602c05c80c0d400310b0255051145002e0380b40185c17030313280040a0010b140b00d030295540c2800071406000480040702c0e103035141c0140d000036040d500ca5540c03265000b8454105901c2c2c5502d842000c0d101c41022254101204c20785074280d030762124a201c841400707042000725210041d6425a070200a000d10610390340540e600450031b190100e000c41c0d882d486141000d522403441c5001e10340b03070300c01805a03003006d0007014030708a00c03156110700f200281d45500b0320900000d46585403452131803034030344084da01c02c020b040080e107070003015075080301904003004502d0761100b03421 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 579811258 1250 579810008 579810037
    0x3050601083a030f0e060f090106030215070f020414041209150c02060405090106081029070c080f0a05250b161a06010318081e0c0f03 59
    0x103442c0484a440d4880400e10720821521030541c0c15190032403244510020345504060340c0d00907000c1342000c01d002d000e5203508003501030301d114101500da515659000401c01c8601da810154100010f80b6491681c0340915180d8429940783c11083c601017480c1d881200020b5441424500d00d01026650108614015032003202000039259114506440340740d801d01c501910452000c1918200074000e4002c410850700c018415881c0c0340d00c60780042e002c01020707084180050034282c02c2003401210f40085102920000303d807800111591403900308080e21280400011a201040c01e000f004070441410b00a4207201c07090354165a0350b024025526584c0480c192814898030000400403010004041010300e501d05d004280f2a0a0002102d500e600c050100d112071141d00c4500004200040c1100d445c0c0c90300c0748250602810710780001020748500c0003031030300740b07007000c840c0c801c002a01c00302100d81d48601504241c0180e007200e08074256500403000b442c40300d4084c40d88240302030900800203000d074107102400d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 579812508 1250 579811258 579811273
    0x3010f141e1507081612110c0409050c130c0914030604081b0a0501060504140f01170c120616020a030f0e210f010b01030908090f030a0206040305060108 67
    0x1007212421140c04100704540081240c0012818088150b040c0514840c0a982c6007110310ba44019040c1c1c0710144604d2002c8003030741d819081100c035848400c900f200034a000c5001141d940300c080e444520201c8076602c1190b481e504d44e802c0040c07d0104030300a0b000103100c26480982c080d42e44028012a107118000220784803004200d0000c00920301d032050a029009001980e501ea89120703980e0301956052003151040314070000003c3e8100070805059210324008642d90b450502840143c1f602e100e90311a041c001042040b625801c1c40314030074115002510786556854a060401e800d01d43c840d01c040f5000041101c1c1c2d01802e08000886900a0004c2004400100e0b0040d00c204c0e228000084020700103000c6201c814195441038aa0000b103e9000303001d00301e4160500020140c0c0345003540c81007420340240300703c0b9000010a10541040784001c0c2420301209115586981140c45985030840c800c800e44480b0084a0300e08214451101d5800b404c51580c5a440342080760351084248103400140c4111403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 579813758 1250 579812508 579812549
    0x50103030e10080f100509040507050301051605070201120605150405120a020102030d0b04060b0409090309060f0509040915090c080c030c10030e0a050105190608070605120a0204030803010f 83
    0x5940c410701e00550f07516828661500c100d910001140506050400e001c1c000c0c01042c603988070107086015502c140c1c0180790513031500d0141030944000038a000c144c041c0700045a041d0907008012124a55824a03149010080301444c0c4001000f240e00000d4101203030601c0c0060010401c8010003e481c022690781e082514000141540c41e800050001d0060b0002d1060502c50002c581180c180c681004002042d070fa504c03880761039803a401a500c94060251121043c10034503400c41d0043d8041d00c02c601d400d44c1d01c0e00c014080076000b84503981d5001c3c06a6501c0000005000f0302c41e2540220f1458048284400c498600780410a0510380c001d02c4650b021f07281c901d040701d10300002c650310203003009020f0982c2c040d010a002c4c3d0080502105200250061004031700000310b0031f01c540b61059044e43c034114601400350041008440040d004003a6580c805882880260381010a41d1031008140400100e10b40c0d44508000180c0203a600c020903581c400b00021801071500f94071001030700c00c1180c4060340d110004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 579815008 1250 579813758 579813769
    0x20d030e0607021e071206091b050f01050a021903051c061202540402060403060e07031202030a26060f04092f03070f050f0f040f050103030e 62
    0x10340e200c1000d40e0041151186440703a200d007000c1130714050010b4075850b03a61140300300c1800141007130031200b0079036405a01040240401c104c400d0752000c02c84190b031440c00c200204405440915540c4e0500c00042038860b1058800c03ca110b100f046480301094031608603241c094041c0c0c102800300390700c1c0d07001110b525010b80f00c18440e140440b848010b81c0c0715000c5d015020720402c115242e40008100c1c9141d02d60001d00145501030740309480b81d403860510004680d00c2e134105000880032414141c0f0f0001001e2101680e0707014103503001c0c1d0381c00c1000042c8404043d51102d00d8050b042d40020420392281641007051900880940816001d5031912004461048907055203004061120446544007401041181c20011a610a80c1c03c0141c400a18440c06888229078071056861071344200d4952030b0342e148104a000e51380c41080c24150000c05078a0706000089c1c091208a004a90040c1c1c05030060500c5540c64008640c1c034541d0280040040400150410b805040240000e030046040c4440c1c518560400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 579816258 1250 579815008 579815011
    0x106030c03060c02030c1b0d1b050a05010e010507080c01060503060403050703020607031b0e0402040f0f03110d030210090809060403050303100510140f04051009030506060301051509071707020d030e06 88
    0x1c0c0d030050018a88041d9071f4405140c0034a04485d00b000b4003180150004c0c3d801045141502e15002c11140090329007010040303401c1050700858104442d074041000580d801000750313a40b059004104030345030300104041038010300403941300a515203d103030140800d041d0804004d000702d501075400e99001c1d5503003d6068065503403030b000c054848249465000c0000c0d1190f9521100454010030143c070345070b40c0b4540b4003504070f0300741c20070300c034204102404204004580d9a02402c01c88240e0b510040703c1d00d03d40700603441d00c409100060340c45840d0114030080100c44400c8890007139000744030a4031036440c2e0420301d6580d00100c0c2c2a01d038412102c000464a4a00710341002c44042c00355172102c80328644000b082d0400d80100b4441d0401d0881400007050310740d180b13989032a05644668460001920714101340d0719010002e4401c80c02a49848240015082034a101c4e40032132409480d400600d4441510454a040f207402650f20080383e004140400c00da40890410074090246e5000d1090000024000c0e458810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 579817508 1250 579816258 579816277
    0xf0b180106120305070f0c08011a0f040903141303080304031e09052d13090b1807090b01020a0b090d0212180d030203190309140a0506070302030c0405030106030c03060c0203 76
    0x1300b03011880000300303412194005184901a003200c642e82d150009402c0d5000314000200c80d896101d540310942c101300005140b0402c0c01c440c02d201241c100e4502826a41018015910785a0700040c2c50120a1010a00700011a801075401e9528a00350500610b4002c1a14100040d506009403c0541e06e00c65082113090b2203008117500500420b810308504d965104804455030041d06d08455170250f50f5410400d0f03d80102c100303003c58400341071302c1d10107140b4400400d40d500114044000341702070f14000400700261005038100280c03002d0302d81e0040c4e1511525040c0107140a03107150800038162401702d4420390368a040d400f1905d00050102c10304803140905a14031030b803117511007102c0c020340c40c2400c0c120720441d0103401620303e030000c020706003080040036041040100743c50313101c440c0420140c1b030401c0c162a0185000350101c1103d5654040d120a40a4103002c101600407000c17980061428049174010a00240200040c664911f01801c140090344010750709540b0700344400741d6450020040384d803c0c2d030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 579818758 1250 579817508 579817517
    0x10501020d0f0e0d020909010203011a030c040303032c0a050601090e0a1b080a050304060801090e1005070311070317060a05100c03021002040b0c10020c030f070f0b1801061203 77
    0x100da07598115010b2003c0071041d90b02c01514408000580c03203084615000d84a0540007503034179818100810040c1030b108003c2c000c0c0c10001c1041100f440c4083c0183c80c19030b545032401242c0c051004060300d80145448120317680c9540308074054204240d000803021901c9104009a50880ea6074501803030454520300b10580e510780003007140000041d51440400041c20071205580d44541c2c6039a01580343c291b0070041229076030300000d0240b00700307034200180c24018240c0310420321001c0461030700d09465907400001001181d85070380104000c1802a000b900c14082034261607030712600d650600902c407001c03841160b1076203403442e00810034508006a001c0207641024202003085032483c04106d4421055100550440c010004050111406800148002e05100c80c6880c3c94030036180d421810030070a022400001c0e4410002d4040d0702c80b002c0300b91b619628580580310340700c10703440c00c3c07002d900074003100700a0407400e19908100c0102c120030b0003411101c082c040208405500c4d90003050310105034000250119 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 579820008 1250 579818758 579818777
    0x3060509060a12170705030403051b060706020c07032009130203032709040b0601080702010603050d0513170102030f09061905130210080603150c0d1113060512010501020d 75
    0xa0b1610400c03a40f1161041c410350444080d401207100d0030703401207441198550000a810001e100e07040002c401c41c0c2d50710010010150a12100050881c81058002000c083e008101580c00300c00c01c0c080074005681105403100c10851080c00c5034440d001e656403061007012008041000030b41c812488080782a40030780290302d44440d0920441c68664a82d08451921036030ba2117901c520780340ca01c000342c043c510a030000d040c03d060400000d04108801407403002160316090041002c0345001400304501400741c00c190341d4640484030003486450b1310341c206a0f00031359020080c50812070150300561065040d001103c0341e41c4c4840e424983c54107800c0d60305440e12242e0080400b440401944140d1300800e0502c0c030780d05508038907800300d501110050a05004510400b0400a990130103106800503208294030800080c41c0c03194244005000381e0705a00320302581e401c0120460f10f0b514084600490900c505080d8041c1d41c0c0d00010007a6002140c030710340d001d00c100c0c0009483d50001524811803c031544030344030302 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 579821258 1250 579820008 579820019
    0x90c0603190204080109060f020307020601051909050103080c160303090b0319050403020d02061005090c090301020f03090a0309120b19020f0409021902070806041412030903070303060509060a 84
    0x140c0d00080d001020a5408820800c8004054402440108589800441d4113902e07801c2104c2150205070b528813519004004001901d940465a03e0542d54102d4100001d107014648005002d00c454000c03404261405001006100a5501070704a26400508a40c0700359200010f00ca40b84459200003004145d0300c80050048a2810000e160711507149c0c070400039549503441801c000c0c0c91007590203801682041c0048651140d0501000e54810425032010030180e01d402c0200e440c65200038031908480310080b4a0003800c4c0d5088d011a04000d50b2032130503d85904210352050b4643c20500003c030040b0380fa8803030019504403040300400030030b40c101c0300c442380700d65444401c00c00b800e900d200d120b428250308104071400c2c54942c80c0500702402120400588982c0c500d4a038002852842d0a100c0035541b1a030400c2046000015256501c00e5100095081d40044200d10500d001004103c02c141c60a0100800c0b503510000409442000c0c025078082c4045a038070424007103c00d805a620980000d0541c0f4103003c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 579822508 1250 579821258 579821269
    0x1d06190e0f04020f0c01060501090b0f0715060e070807090f09050a0b0a0801020405280521010911030d030b01080705130807090203010519210615030b090114090c 71
    0x940c10181035a4201039188002604a9020074482c42461002040048548000344110300107041c0a003440d500e12420001000481d004490110a41c18000103004003004007100001d03061a0068109200050300c440f18428010021520381000a0100c00000c030041e214404841c12101c007640040545414401181d01426005101001c260b8440140d81410340b07a070200400100798100005031141c0c1801d0400c02d80400f02c0304483c0c250200700d03d04c040380c291800c10100807501c08403080918020b240d610145400b04402a0b22000d529100200d401c0c080d0241500c145c3e500700710305544c004440c180b1305034101c1c2da100e03101d07a0015822100045082c0c0c01070004042d5482c5140c910400581c2c2c1d1404241342c40e16682000c1c01054001c0010011810140c11100124020031100844a4100054020310001100003802c40c80d009880b4030b01885650f074465524048520705400d08292642481801e0754801d58018196628014940c03929490a40d0030500600014014180c0c00440d10200304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 579823758 1250 579822508 579822527
    0xd031812020307050631120c150207030903031e08010623030114040c050316031a0603040f050c1c150b060a031a1e040911030d1d0619 59
    0x1401e5100401c584000700d0020020a441103911182c41049807142042101d4000404c5107002c01014424444100040e019100380b50661414544180c500c141781c2403409ca1540800003404d0414030000308a010705520800700029240030303490740d034074a444000c0d40151034451204c100000a078444018011507204105800c41110b41c0340b58145013840300d50000f00250b00c2a4010084040c1201030040ba070b0070a0300603946010400e050050951270b00c804011248010001258105580ca6200001081c0e000e0042d050b800d5020f09440d440346803501d00245280024002980c8500c6207802501003854280024044070001d03d00c0034828803140c1c1c2d0ba00b0020342034540e014082c43c0d00e405403445da544648001d40003450703036560042003c07190f03140f001149205030081c036070041e014240001085031303144240b81f81390340c025100002c104029091060003298000040d540c940140d1070750408030f070b501c504401c0d01e13411000d41a810f440302c480c08000c540d100754000403803608118503150100a0007683c0e5075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 579825008 1250 579823758 579823793
    0x30b06010806040b1201061703070302060f04030c20150a1b060e250b090603071b0215040e0906042103090203240f01050321130905090d0318 62
    0x304044010701300049070034000c5044141c050b0741d14002002020014010100503d080a019526068850701c0c02911080d0081200e0040d00c044000704003003501c124004d01d41d85400c108a24944842c00315040440152400180e10030b0300140c0082c10400400030444c2c00c100da00e0340b2010700e0302102c01326800200e03042c03000544000340c0d20114810100f1080c0000c1c86001003400d0104601403290743ea8061021396504142c503c0e1605211801c002d480e4501100d030030031051300713003a21611000c070084c4101d0340d02030704000d4120341408020400c40d9620400b0300241e508440c00604c1560340c9210065603004211400390039088420411a400107100100c018050707054078002c6020b8505401103071401300541c196091010809da103110303001500a13000b40d000806010456a1545014006652540c0f0101ca55030300d15000c02d02004a080c041e000c6880c90384101c01161401c2d59242143c0340181811140c4c1e20f410b020752075a4501280c800d00c1180070405003900c10306000c0c8003039162180e8140b00754141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 579826258 1250 579825008 579825011
    0x50112091b08030c1c170402030f070608061302031902031e01120210020c010f140405150705120a21020d090c0f140303120703150e10060504030b0601080604 69
    0x1121540c1c00303554914080d10401004594075004c096946150110090903001101a0000100041035200e8640440622080b2014503a5161030000a040075403039070000703034140f1130000300264242c0c0040f0305a1041d001101d0b82d282c1410075400c820164401111111401082040c141c0511210b6a015503084403440344641541101d481d1294595202038101d00e40710303440c2d0b81941d0118034010482039002e1042e8800380226403800000a0803941c8001d0004003804030000a15a100740c1c1801906d005210052640452802d0780e000010326900000060f5203d000341075800c0174480114085590582c100d1780d40405920944291445d2018528410b0b04425020400c0321001d035200d0290441c0d06010b100f21b81c00443c508040d600c00031650307922907050a00000710038030725598044280e4502038141013070000c040d950004101c00600311a6040c16081c1d10180c008903166000030320031482155032000c0c9a13546034035410199030074000d52100801600c07110001408c1d9500c1a0920307074100002810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 579827508 1250 579826258 579826283
    0xc05091c080a032c030a08090c040c0e030111032e18140a060513021b07030b0a05060114040603021327061707151b0309081605011209 59
    0x11a07000c81d5010616460010740c82d260042420491020070b103140000d18902c1d080e010b80c1ca0315450351640074030012107003030101d9000092034000f02448800d82d006001071040040044800780a0100310041803524041c0d0710b03204171420b04200d0f1004490240d401c41c010a0080401c510141a018851940003103c410100500040c40071008680080b00054130b50080b80c04203103801e1031000038500a000a94080c01c01c0c6080100ba21400c1c4042d03c0390701c141d000560380c0c403401c803c0b14603803403034035090603141c0c0c400c0800000c1403007039008a01e4013801d505181481183c6400004480340b160ba018528a10082000202320160180d401452092450b0703002035001980c80d84015410419000ca010074030a0036030000e2a0011a44518409407006444041840e418a105259100264010a42c0d20482816140b226038060b509402c032400c0341e80e030f070014000040e00d4010101c1506102d2082039100c0d249080380e1042910700a1010b80300117035a040729159030140c150010300001102510000200d21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 579828758 1250 579827508 579827513
    0x303090c060c020415061b0f0203030a030e06071805061b07150e0a0f1a16030c021005070203100f06080304030503191b020f060c06090105060a090c05091c 68
    0x100000018811525900d8402e0305900500c0207641e41c41e0038003010207040e0170b014400582c1210030591205110004001071441c04e18000e44030803201d43c000b17949403002042c0303000c501d54507800413604004d0b0441030b107920ba105d054054075071140746608681154481141405141401da000d4031110b10350b80c020700d6041c1001c558a50911245030030080d00c1036601e1075a084019040b05100503141c50a8a514034810f203040784000e8041468040d940d10040d40718600085003441e0416103180c80c0a03062001003a6406187c003404034160300d00300301d000e2000150550440c038010780981d80c90f01d4024000c6c2190400000501008155460110124940d0790202041e400c2c001c0024202461003a4001d50f541c042642c1d585101f581850010010810383d801031224840a21900200240e41510b0300c10500c0c0401c00020541d000300c0301800014803550081100543d01500003600a00c0c05403860f00c002d03030b21006000c0c1690401001d1070013042041094266a0401101803120344400c02d10f014140d100e6a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 579830008 1250 579828758 579828773
    0x803072007300b070f0f0806040e0102070b0f040c0f06051204170c10050105060c0a0f02030c150316140a180911031902093111070b091501050904030309 67
    0x320055442d032440ba004c001143c3c1e04464070403240c2c865401c04000f0780c103000800802030b50f40100094050b40d01c1e19045c40303500d0f90940544400b00d62150141090b880e1030b1501c1450448111010791724540c0c21200001ca045140c00080309459165480c85c2ca060b04c0d40e50703101c3c041c007005041244d400c60b1000303201301002c1600380900f454500e00c0e40504200f03401541c1d000151001a008107200c0c1c0020070409100883c0090302030001980701840c41080360700e500003e4284005800100d403c0006030b002c210004001c0070003107116101020081e17001944101d411290f034022000200030740c10003000400680d82c007909a51030301c4901c1c2059010703d5903ca6450405a92001c940b0078003c000200c2800f42a008001351400c0c03010714640d00b1402c260201c00050300112041c00390150034078080000b5201001c10314080c1c98595a120800d0040e40303040044002968040c2c1d905564a400c072001045920002040c01c40d081081c502c1e8840c0b1590901040202c82c400c064401c60902d592101d01d000040d554 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 579831258 1250 579830008 579830099
    0xc08030603161d090d230d0f0603061b0e040b03010e032802031215030316030509040606031b110a151b0804031d1503040803072007 58
    0x440c09050700201900148100080c0151132000a80c10001881c0342165004001002413003418041c481c01e803140c00c155a01c075100f26581d0090503802d05415520301580d58102000b00ca100303000c200030310021840440001e004082c1c080001582c00300084c1058032301500703d10f02c00c91000f40002515010b09400d81d2840d48200c1d5500c1500038a100308441c40401010f00082c0340c0c0f81c500245180503400f4425805070b49005101c2d0188103140b00c01116507840030415210030207420369507143d08400d182006000c54001c14030151160f1b0070f000011420364420300500d18207122a12408010040100741591641c1a0541031925403044401d034a010510030448800320582145002845580c1889040d50041200e00b1050602c2440c209100010350300c0100390108445454410a2801e68000010b141441d43c801c03801c05c0603804400e100500c0044002507000d080e003601d98030002da0b04c00710078001d040e085000b000030395000004204055a00c600314003a0170145444840221014411a808401c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 579832508 1250 579831258 579831269
    0x402010e01020708060126060c0a030518030a0306030c061404030b0a09020901031208010e070f080702210903010606140d0203060402090402030708060102010b01110c01050c030d0e0d1e0c0803060316 87
    0xb085040502c860303101c034190f0307400d211025000c80d2a11489c0c00306107224900205c01007543d9200041d0702c18903418000e01e0682e0100c01a2079540c1d0715640c0c000c01400b110302040e1200a60b050000407018001ca8640c6d26000e00091103c3c10607103140c40d0100d540310004c000e12240d507203440701c2e20010780e82c56444a008e0f512a295200420b00c010700c000f02084016004030b840f889004050003243ca8103c40010211034081c03501151580da216022030910084641ca08400070004d1410703071015072403002034807946c40150003c105c050382da180101d661000c460000f0f070000d1800c21402ca010401074004540c00034000e07002516040b24140032074203c1c0e00460f032010000e02c5210902820790703428099500c0140c030910741103140e10f0100c0242c41d151001d090105051250014001480030403c1c41a511907401a09040041c6030144280c1c94030350f155070645200159060800001c01c41a44c1886455510144e0703c42c80403100f02d540b509801c2c1d1014001e6541842002581d030715251021628030003409 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 579833758 1250 579832508 579832529
    0x1215080d09060909020f16111323010e0c0c0124033c1707060603020a090204030c0b030c0c01050c0a031515140d0e0a20090402010e010207080601 64
    0x303150480080a2103180d4004040440c01001440a11b50303282082d101d18900c0c0003c40f524042c07540c609596090740010b0490f4020052580c1c0840234012903100a00c880b18491004050896011000000030f8090145481c18401400450110442703a00503004034501070000050500d0f01e604150175204002178241503200d1100010700800c4401075172032450502c012899289080b0340c1404062141c2c0e1601202005040801e100c018020201032444580d46200003850360784600b818541e01500741400182d01a41d000c12002440c102c01e8802c850032241c03c00303e030740700090804620f807400b40d0020740341180c0d495060020881a2800f37110361030040d2001c580990381c5199215019041d6090125008011140710720108451690141d980800e05c45030303c0c2148005044001d140c20314000c0c004001d48252809269618924001640c0000d03103001e58078031041d205180c00028450608074160940080c2d601011800550140f804810741c8001401034501d041c0c0c80300700c01498054243d10504170341 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 579835008 1250 579833758 579833777
    0xd030e1612211d0a05040f0507081b030105040b060702030d090f1406120403030905120c0606121518011503060b04180f020604030c060e01120c1215080d 67
    0xc0071420769408032500d030001c0842a00c91031405030810f10b5030811614845010310704414540d403600d001c1c1000d0f00c0c00030410007550b44605940801488112550408501d2000201c0d00c801000c4000d461040c540c112914510b82c03c0070284406850b401110540068080c050380c40103a030240201c408117051a600c0b008010301c0c3c081040616061076001e130403142c0300368140000b180c40f14001c0710064444900e10450907192843c00714000d12030070300c01a08502a0103240f40741180c520000b40508c92140080300d156869420030041c200b10780031070304580355101d41d01d1041d172203020245e680d5110050008400104500c01180b030309446c600f203801c40d003003003030b0360018020440240301d0000040420741e0204a03110401c4040c06080c411074501501c84000b880700c410455484101303c0d0055980050500c2445039604009415a01c190300328601040100415040d0115030348910410380a81390703505407401c0c0800d0207000c000d0454150f00040c040320440041030a520403c03c40659285903615802c56 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 579836258 1250 579835008 579835013
    0x1502190c0506010f0807062003040308121b0d231f17190501060f260604080906160b040503090a06051831060f06020f0d030e1612 57
    0x14160141c100d00101391580c541400b1304000043d135001030710080c0c209900413802e5001d4141804005240c490b8040c070000802104005540c406031140c9200341c1c1c00c040305501e81c40018175a0400985600d1a07102041c060801d01c0001f50b0041c00c07803502e407020720450386040104959102c200c11142020800b00c070360b0483d44400f20342080e50008054601e841c4550069150b82c0c0c54542010100708000c0d034120780b03161030600c0800c0d40800c0c0100100305120420300d599042001080d008605205078500e40050b081c0070068012610703a11481d40030307806034581001c01c0c082118680201072045190600c0c4504c07880010002012705009501032001183c6420000c401c116520685411031020004140403645900586104001ca211000c9801c0d4410802101c110b994410390320351003090703103004401c8109007118150700c85400c1d50300a10050810740d8486900780da460850740c0c103001460340b02400c003a261038840e910240f12a407012040d03403d4070000b01d018411a00c1a90801169400d0b00800c1e1401c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 579837508 1250 579836258 579836263
    0xa0801050618060f21011514010e0d06020f0f040b0c121207080406020d1406031006140d020d0507030602090301050f0f070807050903070b09100315031502190c05 71
    0x96a052101c6985101c0c0f908501064100c03030710404107805900481d959503c0042c5040900f480b40c15031100800449401c903600c200c0c1c0407040c1c4034111030000c0013a5200c40d08e51082c4400252044050182c038090485982d800b4001e510035030005048080c24000842100c44140041008104208010f0b4a91400c44040c0342001c0441012110b0600b0412011002c42c01507519a40e0103a11404c042801d56145d0400c0c038060311441c5000b090700d40ca012254075245500700d5080d4000e10041d41101d40200c12085950304030b50103806295004d0880208504151070b02d1801005c6551015110002d40019a6a603a2612266410803180c0701e0700030419203400c0c00d0910605510584d280340c1c1641909000910070710b4076074080c01100c100f100304e90000314414050340890b40b9007003002d001c43d0b02c5d495551504807125049080c0341417091041500c01d0b05228800d0054107050716503040304012483c036681e10f0400c1c03200261400407400760240040c084c80071200011810b60b00183e21000b00c601d5440c90304170b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 579838758 1250 579837508 579837529
    0x100927020d0905010204031208011508070302070602070f050706030236090915100b0405130e0f070e0f060603371d0109050c120718060f090e1908090a08010506 70
    0x410048018010030a00001055100c405211400c1585198036642c2043b006071181c07840203031100e070000031a101080b4144c64200601130060b130a540040f600c551044090f44901891001d00c1e42c1814481d102e51030800d507407050b00d016070700d041114070340000011440e8082300300d130850308580010f1404480b20384241c0b40d0591220410304481e412034202507922074580142d01a0500410100003c0440c03941ca640c0048a0010128200d900d80b0703445002c4540d5520381c0d4020110101c14120104420034055800c260007540010034590071a5a82d40300122848600490181e85402e10700758441a20703280b8941d40e90010b0300180c0032071000c00d00845c04440001e1031445440c0381e031401040602049011840c22410102124030502e42d02030140c6035403034107402e41c1295210301d400b81c1c0c1c8a0000d1071745d9403015044030000d1944001040da1640604100d0b00030b41d40c4017925804c038a14104a001144100e280c80600c00c5c00d605013002010008600c03000469000003540c1d0b0754030801e003d401c0c5001c40128 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 579840008 1250 579838758 579838793
    0xb10030b03030301061215080303071407050615130218100806011d030a021201050f062b03050c0604050f0616090b130e15100927020d090501020403 65
    0x500c486a05240401c0d600d200500c102c804002501e12170300715480140e0880354100c10345411000c0041e840e991b801da281ea005480400100329071201c004a090b5500054850041d001700147c6503a5550000c40e0b03a070765000b088a00d034042403a01080080000e0351000d841141c1441c001490080c2910b800d0288441045002906021303465040000580e070068661038000c00d0494440200ca03541804030b0719007150030500941c0194182d00e80d0100080540c450b82c401d2101340d54515031500e66506101c00040d441c458070b0f4a098401003181c0200700c14400301400c1038468505a80703000f10211005003045800d071021140d58001ca40c4429085004005490f00419542524900000f2144024103c00c51510034581c21103000300350030340740d8814114258024445d8107494850b6140080042c5200892081540d110780141c0d40e41343d03684e6100702d00320015161180788242501c2c005c00c24100044c0ba40d9400009056000c02841000ca641c0d030050209082c4078800268480781945410300d4000b0b880100c0c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 579841258 1250 579840008 579840011
    0x340303090c05041416030e0703030201090c1403030f0c0703060504080703030c030e0d0c0206040f1701050c0304020906060c1c0908120f0f0c0a170a0f031506030b060702030a060b1003 80
    0x3c1c060030036001d04072076170403c40307120901000c0c82608006902500d0051040201801660000414980c040d0050f214961042c0c140c0e036100ea8488034644005041c00c07440c0c42d0180d1080c02094522404d040081c1260109401220840da96075555641550320843d0105c51944000c51600205609805040c030032500f10306003449500000c00107995909200107610003080b81c1181c1d80d00a40d141e03101110082c0c080010030507003013a11101503481103848176002a940e07603e04000200c01c0300b00d00007030702e002c0c81d8014070002c01600e404081125540100c100c1c2462400359191219103032105070340d03400e41256580c86c2c01701c4640c43d00e10308a0909404400c4c20035070160410030404c1845441045461208024042d16126803440c5000382c5000c0000100030074041101c506c03c0020079100c006819807215036035841c40814148281141a500c403816032660460112a05000080c02070700301e101d4001c009014a801d0608a4000918002c0c02400c01c0c0c40c50341d40c80d40c801125007081404e4201e031103610f040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 579842508 1250 579841258 579841271
    0x30e0c0306150f1201020d050601021b180c0d0501230307050603040f0507122105070b0a1e150303090b1603080c0f070b060f0a0308340303090c0504 65
    0x44900700c4410500c0b6903200e03082081054078265607100907a40c24444840013151a6a040c1c15950000c0c44c094030402d000d80306107091070015803080c000518587c00d02401a0003603150000030845031460203801480c10303e00030311622811a42d24401c95000380f00c4524402d40c8902e2005540300803040d0700740001c1c0660042107051141c1d80784c0e1001c40c2d404c0395015401c0100c102d0305081550400101b608800a041d141c1e00d00c010510a0344180e401060f0024403444025840e5404151001e2240340da00030160100c0d20b0008009503020344c4140001c6003581d925113a18003441c03000d5001c841d01038041c0b80403035141001c00e205055004010b45c0142908e1520729240074040001104003140402c8010b08100d002d400046010300000d0a403802500541e01c0303141c954040c1c0c9402c1111400441e49c00b8001d28490030079141610f0424000000c42e900500d400d1701e84200c442041c82c2895100700082e80021b4550b00c0d803603000c111034003011003d074000e64000400b2a82032800120104480d803255100c0c40c100300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 579843758 1250 579842508 579842521
    0x60323060103020d02010507170306090f01080c121014010906060c08180301090c06020a0b0702070609060e0402130f0311101220040801020429030601180306060303030e0c0306 77
    0x603038a810b6a4040f00c1c00b0740b50b6011880129071600c6050002000d000c11400c007030580c4038010002d5405903030211405525030b601c106040b501900248288030055100e00c0e60b81d1024184003080714010020481604c24410345402c030502502d0030488050380e81100301c0010040344210f44150000740c03404c2c2ca05240c801829454500300d07401030b041c402c4801d00412116101e1950258080b8441d50307400a454581e080da034000194640041c0740e81030380c00c2860500001e000c1d42c808a00b16007680e4060301c0b940141e506061084400a0301d4282c411f4001c2e80c204092003101440e04142030042110341024a101400c6181c44c40802480b501094040c10102c9420720100d03400096480019000b00d40c000340700004825034582c11810307945c514048100001d00801c5a00040d0002c206a030304604501e000b100c00040400030f00999078681c001017590601c00b14029611412075840000310343c941c080005901c030b440701d6044030f0b1964070440c0826516103038048030180074000c600d000c11080300940214078205 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 579845008 1250 579843758 579843763
    0x921040b040501120207230f010c020d050f1b0d1d06070b060102030d090c050307080606030a1b0b04060e0a0e1302010e060d1802121c03020706060b0d060323 69
    0x2c0c012241409403420781403440007502e9041d105500d030800141040b0300e81340d00e40d4040698450703280400a018608050241041c140285000044154020301e0003000e108030440b165000303402c80b808082810404210100028140489400700440c05000750842182c8081d00c040100703d06c68290500a1814048950b0391000b6110059044841080566a2440100e01758880c080c600c904551030030080d84140418030b4420015500250304481c012a02c444840359201001c840351070b0f0680c014903901c4009504200250300c811400409803c0003621440ca280302908a80c006400007035103008400c90614290140b131009003200d20030710601d07061007014400c50450441c00641844505200e614503502e505c81100d40d000d9545034200003140c03000b08242c0e0101440340085c1d01c181c0110141c3d1881a5000c1070004246250010702040b100050b20f00b600030b500300704000e490190f503c2c20000340840d42031000748211280c180d0b0005149080d460854401e043c002c000803038400110304e0a14040600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 579846258 1250 579845008 579845017
    0x60507054623030f0708070207051306081905070501090317131502011e0902031e0309060f04030c08010b03060a181703060109140a0618080d02030c010c02030a170604140921040b 78
    0x10344000d84a6101c042119014107102d600c0000144200070300607080b40d075481d1034081e0a605c0fc0c0300b82d42240e0f581d0001113443e00d0b2a404058141c042c601c1d03031b00c6d004559070300042409900c2c500881d040b075a40c9203050791591401603031000150351524011110b202440190070b0310b81130404410041c0b0034140d0042036851440c121001c029050307501440410784400c00680742c080000424290751820b002c0440251030304144401c44145070542d0020641c1241800764030103198002d0020304c41ca0b50741400c09400f07420303c01d405001c402401080300c4045071440d0084141e242450120340c3d0b481c14240c00041c40e47d11550311003010205400010728040c2d80300d0880b102210514580300c140b0a03240d015841c60594203902043c890310946240700c96040d00403014254a115140081081521000c0246d03200d200790100040080c0445242e04000c4c400028143c0c3c0080c0d002c0e00018100f0304c101003091181905442d0404140d004003010b030641c80c1c4800c2d80c5444101c240da0038a080038079101c82d81c110380c001d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 579847508 1250 579846258 579846269
    0x91009110d0312020c030a02060a0606080609040f063305010504180f090b161b120c05070e1501090f050409050a060507054623030f0708070207 63
    0x5810740c0e07031040c18454904403400010104045548503480805107569600015130340025005010009c2c09110302c0d48a020125080c076150000d0702e5451f241044140f0130014000c031144800d0003100d2022813401c0c070a02e1600c04868216140c08101d038002c40b00d00000c40290300700302d0040d208003802180da02038240d0f0708031107407450803e481c100090042c1d0f003c0c11003111007422803172500303001c40140851961814007070312040140300320071380200204030343c14245425010300c50403448199200207440d40b03006072201d05003880c0c03003480300540d075076124200401d42e480000c2085c1c901040c0050260408200b64042509080c03140e84540740206515403d0303010300c28144165980c4040301c0922000b40315070800942e000404001c2131400d4000a05113810240d44140b071400413100c0100c2513001454500d5180c0b0808130f9a60050303c42207929090303462011040400c00590000d180e90070380541c0c010f8410400d8400003c3e4030792904090101c50204010b001c80b04112950341400b40d0302d500462124260385 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 579848758 1250 579847508 579847519
    0xf03173112051506041409031801080c0f0a0e120a020f0429060903030408100c050f07150209040c080a0b0904030f080702120a020a030f020f07050607060902040501060809100911 78
    0x40d04c40c80000c005025000202d10024007000400c100c61101200610f4450300c50f50f42022143c0e0020011184000d00b264034642e2a0310030800c845140000d1400780505c400585880304600b11010003165414144042a06965106403020421450503001340780c003411042d20304120a843c03604110318940103400c01d840624446001c0e01516444038170407540b01d010081c0c2282d03034807607586031040e9403030b6101c2201d980f1552501c460149150300c01c100b116081451f142c0c2e96800c005858a526611600c011000c081c000d900300300c40351564a0300d01443e0301005864492202c103103060314003403090780c42301101310f40700c1c100386420080040c1d04865516022100c07407429140e203903540c2e42c0603440c052554803040c00c0181301054081e45964000f83d074480c3e040c801c0c3ea0368900500c503011706903642c00d04907030035000c240c010100620907030070b01c44007503c1414060000412440e1254020804980c82a001580024100d00800c4603203182000028140c1051000801c24500d042e01d405411501c0801280d1042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 579850008 1250 579848758 579848761
    0xa0e060604030605180f03032d180c1e0a050402040806160c050634080115140307053c0a03090b190608070f031731120515 54
    0x101c0d017011555140c12481d000c41740400f42c160481c40d42c982045800c00c4c02c540c8001ca600054190001040d0115000801c80f19040d40300c040e4903440710a03501c1010f4082e881200300b81c401031f40e140c40d00b260b01a1200031050b540c034002801801b50a07001340e00194001c80c01040100000381780002c03055805090740002481d0101e80701d42c1200d1810044001401c680300724420300544401d90b12084d40e841e03800d100003c9076192800f40350300c07a0360062000600441c03840c00041154030007041d48641d8800503071401e9942a0440c9403440d8840d00191881c0d00002c1021450303d0640071140f5008419001c4010002410a00004404100f41481d554129910000b0800c0a5841c0c040c2c3c12823030226600a000c580346240074000418030040701c1040d0543c003418040c0c001050000071a4020035150f0b0341c001000203a046840c4e98488502e09122004101810003801c55204000000c5400302e0118401c02810314010320004001520175410022010302c401d4a10000504000b0b540700503d80346124400300c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 579851258 1250 579850008 579850021
    0x160801120b060613180f05042003070306060306050a0510080a081b0625110c1522050406090e0a02040e21190305070906210e0c0a0e060604030605 64
    0x2c1c0606090140030001c9041d001c140c5e2500c0c042212500c3c45c506004200000e07803140000c00f614401da40261100700903c18400c00061105001c40c2c0001014048800c00ca80c0c0340d80303680071074105510540358950b031201031080c40a10303401800d4100528002c80601141000506130300c2d101c1c0b408001346030300400650480d505580c14056201e1010303d4064613041d2038550480e103e5a030512404030007101c0c0c2c000700c0c07018950042c0407035240e4605c2880240504d038641c40600c50001c00c010304444c0351440a11410040000c101085051038040c4401110140d29160601040d901319411a86055081c171004004800000a111790441c0d01200c01041c5001c004c03a44609100e0604584031413101c10710400d100c12003c0300001c0c07120741011001d54220301c80900048040328001d4911b00002810340c03000b00105407042c105044000c221840c0042d210a40c103982904031856a01840101d410081810342c240c83c0000880c0300a0044d01c4c40500760b480c101d40003403030b940302d140000de09040d07135400887c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 579852508 1250 579851258 579851269
    0x50108011403120d09031205090a0209060616030c1a04080307030c0e09070201020711060a020a0b090102040f06090302040507020c150a030207062c0d050a03270308160801120b06 78
    0x141191140d55281d034600d900f9241c0c00250850170000d0f00400d01541080d41109114030605104105071400740068102c0d590030022840f002405540c1c0c005005d1050a130110300031143c4200c0b944c440e80740d6804e50401407610024902200c984190005500010080414540401c40764481821300c0c3c005290441d07403000fa510641c005581680003441081000441c070740544c007c20b140c901030401010180380400c10030440307110f001030702c6005800c50301906000401c010742117600403303044000343c10b16403220003141c2c003019a075000d44005801140208258109480340321703004480d62024180f9a5080c0c0b001c01e0703501814504440c811040080d110614034403d506507480725034820400c1c415540001030032440d41038140441d07a07124070565903101d0403100001741030b9452011078803803a040804881003a401481040c1c005100c5410840040064a10000030801e242d031090f12403070740310b04010203840411001320810106100510006000d8140c020381d1007140d0743c0d4043d100c46110307035500000c40c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 579853758 1250 579852508 579852523
    0x30804030522090b04060b0f0715021201051f0804020105090301060801020408010b010207081612170c0105090712212f0c01031406040b0604120501050f01050901050108011403 77
    0x15250500c00d50710045010070200010708440750f5141c02c0c00f5055681040004681c414440c00f4050042007100021540465000e8030659000b94200c2d85c060744540d000800382da002445003402c05003614014422450304500c040190120682c5817990021009009032003650701130700c043e050003404200103207290f07800d4010030054032041c3c0c000e6490340ea41d04a200c0c0603088060549016008000000c05c4038107000800d020202d4030000d45010f000d150035820a0900b480e11030603a841e4141100c2600950408401050400000e400015007480d2540f0440d04020294201649a05100020a010501458200201040d4546540d40f22007402c18145d4107452814200d050706002c000484042010710005803111070346660590f403041181c04011001c840c2120b01c0c0290240c00c00001c00c405041c154803c407c0403001800091a16480314950480b4144268040b201d90791900100301110045a1101d80101070aa03460070707495040c40c001818800741402070000641824013040407e40d010081c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 579855008 1250 579853758 579853777
    0x60609030109141c02060c0c150106050d1406010c111903050a1506150c0f02031b040b0a030b040b0a1407052502011d010302210708010914040308040305 67
    0x801c030780282890601c2021007140b8003c2001d00480c0c030b0380710052002c820b5205081101d54040c00d40c0b5542c01124204d00d03003000f21040076510840340c5180ca40106081e2207030203800541c549a44030003003131111000303488403c1c84444400070000d05004460b608601204000350384505c00740e440c0302085c00400c0841251644400442101c800004140030010403038007410750040120811a5491044010075240e2501c00c112500d075500e8002590a40314041a1207540d100e01004d07980c000d0560006458400c030100d52f03450058500352400d00074a0f140c0302d1422920819038801c080e092458803a440d411030000d00c007500d1644040b000174040e180c41e600015210130103c1c3c0c0328000d8284810028020b4020070180704e001c09207036454000f6103615280301c4809907816944d051024604d81092100c01d103074007040a0501d43c00380032050902c06c0c90320500d441c10070501203008103882c003810010840007040e803084200e6031a2402d40150303816400c20f855032164160500102907207071450b0848142c860380300b11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 579856115 1107 579855008 579855011
    0xe07030b0916051c0203071805060306010c081603030507120e1c0201060b040810270602090f0d140120070b06030319090305060a091104050606090301 66
    0x42c4034000440ca15040c1e0a15144801c4600c02650b036081504003540c0200402c6025035100300f02c01261001e0540d00f0038524a050042050b0b0320002d0141c604000c0f5416401041c803010104550001100030f21044c05158242401130051a06070360000002d40c10344500701203002c160280e0b10030700c107401d40a00440400310780700e1401041801710340300070340d5203030301c00003404820b01d5018000034989000584006500c5081c3e2000700c0d80018003145030343c000600441c0e200110300d1582d5450310343c46100146d540003000001481110081c8840c3c7d800012900c840d0104100d44096400301c0c40c0e1070b802400502d200c0e00b040381201d44842041c0d10018401d03c034010218400848070360300a400501034901e8010001ca0409000903140320500c0420005001002009810001c0310307072102004104010385036090f65484079203450701c604548256142d40204803140d5411081381c06880c8021300 = true := by decide +kernel

theorem cover : BRFrame.Cov 579676258 579856115 := by
  have h0 := BRFrame.cov_init 579676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 579676258 ≤ n) (h2 : n < 579856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
