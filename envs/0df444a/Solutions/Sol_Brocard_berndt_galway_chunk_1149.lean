-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:27:49.962031+00:00
-- url     : https://prove2.me/submissions/c2a7bc15-7f8c-4ee9-a1b2-6760cdffad9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 206474820 ≤ n < 206654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 206476070 1250 206474820 206474839
    0x20d0204030203060a09030219120e150a0c060b0a08150a0b13050603060903030c0f03040c0801240807150c020d021f080c04060804020d111804110d02010e0609 70
    0x700080d14040302035900382500ca1b0390344500010160108000f039902143c103403003501c0301e00392a11a00000c1e04819292024840650360040103940c68602052201d142c81000c0b5441d100301e035100422120044100315229450112203d01611b00f030001c44084403001c0005041c04401a01c0080eaa40c1024000c840b5041d100c03107802070b07165103802174841d984070482000626840c004080514002000e4801811500100305110740b060111080b0340d48840c0c8074555030340d03030303103d0345003180c125451503001803c103510348882d000c0b0f40321b030100b483d00144d0b00b009040b14441e602c0d0780205403503a00340d10070300403042025042c4141c3c0500401190084600081000c4d00302140c5801013499070145244040e0807442c102c0007168140d8010703900540144030441d002d81024140403000e80784110181010348070301c50320000c41081028400b500c005004004d0302000007076804011400840b141a42d0495a4461030240302c64242445072046c940982c0582d81d01d444e2900c003e0074010a03030f119950350f681045030074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 206477320 1250 206476070 206476073
    0x807120f06050c03041e02030c01030b0112050408120a1506030b12010501090e100e0a020f061c02040f080c09010b0d0207020901080c0a0e0709091104081006140f0603010306020d020403 81
    0x42c4600c0744100918036203107949150a2801003c0c00040c1d50401042d041d441c101180076850000d980d01c0454401c0c280040c50082600068400798081101082401d00708410482007010f6407010384101c42c1d4000c0c800f42c85032034000f22201030718401c1e1155030844001000800189100741c10200b80f4840140c8418115102c00003030500352002600040034058441c61514040c09042100840004da80541040301c0b0760303d18080303030300c5401503030f006442114948444481540d98030101c0703000c42c0400301595105044100101c010750001e21400300c180100800000c2c03900004187c840c500b40000304640d01c80d1382048100e204603000b11880a08040c0c1c284a04d9006071942c0307100c02c6c060700c00400202000c111803002c01c800a102500000454201c24007448102900301c0f01080941d885400041010422002050a0b900444d07000c081144101d034a081040340701980802c0c00c1d606805540c15004030208207221040303d4103901c2e990080010001003001c904107602070403034440c0140c0c0240c9020307070f00e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 206478570 1250 206477320 206477333
    0x17070204020a030c080601090e0406020c030f0301080601051009151110020a0207210201090e06132d06080307020d021504170d1b060203040303270c09060807120f 71
    0x5860941c00709958408101e00c817500010542d900440900c0c149000f00c0c10000040710350321010780001c02031900881c100e1111344050007980e2840d046140415180e61f514070b14240d49000a10485016a400c12040c51030140300d2074000d010350381255270000c840b0b91022000c588562540a500800380203d801c070b10a01e000b14001808406940e500030503449041015a80560302c0c040340700704103405070425900c0141d0700210800129091540b10200700d03600c040204149840070703540740032480e2074014042c10096101080000d00121960810004c110030070001044408600481c1f01c581d01c18040d240c0185401d0380ca06020364405008210750b00d2040003909181c3d0015004840e0f0740341600c1c0700341c642e120104040c400040491400010150100030580800c810614000d400300c1e030008001810f05000e82c01c00441588840844002c40b41914000580d070010640c0460b44081090360001360b4030818007070107040c3c0c1c9445002e0556a4034001c022080d2000c10b00044a00038410100744011030034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 206479820 1250 206478570 206478577
    0x101b0209070f030608010c09030f080c0a0807030e0a291902070320010e040e03070b0a05090f01050411060c070b0a0e1c030e09090c0d05010606030e191707020402 71
    0x4540c03101002c400c01a207000c0d06840c80c0b07402c0301081343e1600705c4a250301648840690101c0b034000f45417102c40071450070701000343e00c1410001c5000b0b00c0b40318840ba00f003080a10042c400140665504c0279000b0342042041074502e030034030883c0070341c1d0031280d003100007152441d0036419030030744d186250381c54281600c5031a0000031401c08105c000d0f1b01300180070028010700c0001d03000400c120105400e00c42d585480081d150b4085c03044014000c03a40d07903112101d0340100b08102c600280d0019801e040b80e2420700080741c0509421078030340d8160702890100102014050188038051540035583c4000801c0c0201031001a07008100203080300e20403408000741200f01e0380002d0841c6000d40e9654507000300300e40248100c540d05050f01c4000807142403090004a40d1001c44426034281c1158140c0041d141c601c0d0052401c03d03880a555480244000c0f0403041145c15401402290b1450701c06010507070807601d0300750322441d88110002240c802180070000081506682c11901440d101c10a814410590041000c982 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 206481070 1250 206479820 206479831
    0x1052e0e0910060f080912030714031005011e08040209070c02120309040c050903100905010e070b0706050f040305030a0c030917030403090f0b04030605040606030602210c0306101b0209 81
    0xb26581c000b031220310b40c0708204481154050030821444e0810070b80407070381e41e508400c0c1035095007004004506e620384910710064089078641070b0789480c1d0602008000081c1c0c3c0c1d6100d5a40450701d01d1503e0f840106803101141400d0070a03440740030655030380d6020311515020041004003001446980c6c080183c0d1207801400301007200c4c02c011625a02c079a0180b00840300c107000450b0500406100c0d008480c3d8001528071750781000c8040c0441c03001480c0c5049400340107048865405402440d0003c1031000b03400d800b400700203001c0c410a00081c0c0b01c600351017140084c280c80c054000303101080060320080003070f0445078030600d082c60b00050400058403500704001050b03440482c2c6c841d000060001b8594000306500142541490b00a601842d1019204d40381c80b407444000c2884ed1160700090034007400e075000780f00a68003c01c0c00e5507100c0f801410000800203c96800040780441c0300032601c98034180342034038440d80c0068124021a840c161047d650b00e900c15030880c43c0b91224110110050703d5850180340a031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 206482320 1250 206481070 206481091
    0xf07050a0c1505030609010506090a0b0a030e1b090606030c04030b043504180e0d17010b030f010b2508090111030903120a0c120c030801052e0e09 64
    0xc604040a00c0360006240c500401000001c0c8180301700390740d0f480d6005044400032100e0326903a00b40314001c500100781d242e00c40280c410303010170001510f54058108202045802c4240c0300302c0d035950400c0142e90b05003243d0294014690300c0000d603640c1008001141c00850807034001c1d0403c0c2d42c3c1d41d20518001c40403901184c00d13840c201540c51f03605603007001c8010310030202904086070707038140c10f1301c550b01307005500c518115a071500b213903011800b410380d00c100080d4104030140c0360040e003e008080c1c04200501c02c40102641c10f5000007541d10b100c0004c2d03a0182800484900300350b46090004491070704038009102c41a000401c2540340200964205448588904c08444d224500e140014080381003129008500347c004001000180d80d003c01c40a0700c811580b103c154407041d1040d02118034541e89000100200c0b0542c48810101c0d4101c1e1640159a12966484409a1b00c507001e00a2101c0d00c1c0d200d8044903c00d40402c82901500d482682d002a15a488c003440309001281c00101003250596095104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 206483570 1250 206482320 206482343
    0xf05060415050a1803080c070218041406070509100512150901080304081203090f0a0602070b0c04030302100c050f0d140a0912031a06070b1602160302060f07050a 71
    0x996503014190f0300480340d110800102200126000300706045040040802090780e000071031000b40c2c3c0050b11410741d0050042d40b4070000030092580400700640f000e81d08801c0c1d4040390f201c261000108144074031120703540d0f203044c403007020248128154006152400d00009011800704003031030010040c82041d11075018130045420000748081d050068010407a10703082004103201e0044002503d041c8070120125541d507a60703c43c4002d6081506621080d041401421400d0040c411075801525215004401c80c0b20507071904203500f0200c0c0328501c00200560000002c041824000340c2c003036810101d039410410300c0c105002250684692000c10009056a600c25481c04045800c104065104001503000c201d0b4520a4032451201003841e0402d030101511030601c461b0b000c580b401705982c00c02d006440580c6403000c41c40c1c0550350450448011401c03007201c81000040c01e20010b000c0d001d0090442c07102c8a460705640074409154410400c0241000d0104480000142c0800c106a001805580410321 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 206484820 1250 206483570 206483603
    0x309150604141f060206090307110d0611030403020d0e0924042c011a0d0309080a080909070f120e0c03030f07030f0518010309021810170a0c05010305040f050604 71
    0x43c2480660401d604640c0020100071889500200b100e000642080104484200d1440001c0d071030b41d080e00c8010025400d180300c42103d04558000b03140242e00c26002d4481d030201542c000c617869511160701c036610503030801c041a030754425841c001c0752047c07840da50325200c10312000105040d103040303855503030b40d000a482c2840740c2840c40d004060844680c110091250131051007110740031030500342c40c0368030410290300d14108050003907201000901100040c0d90040540f0701702000341d900302d950014042e00052002894842c4588501001e43c60f15031101803d0f09035202d94440240401e61345204544030740540845150790030800381c51154a91141a03075030f8806440c008103490070410700c6006200060048081010500e400400803000070300c1c0020351418a8000180c24030048500e0140c8002c01c2824080c0b03082e00700c40b0102c1503070102602c0300c0501480802d000d42d80c60588001401c20607041c5000e00581d8441e8009075080b500950052100030f013162607103820324405032811238424420301010413 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 206486070 1250 206484820 206484871
    0x30301080106170d030b01120501060503010e060102010507020622020a03080d110408070302040c0923011d01050403110315070503010e010504090312110d020a02060603010e03030915060414 83
    0x980705400110f20224a8a40160b42d41c1480c0c034040c4042c542c9840300c41400b87d02c21040c401ca10403503803c042c4140c0d40c0d0b641c0301802c503500c04c0c014030000e0380d403020001c1c825500500945000705002c2c3e000b00b82c0c50351224409c441c0d018801d580c1b500e0008091035a140565542882840990300500c035281c1e940200c1010031084a030b0500d40022070301d90a1100f001048004103541d0100d9405490120b9079025840c0221142c002680200140382c80d503000806d1942c00c1d01c141c44404000c21f1303d51204403c1d000e0100c080124448100d140043c10400c000e0002070101c910003d8010000390844580017521605184401c42c00c80e81980001c401000410800c09140c845500511043c0c40800180308140c60050105a1708a103249055403504545000a0440310840340302c00c140c030b08215201c0c3c4c10500c0c000e482d00300660f0a01d02c80d600f0030350140710010001c011280500d41c0c01c4010320300c41c03007010f6000760302c0d1000406c400c1c4e05c03540d00c80300c604007810310342d4680748191850308004a10030038008951 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 206487320 1250 206486070 206486081
    0xa03050a151212020312070e010e060f04120804261b01090b0901090503010c030b040b0901051f021603140d080f180309100e0a14060414031e0303010801 67
    0x15407501e03a524404010002c01ea001008a20782c00c000000d00c00300001800380d240d0704c0303002c1080146000301d00030410301c581d10516000d40d50f50240d0321090004004010448503000740040c411410604120401040e40035407862960345115016050510f030f5a02a003040f010400094260b00c0d0140070300d81c0300440e2083c070940c00041e03050750410103001c1515000070107020303040c01241d0040000283c1c030101c82e80110306510041038000c0090042e0307500035000074003a204400c5034034062810480d2a4009280545006041c0c80001d40500e00440354011240303400c030000d08400041d07000380d48201561242c0d2071444c9020b107005100154031012140e480c180341c41d5025040008204081080c08200021400b40d40c0d002100308000441c6007560000d99030451090300c03501c0341d02c2400344600ca110290440d8a40c100132008030b810103800e90741c0d1a5a03c0141854004880c0d0101040100344400f02c84009581c20541c005400c580586010303c840c02040c5c040b0421144085d0300100040010000c00d0051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 206488570 1250 206487320 206487341
    0x3010902130b0a0f111f0c0f03061406070813090605120f2e020c0c0406050307080d03050403050904020309060a0b0103060e0112051c0c05071706040609060f020a03050a 74
    0x1030758a015103458000b401e00b58082104d078204029040d120141440400c02c1200c1c40700802298a401e1040c002c080c0018540707000740c4000305000e00114a40180613120320b00480ea2034080400e100a84201040850360100100700e601e0701c020301440f03120b0818114403401801c9050300000b10709042404000034a1030f18013029105601800f040510070102040d48404800c800e5840001020350440d0a20004118420500031074404100c0980b004800101c2181c940703c181c500f0040c964403641490385496007402990240d07072250a24005840c46940301690081c02864003d04100c1008002000e990040d600100c10f030788420706000e6111002c2c81801507041e0242800c200e51464140600d114000500c511140600610b03048000d004050000b441800180111501002d180002c05000e940c2200701c10340f02407040c51030118074502c980700c0113902c1351800c1e40100b000350381d640d440350050b1005a9088694130f031100c80040030208180064540c900e055100030801d40341c0380302e0140446000b185d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 206489820 1250 206488570 206488589
    0xa03050d0b0d0f0b090c060c03030109060501080727270f050112080c030906040f06080a0911060d061e03020909060c03070c140a0c0e0a0b030303010b07050703080301090213 76
    0x2802d00000f01d508048031072190340074180700e0701540c0d46100d0604180c412101250032030400111411070120100096051341e2020a04128441d200d02c01128000000c442500c00710350b03500d0a16108000703030701d0800c2507009203140792030b045902c0d03a10024800c41c0b00025402c0706884001100c80880d01ca00602c40b811492000c1008551b15140078954030103074541025100701d03c0003c0d1744c030b1841d5040c82243d0301e0100144c040c1d5a180d903504086007622482c1e205003000034282401007406c3c0754860181100c1503401101208845c1601e1040094507880401200c00300e6503a020001040c10000f51031511035149800050f481e03a186006018852000410300d05031030f04150104611092550190b94000000c2d00c1e110343e0708a268a49041c91401030648450107115403c0001d040264912190041d285100c0310b0002c640c490f100d41c80240d0f100980305a6040e0014001400343c07001c10005480b59502600c00c4a0310a0358a032105085039200782c002103225900051071a0f80f5001c03400306140100a0800c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 206491070 1250 206489820 206489839
    0x4090204081c021b0a0e10050901060507050c010f1206091a011707140408030c0105070f0203090f01050904230103020406050306011505130803160302061302010816030e0a03050d0b 79
    0x324004d4680d0000d00c0715400343d0300c0d10300350040304d0f071141500c0d200509110940c0005900f0224038080c8450800e01c601e600c121300381000458158856025200003d501000602510787c00310700641d1100d46110004040048844600311001d1242c040c05006241d00100051160f890a1b203c2c20722003c102c03001414010101070a403042075503220b40d80e41c00305d014a082d510300a0100e1329040c0500c11988514410701c0081400e05010406511040c0142e0840d111040c1c42c20444006980700d0085c0500d030799103c1442e090303030041c03940514003d110381c140c000c10009044440303c10702103000781e0710480c0000e0401d50360014411802c10b4803c00c40504405c41c000c142a6260020040801d40c1805014040110100e556a2805040c9920101402100066a403522450440d10340b84843d58141a0300611030b010101e140303112803005200341c20340c040c0e66080e21590350000c511210390401d07034140200f607a6182191484071041c020846907601c03940e5500c0d075035030125211006403190910030070321071030340314 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 206492320 1250 206491070 206491123
    0x1e050906030411040603050714090109060e060f030c0d030e0319050316020112050a0209040609020c071a07021c06050c0f0315011106010f0f0e07080c130b0409020408 73
    0x40c0103070780e4800d5004050008089003400410050100d65200400d6803140300c0010801d40c1524180e1740f060082615500000e80e62011000150b501d180f00c0d40781c1d043c420401150450400144a1114450107801caa020f9403800000c249003800a104c140d0019030300b41c0030225145002d20003050007894080b000c01417482942c40da06d8491003030315180707407000c210910b8076411a40034042094001114200410040c90500b034032001070350001c02c801d48a285440c2022440760628429640c545034800018600d0500305a6862087c015428503125000418003001c0d0050b80e80101c1b94122198284030014440400d03d840815120091f0040000002c01d00280d81451844021780e94490109110800c10401d04401680d00081200b00c0104501030a4008200d440301103550104032000d0041c283c0e800f0340d5820540c030200405071103d00000e1440d5010510b0014004060041f01c1c07955000b014140b43c0e16414170700c460f44141d00c168040703a004201000606410711182c0606000e54050780356541c0310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 206493570 1250 206492320 206492329
    0xb09120a051903020f060a020a030f0c050327071401201b13060f0501020c0612070c0206041701050610030b0d02150408060103060207120f05090607030507121e0509 72
    0x203080b91200c1d107180c81210001498803c010b140c40120600303064400c1c40c104641c1900103903000c01305101c00b003410600c007044003040512490b00e100005070750b91429500d82d946a054070500080f01c054403401910200c0e1801107007449130034028a2111100c82c00b002200d800901100074980c03410155103921203e01500c00c3c00030542d12a080c04d00803460104081e5140001d06520b00f4034106000d43c0d2414201040500c45407007440c1c19524240c00319a0240b021004002c0c0303d20800603111008603c040100d00d03890701501d01d5a0f8024030003004241442d45414400034101d81030360700c01600d03030345171018000e550600c04c010080070009403500388641801c0c0c9002c621260303d6900c00034081c100c0081614a5450b00c80241c40240c40e4503410344545580d6800c0020280d003020034280c0d01c06142c0b40d0006000c5000d290150b0200110b03403545400c14170030404000c8581c00c170400940600c002040b121000072801d41e40e4900e41001038407808800914401010108aa840d1041d000c0c01010441e01c82e01d03566 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 206494820 1250 206493570 206493583
    0x51f0305100b151207110304061b0f0b0a05150a05030607080a1508160801050601140a0c121205010b090f04050405011103010303110f0d120203060406050a0b09120a05 73
    0x66428041442c841c0746001c1182042a000f03038864030240031684104840b25901d645000d80b4056840c2e42000c800543c0f40c54a0b442540304e5440850800040c45000c42c01041640780320900641c44200314a400c1d881da2103114404a440160280d520400c2000d4807054a283c610b900d50700b81c889042c002e0824010a507501d20160024046c003d0903030026400900b16081486800703071a44004002690752036205603038840303002040318440d0407030b0b03000300d81c4a805126252207210140d48107007000260640c1c0e00001d9000c810b00104200840300131401080c1486240030340000d095958080c0c3e451804280c20403500103070031040d0780030700410400d5525a200849441a0341d070880c1d0001d02d40e281d0f45001c41c010a0701c22900d611050002c80004113154020700c1485502c103c2d0400e844010102040c0c80e6180c07000b1448a8020a0744d40c49a0b10b50303401075034050f550084c405400001d884d40c4a0001031990051070703101400030350000590003860301349a40c401000219100083c0490440c43c2c0d43e0945400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 206496070 1250 206494820 206494843
    0x50702040216080406090302041d070e040302033711030406110106170a0201080708010e040807330c02152805040503040f0e04030c0b0a060503010e01051f0305 70
    0x140c010441c14444800b000b50200810360246049540b80c1d520400035006094510007a48541c3c40d00c1c2c0014104003c1c883c0d00001450114060505a42014443c2c011400050815070440c4820b21040003142c510310b402c212000d20025003c81c10740c07032072201c1c1c00c03114030300b40c85130010400d8252609035078500c00030a44094401c1e60420034000001100b0700740c0140856404641100d01e0f0001d0000c079540081080943d1703d0003070f611a110f130b030345194083d60718450a2040e002c251f0030507030004002c10305180140a402e88038841c40241411a010b01c5218428000d45095003601407000c1070408030700500c079504840140780081c15020b0000715807041c0001c001490002044003000140da10210b280341903801c0d201c2208010812410701b42815996074100b40904074180080d1200440e49e0000e0540c03007442194959078404006100d030391201c0a1000141c44000c0302c903100d0b640800c80365802c2c001c0900303510080000052600d0500da80e101050029003030803034209285041030010403400b2611441c403c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 206497320 1250 206496070 206496079
    0x10e01062d02031c02040e090607020d0f032307030e0111030a11070f0308010e0f01180c1817100c02030a03050402060d110306090601020c01050403020f06070606080d0f020a03050702 80
    0x40030440243e00b18840d030a400300307150700c1011081403100d80560203003060b1250880407654139581c413408036545420603034442d805a407198103414070003841840c240d4000b440f989401714070b0402d0080401015071514040d1180c40d0b84078420042e001d54103100390b5512035031010081c0b04411280c80d0860442c4005408107114580701c1c1d40409054620000b181e01c3c2e690310442c5207200103c5401e00a2801d42d0a0103240035900002c0d0118407550000394543c1c0c1a034101c1201c1d0079210540d10100030080c500b00420b5004d02189103070400308100720049880041c0b42083d5101c8091901d0103040c3d040072191b804d400c0032039183c070610f2039100d175000040d91500790350350400140a8950b03000007107050240c6580314190358100035500040010a602550040c00305480201198541000598484a40b0440c0c640010340a210420143c940005c9001c244040a030105203880c07503940b940015aa42500b06410580c020480c4803052a80809200036880c4144050902041c181d0780050003481000310180c0724 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 206498570 1250 206497320 206497397
    0x403080a061a13030b0903071a10180902040507050a1107062007082b080f06060a091a0405010206090d0c080d15080d02070e0f0f04030203070812010e0106 68
    0x1548940010f2005503030404211411464500d800e1541ca502000045484242160510340d04141e8005020f002e2421650211103060501050040c0165080314003500c180c0c8400300030026850300e111b454007804650b503e060707603115400c1010348401803035900040740f944544400c0008503400881e11202000b200540c1e0410854255180d00d480d41981003529140607003214218009005501345142c404924000c50300401d0003e400e03140d0b6401290340000381c108100c0015014035100d402070021514034201001d406489194111007003540d184440258080068140f0280d0380403c052a4084030f080d0041141c501060802002001d43d108001c0c042240800c0d540c90180319500021403034104031801060080d030310400d290b5610200c0c210392015015100c07003c01c2d18481a07040c1c81c03080300100803000041c0c9616684d02c002d000010415030071800301b0702607a00044d030346800510621074912140309580d414002e40b044104c00680c45182031006000d4801c04486900ca61044400044000484d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 206499820 1250 206498570 206498587
    0x15040306110d05010816140a1511060112110603041101230a0f120b1806010306030b090604060f020307020a1106090307080601080f010b0307211a0403080a061a 70
    0x54054104040310b502d06110020660340d8001843d0b100c0c03840e00c0d1400c55070712980c0d080011902031441c8443c94001620040c180035210751102d044007401550b00e449103036180108a00b90800c0300c2130f00442c0100e81d00c81c0030700090205110700f06e4241c0d54100d6a00b40f850410f40d1303079601c400003046002030501080790494100182e40d01c2d8042100c40c1100074080d502e0342100d5000b40000c18030110000030400c10390035500400041d00c59541d4421000d06004486803007544821802c070030091445040540314240400000c09161000f400317000c01030010700340c0c4e04080c40c248040d0782c00413618159051050082208996000503424240798010032440406c0c0310707a2011900900c02d241000e40c061241000020b4020b400140302412103195406035400104d070840c1c1c060a8502007201203525900c105000c0c0072440f0146951030844c1286074510f910a0002e5840000c000d15103145901510000005c01040c15000394000b80d0000508204005032410030545404505d0f403240078564030500800e07040c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 206501070 1250 206499820 206499851
    0x203100311061c020a081b04030b0a0b0409050f07060507020f0d150203131b0302090f1008010903260c0307270807081014060603040f06060306021815040306 69
    0x2407080ca00e203c00304188080b0481110b000e54000004400060202d00c009a0f5100c41039945e240d40d140300d24a0645014903507103c0782c44100024080c15080da40d40c126145003980c1e14402c4401042c07291002e0410f4880d40e450703090402405034880010f001c405c0007400c005a45e5010300030780425086800702c58505d0070341030448160311001851601d90b480041440000c1d8589085485070030b104400d00c1c0080010302110340d4480d07d41c3e00c0020340010307911001c2402c050340604860341c46014500300c0381c0400c0c0d64100741c07402e40c1c2c5228001d902007041861903010804103079040002c0c500c4001038a03072041c1000510b5052611005113004208444c12840410080320310300b40600091444100c07148490300e5614203a02c0d0b9003180300310400751260784020183c103c21030081044450f00740c8904036495541e20140803d030b51000708100e44200d07009415000107002032284102850050000503200d43c9070401ea64401800060300d9403048414640c6070030030780c281500320303001e49511090104008000581c81c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 206502320 1250 206501070 206501077
    0x2060601080c0d0e160906060201060b0f0912190605010608060f0121020f03010e071b060513050114010e0c0c070b070f020307030f03030b010e100809070f141201020310031106 77
    0x142c00f41d00641000c0c45c42e05a4030154001501d40c0b284040010640e105c40a0342210268819040c19880500c2400c0e41040d111001c0c02c172101019110381c1051400080490602690324122400c0341041110a402d100581c442e1502602d50b9041c02da441d800e0041c00516440d01da44009410000400f00c02c4000101c40200605106007844055482d06840b84000c996a0000d020780786c50071180c003000820603407040350340c03041c0441128642d001440c80c549541e0080c1c480204040a201e0f4902280700014509114007030b45410902600e8556504207144040706150191005402c3d800520141c4409600416080101e9210f00c0729035569100516094001600c9204040d500d406104000802e0046d43c00741c10100502c655401c01c04801d0080c01543e00c0802140803540040c0071a448550407030040c02c4c1140c110420000304c0d400f0300d540c2c50329038003e510150418484900000102c0c505410800c810307084c80c8111100035030842c90009900e541c140c00c02c2c440588031041a0a805500ba215107046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 206503570 1250 206502320 206502341
    0x6070212010b1005220302090114061207030e1506100518040204030b04060b04090803040b06031006061808010218220f0b1c0506011404060801092102060601080c0d 72
    0x2c0e40e44a904604060005d4220401424004840781088020100710802d8003044c0ca80c001c0c50340381300e42d00301810b1210000c070b140340c55030700080204805014124086c40c6507104204982d408200030034031107805400e01c19041e0107501c94040c1c0c0000d01555540d11100898001c4142c0352282d00c6100010020f45210241d0448079045480010040107000792403c206d0312841c0200d5080c800314200c10103110440700c0c0088041d02c030741c000b400400c0004a4000d0f031113401c541d0003001c0390f480d1006080120201c0d1711961020340840c40c3e00b0440c002c0c80311651409401840c03100c000310305051081d5030780b0328440b5100198911030a4600a8000c402440541f001441c1600b250100b00303a04110020b80c0043c810040f6840c482d00d41ea40e90760505403681001c0d00e55255000740a01001c0c0d2074952001da441c074200c05015409600d40c00c5c040b071290800d105076280c89004031050fa01055072801806444000c400e14041150010800c1011998004a2443e005180080303890b40e00e100c400429001042407400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 206504820 1250 206503570 206503579
    0x10050903161704030f230d052b02040f0b07050316051006060e150711010509040207020303030a0b1503070c0305090a090c1e0207030308010e040503070215072006070212010b 76
    0xf400f1050007010032000304280d103c2d241d01040c3c0200d10f404910400e085540c0c5109076030140031603403822480741020345140010710740c4440c00e071100c602c40720481d4050b42c00b01c5044130368041410400100e110840100401d00b81d2003851400009403600c0e07840b4030034003045014905201c040b80d02080b170100322440e0700da050030508100170303034590400504803102200c05500c0b230300c2c000d900e0744041c4059900310340049a00825545003000c100006692542002c1980c07680a913081c0035600268070140000d61240707500310000110b40c440d560400480c40001c0c01c0c20301c4454414410030095a8000007054003a50b01414026100c0c051080058010a2aa0041d80c130306800c040d03601c50002c1e0828501d00701900d112080b09407004810008990310403d500c8050005503095004015584c5c3c840303503482d0004e00400640c2c0c5001c1d4030703070045000090382a40200e03080000049107803c1c806c8510a201c580640411290180c1103000001680b60240302c8020b07118648880300483c0610303096000b00390143c005403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 206506070 1250 206504820 206504827
    0x3030a0906020d0905180c0c0d02030909010603110d090203030d0204030b070e030f120702030c0a1d01050402030712150e0c07030809070510050d0609020304080c100509031617 77
    0x40020654030300d62064101500c104115402d01a0051039070344207580f40a0700c090840080319201d51140d003001f50006d0307d072100402001e805002c0c28404007040c0d0741141c00a541d01d0520000b0f20246150582c0400109440c04141c440c1100071441241c0c0f15081b00ca402207904191800040e08502c680d02e14031101c03c1c40018000b0801445100c2c0c0741c0304001640b01e12150001c00014141c81d444184500c0e070007a00411410355403800d040f000340c02ca086c00903044608c0001004003013181d01d0080c0c0c221070740c0d0b030030b1030502e10032055440c0ca54507000d010259815411420300031000742120107440403000c031032a20341c054140104c12940c8042d0041c00c07807005060180c1050015000c0c568424030054000a115400103440c221300081c20703d0840f4000b03810f540021100e0403040714250814151032600944840740001c4050b11070015501942c0100c0700980e0740c090b040c80091034054480c46024202d803c281c100700d1400d4002c800c0e02c40c04083c04800f903d2110183c60304c1030100c3e403201e008185100011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 206507320 1250 206506070 206506087
    0x7050919140103020310050c09150f03072001090b010e0a02070c06031a01020601150e0102030c150a0b04050609010603021e1b0d09030f020d0606050405150112060e010905150303 78
    0x7904964101da00a40644a02100c1004040300340c5404070b80c003034130302c06041060920703d091030041100c500028030030060800809012070007841c0d1050303491170000381c443d410751082c182d0313031260021722405840000c0001000b60b50301d401c81ca810510410045d40d29800004481c0b0302150100c4401aa010302c0c80310300107440e560081c00501c00201c0550301c42c107424645074040d500028070241a24060a51181030f8100d50100719496620080c045c0d045000c18882c2c503180c0300313041000c440111700307404c2524010301c0c0120b00340c0300311b4400209003407142d03041905021441c1c8419580364152000f6290142c1c1e0b40c4001540384000729034810707c049110a00180343c080c1d1403000b1030090014800103069030900c50003000f0469520915000107400031001010140c0145404078400a21511981d00480c4030381e83d5030005021100100c80b18070010700da100d2601c0e025030344400003500b081030a0720100405800c04a101e48594414000ca40e01d1a985001003002d02070202d1410040c11170090450780d881581 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 206508570 1250 206507320 206507351
    0x1090f02040918060b01210b060912010e10050403120b01030b0a0306051b03010503120706181a0709300b0717010e1306090f050d05180a030507050919 66
    0xd0400c1d61300074503001806010f507205064010b00c800244141d84031807104100180004c01001003055030080040044015030b4995000050303952180000020f18030b0f1045880c141444a901303008003030b0234500802c010000b90030081c20b074070003010b401000030000c03590401603004003640b0301b08941c40769550000204000080d04142d1040d0304042c000c0300150322000c10702c10240021301445500d50000e03044120706008030805080114000c03031000c5641c0c5e81002450b040151104403d540d200750000001601d260002c4bc40e6800014514042c140d45240040003102c280d901c1c14940d500d20400b111098000c8102d16001115a0b00441203040500b0000c0c4090702071005214504140d960150002a418208858140c840d000b5112524003103403043c1c1e1054000d0101100403504405a070030300d10702159042040c258107881c180c039890340d00d4403640c4282c11300011502c0c80c0c610401000d2001c1c40000c0004c5016012200190341010040d26401001600f20480d8800500f08500d414441304501d6907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 206509820 1250 206508570 206508611
    0x70e062b0b0c0c1212010b03070c0804030b0901151401110a0503220b03070c03050c0f0f030d1503121404080607030207030807080f0f06011211030403030c0c0b01090f020409 76
    0x1960004c80e05213122044000a403030044007440041709040100410071505d80c1d400641d840031180c5032441c1441101e940b00c01c0c90390056001954910011b5003000300d1050b0900c80c1d401500170741c4000b45000d0b840d090f4007900040c04800614100f00d2840240515400c00f000242e450307a03809070559403102e8040441000610400e0f483c070b9604950200c0015586011904880c083d58413656030b500c1c00032079510251803542c014a4030003403510072140300115018083c04648038600b8144040e51780c4810341040c0d81e003522807650010fa1049241e660030000a04200c1901200300301c40c1c102801e5242e40e22081080d07501490344510b501e0b00418003001203250f415402841c8180c405c2d00c580040f504c034014100c0e1001c0084501400d1041c100d008149400d08404919a01420515240c00d20408622040d02951881103801e4010324020050000f00350701030150b407007112014600821980d400391a0306400060620035424810742d20380b0740000c0d40480380c04840250580f40414030007820b0103542c3d54070404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 206511070 1250 206509820 206509837
    0x2061e07060902150f091009091802040506031902120705100c230615150721020a0203100213030c120501060e090c060c0109060e03030108070e062b0b0c 67
    0x10700f00444071a040603882624045c503107001381c0c13a00741544502030000258040c90380710107004000d17030300152482c21030007082c1c4d80b03400918942006d945184180001d07654003170401407007074008a550801130140040f1310302c8035540498882145c40c4601071040d04203045500010382201905004603541d0b504440d140300c00a20800c1200c602c00312885284400c424120341c404403a81000011a6107900030345461917040c00700401d5001c4102c901c07000700c10700f540444002c40300420a8850124018080c101101000c1c10500282c203100b02c6540c0001e07114402da85044031041d0340841ca24081c09000c44061000d5a480484507034540e4591210400e034040034041240c4641c00c0080210740340032035013222800b42441800070b100911500c000c0040c2c0342c1140c0e462420b030703640c2c0d0b02000c2d0204905018180116003583c01455030b0f035052104603407e100298001020010300300d814004039851b0070104200c2019101010707121a007182043c1182411242d04c0a00607007285014002d20200c81c40c000d01414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 206512320 1250 206511070 206511079
    0x10813060e0d1206030209010324050a230705072904060902030d031406010c060f0923070b090607030203190807020c0a0302031c120c020c01030f1802061e07060902 72
    0x1080314104000a1310200d01000790400c40c02c800400005000207030948007001c840f00702c030203076601c40442041110310403968068407544607a01d82c0c60500c41001d50f0351602e00058003403202d03031038804000390140c40366480042c4158220000d068180f0304055212030b214842d400b4070511801e10742015006800c0c01c1d10142e00c24001d42961500c0c280c0213208400540d081c448000500340d441d6001500d45200c10f800544107107071914142010440d051213000c00091040ca00680d0150100c1d000d00e0380001c81c07647e001d00c03075840070300284400d424100030f840c401081156038030395a403c940703022402d60042641c031072942c01d881c0c0d18542806801010b01481045964200e80d013010040042248949040c40013a4054002c03180e64140340070f400c00445121001030600c030f052405880c070f4841c21140616404c0005030440b82c02100e203507915008068003000042c1c4284104e180c207080700e68403400c280c40002d200d107500240350f107a10207101210382d05c8445001c0d0b1203030b00e0b40240e0410101a04400604038400e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 206513570 1250 206512320 206512337
    0x4030303020d0518060f06030a1a09010c02061b0a0509040c030506030c03120f0d0b06040e15010c0201050d0902270105130507080a0b130509010e07050604060509010813060e0d 77
    0xd800d00425404c10185142c0104029216044034003100700c03000c2d00894250240f4445100810401501e0903404142c44a90300064076000348500d08407a1503001c10743c215000740d814805805002c911109100c105854295602c20301d9041c1170b00c1c5449034002a0743c04c103040200d59451986c05501c503920860307083d01920030260100f070804d901c0d25005020b007442d411007441900c2c501d9055002a06201d40650b00004000506000148054105e5446841c24000507020440d41032a0000c8070008003900307081c042e840340490790010307246004042001c0d0b00d01e6500c0015005658650407266940c4100c8a103800c400f904003030381c01c10001d40034080c15002d40590354541000860501c503407881000780f5940e6045d01c0e00d03861411806001440344159000300340000e21014220107102d054058040341000050050030300c1d40150400c0352a0f0301c5980b080c4420b010400400b070700b10044603240c02091030464115600c2a41c1e14070300400e100303800b5140c0c0c0d2518449070030141001500c03c0b90b035920307900d0301c109 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 206514820 1250 206513570 206513581
    0x92b0213050c1c02090a081020030604020a230c010510030206030105091b030f150a0503060c0c0a0614060a090e071203020124050a06050f090d05030d0204030303020d05 74
    0x191141512044400701c0304201d1110f40c03034001e858800e072000f81e0702c20151809825000140258205030410070082e0081641c0030081100c0f07115120444a903105086030414078826412307928000102084c0c061070b000515468503902c2110001892402e10b00d61014415903480088140d40152409089a41c40c003801709034000680341201c802c613503008040500e540e0030301c0144000c1c40b502034521a900e800390390341070310550b00381c0c1e010b03521036414003060051501c0d05900b00702c1c0e40070303012011038050005018188120f40740450b8a030b510804001202e65105521b840c100d2429004400152940f850004507141010000903514040c49046505459083d1204001001c8444141e6644440c1e40700343c1d810805020000510300c00789000e80000110100350040107031401c41b101d00540d904800381c010030b000501d40842028040c0c045441e201d410444402c22400700c9202b005044c80c41001040100b50410904000f180e055200100f000d6486c0c994910b00603000c0d40148040c0c1456a051400140c0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 206516070 1250 206514820 206514859
    0x711010515010c020303070803190506010804020d021c0b010305070e060a060f031a090916090b060d0509071e060305011203020d030b04020415090806130314092b02 72
    0x6009150355521604681e4000c030040d101c20900142c100d030075000030b0040d4000700d960b01d000707507104100c809000c0c2c2c20900725083c07800840b80c00409d61810702c6085801d00c0b01603128107105038445a4141c0740d1080031004051504844401010010000c2e80c070040040104030001c15500300b00c5070240d851450035240c2c002003207484e0070140036140000d82a60001380c07519110f90401c4011900f4242032a6814161401050380400c08440c1006c00341e101d44841c860100002c0741400003015013900c20001d1903d1007000401c01c0c0704003111200c04c00c0d1a1004103c0c0d0303980034400d09004014201441c41201c000301c04140c03e0f107070984600c80211f0728000c0001103494210034220b141680c581c0c094401080c5100050340107164002400760010342c288004200c02c1030750a544000c070b035826242c40f646580b510346d13001d26100c8002d00400000041d6428200045d0308035030103080d042d05094240b03841c0c2c0100c03008035140c050b161010124030019a0140c20200d4150342100d80818002d032441d1030700601008044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 206517320 1250 206516070 206516081
    0x405010510080406111201090c080a201e03040f21120513020a090207020a090207020306180a05010203430311070b090313090b0603040818090708071101 67
    0x850102c1c101100007000103d0a40c004901c0000f284841030500d42c804600c0c2207661002d82003042560341d01c40e14144540e80180c406c03a44540e164109118090020110251070b60952407400c0342d0180101d8020003104c402c20980340340c5803070b10119985903e0241025521440c0051043d95800a000c03441c2c455080303180404611007510b51500c0c4000e0644206090050030000c5c00c061414040307400c45001641c0d21401036009041400c005602c4c1e0710316004010054404e0b5010064052040011000588020900640c03000031143c644100e0a03600c03001508100f03209000038190352002080080b00b06052280f0070764480d0762030402050030768201440244000c807a90f1040c0000103600e2a052881c071075000849034020503c020b03820600c1c00d907118040c2881c10742c3d102c0f025800104003142e0042054001e0801424880f100707000614901d401f20f806403201a00180c400e2600240034815200700c24105a0984000707000340307950340781850340103003102010b4401744c00180451542099400050245 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 206518570 1250 206517320 206517349
    0xa030e0a0b01260a020d0f0c030308070924050f040f03050d03060e090703110d290c0f030c030a1404050d0e0f010e100903120503010f211b150e04050105 67
    0x1004c0303818198080002007461650300311200c20000c400c4500140c4031100a10046210340c8444d4810f00301040c000d0032200d55500300041e210424455146002040380382502d90420341d0070085c0d541c15903018428924400c54010001200c00c3c001d0001c10860b0001e07464886070410f0f601008110b40320300912034003001c280c0301034485d94030031081030000c02c944000ca81d103a94402002410f07010900e50701e1082c0c108510216881c01c040607102080f2400742031400c107a1000c020001c00b8901190703003003c07050502011b00307602d94504011002404090059010100d801d006210302e055628152030155515104070709918005030030311003480e029043c40c0c2001c49840c101615021440071602c8203200c400601c0c51100801c0208807200000815403d4010280c1c8110990b111549e945c11700011001450301e903031049840313008214410045103c2c520b221065035070b001c0564010800d034002e4804001c00d81d03030402020451644207600405402504481c200741c8142c074148296030742c40c0100030142014030507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 206519820 1250 206518570 206518573
    0x5060105090d1103031e04150f0206010303080702010617060406142a0d23100b0f09010903081c06051905060304141501051809030405060a030e0a0b0126 67
    0x410300025501010400b14a0000d4103d074107000ea507501c04082031b0020015082030300800a018011400400d0401104c0c0c0f00354144403902c209000c4e002503454105110207410070500c040400c0c1468402c0d0800401040c0d411821400e40500c03595194480345c0603130341111103a00c0c001110440200390304c3c40e544680001c0411006046620100080c540100410794000c0c113410041800038009612460910480c48010142c0b05900201e049441a03009002d4100282400000b000480e006400711074840d1202c030001610342030410010390700f45800c6d810041039441c0128840c90340318502418558211505042400b83d942c1c2e8031705000d0042d00c40f4052103800281e21b00240101c0c10148000c54020b40f140094504140b20611903030700301209842d1180707d00618800401152401b0364211200d0300442c0400720b043d00705015003030350380e102e0303403040074000d2202244000c102c03070099200d1702c12415140c0c1901d00c95100c6103818801d4600074066a420602d1145a2003c0506e200030100100005c400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 206521070 1250 206519820 206519839
    0x1080f01060f05011103090604090902100507020d020d080c0607020105060a0605190507022103071202150627010801020d0e15070305040602160b09070504140c0d060f0f0501030506010509 82
    0x11a20b40107030045c05030b50f501c010451603005d616420001d0004245c82000000c55808030306c10480e09170319081d10303507003005814018030025a90f0350340c2c0c00c0c030150390445402180c82c0d8949414440360041d440b943e40207000e00030401541c5c03601908060300c2000e04541c110081030b01c8000541d00d41c084d114815800c040010011072109000d0b0300240105400207141050414134019460000c2e40e182005650540000c9400d800700802c080300521a8000d50000e0410400c149404074005e0200030500d52040186141a03001111140c01590518003420000c040079a10303680428081d501114458402910340b105040c0300b5040811402c0089003d140050710036281d100040300030303240141094a03181d03400c03c6501c1c0045101d038442c2d0030072841540180c2191800c1c1180509001207a031116025608107504a021408074002142e8400960543c0300e0700c4050780403125000f0402c07170300104150f120580000c0388a07e28801203200300c80c0241da040c007041d40c92600454841c01814025900a540d01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 206522320 1250 206521070 206521079
    0xc0a050403061d030c0307020315090d080a1d0c0306010b030403050318100204180f06080a1737030605090403030b040f1d010b0d1a1f03030801080f01060f 68
    0x50f00503020341c050b9070085030b40a040c40da00c0c1a0035644040c04210465100040d4032007142420300045201140c5800714680780d19085c4005a11111110310000c1003210700800261011a0745e032101101d0024030031110608031003014280d541d5100b0101035403191042c140001040c24030a0101c0e40b03e00c0d4560354a5040d81c0b964280c043c00c4040e2482041801d0058a516095090091002e40014500b6108000c41d600a00e0301642c210b0740c8540d010032640e82410001d03c401d1400003080e11881e0f0303120300300b01140d0520401c0c00d0010700403600600c81300c841c441c40100d51584030181604a00100308506a106941d4101c107804a4903188030301600641000c00050120b40a68086c02c4e5081001e8808900b03403e881140718215901c004040d02e0345503038000d0743d07010008248100074002d14151400c20100c4155183c0134002700409881485a08000c00094040032440e1b41005141032544200034400f0740328600500520030901616446114540070182850390500505040300c2c42c00c0444a9481d051 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 206523570 1250 206522320 206522333
    0x60b1806092b0f1101030b04060b0a12060503070609061101230901140a020309010c09300c03150c020d170a0b0d0f0506131509060e060a060e0c0a050403 67
    0x2008036401007482903401c0c03039000c103c0c04095403e00364403807206403484074280d400150480e014a03512500407880c0141c18081ca604210841c1e14088890034500e44641400d40404081c0220780c00882e05400f8a1000243c4030360000d821038142d0780a600c0704107840d100c0364201801c84070304d000402100c0040116026603809081c9506822500c040b002003200e0104030024008228141c0c0c981c9905a400020030441038400e1003218000c1c48646001e035403003840c110504001c0000351303c1008000101420b4141d45a12861800328615404020300c80041e90701c0c2051408044c009a01e60203060400b0059560544041a1011a04442c0d22444255103001c1d07824401d0040c0203040d404855521059400c5036590700e4007200269204030103134000543c10b803810608290000d040119040c0d9402d003580c0007c1c807054a60030030520200c0340020511038038100f400203003020240560300c5010b280c0c02d01c405000c181c1c00401c00c0e40c4e44060441000d40700c00003281040e1003400e0510000440601c000c0c00082c25 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 206524820 1250 206523570 206523619
    0xb151c112b020f0d050303040309170a0c15051303060510050a0305030a0c030e030f03030610030c1d04090f08070c14060d23130c0f0303050d09050a06060b180609 71
    0xf00030300031000c9000c031559441e20b15031040c0e4003034001c5040300c801004000018141c5c0d00092111001500303900400e6070382c0d030000044030300581210503080d0400e01506441407080e035148091001c80a140950b40707007131a1004040640e800740b100100e01a0204650524490440440703900600462902d200700030200c0d003040600d0400c40c01c00c40c444040081c0c0355010415080c003000b04070083c56413420810100f09100098003402818103040046110303445401c2420808691028007840750440030a00c001401490040e030000c04c0083c03c02c07402024032403000d01078014144500b0780c001d0031760703100d03920600101c50222102ea480601048440381a0701c054000d292544a031001070a00c0105083d000850a9022074035640300c0d0612041c140203000a000c1040c00414601c00345d0200681507880c002c0152140a002401300d41e240c2180804000e070801c66500566000401040a2519215284100d9008062200c09407406e0101c100843c038000c0d04031045040300408d80080038681e41c091400012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 206526070 1250 206524820 206524849
    0x181b060a0e03010c030b1801050102150903120c0903240109020903030c0d0201020c06010905060a03030f050c010f060501020c0a1211010207080d0509040e0a0b151c112b02 75
    0x481c484459065450034051921013258030f0b01c010800401c400d09006130000090004040503c0c800c00400090b42c0102e554100080001c10b4081c460b56251481c034614032504003650610f00a10041040030007820740607080300d0f0009c038244d4400402000c2e00301d0040d1491410038144055901c0100300301e5242e5401041d181c40080d05803400d100d403030400d56082c846860081000350350000703913400c2c0243d0184041c50241c0041c13070082005040a4001ca2034049071030100500b4030003040210340609006000340c6401c02c100d034000780310000c005100100a8491b91054901600c280c045400c03880c681400a10160703620340c40149280c03012a2118a500b01c680b00d1105d0660044038808107072020305110348920b82079030341c0720595a403d2403024001192102a04414a40c02c0100b000000070f180345a220b41002c2d10740c4040100310007560000b50314000700703c1c02034244054242c0b1a0108004407030400b1a40300c04403419201108260708140d800030701100d50a640c00580c0c0032040051500030f40040c5c450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 206527320 1250 206526070 206526077
    0x61309050c1003090c0b0909060904030c0b060418121103040b090d060b060406050415080c0d0c030612030c050d02030301180903090f0b0c01051503030d091415181b060a 74
    0x6007107941710480004615000000b00f0880000e045807282011a105d40c2c00c444103541c00c03c080c0c9031a84005290f4610840020640103030f8802003025540c1b181c0247d00300c0e5520010b09154101140740140300c0c02103503404d40010031402841500c09181c040b0030f5900321440b0290340d070718001101080001920807005e084600d580d030f0ba1040003054998a02520142c001ca03110980c0d10b40c101505404078071803020007030040000d81000c0099000211040d566040900360340401c0342c801140080c1d01a1a49401a60403454200044824103601440451040d8010001e4980c5440401c4083342c892001b400740708440c4407004004140701410b0b51200803018040c0c90306500107134490b00b607807c2500041d80420b44d04034005c951800c86410a02c03416400079520008019144442c00c04030340c69000f030380c03c91640265152040014001080a070001040ca9281a80c1c0e901140d407022221303a900a44203150300c3c40b5803c08401c925500002c211524440201220020180c04020130026030300c60400507040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 206528570 1250 206527320 206527331
    0x402040b041502070801020a0909020c0109060e0102070b090a110111030d05040f02100306210503090d06060e07050405010206150103091403030a0f050402060d0c180806061309050c1003 81
    0x445060801801c058940b0b075000d503030b5103407107290002d02d090841d80200900ea4410803001c0c0c0b1580c1c000000c402118403080d009030300c66411900c01c1d4014000035401030b00d2941000c15562040d02c3c194020042e40c2d115107100b031403d03110702e01d005a0b50031108070010300d880c0d400704407070400758082d00305800980340f00d008907840c0c030785288003000a032001607504079a4034005c4c2210204602d8225185400021179281c1000303409e1502ca21061500c804002c03117441d42c10045641000c1c000c041c0121603d481e006094034100c500c492419000400302442100d403844200c42c04503a203244034804440840d00141c0c01020280c070344980f40743c9442c180c940e00c54141136a80d010300000500e503240558941c242140603540324a001d640c1c0354262401615003100b41d62414007008010b036200f43c195a1013125081000582070402a815980c3d4603600d4001e020000b01c0440c0012079120000740b051050b1810748a85288403000300e0b0000585040e00c900600c250454941200381d410a4048040c6c010b0300d901d004102c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 206529820 1250 206528570 206528579
    0x2030f0a0f210905060c01090f140105010e0106140307030e060709030506060a03020a030b130804030b07020c04050708040f03090b0711040501080319050304020f0405070e01080a0b01020c010e040204 87
    0xd444140c400031500051040381c01c409001109101c100200050b002d01038400d40707031a00c01080c81d161030050364803440d408a8941c0070305070250321054600383c1c81010750703030301d05840e05010204200880801e070003507007841d001003011080903901c18100d0b140d98030752003100766840ca1100340c2c6030001001c4104243e80d5002c4c00a401034208045802465262203146c1d0683c1541421401c000b0300030300300c2e800764802820400068841d848804112134100c42001902d03115a0243d0018001a19010b421490045808000c3c0404490901e02580381d9808450500248400b44070640300200d402001181541d00081c0200f1603c405903400d45200c0d00e0210328264588a4003100e9801542040e00c0c940d010340342c48030f02801c061007502d003d4280180118140400e28028071140440403403803408015012020808540360204000280400200b0a101c503141c0038600500824a40300c025000403440f0010030200d1040344920381c0810810307030103081ea000c0c64600568242010300c1e07910380c000358200300015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 206531070 1250 206529820 206529823
    0xc060612070b0304241a0a0816050603090c06030702161a07110a0306150302010e03060f0103080c0709020d0219090b0405040b150a030905100204080304062a050d0320041202030f 78
    0x1807100000160118080d1b900710140030708001c56030030042d140d40c040400102c1001c038660f40d2034200c0788226200b039613a64440100c1414400100710580e00302d4000b03c28021059008a0384004c403641d2100ea01e0340b1b650351000304101040b180901c841c1040410080c00c0003040180d0451110307460042d00f801c800320750341c0d9150740440364035112040d50030101c00c40500456a100245001c8080103d00501c454200480300d51449201880001c0941c1c40018000d0100d0500b880002c1c01048504811503ea4994902090280d130000c802500703003550204000321030b40d0050004e041500c103100c0b07101c3e00303203801d00061200030b040010056602880081c01e00002401030002019610425600480c61143c18589075140c43c44e1150321010090042c8018440301c10000b05440c112021450b00090030f8000c140c4410052582000040081c0d040e5180c2d002807100004440740444510b980404c02c503410401c21141e110340e110304a0744400003c000801010322414050b10243e400103040d40c900329170441040d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 206532320 1250 206531070 206531081
    0xb092803110615030118080a0323070203180d030909020c190507080606010c05030306010e0d150515010c03020a060218060d0b03060a0501050306040b0702120c060612070b030424 78
    0x2803c540352002440a040a020781145d084400320084c2c080700703541d65002c0b44ca0045403d000101075844240b5002d840e000510a002d188441000c4031075820301031300094987d44550200b0b01400c1540300000300900b496400c01014a805603a580d560b14107180380500a54800009994240302c0c04440414464800f04542c04152088004110b032500e000c0003141003800050056060021a80581001c01d40200c2260780c41102481c000800d80004000030715044000000075000c00b25000b4150700510f503990006002d00c64005403440310994030001141c080601d48070040042c1c00000d51400000c13450b0f00902480c2440e040c682240000305404186a40c020701c400441d55030300d6500013105418180200b80d0415030408080c4034a41c10a40400d41d00c0714041c0004009040c3d000014074414400e0003850507100d281c40089944130580d40d980ca68844080e5035583c4204084000d4010340400041c140c02243c0c05000c54a04654032600c9402142c030400c1d25081c07690b801d00480d01e001101e18442e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 206533570 1250 206532320 206532331
    0xd1b050a06020705120102040e1602031c050601081f2102060f0d1404020d030e0f03160e0c13051e0d0803011d070e040903020a020d0803040b0928031106 67
    0xc0508601d00001c00c40614000e45185c44243d20400042c0200b00182d41c2c846d40c000343c9282e48000c21030100d8804c92035440f55000c1e0308400c103027900a18040586a80225025030426a111101500c5080c3d55524014200403201f17030510310004100310082507584070700d0307040300c56800c16800001140c020941d25400408404c260320b0f400590041c42c41058402e6805501c0154400b050620749540418540c203d80d0b40701605224090740c2d03699841d554040c000b0509000a4103540d4103140520003410020614020301e429210402c0020301401c005101ba5501d03141140a201005032912090140a40d650b0003200022004501135401035102c0f50312103208203208501955a07036140c4014494280300e88014029400156018462437550000d0f00c0e0032400c0003100c00007040580c2e40340903444c26a0819000b508040c40100e00000e01c1200c0018505c100d01901801900359038141a0903160b1546404106100c40210364442c90082000c4003084042d100f41800c135601150070520030315041301200c070f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 206534820 1250 206533570 206533573
    0x1302120703260c15130218011503050405060a090c0305011e0507020c030604031d0301110a03111303030c06090812040c0b04050609120a0f1202010c09050d1b050a0602 73
    0x4041e0790941000070940c0084040c4040c01e0400505040307054650b00f41d40c030714100120050340401c05c2101c41e0580d4a80080d802404803040441c0251100003440d002d02c102c161441c0c6c4280c44600c42400380c080c00b4400c543c00806494244ea0b180480d60041400c40000c0d900c1402c4000c0c0407001400c244073300248010200d60030300302510025800e01c10344400401100454210034070000e00d6480000d41103810503814240815003260412a0241c0c4001103020036900d03600740850300c01128407240c01040140720780c0e13805004519484140200610881610500c8581c041d1400c00100388039040801e07040e8800c1c1d030080340c0340b00c040c1c58101c0c1ca038000d24502550440141c0a200400090b545c1c010020b01501c0389441c1003e140030300050072401001c20180c080c00f4034902c440040c5005100ca04083c0341d101c80180d821075214100300c50702600c04204880550700e405503c1615500980100c0200c1e0001828088401e030309a50b034003d94002c00c0a0301450181800c0041942c1e0307950740340c401c0940800c1d070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 206536070 1250 206534820 206534843
    0xc060f0408061003080307110313030606090b092a0d020403051b0109060f11120408073201050d09140309130b01050702060a0203190302210c031302120703 68
    0x2407100d4140040580b5400140303000540420001d01900c0c140d1368407407404d081810342402d0088080d420352050b40c520307030170100d12000e010082112683c007090a035a81d254080220345005014400e00140540351030000072054421006072041e16042c00d10095500141d850816062804120a03a0815042211140c128000000d89807400d400c0c1d501c00301c0000d20703000c2e1803146401070113002c0f81e50210381c2504025a200522300034441c20040103c204044042035a50780d80d541608a4403101980218481350002c85402d401e1000000300301125003410203098240031b0443c00c0151101c5e444003100c0c10005481d45118800b1940e0581403200020381d00c0081c0d55140012010081d0040c03c076101601c1903840e2400300c400c942d910109071040b003075040d202203584003040f4809a2540c060f610680103800d40654540310301e070350302d80c0140400c00e0300905513054001001c0084001440700301c640380e6100c81c0078030005050b032400710300c0c03035074990f0010b4045807105404101c0a07046c01e0b000e80081c3c07142d44400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 206537320 1250 206536070 206536079
    0x5101505030105070309080414060408030c161403071202040b0a0602010506010f05030906070813060501181d0c01050f09031b0109060c0c060f110d0e030705030c0d0b090c060f04 78
    0x2805000e0340b029482c94100418113051f034138802c107405103014020007000c1040c02e04404d034076484219400ba00184086a0302d42c0409829a9501c03000d50060703002c0410f68200004401c04100a0341041e500000c3c06010750909140c4000c1c915000f40340c050341d11640310680000c8070b0301d40c2140800a0314407940041220301d4181c0015009041e846c56517400c2200c00c20400520a00c0451040c0e0007650a20b0118242e4031001070303411000d00380e43c6003d494030b86000300014401d285982c04507078070312181e10144111000307200c2142c0040d1903a84083d0031a000004c1600c80c40d8429801004401b502142c114241002d501c00300340b802d00300607441100d500708000d0005140d070b001140b82d0010300d00c5240007801c1c1d120075540c25a403a422071284105020646c8940b4001c2801480200440c000340011600e115003044002894241c200070424001e01481c840402c040c1004901e2008580002e031076034a03600b400c0c1e0744003101290018420a0f0f90b01480030031030405d5031981c0042041803d103010b01a00e6a040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 206538570 1250 206537320 206537323
    0x15040c080912090f061b0d030527150a0e0f1b030303010503101e181b080d0c02040e061e060a051c020d12020708070b0408190510150503 60
    0xb07070000401c40b1041c0300c8000d60750360320460030041c80000d65174540c450a422620740c050400b1070f0402d60240c0210001019607941c540d1020b84070b444084042c852040317840d00e800c0c414000c10903000c180c40d0864000700c136406040001203900482051000101308600260040c20510582d000c05d40a41003034800b000c8115004c01c00308a181d40482c00b45245506d094000381d680d101c3d007070090841d00e0701c6011441e00c11181c13081c4e400b45500750304402d100c12034803d907542d10110a00c410031980c01c00d040c81840090309070848020107948004c001802a100d00d5101a40c2020794110200e074026110f00c801810410203100e220300441c61040c000a51003040d141c40740284c0001030120b4003400b00b8140820450350750b46048290164103040c0314002c0c4000e400454072003032680c00090031503100001c01200f41381d0300150140844806070155686030381c45024200a51090b8030642007145d12a41d0341c803081032014405031101034420380450340107000b009511800c0c0d0740360841c00407080f0140c00042056080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 206539820 1250 206538570 206538583
    0x3020a0201060f0509070f03150b040612090b13080c0d0c120507020f0603040501020904110306120a05060402040c1209031d0904031e0504051e0f090403020706030515040c0809 77
    0xf0b078110710003242c1000081418404000c0c441420800e0350290380c1000f0b4040d81c884081c071000c041a1841c03ca0715a85000703000c2d8840c2c40f818000546a10390030094030b50510800c145241e1000c01c116403034403a05510040c0385880c040c1943d040c58100540c0752280390030040040c1e440c1c0e03140c48200c035084160600014450200340807100b0f02c8070410240c8010383d039034001114105004c407105500ca850343d060075402805804005074005181554081040d602c0c2c1000d140300310720854040001600c10455075483d0850780780000c01780d030f0190010800516184d0000c2400d40d8451900380140c480f007803440002d444400006a010441c4c030002040c10300e0149a040c1c0c212202075803042510b00b010340e001041040c12901391440b0089042184901620070800c0f140140340c000e1504a000886556041c2441041c1440503c9400741d50010300c480d08250000342e209681507000b43c254070b85011401d4000d000c00405d5000000368102401e1116a6240300b0366002ca52203a039440940d14007d00b81c54640300c1d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 206541070 1250 206539820 206539829
    0x20a05120f04230723190509060301021305040209010e031b18160c06111b0105091f020309190f030f081605070203120f1e070201080105120a0c0603020a020106 70
    0x320019000700070481c00180150440c0d20102d400c613441e4403110000c00a07800034650442c3d0144081d413440d00b01208001b0100e040e620f003120070148680795103003003600300d00c5454000c5842000001040120303260a6000e4000305106040a1090b601c4000000e03013880e05202ca140c40701407a183d24200742c0e090200c601c1c4940c1e203000180d043d9608211003206448403280c140c40b020400d1201a0404000d015000074000122910104da00c0e001c3c002129030a4449640507840558a0440098917195000549000e01c1c8016140300044141c10303001600a94001441c44456106400c8480302c4c1400705d0200c0622140568110750b40401d442c41c00070886081e0400341d40800c003024043c81540505404156501c0500f400c2c10341e0390303503517520101e8140407041d03007a0f0260ba03001142402c4202c020300700400d031401e80404014581800c12040900038080c0810180c00545100c0c014040c40c249100c007256140003803012a1a403d000d40c0d6107498801d0250414000660045001d1101e103409010714006003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 206542320 1250 206541070 206541113
    0x120c0d110412080d0615020f1002040e041b03080304030503041101090513020703110a030c03091d1810090311010e0303190b010903050a0f032010020a05120f04 70
    0x162420380d680b01900d1021a015042c010700061070820440c140d4803170401090302d00031003c0400e08400001e91207100d00304805c0b0050084000c41c41241180340300b100e040d1760303140e60078120644031500e0b90780180e045160440fa54011200000c408030719100080e41c41184a03980d003135a01d03c0d10380390200c011440850f040d814031407020402d01186c2e407103890801c8905000f2800507101c4400c1d0030200c607001c4052190440d140102002e48040c0b680c401c1070841c10a00039160540b02565400d40440b29110b1300d000401103110b01008504280c0501c0e1142d004001044c04a83c041441c40d4621002c50741490000c134007256684040c024030100a0042e4800401104040d42c110b1909403000000d03051104542000c40f0750f0f0f02178004040c0c0c0a28100f201840d080350442d45480b040c1e00c1d001104001c0f02d48213501240c00520306222a08a400e0010806034404010741000003050401c01c2c06900001c2540d02844030501989803120046021503114450110021015080908049a51000320461207202 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 206543570 1250 206542320 206542327
    0x90d0e18040311010b09010b090405011e050d0609060c030501090b04061a09011803050d020c090103120809031e07060b04020c0a0b07140403052b091a120c0d11 70
    0x3095680211540160903040260101602048a600501140d4070050b0310007150000410314180d1034029004001065408100342e98890f00b048407400b00d1507101882c0462002410311050403d425495803040c03080b40301161921969803031109451800001100296861004001011003401034800f900e605450402c0b410b070800e080d4541d1030003a4118a900720b140018441440c3c1d2041029400d6001c0711031f4000071142d00d03842c003903449100700314115005200303040c1c52000c185085000c0d54122940482c1052031180700711019625104020a1034000d404203026801081810315a105e080e1407a4ac0d071f0103075481006107080320031181400e06942c0228070501c60007207038101c0002d5001c2c1d000d030000d03d100c0559423884412181d680c00c0201030582083c010030000100b00f4006218014204014041100703101c00da0300d040c5010351896043c400040d05c0010401c24401d2b10200c0b0311452510101a519100c15400c00c1001098141c0d000ca031a15030010b00e512040500d80300301c03502c0c03200c3d04444924 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 206544820 1250 206543570 206543599
    0x20a0e010e03070902090f040c27060806090403090513021308070f0e0c04090f02070212060606251e0302070603110904020322060b0a060302190c030512090d0e 70
    0x9072a40f4a01031091060750008186445a68100c14806210f00040c03091160501030f0380007d081c01d1400e8116a55a4a2501d0b048c0c2e11b100000c5116099500300c1ea24005981c0e1413408000031020b02800c26410301c046188080742039100c0d95103000b0f1442017a02c000da034407075280141a4541c0116482180070741c10118040c85050b1580303056200b20b6a02002016582d140c048003031003a807003903620a840342e51514920000321880c6030094410b05000f211074550480400c1407c40d03c0304d40886125a000030b042249844802968007010704c455046032070740c1040c0074180e451901507488490680a4814040c2580c81019410024030340504101e2809100103054400c43c92031078007034031250320303c0b59801100292803082042d403000301000c9601050803102c0100e041480003400114400c2d400788050860104d6298024005c0382c0c2c0d021000c00380e000c5880c2ea030510849880c4006a0304030100041001085003905401c80464017608504001c0c045016510380060a510f803003180040c0200001c402429 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 206546070 1250 206544820 206544823
    0xd0506011509170d180801090f0c06050c0a02011b0c080304080f030a0215190f0b1003020a0806090c130e060a090c0f1805040905030408100501031e03140d020a0e010e03 74
    0x90f99111500f80110301020400984102da10300750801b00030340d8a410701e44002e00620350322140141e4000c0e80000c145540b200405c07181e911542c1d0404001754002220500107511400644a440d03007020060701c407105003503170786401c5a07120780d010f0742e5990300100b014890248240301400031044803074001c514101400502948a08582c3e02c407180007501d030400504808044500e05c079000c1d1300c1c82c804100c07119280b134a40c00100300c220b2005009180711440041c0003400b0780f088a0810003251210758007943d03040200042d012005060f40e40d161024028038100b81104072010000c0c02c20070004030420719100c0c040c440d15001507806074440a0400720981185904a148030f05800940c4c034010350403808407036a1034541c1085611440e0003526040102c070900501101030420340302c0e0036040d21030281116020300d0544000703000181c8610314410360003494004842c180f4401e6031113420542c085624911465400d070f082403c4004107950005803008102c0c3e031000e540201e80b503003424503054801c10704020a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 206547320 1250 206546070 206546083
    0xf06030213090309170d03050708060121020909090a05010e03070c060e01030e0709020c01050a05040c05012714030d0c0b0c07020301021204050a031d01020303150d050601150917 78
    0x1d00340142e4481d20030081c18400c5002c10060035494203821078400f00d24540550390611040504c002910f0240030a601a22039006c55000700d00c140d48544880c0e950310341c0c001035104403c900c1ca400c194200980b1945884984000f8801d106005c0035088200b140d05040d801d448508445600e190403c000c03142c00103450000ba40d06694883c07030800c0c0d44071019001600282110030605d40a88103900e40003601e81040d40040c608041d0750b00090216440c0c40050106407101610300500856962206024551007190600da01c0c802055000c08611070046c00c0b400100142c0e00507007a2150f0707a10f85a1031600701004031414600c0e00f0310700002d40500c00d46481104460180500303024010000e001e03800e543d0250144c0720051a07403920303c0310908103864002c0d5203408a03441100031440c84203502801d0301d104000c0e0742001c030068001d90324681c0c070912080d502c00c0400c000943d018050249075001b094080201c14060500b0941071602d800f0040409821080e241d44036510000118005407502400850781 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 206548570 1250 206547320 206547349
    0x1203020a030c02030f0a0501020d0b0409170702180108010207030801080a0c0614040302040203151207030f0602030a060305010e0c010809160e0a1d0d030b0405090c0d0618080d0f060302 81
    0x1d40480242480041e0030030384140780b00c032501d1042c0c6c541071061100640c0103005c0f44c6c034484010030030400403034188000e44403401e00c09032440d400d08000401965260005041c202c2c8004c0080103075950241d409500003c080e00030b1000d50798049071503420542c001921901401900008000c2d046031556000b41f54a0103001d00c008100d10195135403110b005d25025a0007a5a00401c10354480ca03024407102213602e0b8441043e0700c036007503681039442e4580b00070507002d0950360001003466000d0015115100039600c058108503003d07548071340000200e81c2c2846200f84610070f50004e00344001c0c07540b0005102c10342c05010040c41d82c00c0385641185522fa0b04c5410f004442400b084140303d903841201c1800104040b400c40440403880d10443d000b40c034008200000080241e4508014004044040c001143c0b01200d00b05e026510611134562646018074220810b21300c070705070104042c48103281e5280091928a8101c48400c0d0204160600300103e0040c070f40e00c50180c41c0200903007455900003ea034002842d16 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 206549820 1250 206548570 206548577
    0x17100f110913180b06030c0d05060414030d062306090f040b040b06030403090f090c080f1008030c0d080901050702030915191e020609030d020a0507060908070203071203020a03 77
    0x40c00d2202c020030350400c0b020358126050700841c100060034038030f04900302110031074800e0181c1c41045d040e52425110000301580c0000041005039600e558004481803400960000c61200703105200b0801d85601501001d00811141c3c036410401c0d0b01d817008080c108411009100780ca00784000001a198640c40c844108400c0381e020844200c114042401001c0b1545080d070083c40010800c0b0615030420b400c0030480b01c241c0c401d40d40f10b5036030b86485c400302c419103180c03040098004000310750b1160050444a42016400c449100719590307841541c0d145078420f1a041c0100c2d00f040f584121002c0c1c02000403903101140314001e100b01d141c60310000f5182d201e00c074140c0e44580f2022106200c07101100041d1281c13102c900e1108800000310316401b1b4091544480600a0405001a2010240d10100b603050050403100700850405074600022000703500203184082c20080c013800400007103480c0d4018420030350b02883c0101c0d5141c1c40c0340181400c0040581100400400e04c84110000135800038082c4030b03168240c42c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 206551070 1250 206549820 206549839
    0x2010e01050a0e0406030602030601110f07120213060e150604080a020103021c020a02010b2803110d0c170111030403020615060c010504030e01030c021f020d0617100f1109 75
    0x2c09031003001c11030020355045454004040100202c0c0c0e0f0003540075800c242c840c00e0900e8514803031940e48401041d103202d110381104404000b030350315880551456902c024280307144140f41c4c0c9284002c0381c01c0c5510079170612300c000044c0f080070800610344c01050402902c01c0c0346842d083c070303a10b50b40c0d0f44441000241055800180f03c15040040354001c03030314400c01308080d5900d500d600e1000780030b04420f1259511905980c105100302000001d00854184090305280c800c4074a181c0750031b041881314079159900000f030b00c070080002900d904081c0d4060820038440d120844900e440c482d003101d81c4a0308201c2811410001d10001c81d03000502d09a11500100d41d10001034021000b0031258001c652041701d00d036003020b0600c010190040c050045a54080c0ea08004c00c54654004980d1500d1404070b0362482a080380702c4c0d03440a43c1c16002001c0c2940c0c489008108581e590012500c3d20480079185a0b00f6000020fa0007601071642c041c03045440c40a01c41402100070600700c5d82c000d449002c1c2c240e4032618440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 206552320 1250 206551070 206551087
    0x41209030c0e0a0204030c031202010b0402031501080601030e01060806040b06060f0d02130308210606040609030605090c0306090304060807020606061b07030c1e0f121b0513060305011802010e0105 86
    0x50301140e000c0c56207d41d0050050707a492910a403401041400240554207001d4a42540e0403d03200303592050421501280c903802c4180015102d1210103402d040c10113071600800b40b14a042406460010301c410750042072140780034280100302ca540034060314804c60b8104075940000d01d031401039806120b025400180d0b10404c040c2e0314560100e55600003040341d44041000c0308082c1d11749800540340036100008110a80d102c504001d100c0c4201d010744400710b0540039090010a4041d403080e90300c02c4c901c900300c030414502440041d240a40440e4141c80590002070103024080c4c0c03002ca4213400403650b00007410b0070f042c000300190711401000e041036052070a522000310b000d08100b088000554010110489080d164000041c02030745006034100c07040300b0114006210340450380c1c3c40007240d41004c460b1540d07a800382c3d10340c2c65252003000300300310500210750089804c0d9203000310381c000450b42600000380ca9107076207002400d44003486040e08001d254031524070050f0741c0105030300d885204246096550350001c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 206553570 1250 206552320 206552341
    0xf041119050a0b03071101140a020904060806040b040201110601050306070e060712030501081b0306011403030f040612050106180b0d11030a090605090304030c12020a03050a0b041209030c0e 83
    0x140d40150342c40084210005a0034001900950143e40603642d02ca0003542d0100d4014282c074040e40c0c801085490305400200380110f2035020701181c0310002e101003100c65035441c41c5842c0c4601030391309903940c54404050204540e00302c1e00c500c61402161000d40002e41c5400002038403031400500b414140498681050402d40e114800c0b0740d846a445400100000031003000240100000d000b209098411003a0032890540401407004004d40003c00502d040d030f0170060851602241401c07211f42511040c84404062007600010f04040d241e50740e204102c0c001d400c00750800b51a0181e1007a0244000108880c14464030004920b054510340a041a60f9132414000c9000900010003e11150320b0007005000341608180c12408225001d018240580d480b5404100d40324401c03840000c012400701c030001c0000c00190070f02c1070086400244004002d0f540da0300c509080041a5608075140505182080100a030741941c49900d5a4030340341c0110404c0c1140e0f91281007001d6400b5968000001328001681c03040c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 206554820 1250 206553570 206553619
    0xc070f0f050d0206060a0b070809040209030102120a0f0f020c0c0f0f040e070f060503060d030c050307060203040b040215160206072901080d140706090201022a04050f0411 75
    0x6000d802c81c0c0a0501620707009445540a8070324500c9100e1100001640c0b8100c88180c03041d190300001d00300d1515800340304000c025480040d050707426540a01081515071210081c0c0d900c9a08458808900e00d2100002c04e000c0320788203545e10500d103205100203511394200280c100d480900035035842d481c0e00105000201412050190140c2c46814004050700c0c0220205051046400e1340c443c102e45a81c03901400d4515000450f5403540140450310000301007485204080c40003405582a689000c8450311a04c01341c5e0300032a816600d00c600003040c0700031810074004040200a802e05946d040c01900003801d5a108615130000e40300e00404200c401c20300458100760052020152a00e144490300c13180506200d0809200f1701805004042c1118103607402850006140032074807101c1441c02e00a60f0312400208040e6506904520440f480301c0c1c00c24034008500b0741e00e440508400c504e46003d034800c220030369000405800b80b07100c10320107100006200c03400c0341100440131140442030501003031200c1105d18 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 206556070 1250 206554820 206554823
    0x3090b010f060219330203100302030c03010509061b090a0305010c090807060e01111e010204090c090f09360c050306090a200d05010f140c070f0f 64
    0x200040001607480c09036a079040c122001a003c1d902d0701492454060580010410041c0040c0d003c0040302d580100100f02800c10500c9101c600180c000d280d6031801c0803a007044030079070580d0040e00700500940c5010801a01c0d40300d4200c000340001e152070906070741c489a0152800d0550703090241414204581d54040d602c15007005002404002e0352401c0c41c1e8042c02c100c03400c45001c1509504013013941040400d00c0300584a180c0c803040e540840742801141c000825800d241703a90700802d59203003000c0320140c40d2902401c08a0713001503201d03400c0490f003038101c0309011094400d11082850401039108024400000c9440c0c0000c0002e5511803070211240d11242c03200000e0035000510840105240c12905c0c07034180e24040c1c2c9190b4421611001416950b0000380c2c0c00d8146a400070150340d00086c007066040000c9450005c81030380380f0500802060001202e040100c41c280d4507440684400c0b400762042c0d0003241d0300e20051103041d0230402c0001711a4070030401c0140100049141920620030038000208045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 206557320 1250 206556070 206556083
    0xa05120a020703080603030a141602100806120c01090b090102070e07171803070f1113060305060f010312050a0203131509083903060106120c18150309 66
    0x2031034041030540c029803200908601040c40c40012800d81c1c2000000e5400501d10b64885800b038200d87c442d21a0250010780f0b00750980182c04004d40010b072542d240c402c0d100d40c80c075100d4184606064007003000c1c504603011401300c03039403141089000300c2c1e902112190403601c40e0440c081d55414001c1c0100d04040160700300c0c100f0300c41000c00740070003030f80d0001d101e80300c42035440480096a01d4060784190b0340804075462203401c8d441480f208010841c840308100c5414800c4880204da0b9840c5008560588500c0d40d072818800c0d90b0300000c0061040c00d01c48298402d0b80340304000780c0d540c116034901c00305500b64410030040100128048072854002c0080b140f0324003150307000c010019034480e088000c040340c5001c00400030344480d50015001070300090b803c00c030070401e45924100c00900c404440d81604580043d11150b5495048805192070500c0494083c00280c0d4500d088851a02940f00c252032052400004126003071030f820700c4210303580620700140e49101d82092200600c80b0000c4001c0d006403000907155 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 206558570 1250 206557320 206557357
    0x1801050d090c081b0f01201c0c060e06040203060c0307021002040b0406020f060c1b100c03051f080604110316381206030307140619020a0e0103020a05 66
    0x50003c0060051441002e610031480240403a43c28098424a0500524082078180c1e10f00c221041000000c114210602811100c04400d414007040460b0102840f00c80031581c1c4a00700f105016084c003a80c801ca20886008110509003513002c65030340c2100822045200901201040d0b1041c401c0c4411118004006c1c030a5450b962203441946440d4060311480000d1b115010111684800c08543c00380b0491011443c181004110214000c003500110010309250040c48201c08035500988112907910149a0340000c50b81f0b480840e0117401d440301688a010f2a80c03420042250071f4000070314951180c0d100c20710702d820011440100345400c62628003020302046900000c242c4403c002d0f507403481d10100c1c3c0e6150801805201c20490308a51044c0b54440e41d420400000c660030103140d80c081c2d042000981220b24100050300e40588201c0130480348041c0790094820710a1072040d14030b08280e9002c008070110320300082d07450b02420b03030600014114145a00442e580401e54010002e0781e0b004554072125404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 206559820 1250 206558570 206558579
    0x4140601080d120b0102100b0402130b25050c10090b0c1c050421050a0804080a060b010e030c04090516062307032109061409060703021801050d090c 65
    0x803103001501a000c001030444030304803d51251030084040c2c034130041e00645030407903d00250300b020740a4000b000d500141c080000030b14001e00112071074010403003400415203c42505101c00709248291001c41881e118024895000c00e0001c2101d40100b031080740c0c000118214440d094a14920380c2d48852504c3c0070110b500302c901c4e00040b82d61000c1c00d1240b03844001090450f9001e86041c0500c2c000c241030694007455a180c414000800c5506d603d0080d0f0807500008416030390b02105501a4000d050340703401c84540801040040e0003541507a0f4000d090010408903c0301c0425518201c101113188507030384405a000900c40b040c024010104500610b8140c80c545510028140c94227004246c00c02601b0b8020356496805c4c090140c85d00300d80d0654800d50345543c400f107030324281c442d02c0925009140d590311035800050501c1c403448505194a80c071881c8949084203013142064401032003034007810700401011004103071084103d42d002d0b400742402ca07141c02d0034403841e000805054200030030b407040c00b601c08103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 206561070 1250 206559820 206559823
    0x15110a080f0a020f06010b04050d110904030f031b0c0b0402041b0c050616050319020c011a01120b0918160603050f1003031403040f05060a05180304050901030206030414060108 77
    0x40c8442e0398003203441c000080c45413155540024070909110300c41c01d10003444a46010465125940e008180740f42c4100d4040c4000750310f4103c2900c0480229030320350410070410380c250140c0003400300b482143c01c04140c2c64031070281041030b10201c000c140000701c40000b41191345a40c0030021510091102d18055a40302002420041d070340c0001340c545104100010b444450480c0800c00d02c07540c0c0e41d640c20300f10b450361001d003445880851003441500b0340900c183c03028030b9024811201c1f60280184441810f000600014007a00941c6441cac00c45142800c0010704541c849d1160550045007a02c1d00c9203045010954660400c01c01aa060700000d070040c0000508540c90f81106028401c1c40790f520800b0b445002003200f000b0f00c14800280403422044060501d0f118140c0510380c018081c0284104e84001940c0f09400c1000483e4a2145555100188070200803541100c40e04041c01100442ca0141480f0001d500d402c0f05120003442020001300140c20080d510804000c9405007a0031144079503116503146 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 206562320 1250 206561070 206561077
    0x10212100906050d0218090f0a0f0606060206060d080901260114061306140403061401060206010b0702031f18050304080d09031101080606190809120415110a080f 71
    0x1403805a06061000c1114071342130f04030003210303940108500c00a0507000084444980000d0100955000d40303001032503081c0301403110a04031440f91503114000446443d205084980e190000c0007150f1024040020030b0722095000d070b4103950000c6d20f0507120404000101c4070003441e241d184204104c05804414880081c0d043c0c10305032840014910381c0b22003480180100c80c080c000910030490340419040017200d000369000e41c503051000e0721045c40d01d622912008203485080301d0b00c105065909c801005965414050035024104921005192082d6600000e80da00c60981d030021482d0703075581c20b40a407510f0550000f451120f0b0f0780d42c82610501241000da071250800e105421480c041e0202c0902940c0c402e00c0c0a20540b076001203000c2610f68440c0045a0190000700139030341140e0100011a040000c641000500500507511101e5519001484d54184032034190b0200c0340240601050145070000c01001041414910740744c81c18041c3d6a480c0b40c904040c540004c2d2262800007401e120a01c42403005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 206563570 1250 206562320 206562329
    0x1201060e010603090218040c050d0f0507060509220b030d080103050d080f0c0309102415020d12090209040f06141005060901020307060e0a1401020c030703030e01021210 74
    0xd1001a07030703a500300303030140c4400c004025440f0104041d50b1140b12100326050350030074060005040f1998491012440c0800705d03241c1a0b903404d405018450030844104242405810285003039400c0c6141400451082500800c200c0750750004407402d0f1808826652141400318001812074000400100c00038096174000c0c00203403410702030311204a800500543e041c5000b8180607000c1c60a40e0784100c0050b007140c20142840080340650102034642121900691600820301011259082c0044105001240d815848051044850000c01c3c820700d07008160038140102c14240303a0350003c944c0341880014030030245c0096104691809002c10f205a203402d14000c10b00c940c1c2c2c10070407948005002c0c808504100d03201001c80d03441480601c47d50902002a210400041c0101c031300342032030780c0d4034602918551045c4850304d031b000d1000d800074445030009000700131184900840c5001d00c0c04c0303c055140c1c851450041c0c107068070740e5002c9017803d100b58101c0394640d40041000c42c450800803400c29240c02e29200d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 206564820 1250 206563570 206563589
    0x5010b030601060c031b0309030602030604090624240c02120f01050a05131101030b0604120803070f091d1e0a050603070501021b0d020d0b0403050c070e010302130e0c120106 76
    0x49118040b441c0000c400c6140d8154407a48d8045185684907006540010300140c3c0041e02c440c0d0040028203d405121040400d00d580d2000486518403909107101d020b0340a40d5003000d0b4042642200c900d1600c00000c0c44d51a46091588031303946001042c06d04000c0c0950103054403d1803d0208004d0045d40014010381500c0024013190b00d5000c2c0040c1911180d42d0054140200c0b40741d551807543c02603001e041d030010054440c0b800c0c69580c10315100e40d902c1121050f90750700f40020400c1003003030b07100360680c0507840c00d420300804460a25004002103000107404e0480394118402161010072a8120030001c0100d451076080d940c544888220302030702013680d01c64000d20031034801003081c0d1f0001c03401000c000480442140d1010181d020890b0343d290000c0709a800c003039031540900100f0140ca02651251f806134494661794601c45100300d03d444c5855000d007a03000c2608006000603580d0b08811401900200e2020401a960114440c100091428850b034410f04d11f0700007031401841034104100301c40e021034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 206566070 1250 206564820 206564837
    0x40e0a02090102010624140c1e010626150103080f0903010f061502070801050c0f0d150e01240f080910060f0e01080303010803041a0903010207110f0d02010f03020705010b030601060c03 81
    0x2019110f850107081031074103054000d084044011801d0780c9c1c0700050030030b0000010680300d41d250040620310a070001c407120260306104a03900014005c00c10180079007100a41e040c010340c51a1103140b0b1502603840c0440703141d0400110303100700781d50075001200700803225401044580e503600c0342c2d081d43c030014290000240c061503a00061502040c42000d104041703050320b0b10301d08407604e4009001c41d8000c11081183c0c41e50303501008030451001d50020003404039414021201d504008a401907c81007080c08501003007001081c40325254840070070400c00105007882030041c0c603103012490030012036107142c04840c0d2414000141501d1000150700886401d6002549540d80352038045881c1d200902840b682544200000c0280d141141c584c0a403803409424402e0420700580c00280c02d9074410f40b0103a5003040440b103903d41d14034000301403c00c039002c01c450440e08800d07030f03a0010301170071410707200d03482450350218444050020a410001102c4030080c1600c00b15038690102600c0d15007070b428107500081c0d104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 206567320 1250 206566070 206566097
    0x60d09081c2405010c030c080a020607120b0d020105071104140601180819080c0102030f0a0b06092803050a1a060d110603150d06061406040e0a02090102010624 70
    0x411400742c00e04825000304000707080c0300040d074104404d00d1085041001c140d0a042c045446000688005007156000d001d65040c40c9400910380214055840080d504e40300340c0d040640d5496a1426040e5030a00b002c1e910b0360030500b00381c01d030702d40e40d0462f054206042180d0030741d500310840c4205103e1003090b281c542c44022240a000103145081c0101e0055521441d14036864017444414000168032980540e0301e080d180c0c050741402c1e40c005940c0044c0800e02902030110702c00180c001d0600055040c0c80a43c180801507001441d10443c00c05a0404001045481c600600d00300800c407024617044802c844850055140400d50a10003013100428001c60b000821000e180100c0c0080881d600004203115250403482040910303032003d0124450303444102801c02994407800781e81c2a400c0d005400000b0341d1481e2080045e13001884c001014400e040400c824000c000d1158929078100100750401030302c078081c1c600143c1c01005580c014582000c0081d51401c202c11600c90801c440d80c880d96204420010745 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 206568570 1250 206567320 206567351
    0x1020c07150e09221e020307050423060604080a030503040c0902212205030a020f010e03070f060f05010b18010c0209040204050a110c01020703090f050a05060d09081c 73
    0x2c64025581c04603412000c5410b1a80c500400103d00c00c8800d400d0030746010380d0380e0305520300300806a540030410111014805529003484034800801007070307609020440e400480c114003078211a40c55000c2d54a07031404a207041d120700040c2c40c054400c09049440072402e9080280003600115811a00342561241c040b45c04511402a50100d0401d40c000e1b101c6018090700e140e000d6140144445a002c511a40105070110400d000695607406031002c0c40e0303649040000207051080508004c51184e041c031108107448580001155811a004ac1c2004542e00052500001411076a030124000710b091800101c0c80f61001e00c01068060009480400444040300054a20b5545590007071340c001040800100503040c150003103540310b4502c400009044201e0400c064013900b2150103c41c0076940807604004041c0c00c02c52000280412102c14140145040002003510400340940c1d03000b0800818600c8a060094001c2c081c45540920621303240c080a2140710402c51a00c0c1914082c00e040c1580c1c4003004a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 206569820 1250 206568570 206568587
    0x1b0b0c1201120c060f030e120a081e01180608030f0301170f0606040b030a0507091b090b04060f1704051005060906010c020f0105040503060c0d050609071e05090301020c0715 76
    0x140100e40310215444e0080940b040e4242074150001e040d1284004803c00344180000c804085243c1c262030303120300ba030500c0141100001004044600081e1060164003042c6619040c1120b010a4450161044900e01580580000e5020304074912010804000890070900914169442d440d0899000c0d560f0030507080c0c5e5661500580d038140c0e0400300110b526070416030004090b60001074103c034685242507813070a103010815408410030a9035203104980000c1014600203070800c01d8504007c0c42c908213500340314140718034810b51080c000e4400b518084603001d51000740d080042c040c0341501314500b60411580707545122408400152400002507245d16012000c14042c00040c0d4442c500c14580e5401d224440320901c1989042c0070090100280ba42c1d0b0070403459104d410302003102074940048045500c280c2d00040c1074948551650000c11401c00e80c080714070003041441c1d41080c02c03000e00341001543c80340704c5c0c1101e00c1c1e055400042c5a06030446c002982c03404688014500501801074030b07904803071802 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 206571070 1250 206569820 206569823
    0x60c0903030f1b1504031d06070b090105040b0a23060a050a0f0914090307020f01030f0c1706060c060a020315060714070e090c04050a022511030316031b0b0c120112 72
    0x32121004881c5840a10940030b07d0100041c00c014036001e80ca031501079440703a080b075581d145607440e00c081104101c4210811078000700025428404246081a4a032040f01d00b4a420551452802c000910b19510500d042c00244405030054003a688c0342d95404a440c0c56500036010041d0802e141c00b500c42040c054600c0c80f45091501031400c00225030b0030408420041c4041c98109500c49098044c0440c5510030700b10410100c1c0c54440140e0a9804207112441b0700a0100348600014000035440280119030154000d00203c1c00580c1c0313580d01d0f0807402d8401c08021150b50814000300d61101000141c4001d807010340d00704802c460301c0b03a994204070384004400700c400c885207821200300180d95017003035003080782c00c1380c0c0c508005070131308102d5070204c064055110213280518448801000034425080c0c5070600202064024610306900783c072805845080d01c0a00030200181c2280c6000700340c2ca0f90200c501d10b03d500000310510360030100c0d50b5081a0304003441d4681d411a82a0002450184132000b15000c103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 206572320 1250 206571070 206571077
    0x406140a140703031d0d0215011a0f0d0507050315030703030f03020c030904180c0602070605030105091e040302030d0e031e030c04150201060609050f03060c0903030f1b150403 77
    0x1511101c001ca1000d0700010411014075840e405503012143c80714180c850980742402c000c0501c01040040240380111040041c5250485880184854035110317001d61101071049140355502c3d4030208125050b4400c0342504520749280000307010015601030000c1d070003011401c0f4445160f1031802e003050f4a82d84c041c80002c001c900141c003c5100d05010f1b401514400841c042924105414540440c0076a107001c0e180c0803080740494240410030101305591800b8212030300c0185401401d10b0300c041c04e1480103000e058801c507e04400100e40010004141c44084030381d00c0314900340c2c1441d15029640c0e030001e00348448018149000c2036103103080003042c1c0d141103a000c10309001c402c000201d40350040e0f00107800300901d00d20402010910110408184206142c0e0b90300004229183c08030040c41103001d078200b54032a0030f110034050800e40c1d0005400c1d42103a03c0043c02903640350607400180c80d61003075800416a4400105821500350354000d01061001303441030a90380e19421689140d06942c3d811107005011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 206573570 1250 206572320 206572337
    0xf03030c10050c04080f1c09290d022701210903020703050f07031b05030c151b030702040b01030b0102060708040c0302090f070201060911070206030402060d09080406140a 75
    0x107140c030390704200e812011100f04545010785401e1840d00f8010340d00e40e9100d0540c13000301e41042203210360083d400c0c0f42c071444c9050030300e05052070409128101340300d0b14a2001110f903074502d441d0035100012546d180808007801c5560303042640240804110501078603450030300203c00e0043d2540189000709904401000c0d260200180e04402001045e840c03009800314403480d40084000382080100c10544c100c8ca20007050080c1c070314070b0700d41418085200f011481020402c0204400c0e20009440e440c1d107201217882900c440c0c2c140e54848440e01410388040600001484e80c0515501e012005001c52030007650305200001d0039800540039030705003450300c60040c1d1002e40010001403245800540107803084a138000281d33500e80014400103000c0d5501c1d400040c4031801d02c0341c00c80e024419036005000f03800040c8401d000303d8107107105900491301c0290080d840000080d0440d6140ca0889000030918107040200f420181850b0f410358000b40140c40110311100310510710040d5010585010340071a5031800003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 206574820 1250 206573570 206573593
    0x160302011404080609060f0901060302010e01030f0b031915020405060415030b0310270201021209010306030501020c0606150412060b0409060903020616080f0a02030709030f050c0f03030c 82
    0x600e0380d019181c41400d1031081c04003282070301d02440014090314007600102080d040124401d400752038003600100301680750100400c0180d800c219500115002400e0001e9101107059401000e050300d08403040c0c0c1400ba004403890300700c00d00b441c6080054010031740001d06070b80a07450a4228401c0d4014a40d20440901040003c02d0300c050102c14000d001d49804551083c005001c03d06e450a4464480318080d101c02c5070312907c0d480116003150040d0948020700c031607545c940020751a10101d80c003a8222050001d2180340c1c0c2d034081d4210b1070056500600841d520032494036480c0d00c1d56030039607000348626050581300c900d0031103e40659042da600c08840003040012651540d0050020140c010340041e103400c3d81d440030424520400c0b0300c250003034010300490710707040403998580d0050b50110024041d44e042401030f110070800c012580048440c500607a2a154a11300760741a0a060380020090007051000d001081004244502c44000a80c0d0320340c40c3d04c0380c80003010340740c1c0984c0348900703a258400b000c0b078070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 206576070 1250 206574820 206574827
    0x5060a051909020a05090f011d010327050102042d0e04031b05070e0108013b07080304051318020405150a12050c0f011403041518060e16030201 63
    0x8802401d140d255000c1e680e102c5104040e60801d0b95000007064001c03e81c42e02d5400c100c3c1414400b4002440d184404102005890361f4080000c15698100741e0349200c220250050342880c05520300e12480e0180541d2800e10700396010303501c940100e091003200015007038251141c0c0301e5030013140030440345101006800c0c044c00c80c0c50b03940020426420400c000c640082e032141c0d22406140210302850190295506012103d100401c069000c0d1580ea898507034613401d441e40d00000041c1c0c211700100829809814407488101d07821503240c03001c0b0180140b034400109200300100400485a0944910b24549039094500c0c0450300100c0d0748102d001040041ca42c010715059211685c008000c141503030031f09000b040407800f2800325070060701f100300b48007526806014003000013020401017140e07a40450b1600c14002007804e00e01414010450b803010000c10100114246d40e4581c2480608081001600c100c0304540060750889082d2000ca1500c100c8032000d01d0041100d018401040b400303070b41c22500d07550046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 206577320 1250 206576070 206576089
    0x20d080705040e04030c0302070602030306130e0a06050907030605010f05150a1e020307110409020d030c061107030338010e13020c0304030b1e071d0904030f02070905060a05 76
    0x3104000c0100400f140c064010101d9500440c0280e4070312014010b2450045c0c0b030004184c1001c000d540c414800c024185c2d6402061209407000c40002060b0380f0311500300c4034034007144140c1c0104214213000400c900b1607030016051040307038000c51040c403030f6903038600300e0703041458684c040d03140c015035500d030341c443d0030740e08840240308003402807805241c80c0e07107060b91210321040800206001a000014600705100c0e0000307560038070354811a0100015a816030000d207002a040b0760003001e001c2d0f044003e1040c0003240d4860204a0034080c078466403528645001070007407211084183c0a00903a1030f554206107800c00019880d00710384101c1200400f0039100540e401c02015a411b9481405404441102d045d9400a046008107810040d500e031030541c5032007401c44030f004001e00c0f202620006440c8003e808403d1180e0070030300c142800d4580d41810b02d0000b0440c0740203020f458105103418180b10806034814403c000b24a101e50a8a030240e803910b0090064403001d807606a480b4a40384e00c203000741d18025014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 206578570 1250 206577320 206577331
    0xc0b0c07020d0206031509190c020c03030415050409060e07081f0504180507030605060f1002030d0c090801020c0606030d0e01020a08031e0c03070311030601080a090215040b09030c090403020d08 85
    0x10b10003c11845000108091402c81f050480304441031340c1c00301685444d0264509271441c6001811591840c0804650340f8000d0b4850024490f84500b0003003906800f40084401903e801c0303406100c0503460701ca10940190040d00c840b00007407003070b60010704e9000740c041911201c0011240c01020b401e103480d0801018190500342031a10754984070f02c0100141c8200201401940320307280106d041e01d0072900b0000b500684c0700710180644500c00c030f0b150304191301104603851440c140d0b40004080c4640401110b000030103030000300c1950f1000900441c03200300051920300c1400110100c80301040f20000490ba101c202406050240e400491130340000f030340c1d9102569100c490103c41c11036a400021109030500c0f010b03110400322507000030510140c260306004004220300381051300c910354240140000e28425008220084141d5608403200441d52540001001c10b0400c51820703880707076103e156a8405900c1411111310074410180c2031081401d040c51003602c1a50140c014207080c0030200025180103800415 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 206579820 1250 206578570 206578591
    0x12060b040b03030c0c0f0102060c03010920041409060114040524070b04110d0c150309050f03040f0812030c0a0e040c0e03160f1e03050d0c0b0c07020d020603 69
    0x5145101c0e072810005003260440207001010340705d45060a0050b4014004205811504864204030030030760100308480c1125140d200004440203042c0010141c02103a800001401c04001400a05d0220003441c81c06101c10484a600c1951648001920340b003011a0003190880ac0c240000c2081d13240200703544201100c018400c045030705c8028008030032075108002c00c80325003c01206010034007a11501c0c3c01c056600540d01810461402d031107d0460079410320030b0720080c3c10b0502c0324280c498440e4201035031455000085540071204c00d2441500d87d0494052035660f44070b1342100050000c80081da80c001d1180c120691490f5032103507070f00942207501c03181405041c4034001c1840034081d223940c032414580a040f55661020501031004040c244a032103424501d002c140301c1e0080c041087c3d002d00b07000456580c0c02103a072076030790034114000b0011107030751000d0158003920480700e81b06500040c00040040c416003903117100c0e83d0341d403d25560302d0007103403c0603400014212900c40141030040c02907400c08280030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 206581070 1250 206579820 206579831
    0x602071a04090609060f08030c030412051e0601060e01020114040b06060f30091c090e0109050109110703080a0b0d050609010f06080106030803040615080d09050102100612060b04 78
    0x5822000f070f101280e12141d480340d502e03001008010310000d0004060400300000c1c514010b56407440f00d9990055000c2c84a41449034880d0300700308101004401d0b0322982c0d081e1003400000e09006401e440321824850100031a2181c250795000b507206100340312941c828a001c0814035150341c2c980180e0b5400090945810080c00c002c04000440f054001c2c04903000c207400608034070a80c03184902c5032011400000d8110203007030014000324000204480c4805029070b01c542020b5000d03410b0803904c9982d241e00c50440304070520008074216615030081416542c02460900010140c02c0f41400944a9403502400084c5182c0208190301000d0b000b0842030007000780481c008403213503102d07241020410b8410703040c240c0d50f0700348060641540e4052070f4018903745008003d00e42c61516052218840140010004c1d5610301c1c0855110307082540080103040140115144290705c450043c28100351806640c0c007502c00d0421050740010a40111001c2c1c803d040c0c0e24600441d003d55601018144d4407000550041d10350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 206582320 1250 206581070 206581079
    0x61f03020a09050403021905030703111c0e100203040b03010b1c3803030702060d0f060303090e1f09020703020106180b120708060f070e06030c03041202070602071a04 73
    0x8040da0242080000003d058206841c0103850a2a00c0880e00d20700e2011949130030114101100752821160903040150800358080400c605050100880a001c1880701c0c2c101c4104581c0100d84004d000c00c1035590f0f0407154005030050340d4030b0007648a83c4220003004c00040c4181000000038000040c44061070343c1c0c10300a00603c800581e00c00c01c0e07000320340c0038503400e4040196000881c1c6100903e0505620006c2d4440c40000ca5200d100f1460080c0c01081d001400c60941c0c0041e03405100d401480705002c018150701c924000780b07410b15500c41c0140d54850340c00814a1300b01040f106500d0020145030740c907001407501003000048c0d0890070040c0c0c1503558401000030f0a0240d045640b42c0e51407840300002d944544182040380c1400400712132000b83e489010244425180010300c607070000c000c0880700c4503560300c001d4102e9800300e58501a0317810100c08010b10110408200266000c0c901c5140c00d05242e60704110226680c407058818003005070b102c0703031040282149801100504008005220307141a486 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 206583570 1250 206582320 206582329
    0x14030903300403030e331b061810021317012003010f0906120201050702031c0503040b0f1b0d0b04051009061e090b0111150609090f061f0302 62
    0x7652050300490030303c940e403800b40c1c03800e03019591084031b110b03140050780d01583d91400c001c85070b0b00c14040024540001c0f510001c1d442c4159045940c01c0b48000c4854500d0302c3c2c80040c0150071003c07105420f07486401d00b0000c110347c450080d07403980c810082c1e101100c03074035084203241e40180078000d286c1030b95600c8000c41c220322140c04030840b01c1c500c84810340d41e803035142000054061903964400a0360615180f000d2110600c0762100c0c2c3d0030550240307403058a030700f0140002400c3c488490b0207a50310008186a018440d074224000d984640d0040324001c925655003400440c042100b21100382c000e002942a030100b00300c0b20030180c140d40991010000e105400d40004c1404c031034003074a1110748000300790010006680c2d24054030004e06011441d41e204030100b03c0d404802c0442034040d0b021400d0300e0b00c1c2c584406900c603040c0400d10000c004c085510442810310003808e0184103031100703402046002c0002d01840030000f050500c00300c40100400e19555616860700c0040d1581c000380c94a50310031a00000981d49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 206584820 1250 206583570 206583577
    0x2040b0409110a1706060915060a0f120207150507090f0803030a0509030c031b01023015010c0f020d0b010605040608070903020a0501080a060b0d02071403090330 71
    0x85403100302006107481c420011081c2c001d43c0104210441052011144013020a05541100040c0c4919582c1c2e00d031281100c2d000c000c2e0b02030160f000503001c140740c00000e038051100d00c00d551590311580c0924030b01c201008140d1181e00d01c06402000c10440420507146240c0c042a800041494064440c50700c4444408120072643d1000c00d00d6071011043c08440b404078071030240c111745d9880003036141076068020582c071b900400b1690250a41e41403a2030350808000c5d01281c000c0c0145a101c00da0f0722003c0c480c07031911030404068090b41c00014100003007100040e50031144116005844207090724060b99200d1184c484d800308101c0e0000541c1e8441400150089040390107080207450f4603455904002000344141c10084c0000c04000491204002681744c20b0090780641e10300386024100d603640c080080014244a034401a0742c0200010004c00c61a06a03004d03103801d920544150308103031441d441040e52401860003059141e080140c110b0340498520311060030701c10310a01082c03a80010038407006501e41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 206586070 1250 206584820 206584823
    0xa0c06020d020903100203090c09040c030506071e0c030e040e03120708090d030b010503040803091e0c12150105060309070305010f090b0f1b091309060b04050c1e0702040b0409 77
    0x2070b00450b2005061900b4401400004516007046085140c04194240d41c0c280420140c0d000f210483c01040c18090b000340d40c10050350f013003001c40c0c1070782c1000c003001403040d036900b400703520142c03983c010442030940700358020803c0c240c1658139242d031441d001041000500080384103904a00c41005003010701c945030140b0a10a81040d21006445d00c0c08100b014108505460307401e00301072400030600c10607038005090300d801c83e40010300350b5141c0e620145003914180109001500c0900240700b1801150b40010340d241041a058601541c0c41000003981652001a02c41103900d0141c1000184802e04009000d107a0061010b0111000c00c0d980791142030071500ba01206101044c1c549101405200c2c05a0545070004240300090050f03182c090b00d0b01e07400b100303540c105082156000030300100554417401c03144059480c40504120018807490100000c0a482c05058015400c02c0c1c0018040c9050304e05a801c4071540500c0c54400071204402c0410541c000902268041e541c0d52040d840ca8550b80701c0c60240a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 206587320 1250 206586070 206586097
    0xd1104051812090f0a03080f09010314090705130e03070f0f1e11012606120316050d020303010609060f03060f0e090105060616030309080c031c050603160b0a0c0602 72
    0x3c10502044c460540706403c8028000c8030807101c05c00c00100044205c0707480e525031000a0340c4404100004a003c0e20500c42183c043c00d200d6800d004500c80080ba201c0e00301d030400c0365861050307241c0581450a40312011141059600300b40503840c0402c1c0c82101601c00345100b98601842a100c50341c0c0e80d2200b108440d40082800029203200e4204010394210403184076090800c2c03889010701e41c000e02a44504075006c0300880903800c0c01f0818a0b1240e100c6020085030140680343c40d1030b8100140014031200c140155098032a10749080302080c00401124142e5070140d50700c2e454030f800c104040d54104ca40301044030800d80e6451000480313002407802c11002e090160346403061400d14101550a488001e41414451502002010141e5a03401d00329490a54507090100b240d440c10300300f6203111f02480707100000c14040041c000c0da03c14840c4100c202400c01d1603400300629221032003403560b00c5070219042d00e1005145001849100d10080c06400040800e00e0400904400703035940200380e0708540d0011180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 206588570 1250 206587320 206587327
    0x204080d0908031918030203030f430804050d080c100501050f1306170a17090108040602030a151e0504050408040603110705071d060d1104051812 64
    0x550300c46101d800800860004604011481c0d65590b0301070900206082070004194201001101492419008580082c1501d441d40b2960242c0041c80e480152091240c24600d00450181e00040542d401007040050f08682c60b00f000608000d100740807400290344500041c00000340a81d0783c01d4a034100c443c0303c2d013a240c1d141d810307100f8000d151a108140b00c400d82c40c24200140700030b440f9441c0e1051a1007003292001b00c0000441c11400044c1840d40013021102c0c2420007a0360a6503000413001c03040c51180700303d1a148560b025418031180680281c0d50b0000d00250003040c0440c40703e401864010201d6000050f01c8a2028000d0460350001d622581000420080c0040180301c210b0940c00140f030103440901c028038040d900d00048d4401c900945090590340d29044007910112000d4a105c103911000300c3e005c0036240c1c801401618101280c852200d03600e0400a505d03400c004d503000c130010780d005412071800384615041102901e4024030041e00c2c0007a81d00d000c06a21420041103c5000c0070100340d569 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 206589820 1250 206588570 206588593
    0x1202210901080a022b020d1406030c0303030103081801091502060906060d0213020706110d06090501050d020915060c1501080c150a03020d02040504050106110c0f0109180906020408 79
    0x59800d004080c103000c2813041c412601c070702d8080203500015442c2d034071200c501d100c4001c003000000c1c09001a80d088507887c000d211407a030300100c1842d500482040381114416042c003801c040d0740e803000340070007408828107004080800e0703a603c410300440d91050500071810341d142c0440a8081d0b85800003130700140c1c40141030204000c42806840d410500984482040400f00e40100c0c00081c2034641140c0f506a0004581d000e0180b180d012006c0000203058023590f030000c01c0c0d004000352602e40944082c4629003000003a180ca0008a43c10400d580a0300340059540d40c0c1c91100c00d0220400103042d0400d00400440c0760b80001440803400a078015427a038510f650424620728a804e14042500e406070104a501129070784800302580c4500c1114500966240d0344100d902c03010307009960005402600b414000f2036010780001e00d1000500141d411603100c50800001c000d0140c5d0040c201902041d1000c600f030082c10f0071a102110b803d00348910101da040700690300c13241240e000c0d40c0708001d5034011110400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 206591070 1250 206589820 206589827
    0x3100602010605030a032f1e030301031a040c05090c0403050c030610170715080603060a05160e0d051912020a0302150703140901020a0908060907031202210901 70
    0x10054411440200915410600071075a100ca04020160a010b00c41d04810610807502540c3c055102c842004003c81c041181d1845564009a1302e5070403031480304070b80070400000b00100f62070403242c000762144014a58502560510700000c0c0058449000342600031809031120031038240100300c1c42d10021782d200d10350b00b00f007405c1905903402c480c4a600101c0a2252401e00c007201d44081c1c420702030a2004095003405814581f0072294070074503040c0d035807003400c00380319411140f011301c50801a001d031601540c80441e00411500115030201c034080300b62280045d100e1007168402010b400c0079006c484d01d18166103402c0e1800c415030188907070001000940801f000501d4640ba042c0180c00d00080401c4505533801940300d0f2210300d1540b242c1503a48001882541c441d030000700b0450550130b04e02c1c0090401e41c94240c0030350301074038140c004100d4103440010000c60020300c192141e00108090044182941e0b5105011402c0c0c500d00000c51040700c211010aa02c00d110b00e60268140d2600d442c1c0d80c01d070120014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 206592320 1250 206591070 206591101
    0x308030109230705031017030d0c02011b0f0309080730090e04020f0916090b250f0b010605040905070507050c010809010204180207150908040b070501090602030c03 72
    0x80440181d100c0000800030b888900607003160150030120f44035600c0fa80c0904c1c01e81441d900c8200c1c189146100307442c0d82d50000c4020b180c0c21440c1e000900c42500d0044040c4d00f40c540d0f07110034542030b000300940040c00700d201d0010600070100518000c0303540c2c1040e840e10181c07a04810004d480d025150404861820010b4243c0007203449051400740c452030a01c08050484005481103035031100c00c10001404542d215982002d4000c0014080c036054100042091801c0032020500350109031003043c0072401250602c11b0f80d21400d0442e030306514203041003400b480305000340c0e40d0844121501d2021480051482e150060180c032560381c8190312a854001000145d40340a4611814020308000c0c21010407404541c001c80c0c040c080c02c112003d070300d0740a4001c1c0280f25680c04075480c0c6030b01001d40d284541300f0f500241007880c026004032a8014508826200b103e903001802080b45908010401c9800300400140403071034000d000004121885840d503c0599004981c2071a407990004100700c0c00c0141403001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 206593570 1250 206592320 206592341
    0x2d03071109090c090c0d090609050c0f03060115120b0a030b0f0a0207080a030902010e0a0f17030301060503012919080a0902060a180f080f1b030c010302090111070308030109 76
    0x803c030303210180c000319004010180c44c01448800010392048a20820f80190304460351180080115500c0c90a0060326607007035052a80c4111014500d0110714a000980c103410b0307030400040200688212070058400c151440c031305c2541d0039214200070b1041d681c1c41125800550040341004203900d01441e03401c0c11404000c202c45003d40c4140700b00c4011518910a40c0c621116074180012864401d0006139030142c0003d0205d035101094800209155198220f00d90403600741e802041000c00f9035501080d100c1c0424001c003800280c0910040241c10b0f946581c03030992225007a0a0b00e98002500405504c1e41d020f90684403000b402102116444ca60000066a00964004041101e01c0599000800300d1081d1a514410040d00245e40c81ca115101d60364400200140d16803070b20300030740c0d0b5141161615901100d803007003402807100324000d01079841d07071070302d4403050040150080056500065000b5000ba00005040041d113000c40b9910304410025800076502881015403298900b84901040d9400d0a05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 206594820 1250 206593570 206593573
    0x6070c1a030c0715090c2709080d051008101b05070c0302010f030e0313062a03120e030313060e0d021005220f0c060f022d0307110909 59
    0x1000801c0e074000b001e54111a6001d10308610b116080c64030080600304c0000003814000c440c410010b070320710f42c000d149410180c10b00103106100140061040482c0d400c04009000154108402c0c640f40200381d2056a002011a0901020a0715030012510f08141030b0b1454010aa5401810b1a003d10816000c02d0102c500d250040c504081070b41d504010307100038440281031280700d01d843c1c0c4941e070082c1c002c40500301c0010103c030f464030071404450104400a00c40d82010400041481c5a0166580d0451090400801c0c2c2410560599070b004c480c481613140f03008440d0759030343c2d45104003014140010b5000b61400dc203c00040340c0d0500305203045410000504100381d00000f080f2102c99004270b408420010307030380e4001429950b0340040e2004000e202410780c01e00708540c04d00b801003264028030341103c0c40c018170007103681944482054076107825054003407002d031b48009201d44941d45040202c2406401b02c03509003c2421604a4040c9581c20241042311038082c0011825010300308100102d44c070880110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 206596070 1250 206594820 206594827
    0x30905040c0c17130f05061b071802070c062f0319030b0a0b03010609230405010803130504180602131707030213050f1305030408070f0e160e010309030c0206070c1a 72
    0x180001c4d1f19208010b8006095403009103420780e140c005124540051001040030b042c3d003070301c8219280003503010520858940e9141100407c419105092484101d07840c81c0e02e03854101c424500e1680110a4004400143c3c4020400c9a0408aa040900c0c10034600340c0c8001c1403140c0b8000400c0f00d4188241c001121642d03007440100300b0a5800307101101242c80e44400301c126450900e07a4402e03c0c1003241c3c0404d802608060000403621400001080d90151100358407000c6074941d0104401e881001201d861115001e0507a1004580303184c1c000d107150701146c624040f50316a00c0d04080c03100f0780304419409040d00446010415810001c090510980b2508010031882ca0565850380e50518090540014241805451410030108004440190040000700c4441d281e07280010700d40c1804c070380100050610f01c607000c2041c40c1c5642c1c40c000411091900c079108908420401180281007101080d402c0060b50500710016888010003040d6843c010750b22180c89a081445100320b480100c1f852002c0d504042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 206597320 1250 206596070 206596079
    0x601020606031b010203130b120c04060c080f070f0b15040501240212130306060504020a020c04051e0f060103051e04020409060b060c0c01020613030905040c0c17130f 73
    0xc20007095083c1e050000c60710000351880102e25602034054011500689601d02140140c4510081c1c505000104800d522640da82e54900d04240954401c6c4004078075010492000544d080010f000301c3c3c011924820304050b03450710341400d030001c6c2032002d4400a01041c284800180b02d40081240d03020b040d9002e11455240c0f40412000302c0c1c0000e043e40c21140b40c03007c1410041d200740140440300c0e40030303d45242c4a14103040714044503022440308460041c504000090181064000e0354050348258015080c540d034083e05000c040c110090a06008a14005d28840b00e080540185800ba941c842000c60310f0f03103048000581215806800341c5c1d0f28a4a0b100d0b0604002c40303000c50580d1103030303060700c01140c0074001d4a00600600211100b040d40180041900296140001524580c68000340d0032100c95803100102c50413222547c60000c4c3c00a40650002c3c4024103042d00191003400181c82c024881942c0b5841d8043c00d051064a24942143c00103682e41020384072004034809072890702e02103120141360 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 206598570 1250 206597320 206597323
    0x3080a1523010509060c010501060e0406030302030a0f020304080d031505090f070f050421030f0509100c140610030b06040b18071806022a0f130b060d0212060102060603 74
    0x4484450701c46080c242860005901c43c0e02512803241c3c0140a0035100e05030040da09010300003d01885d40007415403a41802d407032030640910402c6031b4042e0080d602c0c041c45210200d600140403080002584802c103c00140c503c401c1100003a04682179800055150240800002c0701c00e09170701c034a1081080c04144641202411005604403500742030030607521078617920584881c011a405031014001c1201c05020660134118243c0b06240700b41d07560801c03444c1000307040d1a18000d0000142e0001c1d41c05001035580f600999084054a014403400702610090100e030515240341200c0c500e40a01010f0340403c00c1000d841c20301c44d006501190203001c02100e0101240300c2990580c0c1d4003003100c0315140441d0b04103000c2d20b100c0601c0c50744e44c1018905551074400c0a0f60740c80303410701207803003050b040190700d866208203640507002c1a40051000150701c554008105c0c554882c280000003540d80c4e00c0b40c1e50100d5035210020500c40c0c2c0c80445c0507842d50a0500c6a40340010010501c4d815908400c04100503a03a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 206599820 1250 206598570 206598599
    0x302060405060d090503041205060601030911010c02030a0c0906030215122706071107080a0c06052101090902090702060721090816020a0b0721030f0903080a15 70
    0x10b80d001c6840f0304241d81024040c100f40403001c2c1040c0400a80802d50032200d03952406920b00030707003c5420a450b564011400c03200c81d6000035294411500d071580c010343c4204410141c05e80000c00300c4075001810745440703000d4509588003000f810b6803998200700310f08040392401c038030302800d28045d418500b000d555400780c50f1005002c2000300c0d42030092040040d40c4000c2c040303c000c4c0d0350012160039141915004d0a24842c0c518045544e02c20000001079001000481c810303019885818565402c0c54039006640030b07000b4408165a070404c550300101c4090b0100200d90013481d00c100e002c0f4169900c0d0041c0001064041e2143c4c01310f400400400181c99000364528040c0030220750070442450700c06000314000c100c113020050000c1000074640c2094a00040304c10030f5103008030f034181c680a96030b81202d000d911a403000107002d080300c0e10105c080c1c0c4d80c180012804003030440c200452804010940c80c011030350a20000c1340419101804d1040b224070074410001000301e400c24000b80b007420411201e00012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 206601070 1250 206599820 206599829
    0x2107051921090f110a05010c08130e040b0105012c010c06180309092a030f0902150a0806042003150d05030a02010c020604030903110a0f061808010603020604 69
    0x18000c0c80801c1001241d140d4034140d850440340801200a50340341c10210454041c03003c1d070305009103c20b0441c4c80c4c074000b0824401c41c0c00503101d0380000c0754141c3c0c4e040c61640001035100303a0350491000000d0304030380400010340b0480c440c0c01e2205466040c20000f62502040748040c0a0844403070044002404030001c03105c6101c0001d01300b400780c140144c681403000d080e0000869000030110f1084104140d00410181c007504c0d8104400d004aa0204540140843e10700018140c41e05e811544039003081e01aa20595441d0782c0e90301c02085c000c0c0b0b20b4000c01c050f00804414a0304d0400b000450071f079016400468503070403a0f0110350612400d8006015021000c0a024050504040010203e0281e038038005041d2001d04001d052001031100905002e0340781c0d0042c1301c146001d54241040505000c3c07020a500d40f00f00d90645904400900b16101d44802640c90901d0700e40105d05041c001c2030714a810001c4000520b05c607500ca0849100d80c80e4498104c01c2c641e40080f0f900d80c141082030005079035000a690645 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 206602320 1250 206601070 206601077
    0x2070b04170928080f03130e0903120405010b0306010b0306120d020705130b03120406080714030118020c06150a1205030403081606020a050909060f0d0305090301020c0321070519 78
    0x1426a00f0f100801042c040c1e101122a00c00c501100420000200140c84203090303004000c4c502659034001c0e40130010040b11075481c190020819100826003885c0501d03003150013030000003400d6504402203480d0001c2038000240f02e50000c420000c00b80f4050403100a8510103202900c012540d40002942e0344c402800794510a101c00b041c0980308910359031000445102c000d040b035800381102d4504100d598401e014140002d1100000504aa8001c1422a0b100301c000e000c11072641e80b828582c801520308a002c0d82800035002c000391450500c01f0421640215000411000d1128840040001c070542940c86040c6480b85c01d11010045140413003540e0840e500f101e19550f544001d00781e41041e401c83341c003004001e54404078a0208142e400400350056482c00d440c0200c603621400104030002c0e0141c050340c1e0b448130900e942d24002030700c6100a003114200150001d400d008117040103605580020300c1c00d03c820b03a00000001081610440c80c141c02100605000b03261065102010701d0794078030b804ca84c4061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 206603570 1250 206602320 206602369
    0xf061602150706050f10061d06130b0a031b030e0c04051302130212071e030c050d020d050910020a0c121205010603141f141302070b041709 61
    0x310340c08003086501d42c90f8440d40421003841d0811580314480029142c080d8079800750000850454024103d880c841240c0b03400030880e018105003040340c694884000d03c4046058645c00140a03034000d0060002902c094170701142060611481c460a403841c40c0c00300b01010701f03040315001c29480c007003894a01c0c3c81054401060b1607540004a401c5100c80d62002900308078007003a14000310030a5130103400b683d0709a425100b92030325110821101d1000d1000c05044082c0007121020b80d043c0207601c0680e0f407442d04d00b0280d09141c072904000049821a000303880c0c80544441c100602d0307039000d101e81c0c2d5034048000d20840c201825400000e000b03680b010802810555a030881132401c82c081c43e000b0a10700303580c5c4014400307580c4804006001d030896003103d185420080d00442c00e035030042c14491825548024080307954070301d8030010248030140f9000080d000054415138041005842c00141340d468014544d19005040503c0c4c00224042c0704130070080020400d111b40c00156407002c407101c1e41c110000e40448134 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 206604820 1250 206603570 206603599
    0xf05060a06030905010b0d0318091e150e181903170406020c061501030e07180b06070213200301050607020603070e03010c02010c120504050303070804050a0605090102090f061602 78
    0x1041c0d43e11b0400c0c0d01400100d010804c150b813240700745084808502072810030703650303880741c40090710a0544144000c02c0050382400310031940758028003651144a4290445d030356103140c0c2c0f1048010a84013680c540c1003902e1518807101c420400200d6800f12402d119015121a4500424014400820403076070020b210102e400d014203038042e52400340b048810343d201d900304282d02440030098600d0580c0803074103066131050490030204421040750805009000041b0550400d00300a001d4400450b607c46024030151000d42c448074000641c1000000c00006c0c0f01c1008100c0007940c070321803103d28010784010001801107071a000290f910243d41903074a1600c075165000c003942c0306c84030b140c54150150301e000c14882d403040d03054000387d615441c0c07522501c201a400140103000c3d203034100c0d0090b009500c10000b01d044a84180c606651050082c0709440300080c81da51100107681041d544490242c3d00410144020310b0591901c445140044560529048040001b40c540b41171034240684542da0342d841504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 206606070 1250 206604820 206604823
    0x1101050c1204090b0927120f0309060c0c03070602070303060308070507090e19020d03090b040e09011812080a02040b0a0804170903120703021005010b0d0f05060a06030905 75
    0x8403800c58020564030348551080e0407010a40003440b0b440301c40c030b0802c419403015080c184003040c0070390b007028088407001c44540310700308400640ca0800d42262040c00003501107140000085c01d02e41e080444032640e00c0c01d14204140c41c100000d403500c80d00003c10440303034103200400401c0710040c2d03038031420141c1c840361503040c1903008058a5101910001e0001407440400a001c0b400d64191802030104204440244003016a904268808070010000288600c405403600d20124810340d842403a0222504d0388542c00f1001d590001c0e8032044d02e1106110174488225401c0c000c01c0300300d240082d40c0440d010741076103542403250900c07600403082c02403100206444003071a40446001e05a510082580c07515203080003010840101c4042e121124074240d1000b92412103011541d1495005004140d2006512410301c001e500c1203100300c0640c40b51820a209030b035480d0150382d0091411000503510707850311114038010345103600d0b030403c801440c10080144503030301e00111105440d20707840d00190200003843c005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 206607320 1250 206606070 206606077
    0x504124503030f031518050c04090e0318100f120f020a110c090c1b030c1b03060709081c0912063608070201021e1015080703110105 58
    0x41a40a4100110034160459000640f65015540402224041078221581d20b205d45c01544404403036544d100c40005d071290496900704448955040ca4643d49030b90f80c208540d08070550311019007000c0740c680e80341e22a40d40c1041041c402039440d407000700a011001411129140708100901101e9000301e1204180d542c00710450643c1c5e034504543c4c0e074480020140c03110000108150491003440311010090604c59141c40c0030740180181c0380e0410030014140303001e00f64a42030500c4684000c0c000e156a400d02002500703481504130503100302400d000024035040c054000d003050240b140c1c03010200161480007c1c0318140c1d03904011800e00c0d00d400308008880c01c0665900c4800b00b0556200c0c101c0a2280351750100b0303036018460418601d420010b00c0701c0785440300156120000c880c0c1e51102d0401082c140300050461302c1c414415504a04603a03505400c8003801c40716421404e5004002c0f42e20030035114458402ca420114420b15140340ca445e07110b41d5200c40c00e0000034904510720000035107690042054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 206608570 1250 206607320 206607437
    0x18060b030f1f0c030b030f1c050c03180303071a01030b16020705010e0109080616080105030703080703030207060b12210c120c03070c091505040b060307030b060c01060306050412 78
    0x9a4501547c1c00460715503a41c0c0e8201810b0390b0306108908800c20a029404841110907400c01460810344032400d010f205011000181d5090700080090b140010000c1c0c002c00d50051003012810300039411800d10000d500300c018044d503c0d900b401e8550b01c0009400080090440304240707031501e0900a040d004032071400b26076120100c648101400d000601e03208071074400101c0b040c2e694207940350b03a80d1002c1560302c4103544009410440104203010103e1711a800a18a4034080c440111312506da1001081c00e04400c800480e00750b0b013016801c121030f000100b21404000024182d5241840b1801541c0b544580f2003140d100d150040000e00c035130400c042401030f65403998100240c0124207075500303032a202500f111280341c1e91880900704040340130310701803095581e00c0d180505180c0c01c1d42e68545050b40208809003103580d1180003072002d0080800300340101c9025511680e80032030700342040d14100315000c149040e0792060060b1464001040f035008800d251305030300f080c3d20044c100310007402c2c401d503220846080b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 206609820 1250 206608570 206608573
    0xc0f09060806090411130b03010b06030c0f030a411009021e070b090c0a03110909150a090213050105030604030c030c06060b03042a05040902030118060b030f1f0c030b03 74
    0x60005031b1301640b054080c00b806800034840c030041c1d0000c02240d440101c40c0200102e41c01d1064901c2c406500300656440695104006542102070b00c0c403110301c0c03002c42030080c60b5a21b4491103040f065401e0102d03034640b0444084222140c01c009060f206220030342c4c06400d10503a40800e0050b00c00020011148000c1030358030116985d020700d4148500b080ca001c90703282d030407403080346000011810001c05850840fa0070400703c11a030301d1003004200341c0c400e02614055181c450702d01d41c07841e088800d1f0451401003642400000e40c000c0248188801350802c0c2e03035840101844c200c010040c90314041041c4d50b020b581407801c041021b440c0d19059907900d60b05103010380414038000300400c821100400550140340100e0741c0640c22161005640c5886041141d0f0340b1503680c030480f0410540c24241c10000c0800d10050020840800160b07a80402e4801d400d020795800b601c0f00b1035801c60b424140142107080c0e8a440181096110301840149103007035030340040600d02d03581e00c1c602141d944a03600011a1020040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 206611070 1250 206609820 206609839
    0xc1d0a1703131707060c080a031a0a0602030a0e010207080304140607081204021203090d150e0102120105240406080c0c060f0406180b040b0c09130c0f09060806090411 73
    0x100140d6100100c0c1200340c80b900c03c05101003101c42c083d40302c1c04544d03684030313551500c0d1802c087e42c08c80242103200b04400b11228407684800003581c801642f1006000c265008648900038201d00404144807000b003141590003081c0c00340541c032000310480d010f8074a0640300039a6003005c0c00105880344140c00c0d01502e2810017095000861601a4031280941c5c004c4030107401d45503611100f26240d2068a41075640300340380000083c00550080480040380030f9608001a503541c0000e13400e801ea0344800301124a10404400501c41d519001d8070102040941c01c05018207074600c80302c0d0600c644554060345090212250010328014115012588908003100540e00c06081c11802c2044d2584159012501c080c02d01e0f043c1c4808800382c000e0800c075160000001803080d221a1511021681d01a100901417603003040701801c507494a4942a10351407050340c0000e01c141b05610b00800d2541c03409031007000c00041910070000d05074031000345904020700300c5010301d40780c403940340c4801d0b42c044400416030040102c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 206612320 1250 206611070 206611079
    0x6081c081003080324181006090b0a0c03050c0a06090506010602120d05060607080406020a030e040509190c03020301060f09110405061917010b071704060215040f020901090c1d0a170313 81
    0x12021400b071f1303000020403121183c6450069480c6500c0f8001c00350b9901c403e024034400c4512944103540c07081d000c0c0c181a071810303108034030350b5040150340d0b401a500940c9442204080110410026004040d144007604144c484910941010f03c222501801c5c29500c42c80030509603078800c0c0c1200d4200d0351105480e0390f6141e075000c1c065151341c510501500403c01c2c0c8501400d5905040c0031b1103205d40d290101a0020301c0414074240d000c01c407e11f806980d56540c100300400182c0302445030340c010780244031012015501c1c105044043d6041c1d000550348401040c441006151901d00030f9411240190401c009010003400d01112060003c400e000d000101050000451400000050203080c0c021071000a50b4003202542c0421481240326000042e40f20740b14041a510000012a421500c078150390000c590fa175070002111018280c05c28006a50b460000314a1650031511141a1440c5000c002c0010400e0b003000444c0050280701c0c10032000d5a103540c140b50040248120b800300340c4944510302041d52034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 206613570 1250 206612320 206612359
    0x30919080105151c051c18170d1b0b06130507050a0306060305010302030312090703080304080a1b050a061a12010912020a0c03060c0306081c081003080324 68
    0x4a000c4500a001120302c40072007408904481c680c1682080041c607446c10803a01040094541c0000708042150810b60403071200c14152178203000f802010001a030400341e9034406410301c11201403100601441d40001d810548480c1414000b4680100d9100021754510000c20200c02c601c4c010410042d10740801c202a144d00003010344040900c60b41c0420001d6101d141c01d6048690a00001e51305030f00902105030481c01010002c1ea02001c0d210a4590090781c0c0e0b0b0310408540c000f44c4044400301c0300810b210580d240e0000c05428041401c0403845003188550b25401d4452400034409000c4d5034603500f2022813f41240121940890050301405400e040640c00d980203043d0040111a45498107101c0e105036440050320001590b0484400400c42d4515a1440004e1050909010030700d6110780d4001000107041c460b40b6805141810251a090406200201500801040390b40c621407214010b20109204d9002c1d40d0f4441c00d04240d043c020313240c17200340c401d040c0f01d1500d90321b500c44042c02001942030030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 206614820 1250 206613570 206613601
    0x6020708071a151e060d02070f050c0f06030421020c030a0302070305010c0e090c090f0901031b0b0412020906030106030c06090f050f01050f09010e060f04031505060102030919080105 80
    0x400380741c4550590010307402c002c000502001c4c52260742581000c21495441e05a004155403480c1040061424800d581c90980342d5200c14810364480d08052580f0b80141040f100b580d8201d00202d0741d2a18618042d9a071004580055460032141080b815100d950070f0b000b0801a21124002411a038051000d80303402592060940401c988550909407000d403030030b01404000c0d2580c000188200d58a075503c0006081d0382d0010040c0e16803002ca07045207800c10342c40e8500d00c1ca011f03601410007181001010402c504074212582d00650015108101c00c200c20504900030702d81d00c0d603040740d400c2c4054680000290150603180c1020b001c1105440d00096065080031141007218004107000300055501c43c100203000443c00209400b291040000701038800c40c0c10000d1200300014103086410100e803201041030340d084024600c0001d000001c0034028032180c1c3c0c608504401c04180e0034000b40c41c1c9080000d40304e014100300c1034006c034105000701980c8100b542d82600540f81110080150703151921b0f04140c03800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 206616070 1250 206614820 206614831
    0x605011203021c0801030f05030415030605031912030e0102040506030a0c02100c02070603050403110604121b170a09080303040309060f051303120e03011107020306012106020708071a 80
    0x1150365000d503040030a92190f448590b4070341d181e030748039070b0302e580c0314191451920301044505000402c40411001d03010650a040082180c0c1d001824a040a003031510f0301103070008101c4424200c0a50100003040e171082428260070a180c00f0914000c40030a450190090307810007548083c01008001d00c14299034000e41c10404240d003150078034a130050b102012035001e9200e0000581180c0360a02415000b5041705e6001032181c581142d444d1850500719003043c0d81610110b80304c40d9180c2c07500c0c0e45646c0c86600c10160202c54801d075880c1c1c0c1032a076501d000c12000a8030000f1304041c04039145403001d0040c01100c000300300c0c03842500c0e070301c2c9860f03d402000c800f8203004980100b40e104420000403445641074030300103900d02c282070070801d045031140f00c422000c92118a0400100c0b5004400f540c17401e004110a05a400d80513130f842d082581704060400c20141c00c00303d60400f040480d8110f082000401503200b9820084c01a560a00d0381424501841070358400b5000c0c414282031003259804200000d807160 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 206617320 1250 206616070 206616073
    0x906012c0409020a290c07050402030c0c0d0f11010b0102060103140a0210030902031002040605181c060504260d02070c0e0108060702010c080925090504080a0306060c030f03020a0c060501120302 85
    0x501c5a200c108030b01c0e003d010002c06d9158001c8a080c851410603600440c1c1040b40c1d20500303810b2200050007a8944603031480b10030009a0302103010306103070781c0125540140c1030800c0000c0c84210b18401c0001d540310701c1480080c2801d85c4503101407441000a1200c00c42e5160054411086050410006405040514401c038080e100b9011070344c4105025100f61010b40b038180d60b8084c074283c0b00c04001c42e5407150070300e822a84445140082e0b1071000700031a80111343c0341b05400104192915003031000c04e1403417540760200c2c101d20030305000e028003450208503070144071110401600e0740940d0500300060801a00f10305072095503580049075003007000a4962203485a0350091280155408080711802d109a4104446500180b0030518005650146100000034191008001642c0d50410019a0b805440990300e800740029014038186e41401084c0140510b0f007006036051019a40c010031404c0318800c10310070590b004c12009007080c0b03d1101078960130b030440b4050081d075071170b54a80d180c03038018280200c1c0035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 206618570 1250 206617320 206617379
    0xf0f030412090f0302061b07090b090f01031101140d0603030908010506100909021c09030306150203030708070e03100c0503070f110a02040b01020f0105150906012c0409020a 76
    0x40c98407882e08881600c030384241c244a034a14540c01d01210350003000d83ea001b8409080021720346010200000b000510307194102003183e0b02c424040c8151070340050801c0c00c00c0e448040040c00482d4403040c41103a10343c0c0038a4245414504c154107100140624010030210a00740301c000000d01d035002003440140c860714002040340e0b440b00c00400070411061b0f940b90340410a082030800110307449501a0141c4007414801c01d18001019012008881d40d141c01180170a80c2d62000b4400b0107070301110300082c1080e5000662850030a0f29011740300303042c02030400c01089200c85254210351801c1c061002a544810000e00c41400d000174007928580040782d0f91130016400402c51440103210746200d0149029000184c050b1003229020300010301103c0804506521580d001c0303a10286003440303000d1241461020521030540c0300020803081c0d400103420b040c10460001041860ba120180242c801850b850b101c030a04441c0d1781d0f0104010740b60381da20103540488404000102d6103a2001c14a200c0034411141158 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 206619820 1250 206618570 206618603
    0x306011704110607020d050f1c21020c01110f07140d0e04090f0206030708190216020405040f0b0901090c050117180f030408100c0f080f1905070e100305090c150f0f0304 74
    0x100d0344140b860b400a12003050b82d0090000c01c01e6400cc002607a010310022540e4031003111110900d40c8001c10030b81d41004005018000e00c40403805030074a00005501410300c0c0f289035900100404990800e20b881151384103011010071060140c864072a40d07000e0311003a2a407038986070250480400b1510b411101040400c0c07030800d80f0b5076200301c8990072000c01c007145c80003c0d25002d001c004d0000910464928440f9a080b2010841d6401024400c4014cc000807941041610300610b40d19890740c000da05001c10400103403461440469656070151811a40d409846240d080082c80c06040d454804064040060041010780003c961104e20620f19882030000d180342e02402c640c688000c406000000b428900441c050402c1500700f15001440081e00140810701c002c440702c1100c40c181c54040208aa100c001e0702e10b4240721010003103591160604120300e00d4038083c40f58980b800030403d148030b0303a030508031607284044050903110480040030a00c2d8690320108614005c543c0f003920144c4502018070300300c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 206621070 1250 206619820 206619827
    0x120114090604150306200705031e0f091e04050c0c0f0303061807030f06090504020319050303060d03050c0319090906030c0501031805060c0306011704110607020d050f1c 74
    0x1c3c09895440402c1c0759071554454030010460541c200c076174032580c40041400f043c501405000c00c0307030081c8003859441104402d102c0320700340200031880c69582c0030b024980b9600240b00036508804010b0f1150148a2907402030510300102c2d900003113520918043c14403064010f1180600301d9600c80ba81210f03030800750b941104d41c6e80d00080300d24640c48040c00800480100400b4000e0703820001c00d050200b40d50070702506400135200103810446100c3c1d0794504000552908200d403403001c16134040d05204c5400f41c0c0c0c40c1e5039203e1000801c2c4500410190742e000d010144690115a80c407a004000e42e0f80790000300707450107000468103080200180300b604021403004090310951080342d5000c0800c10840c1c0c0303040300540140c40440303010311a052500c00d401020410070b11549100b1402c02c00794940c0d0b484e0000000d003c040c0142d001d1004205900e040000140380c1c2c69120182190496900c6e4841a084c800034000585007140144140038505605101d03a100040c25804441255101d0807031081c48141113 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 206622320 1250 206621070 206621081
    0xf060b03010f0e100c1407031701060c0317150607110a05090c030403180503030705010b040516020604060203181c020105160206060d06110f0c0c0105070c0605030903120114090604 79
    0x3200f103504044403032810403080da03101c0f280030200c80c00c1000d503103440c0041149058005540c00c0e00441d015624030040c00e0b4030900741e1805402070303060444080c100354034010083c00745c01c40041e86d20040c080c0071490700e24400d11800c00c2d01d500102065622503407860241c100c2e241044054ac09610b10100110381c0c4d140103039503c0d00c00d02e0340c6156141950344641701203c1c40c041c1500c24071403c0f5402e2070040385c030f070b1400d0004082d16805480040f902008001c140702c00c50340c00501e000e625240824080d580d10764040f0740300f070b0041d40001380541c4130f4607046404a00090345504074003291040300d800090b012407281c454202c10903e50003c10603a55480d10b64000c81300002c8814005070820400986145000114420898050304000031410041241c450712548559004400c02401203445980702c0c4003006202d01183c1d0a180c242d00303041d2640d548119110440c00703950207011003c4001200100108280c5801c0c4901c003040016a59607080d1b1180041c1d07501040d18001c24031500050740c2400c05010780c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 206623570 1250 206622320 206622341
    0xb12160605030c070609030c0204180b090d050406031d031303060c03063b090a02030c0a0819170a0f031b021b0d020a060206010503060702010b0607020105090d0f060b03010f 76
    0xf0307103181452a0343c5110080a1004c4100c05110a9081c003a001d601c4c0c40c8a150503c4404040c914038101003424544c82042c0d000f88110321a45c0030340c0769161001e502405840031500307207040c00f2546211a540002c0c0101c0c04d015000100d10003c5a512010391080340100103c0c2e009500402088445480c00c81c1070b100c03640141a580d2090344404000710107001840c0d0151031050b1140e1791500e000c0c2003800a200c9090381c1543e00b9511400856080d0716007480248540202111400200c41c46c00c00700984401154640c0800125410618000d2102915000b011007184040079560b81044006c050030080c808000301001030310b00084450004100740000500e00b1954008000005545404507002ca014030031582d001086540c103000140c6a4000c114050310503034010340400e41c14242818078000c2d0050503901168144164541c058442401f2618815020300c1d01c1665404038401042b04010130f6100100780080800c558024041581d000307a800610440083c04030341c02e0401d25005a6001044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 206624820 1250 206623570 206623591
    0xc0d08010b070c060f020312040c080708151303140304060f061413050c0409050108010f050903071a04020d150b030f03120c030402120d0807090e090d120b1216060503 73
    0x1018007045002e0003403e81701c07507035901c1180c0c900101030000149850003920200c8584c41170080c2880980400e201a9018080c500b000f002c1ca080c0410403001c91036005000d4030074041d4240c031004240b40c4586402c0441c42050305480b60740c0e0425280103402004210084039607945400d001158070034807268007102c50100245802040818081c214004002c05401860480e03001c010014001405005690003000c46000010321118400c00300030544030f00500300c98094204000300e000044c3c44181740081c014845c0d0100c90150b9580c13000c01c00106109034003500e1030001c4c1c1c10244140d0303916003110140d010158280d0350307007240f00b18a0598030300542c0e10b109040304a010014403007040f40006164400c0c00140030654039143c1ca00b00504207031600c920000091a22410800e40c59000100703003000b00403440750524580b034a040b5036a11051203d1700d40080014000c10102d0b0842c03960400d001d103600081c548400200e03d001050b03601c3d0800760f5041001d85400e00c0000d01e41d806402524469024103c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 206626070 1250 206624820 206624843
    0x1f09060806130e031603052a0706030b0102120318070f080d050306031204060503040b06060702010503060d020f1002070915150f02030408060103080913050105010f0302090f060c0d08010b07 83
    0x8210043d202011003100c0512051224084074903909020701d070218040e4640301d98504070a400300c071408100b1060a80c0d21a95010745504120340040c00c5011110b45c1c1c5400102d601818004030304104140d0300f52160b0100100521800803012581d2a6440300390204840c00e2543d034403c645c121590a20900d000b80c0c01c14000303451103074000c00065500901c02019101c00600581c40204580c1054004000095002c0108020000211101600010b04585450404862340d000038414800284154082e40d240d408400c115154031740c80c5402000014441d5811105d0200001e564001900ca05115141043d14050116400c000990261190100045001b0b2400e00e0182c854524012540d4214401007100003000441804a036001c0d62207014032907500c070b962108016048419400e21240c0d0b5141030010001a03130045030aa080d401030742409078a0304501000145008099055a40c0003507000503a41c1c0c1514003c180381c040e0f10351540703444c06c0720b0762900b402040c18020b102d4002d01c02c49608 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 206627320 1250 206626070 206626099
    0x9021b060601020d030c02070510090f08010603020306060d08070510021923070c0308040806190203091b030c06210106081006050d0e190b0604020a080a0b0f1f09060806 74
    0xd403c86c0d000d06507140122035040b942d9101094800da0304401503000200c102c0300500212104040110052910701300900007603040da00080c0d220000505454403d0030442c01c10010400940f00340c0d01c46075007150036500100340360054000a54002e26616045040c49102c890800b4040d001700c4100ca03217401c0d00030030003100c0068900c0d00c0e6482500161000300c0b11080010000301004010400791142c6800b0b0b1400c0e003401c01c00701803c1800603038103843d01401401040700a03800000c00e151100c0210034007031400207141d4042814100c86102568101000042d8101c0701c0343d512240b004106100514000541c0c0d0700c900c03c407070b821020b0716511011040d50004005591007200504100d104990b8000303070301d07285a601645800c24182d034400c0b0000c072414000c01071005580480d944080150350a525192034800c1c014001ca5005142c507850695030304001d6495103915520002d1244003920b44880d400d8007440403c000344c440e04034940082e0582e000454590b200b95440783c001e00015200700780e648001d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 206628570 1250 206627320 206627327
    0x1b0e01030212060d02180a09032c0f0a1206050f061516060204150206040203060f011815030209010e0108070b040506090603090a050303011206050a23070302070c09021b060601020d 79
    0x4007802aa40a00c071640c03c00c0a2049210820b4007903004554005800c0b2307000d180140c880078880207501220b04910b02d10703444100c6a00d02200004004488445500b8030700c100044ac00c0200e80c02940008040ba0b02440810550364040f07401410240e00c8240d080e40c0d140300300840c2c2d0010a8005c0441300d424880040720300b10060350589101d2040c0005401c00b500c444591100b4101000c840340183e004130103100070742c2801d0048030703005021031922200300c0d8117201000c0b020b003030366203c448121a038584268007540c1061400401071540101150391659641e04a120008400c0c040c1000b14018010005020841d1304100c0d003c0300c03400b07000b00303040842050403c880c07504010700a1030140620402e0000040003880103501804801c03a04404100c23403400d000c000c450b00108a02082450140070410143d140c1c2c6034012040c1320044003421650b240c24003100680101d4000400342440d6610105409140b500602012807082600710000c0000740304450303558a00fa111a03015810440c504001d0510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 206629820 1250 206628570 206628589
    0x61908070e0310140609160c0302030f0a0c050d03060f05040509101b0e01170c0c2b270e070e06070501020a170c03010b0a121b0e0103021206 62
    0xd1600300300940d075110402003030411800c02c0340038442e00e554584004000c1040c0051070341104007540c640010b480d0984032102c1503e45225110140004a00404201442081103c0188050b45c03011522441400000382c41c0081440081780e090142401d900320051203482070100b16403e4041c0496a10301d0901880010f00028042410798090700c2c1e50541907410900420110001c030600010f03550f020984000c0ca0740414811540c10007035034413146010556100c5040760011a9034010350b0380e075010202110301d400011001d40540004101c11700720358240031400d51700d10019540300e0302e02c03481d810701e10402c80390102416100352118542c8103000b000c2012102591184140c1000c0780750359040c00001b9a40d402a4000300da0580d0002406030000d60300250102503c806034001092070700b8213200580840c08140a0400400400705083c2646880f4034001c8007100c074062400c02007003640f40000d010046078401c010340400d440d00010070065110784221030045440001d48686501e8002c2005030050303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 206631070 1250 206629820 206629831
    0x281b170a0209010302040918020109050d0203031b01091a0702071d070c030905060d05010504061401020307031107050a150e121f0209060f12010b1305090601090801050a06060e061908 80
    0x5038280008103000146214051400388d14a06118132403200d807000511401c03e0790800d0340a02248401c01d030060f10004165060910030048072100c815248075600d0041903000000344c07a10407548900d55404451441d15801600c0503030a0b0340c2c5c40c0b0f40321b2070844443d208030f03200b0801c5454460006542d80d40f042044590007807023480e02102550383c800004026030003a01d400012540d640004000c0ca1606100e000028804094440c00310594480040d40324082c03608040e05000400340c1080c94040f00307012100140400400381400d094941080a1101d03102e8001322001c6651a81c0170700c110302d03003001d4111441c41c00350002e0000400358007003642a1050b15885402c050307020701c082d03800c0340d032010090a06400c2c0f0301802511940c8064500c1003403076040c2e01186006908000907045403000b4071940d01a00d070240c8448209031178180c012100d0690079401a6007652a02c0c2c01e21149140c1a00082e084884070b5813040042c111580c10000d442c450080262840c40409561a45c023a0140c2d02a581c0807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 206632320 1250 206631070 206631077
    0x102070c0b091216050415050603060d050a0c03030302180118180e03030108010e1b0a090e0f06042f03070306110c0319030c08040507050603281b170a020901 69
    0x1003c0144030501d880300c10780380c030380440360141e41c24401810b0a2003101104060900b10703502c0c0d24034240220b101e6110103071615006403640d034001c10500c981003107180011540400c42241c159034905008009402c0054818404c40080160b039420b580302d48110091044162903450040b407508030704500308085041120810307a01d5150220845006101440c000c1217480004618101d11000c81c0b401c10400303c1e00c000017016100344480303242d2100c0c51958150340c41d050700050709031101544589801820010203e49206010801040000444035080007480301c1d00c440c011203605118618060047c0d079907068143e8044c0c5010808103d640d0001d0800442c90307100c02d464128203c00781402e551048090201c1820400e00310114680e0500c034075508146a450640c01c03070b061690301c05454111510500d0321451022011600d0f08000280075842c4518640407985000c154450460180503c0d040c10100075002e044940c1406000d05000e80078040d00e04040203803960b404440320000e421015065040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 206633570 1250 206632320 206632339
    0x7110105030919080403050f070f03123f0c02100b0103110406110d08070c0f0206160c080f06100303031116080903060a2702040b0319060507020102070c0b09 69
    0xc0e0346143c010480054010b501c003a030f81c1c4d42941045494008541020f0b00380d507000d188100010000024034170180ca80c41403024559418000c0100ea1300031469502c5000500300035000505c020a10380080d1012407402d0400019644180c6a0411101c403071084102503003041c0b0301c241d0791460350b80c001041d1308014100010031038540c2d104203105820035000342000c585494000410f200b0708228110910140e8500380340c80340b43c201c0c0d0050800c5481d40700240441081d028550840d40c80c42c0698104101d80c0000d0b5a034800d55040840300e00300d10b8030603060540220205011000340c0820b010748240f07205407504640d14071b150380c214010300c00d608580c22a03580c00d204003540d61081030544034040d801740c182a6200c001d81c40030541000c00103800e164110f03240c102e803043c0448485d052031440c5051802071068074a002c0c000715000d00100d104080d814003d078030207105401c03050381000038800d002c1e940c10071a83e6104c0100380e080f44a00b0300c0140250b800d20700e0420480000a00506a4500203040d03660b2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 206634820 1250 206633570 206633593
    0xf112b02030403051b01091a07030b03060a090c0b040323030708030f0604180302061513060b0304232d101b02030f0409051810020306010e0402071101050309 69
    0x201d800c19a0220001080015203030f5001070407001051000c00d044008110008903681c0e1440c000d02c541c5841021811036034002100300703000e42e200401d030394000f80507118546030501c0214000d06960f102165091300402c0c0120b2040e00320300503541501d502c562451110105500e0b408407840f4244060145480b042250340d002803101d07030240d400703810298601c40c01414400304000079281e8440c00b52000410145110707012030307400118690803580502c64024022594004a40c2d41141101c20501c0c10382003800004040c003400d0300440c4594043c105840140052408007002041c140210b102c4a9101135202d04014035001b42e031040480c1166a4032401d8109294058140b0720180c4640340915901c180f41c94400000704a080040c11840c07010354502251140507079124010b07801070000c2287d0703503000035140d1491095030061107450318003100c0102a00c0004030000e03500c1100c200f030001c1e00c800200d030305a050070300a035511a644091100c1d80d120451004540c035400c02440b0100510841d0303458403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 206636070 1250 206634820 206634907
    0x7180b0301060c020a09180b060102191103070317182409040b19060e0f030334050c13060b030a050403030605120c030d050304020a031b090e100f11 65
    0x21f06030301d2200c080c040c3c1e180700c03400d0440e58400c0c000c01003415904808000c103590700945003a894403650105200142e00000c0d07000c01c3c03070701d0383c20b800003011a00300840000e030842c4030b030300034003d00c2030306040521001c16644144103036401440700c445036215400750382d07621901e614005041181c2d405840010008072220000f814645140d22082c0440c030300310000c0c04059440031a003002c000c000e4440305201c80d460780200f41c3d00e104d100742c0105041c0000c401180500c50100d200344e038890a40c0c050301d1401c04a404c12980314a0745102d01841741d4010042c0b243c0d0307410716000b4a0101d17020905000d00710303980c0282010152900404c01c41c105913a90002051030350f50f01d0b03000e6000d0000140140300c609944001d043c074040104070500c0a002c418001c100041e69114076013001d90b035000121401400004400441200b101c2e0000395109040203d1810124000690b4403040401410207108441640c0039400c216820304410b280300c09030400c0813519440c10070212401c0001d203e46840030880c202000380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 206637320 1250 206636070 206636081
    0x32f150a03050a0515040e0102040305010507050d0c08010f03030e030a210806040213052115191e020919140111060610110307060603080307180b0301060c020a09 71
    0x569158804a1100c0c8080e80c18410240d218146020411803814055070113041c0c1c42e100125140315584807100b07034803000d2080d01940c0c019036020009008a0918410103041e903080b505803881d445150018200c20720340724500042c12039107080742040c07600e4107549040f101e980a200071982c040c4a201103460000d14039160080500080c03070051140500c200301c0c028612800600024447c50052284041c00200c02c00900200c034000c503100c1511128826807400c100760b0146000d0b4080c0190521010300340d25004481d84603400480018074010100c102c0441200c0740205056001d800c00200c008000c94194002d15075140000c203c1450074804488005000955804c4580700b003405880c0e4001550f001590f40c3c40c5104802c010782030a14200012541640074514403404110300140f0b142c06102c0c06208440d40103400000c02e0103426140c0c1454002035101381c1d502030018464150495004d03403041035000554035040d518601c2c1d03910301841103801e82d000d01c1050f40d20190010b800502d00e211845070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 206638570 1250 206637320 206637349
    0x2160603020d0e0604020609010509030703061a15070b010e0c0408070314010c0203120604020729011404020406020c0f04110c070609050103060305061314010c050705010501050a032f 80
    0x541d60b640006140016581803d40343d00711a0f00800503c801651645d0595540d5902840c1182e203900c480d01c0000d280009503407028040c140b41ca46440c3c0310551082030b80310040030a580d0110300c180200c1c800c034038510492502804065180c001401084900c4a41c107070021064003030030b402c082d2038483d41420042c4035801110009803000740086042d03000e0144c0050050039001550904586514800c1e2a0f400245594400c950000710f40040101c0398400b100c250181421458400c0c0789036840501c0e800003030042180140c1c058280e80c04c24074003402180d00340c0d117096000d4212846084e0500c8151840241c7c01c075801501e8035601b8400c00071403005441068200e0000b042c1e000d02d4500c001d842c0d0321032030700100e0405007006000d00c0412000280c080c0c02c0707003108201c46100c5016081041e4074400c609910070465080440c905141a4880080c022050140b4001c001d1641d0f44da0412507200014807004205a0880303070402c1d21103034000100d001c440d030640f00e030806103488030b40000c0d03104404114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 206639820 1250 206638570 206638577
    0x60f0f030f0f0f16031506090e0a05120c07050904050a0203011b0e01030c080f0a090c090903030e010216142803110d0e040e15041406071707050a021606 67
    0x280114400410085403280160081c00340c1840d0b0280c036840408280207000c05401120101100c0d94006c5440d0300080081c0098101009101c224a00540d10340f003030620309642a11076811401e10180c01c03030b002c580a542e1810b005114140c5484140000b0307143c0180182d980b8000c400c446809a2028050424018245009a2521940c403500581000f220b0007400741014600a44050640d400984407a000008100c030030391240c3d180c3c0601d001800140304014891094000b0029202e09550031400115120303480500088041c17140b200e00b00d004c2e408442914602255000010600030100080c40c10020020341700d40365151280d030714005001005c2c1c0b403020640700440a05159002d03414400300310b08003024240302203585000609400d401080710340700c1c550b03c5031002d1090350204411195003028910704250b901d000c1c1010711f00c1c101c0784101d003212402030900207840c091051f00da2080c0c00d641103401010070344429504075641d4001104480030f600c42c10211960034801511503400810030b0340d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 206641070 1250 206639820 206639833
    0x40501090510120308012102040e070906050d0b06010e1804081905130312030603050f0c010f050a090308030a09060203131209050a0513061203020c0307050108010608060f0f030f 78
    0x482101c00c50101c0c0d40240b2040028603000c2c030000341c0c050402c2c0e0460300e01c0210f1040080401f92080342c02c100c1c5010080d4494500000300d000d0340030104c0d0b4641111907040007040f00e07566070410f0003552207854030014203401c1440006003696014848583c07541c4005818100081c000c800f1003045c1d124140c409503130a00000c149284860147c0c1444a890841d03460b00c00d0a1226000f0006200681400010107440e841c02c03205140c00e110b6840000110303045001c50705200142c501c2c20351200d8000c0a00b80c0043c0e81040c07506001805141164240021075803200311b0b030762558842c4c0105401c0034001c4a405602c1d179012170003080b41d0b40003a40c010b01401620300302010381d41c58842c4c16180b1106485092081d40002000aa59541121421102e0039541c8042c50300c001000f48004001d56044000443c3e940c1c112072040c9980090f0405101c80194210307040aa11840191070341042442400005069880091540e0904100c603c10b07200c405010001402c200310002820948a0040303901d4592000303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 206642320 1250 206641070 206641081
    0x80706031b09030803040201030f0b040603141c020607050310030b010e0613050702030403060218090f10140f1011070b0c060a05010b070219050d1a0a05070221090405010905 76
    0x11401900105242c1c2003a415003891682c2d105000d000c0140040d041c56030f43c07444444c070240326802c80c0000707110081c01040380b00e40303d280c01503000000038410001c1e841160840340700c403042c03902c440074001d5403a0010949903503050030880d0141c1c4001d01c0115000100480080092003d031019800b80c204148003526a20300001407000f002e03030002241124a0138603007400b0340185c010084401b500d4200c2c1016a644d032070740c00781c00b14070700703511402a82042c640d00411040000e045821350060020380340c80d0190ba541c4a00c00b0540c2c1c91200b070350640c0003019101c40343c281e00c1d1401d18050303003103a2828100090034295100f00d00313141d10b56101c00f041c014001140d440d40e40342030100359803000440c0d03410449941001507a486a00038848001e0054201c108440c41d0300e0250001d0070010700c40100002001000e5107030030448250860745c0610070303500850100701c143d14940207061080031141e000300410044600c0c1203c1060302c020b2248103000041041104603243d0780a258080c02803050082441c0c00d02c2d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 206643570 1250 206642320 206642351
    0x1502070804170a02010807030b0111070605070b0a0603120c032d0e030303090a2a08011b020a0b0f1005040e03040314070b2a0607031a1507081308070603 67
    0x40094100040d00f10000c2c0500603038008410a0700401c5624000885181c1c40005031a0340f540300200e44c044d8411140300091461344400204601031060702c1c043d219403903422492050302c0311800000d10749138040c8500c41c111442001814a111302038134003030110800d0420f000d4041010100c00c500403500b80d10340c046805800414107541d000b02600250720f98580071085035114903820300018072441405117600021940050f031149a000c41c0d070101c0ca5126502c5080b079009210460000f01900e0404000030280e50012407100c10540d000020f100740d0384d41d01c403c0c100d43c0081c0107184072403d0555440104141d152407007281a00d4524000866543c3d01318184683c03991019100c04040e58000070b02445003140442c1950b900e41110b883c02001d403901e0000300c003200c0c860800c00300790910400d010400403079850740201e807840f455011079040c4031090b03a0a000c0080c4140b00910380e00c040070083d2000003020302d001840000c00c15441c508102d6122240d46042400743e51050700040d444d113401c08640d004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 206644820 1250 206643570 206643599
    0x140d08060d0302030f0c07050a080303041703040203030a141902030301030203060f01150309030311071a010504020901020d0c0606050a03140601090218040b010306030c15080f0c070f1502070804 85
    0xc0440300045511680c0c0c0c2d0082d03683c4a1075104e0544000c0c00b00300d203064041300b0000e003400351600420780800a5100d0328455541e8204540a1b600d1507001060000809a03260841c2d02580d00500910300c0c2c8040c081c4140c0348540e4000a90303c409404100801e030162140c0034940c004d0301e542c0c1c082d6690303514500415141000242850b41c1804455004202d0118600d511840304101c5043c0890000074500301907008083c68007901d51001d500140c5481004004082e98803403000c6401403200c1c913600c49060008034042c000050f03000d40d10400c2e64009840c090071a02020034460304c8045078062710340000c12450b02203a81308585102c41410b401c8400501408858050001c0c0340007107042c20303451045000010090a052070007181e4404005402d80d01c660803110107141c002900b001081e54034002614030b142894040d03000206010301241d5a401c01108540c09003180c82d1845040a41945500028000501044940d54030f088851200c44005002078101d00380030700001c0c1d489a280c0100c10500e2034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 206646070 1250 206644820 206644831
    0x280801090308060a0501092105010501090e100e030318010603050114060324010b0c0f060115090806040c1e09090b01060e12060c0a0c08040e010302030c01140a0c030c140d08 76
    0x101000305102d182d1f0b00040e82c1b4112032070f07006404d00131000006c190f040d0200703104001d003040d4241030012038654400d030804140ba40e446001c4580300045140000221202d084040203642c008001007881d414411500300e034070b9680140006a49a501c0d5107403400c5903502c0350307030703031709800110301001854a4148081d5040494000440c8003110b00301e84c0300da0407554140180040d0b04808643e9000071102006681c484804000864400b56116030f00740c80c00ca61500e40301c20010304c1e802c0000c030388094049115030003698040007a0051a003480c41c00641e00c0340d07180c2049103040410200142107a16801489081800fa07040c0045650510800130249400505181e008043d21004852004c00c00900c003603000c3c241b0b08040703498241d034840403109084044c038003030b148000105020035200d19402c1014100c0e07200310103d40c03c07008a0401564010050b85844000e01d50600840540900440310551607a1203864801d05003043c80d41d624200b0340700060f20900a5008002404046812450031034101e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 206647320 1250 206646070 206646079
    0x1080c04060c030807030b090f040b090c0a03060b040e030406090e0f060603180c0d08220b040608060d060504061d01020906090f06040b030123010e090628080109030806 74
    0x50030641e000d40048101c10700201004000e10008248a1080d80000c1146030300404041c0a401d08010850b8843c6040e2001d440d00c4000d0b9008c43c00724000050408003020014240501492840e11840300419422211a4106407034070070010a0740c0e428030052003e8117068481d00e07a11400c0c0b03200208031800090000103031750848010302c41d03246e85900070389601c8003103500205aa0001c41400701d003000310284810340c0102c2c40100c00c1c4104144400074201d590304608110301c014600409486048406204021111030200310503c141c030b21540000d640200080c0c040c80b41001a607403008121941280c0070307681c2507580d4070b8040103500440702454602603004020341c140300e25103002902070302c10007040600c241152400b00c0302e03030744540707003910000e00143e00c150351a0b60f91903081382080d1640d0141510410b0485c40426299801110031504100025007401250fa1b2904148050380000403011140388030494174107904d0039011012200600141400414007406928005c0c11810005e800c9900c83d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 206648570 1250 206647320 206647327
    0x14090705030d0c0204050406060f0828020105040302060d11030a020703020f16090b0f04050f040c0b19050c010f110408100501052412040c1a070b010603050606250201080c 75
    0xc16900c0034074034401a030111000941607e9628110f001010582d00079040703103482250025202c5004601041d00c101400c10161500c028600a514165440f24000307001c203038240018005403c0503001f610301c078045542d00046114481400c210345420840741118070b0390f0000741040800da4148400352044038000014881c100d0700031082c6d1500040c50155203035590340c403940031080f96200c00958407904c2001d03100f0040f0f0308000110100c1c1c000215001e840704404040e0004651408408442c8060a040058802d0750b20400b0200c0c0d89078003614400c10715648880d20f150041c8143d20400c4c0340b5504000c14942c0c0c4070f180004060070890790156040e010351911004002a448448902e003000304945c00d461400d0014000211180c010f203101a00c09294200c02c02082000701c046034429506c810b440e40c00404030981c0160075500c621900213000e022340c0b0300100000741c040c1c5c002030f8014100621480c100220f001040d600030481c656441e0807882806404015560400d840790380203141810203519 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 206649820 1250 206648570 206648593
    0x507050a060318060e0a0821010509010303020d03051312080a0501050103090305070f03030914030c011127030f010c032a050f07080403080403060b12280606091409070503 75
    0x1400750640718044c14090319a02000001c80c01403201044440d8400841e80d11340f58190440e14450803840703d11244460758200214071444c20524260407650706034001d00741e5032200081200a0000a000c2000102c40d100200c80000e915900c0c41d914210780e43e0381ca55031441e28000c42402e490060380402d050514101040700803da01404841b4803070f41240c170100c180c040e5441c00703c0041c0b80e07142c000380075030000100c058188900400102440c41c8060000d2060b00840c050280030348c415090f078010040b005900700c1e4608548003c00702c40c110301c001c041d101c0721800340101e80d00355243d600d074020010755200710210301ca0340f8004c400b071940c07908100b0b03500b140d1169a078060200e20442c0814203401d000401c4210410078002c08640141d64000d1400b501c0c3d59807450164040c1184559a17885840c012480c00c060020000e03980c80d54840c206143d188000d0410120020502c8524041c2c0e41c0c1c83c2c5072040841e90310341600070ba014140440c8122042d41c40c240401c03a04181c26608900e00c2600924000709 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 206651070 1250 206649820 206649851
    0x6010e15030c04050a1d070305070c0605040302070e19050108030712080a11070b04021806060a030c020f01020a080403120504052a130501060314160305040f06090507050a0603 77
    0x328210380012040c0c1c1c0c0741c6614000c103201d80199440103a0007484840f000c951180006003160190b480c00c0f0218041d41c0b2801415416210200c91800006007a0030a0f40003060081d088241c1090090040c0c44c11141c54040c0501340180403101007103422680d100e1810300f00e01510605004050150145080c21060391301d4001c0d80c240c102900d000c1180e0040070800b0f845013a805030714441050784013a40e50380300c0c030301c1d11010f400c0c400c941c181e110780c0807a0058440007030103044207445802c4c0202882d160911030300040d4000c215200004045210780384015400c00d0003480103107002920380d100c2c0348013458a031030010700c160694483d85101e00e080005010000d08005101944864071601120003c103112110360f501d1903c0d0401d45501c4000b801e03a0b000d060807140d03c064117039401d40c1e80a0000c1241086664900d12064803128440c8003400c0600101c58480e078803483d0400d1145905030041e90154031003109480c2c0a4505840d10780195000708001d18203044840000c00f8a8107051104488180d40c85 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 206652320 1250 206651070 206651089
    0x108060601030e1905060106030c020d27050406091d0a03050306011407020603100602060709030206040e060f1905010807030605240c101d03040f0b0c0a0c03050c0906010e 75
    0xc0c10b1645448a05074414003c0c00381021066a003082510062914249a961104207100c0c10020a28000c204903100340b01245951442d882500d40025140362a0040d907000b48003444007c1510b040c1c014049400d60782c03070013504000c00340741e0400f2450582848140100e0380608c00058010b80c440e41c2500700098002d001d580c1c0c004402d0130a0b8402940f00340c030309a150320036403070000d50000000040102c00c1e0401ea8203042a00c0c1c0b10f5003140c0d81ca80c0c0b0301200f50b880350f8940c00007030342c0200180010419451441100c40d03100001400c004142a8400d003c9015204461170001c0415002d100601c01c6503407206905a0000c62843e051240c0c030320340004510f0300d0034102c8541507004292454140010034078422110b206012078201c603840e00910310144000c05910b420b0102c203ca06020002c43c144000080d00c0c2a50802c2c661820740a00d000890702c80c980c4070503070034034050003a06410f03c0411600c40d100350045020348060580c10b01140b0800282e10030081002d414013140844240c282d44a00e05031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 206653570 1250 206652320 206652331
    0x3020a140906042601050105031f0b060408032b060f032907030614040e030412110612011707270b211b01021c0e04060306061508010806 60
    0x261a65600001d021841a21494002c4500e500060304c41a40b040e013202040d0040040c104000c1041e641c94a04040c1c40d000785041103607041140201801202929602075003100c1d40c002c1c162480c1c40c2e61940030500b503420031103c4000c001000100401c422081e00b18481003600a03500400c445030034014a01540320300c500020f0071904494549101d41c06514138011468516840f4030010751408900c002e0103007603580542388141e0060b0440c0c0e10701d81800d00640d25440c032402c01450629061142400d01000100810750750748180200036401c0740c84241c020042c80303a02300405800b035810600080009900b03201c414000380d11240d0200801120b1841d40c0723200100b192056420152891451000380000c404601ea1194907488201c44014010034481580507040b03040c1d801e078000002c400d52031820103040c4079015800c0070800c90142050f04003919501d44c09420300c03c190800420106048400c60307002103800075507405060260007020818105903c48a00d0218613642c1419095a1204000f402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 206654676 1106 206653570 206653607
    0xa031109090a1b0309081912060303030f06120201020a0602090a2105010c0206011508071205090105090c10090b090f060a0201050402040b04050f180f0109030203091003020a 76
    0x117106a1030f40c0004100341040d10b0313500c2a000713104180c0c1e000c0d81000140084541c006030248600c2c00a540240e0f40001c10741500202241140c0054020642c1280b20b200b04500507039002031481289a407169015071207000c2000852030340c0c281d03500b0600c080f14140f641181011002c0d11502c511601500090100e0b15a44505a0315510203005a6040c50b00c400d83c91444a4010000e00340c2010782e504e49404039050049000044520568030500e80d079454506000034007404108142c900303042100c0c200342c41c1c0c007a484060400c2d01103104a011940c0c0204400f00295900741c034280560708007812055403940d0501009000300000c0381c00b24455460700c1c446240c20304107841014030488415070040100d49039051140c42190501c05510080c0c0300300182d1288480081c002c42016078800d070021a141c64030b00d000c000240038040031000402d0701c180048410230b507101112110b00c2c4203285 = true := by decide +kernel

theorem cover : BRFrame.Cov 206474820 206654676 := by
  have h0 := BRFrame.cov_init 206474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 206474820 ≤ n) (h2 : n < 206654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
