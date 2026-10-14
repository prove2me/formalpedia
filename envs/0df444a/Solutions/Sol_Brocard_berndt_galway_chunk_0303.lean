-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0303
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:04:53.010606+00:00
-- url     : https://prove2.me/submissions/723c24b1-2f49-4b4a-b5e2-cce0f0ffea9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 54316550 ≤ n < 54496406 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 54317800 1250 54316550 54316567
    0xc02070305010507021b0d0f030f0905100c050c010305071d0a03050102030106110d08090601050d052a0406060212030c0a090b03090309010306080307020906060a030207060e03070203060115140a14 86
    0x82104c841e40301009041c41002031b00f24007003140708000d40001038900c3c01c5e030102c14000030f400b0b09081c802e450883e0800d550141e0751500014404c0c410600c008001880004c1410304100081118003c562824242401146802c003002071a4804c8482c00040200c0c40510803880d507103d00d41001c0145801800966481d078580e04003800c140321030043e40d42d5520035848004802031141504901506404001d03010300c2e441d2030100414070101802c00c0e2181e004141d10000c03002d80b02d144074a2001c15040030060000072000c10030003120301561101d002d40d00310199507100e668901c0c08480d40460100b401d649c56221520003112103048980001500040c00000d00ca0318050000c05441c0e1407009036414407100c0c0d100c601c1117450703000f004802900110500d0201e04286000c10141c00c0704d00701c0b80f03001402c0040d2038aa9906031009440d61f00320319000000c151041d81018440280986071402c0c0980303174101c05a000500c041070783c00400c0150000031a184101510501d0303480100c08641c40941d0303c40105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 54319050 1250 54317800 54317803
    0x1201090b0105120601180203060105091017100303080f150907080a05010b0a050702040f0b04060f0305010b0d05100b010c02090705030702010c080601050409020f090901080307060605220c0207030501050702 90
    0x38080c07503209501c00e86841d1041c0000044850681d6600900c0703a0130b44111031415030188d040582134906001c2c06000700c1d41c15440e1039450700c0d8100501d50b0340c000300048981d6a80e110790009000d08109004412040c0013003500604c02c190407194002c03c04000340d9845003414120349a0301d8819030710101e450240420950701c600558010743c1c4171401048180d9a5805c800750328461040340c0800301e20140142005441d00b94000e005441e840c0402150521402000070101e9025070410b00e0103402d00e060078000e0000c24480c411101c1d8060303940c8200f140321900c68540d0703005078100420a0544851002e80a03910a070707942da43c290350141400d521403c00d820080d00ea90000c031003070f400640c0f0300301e101040c0c0c91046030346600460041e1075080c0303014103045031000a540301a050322860142008128425129044480d0081c5152030295031561400d151910544805500262244540201106443d0140110504c0702e52956034001903010200318168107040d60781e40041c2040d440c0400b0010002d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 54320300 1250 54319050 54319073
    0x112a0105090a0506060405130308180712031e02071211030706052d160804080307050102090109080102040e0c0306181006020c01081e10030c030f0201030606030905060406020306120109 81
    0x20031003c3d14050b5171a1418001200c1e000c0b00c03410548a44081d040002c2402040350f07603080368019004c5081c0d001c1500905291540c00e5010110f0802d020301c0d24418140d028074451a5044001c504040762071760984001e507118040c4c02900c450124201c034001c1004407505031200c002d007001d010364400c40e0f503514003e01142c001100581ca0341029100c0010000720002100c5034000c85d1052003420009040038400282d04655012542504204000308441c0000c00103440741504c02c0b00050b0f0340d40e842e070000421030700721944010960380c014003040c4903c6070b00022155214454100d0142c41c0e82c2e45070300040c5518445031507408814041814840c11000d103a14200c1541d02030f8084030755015150004644501d800c540c0c68100351801d040864040f40d042026640044104840012043d00c0c3c0e240c104110f84a0303407084444008007520b2104558050043c80c1c01400c25048c10400080c4584446480b40710060005002d15400800280c0d190341d41c0d1111101811650003c118090b40d07850207018403074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 54321550 1250 54320300 54320303
    0x6110304031b06080a090203121303060e0d1107060f030c030902090403030506150a021018050706050408070e01080a021320180f0112050402010c1a0a0f112a0105090a 73
    0x13040400092800354403401400300181e805401000c01511041c04840d03e50080b1079007250502c200d08000020442c540a51020b04a4000c0075100b0b014a0280240240074a60000c43c0350750040c1d2000c010b81074100b10280040c900a0038080f40d62840514214010b1014101c000d5002a0704024402410b038141d001c503125a1040e0f801082c500359030f9200d842103000d21440c500c0142d1003d0210800380880390041080c7c42c81d000c1042080a2447d51518101003d0340c02100001350041810040240104920002042c9500c0140c08075410302503115192a01c0001c064004c440002c00030045400d141c0c44000c18401070301c1351242901001200c0c00e1103612691210b00260107509000c40c0c05e1400400c03c1070012416181c0444a072030b50075118001e000018003d905010036202c40d1400b1038440c001c05d030306122925045003260b14090380307200111015142184403c5140903034111058400c4801c40c0d801d8140c12141e4280003103090742524803040c454900c40c0d419401c1030180700046000203040c94209 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 54322800 1250 54321550 54321557
    0x1a0c160e04060b010201020928030209040803040c051f050a0207081606020601050f0f090403110307060209010215100b09030102040305030f070320070b090f03010e0f1005010b0406110304031b06 85
    0x443c0c60001217090380030b40d9030040c0d0f1001c0c00200f81c0350a12941d40c0e01495148402108004065480e0005682d011003182c080ea54403d0002c10031003005008001c030b4001d05400c0391104c114400c0503021400e00c1c0075010750041844000200460054000c00a180061580c4004c80341c034550105500f040f0f0345c07628031805000d0b21403a000400c052600c40d030440c0f0030750ba010701030b0346580c1c420108021041ca00904146c040c00800d9170401600c0c542800203101d464011040940d4400301d80c00024684801004d0200251059900b131191019060a6241c100c4180c8003460740c8505c5c441001900900c1181e0000b411440002046440007500c0405410300354003d0b290003d905d03200e1710708080c840c41c01810440c09a006110103201103013441c0d01070065000d02524040030b01d1a5000400d00f10b032100e09264045030300403907952900390010040300c1c0700e1a1012000b07011551618440744540e0195025210900c2601081e20b13000f10740c20020b842c01145c1021072030802c44428800d0000315900d502588001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 54324050 1250 54322800 54322811
    0x9120f031103090607140705032a03030402090c0d180507060e011b06090309030219030501050604020703080114060f07030504050405060d0b2403010c02010f151a0c160e0406 76
    0x240c603001c400d03648544251000b510080c1e9907100d08490701c1e92603100320b00400382c00f408210b012810800143c00550103002c45c608104840c515142c0039406110b100000a41c01042000010784039110036a4003e410450901c3e10365100e80d508101600c115444108000601e40d03468050100c0018803600300c0d400c90b04c407540c0c9181201c2c011103130070200702c02d122042012005428009840d0754008600e0381d020b4034082c1d845a8030303540066141d0401d4400e0918501044905100b484000c2c0f007656000320080718210300c1d00e9001d50340039114000510445003400b1a02d445402203072542d108941070038a45000d1503607100d40d140740280203500503024290190b0b203020b00003075450405401440d00f66410445d01c00d52a561201d44940c80d031040000140042d03000c414084207924240240da00c004141c0e0008208081e03c031480340100c9100d66149901c420001408002c924000b041d000203081500315000d0b5038601140e201c910341109202c081c06480061440001d90701c1c0380602c1980190f21a0405228 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 54325300 1250 54324050 54324071
    0x204050a0603031b1104020304060212060109050a03060f0e0313030506280f06030501020c0708060a06030f0b090114010f0501081f060c020406050406030516120503040b09010309120f03 81
    0x84074050301000300490048040c58079406031445141207210320482d1042848070380c82010400340d80043e60200c60803034010410b106500032001406078444828030b05810a14508000501584803510015110940e0b50080c4413161500d600290885ea100c8021295034001e0085019040c10300d52000751114020180881c482d1321000d040d2408003840244090f004056010044008201c0ba10802c2c40c0d42d56140c0000000600030b0001c0c4c02407030b03210000f91180a01c2c1c441c0041c100030004043c802c0302858042c00784005100e42100701d01d4030f900700700a20b01c550303101540c060040408a4982131414108000003814000c081d504906a4000317076110b14007a100c002c1120000004c00b1500710350f48401c113409002c0c5522a000c124041d9000800c04241c00d507a50000c01c00f01c0d10b081e00182c500d5049551040004640300051000a1840311820f0789003003000d0715110b0f00c034040d900600c640520002100a81680710b038102c917000a802c82903d20b03d4040c5000080c1c18108004459000b003800c0103003818 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 54326550 1250 54325300 54325321
    0x303090810140705180a091505150a050703170a0b0406080102070213150902070602090a120b130204020909090a0201141201050f0109080708010207110a12031d10020a020405 76
    0x400d5400756404450782c5846110043d95980c0146284801c028402d042ca0010340d84c03041c62550040c50306030310005401c0c600c00b2608084826582106010340c551052020074181002c3c104e5102c44424580381c0d17112441454210f81840c10b0344112304002841200b0701203c0403496004080448003104d0400c04d181da100240c609074040e841010f03500c140e000104e680fa40105401103081d0083c400320b550049611f80c103054080360414038003550025804a140941418680600d1028007500b41d0080c40165156642907242d01e0014542c200c0ca070f032031032496811515983c041e00c00403940105904000c0c40c01c10708540e0356005101050380020003c8000308510381a400845019179112150158241e0030441840a1042000043d41c10407980030400500100c0510643d13024021000c00583e9507402402c081100000c03010f0178900c00c45182504000e00440c4009040482d035047c20700c6428062a100001044c0308070350056504100e08605099441358042003019400e482207404000b90b40701c840062 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 54327800 1250 54326550 54326561
    0xb090403020f0d14030609062103031b040e010605181203030f0609010503100e03070c030c0f06030c1215080106060210050a0b031e0a0203010908030613051009020c0c0402040303090810 81
    0x901c020b1405c101089840c1040f10f403a590100703001d03058000b0000e000c0c500074800c051210002d46950404030034400500c100340c04600c2c00e503480085007030a05003094000b0b1503010040c4a10030500c0000150300005a0f4500118001168000c200c140016004550907031264812544510050700900024070f5500d03150020a06036200a40100704032101903500200070720305801521402d01c020700010703000a044012203030181d44114a00035000d031a0020b407030b982088079040b0b1001d1508100c44022204c4d0301036002d90b0305000919002c00c03450510155060f03128103a41100005500305000440d84a8002818220504400304200410355482c44001c04594a01c0704480c0d16800480c1c80d0394005004035840009640c1c07034400c0c0d8404070181c0e40020b0840310300c400100c901c0c043c084100010791401c4c01400c40c05841180c0f05100c1884c101814102280d0b0500805604039400309070200d848408201c800c0207a10b01410443d42c0702d48900707024099581509c00d5000d03900c103103440843d10040a0080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 54329050 1250 54327800 54327827
    0xb0a030b0102070b16050c15120702120306010323010602010e100902091f090507030605100c03090b0a02010e0304080102071b06090b0f0d0207150c03060303050405130b090403020f0d 80
    0xb517420014407109400329140c1000c03081e2403a1003502d0704000940c2e82c4003c50304d00c2042003d9081c1d901c02014a1994250000500c00d0080d50080400da0b03440d04514401c9a600507024030340019207014104a0f010003840400071001109803001c00031030071640540c40481c0255044040b2030100942c26000b4040d03032600c00d4004d402901040c0030860744080e0007160190402c0c90100e4200c0141c491790403004640f8100d03605c00010303454070000c020b6420712601072850805d444c0303055944005d01d07480103009030a15100d40e90540c20005102d9462038400e610050000c0d000c0020740c0c1c0c1d195503a0341c0050107500303e008186d07240004400c061142e00450000c1808460700ca0b01c410380001d240c0200b141250704580400242c01900b088003003a034880d01d2009110707c610800c0e450600c01a00f8800c002220004941c05081c145005018000700b41c110302650200c84084481d2035840c0d041c01c0c02e04028110501c400c82c0c0040030201031208050700807500540380d40e0f166045401202003000c04a681c04141d070300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 54330300 1250 54329050 54329069
    0x20708120403121407050102090a0b03090a0f02010521010f080307030807050a0c1203020d060b0a050702060d1410060f090e0114040b0901091e0203010506090907180b0a030b010207 79
    0x2c200094a030006044580035505182d50300b04d0861280106136802030800320380c265070010302203110349401e59041010700910400380e1704510381180c02c59620382d01600080c05484424040c03100f168851000c8860011078400644d01e038000c1c1c0d107000f107400c7c01e0030f00440b441c0c104800c03000310303010b10300209803100c0b20703010398500405894030001a591940203540c1d043c1000340b0321031302501050510401c4111604656801030707403000300a14050480b281604820b6100c0c0d4100400d00c006030740303c1f0031341c0c02c1c840c0c0444074140c2d100d41302200e0100500194503000200391030601002003005600034404200c0b98691641c03030b00d1844000b01101e0450540c0946161f0840f8200140b0214030352605d039410f403c0c805440016401c0380ca80010315611000d90000c0c060b01e4840c02c10401f046c50b01366400380000001c9400b50305650510002178540c1c007510705131314080c010345800164180e10840320701002d068081210310f00c032038807040d41c40c01d1980050b0380d04020901740405006c0a510000e850400c807080c00311b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 54331550 1250 54330300 54330307
    0x30905010b060f0c0f061e0403020a0f080a02011a09060402090414090d020f0a0b0f090102071406060f010302071a0c12011509120507031709030f0703060b030d0806040f0f050f0702070812 82
    0x10b800207107da101800c00d80c210300c641e42c5c01e1340c000b90f43e50320400d60f0740c0d00540500361203000303041d4002e0035600c681c2c003d030b10f1000c10b0002c01351142e2140510990041c5084070007588942e030010103d0010031001c441026107014100622071306038004a150076031442c0b00d07070940703540c0301d090407110f40e456000c0351000305400250000031300400a03210000b07401c000b04c000050314280c12915004450410003407001034507000740090000303a240031689031099000a080550510043c2d4440b28008039400c040801203039070071000207101c0c25001084074404014608409070360358461a80c000000c0005885401003190700101082d03030a0300c2944107081e66844001007203000e0450356040f8482c0608401a400108184242401035405001903681030030240001d10340036207141030940955500c1c64400f80646c01000100414030ba0028507503902c50707015100850034000081ca12001071602c1022580307400d14001c20700c8001c801103a82c0a0154541c0d030708407035110342c40320035054981c0c500d41554004800c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 54332800 1250 54331550 54331591
    0x40807030c03050705010c09181a0909030403120507020103050a020309060411061306021c05090d1b030b01060305090d020c060706051506041e060e01050901030905010b060f0c0f06 79
    0x2240e4001c40180b00b86042d6042001c142e4680b800e480107081d1800102d910b0000a00000340c8545d14101d0700324450340301b800560342c0a0580a00d0361480c81c002030141104100249050300c08104a8004640c000701e411111440039600070070640003184102c0c00641041c1c0850825025070082d44d01074403031070015116685843d079030712140410550003680c000109000511540000c114400c00404541d0007418156103401c1c14154410405034000090000070b1011807415110004016841d9500602c410091401d550b030041d030120345c0380d100600c0303500300c14000308520381d05400481c0143c010004503a54407812030740c10f0340c45800c41014641c000b4000e00200000c42d0964100d10382203002d4899010311000c000010500799130050300039045a1821141c6003200d52042c1074104002c009a20b40391448a440b10f0008200344500300200303040545601c2c801e81401400e610080140d48000c000c0390703543c0c52040c4c5002d5544c0140c130201880c0e015100801c034804c0e101056080c40f408840920403881d0920703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 54334050 1250 54332800 54332807
    0x30a02010f0c1b060e0102030a020903010b040608070e090a150207120201060e070c02040b0607240902030c010309060b1003060906060804020a12050f0105130605010b070507060302030a1104030b0f060904080703 92
    0xf506410341d415520f490107062484402c1c401140075002108016a45100307840c1410b096810070110240a18a828010004501b0114040003500c02c0110441e400d0713200c1d074190703e02e0032448030383c00f5055551304501a010340c410ba03401850503911030385503480360501c10082030b0b089440760f02c1020001d010039000240f82038400c0c0500c18080e80b004100243c0010b034500415007540000304122440402c840150840c080b503210340501c1010740e0203003031180781030b40e5020076120b02480c40032a060541318180300c400c008454120020032200a8481d00c041d04401c00000c0182c8120308c01e80d04071a11784000881c00030301c1100183d11a58004c0c11040b50703c0d10b0050541c6800c1c241711000e8805000340310071407403044405c0c0540c40c00b800851419060050303aa00b411011031f101030744840d094a200700040c4002420110701070040300c80506005031030741c0c2c68200301d002415500d42c810444d034400186c0441000a58402140a01a074401c0c041d000d07075801d0f092110220050380c0107019004203010b0403000920 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 54335300 1250 54334050 54334097
    0x20c1c050601060503070215010b0a1b050c0f040912020c0103060f06090b090d0b010303080a060e04021c14030f0c060603060105010518040f0219030e010b130b0a0e010602030a02010f0c 81
    0x12900c1261050140da231660f050640007a00003207000c100000d01c0301c1d10598414003003080c404118602d01c00704002070340c4150340c41c100101071a00492410040308550b560b1a4051080d20790000e0180355000c24203a002502c4100201207140401e00d483c0000c10210010710004003618000e4407200006400d222501c0280d030400044e00c0d5020602d4181480058550303211030340214400e031600e091a003004003030102510015009040010000790420000d41d135080078441e01a20502049901300c201c508040950403440e0726500218800014061000780c2d070103001702203060b401415540651a0300341016240c50081c40740500062013404100300d00600000c01c0445110010070001c0c01201540101c41607800c5000450f8902e0030301141110f029401d07018440c90020540c008120084008000a05982c4014002454541d4681c1c03002c200d07803140003c0501900c08515000301560303595900940d694400fa03039800065080800b51903120240e030241d441c0d18030380f60710b490540d610a241e10b00070080c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 54336550 1250 54335300 54335311
    0x102010c0206071713120801030c090207030e0105030604060522050901090305040618080a1a0a0b0a170a06050903040f0b09060703030522060507090e0f040809130c020c1c050601060503 81
    0x180b91510217000a00007a00f07000a0b040300361501a59585141414101401e0551140b0065070040041d80002940800e02d0101c6040909120b9125207800011500416594101e980c00c8106600c10424100c0311440742040d500300e0306002e0100e0303600ca15020303003642d4102ca0001c02040b000d003c140020b5001d00704c0105040fa002c1c03800c5501c02d5645401500d0720541c0c800a07228080c803001e40795030100e4030b00000303079001000240c180704e180741490105118007010b12031000e01c2c0c9a80d0420008007801849002150303908041c05200d00d051040d000c5c2c0d101d5101c3d05c65580b102125800004140c0700b101c05850042030300a0900341051010b0314250050301004009503282014000c01212848410802c111214002d080025a43c034141c3d0000e40404110b401c8030000350314500810100c2c0703104d2180564002d90080f412a25035112902080041c6911900c4051141c149a18950020b500280400725048125025850600440b152070403c409100d405001070308454014403105004030b00540d00803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 54337800 1250 54336550 54336571
    0x1050a111207030801091406040f020405030a0c1502060903030402010302030a06030f050a1106091e0f060d05061507030e010c0302030405030d080a050603070f090f1104090b0102010c02060717 84
    0x1185408401410512851804901c00c07001046400606601c42c4415015240e44c0300d0821a00c8030300e0642c01d1003040700401d1315200f203460307015400d07403101c068050310300800300902218207100181c40c21100d024007074002e603035641c5488103510843d148000f81003401044030101951840c1c1b6240c004402a500c018134585040c2c0d154480000051116400045040d00400190011604902d003009031110310aa0070362207880c1c1031000030069a2840c000c001020b8950404008041038400802c005c1c000347d90295510032000710f0041c860303911a40081e4421130b82100d4000303d08030307405044c0c04907004480c809400159a98611101540943c83d2402140d00a00459041a560f02c0029150011350f031071660019080d04184021401c01780a49038110104902030509079040c548161081645440b90b8030f1182d860729600070208406900841c121803070760351120b5480740c86a0100c409072804262850066181542e18116070744049000c60054110742da6a81c000c030740c21001129800c0003e403014261 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 54339050 1250 54337800 54337817
    0x606090e0903091018170d0c050c041b03060602060106081609080607030b0405010509010503210903011118040b060409110903010603031e0203041401050307030e01090501020319020408060601050a 86
    0x9aa903041d074410303d6102551710401c008a40004100b03900d54160f00034810441240800e98941c0008a07001e0500140351810311761060150070800d241120f03202e83c03903070424600b59a18002c0c002c80b8280c40d4588100752424407450307640f16000c90f52a8800d01c141800a92844081040c4d140f00070a2440408071528040740c0ca42c1c0c0716010b10381028400d07156400031035520b51070b00c041400e0074000c880c01400100c3d1030042ca58035140120303441d0036131440104040d42d00380c2c01080042d40140140c640d40070010b4001c202c501016020f81900354400e01d1182e041b60f02c4107407282c0080c90107004611241d40068000d60a040c031709400d50000d8960496910032880e414440c000540d02c091040f500118003c0d0f640020070f045000090380d4941d5100303c0e41085410403c0284050744202c4c24120b100c0300c0030300e00035030f899894410403401401540e24080695085c048008180310054000e540148450b213140c14848010b05a0041284114450f00e2069005140080e40a40c02003015018110690406050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 54340300 1250 54339050 54339067
    0x80603152202060d0507091a04050f01050307020a12120b0904030c26130306050906150d080d0c0806040c02030a0e091b030a06063b030f07080a1101030606090e0903 72
    0x60320705c102c6034000043d00d198410400c0c80c0384622000c468003843c450303403442c1504080125048480344c40c11203050002c0000818000d61081125820464100309450b10003080303010002c1404503440707407080707047e0304101c1c9810807880c159180758011035241d01c0e4644941c9440c1d0b20000c14071003071016161416900101070450f04c801c3c1000300a8442c45000c40752220382980783c14012103401601c14400c0342e208a0400c010030000c90015001d040b0120740751724405000703140c4082c4038483c12844a00345410300100010180c2c02240c104e0165004640a21483c045100300f00e030b480c0110903a410000701050846c0b0240d041045403290002461440b158a8684900050030594403e0b41e140543c1940d0700c1042203d641c1c07050301c01030b000856000810102d80c000c0c1c8101d84110226007410101071960811b03a2450b54100141204000300100755040c15607508510354445144c00c0c005d07074490904003050100f540c070a1041e441a9062a29001040c82c03d0410030526800000c0240381d2505c0104071140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 54341550 1250 54340300 54340327
    0x201060b0c070519030b1305010603060c03020d06060e0607061d0d080415060b040902161b0501090e0c030f040f0503041202011e0206060402070206071208060315220206 74
    0x2400480d10340c02000302c1480d00003403201d03201301e120803607459a014540510000d50705110701030f0040b44120701404050307528207000b4014038050b800140704034604410845829055000b4005403007403d1400c1104607500d038001e50321901c0207142c0a80c480001c000c9000000c0c016030048025000350707208820400d00c041c3c410303454000c030448158081004901000304200d1030070301100101180c400c003440141c2c40c00c41920124001c9000e00f000307a98011800300103160380e603064400c07100d401c441d034865a8100b4402d50302910116000781800180c0032040030030858860354180f03004a407031458a80c556510140848a42c440180003150840c411513550b0010440c00c0001c0c2000d0280c03511540049061407002401c00c5040c000c40d15084003109810401c02c60b004030311203a0210055902583e1980e203480050740398840c05000400521941ca0700c1e1400f90303071200b40640300c0d203400d80485005a45000070354440000849201c07520b200a0320248409d1441074040c0f000941c405416642400843e003000d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 54342800 1250 54341550 54341557
    0x30f0f06261908040f060e030a0b1315150b03040c12020a090204080607091d01031101090902030f06100206040f02060a170901050a0b010e0f09090313030b060a0509070f0804030201060b 81
    0x41c0e4034400d001c44c05020011410700110024030746d5080c0303042d422119402094881d201400003070010b0703544100060080006038900101c1c0e0f40c0c05004500111018203800e0020702c6c0407202040c00c07803282040450301507114070460340102d400101c01c0c010301d8903145800c41c0e66441d4800498102200010020351480d0500242018007200000350200703240400d402080540340d44d100d501410052800c03580c03001181103003141940c0d040641d04840b041303213000603200180681d11401002d03200204000c5020040d80c10f160181000b01c0c1c008181c0403240b5403ca95800003943c021b03040c5940e1285900040c0780c240e0040c03040300b0b01c038207000c801c0c0c2c06400340348000c4500858058040365103c40410458114034469106a20001d0810f500000700813030204810000c03000c541d5014001110200d09090010000d86525011040d21108880d45074500200080c600340d80720340c0100280840441c840c505010550b2041040d6503078034420284c003180490b40404060825030135550f841700089808802c28004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 54344050 1250 54342800 54342803
    0x307111002010902270f01150f09050a0e0a0b0a0f0b0a02120706240b0906070c0503010219080f010e0c0703110708070321140f0405060406030f0f062619 67
    0x14500e95040d078a200c0305c0100780051004e45000e00440050141000380740b0f114007076035050719240b03c00600c04001600d0b540004d400170b980c411a09900000c80380c0b03a0b41c03029482014100700c14880c200802c0d0511244076614040e00740081c18541c41400000d42c290040c01040860788110f0f480414000010850380e032000c0c005950345500d848180d040c100103d081ca03a0340c0394460b55203681603881d0140c04007140c0604110940b040500243c000f0074042da24410354043c01c00100219951045018941c030f40351030b404200d03408507604e1400540700d00c0040084034103c4e00e4604074129103545040c460712442d401071404400307215590b003c401041c0000c00c0483c0c00750641c0030080c41400d0a6040520f12074000c0400640c007010003841d00e01e85c2c6a40a00c800b1404640140c40c113443c0c2c260505580075034003881d08041c0d0040c01c04500000c00c40e9043d0004084039200740410080c180500704400291074450040c0c050343c2c4070103100003240032540b01d142032241c0b03220800d03503248140c1041c0c00b4011500d0483c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 54345300 1250 54344050 54344089
    0x1208040e1602010515010210090320071a0a020303010626010b03071407020a03023001050105100804020f010e030c0402041e05010801060f080a0e030c0a050f0307111002010902 77
    0x101c0d1600c89409100b004d0b0001111100169442c0310398000070b50b1814a01410740c8c0c030f01d48804104007014010b80e0035070762020b46500c0ea54411210880c2c010ba407a82c0702d1083d6204040d10803120090440d4070000c070303100c00d1000d901451651f800c2450503a02c00c0440a0700d250038032250544ca1110703018180242d8064001e2458841d40c81c06c00c1031008141d10742503010487d281c10100700d01c0c00103984009102080729410f695080100300b041500190034081c00c00c581618000d000c5424544139419031225040c3ca0003210307130243d81c05d9118001c9602d9003003201d00940169060345804915800b560310102d040360010100c1d03202480010106c1e05a030040c2d4854030902e529252075a404620b81c501c003001921083c60001440e43c9090001885080d441003001c0a021564001c2414188150030950081e16005c0c01c80340d8079104480340d00c2d52074010030420b845a00070404c000d50f8400300403003120b40f15070300b060300c0320940300c1d4042c10000700311b464196080540d0740e18804c002c010385410011140071081181c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 54346550 1250 54345300 54345331
    0x12020a05011109030a151107050715030903020c090604020903030a02010504020418050a030c0830070f0203040b1605011409070801061802090109080f0102070c0503030c03041208040e 80
    0x3500c80c0c2034441240c80c00d800458140410b650585001424102c07013600045c2e6401070185480d01040244000726032001406000100783c014000d002440ba4115040c14610351a00c0302e00345421000c5400c2c528009005030401074128105207400d004064100b040208014584030244000904c1c681c048200b100140c0d456a0401c019407500d4032444031079408e0032800d04554000c60340d9150302e41c0e5503044014107001d44007510609100e040f10644082160121201540c00c1180c0e085800c0312030500d40c1c4201080340c0c1000140b016108254031004448150001d6061904020110f2115041060701e0340c80003064041c4040840c0c0c00b4000c0200c0c01030362410b5188207082402d525400c065041e00720740d40750b0381044420424050107804408450310740450040e111038068004851090459110440340e202d0700c002c00b0941e02042d0f000344043c41c400c04051091070354550515407039004030342c040001508244005c1080c10140004c0300a094030521075035103002e4907001c4910112030207881140e41007000c070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 54347800 1250 54346550 54346553
    0x8060108011a030d09030201050304030c12080612072402100f0b010f0503060312091c0503090103060503190204020a090f0612050a051b0c1f021e0406090e060a0312020a 74
    0x400070341c03182c0c04250060101c0340e001c0e8802030281015071200904002d00000082e007414031420040546503480902c460450700469002001038030b0640701e10388203801c9010780718100c1d80002407410843e0460003811007101201c8040501407025094028158014040d01e000105480d10905804070101c1c000041c56680400006200301008000c05091200c2081413000e207640010302da109440344da95040b0b0340d4000780300124081052284984400c415490300203801c020000c0301820303c0c00000c2e601000715560740c0d01050359030700000030745018a14882c11103602505144c2c00804034580a810101002c5036501443c0c2c040390081d6201c5000541d1450340c10324400400c0c080c158004400010501c2181410184403418a40c641501101c030000016413265001c7c05000f520342004036250f01054072a01e0500c43e0300a076014484032010000002c10f40c1e070207800050160360136a070440d51008074040c146140c082603c14050007040d03005005690010000f8941e80f41c140200820f54058a00144030307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 54349050 1250 54347800 54347831
    0x303030907030c0b04030803011206090803102108030402060307050919030b011a0306040b010306180905100203040f0b280e0705030316030302130e090703050f010c0503070f02070806010801 83
    0x640c102111903c4100010401f050034001500e0550364540004070303c04800e490304034000d10a90500610515002c1304020344070810205030301c1190047c0f1008040101940e81511b0004200324006200703c505102103409801c008015550140721414014542184000000c8001a035000402c01011001405008001c6124092401014091603802c20340701311041c040d030b05000c01003501c2e01507682c5035071140b0280e1194100c800140380600c00945441d48400842002d094085000d484a2241c2104c6100c180214030840303120f250001903003908200140d440481c0614042d10445802d006c00c03040b00241800380a00c07a40720703547c0d09e00000c1c0840c1181107044c04c1c00b081c0d600c514804c0e0801d111010007104100d000d0424a40c0c1480d006075104000b503c1c10301c1039001034120b5981c0c0e90341c110411680d100001400c1003643d0094040302c0301c60f001040170307a003aa5206129000010800d20210391081d000d0510f98151150a006840c016521900d5030392610800340e000303a070301d1ba4407164054200440c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 54350300 1250 54349050 54349073
    0x1080706110d090b09040f060909032006010506030c0d02180f0102010b011e09080a080903100203040804090f090510060f0b0301080727060b07120513090515030303090703 75
    0x1a090040c120a980702c0708050710b030400f00d110f600e40200300050b10110b9035907140e0051031140c1140358100841ca4a03160007000030680c4036000c8022441d44582c000c48079840d080350004010400c0010407050b070a100034820a6040580308070340a25092141541d00302050003c0c194441003607072a907180d01c201c8800c020400709041a66819a403502040c46526640b208800114050f4110301c4400c61003e0b4000b15003600c62075010305254002c13407132100208444075004150500c0d0840460302c0d081c2002e21071404030310060b1001032080303d0800003003004da842e90b00b003c42c5454000c1ea0004019801c1d4450760f09001221800f90445640d0301c900b80125201d0018203c05405c006c10210b0856040c4580c0d26500e4001c0d00410080c0001d0010446000e04610b0451252005413a4140900b0b0380d40c00320f241668000c00d00884000d42c0000040c0c41081c85003081e129000749034044034003400d241620039401010003600c00791b180a038000074422681c808000550061100c034006000c4549181840e210591 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 54351550 1250 54350300 54350327
    0x7020406050910210f0507030506180d0c06060909030905031204050d0809040b1009090b090402010c033510090b010c110d060c02061009020c0a0611040e01080706 71
    0x86510091200c03a00d80240120f040d204039183e00c071085190011441d4044050f01d00007044900000c0040041082c0464030348112807240d811205a5220022003072283c0c1507001894005503c401103150003e0700c28650440864014200050a50f1310382c400301c401da404820303060740070400b0128200024282041086107545185001d81d040506240028035190704118001d440310f0b001041c004526560741d4000c412440740207000795100840c0c1240580740c2c10080c440c849009141c5104024641440c0d25054401c0d0303416034800c243c10005980580724401e00c0f001450070440300c5241170175158600c54020104007014100c03145c8610f813040964100c2e00b49a040070070b88a0405403410110f90300312030364003652a803042c000300c150740b42d643c040f6500e0314030300038007401c03050802c1d00f07050202d074000c40c241d07005103003a088020344140c40301c04c0719080c0d00c99031544491a500c180e10340c401184882e071082c48005641101d103803801d59600702c0c0c014054000c0e0003000881d01b04050412240d50051044000b09 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 54352800 1250 54351550 54351559
    0xf0c0726130e06030309040f020c0102030f04060c08010e0a150905090a050c10052b14010518270a0804270504050a060902030c0904051c08010e13080c0a03050702040605 74
    0x5180070f40200f174a902a040305075000b1503d40403c190010711030340540700b114448000854480c03070603048031259050161020b8032704a1030703d20900b628511402007541a100c01007413a0b1066212800c045c0c00074a241510148001115080420545028003ea501491100000300180ca40c0e43c103203e400c10202589085c4904151140c12115036044415910060540c4651030348100c0b019421742d412880004140454a14265a60000b510310480040c1601c00135640e003c09984103c28050302c0c0031080d07540300c3c403031128a41540801d60344400a40100310140c07040d2039648207207030390348a01c2c3e0b04580c008404540c8080201320140d002503100b14190440040140164100390f1286515000c40e4200604503a407522103500a5450401814031401c0d03010745000320b20700d01424281c0e110305660030351b060b0018802d20000707482c500c42d0a08034142d80301a1407084550f15140364401950402000c12114100244890000c03141d040c003001c40c0d001d02035110190b42d03407402c0c41044115145a000240304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 54354050 1250 54352800 54352829
    0x1a0a061803020d050a050601090603060b032d07120501020703030509120901260405070602071203080f04050c0d051f0216110f0d03030f050901050f0c072613 69
    0x9403040c100d00400c03260140d9290390002000e01340207080091002000c1c00901c900380000030b0310701c81d40e4843c100322400740008001c90844c1508050701c2c7d0100d4607100342c400512003540c0e0060b11800b140000000305a004850015a6480c000c4d007004050314000c0c3c40f6030354086a40402d0542600845501849402c0580342d030590341210214240101d50607076042151042e034503400c2509904034203440d020f5000544080c3e02e014501166180d2070340c000d09005009040f00080e10307110005641071000d6243e01d9000140d236840d0901c080c07415004005698520840e03180ca50903032103081001ca0818040c4000d0111000c0b0b05401c0c18001072902e4014041510400c41c0c82503400140c2048001d50394810030325401030411030002051994401582d03607104803c0b4883e0410142c066000780b4504840c0b40051016a5902600700c0c2250405c4910101c01c407184e500081900755a5401449c0082c07003204814007a21360190100003041d0420880305442800141e03004200c000300346540014035820820034803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 54355300 1250 54354050 54354077
    0x20d0b0d05031c060b03010b0c011a010c060e01020724050105010503040c0b030601110d030906200f031b040906060825030c030e01050a0b15090a05060a050d1a0a06 72
    0xe8900c60800c2c2200303c44044a50340c400c1c005030b03070407080c0100300c44428180c503035071a000c01400a62003000949050b61800d101500380d54030b190b081c0801e00905849205a20340e0070b4841d10050440540b501025540c200700710000500d8104e40401544400c01007840c006104012000032100d06030405814400b0500c10040021450702521041e103249880703046d2603444030401a00c94907804010340025001d00f903503151000d036060b8802c1c40c03d0360107000d050100c3e42c805401842c80075090310f55034040020402240303419440f400000d40c0c01c650000e41a0031000c81d41907110f0f05a8009404c583d074100d441c0d8030f040103000c0d4003404194114102036400010b035228090121101103900c4520001c3c07540307400360448010f000358026607454583d100240201c0c54a0300001c8000d00120171114498050b908042c0342e108004415610400005000443c160341030208000f82038100b4408003080040070080e00000d075102d800b0b03480c0c41640d803465480101d007802003041590000b17608880100b010100c144807 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 54356550 1250 54355300 54355303
    0xf070b09010c03030b0901030b07021203010b040b220902190203030603070e09030c06011701111801050708070503070507090b03030705062212050301060e06090102030a120b04090501020d0b0d05 85
    0x20038106090801100d0300a00f40f40690103000400302c601e620400400000040c428000020f82c810f8081e9400d8030800e814060946086000a00034900e14280510080c071407441c9070340050840d101c134454000704092560280a001d00c0340c6802030b034001da0b008500c0011400700c80803110420840c50000d5415071506130046a070311045880742c0780003100307140003241901405004507054140c40700c040e20031079a142c01101095032a08012008658604503281c1c1205611005603210300040d08210b1400116940046030642c00030b200c1600e04440410108001450410040540c20b208101500e0054a000c84035011901c440b11010300a4004016142c0001c00c0403611940c001c031041c4d10903240c0c240b155103c089501c1311410042c10a180001c2c01d81020b60003d01035812135900d6540c0345904010030040c4a0a4041c2e014003a025174400c1c001c902e522030240102038050203410b40c000940c10b1442d000141620016802503515075800107050119980c940125460b020060b00c2061241c0b00355515203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 54357800 1250 54356550 54356557
    0x14040f06030305090f04061208030405070e0c04060e0102160303080915060a0504020319021b06070504060905240d0903110601050102120a18030308010e0703060b030a0906020405030d0504080f070b 86
    0x50344a80c241c1c02d100001ca964581c8090003500c042349800100d000c0c01d00e03001080345c0c000e55041e1064801c04e640011112000340101d40700b103000b01402414103103040d0042e41e20380504038420741036004880e542c4d0300841d010061080194040c5d51542002c3c140301f00b8145c1005002015140000315035000c03c00591900600441180c00580f40141e5a59803140354000119800c07200190240c00001ca000300714061819201540c3c40a1007603814036251039405549500c290b00c6000042206407404001c58644007120b001d00d440c21084140031000c1c100500c902950000340742d10050b0784e030340e8400ca0906602080e40f840700081f44000300b0040d41440c0c0040e40e80c851880302002c00c0718001031042205d41c0300701d4032080303000084480000c0d00740e1070380740142010700240100d030071001c1c1310400203003400d100303000d00e40480e04210711441c60b40c0c076070110140140005c580d0035550180c007000000740e0380d113042105a003c2801c07651655211030a214156040489400c5010040d500c14901482844a001e08a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 54359050 1250 54357800 54357817
    0xc0f09051507080d0c0909050f01032301060f0906050301020405032107050a050c0f0303180111011401090b0109050d0c050402070212061e0106090311040207080c0714040f06030305 79
    0x140c1c1c00d603120000c41d211161103104001008584003040040b07800d40e99402800c40d1042c0d90700d4a1440302c0c0c441020804031007044a154511080b51401000400c00f00d1154115054001294401d5001313039100c6c443c2903031a41d60190640981e0890304001c45181031065801405e002c500a44c98240b400001940e100e0450910062a288191b0300d0201e991900c4201c07030510b903102d002d803030507203041d81440c2d038481190724140b41c001c00343c00803101030601d07000c02291a151034420861041150040044a06410480d0f1720a110740d6030f444051409a20400c41c3c50003000340010101c0c4002d500400100060039039841f66005080c10081003000400b00702c3c4881c15a001a82e0050b112101800091240e03010945040c2c200d0041c20b09004900700c5a400446003000c10f06003c41c01c690303848008481c04201884041c1003030510b419242030a20f010380080c502103020394921130825407100841410b15626a110b034000071041c8042041070304041c0124082c0f10065082000b2052850300e000c7d0003885000c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 54360300 1250 54359050 54359059
    0x307050a0303231b070503070b04080a0b070e0a26010905070e04060b04090318051504090203090106090e030a1103040b0706020703021f09060b0a050330030c030a0c0f0905 75
    0xc9115010b030005139100d4103024180046410682c21020781c440b8660f0280d0303030203405603150110312418254200c8044464460050810740e890342c031010441c030b202420b968200303c4100c0071070074139540d4043c8810240803001030324102c0c000ca0803428881030301129100f000c05c1c0d041a071907101107000800c2607407c80d000035020940c19030307491130310740000d1111401d000c0e48145040509410316500c40d401d05100c4050050742d00f0115260001c03c500390f480144c7d81c00841008000900c103012054024581010600c030010841e02d8803104500c0907120550064690746d4004507601d400164006052090b400511001d1803805040043c880454451848050451600066910b04051081150b000051f1152505058401c860205203019004a9000b940c4407400c080a0360107d00d041500c84044030030040c014107000704d03e9014558801c2124010020101603018008039100c80a001107105140d04282d030b0303541e481c0c001b030140102c6221014203810044210b940c02c0702d1680244442c0c05645085a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 54361550 1250 54360300 54360347
    0x1a09010e030c18090a050105010303050306090603070e060d0c0b0a020a150905210d0507020706170f070c0804030b01090203061c0b040204051b0f30040609020109050d050c0307050a0303 81
    0x501c091401c0d170700c0140103000351f103000000414103900c00c0142d40500000c850381512034580c0307030030141e0b1022280101c400703000c4900c01040d001e1400303041b1090340030700c21031510601d240e4071070216107140c02855400c00503030801e4509500308035001401c200700d02d9a8920401c1021aa62511a900c20fa41c00000c607015110940080d00e080101c0c0a861510032014802d00440c9820380009407101d50314402c41c400b040451402400740141046414402c05401141d03281c1036896040c1116a6070406a0645d01982c0401010003c030301144c6070240a030410700c4025079242000da050000c1c80c41d030000d92070054032926011500080c10342c0306041c0c001d84c044034045103070340346c280303640f0024007032010594844000069543c3d4210074400103018240c641c80720482d0311121804030840342006800f004201040008009000960b50740d210f11000c0e030061516240f8507440b040801e0100c100010103990962210035507298510f01006843c0242000751820000e0501d1617901070240c041c00c0094034004488203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 54362800 1250 54361550 54361561
    0x61806060d11131404060819140f0601030b10030b0601030c02010204050a080a02040608030a02030a030903030209060706050414120901080406091a010602100b1f091a09010e030c18 79
    0x2a0000b80608a0284002d603445141800c803102c607800c0c6216894980c0e201503003400081c5098403418080354060000340100803d10100d8140b00d9502102c115a084008100342200b03980410016614000910040c00c0d103504500702005000001049201c0142c0408410720000d041210000c1d0055000c0c24003042c00340d05540207901900032504a180c02c1242e8100c00207544400080300001d040c000c2d1010072525072901440780d00d034802c5100340c0300981c0c000c1100c1101c0034829407100207224040d2400609014900b00000e8556106000c00e8429503107e005100901c00081120326190018400810060720f040e0301c15030302c5002e40d064050510a408d0000f506014481c0c00000c40b041d4092901901c24500402c0141c2c1c0030300a008483c0144900c101041d03013224244160b04034980010300000480303800100440d10324251900100801120b014000742080f40c0c000d035254042403201c10240c441d0320b41000181000e040210640c400d03800f60074540043e4032643d4455851024a44840036190307940b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 54364050 1250 54362800 54362827
    0xb12090a0309030303050612030313020f1906050a0203070c060302042103021b0307030803040308040c08010c0905040c0e122404020a050907050c030f030f1302011202031005030a1a06180606 83
    0x150503023014000081001032006202a243e08068821285c0409060b114001c1c000c1c907044c0c4101d00d4404108546042c0140c5008901034000c003174071441101d190003d00d50714860003d810b60700110210b40c0204007400203c0c00c2280501a201c1d100c10f1091090b2010789000b9580e465080f8400d03ca005814140362507618103000010255402040c03543d1740707080514000300280c01c111401d4850010317a890100300d103003040c06101c4480e195595065812414801000014448200c0c40028088414480b02d613a40710241c4807000d802e404005880c00701c403501c030010b54010b55540c0b408401c1814804000050340d03900c46810544009613000d02d1140d030f4661007501c451146d03090030300603844007083c4005800300c050000d5108600c150103006160b00c0d816012506200c3d1a40c000b4042a0050840080e03010554040c660200080412101d501c1e41ca00210b4140354001c00180c0b09024180b44c406620b071111a0380b00d4018500380c0b840c01c59010034481d03000b80c9240240c60a44540c2e0000360035400c0038107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 54365300 1250 54364050 54364069
    0x5102f0105040807020a0503070e070e0d0204180b0c0f190908030d090507090e030706090516060801090c020f10150302040608030901030b1c03081e010b12090a03090303030506 77
    0x8240000c000ca41414104600103410940703049100304070601c4041001d09000c40e021044070b001915021054480c0d18007920380308024001990020583c0b034110000d41d5860040300340c0c1c50b2401007140c0a150190030550010f220041202922540401c0903030f0341083e00004031800301850800b4940070440c02c0c0d1040300c1560195100c404c1ca40701c0072030044c0e4083c845600815610740700d9030407101180e540b280644166849400490150740081c010480031480d260031882002f4412010740761000000803011820b01c1ea1500a0030020347e6420040c0010f0240d8800c00d041e40801e80001e2802c801021202d0f0382c0c0c2c00810046030801610345200d0040610001d021201959008005202c0707a52100c11096481e0024070036640068282074105c2072909092104241181d1070400c43c0501c0c40c9241c80079102c0342e0001c1e0500c04982148400400315600d60300ca02400781160700d000f10382d90800200c2034403802d0009011144c0c07541000030340f180003d4010352000212941030801080507036803403000880841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 54366550 1250 54365300 54365387
    0x60604060225031703010609050a05010e040213090203091b03060606030712060504020706090519080301051207030b0a09030906020c060a122306032b050c0307060207030305060a0510 80
    0x519403c600a81c4c1344451025505840d229500d524455540343d042042c0a82c40303125031408030710305054519640c24650003c20310318200c6010281c40699880303d0358104d9000329081011500040040151049800b46102800700110002c21990408030009400ea100c0904110700380335001250341c0e40344110360007a00041800410031500c6034401c3c1012030150400310b5007141c4034011841100d0700001c4550b21072080640080d551402e582c2041e05200000d0700707446050805200343c840000000740c41c2c2d071601d03201e0484620003040c0d01c08103280152201140707402030004e5404c0320461a409895a00c1038074070701b5800d840c1800740c41c280d00210130010100080445c886050840081270103100d4400b50314020030058084442c1c600e4440401440d820028001c071410420390f0310500701c0d0f1031044024000c102103c205582c0f5012a5a0f55181280e00c080c40441c04030f92220200700c410b242150701080185010748418440d407419800c000c005103c01e0f03c14114651006852000203800304c07012040c00d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 54367800 1250 54366550 54366563
    0xb091602150408190816050a03151403070b030c030406020a031b020706020d030903050702060c2d060a0b0303030604110415031a01030603051f0b06030708060906060406022503 77
    0x1402c15003403510395540402642109944400a07074059180f040c00c00c1c5100310355020b4112450481c08604594039400440410201901e540c81d8580070300e50108100c004081d043e21008103065400c05140c2000c401e6400005003000038000c01116413000c00480c1d511507808403006907140e105440030350050028a011010062041c034914041030307000240135003902c4894003104c46034514134030304509980c0207503030046c00500140500c00c01814048050a03180c0c0c0e00e1701c2034400701040340780c3d0603040180400c03030044001c0388151480d194020070300485410105007070301400502201400300f42e40784405080b0034003d030354444d41c0100903011402610050038580020003007001120703000034003400c3c2c4416100e01d806410700e0544115802440f8000c21030b64801e020703104002040c0d441015407100207402618041d201c0c1501d00859440704000c0d8032404442d01c2c2c03c149802c081c000c0c0b008400c402004a070140c1810001071110640001c1c25540c0751104031142043c0e0220180d8484902050340e100801a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 54369050 1250 54367800 54367843
    0x11130603020703090806090d050705030405030a0c0f0828050a02060f0408070806010e0f070509190915030804050f122b18090f021b0d11010b091602 65
    0x215903040d002804054042d40e5070600c07094a40c490f103529014251060f56881c1d1044155600681c0203001070030840c2d000e00c06403401c059484010030305022000004171416017403504c041c081c00c440e240030b01015081d00002050b0b070f071801072005004404800160f0344400d820401600030000b00304010391703400d60b0203003020791540300804441101e42c109000b04002e502511901082d41c0030700062940c1200c2c11a40089415156540401c036801c502400940030083c0c20003030b80005840315144240303028460741107400e143e0300e450640c4040310381d000748072410840842e100f0004600001c054400f0703500c2c21035000003403901c007200085039071182c522001482c3c040c1c8008610303908030301d10344c4c8882c5540035183c0580407840d9000803aa500624000100c1e0306e20502014000e4000a600c49075180c0198400140b404044504400c01c0119003031525006a00c2600b0840c4d0306548080c03068034103c0c1c40402408060340e14000035105400042c400841481d1840200c0e401520070001000a81119800081c0c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 54370300 1250 54369050 54369059
    0x180c030706120606050f03040803041415010303080702060402030c060c0307020405010915050102030a09061b05100f0b0613030204090204141006080c09010c0312020f04090e0c0103021207031113 85
    0x416110042c80359040b61030101c0025896020358103d502800028032101d00c3c6540c0c0781d9503402c070303a00050700c143c40c880e0b01c4004036258030380c0c200700e200b001080e0040c0312030b4035603d1490000c1c170012000b4404411904810140001a00c00041001800b0812160f031a20381206401151441c0900c403000382d8020300303080001901101d680d00460361086440c1c480c090880c0c9403001641d0780d220b41030441000441d40e00c800c010361441140b83c402d41d04105500c0380d0300784180752641481c1c402c415030001c45680d0f81e030308030311400305c4188103c440043c03040c0c49050802d0081f451042e004101484041d00039503c41640c0000c543d0345500021540524805078060f80c2000010001110028003444000c610b90001044801200c81c050b9411624165103c505801c041c0d0341c00c80c2c0c00c03807144c9803004005e074090102201d00a07124010f4006420484000900804081c0c0d046d1b10b454082c4403c04c1c1407600c10004101c0b6010754035007995202c061030401150040b403003922214144a40120304081181e40c20340840c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 54371550 1250 54370300 54370307
    0xb150102032704060323010212011e1203050309060f01081002090d050703030507060605060f090402090d080a020d02060f0708070c030c02030102070803060f0f060d09020118031101020f0f0303180c030706 89
    0x686c0c0c1c51003040540d6100d030020142601300c1c4a062000003c0c000208010480c07000256000d26204420100c0440300175580c4038a850000324010003280810004400c1061000c0208000c50780100c0c611400401540342280f00c42d115100c0d106c000c461190000b03503035070f219110081c4440b45a0303440b900715494a80d8034200144547c1090303000729280b50800030005010b103800400e03944100c80200d0807904d0408107004201c000e51103022500d4108880c030a242d00490403036400340010340c2040d006800300540070030000b41007000c01040380c42c0010718841440030b0580d0140446a102e9424104122034800504080d40c1c001440b00000303503d90300015071003040001e580c000d507004070002c0c0ea040305181942001c000a607805142d071182c020005104a951404003a040411824018180b000300c0442500148020000704c0d08140c40301d03e1525400102940e041061301d00141150003e004803c403965102501c0c1e22000c0c021980303c0c908144c0b02c0211070824801070189510007421a006540d9991028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 54372800 1250 54371550 54371573
    0x10806040b0a0203041208090a0b10050a05040e1902060d020304030201060f05060a0c11060909090714060a0f05130b1206040c11070e0c0715090b1501020327040603 72
    0x101e8038403051074042041d0120034002d5030b001c1d603031040c20f2580d003580d0170100300d4080e00001c00d04515441840c8658000c1585610a28000c08004024403446800c4c0b1080c001954101e0703124502547c40c10310012401031780442d90103540030300e4007901c260202441c00010100d000c0e032041d100381288008184410180c0541c13202c6d044508545c440c03040e00d507a840800565000d104c441c02c000c90989103c80000440c440321406075488000e02c07103400c2c1100d800204050b0001180d01a89903803018805210031401d4210403001c3e00c1e42100c10a20b0007801c100b0080014001200728002e00001055194036111444842c41c0500342d2002207603101c0701c620408044020040d245603018500e004c07000680184512042c1e400110544014000e41d803504440d080280002409451402004d012400014995a400e960001c0c84040080b40701c1d0010700b840d042d40e0a02400845117103a400000005598006c02550041e803541c05000e000d442c0700b003a0354144e070440c9040d034503400340c5442c5010040101c020a003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 54374050 1250 54372800 54372803
    0x1030615090317030402090f0702010e0304080a020f06091c02031e010516081012060204030206191b02100806030f120c0f010b060403020d110415051207150c06090b01080604 76
    0x100703070300c0e112960b800f50030340300540c1d029400009080c0040c80d2807410700d52103038000c082d92000242200c2108481c3d0708580254001420b2900011001c1c01503141030b10f0000b05007401101c40915110544000554030160288004030009020031418107654050280324048881c104414165591f0320034041e0080c1002c96031805150348601000300b40398410304919105d204140340c03a16181b1b04040a01d5807440f03103400201c1e182c4d80c0801010006840340c2014020300d41c040b80d112515075103410006440f201c1000404409041c1030f4001c0000340c6c4d543c24079100034030724a04200d01039481d104080b9092400c200c8515004d48100207140c8031001c0c3c2d580c01007640d9000170302541d0780003000028050982d03041c2082d003a4044814841480075150032103410940038841c52142400700501c10104040d82c420514031781d40c440750500d00b049135003411a81c10a00c110740b13901402d10a414000d4003101d214003940140204019100c40d001005060f90001d00c026030001c030945c54641c1d41d581e1550b981c480c1140c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 54375300 1250 54374050 54374063
    0x50a050108060a1b140d020f09100201090803190e0d051b0106050a06080601020f06070e2b03140904060311010315080601030206181f080603030a080103060902010306150903 76
    0xb01e00c040180318104200d0a0313003c0c0420b8001d0303500c104407442c002c01d00c0c1ca007101560401c00041d03207040c2440100440500f500e1100d40700c0e0030100800c0780d610180721000003564104061580021340910489511003a0400344103d000c5e05030785880d00400d0040140078561040041c003800b00b135005400303408941003034808400848030680f010703806e83d40b00f407044680260000c68140600b9000d54101a0300603030620447d041d01e031000014924042c0c0550380300e800b1038003001c107200d07490404031030030042c1e10f500213058071600511840450710408002405002c001c00340141351502e84201c1e04485408100030f2050180c26101d003030a15404c588070381e0050110f072801441c0750742c400f241800d03502242c4a40b0302900090f0b2854003031200c1035020b011403000420a8100d0070000f81e40e80c00340400800c3d0ba1642c407040d031056403003000e0880030000d0301c1241700754010f001c05000c260340608004d05480d404070010462400340d2005074081c00e0507401c2035210002c4070b01c80c11400c40d4008400d60840e0300400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 54376550 1250 54375300 54375313
    0x30b04050601030b0306040b0702120415080604020f1b0c030d030501050f0f1521090d020d02030306031905030d05040b0a060506040608040303021806130602101a1012050a050108 78
    0x2030056040381c01e400e013a650542c000c640004d0125404415240d40701c6018016180840300550100c0d0480d405074104075428440d00505a4030740d680325840e5544032500740c800b14940000f0880d00d00407401030703550400ca00b80c003010051055103418040c1d1200300700050111200101540d0025000d0007090040394050810803800a51030b141840881c008020081e0840382401036128419010740d000c1e0841c14042000348942072440b40702c0b460020321507840314000e04509808110002d0a08192a85a2f401c550042c0180649a50080b44001402100d651a01c0329106d0514040d4194000e019100003014a094200024804105011031281c6443e40c0100505a101c100b004100e01507802984001428400040c00180c000c0e401007104440c0c0c10340349100064800c1c00201d0a91102c1c0e4141901c4800c040d0401c8400e4040008007840c2c0040c01083c0100b15078800740c00c0d25000724415083c0f14107084100040c0b61030082903039507100c0c20030807014060303850801103e9003d080e00b0f20900c03a0600c40c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 54377800 1250 54376550 54376561
    0x42f1302090f041a0d060e0a08030a0b0a050f0d06060305010501060801030c060306030f0f020d05100c18140d080d0c050403030807030216021905180f0705070c15050f0a030b0405 78
    0x144101014140b0b40011480c884c0b002600f0b1204411041500f2580c2d941d58840d0180b111404124016040b845012696900d1500c201c207034056850f4505c1031030054030281d800748096600c0c0080138031030101c191804240740e1080e05248015101d0b44d800942113510340360003c19003503484503015058074000d40400b017150b59241000c40440d811480b02504080401e5000c4d400a440003c0a11407140010030a504524181d15030506080f18205445c04a65640b80881d80d141e421601001e845034044001134070891030089024201201024050710501d03031200382c041006140425650340041221003003041054124018206d90b12500054010420318000280e071076111b4000c9504404c00d08010b031050a0781036003403005e04441107035035401c040000302002c034241d1a9050848520515188212494202111742030300c8003030058800300400800700070354408504140030323000450310825640c021000d01c400003150f00d801030324803031076030107500044013101c280c0e15400218514508039401c01040d19071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 54379050 1250 54377800 54377809
    0x1006081c0809060109090305042c18120918010b090a0b0c100b06270a050405130809030c0904050a0501050703020c07050f040207020d050304090c0503042f1302090f 72
    0x84440d01d0b4650f00c02001844114100d400c80035183c1e21908085080a4499015400640a01a500c404a241c295a03001e60310120580d2640200c102000d028a1004690809071101204010020b0b200740001d400e0800b40c03130f0007030406544011070341401e0455840756070240d0706a0240c50014894038914001150075081d5504a440301401130000b0032050854482003400380030000b603444d5100c3d0051240518004540c201d20682036010140703840d08801c00300801c100b4000e5078001c140138524110070131640c06410040c04030142d411a125946440714400080d181c04024045140c10260311002e21080100004034446c126201d1170003400a0303070310007a0403812406807000100155200c00d00400940c2090b80d1071941d01840600058a00056034000c01c2e0b806a20500c1107a080d0300000702048500f000340b01710029481079240c003519605050319144440c800d800e140b040d00c01c601600c1484100140002004078040181001e2051045d000d40c01c0c00130b402c206074040c01100c0c0c9809112403481d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 54380300 1250 54379050 54379067
    0x702010b09131e060c05041706062d100807031803050a03020d0e06040c0314120904050c12090609070806010810020903100207050a15050402090f07021006081c 70
    0xb003958011403070b801603d82da0700c002054004456042c41c40303811034011441c00c0c0514000d448054861a60b640c5c901212104201d001d00f2403081250440401d00610b0340d070314044910500b98400043c00085802c9a06040004000c18046c0d0701c00501c00d82c0e08031301f13074000000c5031052886072002c100704215110104514908848020009a400c000540815000760301070305030f41c40345a03000204406480441854048162803d0b10342c90040c8108004011190180703001800420001c1e00d0700301081204a070041c0140b0080600c07032510707000020201205e10703080c0c503042061481c0c41501401c0a1401a46460003a0b4a41010380102540811000350000e000c0b41207406640c0101444034000412200a401042c504e90b0300d4040c80d0240c00d030141103400600041d43c018006403828000341d05d0000d8826081c240b0310041141070500300009030356502c940c280d00c128154030341c1c20240e6074031000305e0400689805003200c003840e10a02044400c00041d804c02c0b2000025810540340c2c4000070305a92014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 54381550 1250 54380300 54380311
    0x7051201060e0103060b0a170712050408120106050f09130e0d0c050c030c180a090c0e070801230411040b120f010e0f0114030a02040509030a231204080f070b0702010b09 74
    0x20800c48c1118102401070042640c03000081c5018440c0c000310104450648600b902c090329811004580c14501c065103110950041c59182003031441c0c03420795000e140380d500524050f144142c84101e4a2882c140e039642110802880b0241035800d0710b0700c4000040c29000d006101a140352198001e200b400b401d00144c032008040e001041e6269908200f40c103106040f5008042e00303a11344e114804000068201e0030301002a00c1d0301410400f60789420607004115400c141d000d840c0802140f070152643c00f01d5812914014030781664003007940c3c0600c24030f202c01c80c45540c1c4691a4010006a00b64808001c07259041c0125892411000c159070382d2101c983c81c1c40340513210501c1d00c198981c0104800e4180541541d1000c1010b0b068680c81402c580000f012180100c0328403070a604001002c4d8480c6074081204003400360720584000000c03401701c88400b4940100c1004a00358114203021509008941d01500c81c545020750480395910032070700e80416101409c3c2c5002002d07600b0000c1c0c00c0300718034211156030300c0345 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 54382800 1250 54381550 54381557
    0x10b0307050109030209150d030c030e0301050412030c091a040501180b09060c070506070b0103061d120a0504030c090b0a14030d0c1103010906150603060e0a0507051201060e0103060b0a 81
    0xf034219002c000718075101a03c024442e5401078025005500c450029860081c02906c40010600680c20050030030405500b100e403280e494881000005041030b0b55241c0c000c2c60928001481060010702aa4116901d400c00000c211200030742b290250f0b4144001c0c0103580003030340d4603036510082c41140ea200c000140078400a0700c2040c4041030140c10802d010b8010740346080100c4082c103a0710000318000b5404100152a40702aa0f401807091000307502540b5030b945510715028038028170500f00e1a455403120642420402030000304411954850740955024503000360211b0491a920f80a040080c81064862030240107860000107240c641c818200150200103400307446810443e0104a504005040f8112406e200d42c803898161610f091080502035031240c00d0000e45c540314251940300c40c200310742c8640304060400c0000c2c015040d01d00300040d000094039201040940381c1100c2900c2c01d019050301030502030114400055029800501914a00c0081e00c042040b00d480c0c25062050780705030f50301100031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 54384050 1250 54382800 54382817
    0x8070204230a1113060318080310030605090303040b160e130906150f03150207080d1514010207050405062d152d040b0a09150809070b0307140a0809010b03070501 71
    0x441e4082d80000317004100b00011039081402ca0369a923661034100341c13901002c0c066281c1742402004680e1048a401684001c01541140382654800c400c100c00245042c1103180001000400c0c507008036030100c1c0905000f8203100c4101d09a60700391300102489601561f060f402c00d1051240780310f41c4486030090354a00410525250305503120461580b03482c0c80950290b0790f00700910804580c025020f0407059094040102d42c00303080c0450890703100c10b190803402c0c2c80e01032460341703000a0ba00000c110003106c1b4161004a025519100020507403032107803100761950480c1003464552031005d04c86d40780d00740808407005082c483d1000080000e0340643d41228500d0072207216022505051b1016a045a0714544c580520b0942c450945042a401c4403003004085041d1a90501607801032010703101c3d07599000e14049030b031480c00d8204980d90b41e0f2148074240000c100000858003240c402d100c21607819403105101d81c2d030341858860041151100700d50040f510b500c0c03d04000014640402d00700201c410503503607141c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 54385300 1250 54384050 54384059
    0x10f23090307080705030909150102061609030b06040f140a110405060f0310180f110705060c0304060b09070e010e040c08070e010512010806040b090d0203030408070204230a1113 78
    0x5240c0e00070001502d0910080c131003403007d640c84030582d921400c200da40c07410392030031110000380c41c0042c0a0301d040c1104004240a00c2d0141c0e2142d41c1400301d0346c200401746071a03150034001c14001e0495500c41e0b032080e410448550a1401500712560265a4641c01044124959242d9801a0040d4040c056202d98100910030403038803000c000d0754200c0907e12461480d903980e00140403001c101a0406c0040a0b111f240314806114035101d0b0401010703c0c0c403442440c01c8065036800c0c1d12600002c01c2000c4a40e004030109040c03049641c8a1820100092308502142c24000409005600d6880e00c2e5800100c2c54031902c030017410113025a02404055884041da6500d5005065400020541465041040a000c00ea41908200510f00d0003080310310090403441c101401c003149014030041820b941640b15040c25044158000b0440fa80190410701da00d490792500e00c0060301602e280c03615600900e0041b0f200b00c80500c1400e446034045c40325018200704040700c50003158030030300507503d103040d41403141c610422 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 54386550 1250 54385300 54385313
    0x13020d08030414060720030421080f0d090212011514010c0204150501110f060402010305100e18060907030302060114010306030c08010b1806060a0c020301020903010f23090307 77
    0x640041c40383c161140d2140080061520744402160840f0000e40f04140d000312200820145206080e40f14000e940703041c0c1040d044141da1280030000e0301c800d10041c0402c90902400e5406e0340c0901c3c0d606500e00e940c034080180c1c060080d10720040140c1c41030009403800004640d0502c1401452403540c46070b222030a02e0038139a0964800900d6080781480406a8840d00580d614130a5003445052140042c054608040005001411803420401f81d94480100c064590000241c000d900641c24600825241c0d5121400485c004169201990440103d000c2c08081100e400c07034820b0f000e000404444c183c0d030314607011030f41d240c0c1e5900c40074000d17810510040c440034900b90070f107040800040c103000c102540c0c1d07a65129a440010340c444070059540d9042e1180c289020310300350000d1110b05481c8116414200d002450344c1c03060488000034480c0400c0d000301151000e4043d203e801d28001d000f04200f140074200070010340800802c04200c0d86640720030410010920360518011052a0025800e2203003540d0741c0c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 54387800 1250 54386550 54386557
    0x3020915011101020a0c11120615010207090c02030a12060b0a0e0d05030720220c020f0303010807031401090804030f1b06050a020d09050f0402070804080a140613020d08 74
    0x103504002000e2414540340b9024001404186480c1c0d4031145003508905202c900c41100510581c814074040c002446140d40c0090441d81000d030b00100789109603041d10050b841c05030303240d10241e6802d04103a58483e2894012001d0020b45c9116121a08910b0301c0d45406405c5a607213008401040b00180172101415110b0204400c003418080c00c0000301c8502a100d551542e0081c6800b00c1d11540f030400e86148020314405000c40340316040d03401d0030030402064050780352001c0e102c8024001c0c540c1c0d0354941100e81e2013041007900c1e906104c000d499030303035071110740303c40d12100320f80820748090003500128054a541449203c0c01c8070380105000c1d04090460355500c0024100301c40607200e0581140045a15045015404005240b1070700c1c1c0d983d50384038840c13001c0d003000410300b070711000c0c450300e03607410441c42c0c5450b01080d11088003102c0060340e401403450034800d240919000842c0e184030f01c100503c2040114070701666118025400c561071545c441c1074900010340520802900450700d05205400521004043c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 54389050 1250 54387800 54387841
    0x6020304062304081f0903020307030f020c090103060213170c012f010207021003140402150d060801020c010b06070302030a080a1d160909020120011103010305011406010801030209 79
    0x122100c1d840b51200d6070541c2c21940000640d50801c10019800984401c00d481485102403070074440720400c0e8601175103034050500094240522002075000c524030900032042c10740801081c10400d56142c1c141403000390403220b401c07040f0002400c80498010011013680580c1c40c1030748000e14803c2001c500450f4101c072805480e8400038035846c00c40d59124100c40c1580c090b2000300000585680881c010042e12084e0796041209061504c0e07010a800d107803010820b13078095010750313910b001c0705981c4219224600c41d0070b0301001901d207410342c04240c050042d001000c1c00713141c000c000e02001c480002041014420414020007591080202c411114098544141e00070040c0b40c00003946c99038074000c00d0100250b0b8240f648990090048a40c2980038620440301411581d14108071986180c0d00103484010505500504180600145000c01e40c09400117543d0032550041ca070f0b1030356500d240c801d0103411602d07549054038146500080c59035100301c010074100c0780c0007070030702d4032036114070960703070140f6a071480c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 54390300 1250 54389050 54389087
    0xd0206041806050d03120c0503040218040311010f060305061f090c0c020a0305010209010801080111090f1906050a08070815010c051c0903020f12030306120106030c090e1005010602030406 82
    0x300090940d0b41c142d440740780301703010341c40300040788480000100440e160308000d001400002d00a000142e11181040c1e9190000c03070400c6001c40c2c0b01c6080c10303505000301ca96140708560034441401078050705030304500d040303904c50001c603003a60b00c03440340d000c0c11a002d2502c00307011004040c004000d50441034100da030300c0465034240070031010041d0300400c801ca0680d403c1500c0d079a400003141407055902c503464a00500c0d07000001c00c0b55030039055a024107442482480d034812202c003850702c10144d40703081c503014841034140481019540d81e604050041e410a251080110385d410001906040c0074038211403203000e4182c5642418288100103407915081d61006075a41d118410305081504076880e201d424a0f4203d8454100c0146588108005244460380d054000d0040140380d003a080000000e8a41180e81103400c4c1000b50840031a0500500d00e82e40040e00603c428074000540a5180e404032800000740000d4170352502402d01c1e00702c1074420030702c6100c0050b8800c000800c1280c1c07180b8100e40b840404401c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 54391550 1250 54390300 54390311
    0x70c0f0807060603060c0e0109080d0f0e21100c0206060907030e0f100b040e06040605090316060b0907180e07140315032806050709051903110d02060418 67
    0x125090203c400d140c01c11102c0c40c4e540d0b045283c5c6103401110344030401009107803007070016041c404115110309140310910f0500c20040e4008005034042c0700c0c01c0444800103000e01b1fa008041603840c2c00703901e010502c00d100078015900607500c003030348600444100d41420b8009100546038541480300044004041c0700805070f58103840c0b41600c501b4031126210241e660000c0441400290049040360001d240280c45a49850a40324201602161155109400000009007030b507030f000c0c410307095100340c00c41c090702100b406041d1410045550301460324100251109480d0b0b568011040e40c04107488455101c82d482e10701c04c2000410345a081041e4040c980f0f00e410030086400c0e8060300f0040e00182c90184412000d104150340d14102045044810300c425052000c69080b80007054840200e0420003900040c1c40c2e100142505028240e41801081c0160103112810000c001e114100c1225000c115030460401288401d145482d01c103841c8241c6e0001c00b8545407030301d0503810300d6071130b103441000b400764a4899 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 54392800 1250 54391550 54391553
    0x4080a14130303020706020f0601050409060e030301060203180d1a0907051008090610060c1103070b0a0c170a05092b0b1b0a0906050703020120040305010605030303070c0f0807 77
    0x5405000d65042100c00540d25600b5860081e0800c013450f0030040455002c4003038100c640c440040d00a04454094a0000d03900c82a070070000b010b00f207292070004407807000000003c1d080c3c0d80000141190390000850710501c0d0340c0601000b51a00c4030010142460014451041589540303600392038010485904403800705070346802107182d86801946400104005004022440406002c8036604c090600c1e55154098105078006d00004404000900000c0185500102c0e907281004a0f0000c2d2012000b440e4451049400040040300c910310100c580c8001240c1084c5a101000f0a941403d881a2036407420f14035618140076580003034201040c0c090400b13aa018140d491446000040c55014512070603040c40e20801002018001c448004184001081501100d40e44a000201518010f2401681d20007060408a0140c4848505044820b201418052102440100600031a40300c4c00007406815070300c41c1015240d00040722401d0104900402050028901c4a43c4210b020310451440c0e0400409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 54394050 1250 54392800 54392837
    0x501060e040f0c140a090e250c11010e0d020405010905070813030c030f030b03010c0306060905090c1b07150201020403020f0f010c110d0602070507030c06051204080a 73
    0xa9112401040004486900508060051007101a158902408441c0d404580200034010102d00440b0503400822002c4400f032043c0f851500a05420030041010f0800c2c0e219000c403a03400031990091402440c100c1c102543c01040c5030911a50050241e40b031040c04c450041d14860592010075500030304211006006981c0ea2084901a003080070340081d491801c000c002d07200ba0b0011342442000141184c142d40002e600800c1041050341c903103020400403a881800b50003600c180500e040e419420211079100403903255100d0700442e2025581c50000941c1c40c020303c10f04210941d64104842d004000c1040162a01902e480540045008030f07124117a0f507a08904402c2004204000142d40010b010801e500d459100314178104007c40700f01812013007010000c2c15400d144140241844d40c8ca204580a81e034890500114058105600390750b1907120b4a04a41c5030000d0303000490340c01c0101103000c6041d41c0300d0020b464418443d0540b4150135180c6071915001900151a00000c00c50700c1003c04280991 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 54395300 1250 54394050 54394061
    0xc0a080310031a0f070c0f0506040b0402041b0905040902010c020a06080906060406080604030e03011b09030b070c050d0507050718090b0108011104060c0507050d0b150d0305040506090d06 82
    0x444545054007505500e032650304440380074684800c01100d041401103124003100c0340b039003201c1c96003400740e0044064600885241040711010b0214003490040000f4006510340d201d00c5244200c4d010841c1200c114071343c5801d4200304040e000001c01e00d030414007446c1002c2c0d2007112002d005050820120340680d0005081c11000e411080000340380b10b0500c140803008101064014204860620520b0305140101c0d40e240c3c0014006820002c0ca21480c01030760f14298810281428074030f140d0240b240824401603e0f04115200480310300000500084466200da0072008015a0020180c41c00074081c1e08110752540081400759020300804800107440c9100545000c00807110300e00c08900e08142d03003402d064151050780081c01c143d0503c43c02e091014034807411502a9001c80c1080d08501309141045444d0220507044290081e4a60300d0540c140040240e40030f1040c2c9812920320044540b000900c000d8038582e081c01070201e03806020501891400b88058200640c000d004000d03148600e450700b8040e0364 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 54396550 1250 54395300 54395311
    0x110406120605100c08031003080406050a021006030c0524030103030909050a060506040512010905100b0907050903070b03070315060305150108060307050f12011b09060314010504020c0a0803 83
    0x40c22250350444400080c081d80c1d0007040304450400c590621860060f0030018482002446424000700049400300c003520340c4030280d900119600d0b00d030764640b03a0140242d80003103c201c001d440b80100b92001104603000d00307400e0740d40c00710268030020b24110a0001d00d50319001071100c2d03402e14020003592441c0100156008500076602d80581524000c0f50008503040a40101c1c02c950400c00180b045850700300c22502165015261002d488408180307c60040c94103000040c400d000304440602070050507004820306030000c40344481582c45512040c1c43c0b910031001c196405812150081010702c0f0130300e02960340048242404910741c20004c44c0502007660503000304020170380d9801405100000020f815800b640c003828940e88074280b190004e0740d42c0001d80f0800c0d01c04c030b66104c2c001d00b051f15882503110503000140d0081c01300d9030541ca1152000c44510b08508000b8400300400036030f081c400d005501e11030407404005030303480e400e11080c807000c0c1d030006400c0c0c0c407503201e01002030f00010b003c40f00840c40745c0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 54397800 1250 54396550 54396557
    0x3050714150103060507030209031c03090203060c0d0b09041509110d0506010f080d02100504020402070c090902030118030c060b120f030301051002160905070c2001120e150604110406 80
    0xa43c110300d81350b03080b02c3c2c0252080c010103105202c00c0e6000e480004081c0e5640b4850402400c03081c90051084000d0608040c1c000c3d010300510050108141004014100450f0441404e00c04c544056092020b503d1007210f003c2c1c86200b19001c030f07243d10040c95205000e124060340b01703a9044013000010440f403100c8000200c1d40d59000200403c800044030800030b020b40b070f07020301a100d104c0c80c40300029074610441c50031812681e6903501040c110342d55641120004d540c043c200b081c0c250f0317450b01080c4c000d04407000182e000c1d500f8030071000e0b6070058403285580010760648620041d4030458035214005c0c0049114181c00008103001e000c01d103081040341441310b0943d040119900d60415041c00341c454407403a00c0c08195270001c0d190319245c140c2c690070001070318104400000c465a400728104c1d583c2a0001c00a00b00740108a0ba04030316003400108010070410a8a6406d42400c8004440c0201d03840ba03c100c0304507070080c00794100c07055000b0321066006000181b01040c081c40000d0440c3c000d82c072542c03040700407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 54399050 1250 54397800 54397843
    0x30306030c03010c050405040510050a03050706020f01180803060a0e130314040f06051309020a05040311090c0a0320130608010b03150d0206070c0305030409061703040303050714 78
    0x66103001c2002400403802603009104c0d21000d040c002c0d08038020703800341601c9242c456002411804103900c491001301001040821900d030b0b00c0c00c189842d0909401340038014000d45040000c42c4605009101c4e1280604685d1500041c90b522000e42c50f41000e406103a00407903840c000580c2003646038902c0e02500340c0e54110701c3e4010891402070b00b4800f07c070150702514402800104441c1d4250003107c03045070801d04000c0d0b83c07601ea10b06408481d2540750008242ca920106400008071307070100c080d1080e00e1103142d546460154200400400d1352049600c4000c09070200320039207501e80b20780c01900650000179008428102c010300c003003480750003a05032000c21560805c41009800ea100140900504000d2aa0f80c90b40c240155645440300082a00074080c200504c158404c42d11082c0855030304540000f0307003035042ca45901e0465140d80c064401d820100f414480d010990510400030038003403c499500940c5041d00d559800d0715079170082c0302c085d03811400106103010700038000e0054401e20751801e10345110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 54400300 1250 54399050 54399061
    0x6050c030603150903070f020a03121806050915090301060902070f030206071704020108060105120a0609061e05100507020310020a02010c030e061504060810052502060a05040c0902030403020303 85
    0x2e048006000e0003c0350400c5000c0c4000d414002c011100c4c0c4540000d07050380400c80900108802e400e06500040140c00203103091404035900c0192521204258030308859407595a0314100c0b0b00380101c1202c16800102c00da20160070b0f100c414000c121038100540040741c89595425407030120780103003100fa182e201a074072a090405d40c0c1441701581c0000541040724090b24600580345001d01c005000a05000a0a003ca140c80c0c1c050020703140028074041812146143c004400e030701030100740c8a030b004d916050031408a9006c90004e0301e40004c1070b1501c81441954500401c02c82c980307090140c0c070070900c8020802c44c005a241881040c0e03d4074843c07030380580c1d039a124840080c21505c80751125401c241c80c045c440c0741c045c003010510a820071159000c91541a8a440000780145020350000480384983d48648a4840c600e4000a10076010340c2c0d010071582442094818007080c540300000010b8002100150689907154095600b01e0700801d1214200d80c0c45424010480c1d10075141900940d001008210303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 54401550 1250 54400300 54400303
    0x1603091a0c0d0318060504050106030b04060c14090d110d080a05070b0c03010312030504060e0f1b030f07170a0b010e040b060a030b01060c1104061509060908030d1806050c030603 78
    0x49a0051440e04100030b801c248041420f8a0816000070400ca07286c0e40400c1c1807050940210025580007802c2c84601d007000e203080d44c000c6c9400b41c40100800da0214800401041c1003084d1060141d000e04440e042c2440c69489180350020b01c100f440d03020388080740080110704440060f00100340d8a840e40d0395030300d9071800c0100103040d005000319650340040005000250b00010081c0d220252414046520786403444d04001809640340382a1891003400c0c0030401500000509908503020000e19100f801c4000c0d09240c2c840c6840300f45083e00d540300b54010000741000c1000886185454000d440c0e1490160342d58102c58a02a4004682d036a002800d10040c0302d81e805c40c0399006101280e000c60703d24070310b0b40d811800017014441c403020302011050760030600004034443c010300c00000f0410000c0c0c0b601c81e1413081002d06658100340020b649a580030404500034404c5006581c2c50100646c00c1822555010001d444c840341c0d80200300c2d0903a030500d0009202c60083d41e0203030750003220b1291285828410316 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 54402800 1250 54401550 54401563
    0x250c080f031e250c061a100203031e04030c060203150a081b100302040906030b01170307050705060906041701051b2b020702090a0c0801050d05031603091a0c 69
    0x3101500000014006404403a860740c80c002d00316071480150f4002d04502c15141000b00080180005050559104200000444050311014122800c088116543c04100d0390b03400304484441c5101c1c0d612509d40682405d00d1005a40b00e03200c3c0c80c03d540d404030540e40d90000da800c243c5900084005803580880030380380850070b1002410060004048a8608802903119494500707030140c01146200c10741034645101e9012180034005c1c0030b03001d0290b5503580c80e261002c40e8091190040151480e0301240f900c01e004000c940540d5004402403940d1402c182c02c02c84240c0c0896090780d8018000c00c0300007541140700d9003140c40c2d0004040000380d030b890228160001405801400c011262081003d500c901c071000c0100601c81d00010140390710700400030b2002e03009200f00d8002941c4080c1c0305041201400141c1c22848002d040c45c4d0320118035036a01c200348020040c0352030000b42140c0040c401c0400040509000e100d200b8068680365490f030f503550328941b0044200c0444122003140010740c4000760700e41007150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 54404050 1250 54402800 54402841
    0x60f0f0c0c01050304030c060b010e04060e0405010b010e0d03270305010e06090f101503050727060e150f1504050301050f0105151c02030c030f0906250c080f03 70
    0x82c4c91494603581c010481280003074001c2c843ca84c1c0f4030b404441c0340d114207104007494402900412005488003100400504111030031a03240d0b09140355202d99510070071700a0900c860240c10284100e86695080c0d41c5441c0c0c0d01019a04003400c548070b11040c11000b8840d40045009200000d241c0728008200c80c1000e80040c00707849954000700034500295800642c3e0341844156000c0062010315002c0d000d4401484c550020b04103100f004004140401003c03401903420806414101030015030240c1941600c00501c41d0f198405480c000042001c500801c4e01080100700501d0942060f0804c0c0020356400985410381c043c0840100f024000d41c00c0034801c10b5000380741800b881d89158500000525100c0c808068030441301404582c0e1055488600140000c60f41822020b54032031030800310210050f081161000c01c0d1780c0190002c500800400700c1c515001e01d0140c009449400b0394299200d4402100d01600c10800480300e40c540c02140c0a903014000441e00c407060951f8130304160302030900f5110345451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 54405300 1250 54404050 54404057
    0x501030b090f06012306070515090c060d110702090906011701021315050415080a0c050c07030201030506030709020f1306091d150418020123090609060f0f0c0c01 71
    0x40900494000950904540c25030148180100d8501c41e000d00e1003241817074240e0428004103141040203004520030360070035000b5004003216690500742c40c0d40c800410305200e402100c1000f4015104c01d292b04803c4500c000c6a090500d40005980440d03100d80c41183c030303001c15030031100050080d0103c98208444504064001758108840500c807900c40e05e185d4401d26a800f11842000d06005002d941910014150380055088a804d070142c09412010203c5d86e40420919100180031054010820307240c4919000700104001d5007594019401854042d100540c1032044180000303203554036000510541800c00085929202c1e100c8449001c0740d01078012400b8403560117004d0100840030406d03c0541e11003e90907032040d40307a850b0048844941080c041d9042424504003c5a1008481030023003844e01c01e070303100000400f02c95460300c0d0804907400d540c04050700410140c041d518048028103a0f550008003058a0448046a001c200703500032034000701003100101e44031005c60300c01c2c082d8103050361080c00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 54406550 1250 54405300 54405313
    0x818031c02160f12030c02031005040c0909031b020105040f060507061409060c0a0c0606030f170a020c010309050f01090b040c05060f0307180e13050106050402090f011211030a0501030b09 82
    0x811800c41007043d80038250b8a4001d034107103002418030449010003110740180507a40c0001460222402808048900395070030a80d8510010340d0384c0c802d110b495407807509552074000c00341d031010f00d41c2d20b1002c500e03d040e41003000078880420940070714002880202015102e19998800600e0020140c400945c0786801c03070340505003040301c45240855510360141b4800d11155407410b030000140c1d0703040002c09015081c03601e0030f00040100880708503811021801601200c12145e1120541c421911980c060400160840251313400154000e8001d802c00703500c00c03c161028281010318684c21501c818000b501c08644103400e10003408200401d0402500d0240c482520380445040d030040c4c2d0344000307800b440800c108542c80030400d080400010010f000b94004111660a20a02d1040c0c000101081038450f54600100043d06103000d208880c042c00000d81079020759200c540040d80c003080078400080d02070362039541c0c80e1204a174100085110b20030550700099a5410350402900e10100201050007550102c3c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 54407800 1250 54406550 54406559
    0xf0e01120c0e03190f0305030c04081f0510212301090314040b07020105090f130b01020c010903050709020c03040e0108031803060f0a11040503030705010209040c08010608040818031c0216 82
    0x1174040301081e07905410700c283d8903240c5074500d61a41c41241e00c41e1100b8081c0c900f000c801410160341030085e881180c542072000303844d0340f040c05840b6400ea111340c484040c0340600303000c2c044209010a030030b000e00802994240c0c1920340107415800c3c08803500c0203250303555641e1500070140c00003c40592440280c1050742080d0a004400e5403074494094040e0600101245041d900d61f1003c8983d20450400380c000205007800d0181c52000d44514000507003d4003640032024095441454500d0403240c1000040601c0c41c50300c07401c08000e43c890b10b51100c59010400c0b0210f203480e16444424000c0c28010003c6540d0301203001034221001140900034481d4010a05000c2d80c0035a5240445c0c114608000c000345030100100794001e90303c12903002c03580502011644000303105042d8040c0100340c1c410382d4180946800d21404072103c0909010f070304007007820706020030f0104241e14054810100c0a0300030014000c80c210009140c640341c110010b61000b2600b1100318140e074140300400c0c400f00c1003041d81d6080c0307082 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 54409050 1250 54407800 54407813
    0x160608010e0f0406020702030a030206041e020303030609250207030302010c0504260313060806090106030b09040f0314040e04050f03040b1b0c0a0b03040605070507030f0e01120c0e0319 81
    0x20b8542405002c0400108007804140d60480d010b13580d00604940c0d400e0341d1481d0180d15542c0844d0250b81522445016042409608503072514481e8000c1c0518a1996003008020205001411030760480140c08603e50a0756103000982c1d248462540041410900c0c1d031500900f074806a009007000c10105101c100103034090b010103000094210202c0031416050421114598040c0002d80c5582e0b01c1e0008c40040d0860300109460b0080070280c80b40303107039070303803100000d030140c1e1804070825420070a12800500030030703089182c40b20800c1c030a2802040091000c0144d100035001034015440c144046000d01040000c100011812130140001950400380b515035a50031500580d44200c0880b1030145010401800500002a284800a140e5018035850784502e04942e0001c440c101d03881480c00010510641c01a015180040e40c143c2c1e07038180c00c0340d100781d00b100d18020407941c0314184a428a0f91100a0115001d0015500300c0f075034800c0381b030300b054408242c5054500942c480c01e00240c0001c00010450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 54410300 1250 54409050 54409079
    0x30090605070501110406030e07090203040308070c061b0e090a090b190212010305030903070b04050f060a0201200d11070206030a020f0d060b070b0a050603100f0209040e16060801 78
    0x24144140c0381c00e010705220380508104016242c84510000b000300310b9940550103000d445100c0004c884040742c9a648240c2284000d48000d408508102e0008894601c81c25040c00098460034000c9240c60301c0084051440d0b2102e03d48001040c220701900ca09418080c00c9582d2005184070300380022039168585d041c5d60309025140d9813040054400d5071010425540443d488044041121141303581e5a00700940c9170b4200105140c4070703006220001621030700080680303041d540003c2a240d0888851010800e041d0b110a03241c0040d5500c4061505201c0694984404a070400109040e9103d4801c0004c0d022144040529180c006c0107214010142e100c1c030040c0c030b03480181e000c070041e030f03520407400c21150b0b40c06551a800c508908014002c40c120400d40054100c031407040b210150b0a0320390079654070070385000701c1d482a0140c0c403030b1043e185200b0845c0c1001030824018070005103820005404a4143d50f0b900e20200c065a104070310302c800c15584880d9901c0284440d10304010075504020040c0c02124 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 54411550 1250 54410300 54410309
    0x10e01050a020a050f0f0f070e010915080d0914010302070b040b04050f0f030a030c08060d1b050a03081321030f12020406030b03070503010e0703031b0605043009 71
    0x2901052032180c440c000c02030f0700c54450300901155901ca8502d40a00e91700c00301d12429110705e0040858010300480300040d24401e4401000030420545e003040c0d016401040c0b070241001c020a007903c40003440303180600072821801c009940e800b051a0818601c070f0b036130404120246041610401007080481e01c01e800140e0000c8e4081200f030a281c88030b0601d18a48100d50a514101e402103c1d403c00840340000001e002001040d28140500700c298401582c906404490300380e0001200403c0300000780c240d200703644842c80a1465540d0701c0f600c03200402d5405207280c0040b68030004c0010850005400e80c0c03e46802810080b800c2c0b0300302d0b0b90444c65082c0c400d084480040a00006001141c010380c00b42d9240311038000c800e0b80454407150342d40c1d4028050300c802120342c0d000303015142011426080c10f02a1003a07081c201001018070500e55607003240c4903841001c0c00c10414a176440c3d05e60009000303000c0e85020718050300b140d518242c240204022400200d030800c0c240e0344d0308403051150380743d00700d1040d90845 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 54412800 1250 54411550 54411557
    0x2060601141e030708071101060b040905041401020a0504050112091106130506070303091a070f0e06040f030b0402090c0304020a05040e0a12030501060e031b0906011205270a02010e01 80
    0x420b201801c48200004103074944141d0b00010003081845540b01c0345041c858011a07a80713034090010a01024202c030700310302405a91400420083c094800103800858105100f8181041070311824030240b0700b2a0850013188000400003c3c0410141d03a10101081c012020380b4000c1020100c29541d01881c0c180c0050007034080c290100d500110070803442036060081c1009058659150014a801001001a40380c02c075441c10b9007076415030305081d40e012140d104100d03644074a859004880c400307846500e0101c82c040d9110008100100e46031982e000c07820300441c4201c0d9a09803030308040c4100218450010040c1480711000d00402001d66154ac40c00f004903002900c00090101349124003074107000180201500c0134103020015a04580c0c55845141204c40d944d40c0d40b1088030303a2108050301e501208171809440d484001814490b4a07200d1440c62b040a01410b0804c3d1481e003038203001040c2c0340b0890754504242c9a40d041c1e11104401051002c14114105000c0c0c11141c8880c0d001a1080c0c0701c01c0c00743c41c1003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 54414050 1250 54412800 54412807
    0x20c031e060105010f09033e301c0305090a030e0f0a1211090601051204021c0b090606010e0103110a032c0307050f0109021e0409140615010206060114 66
    0x9a8001c540074001b4623088000944840d0b40111480c42441c81c01c002c0c111511004441449444400611100313004801810303a5951550032039280c0340c072030148030440b00c0d00e25460006080c1c194100401100c0c5040118940c036200340c1c00030041d0031a04001d11149861300107090700800aa84804004450b1504564a1101d4000d50000c52138600b082d402000310f05850191a1302801844440c0c0f404074002120101c41c50780e40c1c00300449141c0160442082d82008020201d00145403028020999402c1e003d4000c418101c03540310300d00c40403003c0da6000c0d9150409000d2160f01e5038880356401a4000130700b0180112184800030307120501c195010390307003010307612440113500e0644107011032403401d0000c001003814501c900b0b009440341d2090500b1100c0e031080a0507821074100600071910500c1d001004841c15403100100c8a0010001003049030b4050303540c0040c00c0c0020b89444043c45d1131955800105010714009020441c19500a0600c50540d0301580811a20303a030700040080000d490864030710385 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 54415300 1250 54414050 54414077
    0x60911070318170f06071b020d0203101b0e030303010303050f0d0603020303040f09050a0e060105091e0106030603020f010216170a02120d1202070b070302091f020c031e06010501 78
    0x41c0b00000e41141c40b4500c0c003545100200000042e59491461400b4140d403010385481e481680c20961603031040c4c04040d501e002420240c40d0120050440c0c0340050305444400c410150b9502c100e82e200581038030000c82c1010591421907020103107250a5400394021803840d41144c5020b041da000700b4180300d022080006807079126440d240c10000045a001d81100e8645844440307a52071206107006403500a440e00000501d0f40c443e9014194002c0c640f0000750012341d00b002d0510401542c001c0012810140d154801e80d00003000c07074012402010a07076000940c0500b503104000c22008050307149e40c1158042841d4907813500b0014480b0044501c07103910088030f505500569401e11802a4000c0d5210f640c201403200103c8020500c0031518660750f480c87d40b05e100d2100c0e204201d0103424005030641c01c00100081d06180a0360040c50b030314400403c250414000010060314543d4001b03441030050300080415842424204403888400d6507080140c0f001940800389295900030500c038540c10802e01e8400c494 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 54416550 1250 54415300 54415337
    0x2070201030b030708060117060c0a0c020303120c030f01150914010e041d0105060303070f03050315040e0a0201030510080a080f07050601090c0e0d0b0609180106180609110703 77
    0xc1070002500f81d80341145d0b80d2140ca41c4500003485154100310580900d50940c01012403500d00c00c003040c60b010750400a100030125010f15102500b02d0b0580310412006507010182c003130b1036100310700c1c5c6120142d6a01d001d002c100c00e0b0702d4042e4020f4007288004440004440c3d00705200e0416a034070480c014070400c5400b0012640176078400380340c0d50000c2c030344183c5298030700f1054080107034a88604004c0c441130301c446040c15500c0c4510f05c400303000750251107209030010303120720000d50f080500d0300f00400307684c440a00020120381c0860140041c070f03808030102e1400c43d41c240c010b4030340c015000c248805034940380440c4075440301d03404040140b16010002d010140c166582044c0d0f84941c0c0c0000890b540c0d50b8413000c20030000c110f01c0c82900003007202040c0c40103440c41c105c1c05151035150f100c40e5007405a00d60358203104480001505400208060201003002010241f04000090048070b80d40061000000514005c541c3e01da00910300d00c60034440c0c094050b00d4800100e818069040c40d2034540003080719241d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 54417800 1250 54416550 54416561
    0x130b01030609090501050f0601020a15020f090a060519090b070222050f0f090102070804060513080102030a0b091302090609070e04090b07031b0f0f0201090c030819020703080306040207020103 84
    0x807889241c2031100c0f06210781580490700c01d44181510220340d07150b1800584c5d44043e010380052800c445c12240c48140c88058014143c0b441400103034074201980540051041d021a400c8080014000310b94031500049640138105404460b0a0195440d4244685c02c80c00e40301d80d40300030f401001d001c00001c40e0b039500c0741810b280000382d07034804200030300303007601c0011110340d094074850b0f4103151400100758400b40c1842101c201d180e0180032a40f40c285080380545494100070303038040c0e041101100010b0603407020b000451140c2100e900c000780c00111102004100c4402400c0700042d051084642d0005890f004100c0c0e4100c8000c5030001c010355100c05045421844001c1c0c4680c026040288403402c0103100002c980c0500081c1e03e09200c158241800d0139290350000d0741180001e54405982c4040a006244495035031055100101c2c043c1d04a071104550018940e100f01d0740808005400d000105440701c9400c1d010416101400000d8a191038200ca1400094240c5108aa00040306000c5a000c1c1d84030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 54419050 1250 54417800 54417809
    0x904020a0605090105040f0e0612030f090d1b08010b0a2909060c0106030f060b060307080106050a1202041517010806070518030d111c09030f06060b03090106090f0b130b010306 77
    0xf00c02c02d03881d81100d2100c00400e271800d9019001000c0d0000320700b0000700c25143c210151080b4642018001c00800c00c00242d0703130380140c4002044004404400c0600300e91b01018102d02e00005c00c1c0b81100c0740612000d2000d59100c080042c00001c030b0400c84804450045d281c0e40c5940b28820389030544600081d506228100c402442c941c078101d00081000b1156070000e541c02d00460082240031078840a1282e00d210840e940d80008103488014442240901c0240100003001c1c0750406002e800c0c0302c6c42078103e0340207412400d1241e0503403848400c040e60003841c20f4900a0051512001549841062561114040d00c00014071401040d14000e10b80c0f10302214000c084010700f103403e0308804641c09801341013034240e802280d02600034120a000006040804400c841c1d690303c294881c61354440c0c071102c1014081c1101c0c015252100019590550030145001c0c1681c440009040c51408103d2421164071303040007002135013801d80d0802540d41c0c08003110700500b0300d42008280008610012401043c860b0407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 54420300 1250 54419050 54419069
    0x61e04051807090b0408030306010f02010f09060902190303120b0d02061911010203060102032505010c050c010606020712030507060906051008012a0f020c03031c05060904020a060509010504 83
    0xd101c1c0300c0100c1a207605001c1c061036200c000b11262104160f03507080c852401000b10750303401040810301e00c0d4414168110340c03803528030002859603c5005800161a2050829544181c40e10240410f610341200161030a140d26003100301c5c2c0c280741d036130080c0c69020317548001c6a07103079610074101080d91540541c084015030b0081010340d45050404480d44c4042d14800140005840101c03803800c450703414400c0324040c0405800a41c10500b0242d442050464480308030301000001e11450030005000740230380d010000868507a90780700e65204489500b15140b07a8011411036000410812500e050303500300d1240f051300352502ea0754908403800c20078090300d07204000402440c601010050004c3c0c80001420903154482c00030700c681204507490801d11021521014181c81402c01400001800358207013214031020b5005958170f0070701440c002400d44d00300c80d81d03c4840c205c0c0007a5503c0d540c1030601c50140d1011044a0100060509401161808040340100d5088c48070006200d8010383c001d5080c3c4009010070700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 54421550 1250 54420300 54420319
    0x207050d1e0305120a2a051e030106020607030c0807080a020c1605040f060807050405060d050a0b06010807170408030703140a1406221d060a090309080705061e0405 72
    0xe00144542e00016504032150300d45401716100c00d200c0d00a504200c40218002159001c1603400d59002800c84c038426428440c0810825444403000b686018030b90948000380b5442c0d601d0410007904180d070040030141014503101482d16216041310169030000c40c0b610f006661541c2c0d0b4100070000344910004d082c1c0d54845d2800c00641c0c07002a203001c01c2a10f000b0b481c10b0240605031076100302074443d03500501c2d109401802c000d11580c00d141d0b10039a40580020420414200c07280c0b200f60030075049000507160304d90b0f40401c010407543c210003680d400841d245841003000710032480f2101c041c000038100500c1c100300000803488043c0700b034101c20f07284580f101c00c46c41e843c20000f074400c0c018940661a014500c20200c0062114134084004084448100c0e400f9035031640901c176031200418004002c1d549804100c65008104242000359900c16807898a000803281000e040c09028541e00d5489031601d40d000b00f200307000c640c5400301a00c0b0020100080d01ca041111803484004d43d003e0350700130b250802c5a06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 54422800 1250 54421550 54421553
    0xe01120f050f06370b1503100603050c0a05071b15020601050405010e070903080a17010e15040b010509010309020d050d02150a0c05070f1b090c11010c0207050d1e 71
    0x421260b0003104100380c40c4001e802d000030a4800d8040102e00c600000c44d04070704110343c020b600e80044000090007050080d403222013281001d015003080d101d44c0c5034651590018041c0340c1c0c05101d00d68001c9014800030b4100241060000e001d031040d03100003040034180403001443c0510803c1c5110151030144070303030800304203e400f00a5079048240300c3c080c071942c10100000795201c03172010542d0007540d440d0b4820400e20300715104c00d0f200e1303808000c080c030420124402400c40a09100c010038043e141c02c0080c1d41160909040722141101d2000580b40709502d8070500084580e0058111044600c1c28240030542009a000145596803100d10140c03860140f100c03440700302a404103444002c25024000c0d03205540710a03e04104540c02d0f40c160303a001c110b00f000203d0104245942d5140a28420011424221031443c50b00c3c08110310396001e40c0409840c1c0c401800d62941040100241c54400b0008008000044100940d146082d1098600549144141d48140b21628803040e0030b400383c00e1080001035905 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 54424050 1250 54422800 54422803
    0x6020c010f0f0203040314300103060e120307110705060d021201080a050604140309040e031306030203100e06030f0303090604020907051903020a05040f0b0405010207050a0e01120f050f 81
    0x20421500300da0b4034100440084030000e109503030040b501965451111000e42120700c61941c4020500d51202c02d440c020701c50750000c99203443c402218070300c440c40309951540c43c10100b590400814044144c024081281c008040002926030002151602d1107010341c00c078501908002443d00304503000040080e407000034081c590010406170030010f221088603a80c130042d02d030b2101815070300240356030804008074011070401641c01e0741d1a24120b0541b49001d4000c1c000401711001041c80d054142c002140440c00040724444900040c046070505520b54070f0000341350a00f100351405411400030107a000f0400a071002c00c400e0600d0600401281d1792810044046a55a04115002c920440d036090024401920850a45100c0c134070401c803103070180c8160a001d8000e500441d07515410024103000020b004000c0901c1f21005101424480e0b6449007040002418007820b5000705d4010700145e4420000c02111aa0480c1103508203844000c0f80c22451070110300201c1c0d0944064442c0c4500300140109120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 54425300 1250 54424050 54424061
    0x1f020f07060e01061d010b07080904060e10030201110f2808030403030204140109030203031c1b030f050a0905030a030b010c02091e090d0f08060a0b0f0a090603110301120c0306020c01 80
    0xa150400c40003417084010307080b6407600d00340103180e14a0000d200c00b07400503c4000152507140701c014008909140c48004c0078000c4070040768460135811f9070400800c25960483c2101108a80d00805010b140303103400d901a54074000784500d010086590345141c10320200480c10072201590120b40f55659007418200200690000c0c01100010020a2101081c1e03600031180f80c401c50358054003450070040c8207140c0286110114041c407a4003520750002c2c0b109400040402124a040350710300103800441200000110b03003005000c415a145480c0a200c0824000415038070f09000d40e140c00b04070794842200498152041070402508040c0207410b100058012200c600d101404004072004a5559860b9440d503408017881d2030000f080c4001c08071644103205146c0d10754403540c003a00301c90301e42d903440f50030350620707404203000b07400e02000403030340113603643c0c2c464200401880c407417609008104580214510500c01846641000c0843c041c0480c20042c030a8646401190031507400c544401011080a01038071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 54426550 1250 54425300 54425309
    0x403050d1d0a0e01030605040c08030a020a0b090a0b01030807030504050a06030b01030c02011104090209011e03020306090c040f2d0e010503070f0f090b0102030c010905010911031f020f07060e0106 86
    0x40280c0c803200400e08003a40b00d802281d403d555400c016074030315140d1000814020b80155050724407002c011503980c0041006142c0c4550f554024545503103503040140c070800000d0700071401130308413601d107102040301c1604080c15a500300c5035140d6918801d01d0280c0ea01d20540d401503400a482c282c00003604d40d05517128810008080e00d061014460700d1100324201c40360241c800c03070030350014031062202e2030302a030180001c0641814681c1c0b241c0207580e030f03820005803a0502c2d50b001036000005c225190400100080d0400c0807194114105030404d881d14118606a000f011442084440d1012503803c07a4030030807451441c4c90700c010094585540070428146000d0140c24002e20a2460000d400780f41401440c00303e41700500980200c0e414140104007070922825060304610080c88680000d076400c1c442e040c8a5032007400002107003a0540742c03250711040788054091198000c01c101034031120b05842458200030b070902c001a0368070192081c500035070088d010003420030791130904005070059056000c6c2c800d0784c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 54427800 1250 54426550 54426587
    0x712050a0b09010e060a0c03060503070b031005060304034407030c09050d0212011e0903030b06070302190203160602070806090a081210180c0305070e100c06020403050d 74
    0x25070310355a40500b65030340d5501100c91a40b02c000040c40d5104c01f5880703a20310401e079180118240c2e64440000303281560580202c018813200000744000d000a018aa4000f820f043d5609800c524103528054040c1d402a82c0480340c2c2e10703541201c448802490403074111056481070740303030315103840c1ca5540c441ea4800884140001c00e207095250892035006141b104c0840304014020031104400b036091103003442026040c20403070740d242d407803042800501d06c05020046198201c0095440e8031400c0003400d49080e032441c0c82c041c9008005a0700440d601280c00b03444002c01b56160342000000348003003031070404072001641244843c07981c0483c0440d40412680b08480c550803c40300c4c5a02c40100490310380701d4078400140078007010452401c14080346202c40c1e0f40070f5250800d0f8100c10355110604a071241e621003901544560700c01001c603042d0781500ca402d030072215a207405401420000045000d24000300f040d88103114402a09070104182d0350100d8010355403240c00d68400e4042c0942c09410303080660785480340d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 54429050 1250 54427800 54427823
    0x3050f0114010f05150c01060305100c0305060d02090405070509070302070209060a290d0c090509100b0a0c1119080d030903020616030207060504030509150903030702010f020712050a 80
    0x1415060040381c0c141d41003210343c5600c07039190400b00210400c0703180352880614002d010300d11b205002031007220000d50044000d4080680900d90090865010311040814540b40800b131041d0303512000920205c00d1f41c16a03003a40703146c60f00d0404030710b800340a40c000340d807080c590300401c4051a81600505487c5200341d50303076070b195211a000c002900d040c9001d8a0001c035414421954856948115052041c00c21207000340780c5004000d03054291140c50241030007046249078100f20380e0508135005540304034150144080b66040c80c24051851152554041c00c225a02803240d081c4590400301000e4001300a001e80260146101010702d10740103403240740c50340d0081140e410500d038000d000e0b9414a41d0306a001e040c03a03079504000458600036412441c0109542440300500080040c0b2840e40150301a40356030b5218443c0d5400c11103980b100d06a02d840001042c0304a41241c0c4001083d0780040340c0c24240f214150300c030300008070b00d001c0441d800602e001e040380100cac105102c1c010a841c0a014003840c1034020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 54430300 1250 54429050 54429071
    0x110f0904020d0204200703020d0f0e0d060218060309060a060e040302060604050714070c080c0114160201030212010e07020d0806010c021002010e0f072301090b0711040603050f01 78
    0x458410840c0e02940260100d031941005103015070000c1d103204501644403640c1a400f210403071084d0400003003100503034045005e0300d0815410200003d017104251610740e412568a2000c92110000b000c8000d15071a000314161a014583c0700c1c500c036211a000d05460382701d10b052a0f4260742c1b400e0660f1a65a1030346804030101d050060b010120344900d802d078006101989a40080c0300c002e142c000c0c050820000301c200c14001c00300b4880010700c0c0c0740e40a00700c1144c0150402c2c1c0c2c542c1c10101d040c2c07012030601c60005d003000d49412101c01620b41100080300054822101400141c02a01c11425807190200c8510008140320f110300f4640c45c06180207500700c5d00c6c1c0e1515008195040103060b1060381c04140c21031004001841c4c0540d0f40291080d0382d100118004002452a6180c2503850350701500c0d40c2c0000c80b09001d6400c0c0c0520900a415940c282400321009500c00a860702403d8012003010400001c0c0103c284040325845400c0d14001401c1000081d03524181a500d5031484c3c02d000541d9401c10b800302c0d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 54431550 1250 54430300 54430309
    0x501020d0f020d180c03080c010b13090201020c01020607020a060f0e0a0803041502040e06130e030307020a02030606060a08060d03050c07151101050405060703180204181713170c030a110f 82
    0x98820783c412a048031701e50458607506120303001810004447e41d229100740d00c2c1e54036100c02d08a0b104010381c1000ca11000d0360700c0060b0800c0e0041c07a01c1811580807100300150300b030b800038100840da6000300c0f0001e940801e042401028041c1c0c41040e064070b00c59074074948100142003008510882c042c3e030744070180c608030b0746c004016440365119100d170019014020604c0d603d0003090060b1200c003110b60020f211400d00400d40d0558004490007400350304155144015070600f0f20440e40d1107681104d00038138160320040090300720003001d000d0500400785010004c00305800307441151140f8010804541c8240e0b6607128981d0040d11001080700024601100d00600321414002d550250f5070000c0505041ea5410304100e004001045010305107030218502c03a80941c40f140701e0144201d04007845111280014104204401e4440282c40d40718a400c120660030510309041d03040a550101694006008010b00c400b03142c043c84100c0c0540c54060800d5038010401c60036030b101c440203000d95902107202e54610800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 54432800 1250 54431550 54431591
    0x1e09010b060703110109240f05040b01030b10090e0303070e01170601050306270106080603070303020705100504031b0819020d020603090111040303030b040b040605010e09040501020d0f020d 83
    0x1903800141c103001d4800007078001c81c4044844442c0380c0000132174030b2240e03e6540c07503140a04240002038140401143c810f2440b030180200c3c40c1105070003446141060b0303079038813003407001440050320800360000440c0300e00042c904000c0040201090900070114203081e005e4490f40143c0d00385011400611015410354080c0441c403810f8403c2d00203d4405513114401942c107580300034091544003c5510b400c5c016031101095601c04d000715008000782641c1450741c0a0b000a8010780301c00d11076800100304200103039000810005490040d03c40c030710500348921041e01c003030180742c00007021001d032040f21201212100c080c0d50f0031282110100c03000001c56043d1400c80502912000c1d40203c610f8100001608010b00150b0b00268190000038074003e44c00c41c840c1c000e802981040300043d4980c24220000e103814041d095141c1021501003040e54501000078000c940400c400c00d00039400680090305001007981903c2c0ca0426241081c4098822041d14100940c00b000342070032000c0c500b0041040c0c018610441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 54434050 1250 54432800 54432821
    0x91f02070509070815010905030f0c0405010603020403050a291f050a06021009050a0b040b070908060c070605060a0510050703090f06020a020d0507050d060e010b01020a03080610030b06031e0901 85
    0x2885213603142c8402e00e412120310540142e050117400980000d00c2d84081000b1041400c445000d040c07010411410401516410f034000810503005010500104202040e07a556003036105e29060925060803410000a04a011036205001c62007000c0000c00c1040c480c50842d01070703035503010242c25616002003114807400da00503000180e0150074140d004034180e80c04144a203010700b007210244500790703a94099607002164100c44691425041c40011030300001c48030040c01122003d0401454007105800c510300400324080d203615201c0d030114059842c1c02d200540680005000d0300f00c0f1000042000d082a84002d404400140700404000342610440c05d0381d0040e1149a07002d0300d44006039400b000040655013409944074068904001600c1d941da8161a4001c0d02c610004604008c640d0103403030864540b0b4030b081d07040d03421099040001960200c0810b50103d4203e80c8042c081e00c0382c61045008101e40d18074260041c0b0004103005560440b0f14545880c420804014846503a50f043c01c9400c0c2c4062301e20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 54435300 1250 54434050 54434057
    0x27090a062d17070b22060f05070206090d060c08060f0604050d1214130501030b010807080a021c0203011701060812030406091104020315010305010801020f0d020708091f0207050907 79
    0x1c05121149010180140d40e5044a0848041035210075200119910070319080c0c11501e40b500c61000e042a80c80c01c0440207240f181015095a205000003501610803403800030300c42d140001d0805010381e00d60030091016a040700c820016401c1b404405818110140c40f15840f4401c42402e018031490408115401e4520240000c400c5c8099650380140842d81d007180c1c00c06200b2888804129121514007420b0030044000c5940201d52510f00090211960080c01c2c40c10805140100149140c0040c0f00b03e070403880d000c10040c6c0c0c03204905222610800c2c00040500c8031070001000140708a052140d551560542800030408107660703840603507a902842d8ae40c00034020040c030006010840c540e20444016000782544030201e44003c0c00142240e0046541400a030080701c1c0381429075030705205881c05845c80500840c60041004500071031806103018901c030a940001c3c0c4c55007041281c2c816245003000260100f11482c9001d00c0300a4078161140c1820014401c0000004e00380c0b610306d251034080c00300d1340c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 54436550 1250 54435300 54435389
    0x30a02060a020a080307080609060a1d06041503060f050a05071d0604030f03021f0209030a0215070210080406050703061203120912020703030806030a0827090a06 71
    0x14240481608008030400960198410070b0380131840301401507120744496601c25003140707455810050311034030160035103018042031034062200701d170640c9600f00202507500984006035950310018001e0560360b0a41c01050380e420300d0000400c44550401c07114041d48040a000c50740d107881201084a0040f12039200140810041008502d50151066244203000d01401d240036140c0e01c0b172114441020304100c0050317003c00030f800d034600c2e001559080d105000b91400d52411002000080d6600d030050710181c03207410700c62600403201182808585185902601c04101c1829500700034080100846098958509040004190034071038810f450603a440c0d4411449149407a4a08a030690304011440040903910a507482c04200388244085942d6084e81c014001d640c20740c0b400070400c0402401d814003903801b80355a6400036080c4825242c1000100034282880c2c40010b1080c54803088112540f500800707200288004501150031150680d100c1031254100351000203201c400122241e075100b07110400a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 54437800 1250 54436550 54436553
    0x2120109150302100309022e020c031b0406170c18010302090408030402040b130c0e01030509100e1911010306120b1603020904050c030406050105010c03020709021b0f010c1409030a 79
    0x602c80a44c40c004207140000316400c141d03010940c800714003100902d00010084180085801e210310b103403200381280c405002c500b50300902080d038642c8440710100c181e20003640c0c0c002c00f0b07845943c44800100349100c4001c46030b510b541081502c50000d500268040c0c9d034400e074044844e91203409068126640504880341d150765a0305c41b01c107660405002203074460f45581c044813081c1d079208180c503921521420002402c2d0310222000d803d0a4401440905060914081104c2c0d100b01007144045590080008184050708111b4035040055079125071000c0d0030186030304d4007440071203070100d04048030a8030300304141d644800b18954039480950703000b80011990000107042181d45904009005200d007005400c241072440090b040d103100303e0341c40031000008020030003803021034000c942c0140004e080c40c061020140c2c0f0300039110081800307900e00007500000c1003240c0b8100f640a11410868500c1a14040e03240728141c01c1c080d03c079002c500e1000076500c03c0103010070b0820908903444000700400429912606 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 54439050 1250 54437800 54437809
    0x1030302151605070204020708030f060f040902090103020d050c0312040510030608060402100207050d140c10020604060203070c02120105040501060b0301050102070909080f0f0d0e0a111c06060902120109150302 92
    0x42001700d80041d004d00070a000901c1c0c19018500520040d4000f040d0341c030301300b4148807000c50320f9841544960b060010b0b410242e12980c0245040d242c055034000310000d07035401d105103070a0552022036018800c40c41405040c1c0b0b202c8000d04141c5070304407646030071743e50447c1e01201a28010f0180c0030107a08110b003c070300103181c818800399002c0700b0360065900866680c800101c020b110700c9401e881c841003913403070701e05c51400c00d005001c1c0004086420361503001d91900000d507140703c002d100400c190344c0003001c212180d006548013100154010104002c0d00134000226020304001e5034202d4a640c00c000d03000c2100400001030301d050390030684c01404a5460240baa10142490340c0c0151a40b00781040316900341844c0c0310041c0207801e40c82c0600ca41d600c0303041050004035581c030f03196514190464a1103000040122100840d44007003104c400100c05010b4030410050000350310700030a52464043c0000c1c01120640142100c0f500b0b070b0012103460307030383c5180e154241e886008105124403420710091005160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 54440300 1250 54439050 54439057
    0x10915050a02011b02070812070b060d0501020904060303110f0109240204211406010303051b1005040309080c010905060403030318060c0302090f010516060e150f01030302151605 78
    0x400b44004580150015280c0001e0406102040c0050304203840c1405800406c02140401200c2050454503209031629415208100030b03240c140300300100070000d403e0000035011344450560060003086016564039000d012201e05142c10300d0740740100104850810340610032000080d4010082501c2da01d1038204a040b185200c2c2d0344100c41c194284000300d0800d14109800c0b5044108003201c00f00a0b10322b041007080c403000c0f1100300985900160051000a0b8072105580407500400302c1d1606600400c6000d41c140300540f04102c600c903180100b00400d245c0e2041c0c0f04c004543c81c1d001034840a060f031200444180040f4040c0e1070300400c041104100203442030740980051200381e01c402d0175085055031028186d4001201401c002030f0045481001450900b1900c1c490b0031090030680d285c0700d1151424031041300c1d44c0b08050096517460700b00c4143c0c401c083c02002d10420f80124900f0700d51600840b1000148000e010941c0144520110600c0440414a03c140140a580709248a10001810803111a071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 54441550 1250 54440300 54440317
    0x501180212012c0a06090f020a0b0301060c0201050708041503050f07090308120a06050d0302030c1e0d030903140c1b0102030a08130f020d0614070315030f02040b030303012301091505 80
    0x10a44c034840c000702d4002e02c544030641c1d1250032068068003490042103117504498014040030003003040100106500540c0d40c1d42029428200142c0b90f54060808500c3c0340901e0b0b03c0300c0200d01c0340c21920751009502d948124400c20b080d0480609507122110100c03031400b4140402080c00000308282c13990b180240f61202c8c0e102d508a0300100d1100d44420200d00c156400010450150f4404100680c07540d0040c070482c8013101800800e4020340200d40d116681d00c91080390644103040d616114841494402c88c07910326014440038003103981e0b040841d0b41c0ea07503d0002442a050021000881c01d403158400301c112a4801e4080d0f65005d510b8444c4006120403540c910412501411031111a00068565810039490640580000203d81a1400f007a040e03a0100501134800c061034040c01c40f0952007191000c60550390480c6005208800d14400700300140f04511500782c2c140300c08000041c01c4404811102148031442505200000c034000c01950301d600b00d4040e4040d18078083d8a44035015205001508140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 54442800 1250 54441550 54441553
    0x10f02090123130303051b0a0309030605100503071202030709020301030f1b150305010e1005011d12030f09010207090207020310020a26011703030f06090705070501180212012c 77
    0x30364241d126071503c080e50360089001c0740010070107200840c07074146c4481d41c02c52130320080c01001d0a596030080840340c03030f800004c04196a40020031301440b030400405002d04005012a03c1864542c0040001c4452101c400c0384280315020002c66020b125000f40d9048903400311a0448004145d6200144d0a940d8850394003140c0341928001034159481c0b50100b41000141c60000f01d950610880c00140c540c0281040c0311205c1020040020b642c2c0540402481c045014a00384810007450004140060343c401c0e0014038400441c0e601d415008407402001e00340426002ca944055403200004103a004901e0041d5040d00040703105d9602560940040241940614001002c4102c04403800310240000b012804060a20401440703110200d02d140ca00708030305540294254a049035035040c0e242001820740703020703106030008128580d002c0c000b41c4950035445402400680e011082d40010040c60007001da100703403010340d0006260441803081d04c14159410886040032200c503920b12845040003e84400315 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 54444050 1250 54442800 54442807
    0x7080a050d1e0c0e010e060c010605060301090f0b030f0a02061c02030a0903081b0327030c030a180e070305060a120c140402090901060c0c030803010e09010f02090123 73
    0x1c0100502c60811404841da00b080340d00e640c2c1028982c00c031110075001400740885403140721103a1381c022000c07280008040721860b960310080344c0e40d603007d000030754492600b0544c04800810000341c81e030047d00361801c3c80c0c00700300030008401d800c150361114072035084039240d08a001950b025062a40090036052620462800000c20002c40082207034801c55032010500c0d030314403940e01019440104c040c2c104aa20094403440701035000980103c0c400035001d5881c100c40b6405000c0c0c0003100d101c40c40d1130030494030140c0f034940c907804000c16101d03030060440c580055032944003407000046124060080c0c80d80302c0300d2074039142c0d200da10039030040c0b0025000070780c4922100c00000d20034801c1082449034500c100c15002030645440d8400b04804801703507449214900520000d01e0035200d40c0341c40d604648042ca0440d0319551141442039a1012580010b03010000000011034608078900b4090b02482d02c002c000c1000c260b034602c9400c202d00031041d6084c0050f541c18290401c004107804600c014400f1094194034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 54445300 1250 54444050 54444067
    0x30c0a0e060403030e0307060305011a0706090204090503220e180109120f0905041812030e0a0f140f031602040605100c141207080a0c0b01030309181107080a05 70
    0x100764119501c103c001880740e00c111500c505007882144001e0200d4141401254101107071070140c0414a1491182c03e01c0c08503896040c050b458002590690b0058820416140903041803a16640300c0d480011541c1c4204075803a00450454440074102c0745080701000c0c00c0c0d181d80b072035400d14201400540219640316090700f8041003c80c24032801d00e00e15600c80da02d204e4424038002d00080d026074000d52041c0d24107000d00303054002c000c105000c0c8541c40303124807050700d4961000341c0003405140c444406a02c140900740d002c0203502d00420707810300d0007108101c03a007100d0705500c2982d1b002014017002c0c203a001801019501c200401e0309009880c0300038408140f241d200c01c045080c002543d020b03400003846e9001554180866903180c0d22010700c054001d40000002003441c00c600d88600b09000b015040c0018000d11035921800c425502e0541c800154652541d40342402044440240599843d40407840040380303494100e032040b0340140c01c20005e00c3d402c0c034076141c9035202c075500b20050090a002c030401c10500e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 54446550 1250 54445300 54445309
    0x304050c1504170307021014070803100e1f05010e0307051302181002190c030206072a03020a0308130f150e0105040803030a050a0b03010c050c011a0105030c0a0e 71
    0x54204054801ca62503900d00f40d0314110b441c51a07100b50241e908200320840161310b07180d61819640090742840720202d5607001c4840c4181c4988407010f002010040305020108124009000848071408142e1025071600000040500305807a241d28010a17100400c100550250754038184082c402415110b01555410100302c034070f8003032242060540e5000170a489401c100211000c0d40302c50a0740d12031240c032501d500195444640c80e9244180b1098024100100302d00180e03808085c6a0141c4026120501071520108503654034480c003d100e4111080030102802681480e4201d030b030000c04652000d461038694114542c4907001c040da018504042c042003600d00c4005210007008036600344442a0304043c0d000f03000000c100711090400008000070081040000180e03600000205000100c1c0c0d00e50320030460040030301c11505900340d401d00300d41080d516003000140843d500800001c1c0300b00102e080514109003440d00003540404c0d014008115020541b40107013820700f5544c2090161820000000f4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 54447800 1250 54446550 54446569
    0x7030e0307061d060c0a030f02040306020403080c0d050c030702120c09090d02070e011401030b01020a051002040e060406030308070c050a050a0c05031e0601051002030403060603031e020d140304050c 87
    0xa6491036101d950030044481169594040f0f070050078050001401d00e0a500d90452107030903d21810551660000e0300d0207032143d4111401140d00102c21541d80383e0302d1078880c5031a00000010800c1c2e0103150902c1d10079074010021507201d20040704c05180340111b01c1c0d0070020b9580001c41200c0203489800b40d250740b983c5030041610b00452041000b00080200b441000b4a001c00b260010721400719000c004000d882810011200c20460900300800d41c0411480101d1802e0340c420005466846114080b04228010f0380c0100103070740300440c1504c515034446041c003090b41c0c0303a840000c000441d260002052280b0900240d400769110350103503251034100d501e405250114211013a03c2544500070100400e28081203040b80b10f010744101080411841040c00b600e0b440144200ba0243c6600014011001d20900844000d035034059001c00003e6124140241811607410340e0780c12060111040e034480340c1c0001503290100c0d110b0703074400d6250881419640c0180e040900222254456501090707400e0342d500300035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 54449050 1250 54447800 54447803
    0x6090503040315090b01170f070e01050114070f0602070f0b10050906011706010e0402120112060606111b0d14010902010e01170609040302030405120120090d0b07030e0307 75
    0x255116425800e090f0302d640f441034a400002c910b0700c4030341000100c500f10f00a04603038809030300401890000903520700306081050104414020309802040c41403c3c40c44060683d80d00382c0c4d070b010029500342d441060500c9900c001a000711031001d10180051706640083c036030f1502c111481c0c25080340640c0c03012841441136a10fa60180303405941400941410b49200e030388039109180010501d0740141031401c1904007e0700031410480c0c40d5141d21030b00d48441d0103c41000084810800c0d10750b81d02d40c10301142c2c1d082c11004072500340c105000010418802d450354411904048003408501c05e24581c0f0504032044100c841e50001001c0840c14003040b046449980500400720010402c04124800100604100c1c00e400c4e0600803594444c071860361862007041c0c1d2042d415514440140c0711810140e195010700c0c1d1060307074003050b0240201d540e15410f420001440c400811ba060741c49a000d8400b922074005c40c011243c000b038000c1e03c84008117020607030b241c1d0070a10b103080003c0d1a0f40316104403411035006400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 54450300 1250 54449050 54449053
    0x5060109050d030807021924020f1803060106050c0615041118120610060e130905070321050f09040603020307060509120607170405010e06010303081501020f071809060905 75
    0xb0010f845d9014801e159409101e030b031029041d005130760740302e500d04e0700d0100702000c0d41494510b2104a4401d15030460380005164100c02c0c3c1c80d0040c12200312001028030145034001e00404000052403400781050f00c100c0c031204400f520890f03862030708420b0b102559054056101745c40704520842074843c0c100a1030700d18031410583c4114149981400140c0c801000076892640c4001c0c10024070703100d001410403d440300b0703240c105515a440310005140012003500c80c0c48407407400d07030824204900000c0303e40c2141c0c803400340185181d442100000c030301107003060200c0210303904002102500d0740740303002045201c40c014400980f203030300da0b000f0a00c0c00d03c01e17400c03a001080000810564070700c1e00003c0f14030b210800d00700501e10341c5491a00240314107612000c481100c42c400c03020404000003900299126140c501c110b41c41076a4a0400500340c0f9419158000c4040400b505112954800315604031194400001818800d18100e085046d00c54003140c0c0300c2951340d0303907800e16001590350700948031070b00c0c0540b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 54451550 1250 54450300 54450317
    0x50a0602070c06020d0905031002070204020c0d0c12050909041103210405010314060d0b091504030810050f1807020f030c0f0105090d090504090809030a06061a0a1205060109050d03 79
    0x41d207002c1d6485c056005010800c0f404010036a400524011802d40d00382026840340414804035010f80681c011844050250074211582c440c2d1001e1b242030b91300d02130700000111183c1c0301c1d0241c40610407505442d406c6051180041c010980385072584101c40c5c405001c86a000e00c1550b185400840c1c21781d12003404410010f410403c03507a05009030444e20038858003130206801c040300003400c13010402e20000c0c9040910800922500d81c103004025540c90b00c00c030310b00494981460010074a40c011540328149130540c3d580416a4248941511401040500f20040c4a451102e1081c400a030040900d811440380d00581e081001c4184060004034090a000301303031060340c0304901801d5450051601003144c0c0200c000d101d003d503100c0c4e02c0004544d415240040d520300c81d810a003103030744a03040c00560507202d900407250420000707600c5031b8202c960510008044c1070000390420407038412442c3e80e00004240c010030701c3c0486425031000c1d401901c14109039212554076004100c3c200408001640402c0100c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 54452800 1250 54451550 54451559
    0x4030b19050a20040f05131b050a03060f050f040905010b0a06180602010b03030f0a18120c080609031c0e0708030304050708240910290f030303070804050a0602070c 72
    0x510f5202407120003291003030b0a00c1e040010540d441d0025120b92407140d0003c500c00c0b20051020740c0007460001c000e03070506540b429403200280c40c035400510a00d00192500760005081011643e400f029608002c00010055600008100c05088081c000313403480e541e2920401e1a540d50607050900424003074407001c910102a100e00500ba140e01d0b03002609690424001c0001c0d40c1d40441102c2840707200381d58564a50030b1a5004030382d107003564211640d440200c2e20001c1080c4a015400c48026449060070308015074543c084241c070b40c402510440c2281c0e1003441105180c8000a440308505408640e0000384112118482407801000e42c8c0400e1417034000006200074400d042c041440074081e4900100409858200401c01c091280b10720b0780b144180c3c00c804112903044c1440075801e0303c1c0c07441d402403140c1040905040901108801041c08806102405141e2070401210026071900020003a40c19503075201000d40707030b01000800440303280c000c00005200055681c809040428010880090002e003030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 54454050 1250 54452800 54452831
    0x170a0905010305091b091008010515030d02010605010f030902030a2307080109030f03111209280804050402032815060507021302160206040b0c06100b04030b19050a 72
    0xa08501d85030341100e0707444482e1040f00c00c0c0c81c009a03001515241c001d075076070100003087c11a83d900702c05034550030301003404040c5d0522546c034504800128141e44250300f43c140d06038201c9006100b16404220f80c102d070350400e607011b64440b0344443d0018050390f03284250395031141081d04494034131089406000000c180004800c005600c0501600402082025681d480107403900c002d00c0045800c240c2c03030f030ba0105503120304da0782030701c290000e070042c1d0082e01d050007038249445a03010b0500c548400103c20042e01003001901b0b014101c19003020030f00d4905410042400f0107584000c080c110801c0701404000700c411401c10b843d500c07140b0b01520000c0c9860030350034000c038a050540c0c09082002400c2c801600540c0e02c0700c50411811044c1200180e4a498448401021881c0244007942c0020040790001d0348410f40e1009046041c003501c280d07030241d61031001d40624003006000303c0440c0c010034007040c80022003001c01640c2010b90014251500f4030319010348070035201d00b201d060020b10f460701b04a1808550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 54455300 1250 54454050 54454061
    0x20706060f1410171302031002120a020c0f150103150b2101060803120f0a1503030809010209090a09030206070503070c20040606020714030d050307030207170a09050103 74
    0xa550038010407501d4000101d02c610040000d8500c1000004495941c03240140318460075001aa15110381514140c0004c52800e007958405034000e000385203101d02c0744102442110514511030740c00a07070319100c0d810490b000390400b030441a050720954600008509041152a0700d990f51440c3c6868998110314086076140c1940c9030303030480141440a460450394405141ea078220b940d040e410903581804c034240754050411944074502c0c03404001404002d072a002c0c1c6e03455118500549418003691141ca498104442600c454152001e44400090001031310904002da0400355a800140c100209800000c00c581c0c81a0f80303043c2803e568290b00010103405001e5594800e11504150b030540ca480e2401921106500b04002c022802800074810204840b00d800c8071003001c050030400490f074440c800a55100c026010340c20b4410101c0c5c070f00510a01cad0014180300c000710b595607800d0850f1154401940039401c400812280b00c01c00d001c0b90381482c0029405003000040c2541c0e500078144c54034002408584 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 54456550 1250 54455300 54455309
    0xa02041514040305060c1c14070809070302040c030218030d0c08070305040e010906090e0d05190309050102030c0405030f0708030711010c24140405030405060a0c0b010608041205070b06121002070602070606 90
    0x1400c001072903c0080b01084407689c860720314100b95115a40c2d40d01c20710300344041c0d0b41000354028130f000c0f00c0086040d819401f400203043d81448501220305414105a42c2e1551008160005101d2081c1c28001491180c080d02c9964400d0a140c2d05140e00c6400c7c51021100903040341d540c1039aa15010404a0802e00941e140300003e000540744800c101710303008040340b2a40f4508015015a400e104201d0340c03090f40108400c80e0031000071500c030b0901064500d4198414410540f1900c00c09e0095400903101062420445003120010751800d070b03440d9a609000c009601005052202c3c0c1590040425461065200320741e03820500028a010b415040c50101c1f03500501403034034064880100000074800200326020340710200c0740c16847d004402d904a68003140040c00920313401c40c00000059158200403903500a503c5107031710010500205000325028055000081e140d00046004500e6030709100c00000b111101400590b04110780700c2007a001039030b201032011100703a40d002900c002844a144a418041d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 54457800 1250 54456550 54456607
    0x9050d0801140a051c02061b0c0a060206061009030f03020f060703020f090906150d090c05041107230322090605060304060b190b0702090a02041514040305060c 70
    0x300b4107502240d40c00340c0c64010706010300ca142e4000e002501600b0341841e0100e40c0240b06a9a070f044001003820400c001c034600e000e9600c2180c2d00103070f0b603241c040d81c0348055030195801401940d41d01420408843d806203615010700000c07400c04808102c90b8299509500d000c1d4000f41078150411000901e449001094a81050320600440140c800c8540494502e4001102c01c0c0000e51500380014a81c3c500d0382c421040b1241c0001a0110600036503048040094098800040308a80c2c0e0014001036504a50f806801c04104101050001d907201c54510748004008c40c00c40002c804049445265501c9600071000107100ba1020707000a41005051201a10102800b408040d1400c3c0106100e800003400081005864020313034080e54580c050341c10203400c4c000d020007014658a040c100384991000100ba40139440c0d00000841c0d4082c42c0c000c4408840c034040315410f030300f4111403045581c5041a142440b03401c0c0208400808100c04225480c000c00c00080740981d120400b4040c1c3c0e401b031b000c0603268001c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 54459050 1250 54457800 54457829
    0x1060e01020a030c0501020c0109050a0501150e0103020402030a0f0e1b0303040501080136140604110f0702060705010507090611060c0904090311070605030618090d03020a110109050d0801 82
    0x503907400700300c00e0041549800c0c110b0182c0c1d480c0c40c0c52406405480c091a051b1340c41c1503c14403d0005c0000c2d02d81c41070b40540020071800f9a08140503614902e01c0c05024580d1142d20300400050900354010740d800000354100007203500400c4850000c0d035040d04810081903110b440034036030b90722184940ea543c20030100e00031450315207880d0018040d0001445400c605030000c0c440c3c652850010400281c1440f40910090040ba41d1582050000d149028121000060141c0000d1880c2050b11804440c403408010716400c1554441c001c0115600c0003038102d2700800140002e000040013401003501441482d11030101290800070000d1640c12040407020f4140d008100340003075401c501e0104c5040c1c440513200801c841c861800c0646071f0f420b840062503114401d11030300040030b80e0f020b0091800790b5400c4691240c00e081c10901d0a400c10340a451640359500141d03c102c00d40f038029801404c440c0c4a9007880c129441e40806000d0860340f0b412000d6626070842482c41204a40c020b05107030141c200385030012075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 54460300 1250 54459050 54459077
    0xa0e0108060604090203120c010c1101180b070201061d04050d1409040c050702180601030c170c13050a0608011e0815040302010e160f0501050c0a1506030605090f060106 74
    0xc0d40d190240c115402260b40e0041ca0313055440500554144440542d1915901c090f101c502500a142c0b000c00c03c0005800d01002042c0381c4410b0141341030700908065039000402c10f0b5100c140e0010000b624a4066642c0e85c1e034001000c0b08441d402c83d001181d500000503030347ca4581419424402d5400301c2c8410040d41d42c24090b84400d184c015909904800d4a00040424101d01c0607a01ca10a94101a51000210105159002c20160000d12528080c0d0f024062108c80e400c00741c1c3c000c038100ea8083d41c2da01040f800600b1550b400c0c80600301c2c8440400c04042c10558134000326100e0980350f001180050b500d00b0041c400501e140191600900126501c09081864003041d5a220594070103080300c044c9480c004101418800d402402c0c280f1914810f854101656a1025942030403922420040c08030344040050158080e2042c3c503c104040c5014004170552070746c03500b07501c4003150420032003681d654030701001084070f174402c05105010110013800d0541c15840c49034903050050703008104121020b14000e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 54461550 1250 54460300 54460303
    0x10f12020906070209130303140c040b030910060602070608130b010303030207020d02030d031d0601030320160b0301060816090b0a0203040312020303010e0f060904170918060a0e0108 80
    0x54628014490040c1c8415101c8005010761241080107503001c00f0080621003289448560000d0031032183d1800c000404002079030b101140c00880ea0100c403013034140000c01c0403503040030085621545840036a000343c1c00742d6036040202c030216009100107034050314061050a0b0000362454201055007059007049c4055070f2450007601050000608160b0080344141c00c64031b4040c141c0007225401816a42042c1c81e54400600620390288280c1d80c0c50300c0503070f1003800740c074020400605903500b44d0703900341c5200c0082824172145020b0b0603a280482c494000c480241e032035941c110313001501140318060f5032035140510007004070340084c0216038003003000c220540b41c0c26080071a032030480c1c004440f2280c0341c0703022003c1030317041d40115400034007040a0024008000307035000c002503040e551000311843c1e15460b07143c00f070748244104940041d00002610b0200e030203d40e2014011100107031440d0039610f05900e080c013040d840d4405061b8040707020700e040240001031078200182d102510b0901c60060703082d854002400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 54462800 1250 54461550 54461567
    0xb0403050714010509040e0f07120f03031d03070b0604050106050c07090b01050409050406020405031c0804032313031203090309030b040804080714100c0f1502160c090b010f 76
    0x605003124039410011543e40104181c60308000700030410400420134240894698441c1038134480503004501000c1042400d40f85070328040350300058460000e00c1c0d0350380c0940062200d0101000265080e0081101c0910100001d0440920500768103613581050010301050b2001038000e1810f1040078810300c0b0501d00d0000c0c3c0e06049030b08400011445030245070040e100307031040750032211249051104100a004a5400910440348250100c0f101c410700059801d00340140d43e190900020402c0c000308002c02c2c403403400000f209110718554240400c01e240d80074100d500a000243c20441280010000c2c401c402400085540b81400c00303002080c0c0d00c1d6402860003540e80001002c4600c894045000d2012070402d48005c0c1c07620004603075505031540943c00b000f1307600c00700c1c0d648141122500088454441c03000c01010603800b005c0205402c042e503803001e4040d16440100161103600788018061207c00d80c41114500380504200040f035424500c03d442070321442030744070781448890400c540da6103a000c0c201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 54464050 1250 54462800 54462809
    0x818060412120212100506031b09130e010c0210050907060c06060306020a122003040b04020f1e03070f0806010501120603060c0809190209070e010315030515010b04030507 75
    0x24001800c015000540c2e40d4001c05104a1040d031010500c1d004da50180d104641c0260b5454190700070841d558400c120140c4000c49104612246110300c41020488440151425103001041407504402998121045601d03445405010340e45801042c0000354062011a5603030340f8004003800381e8948144529078030126031265000b00300c803a0035000d0510400d0b61003c0041d544c8000700355681c40240100074082103c01d5104012686032a200e4000051401285aa0341c2c500c4040e1500310341d07c41d182c50007110801801a6005080310914005076501d03400712280401c2040420b100480340c2606052500c50030707801504a0548071481400f80c1000010040d04481c424030708000d4030702c1c41191807409000c00d680002d0a4034205007042c000349410050462180380060f0840320342011383c20101c0c0c80b001704024041d40000c030174030120706c60f40d00c0b0768807403a031210301030501281e0110707a54204640c00e10560310507541030b0443c2e60499045d402c0080054010155601c019060500310b8840f907403101454801d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 54465300 1250 54464050 54464063
    0x180209010e010309021c0309090e060601020d020c01080f0c0705010606050d0b040203010e13050f010f0911010206070806060f0c0703050a0201030b010207080606061c0c020a0c0504230c0f070c030308180604 90
    0x842001f01032060b0101c101074494148240301010902058594800c01907c025000d070048660b10642c0f10301c001140c140b090014ae4416645845280e9100c0c003140018010440070402013001e100404c00c240908002859165146641c650038081031034215130f00036000c00d02c80c0e801040104580a07100303540e5904002c014000c90709a80d8540390142c40e005040d045a1000d50800524240d0342415601000e405030044800c00007459025004903100c05c41200c4282c0403980d004040303002c40c204540500b5100082e003203200d1038030441d00755252605890307034001c44181d40192401411564036001e0a41040400e000401c1450f0a0494454580c40c008104501030300021511502d0304486542c01449244503075410400d210041000039100d2100c11800d070f40740c6420700707c00a02d80c10103204161140700745c004150000e001c10440000d42c80b43c003415440b10140140300125024035118000c04019124500040c1c0a81c0380d4078020704a00c8000f000440f0701841c42588249804000c1602540560b0055 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 54466550 1250 54465300 54465349
    0x10518060412020a05060a0b0901090c0f030e1609051801050103120f0203090d08070c060216060c020d080301170d0503160503040204060f080a060f020a02070e09010204180209010e01030902 83
    0x2e04038034201002902900c0c034880e0313100380019500c442c0c1c880e6040030800d461513005607072118162400e80d4480d0849500107004144001101072080d403188280c107561106070307a01c440326008003107850362076600002d140558030380610001202e600d04200b400c07020300d0000d12103585507890b65400860340040c3c0c2070900c40c050001010390b80c0f003481280d600c3d00008242410005050500b62855040003d044689480101c00801e056000240354000c59100858510040b41455000c81c3d0301341c0d90f41e004036003040d1440c40c0280095080e00c003840c0648003405640744003000420145160407403540202e41444400c0051054180d014111112650aa81011556601c451001c54018281903200b58881c0d6074408007c0381e104800705134415814000c08081c00504981d0f91800c040344508040e03000941d200d2a010445000003030384040e4490504400142440d9548582e4052145480103038890144d0000b2400c2056801010f510142802032a0030400035a140c1c0c007050211440864001c20034280d071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 54467800 1250 54466550 54466583
    0x305040308130b0301060c020909010b030c0f061c05040c0f0e22170a030e0c030a0f0309090504030f1218170403050102120601090608040305040b030a02091f020105180604 75
    0x1030002d0b20042501c42d40013603803581d4455004280c1590301c0400c9124100c9000410054541405410000d0300014040d161064181c01000300b901002c00c19980c00080c14814028000013220b407510380d072450b11001051a00c0c0900c0d195070950320b103400c400708a1403c15001d00041048070031155002c041003000d21510382c5106034a91075158000c000030502054264541e00044541014081011154509110125600b1182c58552411401240e01030340100c901c0c1c1c0c04117508a005007d40c90090a14641e0705031604100340a54004490a03008a061550400e6a0a500004400007a802c01c501003200d9a1440980d030000c0001c814054000e80758840703096043c141500c104d9008590020003103542c1e0000c1495003060708405c44101d4045403151800090307041c01401c030170b4455a071680e922440d16082611000e0290005003441d80165070034003250f03016440380d40b00700da00401144000e070116045100001c0c2034802c000c14680440c1e500100c0a0006400007900d503800c207901907218008581302 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 54469050 1250 54467800 54467827
    0x406060306020a1205060301060b16140601030b2508070f2610080718050403020a08040909050c040c050a0309080d110a020613030c0b090c04020c010e190305040308 72
    0xa9000a00103920000f2180261a04448240034a0850090500c5507030b0f40c050405003207540354420b41440fa10704106415000d000c403201440c43d9842041c0c202c0c0f0342c0e403020b812680390641c242c1080712030302c80100900c50f00003941c40840c901546000c02c085103030009600020180316016004406021401140210103800f6074409210703854844c0d41441c0200e03e100c10507104800c244c41001054502400214a00c200469044107a610a45400d03480c513804011040003000014420f4045000720036200c00059200c500910040000f4007001c2004030f15418054207242d8010803e41c45285410704e4529290340250580300b142906040005070102c0c03034281800d061080011940109160071403c118600d14003020300b03000b600b15801c8440c2d9688060749030358407001048003d00821300b96201200011740e00c1e491594048034450503188004c8407940440c00366084030a1020007030351600752941c01c444041000da07040900c001100901440d19407000f800510444c0400f41203181c0000b0b110390003201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 54470300 1250 54469050 54469061
    0xd0c0c1b06300c09090609090f030c05030c06160e01030911010f050d020a02010207030f090b040306270c150903020a060f0903120e04060b0913020d0b0604090c140a02030a0302030406 80
    0x142d40310902429051003401002c60403e401140100c9142c00b6010441c07515920400d00340c107612286010082d5403030b03102596074049000303007280c40748001c20603078800d5841440b179107024404450301c9603956012002e0251500c45500c2199042518107400500881c94401013031b440c0c04020300f8603240d40e11070b040085941d849200401c90015000044e9446515415030007010218065503414030b0340d841d5484116078a07502e5100c1c0448000007840140701044040d0b00600d0a0210098107048802c0061f18061140c45000c00954441d109494200400b041c0560228215049440c10044480c19503000030300303074001e5000b01c00400564141086c0300c039000ba284031001d950800800d250341e0201840c01440c074100c160505000ba400c00400003407009005007a140d00351401000300552914120f6094001c1d004030403110044c2d515510000d02540380c07100100050110300b00045140901c400c40901a090205c60084003c6410881c41c070700c0c950b000c0107a50b680041c501e809079480d10741e42482006040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 54471550 1250 54470300 54470387
    0xb040c020706050d092a060513151125050f060d09020409020d08041802030405150615120105040e03030c1206150a050c0106140d020d02060d0c0c1b06 66
    0x100500108141b072020340190f1900c02c041014001c44c181c3c3c440d02d080f5002d002e01200d4107105024030701c09101103200e6003c0b6a2180321186071400e0019001004c151614410b4500c3d0303c4c0010304821140ca985130b03000b0b2020040d10703056500c03110034000c51001c240103104a0030b50551180d032745c80c114000c559070341d00050005500100781d041e1030082030400700f0a5034828030a40304004039810258405581e94000e41e88242d4200c070107401c10b4400465000303400d90008007200e510001880c1c1044171749480d58003402c01d03500ea140d180c510649c140428402107a58580b0503013180d50041c010070181c20b030601f0460340c1404051141032541d459203000724410a02040c22082c80840c04268204001e91003000b0b0201c01014000902c03e4603520103000e42c0701e052581c81079410041e45503401000d0f0614007200d0b00210b20251070b030b0303141c00c6440201c0070840d0500c0040c04005070b920304201090042c4070319042006a42c604000705028a08200a0503c4552010801d001c3ca08850a030000c0c055110a010180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 54472800 1250 54471550 54471563
    0x180406150305100507030c050306061e030c0705060604051b0d06090c080f070f08070e01020c100305040b010905010b07020108070507020d14070b0408150606040f0e06040b040c020706050d09 83
    0x441c0c407807810540382d000580c2426540380c0340800003200180b00340540b9400001640b981403441c2c0741c84007401103550020f40300352a207003140100904000d06000c019441600a491410348035a0705151040c1400340c003829030742c8258146411b020324000200c9400c0300c803208002c3c0e80740c3d40d20002d80940303001d041e5a520402c59149017596000d02680c00c000402d1003584000c20040c0269590302d03050f40c61244120f92440018421000201018020201020800c0050044070303280d21446001501e075000280340c020000ea02d51060104211061000c0c5000d020700d035409001642c1840e003185414002c2850190401c41c0080100c2c44081c080c600b16245950007504800705203c1505004100c2c040e1044900c0040c802c00d0130014603820003100351000c1d2001301000c0c108038240020000907094001d8021a44100b00300030005441c00f00040c0c004c01415100c2d4070805525000e002c0108650495609501031070a081d45521601c1d800b1a10000395441360402685a082044a14004007408180100300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 54474050 1250 54472800 54472841
    0x1111006050a15170a0b0d15050c0301120303050408040905040c150509010207090c05120a0c0801050d030e0d030908030c030c0d050712081905131203020405180406 72
    0x4550390410416548151000c161080d41c0d10111102c550b144082100001c1c040d88100109548803201d2a401c0502840302080c1c64041c0c07000201031490b0b1003011264400c0000c2c0e020309030034040c000c0991120002c0060790466140000304052200c0752180241010b030340e80000f40c10058a141610003234440310204020914103890000301e050028081c80c5501000ac020440145208504503060500103130301038030410f0b00e4185020050400c2c0003080c41413101c04e000345d00030080b5052034284038980c4c2039070100d003103d580c15001d02400c1041e04040c0c02200b00c0c48081000c01c1d001a0070244c620030580e08480c41201e141801c603541d031015004051980400200307942141c2001000c0c0c0603c0c2400710549038249440c0b030b41504d142c8112240140300f50025a01800100d01a02d006503200a003003a14800f8040400380c400200c903402c03954510b060725803850001c14030000c580002c405128a04086250238203060010314001ca01d4610751086503e1080054100300d820380100c1c04030548009802503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 54475300 1250 54474050 54474073
    0x10c11030412081215030f0304060909020706090204020309060f011505070b09070b0a09050a0e0603150702030906040905010e0a050108070506130b0301141801062a0b070503060414010b09040207020111 88
    0x30752205c00d03050f0610a201e048001d4080b0940031007103504480080d1200b2241500c0e21231003101035080040140d48843d40ca40204025032200d0001350b110301680c2c0b018050600d010360610040303103410b8211b4080b4803458601c8480e030980050444440d590000340e81d8409035140c80c1101d00e4010150440141d95101007020321540c0c0e0013962510649104450104a25454540081000100f04d0f00142c0c994400c0e00744049040143d50b40980141140c070559140c00d595030007007102a449a0300c03040c250340d80c4c0c3c0010000c10382c00d52100b6401545081d01400254504840035684818a0292034130034200000d50341c140d450516070307010040000300b981c3c944a60351414500030401d0004113440c056202c0d01e040507020b070754800c0380394140c034601d031148400d001c004010081e92600d00141c070000071005404010100301c085040b00d1140200b540e03003d95914143c8240001e0740c0c10180c00903c0a800280144410b07050502034944042c000c1e40d0040e100d4507180012280707981811134014080c0076218000380c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 54476550 1250 54475300 54475321
    0xa030203040602010606050306060d020901050f030906151210050c0403021816090305030a082e17070602120307020109140706031107080304020d020f040204080a05010c110304120812 80
    0xc100c50b010b4000b0081c044c3e03900700a4420344002c80710380740e00075020010800081d46542c0075010400042c0340c150706060f90f1000d05031031031f48241c5042c01c040c0e1107182040080b04904005030640b402c155040d03404108503005660381c8004003a000d040c55516240020721528013282510010b40d0024102c0c200c410b2040001450f43c00103450090742c000c82c400204c80074501480090701185c8c0d01c5402549400d081400807036420101815100800496040d403807400070101041c02d41a074001861149070501d4000042181501d403803800b10303290820701c01004001e401041141c2d9900105042590302c0c0c0d00c248089005082d103440080c0b801d0401d20030400041d0b00010003409445070341d202084088941e068410341401580c0d4001c00c002c03410400030b00141028941030424520241c00408040b2070b000014042e07070401d80201c0d0180d841401880e007480003d00960398580103c0c100441848051502180c40740f003280075481c0003a80c08110001009910411034007040c0c50b0300e0628200c2e041850312036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 54477800 1250 54476550 54476557
    0xd110411030f011502060f060103181103010f200d09020a0806040b060102120306010c030908012909090a170d060b0c0f060106050307030e120315090c070209041e050a030203 76
    0x28540018100042034042013602c00880295045e0020201035550152614441200415003810951609503001c25100f1101c840030845109030f55070764414003408249421a84403042500305281031007503520b9002c0d48042d0449055031121042966451079030302643c007806d20810001d4103c510702d40002480d40e00490114041da211b0302d008400b50300e03018012a5034a0315440008501c4004002088a0b0342c002e80181180a1085c204001115903411410742181c43c80345010003800701d410318030b42404081c20142140c41804480301459820f10180103503942242100043c14a074010b9044141c40360300c02c065824040b0142070074070285488105003c61600215510f91080c41030302d404100e0720030049003050680b031304c0d40e40e5a4119524040304030080c120104c03c2c40050300135410712003a03401803d00114407485c1c0f4500d45240f001d52020070301204140040c1008409401031000c1401a981e41044582050300150240440f281c544c2c5010081218a00700500074411a80351600301600440038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 54479050 1250 54477800 54477811
    0x612080a02060a05090d030e0a05010c080a0c020f030d18060606090905071b030509040207050102040e07260403031e0c030e06011a03010314070e0a020903010c050708090d11041103 79
    0x20342d0002e4941c502d50200341d8a05581c003659980040750a0001b82d8402c2d407010030681000411980d03801e4190701c03145d0031160030a00384e500241603e010004a1905806a1420003903203100402007140046a482d88a00480390100d11141d1208003403c00c0300880028012903a801640400040d40d03200f1303000c1e1031159188140340001d0b04090005000354050b41c041d840c5411a42e0604110302841d80c1c0403143ca074461804264400c0d402d100000c01310300c0910281015103000c0b0b4803030301281007482000e0a6500c83caa07884000c820f1001403024101120820359410643c50f06010840310001c0c900c143c2804003181c141c80030145060100c18006507d900051018100722064942c5642c0b105940d803070394800c104807104800310420041000070710044294007182040d030261040c1a44400303c81c80000b50644020668940115007000580350a100d4203160401500742940340c0910740d40c03408118020900040c2c03003881188058014031150f42c4010b20900b40013401044141e0046000002540007503a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 54480300 1250 54479050 54479053
    0x3051204210503090f1c11090108060c0a0c0303020405090a1406030105160e0609090f0906070503060a0504020c010f060b0403050c030c01140a031506050403052a04090302010612080a02 81
    0x20458480c003800e1110400702d4110740a1440c10300f0800901000e80e452070100c642000114640030780c80b440900c080040a44070304800031030490420f040014008068110554680050040c01080c01c3c8010864545640e1b80c10400c503c28541d0900790024007855101640040c4c0c24420400625219400718800810300d040034a0140c44000038903003280c80c1207450545815401c003102024a00481d02460860402403469141c40707603080114024001c191090000180f8140500030102801c1c441c26a01c01464030341282546080e40018041004130300c5824011540000d034845400c00a400201901c050440c1c08d02140707903649017a034200c0c1d001c0c2c0301c2901c0f24001c20003450303424540070900d810ae00780140d54003040811400300340c3d042039000e441c0c00c409050f45c07102c40380b41c002900140c10004082c1901d881741c031070707180d0308005091603500f0742c00d001c861580319003081d0b2a0115201d4103503426401d4400003140d6080e032600743c0c01080e9a41101e03100b0b45007800c48030b08120390301e00108a152156070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 54481550 1250 54480300 54480329
    0x1b070b070305100819060f0608060405060c032802070507140102070603060302090106030e0f0f1e060402011211090406030804061b08160c0314010e010b010e031507030603051204 78
    0x1c0094058801801028483c0d00042d1102e03945d0351445018003c8180a0400000c01038000c2181000320b5a80390302c00700441e0890420003050200500c00140d2244203c1116440e500d0000240f403880368241ca03200c031056040c2140840d681c8034950617101c2103680101203410302c50f00c800000f811106141d035118014400c560021a00c9803090242d0411264041c0034040c91341d0038030302c0030707809846210140804c80c0710b0085009880d540401c2400045541d0b0b030003401100d001042c00b5a02c02c1c07011038602030554081c1e010b010060340d10800260410f00c1c040701c00105004be020341c40140c0c2c03003030301c480b6a0b0060814201100744100310300203004a901c80d450b2108440c0c00b149040402d44403000c40900710700000d0002c00c40b411480c10900c41801e00c98900c03001e656071280c0d114691004200009445a076584030100c0030103400b4881c80900300740900346680e850900c100040e90700c00030140c08503807070884180130450682c082e412010103907600c07506440c2004a0f943c621100364200f0b1103041e2034070500a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 54482800 1250 54481550 54481561
    0x31e0c020a081506040203040203010207050d03020a0306120b060d02190b0c011a090a0905030f0406030b03100b060a120624020c0904030905060306010903150e06010905070801030b1b070b070305 85
    0x518a0b41c92a003030203000f541e030394404040200035000200305030f070595020072150000440c20701003210402c80b603407001a10348400c40c074002c04031049608011082005100389102040d91417100a03401981161051032220311403001c00c00008a6104200b40d100d8005004113821320660049d00030300205500030004144484c40740109a0303164590150401d201d80c01144100e40c00d90490f80c0003c2c050000c03645888195001c0594585c0280d10140c0000d03030302c0204545c140703000c0c0300d8518001b0b10244d0510080080c00e00150580c821507a40800348511a40e203aa20b42070b0a0b0010720041a0380c124001007110f00d504504865400c4aa0a80050242c5c190107050381c50408038107070141d509070383e1300f02406d8104003d00c00f140d80058500d03414031074911030010015812070840c103100520604082884003650442d40d1a0071010f8200f102a68100700400030100e0f0b02100480c1166006011901541c56170030403800b00101242848542d50070020b406424000d8030340c0c01c107018010540e81001075684a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 54484050 1250 54482800 54482803
    0x19092103141908040c1802031f050a05220e0d02060a0c12020307031803020706020c03060f0f070908030a03050103021813060b1201020d0b03070608010f03030507031e0c020a08 77
    0x221502c1e6461200010203488016109100495106102d185010f51881d1100c42e44440341600c03144005070703190000304019040306501845001c11003a406140c60860601c40043d81d61b100e20300030980580c0545154900b00020f000d00d00020b0001141d0070803030409149106500d0740c030661600b02c054030804002c100b0f10b014078840c00c00c07900d200e0b94501100111990340b500180d400501880201600d1f075000c1c1c0204103068654510a601c240c00800741c0c03603d014000390400c04005002c52298000c0403c000428041c02191580040d59001c00c81407a038620505551031081500656014880032910114803900760340441e041e42d00880b030f180e1100341048070310a03031203100f103a80c454080d002c201038078005210341d00f119240c42e0b002015034403000690710f4003500b242c10000130400166250400301d5501d0900b03000b603c02400e428a8046180e40c140044030020f01d4261200804020001450707500741485100c05002c1100c10308083d85001100220040ca50115080243e11400340000c1c0050b06080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 54485300 1250 54484050 54484057
    0x906052203081302010c29070302040506090d06110a03090615030206071101030e1006030c060203040305030a050a091a0c0114060d020d02030a0803160807090b1909210314 75
    0xe0540d00c020b859a9401400341c40c1c0601c0f80d900324184420713840c40300300003010000c12070702c1141e5a0604400d004070007100c0c00c0d080c800c0500a8000e0505c1003001344010b0700c80100325a400c4000f540c11290079201842c0000041003101c010003a05000072030040b20a65140d00103200280c00b4120901801500c40400c0c2202e02041c88000e512030010081c10340040c1c1c0300d407686400710364141000600104440c0225013402c1040c04201c10031030b540e0703c040c0304004444034403001403c240d200440c10309095540e45661382c0310302610311041c80400300e058181c5d2440340da40d0310043c00d01e07096503101030b0030300e0400b050541d0092a96503d80e9400e012038121014000e1086070f100d007100901c102415032081d002c0c000c4040c80104140e0305406000c41c50750124114000940c00759240006e1000002c140f1075008052020185c14030007040100d680070024048114240e400c1021100e2040301000400130064918084540c0301c8642030301c54411201070b0301e41c402c5000f07441a0094803007a4064011804c00388441c071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 54486550 1250 54485300 54485303
    0x20d0f0806010305090a05070b0705010515060a0c05070f2c0709140f030d021e030702060324152a070e070507060609091e1211010f09060522 62
    0x468840019603258421340066400c8102c03c400d0300c00340317040754071583d0900c0c4040c0c0010440501c0010b00c841089000d200e050341c801542490f03591a1040a00080c2c200c1c8228408542045400310241090000c03e01807036004040010740c4001003950350444031103242c0c501805a40707071602c1008524102c210940094030400711a916001243d05100b280301420091510701500501b0b03102101580f070f1010090709260041c90780060141c00b4483c030074030319540074900841c2070340d4109025010050b119134050fa40c0049149030800d6400c41c607003282c980c203000a1840c080d8403844d02d0040076088072810000700101c4109a01c40e900c541103400d4000380119602250159903840304500b0070202c10078100003904a80c15151040c6481055150181682c0d401c1d00a25036466403070340b03640d00700452a181d00c400380500807a61904401280c483c0c0f5046c00e1807844482c10b12219450380c200410082d4012681142c009900f0080803801d403d00f01d00520080720141c000c09030140c5080000303d5101c0d41600c019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 54487800 1250 54486550 54486557
    0x4020406140f1c1a01080d020307050d030c030e0303130506070903020f040504030212030a0b0f040c0f0e03120a03060f090207020d060b01050d0207150f0203091915060b0307020d0f 79
    0x210202803e11000c144007401094208514400120000d040c2c0800205943c003e00016400d65050600050900201281d40401d560040045200141c1c3c00300350b800e074107440c42c180040c014031180419401f41c000c507503061a0f2404000700308a10125802d002403920b6004208441e065a961441135411001502010394803107a071000c0e1080740c1c0381c146c21680d80240300707205840c48412500c28250071a0016541c42d50011703100d0002c8040c40c00c11002e16180280200d40600200c220b00e88068115500700c03d01d0000c005050706100400d80303040203061440f0340d6680d00941e81c2d21010f1b03002001420075005100c032401812800045a4080e402540c6030701d6001482c10320744118a5980c04001c040140007207040c00760502000b0040002e601c00303065803a015a8080c2c02c17550030301c980c1d0790449400d00d02960290780706105104607040000740c1d40303020440b400d0072480d50100b6410044440ca0040710069411070501c503010500c0000304018501a0595030201c6046041484c015582440f40e003d449000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 54489050 1250 54487800 54487819
    0xb010203040e0901020903030304140d0f0c11011707170112020907050a09081203040302060a060b030a02280323010303020c04050408120903130806010e0f0702030c06040b0402040614 80
    0x7010b103000310440e048841d0784001464200b01c8404079003150000c94040d28092507150083c407050f4410b21000009840710301e032201d0341c000c14a030080c103c4d5030500000b501c003c3c840c0c0d4602d8001d174040c0c1400c40c554032035195040710300c0c079250900030111642c4203200074200f0700901c000200b520f010030b00d4000c8030354001c1c51130685640c0d01200310340680028031f980f4100204c403c4000751400c0305201c8203560a00340442c00d6500c0c1b80030706019142c0f01000e05808091440c3c07203000c00510f01054181d0b600001c20031000b585d1a10150310f0f05403402d07008020661140514154504c109d50940d000324205030006c400319032034401c0c00f074010222a8003440050056002144030311802e242c86e9101c164018803172442141001c000c8001140d01100446e00300401307902c0048d40044c00102400084002c009440082c00300d03604100d10004010707006883c01c400240000085484c6034000c0c0165148026800c0071298186000d0a00d00c619240c10784003a030140d0300e00782d80403896500307500c620443c40c00050042c526 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 54490300 1250 54489050 54489059
    0x170c04061a031b0d1d0a030c080c1014150d03050703030525030b0102060903070512090109030f0803040b070e0f0127080309030f0115030312020d020301060c030e040b01020304 77
    0x85642c001032100700204046075021030100d03c100060408031103500000500070401c240c104400b01c200c030041d19078941c81140104006580412080350b1a41e000483e661600380082d0580d190002d060040c55140703081c280f035040039200d500d83c540c1c410141c180908185100040500543c3d12480b14082c0016004000500c00329006e07401858101d9240015004c2601e040c50f10404c222150380700341000240c540380c680000c1c0da8108949030300801c80b0b01c081c0d454103006903102035507003440b014100300e80d000101d02c5440c130340e010340d51072001541c100704015801c81c01446d0510003980103c40481d807011190005c60842071103903101c0d000d0010301400013500e04c1c40c50740042d0741d1b1325450095604503010b24a45a0034040050841400400110005544039110903003050300f000309103600900c030b5a1610080104483c006501e14007103a4140c100b140e8030100e4030300840080c1c81940a1042585c1c0000f00000ea4103901121104005029540701c4a00c0c003519010030003981c081c4500c5030300681c0140810700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 54491550 1250 54490300 54490349
    0xf0b070c0b1302060f0f0307080906070f031e020c030301090c031506111c090602150c03070809030706060f1404050601140a030608070807060f02030901210207020a170c0406 76
    0xb490035000410050070180003180d042025446849021502c1781d010046c01152900060904d0700400707654090582032500e8103004280300011921481016100c40d001024170310031065a0003411440c0304150340da00780817901d2035502c0d0b1003030ec10341500300c0c0341440500d8010b110b40301d560404080700c07401c0c0740454a8080c00b190340c039443c40c015505a009110041104500103070004c07850001076143c07140d41c01d28000b0060304058000039600a030360221800c00c6100d020b07500480b0b500814904201d40e0540320300d48010f1942c007404000900c214504540818059110300380042125042a00d0944a9041100303000030707202c00362203041c046901280c002c2502411030014003000784040c070340081c0141d59007615038544081584122225002004142318080d8890045903d490141c00158a0720316840f000a00d10400b0303000701030360744440c1100c420703000c0640d8040702c8080340c008190089440c1c48007400c9140082181002529109044e5448491304060240c2012100f0880b60354801d01000354012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 54492800 1250 54491550 54491581
    0x605070818010219051b030f0705120f0304080304140409020a15030e060a060503300304020109030b19200306060d02090303070f1a090c040e03040906030f0b070c0b 72
    0x1d9065000d407034940d4481d03a03a03c4107643c040038043c400510700462151500003201c46803c00560117500200c2d540b010701e501c0010b4040071900305690031400040140c0300d9504084050030075075801d000c0040c000941030320000c082c0040c5c503004281c00240030302101c03c0104807890850b0007500000d2031941000811284144006145014180826895403619081d401d0010444607910349540d181414001d50804028005030b1010b41408200c02040241401041d0710100c3c40154214800000140440e441a02100b00655010404124031b09103800c001c6080e0410002c2d898084c0e00d0040f40c3c0600d55900c0416034140d0021244252942c1c8400b010700010343e000c10034907145143c003041240707440c0d01c04100074511030340034804415410006152225180200b14995044000801c0c2840326040003c01c081582c404115000645140c03c3c610040c1180a56400245401d150480003c14004100381240301103201c2d40340072410340c1d1510b070242c442424926015207204024070000d00f0041400c2100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 54494050 1250 54492800 54492847
    0xf110304120c030c0902070203030f070813031a0903190804080f0301030507030309050a0b0307030207020a05040c0c15180314040503010f1a0405040b0606130e010902040303080106050708 82
    0x1a00c0c9040c0c1c4510003007000c000149811542040014070800a02105003400e1024100050041d0710b04149034001a0b56801442441058254002920800c028102003100d0310310000c45404040b04e55281001c0c03a4200c80551213414090f2918009204240f01004a40545582c0314030b0707181d075040c41c2c0c1044422800090003180c0000701040f201d4040d141e620083c500852207013000745909411071400800d45070850380100c0c040d08400300e085c008501c48000b5660300501c14034005854501a000040c80c3c120190f000301e03002894404101c02c0c40d40e0203122070340818082c0c0038600c1c01c081d00c90007803001c0716040030841080c8841050100002407041000c3c1240442c800001130030142c4800c00282101d440c2102890705903550b60452006007500180000f2002049800300005e1426484000c0c110308004d1000d44101000220305030300c00c5e048158003000c0c11041036a10510742c0c44030f101000a40c054001500403400600002440d50f210b0300448040d0b60b805865141058240e00d0320f504458000000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 54495300 1250 54494050 54494053
    0x6160507080c0c100e031005042a05010e0d02030a02100513081e030903100b0604030807050d0201060f1d04030302160c09060609050105180102030c06090705031b010f11 74
    0xc00c8042200301020380300196414001e03143c2503082c030b410440c0004002c5625001d0040440f08994580d9000c2006000c0f02e07074072017011415540d5032a2030030501d86030340300040b0040080410007c405c21801d40c8001554000c0c1c940200c1154110100702c030b80000e00034000c0d895840b0480b2a001801c1c0046480e01074451801c0c8a804c1880602c0340080c0104181c00c40f1141c1e030322200102c20f03030622034400301000c0a03400002d14501005800800d85615803901610380d080e40300c81d40c07010161503e40480d0300849e00440915105d002e40d03d00f8649403400c000d07801c0d00544c03c1c1780011442050450b6040100c615000d05a000f03980c0100444501c14802842a404c6c1030307083c04805684010f02d1840c039880c92060b0358152010342030108003c00c40d5000e4101c81c0c1003085a001c04e000e140d800804446010340300709100440036443d0b00c0105d00d14031601e064203940e40100024014200c0c1d00050b02000e4841c100c00307480b1001c0108014280403121044445e0002c0e0540040301c42150042e90640d40d00b052900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 54496406 1106 54495300 54495307
    0x913050702190b280204120b1605180105090d0807060c080126030f040e0a0608060411060309011116030e1002150a140a020304060c020a05061605 64
    0x80110700d40c59400120500d1303900c1840710110b225030a14800350341d0349072114400e9450444042d02203070154540400b10721224080c1a081c02c075500f255440c1814040c0031400400c0400c0128075039414407404200002031034540b148400703080390183c500340b56102c1603881c0401c1184d403c00c8903d0100401e000c01807158106164507040791881c030204904082c010244a03c9c02c51290b03141c054054000003034001686620005850301ca4070340c0d54010400e00d561135100c6034480300102c0d0b004100a6407204003000500e040c5000e150441040000003510400300c1d12422040d0388604103080380715119022000405510082e00302c070b03001083c1c0700b903e6042118480030796503c0c003003102c03080072006140000d41d005100d40d1000c048103c4075403000f0018100015110000c0d401607030f0545085003400110503205000150030030101d5031060040203250349005800d454901141e8044080201c2003 = true := by decide +kernel

theorem cover : BRFrame.Cov 54316550 54496406 := by
  have h0 := BRFrame.cov_init 54316550
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54316550 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 54316550 ≤ n) (h2 : n < 54496406) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
