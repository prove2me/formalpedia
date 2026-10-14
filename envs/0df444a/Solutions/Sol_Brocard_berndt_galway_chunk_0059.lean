-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:36:49.068347+00:00
-- url     : https://prove2.me/submissions/20a8c11d-618d-4280-a661-5e2937eb1413

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 10431661 ≤ n < 10611517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 10432911 1250 10431661 10431667
    0x615050604150806010905040501092a02070608060d1406010317041503020d06090c020312010e10050108040c050405180d0e0609040b040204090e010509060711060114120a030503060102070509060d08 87
    0x400482d1b140d043c030f9008907005403c100c00420640386a4201280c80c0d0100300d240541c0000300203050700d43c3e4091514000160b00224800e00241d4407803680701340d018101414100648080e0360b1411140101c4403103130300c5980c00190042c001c0207041d01100080800340590181400e08145045169602114180c0306059000a811072031013200c3d0085002410310100802044110480194699100c2c505120744003402c08004034806284040d0f90327024a070100c1001e8004c03420400195035414014100340c0c0c02500341180014281c0d181d010f000d10450140d0204c20b160408882014a008500300c4d141c418099003818405440d101e110942d00b06c22812107000c00d60300c8003000031500a00c1f49420500d1401d081024441401d101508194021240001220a00e54034070104840e0f2100c0000c0b076000c41d42001c401088222150145000d021000034207420f0084041c031040303841c10780b1114044012400c04800c1103d2980c05004440042400340e801101500e0060009858a45019001050b00c4004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 10434161 1250 10432911 10432921
    0xd02030a0203091c050609010c11010501151b0501050108070905010803090906011d0d1424040204050402041e06060e04060b0706020c01110301080c040c1713050f030706150506041508 80
    0x1c2003011044c580c10009803401402c00401c018042c020482c480c101040c03902e444a40703010b00500c100d074100e6000034100002d02c0c0c1111011030b03411290300c0300d03e45800100d0f0080c0012940070b00c5010300034006400100004c0d0701e450344110030795005030300a020036003080c807050b001501e41085e0141c0c060700919004528020f80c03248142e889500d81c2c0303511740002441c0382031010450031040c4401300442c050b04031034544903005c0100000841c8019400b01c100c444501080c010309084c0c00070b541240c4001c00104041c0682051190300d002c1c030302c8607110065220841000881d40020072070103001010b4a09004170750614130301c0c00c01403144800040c501c0c2e41c0002c010011810039841607400440800c0311036030700e59540c074078150f56181940d0600e204500e0002070885603806480f48503041d8488900074100c0d0740d01c0e6001880780703a280e00010754581c085e81100340d61070f01c4140010310710244a110001828000040f5440d070140081c0c0107140100010042400040c0503070950f1030492003145400a81c50742c032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 10435411 1250 10434161 10434199
    0x317060a0801022a070f090e10021602130b030307020105070804080304030302070e01060201020711090403020a020301020c0a0318052d040c0c060c080408091e030a0b0105030d02030a020309 83
    0x21079403140550354404540141080111020091003a0545210b90119807140820940b01d14803031058030103110809608000b10304a5401400c2542d22810649841594000d81c1030242e900c007400f20005030810800500031880c00d04060381160300450010003981c1c25850129a9901c1020b102a052080100d43d070b504002000003101c0182540d1026203450360350724a4013030341ea81198003c901900b0060743c00030400d40c0c414826144201d412113001c0c018844c4007030500070920005402170342103002d141210780c05a1001d000600c0c050010f00d000300724120303141c100206201d03036010541000e5150344200f009265610012032109803900304103142c2d55104103850041099404040c4e42d040b030b040c0301d0b00030301036074001c0380e1a100680512024000024605011030b41c2e4981105e005124071014002800203042c420340410a20501c1c030307464644c6401d0301c00000d1420301034a0040742c220071208014030907810144000f060301091400114200305103d070f4080d449010f1490124092608000d0031280001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 10436661 1250 10435411 10435429
    0x601090b0d061104030302060901020f04061101020903010c11010606020f060a1d0f03040e01120f060e0316050d0207060f020303070f09030b090d0e030705060904090204060f0801020403030206060409031706 90
    0x1d071116007000001d1403410243c596400a02c03050300940500f000241100c0c04c103000b00e82c09984800c0d51207203071a04011056403100b4901a16075002e640c2880600f946032002d101c1e16000b40003d4682d0040301074030000150070b5403415088102150400d00141d0244480000c040390068034048020440e000040880c901c00f8850603212000752140181c1a00d035040044010826248400103e85c100da80760140500034a071b40340402040c03460035042400c04924107170310a080910b0680140d0f440d1404400c40740f012044d02c0b58080d0b8580e0040c40408a94580411690000706054181404220714003e0083d40b2800010084028008115401116588034a03401c0d000b80d42e104030f2800c07050400e8000669900344041d0741001040c1401c0d4640c1c864540000d51034101c54000307204910340515003040c4400b030060391504981150321104045100c5001c00f03004009018100001615140f5509000f0315124016000600481c80c001c42500400d0b441040001460f1f80303000341c2e00c840d44a138404214099 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 10437911 1250 10436661 10436663
    0x9020f0f210106090302010c02090907080f240708010b070609080c0607170123032d07050103050105060702060a110d0f0e040203270703020603040b010501120902030601090b0d 77
    0x328000408030141c0841d0061900e00e8140110302590300da0301c0f00d00940e507900310341c00061702042c0403000c0100140342114113550b004501500f0b84070815980c4000524001a020030404150412550290f210001e50001d0111003528858544142041c100c00760000300180074140a0341400907045080c0a05508050100303503200003031a54500d051814280c480c602514642e0000742c40c50b110f064554204148a41a2184450089084000c200307904862a0814a1950b0103000b040502c8003505039148494242004004404448201440405041440a400190500d490007006000304e0700c80b80140d4003500e505440c580e03914141e007001035452215400001c0300500c50701514001003a400001a032040c041030311468520040c007000c0105030b01044030110b2589180b04100003c0344a11020441000514010b95000d02d440c4d80100352240d10444050b9580e4a4000041007e564070240c0f0190782c0a4401040002c0d1103203600107a21214107201e101e4410340c0307030030f060180c96031002d078110026 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 10439161 1250 10437911 10437937
    0x10b090301110a2a080a0305010504180b22050601120b0108010509070501050702030a06060b040906140607170d06030308010e0108030a080c0a031d0604020405090a0302070302100306030803070305010504180b0109020f 95
    0xe286c4400008018000034012103019034240701c50b920081040c05c402c9507003240e020003e084a03035100e0081041c0c0d045030011603440e41506c98440c10100700c062158a001c1e2180031801241c2d20742906040d400900184e1003201c02ea807500080000017040031452206840d02460035a40c0c0303190a000003231402c18440d00140c01645000c10000c0c01104171b000610031110001024000c0566a001a417803e0202a0010790450b5041000740005113a240da40701000b4005001e86045c101040c4200c003c803001c0350411404201c0b104018841e00d4440c50080e4010b0450070025407a0044502c0020003d031405498034134084008904800c003103000340c000c0050044402644c00e41c18100107946950f03424266000c4e8080c0e4a0100420039a00d0080344210b0307407a4150700100b644a26640c240014407181d440c40c00304046c1e4840c000300025240b503000307601840380c030383e000326a550602c000c000884d040c20800c05880c0c11100a00ca00003038840c08841d04440c8542001610381140b452040d00910480e841c11041d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 10440411 1250 10439161 10439167
    0x306080316050c0414010b0702060403081602010201110a020a030f02010209040f0f05010b1e0a02010207140c010207050306150904020604050d030503011809030c06020903070302030105010b090301110a2a08 90
    0x240c1024280c0302807150003081140d040d0716007002030000f1034a44400c514030104010005220401421008001d2203201404492a099594544e00d0098201c08603001d048102c000e03885003550ba09001d102e4882c4106500755103000d4451102a68900d00e508000741485007804001d03004500030340c1a076810340d40240c010f1146a640c3d052044c002c01c211482c0840b040e01e03003400030582d071000740c0585035a5607501e014040c0a100d60703883e0f882c04e60021488841159000c21000000815141c151200200072030024043d841941c400a0300b0800e568001e0750003680f0200c204005400c8001800e6001303001034460404540f503a0011602c14852608900c0d0810f078000d00e00010181e1280055040b103109646000103844444800010744814010140002e002c0c03036191000700d0070980c014515014014121002e840c0d44e940801c1c03e480c0264030102002c40d0111f02020b05041c28041e03800d04048161640f45800d44195014018910211480c0768085504081c0c0c0042c43c50700c001098090340200c51661 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10441661 1250 10440411 10440427
    0x4051605011e141b0106090204050f010804110d080403030206060d0206090114070503040308032a07060b19060518010203211003050115050a060c33050a020a08060306010b0301120303060803 83
    0x1080d02d00204c05542e01e610740741c800507081c0700500c00c1d14203171078004202540c18900c0d04011210000c000c0e00580341e5900042d02c2c0705881c0d840074065844613110b0b81016889910b107050203401e09000810003070080900c8601440103944a030100c5901100909082c126441203810400140c054000c000b0228440003402106102d20f44000d5445050b030141051300c1d50b1200ea0300e41955403805281c40a10740400c0c030100700040c070240c2102d2004c0d2030140a0018840c140044480f2040d01644164040381001504d4000020034408695100600303000071031800c1c000d500055420b5400c400c05070034403035002000c5030000320403055900083d44c0040c002c0c0062000030303202d196059030328460303584240c956400009101d03001e290007144598100702070f031400104150700e00080005200000d8080c0c40c0c0c0004580604500f48586401100300c5100141c503640040405041000068569440395008500400c00600480b00b101c5c1520501070016048000318075003607000d8042a0003804041c040451400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 10442911 1250 10441661 10441687
    0x180c0b1305190306240603050606210603060714030402040e01021308010606081e1302060f07050307060b040902030327120f0d0e06040605090f0303030c0304051605011e14 75
    0x2034241c03400344108004400001c1c14015282c0d121740c4594101005000c4100401c0380290f10203030380003002504051400c2c1c2e1030307111601d1491070701b542140d000a1000500c0300714142045040e07800f1140b4100440c0c0040e45400b100c483c0e0000620080c03003203807203000601100b0003c2d010749001100c000c8101d4561600c0f007200740c0c040d000d903000c3d1078006800100001c1c1d01d40c407a18055890300358460b1819505c0d4990800490100c0e0791110280e800c03010820080b000c40759864010500c89000f04046c58540001d8a041030903075640c0c03980c0364461400d14070141c01603500481100c1040384040c0b121803400440507041c0d840100c403075981e164400300140138400d600001090712101c551020080c0c680441d0941070035180e00d000015519004003043c00f0610045004a00600d80060003c0c814041482e140000030703c1d6a108845030120031101109210400034200700c44c810350040c14444a21490410000800401800c002d0071510b001e001c0c52110854002c50300c0074a9010203c04042d600c0914107000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 10444161 1250 10442911 10442959
    0x1021608070c05090c0c010e1504030806030c06041707050301020f0f03130501050103060203040201020d030c1b0213060602010209030f060402030a02010302030a0b0a08011a0306010f05042a0207030303180c0b1305 93
    0x1006c0c55080100c1c150f040300e00860b0b5564011400702c0f0a0142da00c40ea10304a0780d132000100401d42510032003a800e40e45940b20b01c080c01c0142080030b82d000025481c001c50600b400b200e6440385000362b0040c4840e0451195010642c0c51640201c100070703450765030301d00c0a00091005550050450b500c1e0000100c1804500d40003588501d000380c0855415210500c81141290510040140082c0c003510a42c5c0300750f1a0382440104c96030004002900102c0300c150400100c4045a00480160f0350000d0f60381c1c0307d130074140701d8103003001000e00c06000c041c42d0a8020a8840305c03012402410164000001020742e5841da002c040305c0c40011742081c802c0341c1c42d080130314024400300103000d400906e0081c03d21240e1800042142c140c07001400d81c9154140f82c04184000b5111801c2c02000c00c510801b01c1e0301e09c40903210600403621009900411000386141030250880b00100070840010f41400c4148001c900602d40d42d4003140d09020000750344502c240030014058400d600103a070301030704005400b8506048104c41c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 10445411 1250 10444161 10444177
    0x90905010c03050f0f0a02090105070501021305010e010521040804120b01060306080102040501020c0603040204020403020d0803060103050711032b0f0e0c03010509060412030612060c020d0201021608070c05090c 92
    0x4020702c4d2621114801d4044040741ca504141c09100009a0315055031740151040c040d06041050604060f42d031410b00faa0401c0d0f81080386803200280401c201e6030310440c000300d892401e003030031450140949000e807a04a1002c40c06543c94000102047c10020f80d070b4100da00a061b03540a0700100c00c002d14040320249420b100c0c1100080c00c03c0004078100c6418801c94007241c00580003054604900000e0103c00d42000700181d900550911002016884101071041440d1040005540d6807411400140403a1005000c2808101c0c3c031420388c924042001080354448500b21040d0110810030207407400b000c0910080208020741050b0200215510035004040f1030b18044082d2459000c1d0001418200c0300c0882e0110314a9100d20041000301c1d40c80000319941a20914002c1150b5840b0004209008400107045400941d035101140c560707603042c803aa01640d84144001e5203041798207401006c042d40c0114002c9c00300600014a00304000125010384001c6c8070207044942140790003840055580c000440c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 10446661 1250 10445411 10445417
    0xb030703020a080309030c0114070201030b0607020a03050304091401030b0c0c1e030c0106080a05030a2a1101080a0501030c05010f05040509040c0e01060e060301030809061b0303060103110c060c0c07090905010c 92
    0x101f140702c0c41d0701030018034103a55100400c090074610f4680045024000e00862960001810800c1401507118424807001443c000c030700661b40c0f5440c00700b5140c211200c1c04a1001500b41c411f0042c400202e03c9a080c83e0000300c91038a0a40b07480420820303c0c1000d00e04d150040c4190711484820701145404400703822000210707030003040915039421041e9214940c400004260360000c22503600c6586c040c3c8105009801c5010303c0071640d01d582c0c16040710602400c202699103408404402c912507900c50110380d172203040a42c050000e94515520f901398800b060040381e060001c840855006a4445e03400ea81c018040241803102d98140f600300305010b80c202d800f8111000c3d48000000c21420f015600c2c5011510014161030b25503840c2d074441d072220760044201b42c4d60145007080900900c60340c4c01118001001410040c40c1d0340c1c2407501c0050115080c689005040203024000540300301400b00d0102e601c8800111501c1d130b00c80f09041c03054244041070300300310159480c0450140600078154006440071910751 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 10447911 1250 10446661 10446673
    0xf0606010908011b08071110021225030c02031201030f21050301050103020904020c0105040606050306010602010c0c0213180605100b0301080a14011e05061509060406030b030703020a08030903 84
    0xb0460909941c101c4198100d0f0842101035008079900c85d0011907808055440c08210500080c0d581c64100781c02c6109240b290354003c140f5030640708004e0036841c0c01c0072840c51500000480e00f0400e00e205810740b42228281951600203540b00b500900403540b69403115020001d444d0b8403441e1104210031251400d0340c149a12203541541d4444080c00381c40007540d540c41d074505603071a040044010390b01c01d032000c07504160280300e500802c1f8424001d03980140d01c61301001c01c4c201d041106061400c40140e004008680c14101d501d05084e0300300d107903042d07243e4041c3c17000081c0c006035042c2d48000e4015510711410b003002d00409002070140550019010380c0c2c814580c0000716580710300c07810705800700b8019058281c1041a080c40010b1a142d48504114602800416041042c0c4280004000402c00e1a0748041c0c0700c0040000d907142021100c4524011040b4041c244020f2001003003071030140b802110181740e41d07030401302c200d6035081005d200110b030700074040c2e200c079510b035641d0030348a03007054020700d02900ca0302c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 10449161 1250 10447911 10447919
    0x150c0206040b040803040203011508010b0102100c090b03060409020d08071104050c0a2706020c011218170d0203150f09060108070e01030e0304060207150908070608070e030f06060109 80
    0x42802402290000e00002e12a151030b200c1c07204552014000f00d9141d940c2c0c41c40c2c07014090311311810b400144144400059045070313200003e42085c2d000441030350f0f028506a80e038880981c0086040040d60740404440da1a9540d80340440d000300030501c4040d500200b0310000c5410051203a00400e4494410b413400030a0410610511043d09e03401da41802040303100303010440c0401d00c01c5a141c1101c400051190942403c0180c207044100a00d800140060304880c98803002c80d6040541c4404002e48110204504850010510810b80d420364008000ea6540032440d91000d0200080d1a120820340c403045544c4e04082e401c0310f2140c2c07585020a4090040224220624644860468410a41078503007101070360300d40e442204c2c0c18420f44d07011390505517511602588010100050300251285800800203181021600103480300c0880c9101c0411482403402d00010402141e00710440e00e042c01e2141c4aa1901c100603180401420b442c00d4045c0314030314408490304400540280260000e0b00c0307043c609522 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 10450411 1250 10449161 10449163
    0xd020319020f12060402070c0b030604060605030c0d020c030d060905010311060702090c03060307030c0308070302070b1912090b090a0212010e0715020c06070b09060601030e0a030f0516150c02 84
    0x10300c2c0002035611030144040340c408041120a1a40820f00620042c134029185d510302480452035040040d100001104200f46030030103102c0c00020344001d050141c00d618042d9007240b0036110380000c01c640f00740c010030450b58181003003040d43d00700305200b01c05020040c1c60b610a00010003091209444602404000041d282403090440c1c0081e50068a40203050b583e07024800415403000d44950703003602c25501c000000c108240c0058000d54418901036594941c41d0034001e1609045400600c04c01c0c00412640c16030392030034004000090302906192018070100202500200039020002e0040d94040b0104100da510215404588510807105042469040c006c1e950890f1402800c0c06d0195004c000103004480300003210002021a51046480114203440803981e580c114070000c03030359525880c2c140002900180070071944408280b03010004050b00715075040d6680345546015050040d07000088074042d2103030040315408032803400402a25107580c40c1500139020800030400000b40791082c1c01302c500d44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 10451661 1250 10450411 10450417
    0xd03020a0e09040209070e0f030a0809090106080f1b0f0a02032106010504030f02040b120a140a121101060302060f09040f0204050607170c010c03050f0601020609120a020109080d02031902 82
    0x18001d17212407560341d40c000301a034400c0c901c1c00c1c04a40c03100800a42c6540da50f801c0208014032803089541d683c842e800a400c1c0301210701d0603082081800b1402c0100030341d4040c0400306980c8186075034034258400c1d45240c828190f602c070b8221000541d0400080f94004260000000c041d600c44003401ca05200b08217031302840070540152490790001c0d80410040010881204a40c88501d0008100085108411001907590341a520355905203030013140c41030060001c401038003002c02c0c50080161010901983e5941487d140d40745848007030042400070b1000b8688258403030360203142d01803c1d041d40c030145010410351039000421810710490401500150094003802540e04455000e404142000344940d11b10156102405124820079010301020020a9090298403002100d80c0c03000111400d082c6081501d010000b881d407810340d4459014854403410009001443c160a0001e4940300e0030510000c9014003150203015080000116200b080000d480d4000c41c020011a0751480741c0c15080038146040e40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 10452911 1250 10451661 10451663
    0xc1c080601120f0603060506030609060106020d050a020c0a030302030d0609021606020a12050c0304060605030d090603110c01110408061305060f04030309050a0507150504050901260d03020a0e0904 86
    0x1428100204003154041d610785841d50700c9500c80414603524103c219811140035900540d0015203450510410742030038080c041c0c02540100107040c40c0c0d814580060355403201c1e80c01d00030070480c00041a000c000d20030b10000d03842c1040141050305540e500d0800070f5603034200000d03115900d0300d000d10000e00840d6510072030341d0190605103030800407042c980307c01000350002c8040c08180107079240850405001803140310301c2000c540d07030b80d00d0b220b08041c1080e200700c03181504403078001d03070084220f9030729182c0184140c4c0450b2054640803c1540c1c4056011440340524107120300c0660034109c02c070501102c41f4002d00140c6110004481180d41e03201d483c0c011521714030b42c020b0000e030170060100340700c6820610f2040d40300d402810041456415039441905d003480c10041500d140d04040014010070060303c0c8040180c411b1407504a003007900317140000300203e1042c0b24040541740d0003030061844008511008c0d5000c81042d090310021100200b0242c0a54031038143c03440020a21a062412444c4c24240caa004e1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 10454161 1250 10452911 10452917
    0x50a05010c0605090c030a050706030b0a0608061201020408030a020f060f010b0304121e02030717040506040b070f06020705071a0a050307031e06150e030a0b0c030703020405030706050c1c 82
    0x5281e1030b400010300c0040c0122800b405180a005c1d8152803c019000c299807141000f05030341c602e001401030483e8036184800740320b250071a804104c0c543c3d02001e400d42119085507190040441d030881240207201e1944064014000892040f540c0c580124881c05003001c00801e50304c5c0c80e0350704144815407000034002d80403643e4003480864041155500342c0a220003041c2044c0c0d140785103403507034041a05008910000160700c00103000302001b40d0710843c240e00303031400070381e080c103050803d40068020301443c0181480d000b00440d1010a1081c80c640e05420650003003421941e6042a084c2151141203a001c0c48020026503603041010403482c2c000c031004840d0036600c160454603046c038210060030a08805c2c40c501c0d066086411110300d5a0300c2060002c1000311075a04440700a04c4014004041c1203503001e03c40c0e000a05203a010821013401c082d8000e400f502c86940d00c1d41c1d03058095000f405182c03c40d913014800e020012851a4210004201c0c11140204031084c0c46a035012214203890a40415800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 10455411 1250 10454161 10454177
    0xe12061e1302090c0c0703050709061403010603020109090f090605040f0b0106020a05030301090c0507050f0706030606170403030b06070c0609050405060f0d0305030c0d020310090b060403050309090a020408060a090507050a0501 99
    0x10406000504110742000050398241d40e1fa2313486061034403405402c86040346a84a2040041e141c584400501302e0700203030004d10219186400281c200042c40c4200e0f481c0d1525064840481d14107a1710104101e640510100720504040c240308501c030104400854182c0e03003803400420a5400051030440031395000e402507196a08154404004d0b0541d10b07200c030140503050085c0000203106000071003000d03504000810040c2d1030300c440102628150360080d018000c42d4030001d401d4031034402c005640030781c044c100071580d94880008030b04a44550b42014000644c0c0400c045821603100c4140c0003101c108a0301404031b40c8605c410000e8108030001c10750380c0042c40a0342280003038020741c055540300b490240240c8c00c00c4501000c0d00140c0c0c4c4120350300164258020800e2114407814072481032a09400d55880f411309082d0b550309035483c4116600948603504050018118035038640417580503110280a42e845810f003d0b14000252041d84012950760150131404100c50a0401400b01180c005a54100c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 10456661 1250 10455411 10455421
    0x40306020a05040510030e06100602030403062406020607020601060e030c0f0126090706090303020601120c09020f0a090801020a0e04050a0b030703050607030c08070509010e12061e130209 82
    0x4001e5005a0508051103418440040d0326070b68114030070403111032610041b41000114416606008000340101240940140140b000503400001d480641c1d600600025200d01142d500261241c4c04052400c80015040c1000c1000d9502048240c0103041d2602141e8260f40c90342800c1c2e903154490a20703140c0561221b006401c080c81c0a5651680c440010306000c000c8003072550802c043d18900040e65410781040200307200d2028000c000b0f24001f0320075854901c2883c1d00b550b800075100c01040c8900c21500181c10148403d0007a801c072041c008040c140000c55032406031038003140540d04100c0d141c0c004030300c81c0d00b000030310500107000b250000d04850307943c1110780c000441004001c0002408805180b6a00c55034102a52020400a4007450244000709101c0c9081078000b8166031001040b00100f0150f9814019182d412a00390380340071009007820407089815002141d11205881e203582414843d12081c0300c1000900050240013662451b074114003952088001314403c51851002904840c01c2c1c0c4c0011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 10457911 1250 10456661 10456673
    0x7020409030306050901080102070c080c090412020f03040e0106021606050a050a0905030a03050403022b03050c03070b070801050f01080103020307050d0f1205030a0c0e0d0605190504060209180c0403 87
    0xc120340c440d003000100303240c48102107030004400740c0018010f6940003c0071001d114081744d4031001032845030020810840c062000c40c5101e58094002032118451360b1000311254020321505180c0b20203d801c880d11141e540f41c282d46004401c4c031600d0094001d000141e002c0c80f003c19006000d59500d0344495103464050082111150b008803000d8081148500c004115990140055420b2a00070f5440544440c214010820400070401e032020100085045116510700811030084900b900b50030315035140e18010300c40318114810b41c400188816020010003420b103400901d01810307110103540c40e4222a10b40300047d100c540d0280000f07541503014040c208150710f850f0b40c401903514850b44412004045c01d075a940d0003159107002c0040401c01c04002c001100d4464424803420007643c0c03030600d503144991408141108000032014125540f103400140a12000c84d4440886411401e0304212620745414407500030340240101e00d200d00c01c1621036078541a480342946005110102c0d14034542032a541d203038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 10459161 1250 10457911 10457921
    0x12010b030906041203021606021e0313060903140a021506030304031a07020312090303040b0f0103110f0103061715010b0f0a05090d0b0a1401060206070c1b050a180b04060506070204 79
    0x280c42010303020441f40d820742d401600f100c01d4681c8902030150300c42081c000c900c01003c0d1280e8002041e40018820842036010407000442c2894001c140001c1003c00b50400300d84040c0854a05242507000286503c04c40754006804003090340340c10748a11094840074201a01e80c030880c03001812a582802c0482802c26610251540182550046900d01a1002c42001c07060108880a003a40d0b0804800c100900c2080304805502c201802c201c100c0941c115951641e5140c0c500300c0e454040e80301d111104103030380d002c6e6110101800507120051640d003c0441026900c0a0b5118210100c89019000140c1260110b080e64203420032189030506241c0d6001702200c00b50007110100780c0c024007001d402c0e008518407100090040582d04000b10340f42c1161140500310100680c0b0040842d03010b00204070809901c5600c00482e941d00c814207481a504041903006540c9040d0401da03405a000030300041e0040c442e80102024410303821050100f001000300f0001140c80038810b01da0008410002e20f8014036080c0c0c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 10460411 1250 10459161 10459193
    0x15050a030b031606051b010b090109050612060a060504110702010e0d08221e0503060105011101060306060602010207051c050f030414010603060605030f0106050a0e04170f12010b03090604 82
    0x1102d0000c01c01040f14145a03000d9408003011401c00140d0220846003124203001803aa00d5000f40001c0e243c079408500c1400701481103a40c4a40d640001c9411642c510307984220502d002c01c11034240341401c106a81c0104624450a4811843d100c000d94045242805445445030143c49030310010f6a0321040c011604040102110b5410040025064641040c03188440f1200e000300038950050500d01b51403002d04003541520081c0114500402a954000072800e045d11420b1900000200c4c0c148441c2e800351020f500000c019a05281d80454820340c15400340c2055801842101d044094280c1d8000c903c80d11035a1034800588108892052560000000d44d0014440d03100650f0484082d840d0070700315000342e08200c900341e4607600c040001c2c0c07a04010f000c10300c903130041c0200700b0549440001102c01c0310a02c980b10b594412040002c040c0205840020321a11400c043c0c01e9440701d02821003040b95025400301d1090081110010401070905402da0384a01001c000606c400c0e01c2e02d07260004060b00c9002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 10461661 1250 10460411 10460413
    0x2060a03020c030d0504060911030105090c130608060c03040b010e0f04030305040f05011409010e0102121306020405060a0908100207050d18052d01030504020a0603020702130e0c040615050a030b03 86
    0x11029200d50941d100c5e191045000b03180010b0308012074036004004008003010030340310341e040c01e06208841c00d01050035081d03031108880940303803000d088441001400d21035004060074005d25040281d1032418000440c4901d00ca11040030340c0d43c0c3c9688502d481d9000c00d4401c1040425803000060009000754041d68000b0b0003403100c100107611035540c2500755070054007210901c0c010780c428031610300802d004039021410007400170750806852100004460600411240342074881c42040000d22007a03074101c3d0090700e4080c00c43c0da80c81000650207400c46129106124051007841a00e4141d001180b098482a80d030000142604003480318044030940304021601d0a201e510800020345980d400010741500c0070038041404150324501c849056a00341d125a803410300d400d00e010040141d4440e50b0481c00d44010741401a00c84032240080b50065a0704d82403e0780451901c00c2041c0c0040000507510350390324040b902484015201e01000c281d1020000c6c2e00c1c00800d00620480011502a802890800c50058 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 10462911 1250 10461661 10461667
    0x50f040e060712060e13121b0201050d060f080a110109180e01060e07030c02070806070203041208040803030a0207060b0d2004020d09030314070503060607080901030902030a03020d020c01080402060a03020c03 91
    0x203040206800b500d40380305103e11010a070701048036100302c01c0d4800b50345040801b0000238500c0608512035400c1402410000005219441c445165008502034240049180f50841d2541170441d40c0354032084064074000d00d144203100b219841180b0b5a030965140c1c0d2650ba00d490b00c201080000b90180d02d031084074654139004080b5005122040b0306106400594000c0782454420501034102a019040b4400740d800813410051040d8000049078110380c01c41d03c046503030000300d0811111a0055420070f800c01e0000100b070102101c0c4c15000340c9202805144200029070300c50003040503804034088001c112082402519180080d040b6241410b200064405807a1003241000300084458540c0c00300c020a0380c0300c40c0001c200c00f020845942c040b000d42070292079410a4000581d00d4080c480300103211a1380040d40c2203090344a9000340c135010390f015048842030003803480e01079250b2004600150040c0304082110003198481c1d0070443c05580c02070150380c58124002000c502035403101101e43d003640710070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 10464161 1250 10462911 10462919
    0x2031204020d140706120e0304140105070501050c09120c09070f1106040812100b03040807030c050303070f11010c0507020603090106030b04061401091103060d240501050f040e06071206 81
    0x1100e442c0c104030001c0f101410b030340f40c201a03010b030442401c0075204503a01d00e083c100e600c0003840001154140d44e11a0104009540500012242d85c0f04140300108036500707140901c203868580d64003400031403c0403035030103a948803222900c0742c0d40c50048182640c0074000704003151203907001d061512074a4904d4541880c074000c82d50704445c030b00601503c0c03c580b040400590580e02003000d2000c29000744c2c2c3e010f581c280e44c0d484c0003003e0140d4000030b000600031140000341602018010714000110fa0740c00400c0c0e903220310741500701070203010344149480d004c94110a001c001c0824188105000500b880c1c403107604245044d000c1c4416500020310a00040d940c1c0c0c075010021881035141e0301c4c0b107284038080206801000c04188521020181d100c1034410741049140d00c141c448800a0f00c1e07101800383e441030030700d50f4181031071011050300841e05800c8101011345207070707e0075a580000e416a0415030b02e810b0b1071300080041c04200c42c142540314402e9008100442e131118814000014030524440c0045442611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 10465411 1250 10464161 10464173
    0x106080d020705130b01120b0d0f0f02010207080d0504180f02130603060501170103020409020d06020a0504030c0807060503010b030705070501110301060e120c0d03050d05070201090213020a02031204020d 89
    0x400c0c00d000241c1c1c000c9030b040006203402d01c0e034a00b90010b1081d06110a007070460010300403825521412000f03507218508081c198840181c0441d6003600406481440311050800180740800d01c88207a005008000000c90aa00005062001d441155032400d2034a0701e40b1800364070080081c414501d4045d10350f4021010001140041d040b20340c40c02801d555810318054014044074105c3c2c0c003580c188400391b480e414140c1501d03c0306504685d016500800d48107580d1000a032422514940100700303e10214800380007941c401c029005803482100740c0c4020355158140c0a030740d808903100d0b071313800214100014007103400500003440c0c004207107003403072814208181d40d600e00b07460901d0941d56480e8804001044040e40c080e01520086006543e10350703130758420400c0561546484541d0500480d003e0600380c0806200d00c045489607207185d84100000d0901c01780081c042d00e010380c0c00340d101e0701001140a0560740c0710f20071a0182015070b00110303d4540b00500c21035100718020010b0f87e0001804002c0008144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 10466661 1250 10465411 10465423
    0x30203010606020d1706060a030e030d05070801090f02030405030304080a0207030c09050f0601050a020a02060901050f030f070e010525030e1906080c0906030406020702060403080c070303020d030c020618010608 92
    0x15603005403513082c0008500604030b0f8000d260444000302e080051240580321001102c0440f545403030003003082881103440c1c600d9441100890100e040c036050410850303940c01004541070320310100302840101c0142d05000140c0c001a41c014016410400c0454006103294000786030001c81030060701c0202e03540762540341c1e290b06698003108100303487d82c082082010a095040d90b014109003011414210a10402560390560000090240d01d0010b0342e810306a003c1d4040d034103e21202070005030780e27107030000c1805034880d0706541180118464694a203103e60140040d5107000c100d400014200d107050000e07280f00301d41d03600d90603001d0105030200700201386c4801240079484200c0b14600c0004524180004044030001010300301d482034280f0290101d80d49102c1201e4000303800001c05600d0f518540002f400c14480c5a1004002d5070700000d40384020075012802c0b07421217000b60266154031a003a881038080c3d42c00c0200f28001600818001064017010784032440440404038000101c481c1c07504119841c2c25 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 10467911 1250 10466661 10466669
    0xf0b0a02030603010c110c011202040906120212010908070b0a0219020a020a080705030d1d0301020406020f0601090b0604060804050a020a0816090c020607120b06040b0d050a0504020310020a0302040302030106 91
    0x54000080140b0b81c1002d00074102c006001c3d16010595040d0440c60f41d403200d121110389070410030720b60702d03500740d181d06a01614003a0128940030040c003a51100714603807410b1922030483c0621000321065150150602c105c040d2179402a10182c903005840e51104905071000f402034003144d900340411a60008011040e01409900c0c1e0000e004022050040203150701186d801040a40d128038014001038802060808064100c1d08005030000440307401200045041c8404503010f61000c60009085a8006103c0405c20108070a5030203698880344044103841071101401e0b00f0480c10002008407508c284800356001d802070041d208003100582c002181800d85500100b2030344d001c6170b00c00000000d5410340c1c0f0028400994200f102d68144c400280d15100010040c00512500800080b0107224980000c1c2265000030140c540d243e0b1a0801c0c404160040720824000c03902d02400510503071360b2031080c140034a4004008242c160052082500a51720403416074040640038440000161401d004030400740c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 10469161 1250 10467911 10467931
    0xc0302120a0c0605060a050310020a09050d03020106061b030c03050309010b0405010b03070306050102010e100b0a0b03090706080c070b0c0f0c010f02030105031203130213021b010603030f020d08010504090f0b 91
    0x4200b81c140ba10603610050840d602c42c0c1d520840404c583d42d000034007040010308200001d42c480003041d0054418074903507070090350030901c001907080070144d066104400741c0c0c1850301e03011076034000400c804656103c02180140407614408a80340403a009001941d030042c0104008507014048070049001c4d140287e010075103c400106c103001c00c00d905406610081c003c284000c100d444016071001c0c3d5240d007640540d500f510350350003c2c0e05603a12034001000180c800d0076040c03656800d04081c455582c404034400d40000880d90b80101d200c0d41c805000300d401c500e0700000510701c103840e000d81e102e07219401001700c0301c1c00d0743c820002c030720a46000707005400031413454160040c2c9940c0b500081c14140700b4002d2040905039410020050740c10741c40e001081ea040d4054070507460644150342030314003c1c07041d20240c1c056022307400c1e0004244401504800243c0307110340d40d080d0b64503000c0c20069903120b030780710402408180c0450042c003c50401c0da2005042c940076610016241d005c60300c0b40007841100340c800c0c23003031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 10470411 1250 10469161 10469177
    0x120a0302071505040e060a030f0804090614011707090801060609030204110412060c020c040203041b080d0905010c08040b030f04060b091501030e0703060c0c150506030703030c0302120a 81
    0x24980c0500c107480041c200b020314104181054000100b091040d4002c850b04000d1850204000da2552604c51000d50343c8504500d280d507440c0d08001c00c050700305108030440300b410420046003402d01d40d078008d05c2204060712001c1e01c1c224640d10210003507000030003420401c0709440000034640b00c00d0040f00010a082e0715048540d40c01c6005100c00d90790f9420302400b14901c108020014413580c9019000002e4009500180c0400300304d03002c9043c10b0103682c00d254010300110a0005024003405018560000000040b003010340c0c40009540f544410340303454021034100c4508210550003080401c0d03005209140380c915017501c0384d030955a035410540b00110301484000403c42002000e2003042c154031004c440c4559a480d18a102c00c804400720000300b41016110049032031060001c00c801c501940d4411800d011000c4241b50040c09002009010390781c0b4400c813001403a04940d40d00c64240965005030141180d1429034130155141c0207800c100b201107129400c02414010803a8000d44003036025035a80000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 10471661 1250 10470411 10470413
    0x102010b0a120c08060106090e0702030d05010b0a020d02010b060d090c051509100e030a230105010803190810060f0903050607020303150405090601030b0604020403020306010902091008070824120a 86
    0x805003d0741d4010800d203034040e50060001603003205600c000c81380700140960403940d401200b20306600030080300c0081e080c281000421040c0030080503003100580e0307500b00d0f0070901c5000b004a090703448a0707400d141c01c55410400d00104004d2038001050040c040e55104c51003640e03c20114030030007000d4006040c110000f08162000d45440d00501100d51984d1810310001003140f0006600c940000c6001070080d841c5103030381c003a181e500d82a03940d0342414810003009550f0356012025200d5002c05c3c01c4442007409440300800560203182028080d070b0000400b40c610a00b010020f685888083d0905401d000340403170000b000442c100041407003003d655014607180d08003c030ba1002c415002c0380302e103807040782450200103141e0030010790641103d80000701c44d06940c5031b4602180003440b440e000070390076018650000c02c100388590020310800c4016115040d0707040a43c5d0b02100c00110513074510740040ca001010500c1070500c8000388000b0344083c201d00800b02407040000d16041e009102012440c1c10a4070a50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 10472911 1250 10471661 10471673
    0x1111b01030605030708060a0203130602160b0601090b070f020d0807060e0601090203040803190f02070605060a0e040302030703030906060f0e0402031219030e15040b04050709020901050313020102010b0a12 90
    0x4004083c140c00608034607051002c1b10391103000080c030f02c1b80e41a50100c00981442080034403120040d4100c3c03000c40d51001180c1c02209552404002940d01e0034030900400c4055210b210220b045401140040c6e040c01c806507600d868034481108280d0340207014010345008244c0d00c0e402410301e05d00c2880001220340c0d00000103820044164000f00c0f040d8814030400c0089a20724040340c0c6e0250107141d01c644001444140100201a080c10b000300e4035101141300810049280e0106e40905401c440c01d49246960b1814402002e80c22280107005030070a02211000a000344c03c03012006200740000b01d1010b071148101008104254030107144d4a085000344001c2d400c1c10310400c0602c08002c50114640a107028004555515000d112010160790b0b01c2d94064802051103442d032031000382c404802850a0074208139a4040c401d4506940d94040c0000c001007251940c800c4840010068540b1811039032141072030100302100345c5d0240d05554030b400018002e942c4110480c4060a841103000c062007280342892 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 10474161 1250 10472911 10472921
    0xf0f0409050901180320010203160201050603030f072d0605011d060307060507080c1b010914030a060203060d0501050a020d06060806030c040c11010507170a0911040b01111b0103 78
    0xc042c181d142c010001c084c0c0c8140c0800940494040c1451b4a01c903420040e6a50544003070b038090649544040300b03101c442c856481841401c00711980c001d0019480d03c80405450788510245021030403400c200ca0070015031039980000e0183d035442c501c501013080e0710281706030102c00e5600803a400c641c5c42c00107100580141c2992561641c000312502004e26201000c83d076558003074042d0805000c800300340b41c0204085802281e40c003c204105a8044c200d500e40c0703a0754001c44200441380481c21021000c18081102441481400703002070043c10709400d00d4645400070742c4081e0015822280912003500450b200740522401031041c81c40060f9510f1100c2c0c0302c00211100c68204038100480c41c020701134140d4000842c0301d2000421200003a0041c6d070040140d03000c60f1002036104881d42494100702405400904295a42044180c00f402c0c603981c1a5407941258401080204116003803180c414a40c100b9030f2002c1d903002c0d81810010200446c4038402454a08480110345154411010103082e55906000d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 10475411 1250 10474161 10474171
    0x7050109020a0e040b072304080a020f010c0507050d0f020306070206010e1506030105120c09040b04050d030209030307030e03160b041503090f06020901020703020d030804060b0604080717030f0f040905 88
    0xf0045403e05541e402c40314000074103850b0822140f200501e141c0d012400c0c083e92007001a00364642d495648460440e101d040c5041b040c0d1050310004401c0d4669400b501d46c58100b1503122001d000350a081408002d0b000f0004242591015040c151000040e00e0801405001e00000c0c3c009141e01d40c58103a0300140c031701000380420155400c140707400502d519880140c90649008460070b411085948051928188000000580c4869004207010900000001c4103004da4010802c1c0d80c114030020300240c040e8458420803940540c0200a1440807030b10031490006d01940080c15a506440031000c0e044071030b00a50840b68030140001010015007280c7e2480e1f4001d1402c90800b4810802c40782c682100c1d88101507005001f194000030700d14000d070310900c140c80107185d00034100c00c6500d00909000f40028801c0f038044030001d25010308201d89291800c00e590451b48842d0003402210f04241c10b4040301b441d009a28015803000340000342c1d51030340f02000751002d052129032041d02c5902c0c040b040030644102401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 10476661 1250 10475411 10475429
    0x10c02010606020a0b0c09031903260402010507050709050a0606020c0907020a0b0a060b07030c06051506030c0708090604151407110402070213050906060117060a090b03030f07050109020a 82
    0x810a40e5000b04200b4090b036017100801034a40c4da1400c0d10030082c0704000d070391541030040415110540100c0070000d1030f12406076940c10700307501e08da600100340302c055a0f007020313038800803000010015071185004244d4644100103032800281e80f940c8140c01d44038191103807581d80d500c980040c031856504201d01c01c44d036081145c82c0007142c00d042001070340b00d1400b07140c0030b03001d030307810f8000507070b40c42003a42100c5c004210f0240203581e200401d080080c03140c2d089040c1240c84c1402c0070041003460b03c1c140024140104020141c0345541c4821400e007195500510341120041d03014403404449a40303103000f4000404401440c500300f0203c04d88014549580085400c680c0c2e00306010b081e0100b000c03950845000c040c01d03100181c1e100428000121013041d0031410955403410841040154800414840c2c0151002e80b1101c0c2e00b01d4511101011254084680f250041480801001500a1508a6442001d020b02070b20b152100b2801001001c2d0f100b82c1c2d0551350780c5c3d12220340d481182420a5100004c0203204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 10477911 1250 10476661 10476671
    0x70801081002030f0109021608070614091605090a06050a08030310080304060c0f020a1503090c0605040305030d0203180607080103050d050702031b03011104090501050a0506070c0611030403060507050c010c0201 92
    0x10303910b45490310706004548150703501080c7da081608c0c0c10260041001d400c03542c1a5120111440c04101803c07800d1b009202a08251011400da40000500d04a60b2000b1107507860201d801c103000e1041111000b4a2045200e803110000241c0780c44082070b02d4054042c8001459032440d100580d03001410f03882d0301c070392902e50040008102d526030150030344100c1c60384100b604c2c10301e20ba40d0000070b80b10030441d00140411a200030310003100702d0701544208180b6202d80300e6200c82c180c3c8c2d080d040d69180110712000d80203070010085a00c1520082e030080d40d02c43c01c2648d50340c070032428010340c0c6803603d40100c03080004940b00030018001e00c50100901c25aa1105103092480c10140391b0100e0f032580c00003030750155541080928200156001e4104c0048204550410394a8590759034040002e480203101302070040b2460b801c003040b541090b404503400d45400040d04c1444a142180446213a5004440d00d030341400180404400108507000346405800c842e6541c40d00c51030f0b04c6804a0840310900e1070001568506 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 10479161 1250 10477911 10477921
    0x7090b030604120e04021201080102030a0e010b010e13020c07170114040804090203040309080f010606080609040b18100c08010602010516140a020319021518030909070c020907080108100203 83
    0x30900000d1034a51904d19102d18401c800324003c3d00075a545020368200a000100d11000154061031040b060250180000d20441740400e080b11807041e005400596503684100e0a400c0910411618883d4481c00501d401032111100d41042c080d40c00607441e03a2280081d080900c0c3d824000e401d402600c00c040e840c5141001e590351201441035200703101c60707140c003c80024145405240400c00070481c03030b41a141031441d10070010340249201e020340c001003690078000c207610342000004c6030b100d40c0e401885c0700566210030300c8170802406001c20f24117281c03091032004810410070780a2000304d11a1515211040d50412101a09442c0010103605040c0111000703024807990006c000c1c202c0202131010140d41d001c000808a0441c41030b1401501c0000542c080300c2d0b400350b1b0001e602103070074a0071025510b1030b450b60720350104191f03007146250285a009101c1c03070300d0520b01103d085800030000c0c1000441805a0382c04641400e0003100c117580800d20601c0100322010007030140340911501c01d9021845c40c984 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 10480411 1250 10479161 10479173
    0x405010f0f090e0c0f060c0609060709080610050d140a0602040510020102030615030907030f080703030c18210b090a0201080105030111031305031201090c090b07030f030f0209060a0207090b030604 86
    0x22000d1107100c0d1708450076040003616560103d030b040224180640300d2500d8075003083c69442c2020b0b16544009215003000207168100400e21500a0740c0c2007094040c1b0625220411054514030901615121040e15407903915030420050000c00f54460200035031594541410040940e420310355000a40e40100200320700341e602c100501d0242d00007441d05131744076128441d03d5443c4c1162504003d050540165002050280c07410140200c140b00765014842015002022250308160071007603104410120420700041c0c0c0d400d40c82c4180342ca2041740110250009880b048145e13074042e52020650b4001c01c4000040d945c3c070410b001c0c05003005038000c0c058440032808032503a0b031200500404200c2c84034000d190400a091003141c0010840c01e4044200d0b58407440c03a10020b001c100124408100240710015008a222042c3c1c0c10854042d00d64032002a1990801e0300a0124125605103040d030801058803a0703a0303124003030b1001c485164001c02214ac00d01c158481180c0c80300f0203103417180e8440d100300000641 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 10481661 1250 10480411 10480423
    0xc011103030720010c02100614030a12030f0c031401140d020904060609050c13081504060c0c0203010e100612050616020a0602120609070306080d030b06090405010f0f090e 75
    0x10b01482c082c03441207800c1e40e00100c045181c1052283c0303942042e151000300c41d4009132815030130f07001d641c08000740303139640d2880c100c0804007842487c2c2503001860b224010a440081c41109080d150401046408503950405c04a850700440603001c0380e61603010780d28141810403010b01400c0340741c08134021003c487c1300180381c030032000e000244541d201c200000c040180603044200140048102840039060014a00e0083d0300500035000310b0b045030802c001200040010027122517502a01d001400703403201d40390000906902c0203150f0520170320a088400607102417280d0207642d000c1038041c20700103030300c85c00385803d4a0680d80b250b410000316000350381c04a400400c1c030ba6049520310590607200502e45000748c1c20008868405011284042807159820001200481c800d2404491414039681c40100640854200e4000c20407541d00041d10420303010700a91091007030b080001c0501d420003462070005016500246c000e091014820710041042aa5000c0c00d81c1c054405080c007845490103400406a82e01d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 10482911 1250 10481661 10481671
    0x6051b010c0e12070503030a0305090d170a0c020c030601060906090503070315090302070314010b090a020703020a2003010e030c060603030703050a030b0a170c030c040603020a03020f0301060810050103050c01110303 94
    0x1164901148039403a100300144e01c01000090240d0b903d4294042002e03000b0312003107800b1415405040060302d6010710030300c109006009a0081a40c298940131f140000606911100d401503100700c0610203a00d582c20014140200b80c6d0340d50300c0c410142004001002d0301480e900540c042d0380030450070f1000404202002c010000037940c0050340c12128181203252000b00c0d40f01821020000300d03d03910200c01904000418841511098125152002c08c402203200320700014005070041d80242d400503007a1000084600390303c10300d1401510240000031308451002011600307035480051030380c000030000d104c0250308c01c000700d01641c10600540c80140c018410190880205640c400400c034040c0c0d00d0000501c09404e0303e01d00700b00790140c00e081c00795030b82843c510214030912800807070170007500d040e024074400d403640501031051803032a59080c0036a201c6505030b410b81c1552102d0012800110401902c001c4c1d041c00b0502050329451810700c82d081440b100600781c100807181a40042c0410700004580d041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 10484161 1250 10482911 10482919
    0x80402040504030504050915011412130305040503100f110712030c0302190302090102010b06030112031d030a0f0308010b030f070c110306100302040506030a0302060103120c02090106051b010c0e 85
    0x70b66a103283c11202d9110f150402584125071406200c94008010f1504030002008c0c1c1f540340c96200d038441c2103415405218a581290444c440025101c0343c511141030003001c1c82401d00c5410980c8610009040002e40c0102c160115580d00807c011000c41d4000c0c080001c1090400a1030440551103983c2d50165800014080c140c8510104001302d1080e4103c4402d100500d1007042009003401008000c0d500a0001c54015030074007048001500c1c10504490480301c0c071040098100c00c00c0e90707080d203200c1c811a01203000350510580018503a1010700100042d00e12464940b00300307040da450082c04144044e04005038202040c400c100c6e158080c00800c50b002249801c100080000c289013101d4200c002c0006203806009400601c110749000d1703003400040e079100700d80038045a5545414555070701080700000d001688100b00410204100041d1074002c680107103030103400c1d201141c0114105480030b922000010308006400a4206016249000201c2d100e000074440141c05e00c50007408031100c04203051003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 10485411 1250 10484161 10484171
    0x30c04060510050a09080a0b04030f0806010207120201020114040503040810050709050f061306020c030709090b22080403080307121415060c010e0109060e070305060703020d020f1204020301061508040204 89
    0x84d05005618060007020420211035100d2000d1a00400100f000da030201c010641003a0030f45900350007007245501c9090b060380244800d5240100488944070b500030241e041d5540c9003c802044a406914940b01e039014000850b611480d0520003403030101c2403140b144000e89080140404070f907000c00c8031300448000702c44001100554100160b0280b15104000d1800f00380d0b5140001c07101c0d00480c1164507920100c040c0c550b15036a80078018195030304074a00801d510481400508040f0041030148048280c200342414201a1075071844410750080c4c0003034817800404820440181d40c000122500d48a00d004244511130300f1550100021038054a50410070707809074400c51190315a101075680a46d10b01002b48064458003264600809440c1419541d15003000070907400c0791000201142100e5020009100540c0c0c3e05008a00070341003400c40504e141e4080000740040156000030700403004240003090f0682c00c19204041c21030398698001035800c3e02052858601c25044918154015015a00415 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 10486661 1250 10485411 10485427
    0x30d020a08370c02090105010e0d06020a03110a050702030106062609010b0d060501031a100e0603100606020c01030e06010605041a130303080a0507050f04050609030106051e030c0406051005 83
    0x3645107900304809944541c4102d2604032550b00030410baa107107000366900d004d00d980b5a0b004549850a41030b030141c00c00050a48400085d44a9000f010040140d24000954015001d80c0b0640d41e0300003441040010320100c0d81c401589801e100e8500207200b103003004040d03101c0101d4520341e82c0e1080301020440402c40310000700005030a4001c01b514070740042881c2401c2c0350398070340200106000c0c0415105d4a45a035440c20b0745208111031107000d0350001c2c0d1250f40c010b2401c404600c004c01c000300819090f0040b01c07890000000503000c4c5c03902034030b400e4001e4690102c2000c001003c507040c01d01515a1940720070010000580c000d0221130540702ca07442d031440d603e0000300200006108540c4001c01e088100310001050543c809a034074080d00c0c083d8810700050b210810304071003a00a10384402c404110401c0100074925000e4010b0500113800303400800d4090342c440020b411141071000d88101802c8031a9007054502d01800140303000300c400c076030410085080401081610740b107002042c0c00e0040006c1c17014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 10487911 1250 10486661 10486717
    0xf060507061103090307060b040e0c09090304091a040506030109030815010e090106050712020303161b140708070b04080a0201030902060c070308070308011d0f0703020408060103060b030d020a08 85
    0x41d04160b110414a41d00c0c01d1122429a60f0303840900152105032910300031803840d2405005901080d13030840020b1801c56251401c100c0d90b0312000e000c004141c4010800040e4000d0f03c1d009010b5588010441c0c4852070041c0c2003440705848004001c00c0c41f0b645004807000000e500041016000a100e41c002c00203804540011703103881e0404104240e008100b81d00004415500c00001c04541d0300c1240c0102c0d40740000d5200740d950340825107940c2d00e805400300610100e58400e2140c10b600644a110030241c0d0388250300c0d0b0b483e03040f80082031120710b5000341006001d071280030402800200f10210803146010302c0c0c00d01c1c203030721640000301c02410035844401c440151740d16642980d45c062402c00995800c0e030741d81d1400c081d40354071a0504402042070400002540c00b4800600e0070141302090700035030103503260b0400d9400840024210800c0c5a800c0c8000b00787c082e810040d4038040d5101d09000250803842900f094941001c00c0c0c01c82c01190b04c42c80e076000000f1098003e41e1260309011120980003003486aa01e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 10489161 1250 10487911 10487921
    0xb06030106170601050f1e04020f070813080f0a0c09020309120301090209040609020301030203060703090521090a0807081f0f05040303050f010504020c03180f0306070206011e0f06050706 82
    0xb00484421441400001c6000442d41034101c40046034441040a0b0001c103018404540c101c2c01315408040c0000040c03541015001022080700182c80d40d4039161903907490b40d0f26074102c035030f2031409907010340030500c03050380c0800c1062442850480200b002585030740e102002c0801602802c4075454001c8045007561100b0024032100e000d0708000c01d6120b44e111040302e0000e42140f03107014880c1e4100500080c015409208690503a500a0080c21069039042da058028251502044400c0d204110b03c4504140e01c0e018800c207204012910309a030341124404200030039941da000b2074010342001008000640c000070740c40c030003004808400c40e40c0445400c0550024104c0c00c0840c891142404104420154540d0100c0c6c49064125564602139803203205010480c05210401da440303034000c00421120b07086580c4868111800203102032584040c000c08641414006c0d510000540d024500600602840b0b281454842609070480045240783c116070301040c514910468051120000e116000d10074a9085 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 10490411 1250 10489161 10489169
    0x906130e070509040b070e060a0c0b04020d020a06030204050f03010b0a030b100801140603160e010b07150204030303050405071203050301030201050703020f010903020f010c14030a0509070801090501050402010f05030906040b06030106 102
    0x60300c083e40fa250400801001085030010b000030084084014a0f1420400341c403503024140c0e071201c940203021307500c807000e04401500c1030340d005085810f408016a26081a5005001c469070050703103903441c01c0180079040d42d41418152103a410806005480c1e12002c2c5070b6070490f40c00103c000c413141c032810043d0740d10501070b820008907035007020b0001c1c5203a150361030242e0242c0340c16011030b10300c01c0b002960203003080201d008002200580000402c020300901000e424000e0262540520180c40c1075540c40c102c1e0311550040300031984603810072003404403d1000300010089a03624140c11501560010043d02c01400000d0500c4400b080c01e8043c14402c12107009031600940c000c004402060030060340d9400200418890b946c20455003140b054400e002900c1d081000001d442d0640c1c40b83c19030800038010050045126210750711001808407401d004541c0c0f0103005000026240c207150000500d40c210002d1820184a4100248a00b2000000350958429085482d21445e80c854000003800f4180f2544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 10491661 1250 10490411 10490419
    0x607020f0f1c03020a1a0f0105060c190b01030308010503150601050d020c0105041a0106030605010207050d0201050c03120a060b040315050702010e0a06050a050105030a0503040605030703060f0803090306060906130e0705 96
    0x9100b04040c0c0000f003000703c403030044203000341100300240328814000044802c0c1011a00100040200d81882c42c043c0200c20301d905c041d42c0c08070001d68241c65070710013060425515030188000400906401a21181c0902010b8010f01000200c000c15520389090181c13a041c10803000159903903000c400e6a040d2442c4600701e00c0244454185814600b82c0075080c840ba49035920041700000503005c2c028441c440c02c440040c3c001d8480107240c8801c00c41075440c00340099050000800040b066031100f40000c040041d00e0541c0a0f00e18144955840100d0301150441d14080c9000c202c140042225101800e04200b0311040c04201580c80e454100d026200c9120500014441e500305a400c224140d0052882103a8002d8100400d03a6100b04040e6114030181c4081c0558104000500405104030015a804002402c002c1090f0303590f060084842c0480d540501d160340c2001c5040c9240d0b10301030000c160810310841e03044e441c505003d00012081c8070b4071340da11030310555161841e21907035909000d85130040100070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 10492911 1250 10491661 10491709
    0x17030c0d09030e040c050c1506060f0307050d06050102030a14031906090b0102060609010e0112030201060803070f05010f09080405220203070203040806010e0106050304120216080313050607020f0f 86
    0xc0b03000b50551481820f4284114100710a8081c0c15124500b55002e45100800600c0941e481114000070b05401500300c0c3d0300504100580d50305101010011400b554459540d2680d07114215030600442c1d900b0340149045420130400c943e80103903c06201c860060010556a5698442030300600a4402c881010266141054030001c1e072244144c1c00000d03928401c0e029580d4076135032281040000e100901540c0180c6103244018040203102c0c0620302d030254421f00002a09540f03902c0342c14910b4100f003000711200020400c0640c10001c085c01082d112007200301e0f0901c4a400c8a41c0d0710300c0c00340198007901d400788407800801600c000c0c125081050410720306200b15a24248034000946a1384140500c01c040d1141d08000580404100f28040c1214050741d07030281181c4441d51640d40c40150103a0700301c1184900e0603d00982d02d000910307003004002031002550b88524010b010000c4203107a81c006807084509011041c0541c5030150702a5680398202c503000c900c40c2540e070000e003d030501000300c500e10030960 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 10494161 1250 10492911 10492913
    0xe091903020714041e05101706070f0e0919020706091a06030601080a080315090f07020705010e0d06050403230405010306090504080a080402060c0a15060f0317030c0d09 74
    0x801d0610a45049240039040c61080b80140000c0e900b4082071811041c170040c8840d054602194031550b0005180140f5041c00c03030766628034505205041a1645035900250140050250403039200980b00c45142810410010030000107004000000d1088403010856114140303141043d034102e0f45e5007644400d04009003090b0f401e0142c05414070740d480e00282180500420710310f180005002c0d0490380c83e10000c1407203648a83e00c1c104160009061045a8030301c003130000001d035403141c0c041482440040901b01e03131864485d00003481c000c4d21303520003410302900d0410062241c50326440804180d40100000c2400d85403440c3c01c88003401440b15041c2e0142229801e040e01e0188280144100c42c8240e805103d16900e400b10b03042192016640100b107040c04021501d0002d025088156009000410039401d00c0040d402070346c100516003100b11f4442a05034808410154036209110160072100000703581241145c1d2003483c0780f58502060030000402100013106080440212991040788401c00e1151480ea = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 10495411 1250 10494161 10494163
    0x406050702030706020307020901030602090f0607030e04140702032a01020c0a03030f02031e0403020c03030f0a08010b04030b04150b0a15030b04050903160f080a11060907030c0e09190302 82
    0x3000040303109000718031002500505c004150ba400075001001070b420b0780d2a55807040029800348048a40010780c004c1c2d02100790740d500025214035402503d602c40f038000740408001c111000c44904444414012051058140e0f00000713581c06043c0414034180000b203100c3c00706c8010202240030740720941c00001c58400d0150041072106030349100f80c805000c41805d07041581e040e400220748e1040e20301c508540103004c80e4040013804e03070071078083d0040d6490100040c01280c11a03002c40d5080f41080350003d80390785183d0b0712100300c60043c9a00480705003130030300b199104000800050400b8008011821468101c0c60f4258802c000e00c010052086025554900c4020950200400c0d9400841d2820158000c0d034141030050034841e000280143d4500901030100b510070300010326040e140d0241609180740080c8680c1c0040000420941b50080881c4429070020300d0503c000f08203000581003502c0070400194030802002c04c0d680c01195040711a9150140c191901141c4070101900c6581000c2d482c0516070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 10496661 1250 10495411 10495417
    0xd09050712020111070e0412050c0a0303050108120306060702040902030715030501170109020f09100308030108030403120c03050711010509030a060e01050604060f05101808030c060a0515010c06060b040605 90
    0x101c04c0c0ca40466400304242c0068031003020384103500c01c102c04a0001400070303d0348911082c54000f01e0074807605110325010300d1480e114a0300401c070702090340d540c010311412104121030581c0c5403a0304441440c40c50142d000c1b030141d0089800c003c1c011921840d1400444d41d051080c2c001400c1091281c41000354861402030180400784203c00c4062200e170302808000341c1c103000b1600300c0c40d0090408120908072200340705215800800302e402c0010551004000961048000d500038400a0011512039040d42400c82c0124411030004042c028550180b80020340c00c0425a5460394120500a030560007a00041e50ba522424400c4d56250007641c0320f00040010707550120f0021000d580c020441540d03400103100488401c1e0140400021050604010500d4041d14100d441c0c25140707042c00310404100f9018141240b180c2040030f00340c001203803003265107808200311540081100c42c00d100d18100031400c4140e594200d5055410000e6024901040c083c040c3c020314014a1090549a92691f440c0d0008140390 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 10497911 1250 10496661 10496663
    0x50a090209040b060f040b03060727030501090501050f01051302030405010204050904030201050423030d020903011113090c0503060a06030c2a020306011706010e04050f01090303021c1407050d09050712 88
    0x1040266200d076460909102d07d0500000244c001c2003151a0101c0966012140300c05070003000f11401c40307030001c80e1450300d000300085200d5400400e01d49a00d1506030300b501d038000e055502c81080500100a2665003260540310b140d42c40500590b00d0b11076042c6207003e03204641109801c00a804180000c16605521a40c4180c1c0034606500795144140c2c8090102070000c030861290383c1c4148565100b100c140c1d1b0060500904c0240000351080d201040e102e456085104100341d880b007108000c001d00c1c030b85405400e020081614020340f5503d4104006502c1f01401d000712800c240d81c0e00501c1e80b08602541000074074036000609811601604820100304000b52070b4100d0103030040000009122501c0ea80c841039040d80f043c0500090307030903d00b5400ca0f928004205441c0783c443c5c10840c908204d000e229104146001e540c01580d6401c105c84052281c4400c5500a4249032805d0740700d21203102140c0d81d00b604181c0b60b05d0a25500c2d80b5030184140a0708560b20007914078001d030f80707000500307809818a6440d91 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 10499161 1250 10497911 10497919
    0x206070606030c180c0906020c1c02100810060305040c090207110a03060221040b0609090a0803010f05040c020c010f18030b0a02090f01020601060f0c0204020408030c0106031b0f0306050a090209040b06 88
    0x1707040ca400c0100c1d00c10b03c080c0700b2000540d00c2001080d0941c07424802d041807400500070009035441c083e400280d001101c0301c00c1c0b1008502101c0034001d0003c00c40d00750303d002d03240606090005092981c2c07000700082d014403c0d044c6480d4046001400c00444c0701c04881c90890040600301c68686900340100294440e100802c1e82400d207d80003003001c0307001d10b0a144205e40080c80b51040744e0f81daa090000c00c000060001c0c480c1c2c0264189540083c80700009580601364112403041c003a814001404220751500b0800b400b5984100c0481c240d6aa004081c61400341d014a00b01e0880100e2108401e00441a50401004144107004005400703110f90b0142c42040030803500c40c2e85400d10040166200c0100380160700020300700c184c0503500c550199840b8043c05201810040c0317016516015a03041d90020b1104401594451104009021030b007000e190301c141000608a9505140c00c80091000d0b0341d5100050520791141d00082107082c099000d1030603107401500d01a411319281c640703034a06100c221145845 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 10500411 1250 10499161 10499171
    0x605040515060301180e1b150f07030e01091a030405100908070b0603030f0301090c090803130512010213030302160f0e04030305150a080718050601020304030206070606030c18 77
    0x10100d100412401d0010000d0946403a6908004141101014400d112a01203031215520b65451400300f044507070000003e5081380d480808101040511141c10103841c1300c000d41842a01c101c0800682118002380c0d02d403c16202c1254981c1c0140c0703101c0030590041040c0e28040d100d42520759010310003144528400d01c141e41c848807016040380308403250b642c40903084d20300902c154800a401024210340014000f41102d08040d1540c0342c071940c41e8001d8001d40d003406d0312040302052030341d00300340d807440507000c020b014505203400d10800800b000280c0c1f043e40d01c24010003c0d00c10070703030f5400e40c1110700e44002144502032040d181d05010b0360700d5441c030b4800b9100b40203880001440d2690b0107404426180358402201d46500ca54404401801e805014410b500125010340c0406949148502e002050310b0320160030390707034a0034180d040c1c20990f80d0070300c1000509103400c0004a030303030200480d02030704c2c0e0448005407102d5181c20407000405403604002e080200d00800840c0f40c0c406030720360f44130b8001a8141808 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 10501661 1250 10500411 10500421
    0x70302120301030f02010c0c030605040c0501030b09090c0d020a0509041113020c060c030a022206020d05070209041e080418060b07020a030201050912011b030c020a0308010b0703050d09050106050405 87
    0xe2030744000d2001900c041080d50b18480158401c180e00303d80c00d40035040d60b820403074a90b12400205e800a83d01101d031824441004c00980d6014043c0088a050403181980f03e0301d062400342e42ca55107041c0c184c03403145403000500d00071556280c5490015010190204809181c145404060780ea600d0f025035126429180349440036030b92500071114070520040292103a51030341d60b8403401640001d4142c00d0025000c0c005003da4840221030140c0f40d0a40404245506281010280c01c1501d070450f003004000c3c007040102d000d42c54025030190480d0f400001d04200c2040e4142c00c400b46042c0c01c0c0020100000081c00103991500c454a20f120039011041c09c00c1010340d80e8008001c0e51003008030003504456042d00c108050b601441c080c01e8024030250140c6124202c0315981403c48101c0610304c01800c405017070000d082c7c1d40c10310450315041460700040c201d04070700d51005803080105114150b40d080c00000ca01c010180300740d00341c038107003802c1000600c404001442d01d42c0c007034407450040900451404d00062 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 10502911 1250 10501661 10501693
    0x30c0d110301060c170c10060501030c0c02090606031302090f04030f0908060a0b04020409060801051e0c030c030403020c040509060405010509060c1b010212010e01030b100b0306010302070302071703070302 90
    0x28101c42440d212130460542c1580d80d1030441019100000582ca001e0040c10080c503403d1048410403101150001100c3d0f0400700050100c80c180743c1041c00304480308a40000507107074540800c2d08a07208131856034507039507403102040300070200c00c2d0002d40000c031110501c00400507291455009a109484045030b14443c140c04039001080ba1241c1d02481e03010f8400b148450010703900c40f1800c0003016101528080c1c44044100a403801a4040d602d039a6440c000c10a112200e280811038064030070703800b10180c0c2889401a001d074000603085459062000011904060003080b8042403950301410501031454036a0400d0340710038085405403955401c01000071001007000c103e070b82c46281001601e80c14011000e8803004120350b000c24003402994204070044660049000b075500030104462160705035819841c0c07901c503044001d09010070f40c000005090004005220540e94045000c1c6001070300c0c0c500038242246001b060384d0001e801c1d0b1403900d00c0da1210103c04401001054040d40071554886082c070402d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 10504161 1250 10502911 10502917
    0x6060f0e01030c0c02030303010b0406090f0e040314070204090f05190b01060c0203070f080c01020f01021309090609020d080a0207060903020a05061c02030108071419090506010c08030c0d11 83
    0xa2001848100d840000c039030107944080320700a210701d081551251580e02003465035000b0f8000510610f80032808001080d07010318098041e003000d40140400c14941101c0a02c14400500003d06108441d44820102c043d1201501e0340a90002e100f84544d8a090401d00440340010205030740d5805081050828110302e00d03610180d9a07808008010140c1c6015000c51381c5840880303003280e260040b0f140000f050150b4500e02405004143c018000c170041110000e880c044205c800d11000783d006000741c16a0b07403000840d100446050390070109801c2d01c0e61410724024030000b80025444180034000000b0301034880013404440e0307426000c0780d0410b5213400003a600e1500600c0f00940c00b002d2000240030381e090541c040c1261104d01d101050311014031548070307002d0b60000d8004044a0307104030780c1006001e51000341d107a9100303415680c03aa5101910121046861590300403800b1003074640004c1000c0e079100340c85020742c094102c400d40780c0303c2c20190030300b080c954480c111094074181017440d901c0010745400c0231 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 10505411 1250 10504161 10504187
    0x1110021204030e04020c0607050c01110d05091c0e130204030503030916140609120a051b0102010c0e0102100e030c0703030c020f0102060906040b04020109030206030106031e0e0304091a040912030606 87
    0x20001d2307a8602ea130490720795100400000c2c041d501c40c0380030045002d107a00902405006110049810f00d040d55006144c000c43d207006a0380503001c400350000702c582103926a0070300f500994854107024004540b0300b000c0d01c21039000800c1c0d4403001040001d040004200d10416041202011400c1681d03910300b280d161081e0488603078400401c2290068510345032004640d05000c031000d440c0301c100380344c403034034100001c01074840358a100c3c1031503904071980c0c280305014090740d26007000034200f810440000d54546216600703a4915541e080d01001e241c50800594a0803d6000103c031a180c5d160b2400400316000004124000c9241c40d00c4200c0135030011070000d02c2a4071b0341000700740558990f04e03039035404903000c0e105a05001c0035440200c056184c81006501824141e02c000c01c0c0307000607006403c2e45144080300d00b00090324201541c610f81c000402201c3c00c80344031010100c0c200042020410614446019040c3e119240201b244c040040c0070000f0340e6a81900d403402c20900703583d2034064514407060b6170 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 10506661 1250 10505411 10505413
    0x207080709020706060f0e04050c09010303080f070c0c06020d02010f020703050a080a09022d0109030203070504020a030b040609060503150106140307050904050c0417030408030a1110021204030e04020c 88
    0x19080c000d01c035982d40078205040c0100008288160350b0507035209a000e4070707081901007900b0082000180b04080200044491040d500054250701d103490082514001914190182003074030003045c07074180724070b01420f1f00c076402140c0c2d01d61190b80c9550107541d5194184031203000d54200002d00d00c100c121392003a24065070f015164146049606001200c5546004100d55a1380c0d64403c242801350b2203035450305010300e501900400c0c00e10714416032a18614100c15040e4100181880c0a0005850229102040317038000c1e907015840f01e43e152402d0740a802905903868005142000004005810f03030011320032501700b602580c0d0b0617000814002c2c1c1c81c070401d02402e0045000042e6207043c042040e00219030080c0781c0d241140c201043c180000341983c206072010f4001ca00041018090f200c20809452020800d40d00150f1a251a11403043d0b1280a5803041000380814140413070541d070400d01415181c5480d201c5e04564032040ca10101c0300080b81900d05500040710014446d40600b0329108445001103224 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 10507911 1250 10506661 10506673
    0x4050c010302090118080a02090105030a110103050604090501140609010f120807020103020f0a0305041704031502030603070807060201060305011802060904050402040213030c050f0105090d030825050c0d020708 92
    0x1a0040d070180d4880785441d81000a140618800144445120005810f40700007a01ca100020300420601103010780125200f50405524100044c441c0e04229076120703000c1c240400da50b518400050018103400d20003500380d50030700c050b10219071020803004e84100c0c400c03109400241d0301c60301ca5200b1000c25001e400d012070406032100700400c054501910740315105240c058540b80610081141e50341185180c1c10100780c68105100400c01100c041904615000c458103081c00d2564071401c1c8040000c0307141d0142c151303002022070150744003448400c4c003604807002103940c004d544030700007402410148403da501c0e5183c5020700e58040409040d41282940040c40303242005600c008010042102601c1280d1142c0c0c02c1104803204c050304244071005502443c0d42c0d4030a2854a424080b40702c60180d5024104081080310201903a00c0300640e002c0d0942525100044c0d5403000490003d1200942d098070a1401304c076604650503601c040206203081c049020f9401e039036402c5005076640c803058010a041c0760420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 10509161 1250 10507911 10507933
    0x201080403120f0222080c06070219090e0d030c020106050904061518020705010501050a031a0907030204020333010906030b030106050d06050702150405031603030b03010f0608150405 80
    0x150102d0524240740180000b510f807842c21205049911512000600b5100703250b46100ea900380000354801401c0c2640903184070544600010001c0c032808030000e04ca0b001030b0b004519400f2601c2c00e0f20003c1c1c001c242e001c01c0003c0c03800301d4496aa5496084a00000b800c141402201c544103000348021038001500c0d80303160340c9541e82d9440c090100c201d200080305d100b07804001648030440c0c02c00c44043c4c1c00d0000041c0d4440440c00c0190945605030061800b0345108001040060041e400044509480307811240598641c0c05c215410052543d00180d4000d0020040c049421010301c0390304a0090800c1c0560b01c1d40ca40c000c942030804070201081404a00840c4013081040d00a40040780d0036503000340006a030039141c90014001040005c802c1d030700155518104544c4940411000491400346904100280340a60b0341176074905c5400e1b405c2c60040c4c0c481c13100e5000c041c001c0d0000c031800000140240034103040300031144000d012602c03a0000f5485021640b0486800c00d03051130b4042c0d0b8010003e40890a91 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 10510411 1250 10509161 10509167
    0x1302030d0305060628020f070b031b070b0f0a06050103091106030603010b03030c060f0f0103050c010c230105040308060f0a1202010903050703080301050102012d1d0a050c0405130201080403 83
    0x38206500b204081041c0c2c04461005c051340b400116810407036030000740d071501000b45021132801c2d03040c0003903004903000d01c14001d10a040d030b58490a003607002000038415200340c2d07000d03000f03042005101003114828461110310503409517108020340401000340d80d41d40d0300114142c40341d10b0300190072005103148201035802c008004591000703002c0d00100704c03002d0982c003203442e541c413a80116150350000800d01101048a01169400540c000364050f0a541140c0715640c580c003c1c442d5044c10f0040074003580d8100550001441030003001c942040b80035006010720f05020340011641180010112030000300c080c9031001260403004006031800440d142443c60305200110b0f940c0c01a4107000c204500007001070310400104001d5841010b406459502d80000a402d451a01c2c1c030542c00c4681007150901000f02505860140d0016a4008640f6180c1031406078026150f00f0300ba60001c0c0541c18911060200001d60819144000e60701003101d90345814a401000340f44c1c040090005449401150210388 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 10511661 1250 10510411 10510421
    0x110f1311040807090b0a0e0712020a0210020408030703020708030a090506030901021605070305010e0601060c20040c090303090b130e0711060708010806060405090606040f02090a0b030f1302030d03 86
    0x401036400600d800e48803941d462a2804541c070140714140c45d0700418426040041d8400010304290f0309110300790030103540c050141419107030800300065000c07501e000ca5910030845400e0305101d240e003c56031a5202c400c0c00f600c0307a00c841010741c0035124a00001508840000880350300080c50740e10040d0150900041003603960001d40003964641d02441388114144202c040c44094502c40e0004280c00c40c074501e41682560031107003180c0740c01d030005401040040e41103405d0080040e4826600c16055240c180d45002060b18400b04541091906a560810a810100c01c2c0162802074603610070780c0e0360300c0b4070041e001c4c030038885004010384c4005020000b4268101d00b007500a269414041d80001880c180d1915041c2c0440c5c0d580002008400100800d040c1402000d0308007505a40920407032928a55a07a0795035000740049000d2030392000d0308008a0340650581d002181700501c0b45003400e0b9100d00c112401e40054030640c40000048000c10704540708588481a40c0e607000e0080c1010901101064000304 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 10512911 1250 10511661 10511681
    0x8011503020c160509010e01120b04060e07090606030f02030603070314070902130906150e0f0a0b030a06140612060618030d02010e0d03060815060303040314060103110f13 75
    0x6030207020300c0c1c000580600c40310f00310081403c1e016200e2403901003006030484040e4848465144020014000720000b101e0a10700e998124854500d6074a40d45005402086410300d03c9505004200300402c0c8140e45030015000ca806640e0103005154600c0c900c54201d1000361400b60341039008600400000d080758804085074540c00c41942c0103540d42c0c8144005a0b40702900c0054400c000174000e1055a02900c14030f0054880c1000e034201408050b131000e0710000c00d06950a101d041d09a5810045548610100b4003600188400310f03100d003400180c2c0d00240c44580101c42000c03158450141844c00c2c0101501c0d520f400315190032170741c0d031120001d0201c50f03800242410384d8180680101c0d0040c0c2c8042103071031075403409680000340d00800941d0660a15800318080c100b014144641007158070400101004406840452548142c03101c2000900d988601d0340000e0040b0603040045500c00c2010824604907400b61001d001c05a00240400140c50340c0e401001c3c0d4408264600d070054000c19074030961000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 10514161 1250 10512911 10512917
    0x102040f03050a0506010603020405060711040e0f010605090f070504060810090204030813050603090a0201080606070605070207080d020102040f0608090106170102180405060604030b0703021306050702180601080115 94
    0x540c884a441100e210507410950b219446220f4140030000c04000090040000c1e1400710300701401c0c240010111b100340440500105a0321515503107540c0d803588140c03450003082d01180c8141981e011410b02030105481444d11681440b000034151101011760203105000c2c44d664030740b03028104074023510003d50240c0035461005101d440414000e92070310081010358004c201540c1c4806590315200100e200741d40191b03024040038004c0c031800c0280015117030051682402d081c04603503510300205d4610b01032890040e1201e81081c1c01d01c44020b0700816000c013038418040c25605c030080c0c1038805a00b40c1c8650311513030030440150081048040d110300141ea400c6005100081402c2e42d85c0c9c2e100c06145140b2020700035141e503001030030340655149040041c2204100b500c040c4982d01d4044002a04e0340200d20015008040140018600ea4030a5044400e00405511150903850311000010015002000700300d00503442c980907a6440865400302522030300050350350294507030920f000d840549910340350b14814 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 10515411 1250 10514161 10514167
    0x90705070c050306042010050a030207080706091410020a020a0b0705130303030605010908070302030a0206072306010501121802011103040b0d050403020c0a0b0702040207021c0f05010f0c0801170102 87
    0x42d42d0302484000c1c029805040760603594804400c0d1112994622454a4803402064446040403504041030f40d1821039036040c0181c40712000d003000c44a40c411024020b1640b480c000240003000100140c56200301000000c03034055940b00c1600308201d2040220480140e44000b000303200007038000c0016540403445240450605699086c07540c011185034000b100031940b200800c1c0103950307000c410f2500a1170000000e0403881c1c0380d500401d8482c802c0100c0a8000d40e8001280385c28460f01c0c404031241941041103180040441c211450380350305081c000c5074002240a0b0302c1d5440929107000d48600d44122011844103d00303150300548130240d403549232350403e002c24400019031030007003400307003000c4d8107800400301c2c00d85010324000741130031407000e1031078441c1d40c0340002800601000c5040d2415154151001170f508c22840c000a12a1070b002089541d8100d0011208801c02c20201c07030705146284680008c2c081c000c0401582001d0b03900d24264000000c1c1031000411000707546107403440c4c0501c444000145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 10516661 1250 10515411 10515419
    0x80a09020f0301150602120f120907031a070909090503030a0b030c19030b01080607080a0207020d0b07020d03060801020301060518060403020405090303040c09270204140106030b041505090705070c 86
    0x1c25a03200080a2010309045441000031513014000d1000101f000c400032864200450b22521560040c61000f80940100d000000e8241500704401000355401480406490941c0001c0400100c0c0032181c02001035161040003803680450300a48110707652080103503046503038031201400100910108598103204e1000b4003c45070b2901d0001c17a215a40110122600c1c0e42103040c11a41072106a02c00176a40c0e0011040100703040c1d02020a9410840b103040141e500c0c0d4903400010342c40d8482280241c05c0807e02c10034413500135000140c0300e00301202614140603103641da4600c10f080303000921864002c81d100300440703c0c1d8804038500410103103a0041000e42400d40b01d4011074100c0354120f62850113940004284424401c91000c000300900382d103041484000c440c1c0c500b400d083c82c00124100207100160301f54038110755554004103500303000303000d0550007980c1d1a10010040d0080c14041d9024501d8108054034500e103a10192054802c0900304420503100d5400884241d407022000340c4449a000710045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 10517911 1250 10516661 10516663
    0x3010312050a18080a03020606031501032a061710050a06030b01050d0203070201050601120b030703020607050a05010f0219030e030a23070812090f0a1b180c080108030307080a09020f03 81
    0x20b000d13121200c0104440340c03061601925101000c2d20340c9110754403041c0340740a8400b043c0c100d5415079600040c0515250004038030f0780c0c08440000e080040c2e440c3e100c07070041030581d4861440303590b40860314002d0400d900c40304401581c901046c000c00c1d42000070300e5070505c42c1502030382081c0384048061400c80e01d00071090604404981082d00e0100050b516002031044075a44140c4144241415140070400d0012000020b0394800440c800240202408100308081c00018021042d890717411030001d1001244801c940c80081d4080b40401d05900d17141003074002910700c01d00c120900d0f1403411004602c0d00c20a40010381e64100c60349051707031880c04030783e8003174003c080e0b210082d14103184540c030700507203540011820b20901c400090807241c01d6800050403c18603600043e00390403070342d085024140a02c113070300e07039054143d40c00350001c07030185010001c04520f0303a615901c4840b05203490358600780d480e625607501940b24032060ba4a4400520340a020400c241203540c03010b81c0b801d100814032414920008042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 10519161 1250 10517911 10517957
    0x6050c09030f07060801061b030305060f1008070f03020c12070602070804030303020405040501050405040f0b0402040605040c0210050f06130f0207021309020301110f0703110a0c260303010312050a 86
    0x401401c1c0c010b010f0400440f5001075505000d0801c0e800d0280d402085480000748040390504003808154442000c00e42685502c0c14154042c100500101c0f80300e0802c1d038025001ca40e00780d03040800240e10580c00358500c0d20902c04d43d03000344149030142c20802d40c4402c0914141d000880142ca036680d080001c200001c214038020030066109440150301c0345e240404002c21510141c1c00240141d04107020040040c0c07520920003d0190302c000707050300a4540b400890020403c9802a80e0070030300c0c005501c00a40d0300011601c031100c40c0c0c00000d00050b074a0540d031594018003501c11f613410092540514070004407541040491901811005051404940000e460002d000d500300f880d00b50744610080035402c0a01850b0b44414989600928005030301c00407000310720500c034024041148160300c0e200003640902c04248942e8000841c40701140c2c4600ba010160b070f80308111a650071001d00340b010354004000c01564100c0f07070400740c0d040051120319020f60310b980c40702007100c3c05c21480c4010070415440301510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 10520411 1250 10519161 10519183
    0xf1d09010e09061f0920040602010605120c01080705030a020708120103140109020f060702030f03040e1f0609060c03030b0405010620071211031c080412050c0a06050c0903 75
    0x600e22480c1080c1440070300f00400a44000350841008402a6101021309000011500180800039650160740d0381b81074620003081c590320150100040001e9440c0d0b05400c0b480503500100c1344c540c0c400d80844410780d540c43d26000500d000c1188800042c041c1d60061000d07540c04850307044054030305903d940e500320441e0f00c040c1d520543d840d10400140244040d09448502c40880b51008000303c0b8010340005107103240422000c0e04ca88030006011007103450500502400054030800c403920340d61555032603100224219a001008034007881055581000c4000d14011948a61103c800243c240901140e505403044425804d03da01d405200c40d441c0c4491142a0080010307a5480040145100400e0300780c0100441ca07084640c081c51003400307090903501c2d0380303c002e0b5400384c103641180c1a103101003030901c1000046541c1200300038000526454203c03415521691180300c0e4680754000b0198261114092042c0059040d0722480c1950700042041d80a560004007a500407401c00940c007000074900412122 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 10521661 1250 10520411 10520429
    0x1204030501060f0b07030206061c02180105011e08010e0a0b0d050601091a0604150306120b09060a0504050604020f03070b0a170708040510050c0409021803060c0306010f1d0901 77
    0x808101d0281c00b0b8184402400e44415010310b4541d0706d4900968908024201c41c2c411485588140000f204c0c610050202c0c0ba805000c590080310542400c05030410309104450100b500500c09010941c0e8414101081e08441d84403d80d00342d08200c40340c03a07a180010f20311080c099669003556032965902c10307844919481540101155070405070018180c60a0b40d1219044c04000160644940d42d214103440907203008240044010300b24000440180829034402590790040e81c800806105028818622031404d40c02121030319200e4003491804c64200319005841c030b411000c04140140b50101200d00c0c0e00000400300e0307034180c0d103410396103099511940008022039484410551914120176019511041d642410001352816031500e5840710244680c0f958010365400002e50108410816a0003a0a400e04115110340e28070301d00c0303020080003580d8544248140b10005118607820000c4a01c40d41c01a03503010306040c5007076800c2d00c2407644503200c070f0642c0c88400380165260700c82001541c000e0403035070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 10522911 1250 10521661 10521671
    0x105070b04050a03120204080706080408040e01080f0c01140403080d0b06030a090209010905060108040305070c0b0a090611010c05090d050f0604050102090a0b07031e030b0d030905040f1506030209031204030501 92
    0xc40c01800399480026070175205070051104001c40740d400300303550044a003903081643e2291307914071b4000403511445d0040440641d0000010515400000b1122080e640380c000305c0b401a0242001910592450b10038446000e00400c414000140940082c01d403544038211b01082001c405c60009000b0f400c111446601d1a0390382d800e03141585804607090b40101005d4408012904003100024080800100042c00340300e4000303540300401c01c1c45a05c0c81c00801c0d4000025441e0443c071000180091028462480064000f04c4104207005c818070946e0880d18043d01c1e0940b9008080c002d00c40c10503040503060340d86011302041808a00c4061180c00d125600c64800140d5580340c4c081004041f03c181e411124201405104074030001790000c0c80c0d0784294035a03d0408001c115800800c070003404030106404e402c01480301c001800c143d00150980252041100c0a001401402c1c10810407184050302070f098841500c1e20130003209000e54000c0030328030340190507a10420985000d003035042c0d10a0f4821160382e07540d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 10524161 1250 10522911 10522913
    0x5100314071809021201060507021804080901030608031201150c02040203040b01050406080304080607080a0b0d0311010b040209060f16020604120227150604050310020c010e01020408030d0b0105070b04050a 90
    0x305050141910303c100714203010607080513482801c41401240140000043d4a0043d540c940e0651150b000e5980074824803031400e450f003260036070440400580400e0030f01c03c000c60a441c000c001c0c0c403510085084400d11980c40d04070007811009521184500b1301c5603159101d03015880c0c0340000d502c142e019408000e4194544814841282c0507580001025003042c00280604500400c0243c3c03c10b4040c904522581c4030056030000800c1d80c0d450b125400180c9401d14000c041e003001030080012020300c02007240700e80e144c00744030580c440c95007500e500000804c502c900040c000d102500e20140320401c118610384040e03000c6880da03805038011084c00d00420b2001d40031483d0820011002e124070701d904032f44c1d00381051440088024090405402400c20b1542001c907038880b1000d0307400a0070000d045680c10f42048214000070361003113280030480d50030000940c0000d82e050088400310342042000718a80f6100c981c0e101c00400c02d00d15003a040200c1080100702180c4040c1481340514080c0c80503105130002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 10525411 1250 10524161 10524197
    0x20d110714030f0403151b031505041e020c030409090309030b0702010204030201050403020d0f021e09060d020114030c070f0c0602150603060a0903020a02030115030507090e03040510031407 83
    0x1141079031454603407040180a818401202c203560071654082ca115508100b400d140d04017828042420325005400b00c41c0c0d40e01036a071701d038000e0301ca0380c01e40c1a41c0590554982080c0400d84001031440c0402801b0100203149000e44d50303006154000320306055a0800381c81d80d01300f00541d0082c61090b4002030b040d4105200b844050b504546e00315400c2d0008525052550b40083d059010b1480080d00c907881d482110ba061007940340c000a07020707900400310072280d01c00504404c481351240043d1405070f08200009a00341c00c1480000509903016120306090200403e0303d965144d00c002d0000c684804184501030009580b0741d20500b240384601e1207000c4081c10888000d00c1e0240c00b951003085140703040107000c582d450120f48182c215080d03410108a141c0e1500b801d0b031405d825004025055803070886003d13862500840c030042602d208a0580740c440c1d03660340c001426030f2506103d0040d45d40040104014034505505020719510041c24041040e0522400c2c1c00000c400888106021400b00840c0442c2490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 10526661 1250 10525411 10525433
    0x109120207060f1d01030902010201020903060a15060305040812040203120c0304030b220b0705041d01170d02100b0109030206070c0e070c030207050f0103021b030d0506010503011202010f03020d1107 87
    0x218a0f140e00c00d404184080816001c4c40310906040c142ea07a00c511055910030b4048a4101201404481160500c13000e02c81c01000e440d40b10981c0c55120032008503220380b00380580341c007131a08400b005080000340c0d01c0c03032308200c000900101e03894442c0e40300d08403201110502030300c0c0300395444000c2d60321685541000c107040e0701c000f00542204207113155030708103034002c0041507401796400100c1640c107695000340645081c41141c0000400350700040b1000462090004000d05880021171240d02d81000c61a4096441e00b11349045005a040b8800390702c2880c0344c41e4030100c2c10510514004801a55039000316916500c0000241c40e03200e00d03c40107001c100c1c000d40f4503030380011051600507405446910300940301e80a90050500c41c038079000c06054213a00c02e80581c0c0701504121044000341c0b0060503003580d65802860b1540d00d0505080c0066410b601031400e80307049502804070403140d0001139004403500500c1318482c0b01456820f0090b84404000c41c0724002d0500405411a50f0f90b074000d051a410303580d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 10527911 1250 10526661 10526687
    0x150902030f071b0609050f0a05030d060609051f020a02270708061302030a0b0301022b060b090103051f1215020703020d1b06050f0604050901050103030503060d05010912020706 77
    0x480e20b40f00c9402c0300d0070900701d01600c180c2c001d0400154030f00107290050034006034245094042c82a40c1d044001d000010005080301e0b888000b00f00314007a501e4034140c0714041540b1a150340901100400e900e481084006915103000b640f043c1c900103a406d0380001c401c0c0e104600601d00c03402020022420a000c11482079810030003d04007200149001c0d400600500000110102441e4000c03003c1420780000d42c00c00b00401c00010000c0d0740355803600300a1040e41191400c020305ca200c0d01ea0642454460701e1091a080e9651300b90704e40c0c600001d80d030040d40038207000f8018903030724002082141120710401c0c076948041e02c3c0c072101054541a0f182000d2540010300c142c610320f903a10401810000a40000310030300c0403081800d00c840683c281e180201c140d440d2981e0081d040d2400c0204110321035a1100c15244124400c0b202000591600c1015908817542400004c011810400104000d450040c0009040f5803050001103803064403550f400c0410703403803c84245d0242e4072441003071007495001945003d06e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 10529161 1250 10527911 10527917
    0x5010510080108120702191203120204050f040209010203071505180105090705041104030c03080319090b0f060a1212031b091a04090e06010512010b06030a020d150902030f07 76
    0x2541800e0700907880d5681502c44c1800c000c0e00041041c11911880c80203807107000c0d01915a031141e036403000800c8070030207000c504a00144800c15001103080355442514280c0704041c0004400300d210700144402507010200742030552206000748400a46018242c2000650108012441e814100390809242c1442050700c44164100010001c09450000e004403c6174011100428081c607070340e1241c0d140d40b20325040540325046104001c0140144c01008500900c9144400030011440c103038103030100e4001d418024144001e05001c198850b000e80c00c401e410807401407106c14500d81d2210107080301d008001044030035a668844505580341c01d4420703c0031543c03001c00300303241c180c42240c0000c00c0081701e402001c00628049007070391010301c214000c0d40c000c3d15005404000000040d409255610000d101f498811903c010000d00110b0040c000c94807107443c09010207003551150600707100650443d003103018002e0358500340c2d074858246540c590b200500035002c0c016a00d007454400414444401003c5a0034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 10530411 1250 10529161 10529177
    0xa030b04050907060908071a0a090b0d0603050c0907050a0807020705060703020708010b0d05120c0a020a0306090210020f030d09050c101206050f010512070e030105010b0903011d0304050d050f0d0305010510 90
    0x5081c1c941282a004201445580d122049403040d940180d05400400840c62f001c224149142416442401030382d00803021100a152a0010000e105404a4400c400030320b040c030140b0740e00c40c061b0847c150440110300603101d03075a880f100480c1c181d4121b02025001a440100308204c00c880c20b2003100c810140550b600f00c485a95515282e80d202168122420040340015510150f40001d201c0c480c22503a000700f80e42d00c059a00e080940203003d0303c05050340b04202000050160a00000c7c40c426000c03140d034051403d01c030440110304010584502c007034605002e4401c0c03103000c50341d40b400384004804060700d4880c1c004c2041500c44d0219040e90704a00e010321644410700c2d40360307038101d415104a0000c407600c441d0b090342c8644c03044170a9000200460740560800d40040b41090541014200c0c865080e40200404800ea80086020b1088480707141c0b52a0010441444642400036000c0c114a0088048583c08041010914540501020050000ba035144011b0184c2e1402d00f0004000402c14070303004070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 10531661 1250 10530411 10530419
    0x314070b040506160b1302031c0e1c0203010905070602060a0b010503010e0a0b0406090b0102010b0102010b0d02091f0f06170f0708090c09090607020d0206010e0c0a030b0405090706090807 82
    0x2215100700d0045500c500e0004c66200410541e48070380c1c00d40359501c1904540a401c140c04007110804c181c0c0c9040b4800e0040d01d6100108000026000c0c03540d403000c2e41c3e07104030f0541307120610544101c49241001e65152064081c0b02503102406003258040c403441c010141c0501e05080242003813009008207420f07500302595085241c4e03106007075078103680c6074040c00c0d052a02d072042e0050041580130540c603000b41c18203900140074800c641c050f000c2030100384c00a028401041004908a9245810450740810300564130400360a203c084150b000032040181c1900007800041800a003280c3d610002208800345810701ca400c0c0e11035041075960a41d88107491103414003510b440d401c1c1c2d800924401c100400840010b45a0700c0c02c2000c10b00d800b40140c08141d1300d08107a00309a4859070f08480e41d401501c034850350180d41500c000745250403035801d12080300b0207840740c14100100758021000c11003010f80707800e0b581000d9901c51052034001c500f20300003800403501d007803006001107290758001c1c0d0315a00800d400300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 10532911 1250 10531661 10531679
    0xc0904110c0a060507030f0e060906060f0d060507030207020306040b010503160b16170a0909050105090405030f0702030319050c0609010e0a0602090a030804030b0108061003030509040203060301140a06031407 91
    0x20419038082c038003040c40d9035005e0701140205001840c0b03542c0c01e03040245130090090082101e0340184001410f58a0b90755408052018003014100c0540d003000e8600b000780c000c240a0f46c07209800180c1841c000d403a16a090f00028605402079806407a0303941c8007001040349103004c00c005564101c41e0803c05016900d40340003480c441c000e0300032408805407240911700c03c003d03126041c00e8901418600f11034840200045c001c106030950302607141481d150200101351440c104011611941d485030080d40340c20000d05003801c507038208000807a0544024030110032101c044203404402d0004940c1e0701780d11040d000700744524005001d481324500d40d00d41101e1080b02980030561628158105102682d0341c944400031400484007a400a0b02c5060085404400c00846800f40c0e0b040f07500b0803007220442e0300e4002504000c02c0207031100401149080217070300c0c284d0800b074015540c45507005000080102e415504003060050807100c0138807240e078070748040c020060440080d540c506196002020000c0c01c03d1809 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 10534161 1250 10532911 10532923
    0x50c040602060a11191106150405090c060403031805030303070c05010f0c020606010e03150c0406090608011401140903010c030c0f020106050303121b0a0309021507020906120f01050c0904110c 84
    0x1700002003220302c44040d005025071440b4624040c07520485815207400441124103401d501c80c06031250781001c010540c030030780001d210005030f000140024a0300345141c4c0d080d2088041000203080900c0d00e98000110b80e9001c0c0060b52007207030681c84040b403540241c54020308480c0305d803498110480c13421200f500700c0c5a00280042d030040007030074500240f00e520800246000381c140710a004076034180f000c01c1f140f10300300300141c000c41e002600d072520560f8850388141c0300c005d02401201003030986110b0441180d03103c1c001030302031868900c00540c54003850313002003420b40d030b00e81c119030000c280c4401c10310b48160b6005150401c0e5100c2440200001420400025200e2140400041007003110030003084074800c422118101906025980564540042c03101034080d000c52070301079110300074981e8001001c030440c000f201c500b16801401d0306210707950756040010740f5002c000c21030f01921910480c620b440e5824800d042c000d00d600600552107010307440400080d80c100401d0a030009200340000700c0c41c4840020a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 10535411 1250 10534161 10534177
    0x1c0e0f0415030809060d020301030c0305070e2208040803030a0b0a050a06020606120c090405210405030307030c0c08030406120609061a070201140307031a030c01050901030f0906050c040602060a11 86
    0x8181d1344450443c00221103004d08440012110705c0000008104490311100000b1a44504280c1d16400e9480540300000c1e0001c9803240e0301518806002401498801c0303122600610400e4030500b419142d0b21643d20315041200c440c41c1560391009a4001ca140400c8070310002d04080381c03040304041c145003000b5201d5102510075401007200c0d09a01050080034804d011003442d01404034102c40c80c150400303690b01c024a0048004d10344940e51580060038010f01224151507000c1c000710301e001526502100c0d038000c1000e0645480c886102d02240c0008280000c000030300c05070380e4210118030444c0704c03642140c8580e4890410319241010401c10300d030341010701800c40c000c0c039450241c0fa410640010b0b00c0e80e01803803058000107100001007007807064255200e41880300300300c4007407041034400006240e80e48100a04440c0862002e0040070088d600c0780d0005012070014900119010300c0b40d94604c0c00b994010f4826050000e00802d00340b1465904201c0554000507441e000d01c11900e00741040900741c030030b00700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 10536661 1250 10535411 10535423
    0x303090a05040902060f0a050d0b030102070c03080307020f060a0605030f0307020102060403111c0c030806090606040909061107030e0907050307050702060702030f0f0c010f090302030d030506031c0e0f041503 91
    0x4440c10b56171507106031849180207840da695101c01ca0103000340703550b0180d018442010310b000cad000a81402c05100307070381940c0d610180a182c1c41d400c5481d0a4880c1d00700828010851103820894404800e05100090103001503220105106050070304060500e9400e03400800554010b120704009030303030b00048198020750542000c800c42407180c10180d0402d032641000b40070351642081c0200d0391981c041001703241e01d802a500c402803a12688200411207406a031201c0d4841410311003031007180745a41c021070003244141400112414504100d2085421462058010510840f4030340d80c6810b092144a80c030107400d06e000340ca149490309002e840360041240c068020f050203d00e41046482c1082240e800305202011908000b903211756055940340800c96040c00140400300380203400f400b0f611088203907039009000e4010303a00c00ea03004030b0040000402041e803501c80c07080d00d1094205091850202c9180b940e8501c10040c1c056410b12203181c042050b100e000d540352220032100103030010891000e80368000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 10537911 1250 10536661 10536671
    0x70b030c191209050c090c0a021002090402040302030718050f0907030305070303090b0a06080106060e060702121c02010c08010e1303030915060b040e090c0603010e0603030f12150303090a0504 84
    0x10049510a10110b40031110a190090a00c203002000030713420321942044882e0300c1c4540d17a483c07070410203001740c94007440560301c4400e03c240e001681d0b130040e040541c0017400050800750340b07400103480c049040d80034003015503560441c4210702d521402030503401003612484441c2420040002540c89405e40300140c20450003142c080700701442a0000b406554100181e00c41030300340209004010900c9129201c025840d00b080000c106000e41010421284024601c5050004e22307003d119290442c140340b510303180544002c1c0f031352000002241014803652980009040303040c44c0d402034001d250603041055201548820440b080340d00c04c000b455865418a404940441c2ea031400d103801031340f804004a580c41c28050013090000450340504202c42ca0760400c9103150f2510103045407201e8114603041e0b003000b002c100600003004001344941d040034024041700d141880071a2619495003090090000407414101031107807410910380c0d03801c080541180914030781081c0030001510b21940384200c0340119251 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 10539161 1250 10537911 10537957
    0x309060c030a02040306020f130f060203090405060d050604080304030801050301091101031d03030108030717030f0f090705030607031b022a040f02040b03070801120c030b0402040b10090503070b030c 87
    0x2d5010b0380d00860740080c0035500d079400c0f41c019083e16080380c0b81145501a4001000900b020341c100c0d80c0041313030565009103251840e04c2c02800050100100499006071131203040c0c40003e40c0401c0702034071a602520400b0780b030381032501d00185515810790101e4840ea040a80c000040303814040c0c00f00c480c01003404e0001c0c2e010300345080c07000311100341c18a915031404080300001d0307000408402052000d00c544c50406104000c0140d1041600080d40c02e02c0d80720b1000da000580703216804100940081c45c5000b111030082e0f580c00040c3c503020013110004006a151003589403070f12000421080b03c0d030840c1c0080c0012024108200c1218440e415001c00008001180c035079164403540c1c049961383d01501d4095603103989428010b0100d52054413a1400240b0200c0001881d0740c2d0308a220400301e60040b08542c049195481b00f00550740d010748107980c0980e8403196808180d0300c2c181001c085607459150643d40f1032424003018100849940900401003041042000300720002c0102c0352440b0716001030116070504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 10540411 1250 10539161 10539181
    0x30b03150106020d02011d060c0906040f1806050108090a0201050d0b090a0606110304120807080d0509070e0a1505150702030708060901050c07080a1416030c1104020309060c03 77
    0x2540c0d806900c09060314008202c0590104524002c07003043e0300244030310302c1401e125100100034100c4500391a00000c010a0134065810020050740c00b009184604260b201c200190b00d283ca1a44a520a40030070072405e2641c1c00c841c06000d009100c2428044454075104400f21f440d95500c0c80000e040000014610412100c940d10400500301c0c0a801940c452910ba2172001c01800305003e0307070000c1040600e03110902d0701e0020444050741c1241c40d980030007950581e00c444894100d1031048404032400e10583c180d4030381030b100300381c4510f102c01d0081550b0741c50501c806030b03550781c00352000d9041401d100c0300944030750000d1034000c1100c00a031152040c0004454480d01a0701032003c0003035050007104e0300000c01c00c0c000140390303006e910b04c5002000280c0351000d40b140c1e00d01c41c804000b0150b50b014421485080e020345109400c1250f90f001c1507280100000a41f001c40c00444030840219003400d0714038090180900c2c10f414140340550341141b0b917040a100701903944034018905440400000001504007203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 10541661 1250 10540411 10540423
    0x304020d02130e030304110a030201120207030e0d110f0402040614160506090a0605150d080d060306020406020a0510060305070314010f020d050106082401030c0c020d06090b010801060501020706030b03 88
    0x2164030b810064040b0403401540c80e6071060303400f80c4904414000c00b462505e800500841141d42c161960449844001d800b44043c0d0800d140076800c7c401040415071a035120755007040e500c50310650b05802207030486410407074010b940946480c012031040c0000d00400381c0000464100703484041241c0d40358400c00c82c01e000c83d144683c41c020000e002d400c00303106418100081400109100d1602030040d640c405514141704960000025481030085541002107002c00000703281c0398410f80c0c00480c1081d220740380d031400e03070f4800d03400040164020f006070024000e050180c07100721344907142e0078000c203840c50b02c0b01c955445150001034100c420180c0100d44e001425401140c10600c000300a40d01c9014500c00000180424130036030b8003040308000010465150041c1d5203182686184c0d510019403612401100203040070041d00040c881003403c4000503036201790502038000e10944001c14013403180c0c40c0000c1d02e2070040e0b103d850160b06008042c0807580e00403814405581d001e02e800101064000f000030300e044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 10542911 1250 10541661 10541689
    0x301120807050a230604020d060515150301090e0307050c01051606060806040b01060201050f070e060d0501080c030c0d0816080f0d050109050705040f0b030717090a02030c010908030304020d02 84
    0x8412458003c08001c132074004c10361028052000c582c10b800c00c0b000c40c1c17074a404080740c000358481c100240400010314181c2c40b45400030140740840300f404403d03070040b4103802500198030201301004001001410300038001e10320b40581150295040110a55880b556044040300c0e0324144000030511401e80b01d001c4081615031900b001c014406a6520101c00380c0700c1030251015175400c3d2900c8000300360680140242401143c10324400b444654400404444071110300c040a64404000c01403103501605a000380c0c0c0c060650980a8280034000304201440d00c0c40501c0140d02880300c000307807400410000c80607039107120840c4000d0400b00e40c0e9032401815500c90310030003944c003801c0811007480c1ca42143c2e2055040e01c441130020401901c0f00603040c3e5040c06184202c42c241000c00704180700c100c01140241d44c0014141c207085603074641c031000c04a900d44c0b040300c14105d158411002e05065280400800340100c20a0814001d201e08240d489901d0384402040a03000d0f8855650300c90454803240130a440c14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 10544161 1250 10542911 10542913
    0xc030e03030403030204050102010606050a080a091707110a0e1003080a0309080d02030402210712150603121b0b06060304030e03010c180e010f050d0609060c120e12030112080705 78
    0x82d152624000e402034009000b03990040d868860049482402541103480c40c8080d51030701c00c00c950750003140c0720240c414807000b150040c46410070000f5260048000d01112482515040c00408a003414001d014666034824050940b019050000c0124501c000e6010ba030340044603160754808201060b0041c1203c490000c00180c0c00140d5002c0144143e80594000d82c401c841e0405559040c003040c014040c0d080510f0801c1e900014420060482030319403c1490b54861010101403034011030681d012500980d00c240c3d4090349c0480716444955004102444003042414001c0c0740700c2180c1c40d90340800c0d000a101c9402118000003003828180101619014440300070001c0c00318100c01d040081c140c901c01a50a40c20010004010078801c0000b421141030728081040c401c20640360104022070040c0007036060700c00c59521105030011501d83d000b5040d401d8a00d4490000c418000b103030007411917481c0c0010340300903000344450140c04862001100e044601104030380340b800300542000d002034414000000c0c15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 10545411 1250 10544161 10544167
    0x120c0b01030f03020c040e0c040c0e0603090604030f05030907170a1b0f0f0315020304020d0501020409020406080f040b0103080904021c0603050d08010303080f0c0c010c030b030f0106030b010302040c030e03 90
    0x401c0200c0151240b810b100e03609950040010109000c207450f007414000301950408400ba25590a0a900c034181c01825403800c40701124440c004903442d0703070042e40d0a19050f0005070801051680285880030f03010300ca842c0940ca549002d13503040da10782d07040e0b00402c00180d007582c9041d8508401082100d00303041c0c102e40783c50340a1100c0d01d4003038482d400354400d607554420050000600701c103200f03810313402701c0341c110480c3c07520380c00010010700084d8002403040fa44500c0500c407010108000348081c101400800320010ba4903410910050440d1800400005034034501200700300000390345c081c50340d0440703a0150030f4585510300c0000060103801200304080c1c551090800c03d900f4580d084d0051411240190199101c4620102e02107031002800d003c040e0100c1c0601001c0341c1d41d00300c100d00180e030202030244120b0424000c4c040050a4552015000d00001d40711300388924281340a001402020500d100200925440c540d503d180141c014400070b17209541d20b100e10642a0f0194000490400e5003809982e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 10546661 1250 10545411 10545413
    0xf060305030d0c03050105060c070e10030c06020601050f0406080d030905010f0c020c0a0603090521040b07050606120601120303050604060e0103030207031b0605031f08030a1101050c0301050607120c0b0103 90
    0x1083c09510802c006401c180c00003a60b81440c4007101c008421100c05041c080e424140c0406a04002038514a070b1840107210003c007245403903603540064181a400707413656500d00300c20070284900c04a00c652055140c5002001800d81c0000d05131403c4445080104080050342085c030700601c045194224101c0c18010352003401d540c0410000c04901088a6000380345803a0b1104408403101807034014810740c0220116014603116062070382d99a1200d607109880c0c241c4940c0314814940100a088031f581e8403605c1441840d2419078407010010107071348004c1200d9854950b01d00c60031003003030b40054285661800825007a071202d4001c6400b07440202031401241d6568600256500303900e110940b04c540940b0a00805000d021a0300d808464040e5551411600d0300c1520109102401c45100c161003211100003030b8100d41440074040a40c2240c9901062520b410040d41c2960001400c46003009001c000501072556405c0a94503030300d800851144114010715400d607103252840801821045900300000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 10547911 1250 10546661 10546687
    0x210030b090c070c090e0703031b020406090c03050603010b03060c070c0509010608090609010504020a0302060901020109050d0905010905010203190c020312070f030e010c02030a0b0a0209041107020f0d0305030402040f06030503 99
    0x2843c01d1080c24204401551041d12600300c40300a0b00d0f20100b40c0100c42c08101091081c0643c0081070b4010701d0018084c07420390b0000f8103c0304258050410700fa1180680d2040d1600340c8191644401c064000340044c003507140020703444030001044454240c4000c92043e007808910500700300901400b90500c049961034040190040c41e04442d148228482e210000e640110f06004441c015980a031400140c9819542048003540110010f5070441d0f6940c9240070200c1d23001c01c0141c02d540c07426240c500d00d90381072400040c05010950091030656000b0403007150001104801c052070040070749000e0a5014151000038100301012071084100c190100da090144240400c40c03051071817182c3c6824500550301c1e801940c0083d02540081d47c5904685601008240d940f00a41e6102c0c900550040c9010801c5001a045600300650003008000c0801c981045040120b0b540e07543e2502182e03c0d10140d103407035400070a984401032009000e10340380d14001d810740d41c041c1c024001840d0f204041d03e0301c955140e2514 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 10549161 1250 10547911 10547917
    0x7030b031501091d03070f062c07050d050c0405040809030f0619060510030903030204080a030c0b010902040e04170412060506040501050901120201180518070207060206060105070210030b090c 84
    0x10041e628070301404d00043c03420840a50f0301860501001d54100071854841e4200303209008025110f49442d48000012517008160582d13a03011a00c009480c00039070721035902e103001d516410407400350030790710304010104400145d050070204045a0103d065075543c0f40002c0740c2c0c0a03811006805201d0100d41c0b0200d90004120346104035180c2e4001002003420380410030a07a00b252181c0c641081d1094401451640b003a0402484107021f400c001d460030396200c014074500410702c2c0d0160002016141c03420708000004016a0042c9003403d0103504250404018601c2c2e00c0005e00010aa5040c1c1d000400c4103400308803e40e40100884141d5006039034203411711001401040350003074480c51400c0004982d03481c0000e41b250586500130944d0507000c15950040d00d81011302416010b003413041c2c44c00068170f0394885030717418008503020780000c0280c240201c02a10707010142d000481990083c00c108130959074824159040f580d01200da44c80100041081079004140c40300001d40c2114084042140d010241c03802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 10550411 1250 10549161 10549169
    0x813080105060d0b0402060a0c0210050a0305100608010e071e0c02040b0d0804090f020f0c0d08070f05030705030a0e060702071d060603010302090403020304090c0806040b060307090306020307030b031501 89
    0x2403126642d21002c0291490303008038010241c250000100c0d0140c01c041d4054820ba00803420f1003041460740e40c001401c05450702c034004000070000101100f10562500500360861200d5011600180c03d0101c0030707290700d90501444903c40300c41400694291711803280480043c0b1580c04000044242a0009003081d01c0c1c40820303030050341011100c00c254201a2041660310340c10031179440c24182003c14042c09030104210041030142c00740001c08910384036070000d00540c94000e00900d00e0f40300090003d0460007000340060240f0419080c25951160003204480c1d00031810b18009940b9620542d65078020100032700c10703625500c11801041142c5400150400035111101414800003011f42c56100d02201c0c203c0305650001014070040005051481d14070360410701c6801903030b040c00c0c0c9031040c410441e1103c501d01c800284100041c001c03e400c1501c1040342d600000d40c2ca02e4914604140d01416258141c480102070950000000c2d0707032103200340d000064a013801419100e0b204181c50706805101002c0c09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 10551661 1250 10550411 10550413
    0x50a060e0106020f0c01030b030a0204050a020a17010b0d0b0402070b130201081501020a0f020604180603020f010503040b040b06042301090c03050403020a03030905071a03070f110703060e0307081308 87
    0x4000300b0300d280001120004540070301d00410441951800440103031543c8492950180329002c6024016611406881e108907000710300140c54440c1108000c0900c0c290500c035a031070281040041c44040303154021180707003888295011680d480e010740850028420900b014040f0800b007400e0003072004502c0880d0480c98000d03611219a03484000303402c034100010b0708055001d070303001007684000210507410305100240004e207a01c0c103103559900300010081d00000c00440080c2d44041c14021407915040c0d52a141d4004e1030000d0951401743c0d5407405804025001802d02d07605c5800081480d60f40b504151b00494a0740400e2260710345144800d010210f0038041c403406d40342000d81e00003200f0b10912a851003581c2590080020100f5a20107030001d20300c503071050781d89004902d400f080c0c3c0c200d00441040c003940d00720812592817070302c0b0701c00030305519102403443c0400c45420400600d60900103220070a503034001d00000f44c0510400c01c070500d14401c83d20001d02d266070224001c6035154058a1301070840780782d10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 10552911 1250 10551661 10551689
    0x60806090c010305060307030f051c0513080102090a170c100c02030f061b0a050d02070c18090b062b05030a14030708040308070c05010e160b0412020f010c06050a06 72
    0x7600550540700c0440b41710b90194810b044c01c00201b41402e44c1540414066802d8401e8801601410028411621f0303031400440c40004961403a800c40002c0140209982c0d002103080c00304240010b84a043e09114a0b035202107401000a56642d0a014084807a580102002c144100c41d0780090201428200242d00c80d01034402107026034034001c20038610910440e4080340031400f490703c403100545c010200307100401c8414404010403090510003070045030300805000304403c1c07500c83c00894152000460610281c00c00f00c03002c0000f113440c030105401050449042a001a159000c4429005031500d98514003a141040f40244600400140184625075a40158008039441c0a0120388019103030381c800501080b0025012a00c10240c881c2c0003242ca1410548000395a2a03550030f4410602041c0d08540140d032104107600b02c0c01590351700410550541609141c42c1594800e1008407a54004e4003605101582c41c40907807060201c0c840441e4400c10070040d50070001042c030010405800703900c080d40c16003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 10554161 1250 10552911 10552933
    0xc0a060905150408070608040503070c030f0b0901021611030c0301090606050f01050403030206040609030c02030607080108010513080d02030606040b0706020a090605120a0e0708030d0203190e1507090906080609 92
    0x14003201c082e1013800004051052402e101150300040040080d12940820b100c140e0000c1c030740408030401075000c1c100090900503142413840c0148000f80031001c0c83c0e8070406c0740000400e501c012a018090700000e072402d840c000703140402d08004e09c101c0722a900d0751a09440e9020081c0035801841920010f50b01802d000389058015101c82c4921b00011340036920100005000a490b5005502420301c030b450940080200395011900e0980180d400ba40403400400051001c1c900900c181036101c9610007a441850315251102c0c0024401c0b000c44021080d00000001c4458a510003298020f0260411080c0c1e1a500307410803400a42103030b204038001039803803200020311b148101d041d10b00d45031781c03110401d01645907031920000900c100140c000c0f050180400014640d141800502091400300b840903907249000407100b03103c8040c1c0d1080035105840c011548000c0e450018054480d10016a5004080d072200041074901444541c00369549a0a01002003811303800407581e2030241d406042155514890 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 10555411 1250 10554161 10554199
    0x30102070206070f0606090f14060406050109061202091005040602010b010914040b030c0405070c0201030605030708030f0a02010204031b0503010f05040803190219090f0f14010804050c0a060905 85
    0xd120406548040e05001800204255030540c43e42d2170310445000402581d902035810548101041c110f01907962000c24400c40704110145a90242e0129010407441c0d04100c004bc0408606001c2c0000708a00c2198075403100b15260b0403900607042c014030802c640e02d4100c6005001380c0c010300440c0015400c04c2d100404650258042d0800e8810081d41c528078000e00b1010f10005003048456182d141c8035102c005225034840b82304850265500ea590054907107003a00014040d600e0313560106010768080350b0300700407404021081ea0440d40c05503590075a60340030f01c0790032806801203800c0503000706018800414002d80f48884c06080307480c246c00900c01482048128003c480c000c4a016203200020000202d40030817050aa1006600c00d0900504120210789948141041102040c000c101c40000034482d201810f00e00d01700801078500103210b00e44c1800d0814912120314903030b0381e050004590226082020500540414003406054a038185903914001030480e035061103a103014002c941280b04032504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 10556661 1250 10555411 10555417
    0x303090f0705150d0b0a060504050307050604080a060506010c150204060305011410050903010f06030f05060108030708070f0201090306021206011103070317040602090910031707020f01080403051b01020711030102 93
    0x140042c401074000340302c0d951008484d0300505810b0005070745e0f83d40c8034001e40e070b43e100d0420261203103683e00360320746040c90145454103d154010701c0c4100d00c1800304112a03200000c2c0000d15a0b803225000c540781c0c0303d420060b5890006220014100e11046d9030400203890326501400489016a5050055980e00c0505c08555030090140540000c440364080401500440c0100b12100c1e020300009002211002200300702c50880d003003240c2080301e600c0c000043c00410400180500440805175103081041d0380d81c2840d61051020084c03140d0b0640302480256802025040c000b560084410340d5500c10010880c000054221825404175200c80620503503203800000380d60346503a060710b0310045d114607091090903500000b0300c00c0380c43d19000c1000000d2500ea9501260003108045045240d807411440c1c0f0007110700d802c1c0c100210440c400e00030200903075217181442000640078282400c0c03603211410101d60740d10440c6c0c0c081c6000d20405d500403600d91415401468518040d5180c10076540d2140e00b01401d0384 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 10557911 1250 10556661 10556669
    0x20a0608040f0b070e03100912050306011d03010b04090b0702070f060c060b03010b1207140616022106090c0f04111219050c04030311010903080c0f0c0a050303090f07 73
    0x7050b07104904000781c0b0040000b0307004201c070b0403c41400d05041000a290002d4051822103154640316030408008400005072102a1713a81403250940c40c014000900c0c0071051500d0740c3c541c00e00c40d029880a43c400f0341c010480c00d440079006203c0340180e0309000703003141e0b010703a189401440742600020b041e404900410040d035803140c5e100314500c1d98649a48020740210300c0300545c15585c8182940180d41d40140d40c00c840c24840001e040410300e440c04801c140200c50000034000c00c410058030706050024803004c40c4c41035040b2056541307100e01014400c0184110451200d5602c00c2c80b040c0700e0b510400045c04621040121840b00b50302c4c0e4940180702c00c0d030340018103403100d43c2c0c400c0c0103d106074880442c0440e80030f640d503405000c150740114948015248142c0390b80b03021880c001002d0091507070000030b0170991000307100240300d0568180d4008268440040c884049804003040030200d180010045650045502c01102d03140c101d103050440d2258020703284961544503441041240314008035150040f9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 10559161 1250 10557911 10557923
    0x2010e030901030b03010e0303040609031205070c03030908130e010906060507080403020918030a0801090c0302070507060e010509090901020a0f08090a1217070206040210030212060609060702060a0c020a060804 92
    0x824807240040d0007410071840019419500c458051482c08800c0000d10301c13440c09918080b0b0b44000f41d003005882e032200b50b4201500d25080c00c0800040d40d41216101840f03507450b18000030020950305001500c0c0c002c007a164044203c000b100041e5605400141606881c9481002c011465503040140c8040c0b00d000401401260148800c00241c944586502d501565051780c8540c001500b03a0007500391b1b0f100800040c0800c091400500a1202c0c91040086500450804510b410a240c948642e641c0c540d100d04020002e10080059103644100284c40501001500c20030a50420050b000d0207904944585400030f0001c41c800c003802441a039849000ba586840640b012600c07980702c0e1000303110922100c20034000d052a5031105800c202c200288101d072554043d0003142403e20402401c59042089403003014014401c450301c1c0e80d8060405a000701c4120742a40e511101e51011802d0390041c04000303580a403010030010340f00364202a821040354400c80328440080d40326441940c1201d41a00d0107000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 10560411 1250 10559161 10559167
    0x2040e01090c0c050d020601240815040b0409050c030c010507020d030e06090d06051008010c1407020a0b12071b2004060905010618090606080c0f0c010510051002010e03 74
    0x18400d9030700c0101403206510b03004490440b6a100c10317140c0214030749060016409040104107030007042c6850520b0940c05030380c0100f00300441c0c50007403001e5005400024811007070044008039541e1075100b1882c503a4050014452840203080054a44a40c090103a000b40200007101810750701c1078044030080c5a0007030418910080c180c030111410070050080d150040d0040210302042d0f911540c803a03542c3c0d4420b20001c80c070f80c0340001140c1640381c041d5001074810380c14210b80707081c080d41008020000050302c3c1d469503121460760001480321901d80e070004402100c00501c012800b46442180351003141d0a454103000b03041d6030442c8081400384200d01030014004000f5582c10941c11150391411820010404680143c54001d864101c4000381d0200d00421580003000000035409028a0001d015404040207060300d4a00e000d003a9042c0105030380030806c0c0c0084e001c0d00a2110209403884458894000c101d185000c4c01d2011a62550b4041d451040420b01d044412440c814058000c1c1f07090034002940c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 10561661 1250 10560411 10560419
    0x50c100219050c0d0605090c030d0e04090201090b03010906051e09040809040f0c05040602010b1c02060708040b0c030703030b030105100b0f0403020d120e0a0303020703020108041104050703060e010902040e01 91
    0x50480003500c82260680100f0042c80020341d01c2c4030f008401300713001c0c2500090341d0400c843c00d00e00c1c188600c40070034000e13000079110440107504030303503894a00d8a0540d00402d00030030a00c01240c48070402e0300b181480601c0800040340003445580a2000d4500554003559804610783e0b96030000c88a40d04905c1d0700c9642003000070002191315000d00010720000e0030114846074224021400d4410310a070300000904081030030811940c0c2401174095410064030119259820b0b0907141c0b11482143c40c020b40200400200a8208905001100e005094204029807074000d01d806503600c81e4442d4809030002410301c103c54580345410f00c942405542e000c50b20200840c90001c1c08111500100d1061001c0c420601000016071200c0710b20104507441a08900c0c006146054040e015681c01080301c0e000f600d0060040c40000d400007101404e50f602401c294100b0303966032801002d00f152101846070800c0c00d05040c4201d60b40c05401400c251901003101d5000d80c2e032161140d904074000c1303215070802c41c82c40f180104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 10562911 1250 10561661 10561693
    0x803070b070f03180f0308070311030f04030509030f150601050c0607110709020a0305040b10120b040204090609050303060a060201110703110a02040203010b0c0607020303070c110415080109050c1002 87
    0xd16024280410500013103801d50b026081c10503801c0d5000701d00317142c1d00e50030503078800c02081e03004e60706050405c00c8116032090300505000041c4076a01d040166000f00782818080c01c2501e00d007600040480350504014200030761201c40c035021000030180c00c030010400541c080c2c001d0f280c8482c159002801155070790001181d45488103c0301060b940108007011565101c0d0b0300041c603500b00c3c0f1340c80c00b241a082070320300741e0140c810080030b1110160121000384240030401c4026010940c001c1c440c06610703111130000600038040d8074801044245081609010054084003442c4220800c0350018149640c41070168240e42c008449209000000c00140340000d000d507100f0041d0a00c2e600c1100c10611312507000c1800c80c0e100b170300f03d00850760001c0f8852540030410049a40e00080c0761010394114100b50001400036013615030000c00c51a10b5103d4100c0b1511168480680013100441550b980c559440d05a070003404070960a982500800b012003509040c4403180890583c055401040040100a250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 10564161 1250 10562911 10562927
    0x90601030b1f02070501080c0f0a050d0608010c09031203050402030606150409020d0203060a060504060e0103021c09060209030d020a11010c051c02030901090602060f0109050c040b030406020703090803070b07 91
    0x907034410782e40601015002441601c6095941e40c1e0340050100034101000034150000044c0720b00380708403080203000d0360080b41005540f0b118100c2d0a24603220840340000401400c500d1300648850344c13821241c5070816600c00c0c500703011640585080f12070015081000c50542d00100c4019401d0303400480402c4660400c40e91101880502040c50b908042c0c0f80c000782402e90740038441822600d6000700520125103000e4a50000505040c02e1161901e0300d031800290008055a040354113050b030209080710079055989800c0702d6012800e804010400309450300c200250807a14806000344105100401010300008203418025088511100903503a04801141c3d02610700c0c0c4100c40d2802400380760070f402c680c420b101c0c1000300000e80243d81c6130100d2070001005805581e010b10110341c0144180400b074400005800c1c190341c0c1044c00401c2c640c1c0c552100c2c1d44688941c0c3e1060010607400006c200c14006981d02070100c09200383e50300c00c440396030b65140c0c2c0d81e240110b96010b042c1d03d18580210f00854090010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 10565411 1250 10564161 10564181
    0x21080a0302070803010e010302030c101202030a0905150a060f03050307060c020114190c0e0d020409060e03040303110105010503010903120f0b06071a0a0509070306020f04030c1d090a0209060103 85
    0x80076181090940d03a40e5040e40082e800b211420040d04014070844c503041c003440840340026030304044403056950000b440c542c1e8500240325071a600202044044a480c3c0050011a800500303c900400042c1010000c5c120200c585454a034a00700010a42c5c170f1100d042101141d4000009506080d801d0301d039000141540e14000d01503650b205800282e082e0702182c490301c03540c10b603c0c0000440d41c0083d08d07002617402c0c0040301000c003d00348009054958800000c0c03103c440e016500080c0141c030905c0c0a4005004216000700ca5200100c0c0000815601403840044502c00500038031540e40d03100305041c2622440c104c01004203080c02c102c00e062100301d80c07008103052480c1c4404070300f0341003001c041052039014441c02e6607900203140c2540c49a510141400e03810203a007880810142c50b041c0e82c62519108240001040c1e150005092840b004070b03c41524091a0001c20039450203540701055901c462040030800c58241807000001d4000c18041201c80030141c001d4009003482d030b58940110014410855 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 10566661 1250 10565411 10565417
    0x10c021c020907020307050f06010302091305070b0309070501020f011404030507051002040b0a0e10020309010f02070e010902041e030206040504111204030306140607020604030b09120a0302040e0121080a 89
    0x1031000090395480c01214052110b40d0007440d03580446040090815807450807007081944414010801a10b0700d503422540400140311241650140b490001d0a195040d485400070f51030110901000310004181a42124426021143c0310891404410b098500c032041524204200394000307004240100c005081040c0b1800c2501d51145140304901c08907009504124a000800318900160b42c0e005010010550790845112054079a229402543c0344100080319040044114100103142d000704554005800b5641c1706840c15a11441d9481c001d4115208140f460640318030f1000c030f00031050704c450050f00d8019142501c0e0904250902020b130481ca00c0f85c4401c0e0300d0030494100501c18200007180654882d030b401180080c0303001040040410700e850f840780b0503082041100f006946440407a02100c2d8001886038642d501e1984040c107081440349984104e03000001d0848415916500034010b880105000c000c2a903203070400c02565819101c0c40070300d941c2d41c00c2041e0011401c0c50000d0088001c0600d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 10567911 1250 10566661 10566709
    0x60d0b0109020909090105090a02010e0402070c030b100b0406080a0b0111011a090105040b010c140c06070501050f0a050702031209100908040503070605070c060c0312060311010906050405010c02 85
    0x56980001240241d1040035030a41c085043c03200e41c90031104141e003040d5050000e000a082050701071f6290203a40e07a000f0306105940c407440417503864a806590344240c00c19058107400395a070501c110340b2001241c002d0f8820841110214908103aa001d40f406c0d282d20340c0d106007035596401801002001078403402411700081c007913065010b5509024240b1180e541003034601030560030f50305001034014103030080f034411410100701c0352040c0d0b888031b0300c00d003000d411030f40f0280351452885210742400b8400c07000035041880041d40e80c09120054210302d0240d058054040701e00d9903040c0b031b00411102d0030307202c0d600160010844151000c0c10031610681014889040d41c0c4280d280070074500031a1800b4408441080c2e000c10104800e140c140400310013403100d814050715000b02da030345040340c0c61064000c1c0814402d540d02030780f0500d0f208118100751801208070800880c0d40b21300303144a1781080070240341d0008245000100d2081c1c407950a850440c1d006840e1214000f01944c200002d440400f0082400300b8156 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 10569161 1250 10567911 10567913
    0x10212071101060e163207060e060f04030809060f0a020c0726010506031605190b0a030506040b030c010206180a02030d05030603070f03080304111f020d09050108040804050603060d 79
    0x84c01c501d40c0610a0b0401900e0b0031440c00002074520303040003000003140d200b11803590441414981001d010109000c88565481c1c0b01031400800502030807644000da0300c02d490802c20006500c04915000c2c0340240c586110a580e9200c0c2c25540b44c2044441e00e4105030f008001c9604035070701b600508240d18a140980385440c0d20707440c401c0301c1680f0580111a0911800c4020310b41d10a00784692a0005401e070080c02ca40203074000041e0b504c802c24807480d8011640003080d0140383c8100842e80b4082c00e411840c41e591043d1040008000d000141d0300b02e0320803031401101c00c20521340042c20f404420010b0300035023950303903d0000303441e01041c0c2c4426900850017005001c1c030042c1d0b002c0c41764100d4019661102c81c2c40f0304000050520340190f80e00141ca66190310f2505201040c40304080d0b9521961006245001c101d500e00801c10b03000002d10b602010302e052075054580030b03401054140030b40099a80700030940303584200449030b440094070041c14a0600300300034003460614000039588031001904942ea220b2807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 10570411 1250 10569161 10569179
    0xa0c060c0e01030f05061e01050403060504081312030807110a02120f0705030703050c04020d06120614130b060f0105040302030303010815010501110c130b040e0304140301021207110106 81
    0xd50900002510440000141e40c0c00d4400d51a44030324a1000700505c0c076250340072030018141d80e446084d0614400f407119499038400c01c02c9901541d030100c03050280e820f05240842c100d8101d00c441e444105250031020a1400401d5082c04045416035201d503695160b81c1300a030307040141800f40074010b000b0404c1420141c0c464820303004c050b01ca64401080c2101e16122a24140203054000622035000001e0400c04910b00141641140c0c500b2070300181d07541903040a0400070300541e4055507042c100c82c4030440600032503601c10380e184d4205a20f104d60301d503100c40d06403d62200000008115590400100d6000d04000b0f00325040d802040c10040e242603240e1300080d1541d00242e002c0c01c02503001394805a010710055070181d0043c4000e080c0781070411200043c1c552500e0b50300503800d02a0040c41c412514001c0c0940003000c88000c0940104010310010044540300d41c0540a616091548030f0f03c01041c5041c148200c900040c0f0303003a010384845d110030108079110351811070341ca091903407245404540b00d02c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 10571661 1250 10570411 10570421
    0x2040b040e0708030c0c01030c050a030509030d060306020c0c01020303010605180d020d0c0311010e0d0602030a09080a0203070b011a030402090a0b0402030f040b07080c0a05070c030503030702010606140315060a0c06 94
    0x50000210340310700c10000e205e840e0020007807000d410141031412403002c003500281511000e4401d410003080030f60f40d9441061440c004c1410f440c65072410132174000103202c0300e135006051403410003041d14200c041c00c60040e69203210038440c44001980420100d080c18111081c61580458000c058410701c5499800184020351201e8007900c1c2d45811900400410600140009072480b0a00780075000d20b01005c0081c20401c00e00c0c00c045c11041d0000000703402218554071007428960301c51503d5840d8501400020354a40040d602101c003100440008100e002d0f5a825040000581e801a90729507540c550900190b25400351201480740d46540142802ea6a940040d61066102d62201401d61a007401d18880e445005030840c4180301906040c448800203c0c4110750303480f641420029a940090f2034a4071501000360300c081d000d40404018003942d41d030306400803002c03140a0382d15140080b61038007880e42d40d44001c0c1ca00100a200900c2d0601042c104000a4600c03981d0505150416030071686807031090711 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 10572911 1250 10571661 10571669
    0xe0105041112070b07020f190f06090605191115040b0406050109050601090e100906031401110c0304030609021305040506041707021e060705030a0c0203070e0601050702040b040e07 79
    0x42514a039041c1e003044010b110600b1800340060660504d452000012440703000400717805550307401d14484132a01c81181c12035403006034100200045a803910910310684550007600b00007080c507400040d8035841a405d840e5070b03003290045590002007880c000e0750741080f0118450300c980102660749030510301c054907517849503009030b000b040305207850719149033103ca0581001c103c0c0f07458202444580c0c0d900101450580b888103402c115180c60301c294400e48501c07141d0085500c20704210b00441001140c4402c448001c48120007801300c43ca4449503503800d0301518000d0142e40e441800100007145c1c4680001028034005031198134002010705019083d104100c4064540741e02c03220034402004130105005001c400c101447c5420038800e0340c002400c2074180300322941081c84480b070219880d07503007404a03018540d026040365034441454001030445218034500380d1007805980000140f414130701125070310540050b0349083c613103100e030750030040100005c1d0f0300c01da0803942d0f8628410101e0020461a0050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 10574161 1250 10572911 10572923
    0x5060d060f0f0311090403140c0109060c09050d060b040213080604110402030603070e15100f020c0307030b0c03070e03010213050f03030c0a030c060e0d21050106050d0e010e010504 79
    0x41d0074100a400a0341e01940b01d680c05540b0102c04101140110b611104822012a2891155240d605089980f200900c0c10507011503400a551081500154010300c1040e105aa081c01309243d041030540d100703021441603a0700f0540c004103000000d030065204481107280140018200100d00300190f0301c245045e00b04103200e0b440f403002c2c0820712802c14100d5140d5001144c081d80745281050109490701018803440c030150711030402160742075440c80902c00c10440040d15070913014129007401484018a40b80d10f0000d401111070f06a1242008a440c0d03094940100345107185441d141000300d02d940c002841c1d00204441c99035038802c01d54084c0024544019948181200141440e080100c140d00d0014480d2013035004121a03500d1401c041b415442843e014144400648046d0800a000e01845407000210380540080304000c0742d0460750301e51520f0182404c101c40c11b142c0106480c1203a000f0700410740454403d010030394000240d40c010300340901c070060012030810740302c140741402e441054408980c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 10575411 1250 10574161 10574171
    0x30b061c151d0601030213151802040302091602030307080405030c060a0b0f01090e04030e06130e0114040c091503090506010803040311090f070302071103030c0a050c01031112090705060d 82
    0x40c00c2c1c1e10081c0c038094010402410042d490742d03000a030608203060340d0280326501c62100444070741c055000800180344060411307182640c074000c070200a602c40c1c00200c0c4140040000308000302064084440700240a4004610790b1b01c4400302038891820042040b54a40700800c41040500c2043c00b420780500309541001c2022448101005900e0f100f40380082d04001e40400e08100207850441003540003a01400c3c07006c5400c00181c0411100d02c0f82480c001c0350040d40c0500001e0542d20842c040f03040f101c84403104c0c540320440404101c15112030301700c494001002010b06028200380540f000c00000d9640c10005020140d90f600c080c1847c20907804002ca40d00081010420b000d845800c821465004480c1c2c041c0c1403400203155641e4a2000e84101d01701030703010038100100804500c052402042c0142100d0b141c00d0040806960342d8110792003160b1a000f091000601e9500030300690003040340301c0c5241d5090040300b00480d95455001001c031050341c46500030000b010b4841c08000c01d0344040107540454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 10576661 1250 10575411 10575431
    0x20601080c010c02090a0f0902030312040c0501080405060a110c070f0f09060602190201030b130c030f0c02150a0f0603080c0f0d050a0507020109050901090905060c04030b061c15 78
    0x400c01c8000003a00741400240007914006a0712411840d510074907030724000448581200307100004008803171000350140310008296106820a0301d40505c10b5204240b260113031612100111010740060f00d00401d41e038000400700d0000b4180d608040902c030910503015003015840c845851800f85194814404c2650701c1e00180070003103485044401404070130100384902071421034001e69617601c403035020300c0c1844400c0010303085a100b5041510300340401071840700e020514049581c001d010f00321120000c03910300001044100401c0c0140c0384490900c1d0003500c0078010113202101d0740c40d001011140f0b1281d880401c0b110600c10340c41040d000d540249516070301c9007010030a4070310b41070b4481001c0290354840300300c2c014140c0c1d0000441d90140c8a600d001610740c00c0c1803005842c0d9040300e070803080d0700647d40360022450701d51a41c0003405203030050080318400c0c1c40c1e00c5c2c0780421910a0740405003045050034000b6065040042e02d840c80c0c096440c1d0301d40340c403440325140d40c456040744034445400c0c1074441031400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 10577911 1250 10576661 10576663
    0x40203010f0905010905060a1a0712090501030f0606090b090d0203030c010903021e070b0a050c010c0201020a030c030b1302210f070e0913060e03040f080a020114040b09040209060d020a02060108 85
    0x24058000c03105c042106043c194001030002c51030340300c6d12032055041c00c0341802c41044031042d140055809115a59594100c000103050800d143c05200e001030710b8100f401c24a80c05034044c080880f185600c8820385036007400d9149820750301c94031200f074001401d0b140c3c1d240161810801008041610700c0000740801c0146030003801d015880513045030307220200b8030161400e1004602a01224050030034990344240800d81500c0c14002c10414180700d510b45142c540c122034044d001010312aa4644e800c2041206004090341181c0003883c0c06900141c2548003001c0741c101903401401e6224400c0b400310127503140c4681007154500f0440d100c05071101480f0034040041e0300000d070580040c10860314001c00c0d1408100c0d0040004a0040180a41781c450130320002c200c0c010301c100c0d00a007161440607044140c40c1d540d40e0395944c4451204900143c0300d10004880307404a0b01c20b40e0250380d021a02c140ca800812070800002e500711810155100408210300281303000d01e44020407140320540c001d0100e5624100d101c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 10579161 1250 10577911 10577921
    0x30103030e0108011d04060e010504030f08131a0c07020a081006050612040204110c0d08011802040506040b090a090501140a0503010b0303090402130b0c0a050d021b01080411040203010f09 82
    0xb030501c0b441200510600300b040c0c4502444858210f600492581da50a0950181140c04c2040e18154a02400e12003419841901c0230560f15054070b840a41d51142d80f1b0006d10040702c0340700a0040382c09400c0040c40700600300505030700016002d401905100c4c40703070009881c1c8446c580c840b20007a07120000b411010700c085c1c01903274010001150140c2c14a07590b1801650b0f0040d000707000a10403039171a503090040c0d640000a42e501c181100f400c81744042c0000c107014009038400e0040b80620111203c035000310b408940202c1d41940c4001e48150304091034200e4020264000b0465642d1025035101d0204000c7d51501c9018021300400ca03084044042d002c05000300200030341c01c02030003170741440045800e6481c000220703103c000003610016038449425030300c0e409810ba503810075100e4003000941d00224040009085440500801c10307510b1941302c070340e8180d9691440303114212000f003140c0341c3c0d40b0080d8012028180c0c010b009143c5443d5580d203c1001904990003600890303c0d448165006200c140507502c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 10580411 1250 10579161 10579187
    0xd050108070f03030e01091a0406080603010203010501090501260c1801080402062502030604030203070209011d01030303020f12040c060905030307020603010902070302030d09060c030e03130303030e07081203010303 94
    0x903040080c188a115a81d0b0055400090180b00b090300605003240d01c40d2100100502240c4500c02846030b5107010015550702c2031003140d002a510102042140c581882100e04a0b181616030341005880c1500640d810354009000c0010342c00c2115106c0c0307945a220810364031400350542e00700d81c1c0d101ca03148071005552000240c3d604000300f1004000040e2249011500051100701c410005903200103240e4035411051500290076004800c14007042540000243c501035108071030954450f80c80303541380104410000c0c0700b01c039007491540c0100042030103a40100240344031f18000603c0c1c0700901c0c0398024201801c0d40d08a401400d00300040101c40d521401c58800b80400324041d51030900b03143c0000c1e1050206029004003035900081c0c1004241c000c1040b100d00011580086c030212515080c0f09000702040e07904a0301081c10030b00001d40242c4007004075042d95005026503001c403400c6880407001010400c1400741e00d0b12176aa0003281e409003c1117800000c03034084001541d6981940b400500382c4a00c402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 10581661 1250 10580411 10580413
    0x80d12050708010513020c03040902130b0304030c02090c04170c04060602150411030f0a0308040506070302031e0621030c070e0613020c070302040608030a03140712050603070305070b0d050108 84
    0x81c0014070750310070812811100112101910440c143d89100d000b0700c1805801d05451000203800100500c4540142c44400f20000c0103040f11551080c2c2801144012a0003c0004100c28448001454148203113038000d00b1904000742020341b03e04c100321100900d5501640c0380c0c0d02c0304010b941f0b43d242038010301000d0b00c42031020b48030910500690419900c0050310040484c8445034985860b034400700038100c643e50000c011500b644896007000b03000341d43c00341d8041e0b40c240903c10011320440d002e40226402203c0c10038480c00c01c504407614050400d034000e09000ea01081403201c58800350329490b021903604000c9800342d40d50307840d5010b05030f1506515a120015000d0341c0c0d4200010340c0c2e59403501480d138030b640c1440542d851800406003402c2400d01d40009600038546203011401201c00006020643c006441c100172010702d4801c29490030b031048410b940010a0001c2010b03030780201d034010503040013018084504041e100c0c2d03210b41c180346243d0040000c039078000ca40d00e80410128020a0f0040150354 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 10582911 1250 10581661 10581671
    0x804180609052502010209100c06020c03030106121a010f050d09020a06030e010f090b0c030405010b041104050f15030a0e03160303091a010e042a0308131a1206030f010501080d12 78
    0x107c0414040301e8001204c0091100b24090901803100540407600811a0001075030703580d40c0c6622002c1c00c854030700d802e0241114688440c407156030782c030802800c41c0c041058491010400150504403682d900214a032110b880d00c4003d144010780355440d10790040c02c0e054502103144d031540d18540d421111a840080019803d010307168011606400d0b00c10341004510304003a42d01c6d900e80c10000c1c090003e070b500487e007281c50402c0d807081079002c541c054415500200d40c03980030031400d10100054044015564035040e241040400d12940d103660100744080c0051007940e00b00a200d26101c0c1034074602880950109459200440c10001c1281481c031444c4183c120700d0b503465060900c62021248003d1000b420000000d03c01248805000039820640039160b040100f415141d16000d07006810020364502540d0400c18040380e0300b26003290500c0e400d642d140c0d40d07505001c90811044ca001801400054240c010310f01c2001c01d1341001e0003840c1c0070b400c1420042014101c07980c0020409000e80c041c3d841c0301c2d4600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 10584161 1250 10582911 10582927
    0x601030807020103020a02070806100504050702010c020c040c090306020409050a0c020609030d0507030605030313030b0601020a051203040c050a0b091806100804020a050310050f06040908041806090525020102 91
    0x1403000d03961035a40a280050320343e904007109a240080940161070184a61020050000d255031500001e482042d1001d000d141c682e0744c0305034240c4100940980258000d0030f060011400d081e44000da401c140c3c0d01d0a02025a640d854450032a40250031142c540b0340c0b100c1c10019422282c0c0914071980425200070036861501845d42616030181a0100f01c0301c46d1103c001c503503428483e4110401900d0014103a0f07541c3c2c020b8905d06505038105101c1103a1107460000041c1c419030000c107080d40103680000181c4280403d68412250035403000740101da42c8801181e001c10315403a2025210301900c0403402040d81c1710560030411001c0c0500016215101c100e01040007a580c0700d2009200a5010342d040980040c2c58a02c00200742406503080310f500740c460100c000d4150384150f088640900018600901c41d5240c1005000680c1c1195801a281050400041040b501d80162102c46140c107000001070b016110f18150707041d940c0644550310280407019405420319441e070b05008851810303000031032500e412 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 10585411 1250 10584161 10584173
    0x2040f080f0a03050417030403060203070507020307060201050717040c080102031806060616080c010f0c02070905010f03020303220503120904050711070504090206120406092102032a0f060612060103 87
    0x356000320101b800c00d042201c0c1d545030081055030007456100320300f992a03242c1300b54003d00036082000c4c01c0c3d102c0d00c11141d0010b0203a006200b1076000746500e41d5802201c0f0003810076000302601c0540b045410110134180019180e20a2010b54041c4146040c0d001d070542180c044035183c10009002180f0410040004210410003500c1c90cc0d90b803540181d03001c3d211844507101500400b81c205803204c0300750030843c030080070582c04a950019149124400c000603600c1d02101c1800c15407500009405500c10000b200ba0320450104812082282003082d01c0d01984803400300c0d08140741c03056241802030010403415950f26007409070070750100852620344100700301c104900d135840c111442850b0003140d54400e9a420340d00d82d001219981000100201c259040514200d00140110030090314694075034405064100f8903454038a901403201c4d40194108542c202c055001541e00c900007000c032424030224a4440c0ca41070051000c50070490740900154541030061005110700078103502c50581060f4010300016007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 10586661 1250 10585411 10585417
    0x1403090906100314010f0f0603021801050306031204060302030406061413020901051605030d060e0403170c09130b090702030408070b090609090103050a02130501050306040b040c0902040f080f0a0305 87
    0x9401c4607038200964041c64140c001346010780da02080040340c50000f00c0d07142c01e100c0c0c90b40212460088070500703032550754074110101c0c0501c09051800030200d00d440141c940c440c0002c1c5402c00c5009041e2011200d400071021103d6019501030300c0820340100420003070203000e219400c002c0c0000700d04040d00407001000901842501c0d40b0780500c0b80c0c0e02103100d07003040e480344090f20180359034032505000c0003405050069032078000c0c00051403442e0401c41e000c501541c400d0039007801103515455083c0c080314100e840d1560100000c21958401e503041c0b05015031035481da8501c1080103001c0000140000c42502444003050004100c9400e55004203c20400447d001800604440144850313a031141d00440004400744544503a1036448a038000012051200118401003614400c4415000b2100f2503d20101079990902c80c182d810f40014000030080750030005c0325540284a07171040c401454840b0103c1d4100d03042500325840c00f81040e502440a102c080203588a5980e03104001d00d00b5440e6035030010705900c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 10587911 1250 10586661 10586671
    0xb010e0609010f05090a06020a0c06020a020d0b070e0402030a05100506041a090303070c08060709121a0901140702070609080102040308030c0c0304121203051f060e01020c0907090314030909 83
    0x10902d5040700c5914800c138196a03c040006002d14046a41c0d10002559010130813410340f40401c03010000240640000742000c1c0c003541c0a01401012005a25044541003004190354180314255014042d01e554501c001c40c440d4600d228001800e0903e04141401030714507070030450150604000074441440c811100302e2882000903030003992000b0b03d00100f0308500504c44010b08600c1c0342500421000000700d007092040303142d950307a840626511104d9040c03a0045a00c0680110400550f01c1100c01710410f81540c420201c400118030388030381031414181c81c3c50460b0b8100043e0040c40e810711003941c0c010b0091008141400096003058150340b03582c503c51002800107880b2440c00121100e01850074000c1d1401452020f0041d1078161890800c4c1c1e0f018042001d500c00004e260500098802c2004204c501c04c03d030f40c1c080445c28507030802c00d09948003c03da01c502e505510810848050569800000714403400c1c0540e41c3c400003d203140385c0b00c035241008021030301054100b481110101d031209000c09500c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 10589161 1250 10587911 10587917
    0x210105090c130b0304030203030103120c020105040603050901090f050706020c031204050d0212010c02010501090b1f03050601030f050103080a0305070801061b1a070c030e030a11040b150307020c03010b010e060901 93
    0x2d580e94040d1a401514180e100745007080c4003008000c02c0c507801101450480b4003a00540c40220389040c2c0c00c840307103941504000e001c61420321040c400284241d100c5907210007200000a039244550711100c0443c1e450f144201c5039075014034028400b040d03051001064005059004004d1091070ba00c5d41c0c5481d0086000c2c0a000c1d40d007101805095594400c0e8141070788026200070000c0c4c0c4c3c035805001307010304400d006115181d4201801408182006281140080c004103a54123040350103c07030440243c100684041d04140d2280701683d59003803680f08481c001c41c81121031603503442c10203401909030341005204009000c00740004214441d04203540e1840d103014100d0010702d2a9040c64601c65115600c0940341c0c00d0600e8108020205801c0440359012034000d441e013011400300c1c4403c25603591282e80d4000c1c000500903102c2c01d110f05240d00101d240e14401081c5820000b50402440100d8000726200300040e80102a52030b07040c14288540e0203240070a207000c00c243e680100100398584185a082810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 10590411 1250 10589161 10589167
    0x4050a0e040c030b07020d0915020a12090b0a0306051306080a110402130305011a060a0e060306030f0102031021030f080405010906060f0303020f061b13030209070302210105090c 78
    0x2045140d5520b071010315484a524182400d02d80002965032044208082c081480000302060784204001d9500701401c3d030364003d000e50005c5556a000c8000d42104c0482488140301000c1075083c00c3d0340207020a00140d541c0043c4ca0f6281c1020026400e01107030150080310b140c08002d0200c43c3d4003040d0b085100750041460034107140303c0e07001b0038000e110700f400c105c40d050055a030100401070107410903810102030007820f0301d43c80300d50710400c6a91300c07540b803141d00400c0707000310340807114240706000d07591150006042d68030030300489030210f003a80d0045696a6111289280074030a041c404007000341442040c203d00040010796590140c003c04484100320240b082c00300000d01082025000329904a500c07400510107955110210b002601450004401502481807441c48012000a03441d11030305c0603804946450b0b200c60316400166014410a2000034081c00001c40543c4844280a000e00318595005a841e1f90155800441400c0000e41030441181000100801e035590404550403001c09615103039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 10591661 1250 10590411 10590413
    0x1090302060c09030a351c0b01020303070f09030b07111002040b09010311070c081b0102060f040311071e0303031410030605090109050604060b01030606080c191403130c060504050a0e04 81
    0x60b4100340308a0030039046d6440340b4001e00c59140c1005001d00b0400c180328007289404004550041e00e99007112507006038024400650741c0342c40f07260f2200842c1130703504003940c0300da40b82d4958195003102214105c001c940030020901c10080200501140406442021400c3c1401d00700c00d42850300c20203113418109921800c0c4410110408421150300780c1d8000d9480403010b40d81c0040300d440741e451210141d00030000201ea000380307500100d06240b0508500ca00b0244569460b5000e4660b1001ca0141c0455403040140109041c2c1705103601400d002103545c100607070146903103001001c0e2401200c100340000200790038400e50710601807001040c0c90740488041203d5440c5810940100300040001d03085100782c000340700c00d0192661041030503140a03601808002c0d1500c1c0c083c1c1700703181c1c2078951641107142004440e11101d59084416950421480c0c00c1000c4030401c04811502e4200341c98400c1e1052207000d1020401a840440300c00402039030a1250600e45810001110b6944070300c5103140c10004100060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 10592911 1250 10591661 10591703
    0x301051009081b130c020a02040506010504030b04060e03190305060a09060602060f06031609090b09010501080604030503060f2206090501050303040311060408060c04090f02030411010c060b03030c01090302060c09030a 95
    0x44184c84c0e400108028800060000941d0303034207540340681c000c81c40c1c01d0100b009035218904841c00c0d83d03000341c1807007001c0d203071580d62400a050145240d011400103000761100c005110241c50900310583d540400e007424030700d041040100040d03003d40c1da014508001044902e4010429650000301c1004000d0255106800309090400302d0346d0702c0f84203054035140819038003441d41c04080c81d1801120090f0480d81e80407541c500700c5030300f80034681c2d0035801040000c0000344200011640010081e00500c407521004010a58000ca03000300c0704021058a505007003220365620a280007401100e101348a154545000300c0d450f817045010181610714080c0300c000719078035201c044800502008003101d0305c600d4800301c2604290014040c44403400e0a000321079003054058020350f4001c0345c00c50b1f0490000702a1700019220601c2c407120490b00113032a522440a01da038140082c0042d1080e8000105100c0044e01c1d0090070800c00401c054140300d800c0c04190b40b540c500003011384000c1d6020f911440400301d010151 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 10594161 1250 10592911 10592929
    0xf090c04020301060906080108031e070311070303030501031202062809050304090b030d020106061d03010b04091401060e1009050405030f03010605070c05030114040602090409080706020301051009081b 88
    0x5940c000740004000035403e0b90064020046801c2c560b05c5048990b228021191a8410030841c0d440d60034003080454400c40d5204001e03c03c251090604803030904003818020f003000782d568425070100c1e640c0c10042090100306500007541c1f001503c0038141030305e09844030f405c03a0b030000c030304010103012540c00380d080280d543c0c0e2284c141241c015003140e441c4d659414801c07028203005503006000707004142e00b2514860050048100f928425120400464440e00003600b0300c0c0030170000745c0e0745592a42608002d0303031128811004014001c1c80485440c1501941b0fa82c25521207901c4800341101c1281000618150003580900351b0380504c0011a1603203031810658518018000e0350070f82d29000100000d5940c1d0403e00810b40b45100d65844e600980d0f80d80c04042c01c80304001c1c070703500407c03449000040001d0306c0e42d801000d0b4008002c00c00244804a03458902640e0054003045078010781c004014003892412071000003024080c0c0c039020302158281880c0347d4070342c188a4140c41c0d00c9403c1d000c403656a9500d07540b0b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 10595411 1250 10594161 10594183
    0xb010801060c050d200a0b06100203030103030815060d050a06031704031106030903070215040501090b0306030604030c03030e120304020f090105100f020a080a0503100504110403030e0307090509100b090402090f09 93
    0xc582c06c19200d810180d0082d5420744007103100f58035601c000308002d40040140d030f0490b60182c481000558991000280c01840a900c00380d1102040204031140509481464000c540164001030b503507056260003c102c048070039105889403403e03c030030000a00018804402010145d42440e100d0f19103c81c074900d58051030f03600951010066078043c00c24544072000c1d1040740c0c0260303200b00180350380f803040e103060344000e6034040c0c0c240c0c2281d40014040380c041d407120700d4200c1c420b1900103200c180622001e130070844040e00e8007035641d4000007404150b1400803114072007850100c4000b12603506d0030700020131150207040700b0000d03c01d100721400a187d000380400c01b42c0c143c00c078031000c0d9100d0341124010840d86c0100e945030000800b2000101c2c3d00c0c18603124a040c0001002c248510301801c1d503e0541c0c40c0c4201c150b03800d5051140c0079010441e1585401428010f0850100030440c2840d00c0c0b1850702944ca01340011406460f0100800c80560b8800d41c0c207a410a000351007540113901d8055074681842d04000e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 10596661 1250 10595411 10595413
    0x60a0b092107180b0a031a070c050d050c0f0d0504030f08040509070806091501080a0f020c01020c0a20010905040207030c02031501090c0c020d03050f0d060305010b010801060c050d20 80
    0x40001903500c43d100008840c01d5040c1801c0202400b0701041040100a6000c080c000c000309021400e4440ba03010141c541000d8036003892899a07415550700ea2600c008104010b0018078041640903a05004101c0341d0040e641708800350100c061843c3c8000d00314000c510002d481900d048031081c050040d41e0048801a0101a0461203203141c01c0b580a0b00d4010b080c1d0360300c0d00440d441c4000442d0880f481c0316a004440d0140d442114903121281300742c014162443c00c8044441d0308001d20204044248020b150b03c80211002e40044985070801d4004105060403c1c140201d81100224180e80e01c5a10003080d50000c40c0d0060b2103420314181118040c0c903080d0000d4141c440c5158100241c14a280ca481c100c2d400004140103c085400c0b007114103e5a4200094001004c00b41010000c5c1c011005440302c000401245420402400d1604040da0340030342c000e8400740d40d0354045144659000c040d641c05000c2905107c49981820f076036a640d1421001d00ca0001c0000c1c01c10421002c2610300303101d40b0301c11a108 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 10597911 1250 10596661 10596673
    0x405040b150d08070302010902090901021c15050904050c100908030706090c180e01060b090117060d02090106030615031109010e01020717010b210604060908070f030203030609060a0b0921 82
    0x172901038001c1c03184e500700364841c0e040d010001e1600e0105008450708403004044840d031070030050040102030241500300560b0f5600080c400704c4c0070380301c00c1c00580c41180540024990100039000703000348e80c2c4049208030308005040d0341c14440000c00004803554654840d5002030300c0b010300e041c9499000b03c140c000042d41402d022041113011210742020b208150780030002c2000b25a00c0c1c1d003250140c4074200b0b003140412030300000c04440024815005500032009070514003903030300c55800105105826001040403941d5498103000385a60001c40c02e4410a290900304101c0a4000401402d402001081030400081701d50320a85640308ac406040208042c03085150107040750354080f4080c1243d02c0000307009d1400810a000c800c000301444c21090f110300409000300343c9498403650041c020b00c0505483d08541000804000f0384401484980d6501950242d500e81c1060700c2000035030720014040c03601c2484986d200384100d01e03002c0111007000710101c90242148442d8208061310445162280085014031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 10599161 1250 10597911 10597913
    0x3010603080d020306030f0102031003030503091501030302030a08070801030c12060f020a0504090f0204060509060d02040305060705090405060306060303031504091b030b0106140a051804060816050405040b150d0807 94
    0x3c1d00030b140243d000300c041e22034400c2c201d0483d5080b40401c8480ca0b0015000c800300700003080c0184020754011691100b5100503400c0d10501403512079080e40100c0040e8000950144200d81c4245a141c204980e403414520551442c1c9405120811502928100c0d1a01280690821980798019483d9070003545003592200b03400c100140964100d8811181070504120440c1140702c0c0301c2c0300311800d9514030b4641c42d0074001c10b1010700030345410400300104c0d0b07161300300008030224000f000414401c004541e40c5554a07088901800f00380d8401502c82400380d8049804d100c50380e503001c01500d0744110740400341038210000000080291146180280940d41584036506800702480c06220a5038081c011302c6040e6640e61008880c808060001110420424455010b80c02d00c0742c00104107698202280104409402000608944141e4002043c0381e200c0513031903001c1036500e80084014441140e08226a240c191178080803030710010f08442c450f06542075800c510b9601c401050b000381d500440c01e95250072007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 10600411 1250 10599161 10599187
    0x503070e0a0e01080f0106050901090c2102091302190e1816030509030a090315060b0c0706080108010903050702040e03130b03010609150e040c031d1b01080f04030c020301060308 78
    0x307003c3d0030b00502820170b0540310107005018040440700050020007e6038a8103801c0e400600d204805402000180115040c484901c001c0384150a20201001030792510740804003c2c002030303500b911200c02c034014090402c4103921102411044140e03414040f4000480c2c200040105510110707044250012000b4000f03400b000c8400100802d410362401c015a8441001040e0340b8080e01c00300078005201046e0500000c0c2d1144000c43c01c404210300c001c83c602c3d80b43e0001e0091908200803240320b0f60b0049a00700a89540408000c2c010102100208022142c6460043c641d02c40c000d40680110340368207040d51190000c00c115500403164a4850003095291030014415134030a2042100040b0580c0c40403a424241901c1816112000c1e00d6005e2420252000e00000e0440680400240b43d034410900c080d00480c6180074000c20360314805840ca400302c00b41030880195464044c9030410200e44100b01008440380002e5030419058107100700105480d10000e809044c207500001c00d006000704021071200c83c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 10601661 1250 10600411 10600439
    0xf020405040f05040506070908030a03090606050d150b090606040302060f0403050613050d0801150807090314010c02061503030322050d08090c030105070207090207050705030d0807140304120503070e0a 88
    0x205ca60f0a030b5003a900c8000d01100c8042c028040c002e0035400c10404002124003035403207400114814080803880c81c2c2d07250005040405242400d555180e440c81c50704280003401c5c401d500c1c0d11001150716054a00381440498007070700803408000e029450016290001c60300c0c98040da8000d580c4001161514034090000c034a402000b02c0048440384600382242801c9801113042c281a65103c442010384030f005104129445403024100c401408030401010001c61750079002100c1118100d000440c413030485a40080c03034040f004080720b000c0d4804921081c0701e5600403003203e0300103078040c0340e044a03805016203040c1042c4880000501c0e51203007904000306581c11509052140c0044c4060b2501d40c1440c00905003a00c10844401d801608080c03010b004032a4164044c00d200b5000c0d100715130f1481e464801107480c103a0150b5032000421507010402105a1380f0070008200841038468440c15410140d03102e5040300003000200043c0000840010b907900c0c071590284108030030040060500710360303d041c0d0a591003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 10602911 1250 10601661 10601663
    0x90303020c060a02070503090409030e0306010305011508010207020a0303050a090b181215010302102f0d0c0b19020706020304030c020108070314040b040c0b042d0312030f020405040f0504 82
    0x40512000200004a288203075205c564121004e5454140f1a40401c0024071108000301c00f0b201e80c42c0d19150f1251000c02c6294065442900005102204540103501e04950b0798805c040d5680104500310050301c42c40e004508481e4981090303512031136540701c16250910141c00c003400e02800401c41e101c01440c0305416211603107054a81c1d4414184086c6d40030f48604029040030400d80c1180010001405d081c2282843c2c04c6040c90002d082090601c84c5030303800c018540745100410641e4100031008041402840f1410080d400c1c0700c540c0d1500c0766180ca03c504402840310007800030305185041d81d001c40d5011542081d51041c001c41d5646081e1502034680d01508005078002040c800002d01038501070310409140021018801e900b513600c5035240c1c4c04c2e0f942c0081c0100c80e17070b00300750000103400508030b00903101800403900500384111600c000c0c150700c1c900b003490070700b42038005035010400300c0d4480e0b5868105c0700341407402050023250210550064072450b0310403900145007040c00040d0f811035604c581d00031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 10604161 1250 10602911 10602913
    0x7030806090420041d030301090605060910080604090c0b0c161409180105040506070f020102070822051002250b03060907020709050f0906070908030f0c10090303020c 73
    0x2038445005001c80c480d02160018028a00b61064030007840d086003400000340c40050000c03855070100c580001141d140c0741018081d80d400440180000183c501500020b410141d030306d030307082a200380001000c02000901d0301d0240000500440d0540c0c5445d04442070b03040d0000c03109685155660b4003442c144d031101f81c40b8a21405020400303401510741c611f5007400c440c2007405c1880c0b0706075004200700c43c180000c0c2400b031111054400c0c044000c20280112071085010f9800f40800346440440079140c50442c0343d1000842e441001007000040e0078030152a01c0541100104401c640240052000f80314290015079100c08900c00c40314541d5400903c091807070081030b42031984030f02021a60442d41c820350240d48004101880091607500384401d459610446501c11102e0325030365010b10404458040e118014030307445290420281d100d04100d0203801516a00d080c40f4502d1921101d65224090250039003140c22001444c544169000c00052072300041100c1d082140c84014a800380c0294882c010254003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 10605411 1250 10604161 10604177
    0x803010306180314090301060302040e0105010303090b090109030308040f0215030106020c01090503030a030216060501080c090c0a02060115050c0304080c1008040c1a0c01020a030902120106060203041a090306040302030703 97
    0x2d40c44182000b0b080456043c1c0b603041d4101300422005007690001d15410341c142d03584210000160790f950144d1034040004d840001502d50441c10001c1c0707403a04982044000c10401c000324042a40d005000c4004c03a501803925035180d480d00d00e40f981c0b8444c180c50001c0d600851841014081c0450ba80003141250a10740031148200c803084015216000c1c01c0c400c0c0c0394150000d2040c0e145003070003034006080c252540081400d9912903070b075810084402c01e0300511195804407a446886042841c44e10f07400041c040516401e2080401000390340304014010440391102e94441104080d028406581c8804c00140a80340c03516102d81c441ca90310821b82000d18032940144c411010700601450710b4500594221074403120444c140045d42c00c903808295225000c500080280b9403042200f0f201819041030b0315a004075843c0d074940104071000800130f104203000d9140c0b000400c040740e00001140c04459010040d048440c4031918100c5081c05404d08190301409500200030406901100510705640700741c03580a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 10606661 1250 10605411 10605431
    0x160905060120072301020604060f1b030e0105010905060603150102010b0a0e060901090501030302030a05030403090f0e1e01060c0b04020d020306040b16050a0e13060801022d0f090603040302120301030803010306 92
    0xe8840414402c05e004d60043d002240101e08250011181441071000120303c0042c101c0c2c980d400c414000c000c001c0029a601515464508203001e41c60040c15651010301090a103640002c41910001d812603504081e038010a0040364000e42144e419240001c05d920764460b512a41c10b81d8101d02140c40d544242000c0e000410115554400d003410399406900840c201074203014286c66540c00030380140c09110380007030300160040440c0800c2000d45810001e41c0341906148019500c100021050078650110030ba0060008035404988140c076103420400b904100c3c0c4503400400d501307900201010f07426011303072010802070200d06001e06000c2c01031a00c0b030b80e402e6441c1d000116500c2c001c0c0354480000074183c068001d01d42c5003070b0f0310200420329038801c0000c01d1642d8074070440c00c82e0300294202c2d10450480085c2e5035941c00711300250245001d0901ca13280b80502200e4580003600c99202c42c4d80c400c000200106007070500c204500d25420101cbd40c101a03803942c40e4144500f06410901c000c8503150300300703800c0c45 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 10607911 1250 10606661 10606709
    0xc0408060c0304111005040504091a100e0a0f0e0604050c090901020414010503091c020d0e09011505030405070305010609051909030804060e0c06041e050316090506012007 75
    0x40d00c29a0800031365030381142d03444100040504111030304030400c01d061201040aa0300c038820424060b10801c503100c003441230014020482d4500400010300d8542101081000c603810284641d4030a085040000340018203996000090829280150080c4201d800b0402004400521007004190407a44503105940b205a56403c0c0d10a60081140b810f40c14442441ca80d4051005142c01002100a0b00c4803a1001c0c9501e01080d1180c400807001a480030018600054001d41d0340d101c070320801d0b58030058544c140030252011005d804101420002d00000080500105105d440040d603408002813091903581e2100001900f001c1c1c8a01d0101c1030480305000d8091650f02c1020744459240e294401c1c555204d4a44c0d0000f0700385090f001c84503005210b0f40d4502c40d6607800081c005400c018001c2030070b54460310540c0402100a03001140254080c800c1100e1000c46018070000321102e0560102d20713541d92200403280300d0f40c80408400240340904025520903408991711041d507420702034060043c1039a40ca03e07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 10609161 1250 10607911 10607917
    0x1309060311150c0a081608070c03030e0a06090b070807050607050a080606070b13020402090d0b0901060605160f0305070204050c070203010c02030405011205040c08070602070303030b030318190e0c0408060c 90
    0x210585a101a91300000108000003519028074000302c00b4002d10b50989a08201e42c1c4100d904491058071200709008060304541c0c1182d06580940d400740100341400009002c400c244e02480025440200d000c03400c000d0600102c5038070726484400d0b00d5050411290241042c0c100104900224644000080c980e082c01416112095080703030b49080b55803166241d04200000403001640c100790204400302c00b907212070051000840c800c81c1c2c00e54051404502c982e0031600d16410220030800d040210075251a8006005124503421445004c1103403260f10382a202c9104120700290824205400c10825208140141c0750190003900203005049800d94101d80f640f06a001e400c0c08100341d14070355040c00903036922542e80544660440000c560700c44030414a000b08a512940040e40f000c0424410964140600c0e01e020400750000c509218240040310041010450090700501540554a2001010603041c0e0300070311544403180c0c55800c144100c145542c1c0300d0301480401e84282400304441100d00411 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 10610411 1250 10609161 10609177
    0x2030702060403020402090103090c120b0906040f02011413090203010918030503011710020408010b1002012307021509010c02010c0503060607060216210e0f01080705130906031115 79
    0x280e00e242c00d045a080100a41000343c4050406507514100800107542e210010040d00c01c807003400c5119519481d18580945006100b001c4030f400c408103005c0098002c14601d00c04a80c2401c040001c880d5410002880d0f008203803012458010301d07100026006034650095050722100402841b0700c0d14211000b036880920120004c00040d41000100944074090201807040480b41060780e16401c40c0c606a102640c0080c1c00c4182c8995680c5100b184c203281021208001404500007442080048a07011407604083e0020490850504002850081c424010030329031020445413007080303040c0907022078000c201d40350f1000059803a0005600d40d05004000340ea00c01e840040159141c4042d0340c0d01c7c50040e41005000540c183d4070f201c0c140c0c0000702e9400e54440540c0a45080460f02c084640c001000400d002034000e0041c0000740b00e8042a903440150030fa8051500e00b0724642d034404407810003811125039880001d04502c2d06001104220140740e203542d02c080102c071210b000d02014440b01c0041d10803160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 10611517 1106 10610411 10610419
    0x3060b030a050a0e070b09060906040503010e0a0201020f150402042003010b07020307051008180f0a0f0b1f060305062704020907030506010c0204050426040f050102030702 75
    0x400c0422203c1944c000b044100d141c591120501d1061281440c01210f000542c41029214842150010071010b002042103001c020745443c1c4500405004a00500420351081045a40066108529a81b84444940948403a404c100041086802090b01051341c8101c13881c804039050f014600034661400705995440c102d05c105820600c440c1c214921603041c804002081542c840403556000c031841c00450301070a218000c941c58001c0071340c007000c3c4611560320003004000102d00002500e03031243c8070782c601544034031138500b0b80014a441030840703021351518104002ea00c207410090304490302810300c49080d100f074003210840a44030849608a0001a81072108600303003021307010b6200001d0302d0204014100000000c140796003450300030f03101c1c5403a000840d05001186450700c00351120318090800d04200100d02c080d09802130f00c40c14100e5074400078006002e500200c11554042c2c1d00034 = true := by decide +kernel

theorem cover : BRFrame.Cov 10431661 10611517 := by
  have h0 := BRFrame.cov_init 10431661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10431661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 10431661 ≤ n) (h2 : n < 10611517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
