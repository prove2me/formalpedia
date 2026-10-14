-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:37:44.907293+00:00
-- url     : https://prove2.me/submissions/bd552c33-9cc1-4747-bd52-32d96923d61e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 10611517 ≤ n < 10791374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 10612767 1250 10611517 10611521
    0x10e010f0504060b03060f0301060314011505030109020d02101202030109020c0609060f1b09030607020c0a08120406030c02030c010c0207050f0414010b0906070c030605011802030907140103060b030a050a 89
    0xa405079001e00c2c900b0100304003054421040c0c03504028111001d182820820300020f01414454101600802d400b03442c0b0a00d4000560144107a9800c041d0000402340d9540101403c8640a950203904940040d1105c801032501a00904c200402d80c103105000307020704000c0c60120f80090b0088650b040d030000d90031044080c10800598005c0c9060028021843d2081c0d02600d00c0d4009030180c4600268000c0c81011208580190341c4011400f4040390b071145412640250b03107484058003103019030f041072004100b0340f0001c12079480701003c6070102407905140c24822001012200480001c600040c00300b0600c2100c203015800034000658020000703941130008001d034035a28444c0461280d0b19202c1000c4034110b290f00003d0442c0c80e8512070980f03a452102c08aa4035204210004150715070713011010040040c9544a0b90598208202002001c0e02411002c000c9200c02d59002c039456100b05410420b440980e0021410f20406150108550355a80d414051076082541d56241107912003040002c100401c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 10614017 1250 10612767 10612769
    0xb01030807150c02071401050705150f070f02030a0813050a0b040b07030606090e04050c060705060a05070c020303031f09020403051b061606180b07080601031104080c01050d060b03010e010f 83
    0x5502c0400c071440f24040040d550308004d226000340c0390440d290141603170b800b441c01c2c0c44c0d000342c115050314501780506450020480c0125960301c0b442c41c032100496030462254030b140d4200c800540042d0324105440c801a07800e503500034003803482d081c0004031041c0054418082e01d102c0314403681035095641400d02c1e00280c1341c0b400400d070307004141c501142009a2680001c4140c00c6030010100000e40d601e40b0300700142001d100340d10003030300464001081c03010004002945446111076101c200015151840112044506060081d606900c10300200d84550345503103542d04411a628580115550307269205820703600030b40c0c800e5400742c0000b80500e08120309822040596542215010301e81542205140c095080061000d0200c6960b00245a5030003c9101004881034018044511600c2c00c180c000b402c082046444900180c203000304441200400b9058905465200c0302612504100c1001100d4039000645100f0f089501c5c0c06001039004c0e1190004c501038060800e00e8a86581031040400c802022 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 10615267 1250 10614017 10614053
    0x1060608060f01140f030403050c070605070206040e0603010605090a020c07080a0201020616050c0102040e0114040b060a140f0406030c0219050601090c02030714011d0105090303070e030a0b01030807 87
    0x82030081101e00c2e50349030642c07a1084000d003004a60712452100400301da00640302d13000c0743c0070000000e0009240e0000c0c05040880c1e600c500304c6070b1032034480500712814050181c001350880c4007404203015200622011641c85035021f00001541a83c42e00025410001910301c41c5015500140c05201001e0500000e4003400700c000081882a000c0d9000135940c50b0000c0049031003420229220502e18415411201ca0a03400750081d92915220002220140b03001e01c01c1143c1e188400c50310703c100341401d004103201840014000350038128629010b4480c4003000e054409100020000d00c0c0a0441000160000e495580e83c0010201d08860000e49455071805c040c41800cae0744010503900081e8006440c5064502804c40454000e88850f8140d2940c00b0f0301c100101221b07040d1900c111010f005620580341c1c0b00c0004865022410045400360881d1025204058540c000300700050744103000d5615150400b00c05021a0070200c0e2949880010072020381080701c030a800040d14505009185c08202101f1031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 10616517 1250 10615267 10615277
    0x18040c03020d060602010917070f0f0317010501020a030210051902030108060103020109120b0a09020609100206090607110703060b010c0210030b0102010c03021204030f020f0102160203010c02031306110313031202010606 96
    0x1c035940f035048240e80c048400f0b0234070000004e800001c000c0302c0c0812030a002d07408034014018500034980501649170381d070840c100d258400720001400c0d600c0080c0c2c4041041c3c0540140c50801e21901d400d00140c01c000f0000c5040005035030f081c1506203090b200440c001c02c45000036258550440c030006002c140030744c0c00589401a8101407602045a05058640200004c100015903030710502c04100340f8064000d400368440440c140030f0410740e0300400c1d518803403080072058480d969600702060320b201c1d095585c500d500d640300300d0b414000039415912032032410b00e0504180c0c7c2911425030001c3e50000b41e40503281d00080c0c440c4c010200c5960240646081480c1e10b060035410042c0801a042884400a00140401404019414140380240030004120b50004025035031205409082c0030074403001003040340250328001c140d0340d149201200b41c0e04183d0011070b10624262a040c0c04030760387c030400d4402100783d01040007000001d961103495140114071a000c8202840903821019007114140da00440a00c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 10617767 1250 10616517 10616531
    0x20411030601140c011103040f0203060601090b0406080a062105150402060a0503071205010f030c0e0f070804140610180603050d211410090c1418040c03020d06060201 73
    0x282c0c00c200409004003c501c205501c483d4001c20880c050040d080f001c5081c000700000340003e0000301c406991205000340e00f01c07400703902d03600c004440c002054451040356200522052000911483c40b041d0840121440410311688591070805201d104149400c810003128080f9400c1110601002c202e40303180003140c141624064000c10003c1c818251028200320b0000000303242e00c0e00441c00c00e1440210080200711030340e10b900c0c1c03210008a1a01003901c0c241d03082000040c3c40601da030341140c400c61020100858070381341c40000382c42102000e40100c41c00450030300507000c110820400244102041890307800300074901203100c0640ea1002442c400180c0c14510140045940040d01c10700c0a40300d0301e8484010f100303021080304410800d0242c9034185060030256590103040f400e103980148044100c242e2155038820302001214616440740c408920308004400f000c0d440c01002c2c1000c2c030320020482508400c0e040c00102142c98031041900801e9000c02e01e0042e1090178440d500c05808036000801101c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 10619017 1250 10617767 10617769
    0x1060c0b0a180b0619170106170a02040b06210f01050102160303080c04080f01020a030b010504080c01050306060706150612060b0702090405031b0c090708011412030c070b070204110306 81
    0x1292070307030b1809000c88650f040840c2090300d60000100071140403001d039440342521080303880120b4020020321441c9609151000c5555604052071800e0130a503c00240030452460307090002401c54011810b074000c0c428462070342c00a0160107184044044034041d00100d19240010344803803c4103030401c50440d401b0322060345600305c044031240c007a41e0305400c0c108242c7c0d40320280c1c842e072840341b500041c0c101d00a03040c54800101054019102500f010b403820b01190001d5001100e5500076413140000e17a40c442d911040d11540684010340d08040082c00c0c0b14503042e015100e000940b512400c01c001c60102c08801084081d83c0902c2d214a041034682e8184409881c103062000c25001e00381010b4400c1d940712000c502041070820403034a805101c00380f0071002d40c00e070305426501e07400e03030b1818103004442d9800051403051040702a41d05844034007240303840044c1c00c03a0501282e005041007c07001c0b4841044515200e20080020b00001c180c990f60403a9550003a1060105540380c58100b2a0400003d000b4000342d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 10620267 1250 10619017 10619051
    0xc010606050918150a0803030103020301200d09080909070f02060601020f1f0905070b030103060f060b030a0209040905190501061d130614070c060e0604110f01090b0301060c0b0a 78
    0x900c0c0d00f15070a4041d01c1e11466952250b1240c0300c083d9984c408100c0e07400099000c1c0100103135040b00c0c004c40c000c01014001030741d09080c10301e03100168010048100300e4540e03242c0440d48140b00300303401804064107219525010509424040e03804802194000d070503400316950420059500000030320140240074200840700380d0319421001110026101d03552000c542001c154004604603802100710340301d0700d0b039408104e80550300a000513503080341019007904204aa0b80100300c2151150b03100d8602d10742c0ca101c1d00000035045880c0030390b4882c0d103454551000c200204a2000441086d009107000041705142c03050840e0314540c40f20a21000001101c082d00c4103c1740c890350f020380c4401034000118020702d004401007101d2104045004458001c0c080825440700c1c6141005100c0c240800c20801200c40c2242d80b000304550041c8501844181c0e03060300e0501d56401c0d042d001d01030501c1d04546489480110040d00240c0103140024850400b130310071300140c01001d0f0f4000c0c200f03400801002916088ae092 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10621517 1250 10620267 10620289
    0x610050a0e010512010e071b02060a050304150e010c030b010207080d11070b0a0305070905010c050c04020c0307050604050606090708010e010306020304030e040903030b0102060a1401031115030c0c0106060509 91
    0x780701003820000e6169009400315001000d208a0580d00303580c64000b02000e401e82512a0703800500c51580c0c4010701a002d0781c80f181000e4009000030300382000340e0300031184c562000f80202c030170510901e040c02658006000b02c0040040005c00440d00d5170b0410300080456510082c000d0441d0700c0618100720f1031401003081d100c041524600114501000c0b1949443c14a1680c400000a800050700d1143d50303505a101d14001e00302da507500da403034075911801120b101555190107040c3da040f146202e0100d2a1542c024a841c10b0541d05490504c909604c03580d0400c44200d03000d0303890b82c0106c030411445103444449941d00c44140d00f420007842d41000c40c440c0c52920305000003400d10754000049010f25000d00d103c000c00040040080c0f0000c1c0d01f0b440c004002c2d00c040420306015203c0c84000c50b145070a0703030049403401c000364420092180c4c61178843c0d8042103078034540c650f000300341500108021180400114400c041030404650b80e500d550034002d084891903070140081040602000040d03030b071200b040325 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 10622767 1250 10621517 10621537
    0xc0e0f0d0201110607031406010f02030d050405010b0307060306031a0906040b0705040f06120e0105010602030a050f04120b10050904030e0105071109090a1106191101020708070b04050105061005 85
    0x302030441071006a84800c1410700c1c2440c240310703040410403900c1d45604241451028420f03443c00c1f0b515041d0055546002c03d849030000758000b4401c1c009031940d203034000c982c020b0150001041720005640072a041102c540c00c1300c0c0000c0d85402c01401408445843c500c031107216180d9406603450001c5905440e075034090700003070101c60303054003103400e00348540156409071000e06560912107a5616000d41600c240409014a0f58100004032074a4041807060f103041302c1494019500c0c02c041701108541c0703580651012421001c0910010800b20301503150001540c3c8290050805410200e80d5200564400d510851140c0800001c0200080d807110340450307110001e0070580e854a07100d1425074484403058420541200302e00b010403071805000901c04501c18007131294690b994072544184a01c5118003840b0b04507a50408460400030b03403080d10707208829280340780018101107076071761000510382c400c04003915101c0300f9006010900c007082c81065040070046130761020004c4224005044c40c0035041b002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 10624017 1250 10622767 10622779
    0x503010b0a030e01060902090301050f0601090b070c15110708010902010203040e04060902031506040e010902060901050703120e1b01081306020a02030702040e03070b070903050325050d0905040c0e0f 87
    0x445440303800b9801a015001c0000002d0080b640c4030148803009422039011644650300f0180450500792034006014000c007011307595422890705003074400103c0d50141a04507080340700c000c40021a110300308500c891b10100d5039101000032201c01c00d0685000703241c0c2c11021031039143c021090300503a000400c81301100c01e107121143d02c55407107081c090005c09030024080e406020314002d49003a07404242d401880340c8411182040481022a8400d08030703040002c009400a804000d0141590b0240d800303821000c1c400d00e801804c00c0000010b0710140e840001c2c0c40086035100c600c10200640301e207420400030306030138030300203940d440c1c00b1070909800c803020213020384601d41c00601003445900c00d00885011540141040c000729501e81da0155423075209580686c0c100300b04201140906200d18800f10489410000131428081c0000e54020a03010b400340780040c3e5502407560400084003400f113805241c0c034648440103054501070038881912402cac0801c02c100034000c00310540301c3e511450078113624031080d02c00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 10625267 1250 10624017 10624027
    0x3030c030a1a030a050d090815040b040c1208030105090f160e190608040c0501030606080c0c070f0602010c08010f1a0309010207020a120501060b09010801060c020a090509010b010801080304060503010b 88
    0x1d46503110010102601400740324070003000d105c00050040c00302c608540d102c00c07403540c2e10101d040e00e0b8070b5010001080d240c0150041008a42080c0c440780e049800303160300308680345da80e8080c0c60a0418140b02101c1808002c80100301a2805101c80d40c0d000c98203030403550a81c50100d4a03002c2d136185c141d5142c010f009120b204110140c035402c0520301e6010030008038821054964002130304041080718200d0ba4008124408505544a07016a40440b10580c0f902492615408482c030300796080401d1480182c459140001508404403039858000c14541d0000149184c00d07140003055001e0503081801c10740780c5402d04003c0440c1c501c02d91a450030b039100d1a16100c0e200c50459501907c104940a507000a0b014004140b8a404200503007806106200812281d030741c8480740d0000b80601c22009020480c1000100103060042d54031450844c4014a403050041c3c65503404003c4034002e4a15000a83d540c000c01c44141d41c1204c015405091403000440c1000d10308036004001e44014051802c0350000454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 10626517 1250 10625267 10625291
    0x203010e041b0b0a0903020a050f09040201051b060a020a020c01020c01020d0507030215070905030d030c0801030b0901020903060a0b180115030b0a120b0f0705030402030c040506031009050703110303030c030a 91
    0x2d1000c06004a40081c541d1242c000d4401444008240400e9206a203002c60002d46407400707440701d2101c1c0c0303c06404003040b40d985400644607071b0011505043c5903100c0145e15049075030300788803403449601c0030b4500507119100582d00a00d071100c3c1a4805055510442e104c912680e000502c500007013906281140d0b54030003a2030100e003070002808043e9010017095003400009900624007000383c072400d4007101e8803840070100071406e40742c000300700d100451440001440403a913440c1445500420f909d00241c41c2050010109151202c1141d241c803105071358251504007031600541c400d0044507440e4404042d0350400c408101d40d14000c103080c0040c0365603002803d0705522034050500082071100325582928459042c40307000d02c2c00c2251600c102008900000310140d02070416240242c1c0c01900400d00c0c41400c00030300004000103811107526200304502c50b400030030b5a0181200d203500c210f024180043c650f25155441003402640c0501c250800d00411100000c0b01080d42c2c0e00095071000031600d001020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 10627767 1250 10626517 10626563
    0x90b0a0b010e03070f0603051b040b070303092009010602030405031207030306080d080405010605011e080714040b07020f0102010207020105032206020408031308070803040603110903030a1e030203010e04 89
    0x402d800780c1600900000042c00c01c40c440d0740c1c2c022120a0b840c148041e41d105201c3d13104030001000401c800c94400d00090140b102c200018209040c4281800100c1c110b064880e0048a206512120008802c1000bd00c2281c200351120600400b020300046041c94107040000e0f440300b044000414008401294140c240f51294200800501d400f80941d4880c0072203a00080456000310b80036151513007007150014065120b401030451059286070340031320a80d04214100c1e5054405040e0700104031790a80300c2181c00300d10f01d00034401402c844030941e0743c070025841403118a0030301e2000f44ac19648140080f00c01f40c4d8100d802c480e0b20044d4072807112100450145035100f40d100c048009860790707101140c007142c0b5200000c01440d054240d0545822041d5550820135a50096400b540c4240d410503c03007002014040d0300098030821800307038590b08044071000401d18640243d00c810000505078804404034600c014003541c02480e05203415840e560414481c505001d074040e100400c003102203440840248002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 10629017 1250 10627767 10627787
    0x504050a080c060a050f160302070312020a0f09050301180209090a0501090804050915030d0e1516020a120f0803060105070507030605100906080601060507150528090b0a0b01 76
    0x1100c66194040c48030a02c0c0c2da101c08641443d41e036464100810100c100306d44003248140c800d140407207c42c80361081c04034081d400c0300204501303210344046030400f0206c81c1d001038120384c03455640d10311441d0343c4008028009103030307035000381e0081c0d1402220007031040c6184000a81d26030140c0340a6038640b1000c458514040340201c000c0c006500c0c05090104000c90740c0300500448008032400400340d00d412003a41300c1951a00d000e564558808444c00706020b0107040c096248140c0144456070b0b201055448401e02c0c0e101d56454110441000100e00451814004210207056400c0c01c80162040964801d50550fa40600180074583c000c000111685e100e4802c6840844d400802d0b110a140d403864148043c1406452081d003c243c9100082044895441100c1c11107100e1801050940d1800a06568640c40080e081c1d604001c8607030f200302a24000e001c1d490064842c0d0f2580f010300c0f01d00000d03070a00403035038a00c0c0c00041800c00d1540008a489280e840c0e82005072407200160810341c070001a0313290303500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 10630267 1250 10629017 10629023
    0x604030605010b04030b06090f0a0e010605061204060e0a080405011202090607050a0605010902090d0b060303090a0e09011803120f0b0d030305011505030105030d0e01020102040b0313020a0e07020a0201030504050a 93
    0x280000843c05900a1010f04212407040040034465100c0000700404070100f2504c84071104c02413400201c5544440d001500815200000080c000d0785075008a800c5901a04900c8100c1510340248020002c013440740441c000f001030050007040b003650361040064070491050b5030410110000c101a02c549550440f101e040000304210383e80c5020345040760311400f00c40416900700f483d0100000703c451190080700c0d1001d00051168440703954582e9403191900c0c029010340c0d0144000d000080942d250f42200304050b1400c072015103420b20386902002c0c00d59103024810307441c0741d101049100000c0d070081d5420103883d02441c1c0204090721190340309001841c5003801a6803080d111140801890380660146042e40c15030540d80d862059040401c0d0f03000d20080c421140c160b8040c108960405210b0300c0e50300c240a90520000d4680ba030740d401400340039001500c00007855480d003080401140780c5100101d008100d5803e0030303540da162551002e91549041040a410f042e01c0e84c0010341040b0041c021a52950380c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 10631517 1250 10630267 10630271
    0x504060609050108102f160b0f0a0c090303090b0307020a05030a05120606040305030426060a1a0103050c0418020c060708010e010e060303090607050a050a0b16050414010e06040306 79
    0xa55920405e9441c2940010f0b91003541c54502d9009040000d10345034400783c11801c0201d030840d1042112099968024035000580701401c15000b000a0740783c5000d64018881c02c1e08090f00742c00d10070a8001215008034859042c000000b2003040060b401840c45401c840743c2c04500340c1c89580d4080242c2c14008031450091990100041403120160410050140c51010412842c040d07070700c85007809620312542c00003a145a000340010031103c168140d20200c003140c1024900c8091440103503052038000c0a80d0750381801c0e030300c1e2045142c42000c00507600320030020900e8184038031b040500c1405258800c0c3d015666010400d951416001e00f241d0f012140f40c40c1000381258264600b400c0b005224080038040d50014000803400040d0300140d28807418046c1a00601640c0b801205030f0400916030700403039040f6a103000307d03600c5001044050040c8040180503040c01d800c43d290150540d00700e80c207043d001d42d051080901042c4111114120740454042e82800d1030400081c103000007540501456000030720b858 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 10632767 1250 10631517 10631519
    0x20c0f0315070503010807050d050c060903030d060801020301050f030d081503120d0606030b10020d081314010603030210090b061314090106031203020a05030601030f020c0307060509160f0905040606090501 90
    0x10f038800011412501098240c0e251076440b0710412008001100010740590300c012940300311490210020521300030020700f03d0b03140c1941303c0420800da42403980010f8150754003000401580c08c0c95208415400c0088006c0c05840668078030140544101034100150030700b40031500c103029102004024100d021600c03000f51903050901c1d0103006032203075009180000f4280b0010691600700130042c0007030068240c018120900c0c01d18000c03038400f07500034a1042d00c0304030041d180b0302045210004034000c650030400450103d0960401915000c440510301031403910b40305200020890017801e240d044981105c6860304485281961b06c0075206201d0704c00e020400c0e0700203001300c03d00c0540c098012688500c21030706092400010640c00c078000ca0362060042f44080000582540c8654090885106032800050610074943c032110b1030340d00f00b9201100e60503505c20031720403192400c106c5c4d42d0002da01c10105a02190038034071744114241992042c0300c0d00c144c072030780072508219081d0421400340c03072189002c000315 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 10634017 1250 10632767 10632781
    0x3090f12260604060e010608010303120f0c02010f0b010905060405010e040212070f0f08040b010501030207060e030f070308090d020307140109020d150c170105010f020a02030105100305060f07020c0f0315 89
    0x1078506468180c400c0303181841c006818025030000904844080d00c0340840740c0e00e50703102500d074032800d84250091599180030046004c0f00c0740c8145030002080d40d00006101640080c520101d6500ba40c4903814400c04c107d00300460740c0c42404070b8041e5002880c00c1120300030b400d40454045e00408150003038401601040001c2a030340280710400300d042c3c80d5038801d00d00345001000e9800580c00c1e14042e140920ba08018003e03540a500100070305d9204601c00150105401c3d101c0d401c503002100d001c01c0c58480060102e0501d580076440c5c1da006601c94004c1c16100e000001d02a41e41d01c14480c0c01020a800380b0010404200d007035020208c880d4000d030108001990a01e8085040c42040e4030712035280d45840d140495a41c450130307402110f001e028120380c000e40d00302001520701d031400060700070451003500c6546c80161402e00a16024075a1041d9a42d07400d801d600d42142001802030101d510718140400300039240390b00107401c50380b00400746d4022114284000210b400c0404c44420103485d41c03551420b00c00ca03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 10635267 1250 10634017 10634087
    0x906060e061f1b0302030c060903090310140103020405040f050f07150503070c030e0d05010608060402010f05360603040302060601030b03010603020901090c170106020f0c0103090f12 80
    0x45500c0c1140e940040c401d9900b500c03030b03001e0107a440880004140404580080302c419064445042c0207004030790070105402200f034580b441c12110941c140c1c1022400300d040e42410001c101000c40507132001d115000340010f503500691014403000c0c0c462511900030400784600303030000100c03007a003144c00c0d5207642c00c4424146544001c544920022034100c1c00000941078490b0f810740c0e00851055840d20b55404c80c03910100c1d043c90b031603e0070503803150340740c0c004100140702481102c1c0104401c0001d007007140f610340005802d080490440800340081003000c00d415450200034801c101c3c0c841220b42020703841040c1e500383c101c003600103125082030001052105064002030050f1203817809a900303000080d445003e1600385c074a03500c0001d4202902c04018840d0300c200ea0420360034541d041c0f52030140c003807445c650224410002c1e408100540c20a40b2a011941e200303001800c0482d0302800c05121040f500c0d5551640450712200c05030034060003848142017540b0032000000703024000c0800c91980f10300140200c1e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 10636517 1250 10635267 10635271
    0x90108041e0f11030c0105030108100b0312040603050f0c040303080a020a180b0d050a1505060903030903010c081b0a0504050103090f050709060504051501200c0a030f030318020307060f02010906060e 87
    0x3c841c0c1718840541d40b0035846541100d06a80c803100203803444480c101410009042a043d020383c0c140188a491106010181c02a00c02484140d84c04034060400020003000c0c80c0001e00b04080c0e0300010402403000c41d4114140a8000240c82801aa541070303041c0d04030f0740341180c0f55006c029543d11200002d4407001781d10140c03840102030b0400f00020f882e0811910304548521400c0500030391004070411107440d03c0e1003d00400d00700034040c0c0b840c08000c040040d0840b002600101c011507204410f10126a814042e102e00340010400c8551402c0304201011f4114052445003604154032500320000f0020741040c3c1501c140d80c800202c0d00c0864a50084070094000360181030f001d0351512000480d2102034142e40320306840d068440c3c0c43c000c4455003030180c4541442600314224402d02c0b000682c10380760309214100550090401c2043c418143c5001000d41c6d103885407294100d00501d0890b0017603500412a4401c41f0114104100400c0360300d10260701400342c88101030005c2c3d280c04000038401c0c0804409034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 10637767 1250 10636517 10636519
    0x3070c150c11010b040b030c06090f04090c1a0307020c0609060706050703020a0311070f02040b030a050d08190506031509071a070605060a0e0f060a030503031006090b090108041e0f11 80
    0x10104d84007110612003210380c070b84282c0340e155001e001e415202d800c1c400300400114002400307115000c0c07050b4022900396813010408880c00d40e500c0e43d08100003841d83c4074034508503049018140c510f0406c02e00096a4509408a0314807801001030542e49a607101c0c003c0303074040343e03000341c0c18092450f18ac1400b0340250040c05000c40071034105150031881801580c01c07551003a030300482000407070145400740001410741400345505485440012400728904201002c110340065a80423000c0c45c103040604e44400805040222807070400090003071903680810040829070b8200745403d02580e4075000507180c080c3c00d030b01248542c80e68816030029800e505005040310390041405000a8a90038103004a165030ba12404007103104804c042149001c00404464000304020114250310743c40e034550904650064640703816012240320100712441e0403040d100d00400c24010040e05082021001904003072004000429004e2040448074001d10164010b0540581050501045100b24075100c900e60004241e11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 10639017 1250 10637767 10637771
    0xd0b060306010801060608011703070506131a04020303031302010302210f010b030f0103080d060308120f0a020f0703050c07030b07021f0b010e060304030e06030c0403020a05120303070c150c1101 85
    0x851a00f20500a1804450b02c641e282102680303800d0069a1600400c070f045010380c0810410400807031010017543d40100c040018080b030070001072904200c02074050f884401032444500800c40503a4020054030f601010b010040740032140c5900c0100c00a100b840500700c42c600c1d101811804c810421400d480c4a8804244142c5899032038250f10800d07400229802c0d0242c014420043c13000900c0c21002c0d10045004a40c0800c007162241e07224015904140302d900380702c2210700200091086122445078104d100c240701113103080d07081e070101c0906106446000d0144240091017103a804020403050b0003e40d0000100c1200d030401c410004e4035103002041c00543c07000d440035003440c1d0a044d0310810810020503191040c4501c00c03c420b2081035003004105070240084549041d41c076440c0e00b401103124111501c4495a114154810861741d040d850b0491030091031684907244040c2c000000301c035003260366801c0c80384d1511200e141c225440c2c600c40d922081d10034104442c20140c95000030a49408510307000003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 10640267 1250 10639017 10639019
    0x6030605030606030303090706110708120901120b03070b1309050906060307080c0d0f060209090405010b03070801090c030204050c07050307060906060510171009140a0c050f0a050306040b0d0b06030601 88
    0x1309075507400b00f6104546c880c0c210b104200805401020885141d40300362058640711580c50100700d0070600030120a80a100000809007215a41300942c003040500400b400c008072049000825560362941c01040b813451400608000140c81f826605c0c0010710750754800340220300c2c10100d100c0d00c4440c15500180280f00700d001c08654003001140740c0410310005803980402c200c50b41c0700d41c05040c60010040d80d426038200000943c41d15240300c0307584141c1c000c0001044964074207090600c0c0c1000c99021000c0d59142900c000c00242d04244a101281d4040b9000f20700307620340c404007030794501c904a03005042d8440069007a003000703400d130049403001d07000d50010400641d0f51001c0c040c01c080510340c0e40d00000c0002d0108820500300d4004a80c1113240d03d00301d03680043c0c030b506e1040c00b00c0300110000b02021510341c1c10040180f40381e00a49001184a14100742048002d00e111540c034080d6010100038840040300158154465900c600d208417001005411000c03141d04021120717210a0320124080c0c0034504c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 10641517 1250 10640267 10640269
    0x1060302011407050c0910030f0308040b010803120a0207030e03030409050411100c0201030f1b050408060601050f0d050705070b0f040b07080c0403020d020604050d080d0501140a1503060302030706030605030606 92
    0x3c1d1204142c004005d0203204480004002107600300612075000407170b0910022004c50781e001e0f9140f00c0305102c1d07100c120340c1c1c4c206410b0481c201c41c0705a00500207640104001c089070500c00000d540c1000803190003680714821868103030303a00c8141c4007185801d84030208002861079242d030001030280d0b0150400500c003482c1130085c0a1100c0400244070007081c8007400900065110750320440140040c400000740640e41d8000b644900001000300400245010500f486401d205004d2903411100900f022440d01102c4202c01480d8080c0180840d0191303520300006007014040d000715258507910200201051a008024001c90b4200f5141652110303812000200c000d4003600001d0b02414094030700780d040c603155900308850001703800c00803a0054428040003d0a40f105019585040d124466064880e60920030b007100310703079059101001d0b400c1522036860303098840b01c00180c1a10701d0020107520041520200740d018020950000350507100d01c140c001642545a0b00600540c5c0007181910420340301d00d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 10642767 1250 10641517 10641557
    0x21090a060b060703051c0b0406060f08090d09050909070f0b0a080601021f0903030204030206030a0509060f0402010507030815330408060f040f0f0302011a0102010c02070b031003020d050106030201 86
    0x40001804a0820004641052200d06d40000c0f107051484c2c0210707665151030080f0b8280c420650003c8086003800d41d40769803681c3c0111800340d016003205d0040c01c140f0728402004050f41c06900c5054003c24116010581c068000d002441c00b07084280b008841596032400f501c240342d400b40300000300154804000c10324544c03002c82c0341a42144608284281b01000904402c0207043c0a04203d041c940e0801c000070058403104081e6104a418010000e41450070b895414100203000301007036100450401080f0050382c105040e540902d40516101e1615580d03110450030001024184580c04501c0c10b9518a0300c4059120100c0001e1140d03444054a44131803689041a0095014034000ca41210000500400f9498070103a40b040c011000e00c419012140c442e030340c242c89424010340041c0d469843c2d44510410304c081c0d140c2206003e2008000c1d965403101d00a4445145007d0001300744000008540740540c10f0189001458006005d001207401926081e4020001e51004a0211b40100f4030480c0c140c0520b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 10644017 1250 10642767 10642777
    0xc0a12020901080a15050d140105011203080a1a0904120207060201020c100207080f07080405030105070e0f040b1f020303060906040c0504060c060f09030203030403020f030c07030821090a060b06 85
    0x180c50f503400320340710081075001074001d100410103004102000041c844d501c003d1103003510750180e49642c0802040c20807440c290381d0140c000e825100741d00e0340c65900281d40300c40c201da40030001c1e060007d003800c04811780c50700400410413046da00584c0b4406010500a0b00c102050611071207800700c07142c2d15a9901c00f07138243d004881c0e51810079006104c05088c3c10080d5001011100e00c92612540340000e10610f000f401c7d0051141a40c40d1500418144000d040034490f03d5001080307400c0948c0c0c41c2801a0018001c03411030b541a074012600d95500c034400e9101d01b4002d0201c16540342650001010030034009550750412104c80d03110355080c00c04a0000e042501c02c004840311141d03980b0b8031f86800c120040e150342c40c0c0c41108452007030f40c0380c0a8400c2d8901c54071495154510a601455490500c0d0a00a00c1c20407001c0b000802c54200f0041014000000510f840881c0c0d80300c3e09141d15904403560034003da4241d00800a550b80304541008010000410f10107800f80c4078480c02c00c45100c01200381b02c1c0a020b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 10645267 1250 10644017 10644019
    0x80c01020c04020304080d06030f031d06092202160501061401021e0a0f1a0708090318030102091206011d01060e040905010f0908040f120209010e040302150c0a120209 73
    0x2203000716808a050075001907a2140c0500c00441c5426200741c4c1210444400b9481615101e0304e0f0b002c0d070010154480803c0380203940d40300194085120301c0700007484500c541a5503902c10030309282d466002e004034283c0b82e000c240d00c4641c11912007504101321401002100750441d425442c09002040450740000382558000040c3d004090001010099a81c1c000020440403041e115860900c000140e581c000305c4500ca01c101c182c0f42107003030000708c01d10000001900c0c50741444101b000304944408000700340c03107441010110350031f0951080c0020a0092085e04400c3c2c0c5c11662441000c0b0381c0c0580060074074101c0e01341f5612a00746640c6d0501c171040200d001c0c003420000455030b248508980c60706030801006c107801500001108513441d50b083c02101c900c000304881062010404100c0301b540181000000c0150b0009810720140c01e500044c20604140211500c0d451190040360900d4820402000080b400050001c418280416007240c681c0000c81c140c000219215103454107400a8000d590070010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 10646517 1250 10645267 10645273
    0x608010603050d0c03020f0616030b04050402100302030c0409050a020310080a030c02041509050901060f0801060e0105060708070803010f080c01030204121214040603060503010f020903030301060503090703020d080a0801080c0102 100
    0x35401038102d40c19800700313005a00314130441c01c40f1801e80f0818801e45010b000f501c1c03114051780358403900107028ae0300c590110038411072400042002585a22652141414080c0340050340d03590745050a02d1113000f20b41005900c41e1524003000400d070120b40c0191b0107040138006c8030300000d69801300203944803415240140041c0a0b01840300060405401c501a007010449580e131800e5120003890741150030031500010269141c52080015a5a4200450160440070000e10055082650715420741206119035800f0302c0000590206019880d0103440c49154030041e00303560395958400c400f408540d50300580145002d01c0c68105200d40c000d108490440d070170100ba51806010135207405a14250001c1201d00344526986101c015000e01300007000540081d440000e0a5070408062500f1980d0b842080700020b4810090080b4913500002581e04407086031800c140e999507651455070402259500094015443c075450b001000002d202030086c0c103801e50f0399010070fa070fa0b0b06101c40d51400018010740c0560 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 10647767 1250 10646517 10646533
    0x9060b190905060103060909050313080309010f05090303090303070b010305010b180601030e010e0d03091505100b0703120501060309020f090105090c0904021207090f0902030105060306010f11010c0302030a060801060305 96
    0x189007a0450b9078007540c1414001005a6240e50100a0b80daa9140495613034000081222180c4180c642c5003024090040081d030400b1000c9002030070100700300d00b014090090100380010b9959003002200d541940203019251509414034150761030341000c2c00115819401d081081400341800d9038074400b14950854080015110000190000d02c100d60300c2440075502e450050024100820100c1495012941c00240d40c2c41d041c01c1840705007814145980e0400d050005001041c202450803800752103183c01040d968444600c0c1c1550603d0000c0350032a03030b80b07080c80000140c0e990103030300680400d4020780c1d480c41003090030400c01c00c6e11502401101da0002545011030780d03100f00d0b0401361105043c06080185040c1070380036000340300752084a6180c001a1144400c0c000c1d44081120003000b040400c20070f600310750411000481900004220b50704001503048010b410301e00ca4450020728101060003000804501c110080195008840c006003c030300b4000e001038003c03014415102100d400c140501010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 10649017 1250 10647767 10647779
    0x10060815060a030209070318150c030902030c04050711010501060e010f020f06010e0a06030501060305030a020c010504030314030c0f031005010906050403030203030109110408030309010e1513020d0507150309060b19 94
    0x24071000d485541007541d41d4802d0301800c80c9420200f03142d5070044d401102052101c54901d014ac640c035035004800c01d420050300d840180c40028000034505021603000c0364960786c02c40e0880c3e003500c110b26103a61030340c00c010002600e650080001542d090080c1d039400020041740c881683e582d505491043c1484e4062401003101000e510b10454110500700c2020403900c0c2c1c0c1752240e50950321340b60016202508005032500820b90104651340300400300303007869030409185450161291000d0320080c0c44400000000900c2c045800c1c04440202c10201032240d01c90030701d907521001c0c2400e940601800700e225400003003940f502070b00603101185ea06600541c611703030034600404040c1000f5181440224010b000c04104e060040c0b0255200c1d480c841d000080140600e4030349450f000b00803040c115a0101c1001b4422045ca84800c0c0e0503259030180d0710303205080d9551500518040e025800003920b0381c005210b0036a02c5030b240c1c00c000307a02d50149006011000350300c401c000c1400c0c4000c5062800b0108070300c0401003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 10650267 1250 10649017 10649029
    0xc03070e040605060c030409050a0504120503060d0606030302010b030d0207080c010c080d020408100b04090f110a08060721050112030f0203070c0308030a050f0613020c0106030510060815060a0302 86
    0xc820000e8404601140c0d00c0c8040f03105030300042440c08075604082030034001d0000603c9440e41c013200f003200078420307418a43c50390392110324040c050b50100080000000d030151141e600030200e50364801800c008083c0e99080c000d0007043e400c05154481d00820320b80d0300000c2e01c001124001d80c0c101ca800740140c4170000005540d030381d6868000300d80d410303c1800b0302240c090030351000e400109100320140020400c4602d80c4003c1703c0114450034411840e11414402141216130480c146a40c03004c8006082a03203100082d200c0103081e40b0440903481107404100d0015030207488050101d0480700c044100070300b001401c405580c000d0003258480d2038500d06800110340b1445440b0000866401580d103485103c1c0c0b607000350380244d81c2060f00c510200006200d04d13911144103190313101c040d04d0540b0106040000018104075122144039410940116501100310000c2d40490020340d882001c0300d40c0810707810380020240c1850f200e000e0b00c2d8000d5005a0308902041c100711842041e0051044508034190342c20000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 10651517 1250 10650267 10650287
    0x130201050901031508100e07090915020702060c0d0e030f010b1509011106130c0501020a03020709020904020c0601090c0207060906051207120c0903060e0a031b03030209060307030c090e0c0307 84
    0x400702c604840000c5c3e009818070034550080006180400c00758854140b645c5048010307401805624508607000000c1070011103000310b41101c1e4000540c0d92150703800010007a00a228602c00e083c000d09412010b1641c1102c2c404e01ca410040c0c0540300074000040015080344e00990b40e56400c81040f020201e8081c03403020042c1101481418590903d07940041147c1c5000000c0322a01c0510703500034045410312600d0300202d030080000f44000c1c180c0c10141d0340c00a40b121914442c842841d50041344801c800d58071a010b5441c2015808116803080d030b076441608001c4d040780c10440c8054041d01901041451080e50003c0a85003107481d80351074009800714091440d07100400017810018802c00c0016032100c98000d10b00c0603c2a940c908030b601c1c0c05c506000d000c860311402080200d900250724100080e40040460100008010700c0d14240b12160a081d0003a00c5601c80d0250f10010000400040070740503440751221010030381e1000d02e026114601e81840c0c0f002540c601100890074000500340d02d100314015a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 10652767 1250 10651517 10651541
    0x110105150a0b0f130303090612050c22080a060b0f0904020312090103061a2205010f1d03031605070503010506091602010b060313140a0c060c110a0905040b13020105090103 75
    0x16240c034420408103c010713501a00300320001903442c40d081207000e030310041940b203d4500e40382c200081e00b000f00100c0c0075840b503c260b8902c601c240c140308550908800711048010115a001e80f10380c0c60180c64080c5c010070303031a842d0522a50207220001e01c241420502203110304d5000d0004c200300b000144d01e980c00c035000905414101903c850010a203007400010035504604c4600d2410b45440b101c0c080b000205c0c003034422103e441c071504001002680c0c1c1c13140908030440510304111409954070075030030220b155a4460141c15100000cbc001842c29100d1018960582c003410942e41ea00b03403150101426540c080d00c02c0343c5c0c069210400300304801440982c0c000c2d040400c4c000003a0304100721000c0340860300212110b6245540892110040c003069101c0510004840c0024002900da184e540b10050480d5005640800610814103000c01c40d081501c0b031102c00d80104070150b00b03513881c000ea0000e00030403682260315600340404118051130502422100d154141c488908103d080d41c0114010400d04040c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 10654017 1250 10652767 10652797
    0x30b04080f070206040603090525060509010c08120108070e0405030403060e0a0c060806030f0a0b07050c031201081b01020307020d060b01141605070503070602070306021810110105150a0b 82
    0xc2c10050b40e034140280000d222a403000704503102c90b8240103041c150b4030260b0904120419a1a0065404100502060320b030f031070030004e0b203c011400040700c01031810fa1004190314400030340016034010408407203040b40d800408440700141c0b00c029409074804203642c000e045900078401400003800580100c000740500c501190700303a24660315407038080403841c0c0c043c10224103c1e0091098604041c8180d08070368141c90002c100601030340e51000011032004100c0b2007000030110f0703100c0b03804800f80210780c0c0440c00746160024658544d01403544480710b0f202c0e100c0c27568a44603807815139940040203403001030780c0003040c00c6102245e0b80c48120240c003240b900b02d81003000303c1c11211042e40344c1c4400340425045d1211540d08480d5140380c07162401c01c45800082c0300740e00c42c0c1c6041013080c0d0300245020950740e000d2009a210498200380d43c0e030781045110010b9101c450b80e036022481c19030008080315000800402404280c60701c542c1503124010b1480301c143c00046650301840817230500300040144002c1c410b08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 10655267 1250 10654017 10654027
    0x415140705010507030903091d041209050d030203030105010206100806060f040e03040609050406080303060d060f1d01140f0601050a03050408040b070804060207060203091c02120f010b040e07030b04080f 89
    0x102401c540044664201103546c8a40d201c06150b404100342000d0003289060407a0040e54600f1194034000041004000b0600074140120707a1744070303c04d800c0050901074007105000d025894060b4581c2c00074081d450061140d100040d01403150947e410042700c1c2880040c000f140c54200c14803414040c401400b41c0c02648031038191390048403c00007440100302550700ca0490500f403000300000d482003a8480711990b072040c414041640d64614030000c1c0c05c0c0d071151000903000050202c0102800c00d0141c1c0300301c500113081c1c5007100610190040035001030b0a6044500d1030f030328041058580081620ba5074002441070052a50007030080d44015007150191422a003859555101c54040d0352005004541c517070303004642007000a4040100c14003400e06800034500345480e00700403911880341c40f100310b410000d205052506546070010722411400c0e07a041079412100b078990070300740640f40c01001c2e2400380f8a02082d107050514040f40e08410b0765070041010380b0b0758440383c8510849400054117a131400c078003084 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 10656517 1250 10655267 10655273
    0x90b0a090f0f050a0e04110105030406060e1608070804050601120c09020f0c060c030403050d020d0b100203030601020706080c1e13080a0201140304020306040b0702010f150311010504151407 83
    0x280300802400401e81c0b07050364a08210500285542d00c0e448440721101c440107100011b0051081c00502040a1030110744984e51400c1840c043e00d000d500c0a400f00350010203100c220742c0c0c580040e800400c03060701d0f608102e48860701d044401d4401200c000d0141d8024100502c40307004100f15181c0c201c0d00500202c200151a403000c05e00b20b07800006035039401c100000740c180321540240002540501d00020709410f62030183c402811602c1022841e400803580092003800c442001e900040c980d03600640350301d0280c0305008010b5542c0d801981c0301405481880000a0750a01c90070450b031007220060340751402e280c50020151400d10801d40c004804071411b020500c0305400c001688401040100024000244140000b4003640c0303404100311000f910410820016031030018440b038116a01a403840d4055032458400c13801400440d803a0241d10303080506000c000300f04010810140c90245c940e1501192203580159441d2259108481c82d900b0411011112a0700669100850109010207d4900300ca165 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 10657767 1250 10656517 10656539
    0xf04080609030705070b0a090501050a030e0303040605061504031e0c0305030c0102030a0b0109061b05070909061b02030c0a2d060218010e03030906130306021603020f010c090b0a09 79
    0x794010a190700120302c05061100800496008241c200390003460450302400c000c1031120035024090600c03c00141840400c0d10a5100d500340003480400e132626401c0c9860204003805007503071000c0c8140f40b201440c4007a20703400350031541160380c0022442e1011380c461500c250803a416400544108014460000110300180002c0624403041e400069907490601840022501000c19442c100212107c00b8000c039500281e040c0d001e0459004401c07081090341c42c08610b058041e0b048a000d050501d4061000c00c0010381000504044ca041c000350421003000b800c030381c0e034004d0301c10805080d80144699000700e611070308558150240c6030011104c01404079103e05184070000b01c00ca400390b900040c100c1d5070342c040021240c448070b07007460810101d9403840c000035920700a4000c1d051091703000242e0415105840c140da58019036100070305545404d040c0c2c60555605110742d106034003500900156444000307040c400c1c103620701081e45034003181d6401c018807c2c00c2c03600b008805000344500c101020402150700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 10659017 1250 10657767 10657771
    0x30316080c13120308090a110409060f0204060908010e0c011b050a0501090b06010f020609030409020f0702030d0207030215030c0a030e0c130506010f0809030306010f0903080708070c080a1101050f040806 89
    0x1030b103d070783d00e0445140381c02480310300003c281c240035801c0b01c401400080c6506240900b022400c407004262040581806402480b4003210b64003458800240020800d401c001030304120340d0040d001300100300491070b116845002184055000a81614200b08200034126102080600810454000860741e949041c01c481206006075590122502041403075a882121802e5514151000c1e1800303060070388045980703020300d00660801580200352741e400780d00307a40300382c07254541c002341102c80000d1b59400203034a0704102c0c0020390041858100c41d0a201c5124000c480c007035a1811052803400c004004120000c101462401c81c16000380000c0c00c0a80d5034490300720020340c11310745000642e810000000b41050302c902400c481888001c00c00c10403024804001d40e5030201007801c0107214001d0061046804160a80000f0002c9001207401400e00042c40f000d80308071480b5640d21180c050b2202d0005555480607074008090003103400c00101203502c210041c0009410046070f41c0c0c189902c444503a410241d00b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 10660267 1250 10659017 10659029
    0xd052a15010b1306110604060b010e030a0b0a110307020c0f010306090509010606110c03030921030408031306050403080910050408010608010506040b040b031c02030d0e0c0406050102030316080c13 86
    0xb0200d02d503040e180c12a40c1d540010950741c01c1003006500b4100d8059150800108003429441e07844034010b580364014a410920003400900b0f598092225260011604905a4008116518000c00100300703200c110b0440740035207050b03001800880924000c0180244000c0381090401d515103600003124030b04c84c0210341c02a841500041441400c00000602ca51005800341040e0f5004005141300347e10040f08503551080d081d96038190004100c03800710030707440d030820241b81d2500c00000c00041d40103011020f403086190000381210034030360752074007103a8a016900000c4c0200030104072500c070a250a00001c5030303085150502d181403569504400c0d0031200194494560f99449408008003071a05200c5d4100b0001c04980800078070064078086941d0340140d2500c8051000d90400c1490494020801e6945603038914034140302c000030714036103913803a91007100c4154011810844003044030340c00401942e110f45581d6405c034951541448003150040700151001d0900201000410201c002002c001c00240c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 10661517 1250 10660267 10660289
    0x1507030b0d120206060603060d0b0603070b0703080702060108070302010906030507031e0b0117010e06010f0e03030a030605011206031104090305070c080703021201020f070803040204020904060f080d052a1501 91
    0x590000041e080900c01885544141c0b020030030002d80d5927690034804e1070740380c110305c8010b856a00e403c042480c2824a401c82c0711581c1c1e0200d80c450405034040c640d648030ba2120342c20ba8860743da852280a668103068000203000c03d21084080c84454400e40c4255404101c43c580821404d048031051b1045a64034003901200300d8440702c0c0340440e941c0007001681e190030300701200201503240c030454400f10480a40203e04000e00240c0307840600e8803aa13443c854950000301601d944044219000d80184294400d46000c0340c40c0726044824400e8606c2014100c1c0c1c0c200880c204d80860240030007000340f58001c030443c18080140002c07804102032099400107852004001c0400506500400c40d50007040e46411925a00400c24489221090310681d001541d00400507505c1c0d48440c40001d01900481c00c109401501c0c0542c002882d5031050b060904441a89003559a0a121101c0480700741c4035001d800903115821505e209602c120390039034503c41580d0b900c2a40c045001110700880d10784001c1c0d00050100c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 10662767 1250 10661517 10661543
    0x604090f0b0403110d08090a02010c020112021206010f030b0109090e0a0803010b03010e011a09010810050402031005041503020f0f181005040c0503070c0f0c080d030f06060206091507030b0d 83
    0x2004c1000300c00f21040881c01c10910038500310517003d540e04642c880003410421001104030469010b00075010407141d500c1c400b951200f040f2099140c10160849490303000850402041440074024410720b002c40506950760440b4034201075030b0402070540500e84000b07510404894a000c2980c02000e035005c1c2c80700c00c2d4007030741d07c0d40f52a8040b60558410b0700220300c0c00b8150f00d802c030311291403001224010002801c244003d0340e2052408182904030340d015640141c0000108050305041d20303190740503070310304603000c025105c1a48a0241c0d003100c0b60000a401140c0b144442815140400c002e40400b90024100c4c0a180c808031508614042c1c240e0b2003d960040e001c909200518050003183d05a0b07445240a505500c1d00e02c400610fa941030180107050340110f4190740c07080c00495070141c40a421220111010f076100c0040c001e00404d020020170510624094009c20302610100e0300c41c1c001e80506008081c10070410030680a40b12000d000002450358a03002c0350f81c91344600c40c5200c0094044d440c4101d031a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 10664017 1250 10662767 10662797
    0x501080105090708060a0e01110a030902091803040b0f0d0914070603090c060c060b0a080304060801120503040509090f0604030c02090901060e0a0207020a0305031b0709050702060604090f0b0403 85
    0x5110701410071065a000081e0501030180300050369070b4401c030340c2000071641103c4800039500510b000171030450341d043e0024106244a0b010b03000007641600c2a41e5101f1281e80d0281c022626200300604160346030800c020030000301868001030700b142c24908071018900303c052a121800c071440204121200480c0b84c80c140640d140900400780180700505041c42801501d644000d55503030365003d0030382805140c000c14400e025803603000d00f2000c10040d0294016589544002c1d0380d941151060500003400c10707001040040c6000145444150b2120080d81050308000030000800c000410140349489103004034011a44c04101081c02280a0b032181c2011403000d0050000f10140100100c80581c1445401c2080c030303020140b0590b00c10042c80005803039825038070008105c031210b03070310150041c4001719004201c2da1812000c4507000f20b445c0c00711030710395944080c00c10640340100d540b04003582080f400110f2908040c2c100740009440740c800c00c40044040c2d40c60b290121010355090300000c054144034005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 10665267 1250 10664017 10664021
    0x1050f040906030c12020f0409050307050a03030608010b0406081207031110050604050f0609040b060103020d0204140a1d0a1503050d08062706100e030a030c0b060f21030415020105010801 82
    0x20f040300400950201c809500803805030592011f00c51b01940d80c4d4555402840024400d60301202da00c0001c1e20031280d81820018040d001c180078042c455403070491120700364a4644210811104910302a04401c0b480d11201c6d10b9a03000b031032041e82070100540e00e00390101c0e0203000b4524806121300001455090070b805020440c0c8008007050305810951091004654030f0410301940a64008080003090b6150b00048002e401448400020280007290100f403c10f005e4100f00c101d0a400e864400020b07a80c1c1070b48a013251124400312007402e16541c003251380e08441c0c0d000750341d4521149000c06e007459600d54481c1e01d4095108141000900c42c0001d100075454141c81c0d0b601040c0000441072900000c200020048280281405108516005914031018025003900014500003003d589601c80c1e6420082d050b40e65101e400c6600556450020f102840c0c40036071103000040142c10020303600140408070710290118002d04c00d1910051100040103400c006103120070907015030002c1050b51500c010142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 10666517 1250 10665267 10665269
    0x4060906090311090a021323061c020702030c060408030306120c0102030a030e010902040e07080616050a0e040605040507050408070503060c091c02100309030e01080702031801050f040906030c 84
    0x10030410364060400c003040f401c882000c0c40d143c1c00c075034803165600c400c10920002c0c420700c6280c50380741d42c0740c06000038440d10b085a040484004000b00350301174070345941004014810440322501d949914103942c40c2c00784856000e030412610140031200705603810400500150000e60102c50f061340000f04001c802c0c20603901c40d25070600300c00000c240703081c21500040d480340142e00c40380080503a5078440300c8401c402500503000c540d130060801c02101001e215025102c030b41d1400780100fa840340c05d000c1290f000041c035102e160b400c00d46d40c5103400c005d44d448045503030f4031014049691058484201103100e41d1580300b441d00036207854880d03035a0303180380c001c09908009040d030009120b90012030420043c01c2c1007604540314050200d440c4403400d01440000b0850039507041d000794224005484c482c82054140e0300074101680680c039081c1c0b0b04411f440c0110b8825808a60300760040c5c00a104000c14141441603200c0c90b0b000504215080100d074450049054100340d00100541e0303100e940c00c00a0245508001d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 10667767 1250 10666517 10666529
    0x9040c180e0d0309080403020603010305070510090e06090606070b010b04060909090c060e1804030201020306042d0510050411130b03010608060d0c030803040f0308060607020a032006040308040609 86
    0x721031200408030550311a6500015541815214520541000720307080456026650050110f81c8a58490400c640e48240d03d000c0c56006410200002d403505005841d07a800302d83c84501103510513a50042400f030072550240c40705412050600820002801500344140078220101c074154a4900d08080100320700c243d43e0150382d10070b140c01410740c082010400d202c0250303045401d06055002c0f80c00c0c081303582c001141801600c400611320a2000f050b0f4190021801040d003141c1c10b0040c12001c00541c52008980e5007028841e031002602d1440d1000207400255219411411103001503941e80003190a480350404900c070b00c00c0740054403051150304000300c100a000078104860039981010000340407160f010700b20520584a50038114100041c0c000580042d42c2c0c000a520344a00f09803418902c1e9010311107003100400e01c0c881c001002400c5c00c07001c0d42d10080c2c00404008a0a1a60b181d140048155642d02a0855640010010036851b140000c200541c0b00703039440c50f51180380ca01c0040c000741081c0c01070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 10669017 1250 10667767 10667771
    0x20d0504060210020a1403040302100f0c050d0518160305010501080706020a0f0632070e031509010b060403140f0c0a060e03070302040608010207030e04020313030f050909040c18 78
    0x501c12141c0c005010407096801000040e602c02811600780c416103154416036060440c00002c2004240c0d001c540e0320340100005405201c802d1110709440140c981c16004800007840c240a146451640f41c1c005507040b072032402c000300049200368215418850151034900304289080300c1002081001d01c240780c014884080030300742d42d0341407200083d1038000002001c2c040c4403140d0301c1351051141e07690003601c80440c1840001c44d101000361030f8000d0038184620000414408100152080380a4103003124981001009400d0040000905003404480540940140e642c0c0d4081e001c0030340c54440c0148080c50084e0428242a140007000d0792500f0f01c04d4035800b5158018010820342a25072111310b20a883c0c950810b01c0b044121f41d00800d251038060350000c1e52282c00e0040c0015030613030640c01018030134003c4e600e098600c204c0e0307030500c000d0f44015100310440075004110034010912a452100801213a0700d40145489404000101d0309007007520241d45440c10032074100061001d90700442d50b407419003441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 10670267 1250 10669017 10669019
    0xc04030c030206030406060e0a06031109010803090103090606050411070213090302030304080a050d06090b040b03030403080702060a110303090106090b030a03080f060a03050a080a020717100b0103140702010903020d0504 96
    0x19404040c2800e1200a005030700200124040080076042900608440c4900d840305281903404103010f451540b106a41000c6140a0101d5508102103d00d05807030260004515100140004400910003044141c030150740d103120100c0c1a544d00e004d45500c1c0404608103980740d10fa54010441505468503030500440d14111681d400a500802a00d600a40008a031038640c6c0401400340d07001d21449494440f00c0e880d1005c007040e4050b9907444082d00404c1641d04000b908607241c24503507039208600018000b60320500104005140140041c41c8622403880c1540580000e04200e91940d001616030030126512a90144039104051140e5142184114001c2c4a550056200036143c0c080213803940c6400c410303181c00234405071545d000140c000e41c1d00404940d41e00c0364a0405807030a270082c200a50050050715000140718048000707400c10610440081d14540c18241c01510080005003680d50515803a42680c0d5031840c401603040f0300c5a61a42c0000c60a01c044d454000d05280c9180e000005004042c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 10671517 1250 10670267 10670273
    0x3050c0307140304021206090d1404050102030301050607050102070b0403031406010302040b031501031104030501060f0f0803040b07020f04020d0b030606060a050d0e03090301020304150e01020432090a0905060c0403 94
    0x4a560403035906030002c1e5600d450302e001040152120b5280d0010358424003090110124002442070f01c00c0c40944d50307590380801043d1300185140301c3e41c85070b28010f81c01400180920b280c4100240030302071007440010314003680c071b94400c4805a0200d4058020a0791011302c51418001c4801070f5a00440034a400c500d1f050074660403c000740006000341804040b01c0e6480c050990082c6d00c140d040080369800e043c1c0f115600c2c94218040c0c20240600d0340c6480038007000040401120003c01d06407011a009142800d007001e0381141d69411894090345c1c00305400200801c940ca45100401507840c0090021178181c00c2842498a032400240280b40110070401c080c5042991000590f40c0002d5101000700c0c0d80410031449514501844d006958994400401e0004000c0700c160526441d220040d0284486400c01103d01e00300c0c0643c1c842c404645e18903400c192894160120f18060600264900858106410700401d4404e04212900c5088039a102e41b410140082003080c164003030103ca4030382d8602030030340d0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 10672767 1250 10671517 10671527
    0x806061209070801050c09030f070503030708030411060a0e01080601020a0213020904020403020301020f09010807020d050d1d01060305070603060f0311010c03050f0c010515030d0f080703060b0c0a0303050c0307 92
    0x103010480d8105810085500d05000303014010007030071880000d21940c00c098122036000d81c041680c1e10320a101d40c40c2c56500500700841e0400854030014007650504556880d940d61540c0003e20890b1500d007120f02c227030b0481d03661070040c0405404580d81c2045480c03a0900262801c0c001810850655201e008004e00580d44d400960116004e00000075032a1034450011030007900483d00001e40c15400460180b10907022034000e000618400d030784488071500c0c0c1c48401c0c4e0f203c0d4411000500014000c00c4490710f10040e981124012125080c40001d10030306012005c0d08480250b003084a46070070282c8104005a171500400024240c540d0f00790704820320319926640240c840c885a41d0520801d5981001854045c2e03040c0d4044c03000c0c0ca00d5050b0380744140001140200800c44841c0481421509400203900f00011558851240d940711481440c0000400307552260008007081704050b105e032804104e04007481c0242c2103980100b0000e10010142e80780190655a00a140c0c004001091080041d000d41c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 10674017 1250 10672767 10672777
    0x10603051e0c1e03011205010501050904050c0f0a03050f07030507050f010207051201090803010e07020d0503040506071404080708100501061106070c020406030b010e0a0b0901051e0d0506070f020706080606 90
    0x180c040a565895683d40d41203420f42003c20030450110100c000151071840940e0611075501c41c0e030080000782c0e21a001c002807082d058802500a5100d884003a40904002c01045001203004140c103030925541d035030321407415200d1800407005070440c680800401c00104a10001b4140c111407507102c050131000000e40d20312142c486c2501c501d022450400d2440420343c403400c000d640040600380e480d80c41c0c403044070141c013050fa6080300610603940819961882082030f171f40910340c410301802c0980c641c5a021100c001c0c0560071010340c1c03d020000050311035000c0286000a1503100060940e0300181441213080b2141640301da800c1c0400ca05550803200008503181e9448841403c1c090004407843c0041030003422150402088044200c1c0041030860030004050700c035412568043c41140b40c610180903501000b171090a4000d440c0c952840540002010203001042c8043c1800d179540251307032910351401d00b050f516400031503504e14401010039814444038000d0801400c015489003040f0021820a08c03038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 10675267 1250 10674017 10674031
    0x118061202030c0c0d1e030203010605040b09010908060702070509060307150503090712031116030b0105010f110a0606030209070f120504050a14031305040504080910020a0b0f010603051e 82
    0x4008002640f8104500a480303c4458620440e0900b082084000d014540c1c0051500c000083e0b0641c00b44100f442802200d0503034106c0d41c0c682e810545407840102c466004520302d1418402c40410208030031104101f0f051148903550300034644640341800b0700c039030303094003070318035030281e04184400c0c00207180c0b4801240c61180e161407c00ea603940c1d443e00d81410f00190b80c20401d084e038084882c0384c06055022284541c8006400265400345001c4042c284800341640720080412030054010445903001c1c0810050341c00c1d15080424082e22841016401d2205074a0102e0304035944000c1841542042441640c0c07000442c14401080b542030308021301405025054680444d45900010302081418042642d14580c00a00f4200c40540c1c0d441c1d8039100d0b00104001c020440c1802c800003014541409818007403504444407a20708400e5509008189200a4130101075100d540a8a00000c0300c03400d03694400e4904100e40021541440c0c030003000e80d88003070b003100d48003500110032401d0906c01981e40f9801c50340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 10676517 1250 10675267 10675271
    0xc09180902030a12090b19080a02031005090a02040506031003050106051503010e04080f2703010b060301030f02010306050603010b09040506010c11090601031d01020301090606050a020d0509030c040203130201180612 94
    0x13000340e007202d4590107508002c3d4888004514280c2c45500d5940010b00c1c15603d4a90b0141951440f10f40700490200715407028003841000410019428414241d5410040001001d850a911131010030321070b500c1a521455441e503840c1c820018003100f885040d024040491b1080c04102410340d440d0070310301042c000d004040901da800b00c0c0420000320205c5d035100507040103070798407030416401003010720540362144140180410400551403030b042c4506a46d0140007000326003184d0030340c0c507002800004a1412414580c0d50389010401c0d039030700c0010710700034483c0c0b45800c0d13914102402400140c4501070401d030b060000ca5613004000400d038008126540b00d05035040c1040380d0300c0300012000740c42c1551171011240724462a9001e0f8402c19001103060f50b170207078001e0050390f9031a001103070300e8840c240c0101d006802444090703400038812030040042103401400ca0f045414508001812a4407d48280712001c0c4241d161804658210502c88a40c0c00002001003040e0b280210180030000c44480c2594595 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 10677767 1250 10676517 10676543
    0x40e06060904050702030c0706140403030e04090606080d030b0117040807060915060305070b03070e0d0c0f060806011806020303180114090d12050106020a02010507020102010f0c09180902030a 84
    0x144800003a90100700300103000340410300304100065100d03401141c0b0f28840d809000e50102d1b81078014400000065110208941342c00d103561021510940b290f4a0319a11548910091002c42d54600915024005210182120000e071040c064129001c85001174144010b05503012070f5184a5000c07503074044c0d000380701a03603651054502280140007034100105100b00f10400b02101d90019800319090303e01c07500880713a0b819184c180690aa0100700c8032a00051204e03040d003000c0d8102505c0c64400e651007040340306d42c0c140c3c035003000e090210155001440012024400c1040643e07003c46e441c082c0704100c1c0c000000003401e01400944910004220050358480020f40b0411000c095114039040c84660307800e0011030621903101910b4207a480381030b02c0000c48681c0a12600407803072142604840854001b400c1003545070340151066003000c2802e034159503844020360701d8511303e405100c51042c03c517030700e9204da14100000490841c0107000c0302c40045141a0f0f0700001a10001000c41c0c48a0304001c01030350718 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 10679017 1250 10677767 10677769
    0x31e100e07050d0509070f05090609010303030e0a0507030614010902120103060b06090a0b0403060b120a02091015030912021b060903010e07060c021f050306010c061107050a060b0a0308040e06 84
    0x41d2142c03c14114440380342030100841120701284c2c010540d220005210324041c0e48904101840400395000c03584120030340010400130707010b0b03480003001ca900703131003a2034182c4000c1e181d450901f081c552040d41d130fa50f03c591a25140700003c90301d6a0260810384c1d4114208032145605002d201d031705010041910307aa42d00010440da6441d01a10344188009000c03480b00794a0300c5c52042250060310080f00d106040a001e5201861300321030288044064200600d00c0c1e030002e0f001c10030082400340c0902c003107011490300454a40c00507404c810341e4202e1900c0200e40000540b414800580c5481d0a40c0219040031641c040c003401d0003c800c40c02e214048035403d459003035140003c1c3c0185441801707035405119150700018025000049001c441c1c0c000c50344001d100000030080c03104281092072040006500b0000102258001c040c60559903004500001d507890910800e05500ea11960065034035610100c910000c001290103581c003842000d9510710242440e6a98007201805140200e038200f03c0241c001a0b00307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 10680267 1250 10679017 10679027
    0xf0c01081003150e010e010c0306030b0105060c030d0c0c0b04060902032a01050c100504030909060b0306060a080403030b031603140f07050111010b13050105030d031b03020903070806040602031e100e07 88
    0x2040141b070000f0010b0070010700f00500103054502c4200d401504200001416180040940d55040603c8000e10302e084071442c11030000780940781c810710a10007a5055003020421000343c4520403442454000350240d082e004040c0383c040d03ca928408a021100c80f0422850407002c102441c0c0d2000303003082d0352034000b004241800c0029996980c02042e00c4d000400c02410740c44201a0300300e0750030380003c002064484038010500d01c41103031540e070020030800c251522144103103100caa0140c021301c1c0025250f450100001e003007820f54900b205034540021000d10078448101e07003445415406000414907840a41010750310b80201e03102e15810b2000e111044112101e080d0088407a6030401040850145802c0e480768009000a001d01c5000380b1843c9595409980030344581c500c501842c0001904040801c0002c4020394410851690180540000011000c50400055018038411940942c80380382c1515158002c0d43c00404000420940c1d00501036510f40d02c60540302030b94081e20490300107560302d03803094039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 10681517 1250 10680267 10680281
    0xd1503080d0506090a020702030604020d03030e070602100c0e0904020607030c050d020a11100207050f0d020301050f0a141501030c03020f0304050c010f0306180203040f050f0c01081003150e01 84
    0x11045200003450301901d40355074001403050308100c2c0c0e24072140d25104030b078100700e00aa020007500b503030010f00814090300d0300d00c10b0b020005e4405d1402040492900704c2e56414160260302040140c0e20042540400303441070702a0f19541d40561130810b0300e550b040400039005220142c4040e0141c280001ca032001d25100d030384030020007a000011111034000300c9a0013580c891950105079054400d45117042d816203040300150100c01440e50050600608240400192003041c0340c040764000038034610302005131800c0c01028800d18503049248031502d4103102100c191603103880071940000c00f940c2041105041140c6d110300d142d07c2882c3c000307113041138030400b80c2c002e1151002c2005400c1003c01000200000045c4c0c80060f108280e03030b200c0d40300d104c10341c060f4255680c5001d075100045e150503039809107080326406154032034010b41c4c1d01250403000d0b03200c583c1840c0480d030302403046070480340b694140c550300081c45541044c0c03c4500c8070754140c074586545400c0c1c4c500e0348225030324035192400800d02640c2500080303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 10682767 1250 10681517 10681523
    0x9010605160602090f0613080c0d0506060907050d0c12050603011503030f180b030402030d08010b0405040e0307020a0605030f09060105100507020301110301060203070c050406060c1205120c04080f010509030d1503 93
    0xd51f46400341d031071402001e0300501c070700e04036032140240700c0840c0d040c010b00d001e00300c9a00c84000d003190f03102c8008002d0041e07001002030b0104201030201390a2210b10f809001c8100c00c0548814400d1a0710541c5042500d40047c030860082e81001044400b8003101c203040b6007225090318003d07030801412141106c0010000384d50196140d5664800705403401440000c3d802280708404035401079405d100300344d030485003d01c05d402c01d0540038041006141441d4125800e6840c01c04182d0b40380018507400030307d05003006d8006100050700842080803c0c50541826904030088000034440343d03242c44009502c09d0450301c0d80c80700b041408181c01c001c6440035008070710401f041c049540d8032582c440000a41d29000750000352181d40c10304c1000546820180300d6501511a250b40e6031040680780d4503840009070500e030080007000000c00c007195010100e000ea06000d0080300015079a150b142c035018501d08400041c1e44112a4500014049080c0000089440c002031080b40030802d400035001c1d034041031352113074406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 10684017 1250 10682767 10682779
    0x102040b030105180103030e06070201051c0903021005060a12150903050a0f0309120809030408060a0b040c030c081501111b12030f0f030a060305030a090509010605160602090f 77
    0x124101104102035030584005982d00d5a1302c00c2074440140032403130203100103400304501c0b4000e0310705820400000c081e65401030400d1441d0411001014402d590b00b0711a4450a83d0740c0c0103100100340e814003010b2401401403c05100c107043c00000112250b03018800c02e800700e10090155400c000360316291140c050460202003040e041c1c1414041d00c0355000d4000c400000e003e0038035000c0041d01078400c2800700d40d002414080441284941035840301c0300a002000d162005101c00141060200b00d1070f4801d418000e004038442d40003005205c1a104120703603160505052941c0f00164960200b481584280b800342026041140880140c0c3c0c0d0200c00d04001e40c0c00e002d100c3c070824694a81500301050328500b65550007010784c200e00750503200e00440b001c0c0d04584000700a04022801608040c64200a408000142c080c0d9a03984192555000140ca42e000c40e00607281002940fa0994215005121605007140341001801380b05401c0c0c000fa81008282e958082031414040d01c401da60060001d10182403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 10685267 1250 10684017 10684019
    0x1110a06060311190302090c090904030c02030d030c08150a050301020f130902030402090708040302070b04030f030806030102030601020309091005040603080409110a17040512180910060507030c14010204 89
    0x140040c01c080e0005480043d88840c440751641411860224402d00c0b1444d141c0303031282164204004000040c113800c0a1060610420645a540c0c1403110700861203078968404404c420701c103040c2000109540e200c01d02d4034082048500d00e42140010b079108200101003a411010710000414103022901702c0368143d8801f04000d0880b41030000141140e90307104a081c150741e540d640030203007603100403074009412907034403070119011a0044682a410500c030740140d4207100d072110b4103940c0580150b4410780340b11300202001400d050f00a1001030304540d00b076000703610b503103081d0b2b0000c1d56034440c0c6070703505020f40711180004415110b9000701c1c10103080014000d018142c6e90381000031042c1c105004100842e0b180c021103000c8940c098089034070f0b100c200d0f16490780d0701180e002070284528000b1b00039a02d0303005894800d414529210020702c284d02040704120f042d14003d20900040440c01030582c4021400950140000354221041d103512651510b860200c8011514002a03031f00300c3c8d510004025800482c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 10686517 1250 10685267 10685273
    0x114010f090e0102040506040e10050d0803041e0506010b0f0f1317070315020307120e070603060608011a0a020304030f03020102030a050a05060a030308090a0212010603050c060a050a0e01110a 84
    0x19030390881e050320105100d604203a41c6118200d01c658810141e200004001c108103092101d42e6596000c120f40c0d440d41d00442c1c1e15404280300103180034044416000000c200001c0103100f10719812151400240c4d00c1803c4515500d0a680f040d06000705c0314030b0900422070004403135058040b280d003004046180c68440c14603034403012140c2e00c5400fa9640d01140d80724030740300300710b40002c1000c112904003252080100340e81107080c000390320241c804401c200c04800702c0c0e0036018141c0101c40681c00214001d1a18a10380701008040b40c503e50000400c000000d4010482101d000c0d5004600561120429541c0e100d03201041e4914410b5500003403002c60104002c005041c1c040d0f02440c491910000240030075074962100000f240c000301d0310300317900424034201800801d104241d444d03031000c5180201e814150494001032401625041c021011f60b4482c9818010401c0510490070010402e482c030030700703000c1024005001400761428410400501116179006a881a000d541148903090240c4500440c2e42c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 10687767 1250 10686517 10686539
    0x50f040503012a1403060105070f05011a1c02030c040e070e010e09010b01030204050117040303021b0c040c020303040c060c02010c0f03020d020705010e011403060402040806090a120507030801030b0405011401 91
    0xc6014510f40c1d100e480301d0722102d005080500c020100e03034512078a16642c140043d503180d0051343c1f059a010701c5402034000024001d100b40b005050700038030401184100c5504200d41b008403c0c81c07416140d6101d21002d0b005840c0003c5540710240c0072100458800e03426840b451400d4495400204400b04040c00024a07200d00220103000750001402444202000b02c01942a4400c500c00c0900003414801d182080170111080150040d202e46000742c602007090400b00000c19401e00040c02d90f0704110740c1c2150b285010b118189000c3e032180013442c29460640c8621004610501c2030384203004080400400b107a2050005c8a51140e10000e019000762003800d000f0750700c0855020420152090290224041d8050441400f2000b01651807100b10000540c00c030b4069000942400d802030b40921002c9412001405090704c0b400c00140200380720011805c002101c054132000c2c02c02800820003281020a07840800241074a030499800403145c0c540d880c00718010b15a00c81d8041d00c207100038001040b0071030b00e5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 10689017 1250 10687767 10687811
    0x706020a1101060911030105130e01020309030901021009080304021003020d0212010e060d020a0b0901020a080403030503090d08010806040206031509010905090f060c16020a0803040603020a030617060106050f04050301 95
    0x108003c12a907034503814490211007052400844c0e071310080c80104208e1800d0035610218000510307000c9405440070310750b1420398000342c0d849080c0d5040410b003000c1c2d9582c100310803175070080b440d10180914641c98079010720502c0007034400790003002d8900500407094000d804940115035010402c6507102c5821509c00c54841d807e000ba540f0070924000850144c0c81c1c200c01a214043d0000c0001155910f82103000780641d00046041d130660103140d0561010480ea07001500046004e42c80b421ba51346003024205040c109103020a0090086441c0107100103803000550591095040e02d40594980b203034070b29120f412240c0380107958840e480c140046080c04a07074011500559003082280c00501c00e4054031915508102c8590311055002d010385035024840742d4442c8000c3d800500300c604201e0b1111006030450f071080d080040400d80019030f10040661600ca0318005280f8100c3e0024598a4450130030f44440307040c40b480041041c08070700301c03040065101c05c41c3c0007410002d0003044041f00444412500e2222 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 10690267 1250 10689017 10689047
    0x1502120d0603110d051002090111030f18100c02060319020c01090203060601110a0209070c2a0b0405010507060c1e090504050f040c03031b0b01090e01110f0406050c01020706020a 78
    0x24003e00202d41c01c000f07820403d41075024024295845c00101001d00941003503040a0400000c0c2444030202c0c1814802080702c500c55540142e601c1e00c0e514000d54502d020300800781d000724503040c140240190310011011041c0c0d41158025900d441da0840341407001c2040944101c12440020030106d90704d0154082d64841d4800d400383c845a9962100540d034289403510809070f150040d04000005180111b02913500142d907040174034580301301d611f0381e054484580d00c2440c2c8030b891f17602684140b040220202c500915604080515181c2040002411805207440040641e500d4445030303d102d034002d424030506044031070b070b089080482c0c1d200c1c003c20310101f5108140c09249000e0100c1c1c85005d0b2480d46034404c6030441001e0004034070790396040720011200b4260507002c083e0302c2e8200c800a1000075005000304140304000c51966a006241c0f42190b41021508a00440170002c40482c00696011b175000c4640074140141c82d009008850b0f4060310603518001c02081c800580104601e40152000f109407072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 10691517 1250 10690267 10690283
    0x204140102070911121008010e0d030e0703030f1b02120d080105042a11100905100c0e0d05010f020f0a110309090103020d02040b0a080c010f03050f011502120d0603 72
    0x160300c2001d102210203c0d061302661003020041560a066200f018640007800205194003207591141418211a0f04000000403038101011020007030303074103004608443d03481c1c101800c8032514683e800340a0716012042c080502c0b506a4242c08800441040b0004554000d070940c14110003806105450342040d00e000710200d1130070030000c200380c2005e219808484440742c00b425101d080c25031b00d150021280080c20302c200080295020701c180d6050111003229900c50001080345c140c14a8a2410080034800f8480c10928025240c034103150b121000304140704046c0c1314101440d0141c20f20030301400f00340504020399400018030004502c15a0001c0058500c40d41d10400c022141c144d040c1d4492003034200c40c641c000b07140700040c80946400b9001e42902c500c0280005010005200407504c0268903510520040d085040d0069155800040c0f1255201c110326041140c1e14042145444807a0f06001d04070807481c1340c0d002c42030030328000c01804000f208000c03606902c400312005440087c2c0f246000071a4244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 10692767 1250 10691517 10691519
    0xa0f0503041802070507050103090c1a0406031b0e21120a08070c030801050103021602040903030b04050a020702150702030723010212030103050303040311010b040204060201090b0601021906020a090504020414010207 94
    0x10003d200341d814413039000010700700080c644001100a440f0504040d03070b96441c0740304000364040d01882c1c00140341914080480c1c40301c0c9041e0029003182c1c038140100d042d4100c1803255541d141da01245101d004039080321031014024007040034500600350107003207a113a40310389072611001c24040707005005019a19074611190395603c01e01103031040c07461b50005011072030380d038010700444d0b0094000d0841c4183d88510b43c1078610254000506031038604400343c3c0842e40e036000020046c10140502d951013404040250710f0003d01c0d9000c02c00f01c502058a00e0203c000100b00f0380110346d01801540300500d500742065461040340d00c0703001a41e083d00c0040d940940b14680b444418040b045060303a0499410402850440c0c0d5191016100c511440c1c60b00029550307a030302111142d82d03452026101900d119400000d2004e118a40b01c04003880103800541554004103441e403140391701e2010014210b50060740542c55030341c404000d0b00c0340112600886d92050000c28007081e410033541d041580b01200740d003114901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 10694017 1250 10692767 10692809
    0x9020f0a0b0d0b030c0604030303050a0501090e0a02060c03090306010314070501020703080405091b040602010f1d0606060703031803050304060515010509010c050f010603080304051606020d030e0a0f050304 90
    0x40d001510801034408028411030301c92028682c0f02e00d42c044406001d680c10726040000181c11940182c00480c00300e50b43d103041c42406e04c40780c400c10f8050401d0304020002c2c0b048130301c6160313551400c0640092080b00000f074220300100041c41902c28040001d01214031558507031510722650710401d0021070141c0724010000406610005407107003229000400b0628048c24a01803040410f001807650002c503c042e42d018144080f14001030000303004903030001516050035411041580c40384100a56a204400410f0600100105000c0d82013070085405594421070744c50b00360301612404011030489440d062035a4107140d0484010751040e03204003030800081da28600c40303d8402100700310850004070b00707000c000320325402100d011103401d015030102c40c40341c3c0408060900f5603c55400c202d40260002c800e01080210810040c484048441d040c102c030785090845c001d54542100140004064854169403c0710344188000411150014050b0702c0025003824000c1d5254410b00c40c01e0a04030983c82c000b100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 10695267 1250 10694017 10694029
    0xf14010b0a090b0d0203060108030309010b0a05062a1603020f0103050f07080604060b04140a0b0301060203030415020d0212070e04060302030c0405040501140415060603060302180a060504020d09020f 87
    0x14540c40180081103003410300b4181c400070b00d1041c2890340c0007000c040390000940c0d01005498024098071004540e41e1801040403829108101315003030040803628014005582d50707000341c0341c07101d01e160005441c0d00c03220007d10300c540103480007900050045501c1042e07048446117410040c0c07402607a1120a0f0390100c0700441c204c0e6801c07a89240c8008204c40858691840790010780d81144004001144c502e0300c1c0c03003480c18940c1c0964443c2c0c84101620381d102d503460034840c000302c00078110640c1e03072070a640c54800c0c041d49a01c00284010541a10b4242a81c0f40440ca035042c1c4082c5500c1c00b40c21500c0d0681100c0740b0540170750565609011408449807000c442c40c246c080c0d601502c0c0d0180181030703000c0c1c1600072b1002806010b40116255500c40c46056040071074030130000c0c410f50040c40d60386400c2c03c03500b1682c0c0480380e858100c48209400d2803010b01c0546c0350142410340034880b00b504040c2c9907440850110090603150007041d4046e00000c0c1004050034160002d0b280d01d0f0003211a401307040500d004000c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 10696517 1250 10695267 10695281
    0x20f1206040c0914120c03010c031b09030b0f0613050103060203040b06030d0c230f070314060f010501050c150a0b031903020d05030a06031506150c0305090d0c0906030f1401 76
    0x4181360601098191400c141106080c6130744c01500300c90714015404006070035078180710440701c0040d80c4c460461742542030b91202d111192000e410301603502c1e4103646900309a220b00801d084050301c000307804210f45840e01c0c101c83c002c80ca41404d00300030558503464244040d6000ba6019148041550f010940d217280203d8030100d107000540f292088a821a80d035003121000c00114103102560241840c0306403541030190501c482e0114002c0d000041c19490b00c00704412013086041032030352000c420040045c200b40285815a1001d0815585130600740c40707490300d0130120001d0780800120040074004109a039401a1010348000c9096411050800c4403690f140603a2400150041e401996605044c0b8062001103800500c4141c010850310740341d80700c100c0c40c2c1c60440111000d0390765a0300d082142404044218000308454074004616413043e40f0003c02500400c030000e4440c04109504500300a44655550000c16500005102896480c28180c858100d03080041c1c860b03060340116009844d1043c44ec0300c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 10697767 1250 10696517 10696529
    0x30c02070b0a140d0c0302070209090d0c030809011508010506030f010905070909020d06050103030503151e090a06080105010f06020d08130f1103011506020111040501090b030703020f1206040c09 85
    0x70b0030008803030000c6a103542c00320000c2e11001402c00100d06540c40c103000354822520706440260742c807034092040c000e00c0744000344031762141c0c1c002d207240d141516405295a11a1905403a01032002d444240c2d4050040101c903c0300170718100d0700c4000081050042d002544112022025135444456903c1c0315401d031821010000c0c17481d0814642488601950791001c00c0040c0080d20300c4c030700402207664040c111082a0401e0700450000302c200251000c1d4140039100541c0180d1b060035400b080c540c0c115143e078180b0242d161291071644001181c01e1050740c8a10020311045000340078559540181c0e581600c2140200b0700140a05caa001119078011841903000d020742d02c810724a110001e031140217510056040c1294200040301c0181c1d00c036a000d0041d0f104007003609056074070003807801d007000c0c0c21180d004001c0d86500401303000401c10b81ea0001c5211040b12174441c00725540e03030380d203001c01c0f030007032181c1c1000f24480d403030200c1c011070b900d0100c4454501c100401d0700d00b0004e040304d01c541615151440d120701e07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 10699017 1250 10697767 10697789
    0x1d0a08030112030315091a0d08031b0d0c05070507090204050307170102120106050d0615020a140106051504031505040f0201030e0a02060c0a03020c0409030503040b040503090603070906030c0207 85
    0x1040310400707007040601018040d04c0c001400b41002c0b6402c0405400a81c441510951100d19520b001031001c41c2d0243c0000f0301b00d50300d110908942d512030307400d804000c110301d03a107101040d000f034840d5030380c2400c48510000d06182041015103c00010f045134000034020b0700c8034400d410700840d19040701d00c00c40c2d041c2c880040091547e107242c69a4150203c16502c00321f000e55409210500c0c1810030b9a1110f4080c2079103448840d00d03900030142d19021203450b82d01c20710b10741150051003090a900800e8202e40d00740c100d0b420803000441c0c8280c05014100c0c07a4095604803120060092601c1d8405001d4004c1e20b204464031030190070582240815100e090b10003400c24402000c00720019030107580318071040011001560b4210310540c0000d180350300000d004941036000302020704101030341440a200f444c0c0003202c080140b2035031614010207501005000603d2502c40304041414000c080050b9034071b02d18020600c41e641c2c40c02c014000d02e03e8005200e4840400d08140c041c08040d40045868030586e080d45001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 10700267 1250 10699017 10699019
    0x11407080103080f04090614010225090207020316080102030603060a05010e01090e160611011808030103020609120a050706080f06130506060706090b0f1f05040504060b030604061d0a080301 83
    0x1881e030f55a031141d004031840c080100400144d00382c00303004903001401801e86a048541e508400603040030812074890104003240f10800c2c0c15001d48a0301c41c4181d4012100060300c4000510110f40341a68420180c448154240000140000150011442183c0c02e80030f03500142c0354050600c058850a025a869010140d40103000c40710340b43d40040200e507000c0c07080301c111801c616903611042e646900800005070b4000d000f1075049000340104400d004407107295849098280d220b1003003602041c00b0091040c1c2c00000c030284241e80b10941003c3c00f40050055070b020700e00501e402d980d40c80080c40b881d000305410000154083c40613002c078034403c0001402c00f4030040c0302040c1c4200100402401543d01c96410b0010314003013840b034410411454400c1c0d28596aa0802400100b20210020309071440d0341c403054080c102840c43c11000358101c940940340410561518a081000740c006500555003500c03e15040009005441d00711200d00c1d0503a21008641004803480261602c2111601a00000c2c00b000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 10701517 1250 10700267 10700273
    0x5030d0e0f041b020c011d0303220b030705040e0106090506030f100b0d0f0e030a02070603020903010f05040b040c14010903030c15020703050301230906100e0402040602030a02011407080103 83
    0x180301d008942000b040041d0042c8240350740503030804010144801640b1501c2d040400d560025a981d40d0406007921014640705c1500000e5502d226890010011990001c070290042154101820282c5005004141c69160101009055412034442c0400b01140c2800008a16001d4040c0b441615809441145036990300314002e803c0310f80117060103000c0a00190b00049266040028000d404001c4802103040c800d01ca0b5003d0596107464124402034208200001c0341c0c9030001001800c41c3e8a6003009600d0304000c40c0024010140d40b08400314003410407080004218019150318404d5202d00541408c1e1030b00c1d042e0032410f07622822211804035180308d005001081c003a49480c0c1d15248201c403010391140500b04441d090f40c104020807004640d01000502c40040d900a60030003042404902c18800c10b42500095030300e95010300740300c1c0100401c18007241c119214940b904015500508155680e668a6100075a641d10000e071000041d442d00d190641e06a420039480350250000f9542c2d0f0000c0e0342192 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 10702767 1250 10701517 10701529
    0x501060518060f0a1b06020409020909010906050f0907020c0a03060209040516050f13050d03020c1008040503030703020a020f070b040519050303030604050c0d06030c05090603030703020619060305010501080304090605030d0e 98
    0x2501e288106441000345c80002c0060006001030070b642c510168649500409115074048103070400404036060071000e100a880e01e003107090000400319601c0c03001e9110b50a042c1e08000900600a8220360001408400e100c0d1603001041c10a038243c42c10440ca0340e81c6a003401b600c10700208100d0015904100012102c82007901406900b9401a01c001ca0039540304c0008000c0100e034481200540c1060712254034515200f95901001c05013418026000c0c0707826941c00740c0b030b44001800380080c1640410400030301d610800401000d201035000326908141c035402c1c400780d0f680192117224418000c00b8a09049080c41107940710031140d002d802142142c0700d0a0401004e018024640000900184145503030403100340200c2e4000d500400750302406504050501460000c02840c0c180240c0c400c101c0100000e41c0043c03103c6d8001500c0e684101d01401c41c1c4c5491005e0700c1107a1000d409507003004000304007150040020701c121460010200101a902c500b81921214881100000310b5440030745107080341170131 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 10704017 1250 10702767 10702787
    0x20604080a050c030304140c0904030503043306290702091e010308030103050607080403020307060b0a052707030b0105190504090e01021b21070203010204090501060518060f0a 77
    0x7400c2c02c81c1040300565985107150011a400d644801c0d42030111105010b0034040f4031116102651036030f2052a207501c000d000d81c400501300a100840000008600d410006d10103c101d03003003111824890340e003e2403158040c0a81b0700810400c12143c0002c05c11726202c0c841c900403462100d0300b00c0c506001c480d800f00141d034a0000c186014442c4400449101040c410090038040c2d4801d1100075225410341c140700d49054002000031050040f000288070102e9000019100c0c10f5a104501040703031850000412141a12a801a6002491500720084900d42450a000c0318841c160300101e9030b039103840307044050742c0805d110940820f004001c00c41c0502010fa2100003c00c5e0705080c070902d0590b84024070320841d2070240050800b070350301059024151500f1825210a60a50001030500d00c20451143d10a400030000c0702c058010000b0b543c1e0111344007901074800070b01c15420104010f60751040007a145600c9800359080000c3c03440d8110866180507410345026410070802c10b410440700180681d42c1d1109 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 10705267 1250 10704017 10704037
    0x1009060204090e030c01060501020c0105030411040e030a02010218030304260109121106060f0604090e0a050f0c010906080405030405040b0103090f1101090e01031101050f0d050709031a060102060408 87
    0x800012484102c180606588400590019940d0301d048400310ba003110b80c0d1b07811840c115004846405041c0e80d000d419a508144c01c1544a1403801820380024000c02c49400c40103400e00001c90034000c80ca8041d0f01030568110713a103540c6807211034000708050b100d1042e40a0b41c04580000c040304041010003080c4240c0d44c03510000001545819911615800c003814041d050004519003006040c0710428003105402160541d03201c00440e078400300040b5940140d025103208a6a030f6a06008440800c0002c0000b072174100080c0d4648110000c1400d4541541c181c0e402d011800c6604005449481031034050701c150b130404081c5052508140801020340f040002c070303604145c0c840e05003a0118610750707158441d007031240c09000c049458010000d000381d10503500c141082d080101c01000410110310441500101c24600741343c0d02c1c000700c0810307802401400001080c441c503020070482403680046804013030701c0c00703410f18501040c442840e01c1412103003114201d005030024004180000c8110001c1c0c148004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 10706517 1250 10705267 10705271
    0x20d03030914070806100e060102070b0d060b03010902090301051b180d0b070f020106080d0503061504030b010605030403020c040501031a0405030d110301090b01020c06180303070209040609060507030b03100906 92
    0xc2d540300301c60b14080540c0c000991170f03049801401000566114144001c01c0c40b03050322419864403070b00107502e400151090381c2c0e162400103100d50f421189944040003030521100002e0310b03940c5500c0ea07036000307410101c4c0c0c042c065841c200c0450807807440385203040c0b04207a02a048600c1c0c541240c400020240b5030700156600102c0d1074940d00001a00112078038854012aa03c0076402c203800c0f9070003829502280e02090264010000c9944810390040c110395200300203441c81d100c2c5c001000180303003480c4500e41c006090301d117032000041421640480114010360003079080f11515031a060030042183c0c001c0c4402060546556180401c440a48405560182c060070030390b824201001d80d4601030702d4441075034101d1800000014010840135100b030581107042807000b08007291105d40410b0141c466002840c0c04818104240c222503541001290070703c0b0390181c00c2c51400e0500d032800002410305080111811401c00300010320680c403c0c81191119140100140203a001e07109620008219104003514465 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 10707767 1250 10706517 10706543
    0x213090b0105090409030503070201050c0313060209060c0109050303040606090203010b0703030c0e0301060f080f030705070605030405070503011406011d011d04020d05100e01090b01020c061606050a02040f060309020d030309 98
    0x1940345c2c441e413800e560081e00c50696900e440d210003421101c00400c042c04003007040c024082e481d1642e4a078018415400940143e5908620700050311074043e01c2084806582020440c008004000c4003450060780304d568144540c5071600030b1801a80424000c109019070140035180c0402c2c41780c0c0100d43e100d0000e0801810000001d4046802d40715070340c02c56256440140b104110f18001000007040070004803001e1418405c0039500c154403070810b03220328800c100e0084042001c0c40400c1c003201c00145001802040366260707424480108400c219041c43c04203205401c400d41c1200c0e0014007038442441650740c00302308000e00c00010501400c0400c4541c200e039007801403100c04e114620403603026060b401c070301800b60352400442c10301010301600140a85400e1000c0c071075099800148190f0a031204131100d0707885050031103604403003818181c8042c0060342420301788100d16070203a0041056414141a183c00d261312440d007074064035000f85009420038407180d040c10200c2c2c400e40c8042d03200d500c41e0071244481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 10709017 1250 10707767 10707769
    0x11040b09010807050f040203100603090c2d05040c08160309170304021c050604021507082205040608060a05100b0301140906010e03150c090301090305120105040213090b010509 77
    0xa0426000082d40e80c1c450f200a00c103e16002484180b403da046809514600e880e507131010b0501b96601c40c00c020706458a0030f0100b0032020766072800240001c000308050420056034404007140b0340e501c071000c0c02c3d500080d010586041ca4021100e08a006888111241e120903d0758641072680e00c0740c0380c0c10503642d0040e00c00005c1c0e4002c2d4440d42c14050b001d50030307107900702801003201013910080000c402c1079680561400155000ca00a644a82c040710340b0b100000000140030301c0c5104240005040b0900041e50021400c51550200300c20300c40e80c04211005511801440200d07245030142450507406907000842c149620303041a540f00c58061900b01c44107036035032000c040c1d035042a00505881d18610100d12046d013800d841d15544a03800346005483d40d112040442d845289180c0414a106005800520441c64010484e6041c01010700200320459880c2002041d40d080807400800326008d1000002c0d0310325041c000e40350003d03d40d4a161010500d04968100103103003660b0000d0510005002d90082 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 10710267 1250 10709017 10709029
    0x30b180f1b13030203150105031504050a021c0b01050109061409040603060e030318010606080601050702030106050901060c020301060b040b091c0b040605010815070806010507060605150415110a11040b 88
    0x2590b02012286207003541148100340c10004441c04891071030b403a840041140d80c0e4001104443d020741c045505c3e40a480700d0500b00d040010805000e1b4100c24408441d824041684c600f50081901a0301e9080203a40c03901c00440c0d0040480c498100010540040712180b140d100000f0940310384020700019035580c2d20f40e81c2209071041050004410342020040001807880b40c000c542450f0f400d80000c10519090a1000c0d0006002800c3c0341d0400c0740204500b402c6440950004001c0c0038005d14900e01c1d5a550a0010729001c03014208a01a5082c40d00005203227895030151000e071514a2181420001104140f000c1070b055000710b0360140e4203d03203045011809c0348280e80d01460281402042960400e14104c3c81c160040c0301d07191008820000f0440c11540c450341c0107030040024a401b079991002401e0400107002d0f650095030b406030054070216125280b5400400071a0030a1040140d017444451081d5a4100444240d00071074210b841c00e01c0010f54007040d4070300130398001000056030107519000710b07038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 10711517 1250 10710267 10710277
    0x302040609051803070c06050901110106080706030b0a0f05011103130608060a05030a020108040305030a022703070e010b09040203180f010603030305060303090616060b0d05030703030b180f1b 84
    0x202160b03a1414415488140e0050b80304941c04140150310344541c43d170b00e84400756814421902004004030300c40e649a8425000c203100f1168001c000d101d03c40c0c9034401c05458654a03c02c000c0424503060406605e405c02032102000c4841000340d24002c01d180000558888146040c00b8409000070004c1900c401c007030604180160500e03039980092480c290040c4040f69100381c00280c03096000d00210301c0141c1e4032640c00340d409a8545442a10780c0c9901301e80d03a029014000c5a107212007604c03800f2000001e401319a004016504904540d80d4a40da803040010201081c06200e03211001005a228103081a800541d04903030901700c15401d0f403090300ca40d2801c00d0302402c0700101a0351112002c0042c940d05004081d0030182c1203001d1403030002968002403851180000f903800902c1648111001d0141d140e000c40c040880181c0001501410340c901940c895101582c101c001c41e11b8803d0b26401c5003400c21642407000032010089a0545402c0129480c1440040a884010012040d00c812400b507060182c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 10712767 1250 10711517 10711529
    0x3090606030706030204080c01030e010e03040b071502070503040b0723031209070f0306090c08120c06070806060d05060307031203061403060907031506120b0403080609070206070f050403020406 85
    0x4500c0c20010101801e1003400d40c84041010300601c02881140004501c264610302c003428001180085154028007602c170341102400381340030101e000514421000c0060041c60b00ca240c0100d20451034030340384422801810009005e5a00c24041805400404001041d0301d42c050360320b500c50705010200302c00f002e0b0540030303410305103800c080750231282105006821a080039168000d051003034200300500f9464400c1d0f21002c0e202c10340340c01c81c0c4414031020400c0034000d011080185d8020300d0b0700f40030704101035112941116040c03003140700080d110b501c12030065002d407400410540c50010109004005010080c1c155613160041810000004001e0100c00f000d0942d1a00d0110300ca42c0380a0402040c41d0720403401d40e00a400400030060f07209808074040003903aa015822450306840c071050f07003004011941162591440104035882440320070741125104074800d60300c542e19907440c030051014014013601c1c3c40005d03078400d1300440d4205010320300221030100c191030500c0c24a95aa00004c00ba20b21a600c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 10714017 1250 10712767 10712773
    0x2030a0603031107030203060601050a03020d0e0d09090c02030901080a020d0606030e01140112030807051201030c0e07020c0906060307110109140d05070c03060203070302041502010c0e040605210a02060309 90
    0x400802d5002000380b05001c0341040680541451900481d45401c2c0041616040120004202c6e82c0b182c02a8140c5a030032070280400c000c940b0240b0b11031955090142d40c40f40c003045801da00080c2a10041c000c1351a4840950301840c00d110599006480440e009842d0810058092003e810003400781d114242c02482159008650444c08625040c00c695a00e072010007604002c00061007425544210301c00c0280e0715141a2100380c0d02c01d0001c0340d507805031003600034041c1a04070002092001c0400c2c0881079843e034180c82d00507030301d03580c400741d80c1c0d5150f16810a81101610000810031f01e4031002441e4030032501c1c01e103000d542020060070b0b4210341e80c000c01107421020050003200080000c11044859500070f08016141c91501c2d101c09615900a00c8014203045d000400100c14921a03010390300240320040361994008404139010340613100c0c800d04000000e244400d5075106103400c0c003901c0100c400107020040c040c16402e051081250603941c8184c0c90380b00301003072400140c9030b2170b00841c0319078110000303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 10715267 1250 10714017 10714019
    0x10e060c0604020909010e03120702010204080714031002180409031101020406080103050606060909040b0402030c060a030914030f1206030a0c031505160e011805101101110412020607060f02030a06 86
    0x42013000c68001e4001407040c1c1c035200321040d0003000001260745420760a040b120702a600d849040b800391145402216043c0a210320000380a484020745101108080301902c2c14081b1140b9041c0807400f0340c0c9484000300b1f841e5000c106190403d80c1c04440101e003c0d240c940c0f4a4500e40061509a0b44258449800180c1c400010014003006202c0e6940122040300d440d0b1404a2110000b540035002900151103c00060040b404544c2c0c104417441410310003a1420b030301d84814840180007084220416509100c1908030115080008411120f0200e1084006d50034800462010b0758003803c003c2c040c50301485184110001301d824001c00e030001f58420030b5a549002c43c20541d1905440c805081c1107000a01e89070700303030001c581061950300d40a4081c40c184209940314540c121030207841d540940d4100742200c0501d41c88036440b1101c070003a060f03c0c01c001c5c08072041c0b2013410b0000c0d1123039100e400c4440320200544401854400c0c0100701386401880003180820000300c0f08000ca80c403e071881201c8a9039100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 10716517 1250 10715267 10715269
    0x703090b16020f0301050f060613080a14010507030b01020607050703030b0306040c150503010b040306020c0a0b0a0606021203010302030a030f0203040b0a030504110105090307050405060103090602040305010b18070f0e010e060c060402 102
    0x81c500002d0303242139009014904141100303144d40031015012502c45d92000c03490200035080400d144000b8028282120450106800c0081000c000e402c440310a5500f03010002e01182c0c0a40036440e4201410790041400da5240b0604071502d8024000450130540c82e192810354541d0104a00c4d40220b0140088400341071502c505241c00a003e41c0103c404d214083c80100111403122058400b101d801902c05644c1d0031501c40200c0c1406c0d090000101505c421030140841c4822551041d0183e643e540c01f280c028107402c2540c0304050009210080d0703d5030000340f60200107407040d4070a810400d49401181c1c201603e82c95100441d4016400020001c4d98400030401031248243c03120406c400c082c20214903010014001c40c0d00e842c61801080e000d15212404a200c0740d00c680d02442200307401000454585403a031401c6030192040d42c80d41841400e11541c2c075080141c20a40440c010410b030748031504104150001903400e04981c0500c0707410301103285040d2640b91a40c00041900d032800102400302807074284 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 10717767 1250 10716517 10716529
    0x3090105070f0905010c15140604051005060d0f140906070f03050103050307060b0102250e0601051603210509030c010e0c01020d0c06090f12080c07020108010b0703090b1602 76
    0xa0814007005684032012040b40c1d000380b03801c0150360003803800303031950682070808445011215001440c6146003c000007071804110302150700881045030288070589540395088000d8840703008080d404401081190100d814680c0500100e481000002c20003814080c80c0310a2010215404509034104004101c50b6031fa10050b602d49644c42804c08104550450300c50030354901a101c4018a0b6564442414545070700810102a401c03103002e501c0142c2280b00340c0507007502d050b684152030f400d400303a001041481d03014001f515551100c0b580040303c000084c2e00c041b5400407003104501252401c40042d010300402c54011b0501c2103e15200950b41c455a46a8441c02c417074031800380e8a0305400c0b401405d07a081e80d02003640c0120780064500300405031018145040140503000001f82103100020b00c8008000400e05000c68095194461101d42c0d5521380790303011240b0603004024009903060b030040c8030029410b006800d081d40203142c0780d0109600d6141010255204442811052030507181c904110f01d007070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 10719017 1250 10717767 10717771
    0x20a0303230c0c01060506031e0a0b06030f13020301020d090201020606090108030414030309031c080106050412030809030702090711070801060f0b1608120a0506030a0f08030709030609050303090105 87
    0x11540410712048400403184149074058006203000800040c0004a5103003500450042c00f00142120395a05000508258098442d15011591002c0d14001484030006110340c56068030041c1005207543d4440c0030382c5d80072000050843c5d441920300c442c64005602c09101a003503075400d0000005550080d40000791600c44c00a000501ca1501440103212040010040d541180c04459000400340000d400081c00e5000301144c0503050300c80d5010410800d0700c10840d0700030191681d252100c05989480c41119903200305d0288440303000a010500c00001c1c4140901079124180e0300a885c01c004459000646000b01920b04100082c0800c21076480030b00c040c4901402448450005c1003414501400c02c26a19000d02c19101c43c0d0402090b00100700001710314903810540d010b80301070f955043e05c021800341c00c2400e940661100345008000783e61800d00140c800c84182e0450101d2003414126500c440365130341b00600701c90030800d03e403200100240c0180a0301c00807602c180041c0d41c40b13240000d07140f4215800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 10720267 1250 10719017 10719041
    0x150a08060a090203040201120b01030902031f0b0d05030406050f1b0c03010e010b01080a0c0908060a02030a06051203031611030a050c060f01150c05070e15040606050903030d020304020a03020a06020a0303 89
    0x4104217010044c2e03003040c50140c03080d40c0003401042403034034030006800607d01101c01a40501900c1008070b11022010b000501c108a00c20080015030012014450f04d0050000003c3c10b41e8400c00082c012a8010800381c40f5400480702094500001c40c00302c1d2800d803255610030107095108002104107413400b03021b05001041d6003802006a00c038414002881c0b81e00141007801043d0340d07411194010f0340303d10820750140880c401114164203024800340c0080d4002c0318501c00e01480c0240202d03282c81d00b40107115046e0350381c00086040d501c1d01c0d610304c280300340d5600c00300c0284a40b100750b010360003400703001600c1003108a0b29500c0d22a4170412002d400c0603401824110b1149240005004483c8080201c0d4520348180c03401c6c00f805410b61410350321740083c40c0c000d00018150346080100038120401caa10b02640240d5091202d560b907081d01307036024040c1c12469a40b6400c00c0c048441003080c1507000c0c5600c14002801c2e50b4000b41c0e42d0300403907a600e0b02e5402120058224140c0102413542601510b242c0000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 10721517 1250 10720267 10720271
    0x305090a1e05040515030604050604060509070605040603151e030501110405060a0503130606030b04021008070203040b13030602030901090b010f0602120d09051506040c0206090a020f150a08060a09 86
    0x24a8285059031807210740075052103580d030f034000f02e01c481c5001d903e812143c0c50094125001414982090f0b9690031044408070b45c29030511001a04050000c2101d070216161030301c07400d04041c1004815001343c494000f030080b07004021040000d803415102d64000001d68119040c3c0c41035821410005d003500d18100c032210035070000308410041c0d6140c00781165860450391401ba612a15584110140b05284000c0030300024240500403061029001145024610803500c950002c04002c1c0150f6620904581d1100540c000303210400c021500301c80100241404d1443c110351050b241d0340c1d194201c3e08142c42840c103c2c1e40d18440e0400300421710518602410081ca03e1240c4c851824100a550381c203100d801d80e40d05c51020038900c0b407000054200300146a03212041e1210b00c004400645528a01210190b103d0703818183d800c141d00c0d0020651a00034120400504410241e5400740403482043c489540e41240221024000c07041404019100b1301c1c643d642e40c0341050070703c1030400048c0f0400d5005088094 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 10722767 1250 10721517 10721549
    0x20d020c0f060c030f040311210601060e030a1a01050103180807030c030302191d040902030c12030f04060909230402090405010f020406020f0105010806042310090305090a 75
    0x358a5900e5202900021500c840d40c1e0143d40042034154001c041c400340140c031010030040f04010001e01d40120510060795420404807107145012000c0070805030980064203ea4014803025201e12008180003402404070f8044100a5447d003150700d010700012412035421000503c07142d031f81805041c0042662010580c0103c0060b120b81d801403050840080030f03c8200e40305181014003c2e0183ca00e03d00c0c0d07581e1262100d03001520702600d0034900451890980d0b103050203219081c0392034840d0182c01c0b5005001042c6003c03561040c090080d240158400c8103110034482c000300540307040000c0001d020281e45502056150003045400e6824014602481e40080809100c000c1e00d040c2d0002c1d4003039012940c10045071254100365004002182464005500000300400c41d690005020700840c14018001c11003a03985042c103d45552040d1802000212600c0d15048000c054541c1180c01269080c242d8080c084c411101e442214061441200810404a042c09151528402240051183d030f00442e10721 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 10724017 1250 10722767 10722769
    0x1201090c0807080f09190b04020301061a090d021c120f0201050c0901081314030702090a050105010509060a052106010f0f02030301060c0501060914190b01050313020f030604030906020d020c 83
    0x5110020804528040c1321000545032102c10424030300000d241a003e410035001d682085002d5030700403181640a5803c1c8600041e0140b0303808003050f0300055590355241065030704030400440410000040c4d03440050314428404080b10180d503050381c54801e0f2602c2e00ca250042d0303400b5103002e91452000c4250b9241034100315441381d0140c21507190003000d103010320003a0780760b40102d02d098100040140440c4000040c0c40031820700080105111070084a01a00075070f1002c1041d826240c003400303024006101400881072a0a080c80034046448070340c14454200f05558442c8800d407032401103540d1480084005000c0c09581226030354240700e03158540301d40407071200d1502030741d248418481c0700c0803c03406900440c18007000f9801500640302e42d44051240c1100302d00b0100c0c0e51102501c040001c0b1044200310200242130348610491050180c60b103609682d07545540848007440d51a05980040da4080c87c003185903024055188a00e229890348140c290400030024901900c0514034000c1d50300c4020f442c0c9003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 10725267 1250 10724017 10724027
    0x10e06030901201306031e0603030f03110c070308091305040302030403020f0108090735030903010b060c0601030201050d060b0307020622030504030f03030204051002012301061e02070b1201090c0807 87
    0x1d8900038200031401404402039070040c1f01240e0107a140c018604003011042590281610000300300a6030b040c03041c101a42400d150074031514010308136036407000c58100005840c1201400075488001c03c6181c1c2e0080e0030903240e0582ea4200c40840041c0c20002e010b20842c0780c082d031410b00200013843c00f010b03949404a03240f40c0d13030881c5000d20415104145451030340f65600200d08861440300415030110a0b40c21003446a880d040113014500c40c4d400c06180d031903907040090998003140048070080900e640f03150019216940070880c0303101455180d40021660040241c000c41c000d11555008100c50701d080320b0122040d8840140081c081c800d0b001d640c00100e64468103a40a49030042c100034240c0d5124981a0000c3c03150741e2246130171040401c265550203030194020000d80941c4007a80305404110031101110300c3c8240510408034054051035161040380e40700203214031202c0d0044608060b211484000c0940110200348005002d21006006103d801e0140040710314140c02d010354541410080a01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 10726517 1250 10725267 10725269
    0x9050c0f0a0804080f0a0e0907080408040e04030507020604031505090106050d060b0d050601080f01050106020105061309030c06051014060406050703050703020715050c0d080601120b010e060309012013 88
    0x4122014020905020040080b2000305d02d003001c131681e40ea21040e50282990300e44d8060a03100c3e03131440c000940c2060290201902c00c0380d0040803245050700f00300c031182c40000c5c050001c1d07041150034412880140c0702c540c0104040e5020316441a403000c01800c181054400040c098562641464020829502c0d2403c061085030780c80340c004102014020302142140340505000ba01521400000040140b4042500320461b54802c00034006da82c1c07a294207a080c1da1040e500990040c840750340304bc405164903489040603912919007031107000125240c081c1540d00548403000d20110050003042000c00190102603d00800e440850401c3e02d0f101001c7d007207000750440542405030004200082520910002001c1c00b8500500d0394000161400100245c2055102e09480d100d102c1810308070500034006075118582c142e4400380310030301d0000c0b00c10182240c54080ca051103141d03110800f0564580703010718480c40799a4000200c4003441700d1302e2401c01e0032803140b0380400082000368100c0c0401d000c070b03504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 10727767 1250 10726517 10726537
    0x1b03100b01080115030b0402071a07020102031311012001020c010c02010b03060a05061203070803060406060c170c010612050d0305060a120818030604060c0f020d02060a111309020409050c0f 83
    0x41c03e403007904c040e000360400f00c40441e0f10903c009403001c02c1294a542031103000c1c0c52207055200603a10700806a00300d01c0240e034102a00070a4150300342c001500d48402c000b07824010315180240403c0903400000111180034103405507500401c494501801c01d100784990b80219100902440174441e01094544901801c4145010341b2403002034515202c200d0100d105040315804ca0384d0341e002904254002e50000e8804e81c0c07260303003401c8001440a200b80d441103010364101c03da8021020740c003103141e5002d41c44036030b079030030b841d500c07640c00040484603020021080ca02400c0980b5960909240c010201c0d01d00401161189045550600c41c02c01c034440b80e40301e100da103d0380240ea940d0fa10083c0501000304489000ea0602c102c0c0208020403c45401c581800449503c9000042d09210416038850341c131005080c00682c40200016030b1003240fa0000070a04101003140b520f01240c008144c1c0511203030b60003200d0410340010301005402c007180304440c3d012000c0002e807800c0c41201e11810781244541e90800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 10729017 1250 10727767 10727789
    0x50f0d090b1e0408030403020a05060a0f0e01020118050307021504060c060b0105130b07020906040b03030d02090f0604031202060601030603020a0303030b011416050606030d0f1409031b03100b010801 87
    0x1034240c045020300d82c00b21200c00d41c060300b03440e5076550302d0f401d560343d105000807030040d840387c0c1e000201070070420242c5011040d01c0e00d0300c4244450b0100212104103010100e54110740d02c4000c0b0b007101c903d0380ca41a0100f0ba0041c0b004d95034079110703801804680c08440341c4100c0c10340d60821041140640c480c0c040e1010590295010404480090040300d10707008020010505c3d40000c4000501d0296040090002d00d00c03d8900381a00c1c0c0e00c2d0b030b0412044031700d0340905c0c40c1c068008010f02070407040c0300e44c01818a180020295080c20301e6000c00319001d40c1040c3c100310b90501e10b220759030000c942c0400c0716581c0003109103001e00420741107030b0210300320102502c401401c3c540c94150006035a0f00450003007a90400c0316810a071220600e01c401e0750b00034400320342900d25016440116002d41004100e40785030844a460303e080f40100707171a0860711141c0c00304201040a800340650307910b66030280b010300c841020790785100d00003040f098100340c2056460402081e003140380005011103643c0210300340381150010703090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 10730267 1250 10729017 10729027
    0x90402010c0305040b0409091407050f0f060c010e0c09010801050c0904020a0201021c1b02070b0708070c0b0d060f060f0906120608030d06140901080703060b1201020c0604050f0d090b 80
    0x10a5425001310303000034080b07420100c0c0100e4041425400349002901810202007541402c2d002c15407502c0c060300a0580060b030b00f2240c8403181c03e00c2c00000003001d802403c4149003a0701c9981050844d00d8005240019800c281034070700d030b180b03421111503002d4603220000f00a2400c221007036070218415000b4040c000c42c0c0100300c0710032040c000c2d0306031003040130a144c64411000c00320708614024040d040300c2200400302100808078a9100003641d5040d5200d103480c1034940702040d1202d40c0c168010240407a40042c100c28080340016208020b0310090922103404102103041c8202d4000c61b1131a42c009a04200204000641c181c1d07015440f242126954107050f02108070a2400d200a0900340c0c1041c201c0b4440001d102c610800c042d44918101c030b0509030340d0045245024104220341c0401c4c411400309034070102d010b10120300541d2100301c016900a0050309401785d070315141426a00045210540c1340c1000b0200400d104082c001a45c4403801940070700b02015500d01c01921004460045545220001c00c0e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 10731517 1250 10730267 10730273
    0x3040b04020a052e050f0405060c010905070306050f070302070b06090405010b10020a110609150307030207380705040e090c060403150b03070b09130f0e010f0e0705090402010c 77
    0x1d015000d803d015040b013503154030740c2c4c075042000000007506442e1501c0441650358500c0c803500c140e0341c0f04039940a1840c5041c0c0b6000c00c00c030450b08940703a480c541c0e543e14003002001610402c0104000c503c01c51021441d40f90002003030380c0101c0d0080c01d01060500401c0140b0004000401240e03100c1811241c08200340c0b150b082c40d900518901c074042e03400095500b503185006400052014640e841280c544140b040d0030f40a204803406002c45441d040503101348a22001000c44003e1a400160ba00c1c005040c40d10300d444641518801910180000c003810110881c0006070622120528690090124060a101100610301c1c40b03188036142ca41409480030600d480022300100e8101c0030b00038080c50301c407601c0b1b04000180201c203000320820030b031034003d011580c0e04000c1141000c864041c6074541c1065a240240101d000e64184240341540c2c0da40c0d14481104032a208440401a1500002862116181080040381c45001c0385021551121004009650302c0d00c00702c5070312507820310f0f0103824041c40745 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 10732767 1250 10731517 10731529
    0x302010804060e010f0f051006080402060d1b050702010e09040209130206070210030e0d0c0309030b090f0a0303020307030b0906030303070507080d020301080d08061807140c0102070b0f0108060c03040b0402 90
    0x40c3d1241c0d5003842e50051224590b80c101d009000302e4803e081207503403a043e1160078020580e10403240810521030010b0054546a0003801c1d5a0341000d80104203544030364081c888040c0000d4243d40810004140c0c0e60540d40d0280c0c800c1c929400641c3d0701240340c02c054000411440004280800030640083c50b0002c6488520907685c0c801e80c0581005441180400060040c4c10180000506449004402c00d01107118940c0d503c03241d60152901003c0d00d08540ba800c9140380f008184441e18441c480030300403800c00070001041c5141c00381d0f60060b180d041000c0003e0039200c04030441f610801d5144c2c10f1024581e00032007100e801c0301d0340b8104940d031008180361051303030307409002d948100356407000c07000046281004c201203214801d5503840701c1c29a5260410800d009a1640d171100c0c8030400c000c00160650300445003402009903819850741880014030100342640e0020108072180c5e1907060034860710047d22010305d400b40c00c40c0800f501e01d03484d100c0013203011408010006404100864042020f40d1948 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 10734017 1250 10732767 10732781
    0x160602090f030313032d0312140a05040b070302131403071701060f120f1103030405040905010b030d030204050d03050901030207020604122003070302240301150e0109060504030201080406 82
    0x603090726203440807030302c1030f604d4684284801d0382c010450000c51030352504a81410340401c1c1c03039040441030000da2624211501403468100615081d075646010450140c56500c240c866618454003240c1e0340b500340b4040010081c00303008542450b005000c11b00701d904000b16000269290161000541245d4900103840d24009502c100c1040c0c00303509422602c42c40640000090780c04284004844559501c0c3d8101c60501d0135402804100b0141c10440c005a142581a41c1a40004040300d050540300d00008085030001c442c2110242e540c0c0710802c0341400c041c804c0082c080342070304045003002c0c585004a001c4900707560000302000400286c1c01c405030300940c10b81d441d00740c024000b1501c4079100c4104038181c004041d0150b80300f00c0f04401b03020018103948040c10304c108001d00034111287c41c682c00e00240d000e0f0300011051381000c0d0b540040004e28010061802008804901c2000c201c0403140500710340c214030141410040120760521000390072000701c600b200e50a20344006140d070381341010801050704c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 10735267 1250 10734017 10734019
    0xf040b040305070806151804021f02010207060b060708031801020d1103060108150f01050d1803020c0a0b1206150705120d06080303060f040c0207031205070611160602090f 75
    0x800304001c424000000303110b405841c60101220141d807a28006800100090380da200c0c0e003c400d000a114240003400e01c0c40380c0042c4054590898a25940c80c2c40c001000c1d400040e90050b03501044890a02405014800c007501041d01e45614052154440407503901c402010180407010340ea540c02c842c0402541182d210f4000403000300116415588c0301103995006070703007030ba00182800c03011031107011107948400b024890041c10f042c694400d080042d03680da00401c01074a10166100e8000740c02207400031015014038071940c05040140302510070040b030030660342c02c1241c0c07400d810f115510003030960341303000c50700039104886000d4482580c4e107181000788200d1000030514001d180a42004200f060301074404455000818022282c0f40c882036643d82c0800c0390601c3e4070207808141008a4140f0b0340c001c826010131481a1680c0540700d494010041145110010001e8030000e80d080602115103e41c10000c030b4400047c528040d140720703410380884081c0354050000c9500203204075065607a101c6003030701944 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 10736517 1250 10735267 10735289
    0x20901020f06010f060908010203090a02040506011418010f050c06010e06120307031d19090c05070512040509060406080a02010e0303040f06050301080f0105070504030605040809090f040204240b0f04 87
    0xa101c904c110310b260b42920860f40450008500800c0680040c000c1c1d074400c1d801e403c01000023007800d80800c00980409002d49060114504048044900310801003000c2c81c5c000196240341c152180c00100914000e9922070104a001d00070400000008200281140c10089442020b5201c1d80b000070506110100d0260b070b18800000c0030000c1680110715000c6602162011421858900f014400490403042e10072010202120050081c01e1655001141c02c800f14a00749040920540d5058680550b000d0a00031001000c28104890318020382100e03440b00c0150303001e00009140c6400c090b0303100549032000b0305200c000ca0450201c1e40f02041998028a1145d0890205507030b1002c002d0004e5200b03001e4940180110500303903060701c0c0140122070140c0900e60b40c0c145040c0c55601d4100c02024060f2084990342420440c101e120b40d03403401c8441c082d070240301c01c1c1d2655050a104110480d5801403030214007002e001603d1a0140c21600307a84200c44017031381c0199840d010441031110a10607900010b40c0d4035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 10737767 1250 10736517 10736519
    0x504020a020c0a0501020303011a030c07021903060605040920010c020405010603060602060903030106090e090307060c031a0904050616030b030a0302030a020f0105011203030b030f0604150606031e020901020f0601 93
    0x1640041e402900002c10340d9000c1055894000490300c038070090040c104a5030004d546001e0480c000002180e1000115184c0c50901c5070b5940022424043c0742c0412844400303c51040c4144135003881000000c01701100d0402040e6620f5844514030300c5281d030102044290001b0030300c00c59014403031070704480d42c0c0184104403945e10707070101900070700710b60040d4001481030f4000108440800001c1701d05031056504d42c1200140340002e003041e00e80008240019034001442030400154890140c06807003804d948011a10240c0c6a020a03403142460341d1084c802d809040034400401c10100c2c01d19040141920201204925403905a001c1c03c1d066524581520410401c003041c0f40d4040302070440c0b88004d0b400d5900410f0641d10b0380c2e02380c400070b004020b10191104402000079000b41e0201944103400703801d40c0d8801a00390440d50400b00125025101c82010100f40407054000b485400c02501c600d0800b000100b2806a041c82548191042421560f50004003090b103a80208842c403641d541c1e84080354025 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 10739017 1250 10737767 10737787
    0x405010902090a0c1b020901090510030f03080f070201140103030815190e10030c062f0d0f020703050c1201060305100b0406061103090415210507080105010303080a020d0204050402 79
    0x601e41c80e800f080c00110a40d96252400050503402841176030003c0c0604496400e200081000b0036000c1c2c10701d64240940c40001000a04403000c05240c18013070346035803443d407810340c0944c1e880c105c00800309001c42e450400203006501041c0d10035810740e40c05140100c0c03265a01c02c0c0389054201013600d120b0b4052200900c5200891031386a0050980c5c180d4035004000f600e40120901800d165400020010000040103012841c89000c113244000308145605618011603030209a04600054400681ea00a414201807060700100140c6902010b8030050410624580702d02e5102c4008441852046202c40d8004040f242d09401035800b45402400340d503070810350700612070000c08038034030700900585c2040c01c005001d80c0550b07094810802c50401451038400c01c102000000d2030049848005286100008281c201304000c1d2200084c01c168020b51200b40d0340e0034400e10f4000c0c190b0000030b150b07040c0801440040e901540c41900100902009622070a4a001c6031020340510b410958001d84089504c0400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 10740267 1250 10739017 10739021
    0x10050703020f07060b130209030a110105090d06090308060a0617041406090610080303040c030201050c100e030405010201050a02090d0807030e10030204150206010803030c1b15010e090a0c050105030405010902090a 93
    0x15108507000d09020071103800c008242c8c026405e50607070603000754204c600441d15035131001d82407a0052402a28000b640340014865200a260540b4103d50382d4890310101500a09540d401c050200c1c2d501c10800d14180004119580d044080d5044080317120105003080f04840c80b2013002c00007a0256651840c140781c0d555070b602400c4035070710010642d102d80015819008400c5038050b80d089018407850a00f19001500c00d41c0c070801d000d114030b1007440c2c02900c680e40c880c8074520703101d142100607643d11072602c4002801d503880078000b6102d2500c100040c103c659a05c4018000d029401902240c60300d5042c201038803032154248003150030100410703c118466a040e03004200ba1240710420121031111101c00f00e07a01e0740240246009a84104003040e07000d015603002c1c0005440c25054507070621114034405081c045200161841002000b0052120f00c00061001341d10105c1e02d00200b059520701c1d1140071844205100e031905100c00000407070140b01c001e40140055503000340201d00c55080003484140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 10741517 1250 10740267 10740281
    0x13080405030d021c0c0203030f0f0d0603030905040c09080606010c02060c010e010203040606140108010b16020a080d0201060501020d0c0201031a030d0906020105011a0403080307030212090d02010507050c10050703020f0706 97
    0x80c9104052040400c114001c01c4100e1741c07a60040e000310308001c0078520400300d5611040b125a1484010700014003481d405000b14405584260349001c07181d481d2905200c00d40d04240342d41404e1161b0700400380400240024090360219007440e0a01200d481800071828610a03c2c0c5400b62a50070800d8560a40e03405400544c062445240104030013503503140b02506043c0c0000b030a50020301c215004200306281e2034040d0032203026962020030307a26450780c001100403005600c50600d1b90088451030809503020320030b0100920007800940f4404d501c0c1840140341e00349400009050665811800e4199000d4100307038080010080c0440705c058440c0d10b00030300074540314401c560044d8202000480c08800e00c0c3e084404600c01041500d00341811950303190078580004100204040d801d1001030004000300d00d61502071528800548000031940100038250384d40100b40d1014014108114071000e0707000039401d092030840800000300d940b00e840b4120064418803d00503411807011481400f03010142e84003036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 10742767 1250 10741517 10741543
    0x803061f08041205070305030a0506040605040c1d1005030103060c0203190c0c080705030705060d0e03130f09020f1c09050d0201060801050a0603020d020d0303140109020304060507031413080405030d02 88
    0x1059a0f807038120101d40501c60000000d002400070320119103401810740065401c80002000410455120b42c040780440d00001001c1000508883e18a065050400c8074403003400416504007060000c00704002d00030384018400100b98590f07980039948154424400d407807403c0e01c0030032801000200d65400400d1000e0b100c40644055140c0940090307004c400054143c1112710107405000c0c000d190008004d82c80e0001950031f4401030b140c0941619800d0144000d14000c8482290031800328149444c84c5000000b03900a020110300c1000440310016191007501c906154110300c904140c10520362050181080aa0040080c440c42840003000c0d85c06400100c1a141074900030403c66660803412025101c09110294118000c82048801f42c1409552900828003d08011a003021302c09141d80c09603000364000142c55602006200400505001c1c03c1c0d080b40380c6d454144940d5421600290004201501800c4e400824021003420010a8400d580c0140f4009041c0c4006c2c0c2540320300030f0b40320b0540848007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 10744017 1250 10742767 10742783
    0x204050d020603041103030d0204030227070c050307080a1112030408030103020d15050a020910020a080a0305071704050705010908060f06090a0908030a0506090c210a06150c05070902070f0803061f0804 88
    0x224503710030450720380c0c14035800f10000090700c8105084e02c071050001001d56840c04200b00030008904020010b00c01c5074950356409800d00d950001c006d092080003118810510010414040441c000c0b40030b6034156130f0112600c0c1b001c500e40f413428071020402000500d074413a04003010820781c05811350103003414000940715220140c07000c0100701e0305c076009104000c000d2035041c8a61030340c4500c01d60007107030300c04c50324107201c108010b94010014100404940403540c80d80001d40500080d45e0100110005000140041090382400000b4555409005050354010010100042c80c400641e4200050540c0c00450481c0c0e81d050481034040540404c0f5516070041c003206003c10f0b070024040d805c4a070180d11004150403128002c00740440c12460180800403120780717900d800f040c0e94401d07641d400c1e8040d9054a42c0c1050744c2c010700e4090300b002050b612640860348103002c04004100041b030500f8010b6403000e0000d80d00d50742c4800240031001210400b00300c00c2545085082859000302c403580c0a2401030410f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 10745267 1250 10744017 10744039
    0x210020d03150305070b09040b0306010807091401080d11071a0c0106170a0b060121020711062a031e04030b010504050403050904091103010c0e0a05040204050d020603041103030d02040302 82
    0x4603202c18503042c0700007031141e80300150400c07800c034036200a0603c030400204081525150175002a123080820b80103c1040c0d0084d034001c0144809e00e1080c090702001c852950340066241c20310058481c528025140180601d542aa110400d41444240041c04008030302d1652905038400d19607480d080140c50904c1d0f9840c02d900855400800c80e00188007042500007485e0581c00c503903030207480c0c14020308294103020340203074a040b0380c03038134180c10a5a08402020068440c440d0742031507540b45021401c428000c6804112003000c050402440c072a01405010941d84207400b40c050f01031075442a044c404245031903030b5001003038111140000b402168024241481079903218000c01c41100d03002d98008022800400c032403001030416070087c14005002e03e480c5840100c4600c04242510910706084000a044400c0303004039162884140000d00800e40d0210b04013800c00020824507842c0c40d4000e40703d0140403001030200050034400c3d070031607100a03080c0d03900e51842078000f170041d400a0201f28450072520742 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 10746517 1250 10745267 10745291
    0xf03010f0e070303180b04030321060311040f050403050d022a01061719020405090102070b071e0912031b1707060c05030405060403050f16050610060906021b010c0210020d03 76
    0x501c1e4400c0c1c6981b80d4601c1e24147c0346a50a45c8e200481d210314908030648403481d9285a00e8900c41e8000850144a8226a030002c0c0b00800c41107a0091000304001440c1600b0b00002c81d51180503100c2090000f003006075155260540b440c3c1126110b02d449426240000c01c00d1030145041d005903003200c1c462514180d01c840c00448d426160300c050000d41100030038402d000d002602d026040700707800200103000103180003559160302003a44011664038011645991520f200d4107030008030050240b07018503000f81040d0520013840a1024a5080a0100040201b00c4031000080030724860045a00201d103054030071240c0201c4442d070304035800079104a450000d19a0280340583d00300c900c1198454058030302503696580c140c0b084d401003001c000ea500300c01d01403510480d1000f40100c200c00d0041c001000503203001035000c00802010b07000881040440d50b004c029050300010314030210760300300f040b0480e01400c1800403500104584c0d00a90b00c0802a2040b281254000c560041161313110342c3c06004807100c2c3d10b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 10747767 1250 10746517 10746557
    0x3120108060c071704230f0102030a14090f060403050601090c03050403021e01060f0311030d0201020f0a0e180403080601030608070f050402030a090203030301030503030106021005010302010c020f03010f0e070303 93
    0x80d402ca1076100100f2003100000c041d00c9070183da04a001c00c3d014141500d41340601c2c051403e600401c4102d40c2c0038180040e0f00c0c5022025412081004d1006601d041c941e40b100815000707244100901050703000c10260969543c10025054402000d00417689550383c030304015603107100038400c1c4d609640c40c1601d0029502c0c400d0140c3c91240790907070014a14981c0382410750351030402608010110755a10200400d8030301144186e1001980200b40311964100c02400309414050303401401020740e03104000c0060140700e00d00584040ca43c40d41400c0380c5000d40c81020481740f139440300414184404000c104010150003000c031034000c101c00ea8080001c1c41c4c0303030800d055980d41c2a000d00c02280c10701c0401000649003076001964050302c40341021503404002da0200749150003c2e001210503420210050062310b504000c1d0608100804a06105075499900080c10780205400007034003440402100000079102500422820441c818040003040e07401107c580c2c8800c1c25000450018200203d2925044000c3d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 10749017 1250 10747767 10747771
    0x5010f030b01060c0302010e01020a020a020102070b0901080402060a11030304030801090b0d0c17030706060b091302032206092a050301021201061107090213030b0a020703020d08090705030f0312010806 88
    0x24180c10543d08012041e1001e14a80208408664131200c1e5024440c20078000307040030103410740041046a007a4400642042c180b81c1101e10300b20010302c01c0003908c1e85d0201c40d20750803540548a0070380d1601d031a90100d9030980b00f0034014a0034400001417004040d40046414125801041c0030016848000108070350300c10024000b0305400b9400302e0902140342c082115100c00340046c81280d142c025165240d100751a81580a070250101c0801c00324544c0c00c2c4000604000e01074000114910301d44240c404442c0700c4139101302c1400c0b00c1d21a40000c200200ca500003038240c1e4004000c1103c82400c100e2410902c42c008d003500b0f0740030141503070000d0641014000d480c0d02804aa50240d05a03003008400c03984050403101c0c1030014402c52100146503003e0b440104800381407000c10103019402c40c00d0000c0c09140203400146443e104124180100383c3c04071fa040c104141718604050240c540c001003a2800c5c440390405e6925008000400b04688000002025203450f0b042c4018020303aa10260b21344c071980c007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 10750267 1250 10749017 10749023
    0xc0f05030c0f1c021503070e0d080406030506060403061b0e03010903020a060510030f080405030c01090e070807032c1006060215060301020f0a020f0c0405150103090501090b070f0305010f03 83
    0x40b40d140034609250403100c0300398080300404016119001600003035180c0010543c02e0012640000c14840e5140c2e0220040040713000503691560300c01840d941e1786c189442540720701400c01d0b683d500451b016654880440d0002c41d04404c080c89881c07068000d0065140c0303c042944081811b00041c00e00505040c054103801c1901a00a018450f40544860002e44402003010788882e0011f1808000202d0726040d0790006070041c10f00d0341e111801e1605061a0902103c001e90600000c0242001503203075800440c1e074011040d240501181d203d150094001d4850301c0784d808100070034247d854a01c18280c90350811188200c0c401c0314030100f401440307201290b83c14014031006810602c800319500981c0c2d140c0c590880030150005180c9031885803040d125800c0905140d006802807441c144203028200441c60400398122410400c501789806034085050402001750b05041e20b0783c4002c2c0501c002913102050f140e4101541200c140b8002600070403800521003070401003450500042101010001c180701601e034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 10751517 1250 10750267 10750279
    0x10f0905040902120d02070f080c0a03080a02010609020f07020312040506041a0903060103140c1e10050408010606080402120102040303020a02011101020c1c0207060203030609011406070b01030c0f05030c 89
    0x104150a101c054501c0c01000d0341c1210321586400c0c8514000c20031905103c280d0313400380a003941000e10310702407201c039540301000300e6100400c4203019a81e15041c0508895200c0704440d035600715840140c0c09400c01c1d0b4880920244045130040015125500914202c0e00c22400c0c0c80c064030000500b040c2a01850040b150040340a00081c0300121010b050044402c0c0b0300c140031801c0105003400a841d04500f40c10450f10002c80c0300030405c402c00c00300500c0301c505a04842d4030461804001d00002c038201c0e8442450f1041d140b0002c4002000e0041c01164090082200240190380d22490090a1584c3c00c0d1402c03400341d01d11881e05d00c0340c044103100350f505407a0f040d40a42220035481d001100e82c10010364090205550800160404550800a410300c182540345e14200d0500507a902a04000b03040d070202095400800822038196912001241542c0c1080c031003911442041300801c00a00424000070b00c8944120b0010080c001115803038002c0742e002c520701800303da03299024540c456142c3c0d0407250300b00e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 10752767 1250 10751517 10751519
    0x9121107090e030f071e05010c0f17040308060d140c03060702030f19050c030705060115030207030905091f06050301031203020a0c0b06060f070f02040e070e0103080a170109020a020c010f09 83
    0x10030260003005c07224080c41c0071010366050078220000084c0b02110844080c0e544401005402d5081004003581a2240c01e1600c801c060041013100d0341c1400a200508002200700000c40703690f02e8074058049550400d0313101000da040d200d030703d0b5603c092450583e4440d10514000486441c03000040b64414000848000d051000c1c00a04450781c4491646000038040306026170300320520100083c00329603004000601255261001207910280c0b00d03441001050f00401c0804040390300700b0b00c07076070480300705641c140265640e50200c10a005107a964455004003004400641d1a40c80320246050b0b80c02a0a51070701d003080000294202d12843c800703000400c0f4520420004212018080d5510040280c0002e14180ca05160741c641035020090803180607515400c61400d40c101841440100066203004080300c80c00c0c11544030000d01c05220080802900142000450380710b08410700082024009907601c81d40c440d00d021019410004400c0300511403401e5411066219400ca21000710311500e49551803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 10754017 1250 10752767 10752787
    0x307090507031b02030901030b09150f0d020d03090608060303130b0714070801060315050603070b1303020405040308072615010c050a0b0103210206060904020409121107090e03 77
    0x203044000d0030181816038924006400c108607942c403501c44101503019503a100d51000016048848030904d19004140ca08200000110781c00720381c1005581c211980101c021210300020f254650100c0000d422448a500410801d500300c2c601c402628683d4881400c6655a8824940c0d00c0c003c11244207038024440b5010854014100b00a1018900a8518001000d0729030521441c08959030b010010f180c0d5100020000d20004032040715540c0a000020300150410701b001a41d07941890140d2001d0140009841e40010740049204004560160040c062494030381000b03483e4070b10844502004c9414622410601e42669840d01c1d96245081e4004201d912190340e42d220b01c4d040c044842d0705000b480144980419030401004032001e00c100d529030070b00d604500e0a030b030403180454083e11400610030b000140c00c0d5008120b4a41c402019150104160703110300004000c0c0c00140800f402d4003440d903400c40c0c01305500c91002196130340b46504031015a99501c0803101100d01e03800354403030190024043c410790 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 10755267 1250 10754017 10754021
    0x10603050c1902150f0106090609080303011a0408010e0c01080606090a03120306080102030109020406090e1308031302130e0705031207120201020f04060905010f08061c0302030c030a08010302041802030709 90
    0x1c200b03510320444802d601032039151507007100181c3c0d403040b001c0d241c00f0040000645c0201e100b0060011882d0180360746d172400210581e280018024120040300603403801c0d01c404402c1081c0c1d401811150000d01101e481e5100058540c0d044182050004034607200050322410400120750340d54030090312024046240d038951803030880b80d52103800101512102c0000d0034800c2400a0750103002400700042c1d85903d05040640301140c2c5601c04e8410050030820806103201079074000714000d4100c404103030340359900302810201c00b06081f4020b5100704418407100147c400b0382e010041156240c0200c88046403510101135075002c2c56844820a4442082841e000039540c000e0802d40580300d0002609165002030b202003030fa001900a4000151640e000300025039200342003070b02010150400112a08120000c980c1c80b200030071042380d00d010f161075103200f0188200700f01d600e0710719903100b6252550320721000241804020310060384103608150041d14141d150441920b00207600900914601d441c11042c100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 10756517 1250 10755267 10755307
    0x801140d0312140124080c16060204090c032403110307030b010303050d05010b090d08090a050402030703090c0503070b090d030207080a0320120a0e0f0409110108010603050c 76
    0xc100000118440305160003800b0f6605616080f840c6401d96605014056001100303203040d50715a008a000a001416008444150002c82c01c108a40d561207203e11030200100b0a000c00409040c4006400074010b803459100001c1b00701541d4081c84404081c4075420201c0401150004404d8800c08040002610b071300741400b0003c00c080c060780e1840390749855201540070f0980c02a404507100107103804100c110b6220f800d000d402302c000c03010b007020404c0b0040f035582e204081000f0a202070000b110310256881c010408014140100250755074903105000402910080d1400c85115400a202180502e408504402902c1c12040b00b941852100010029110f035007440581c254040d4007000b28030000188080000d50f4002d8440c00c850940308242202443c0611507201696000000d400d0130b1068031038102d03000f0031010702d070210302070411100051006003688081a40540b82c506c9840070840c0341010200314038002d03242e40d12542e9907030806406440e400c860481041d00100a20401240e6600c81e4036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 10757767 1250 10756517 10756523
    0x6090f0c01120b06030703050106020f06040f020108040602071211010b03071409060a030804091a010206040b010603050702100608010e0c030a0b010b030a020403080c100e12030411031c0c120801140d 87
    0x3090304081c02003c01e513203600580c0c0560000740c41e040140030303450b0100b0175603400a241c0c80007411946000c0e02d0b8109400d075a10f200904200088002c50103118140c3c05031b42071181c01146522400c454058007509081c001d00c038a90907542080140c0c803061a0118001e4100c81c00055401230300d688031000c000d802c0300000c0140746d000c010410040301040c0f0001c00b81c00507207a111300000340c500040c0ea840300980c03c401c0c08141190700074420000041c5207c0315513030446095007404525511400760690401c2502d940484440c1e1502e140000e0030f0005400c034403524190002640e6501003040145a160241c01c0c00c040c085080310700c010026519450015030707100307482000c01070800b6142e94904240f03030b1150911464641c0102145509894a40705801c0b0751706402004056112280c1030903101804000c001401c400c1d43c0124062240d241405502001a4003003405000c2141c4503601606090b4124800d580107062030700900417003406080303964161a407035a507803501004000f0411480c070401210032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 10759017 1250 10757767 10757771
    0x403050604050610050607030e0d0c1a1201060807081504020702090408070b0604060503100504060905060405071401020106050a030609030e0901090e06090105060609010f0c0515010806090f0c0112 86
    0x128a080c01114051440b9402400d0b0310f08112412414080e000d400a42c41994100041030000307402c0748480010311410707a035400d883c50850620130b035612181c1d0711494a0185200210041618803001052081103041511501b0307602da66007140c46003021110003010a4030940800c030310303459110a10307824200c010405498104213601198030840107450455032800c0101d060801c1210042c080340c2e101105075010400e040c913001c0060340d140d14940360150034540d5000441e05000b40c58114002c5c25400104036107541c00c2070f00c0c02c0c5075200302c9445510780010400c038074031003550310600865044a000400304180301f0308584547c001480404000c030b0500c62001942c80d4a034503000340660007001016400244a00c00341042403c028004005581a0740741c5800c0242e250f80b20801d0f5109500c007813801c4513010680c110103541c000000c0c030002d0103522408210680c00d0b80001d00e803a040c1ca4080c03056485503180c04840c182d50b104124286070454002e0a4400b49551048104607505176100b400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 10760267 1250 10759017 10759019
    0x190204090f1a0108060310020702030a0503030c0c0d030506150a0203130906050406121709120307110a060e011707050d060801060504060b1309110702041503030e060403051203060102010204 83
    0x1900084842482400a04589482d05400901c81220510011000c20300784401c09242c0350b0002901c42090342002c19140307074041007030010b64404100206100b0f6008046070341d2030500520040154021206050081c4501440044458801e016040c012000504031524032072915518241c6500441c3e0b00e43c0c21403105110004441d41401c917844000c10112100140103402d2000380b10a490f066040b50000e20550701d40000020420f1655001014071200072036110111000010309030b01240b9007220844c40042484030511009034549203c0b89012075002c8070755552103000303440703080e84051032501044d0f0081c04e0004070511224001d0b4403420300c0c50310350b10384011204a002207900e03981210301260b56412082c0841e09062103004050550102042e003400d400204d008181c42d803030b00503481d10325120010f40d0902e00c982026200030581c0100188603d504041c512910404981f0040d00095000241e5003294103181040b101502e8000024180c2d4003480c2003a04007661010344101d045660801c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 10761517 1250 10760267 10760279
    0xd0809041a090a0b030a02060a030b06040303030b1c03120e0c0a060c060605030c060a0f030204050607110f04020f040324050c120a02090105030105190f0b0a020f0d08190204 76
    0x4500001140740740400c0e8403079014401031002505000f8000110140703031004403821503800203075481c1c00583c101e82da035a4401c42c0700c81c103d014004070070206070070020205000c000c05030075802c0041c58200c2039072201c441194070105000c45200c4003201070081814000020704503001e80d00450081c418840c100d80d220700b6041c001c512800f0741035100d13000242e9940000000c02481e4000c80c00101003c40013440d20460703900001d4060300c9031b52178030000d00494010100e0b07054040d0b0141c800801c4000e040c10740707a040c141480401c000304041d001d8859010310680d0541031070640f00b80c0b003982190308006410242540d41d003049500c1003032081d010780051412450480346003801640d20890300c0003006900c4d00046052484c00940181c814041d45005000844999038408182c80c1100d80c2198402150394001c46a0544084c070364000c801c5840c0f243c403000c224050110300500301c02c0c08a60841711480f15407841c01e51a6013800e00b60800080c0004046200802c5208005507101c1d100100107292a42e100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 10762767 1250 10761517 10761521
    0x13020312090a05120d0503040c0905010b09040f0c05090d02010c0b1f0b03040503030a0f0b120303070e04050603030d090201021002130501090905071e021603060609050618060d080904 80
    0x4010100080d40051100024241107000000811056a41500928464503026101d480d551040003c101000c00020148103030001002d004010141081025584542403a4182c0d446486102d01a038185680c0d800081d08902c03640710040c1d4207644107814201c0010802c03c41068006040c0e040200c0641c0e840c005c55500705001c2d0250808103550791110200c42c040c0c84400703402d54011060380405004010200342c0200440303522480d4080000380710060000904001c2c080f0b042800d400040780240f14500500000086024504503115001e140b8807900400064510071155150513402c140309070316244601c2d0300302c05407140c8140162030401c0b6030701c07102c0300482c5c00081c1b001850060442d4204030950f00003402c0009803508241c140038074600003a01500c600340030144a051400300d810740d4030f00340e4402c2c40703210540c200c00369150304c2e000d9076424600e016203070034066680c00c5031034000414030a01d000e1040600800d038010941100d42e842d601000500b4181c10030980d10f80a0030450280c241e9924 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 10764017 1250 10762767 10762783
    0xb03070302210706090b0304060b0114031f0906050307150504051302070204050711060708041103030c060609070c02090408090a03020d060203041101030608070513020c01051602120301030201120203130203 90
    0x41a601e981d80c5000e00019450400107034081010f1150000c02441116031340c0003148c0d03000d50441c4002c1221002c1000403500e41845c0000100c00c5a0003209104030070701c0420300010300552038005c494140c0c0c0c030341c1958421507090b0f02c03c0300d60680c0541c1c81040035524806031000da4022070b0420700c1c245961030020034000203504c040e00008541c0000c5a408618040c42102d07004041450002803030b070450b1100b103584100141031402803121500018081088583c8a0060280d01406494a4903440500c0c01d555620540c0c07035910452038500080d1801703200f0444160500d80040074101e140c0c4980d218210990301035031425811600d008004809030f1a040c001d00800e6100c0c650040e500e05e4242449403209002c609507904050401c0d004110f070b00b0001410070241c56048941404082d105500c1800a00c0fa0206003016542000c2c10858440003c109000782034a0700d400f0786100d11405842c04660f8402400001d010541201102c1f102d00e61590203160b002140620300c0801c2c4240390000791504100d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 10765267 1250 10764017 10764049
    0x509090703060c05090a0b0306040603021005070501110702030a03050307020304050a0303050a03150e1501030b090a05040b0f0705030c07020d0f1b0504140a05042901060f021606030b03070302 84
    0x260400c00421419203d1405011054030b40300d8240810030001070600113240c0b0400c0050308011003c6442965643d1041d401075a00074030b620b50b4496400703806000760700541815039141d4038041b004400204101c0481c6c1a0603401006000f0b0f15105640c181c0f000e0700f010304208214402440041800e4644084100240d8026112203403100c2844d14000e0503501030704032041d401e07030300d030802000034054089405810498410a1801032084030004038010806040c2160f0700c01498030034802440043d90000f80110b0003166207980c40d580e04201c545446005449090010300100000340c04a00c2a80140c100c40e84020a805940c0c0301030307110400019044601075840c810a1032441e0341c00303000f603d42d42c002400c0070b65050000800000c4191200c450041000c0390705521140000c0801211201124242d0400b120b00c4c480d00c1d148081242400d00c09000c0c50001c20003c03000039940a000241801805c00b0b507110b400c4581d800d00760110050041c80811a800d80306804011006a44007445250503500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 10766517 1250 10765267 10765273
    0x313080703031527050a020706020301030f021206070c0b070c0803040605060405060102160302040b06090901090606080a0504050a0f0510020f090f0901030c0611150106030e0106050103110d0f06050909 88
    0x102103041144085082e442100c1d81050000d140c0f50701c1c09045501414034040310380009030b640c1c80150b040041e119140d2300824441c400000803040100b4941c040103c180265155006180c1c107a41060b0b582d4001d03110403010a81c095488000035100b01c8913154008060720b00185004451364030f0300201e400c01d0b98102c0304280c0b60401c1110608091040d1540150244001d00302007228514841c076822403408041e00507a01ea0500c5021601e890048819191010340209525a03450400c5e10007000103002d8003000503040008074000d000d583c001c26008581000142201210b95030304c5261142e10340307030f00b21100c0c000d0f91040c5080810307501c040c0070501c5d4040c1c41656a10015003c002205031010a558400c2d50003400500100744448040410341c6e04a080c01c00fa00440701002a15180c519040b850544040320000704626506411004038220000002d018440e1a0300c0103405440c0100707a0001010020301000450380300a8000508842030f4900002c1d001da00c40001c6641e4041c04ca4241160358 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 10767767 1250 10766517 10766531
    0x9090702010c02060903090a03151104030f060f0b0a060807110f070509090d080705070c0305060103061418060703090206070b0f100e060a170c03010c08160912020402031308070303 79
    0x250113006056010700103101441c5801d00c1e92000421016581c04080c02584070b6028644952001d980903c00d00e1990212460321186c0d41d160016010190a1003110340b10b041200207140f91500c2d029021a2002c001e0914211b1400c00e082110401001880d00040200a4803a10740d605000c2c4944a429640f071005000220300b00020310120034000750001c00d07241c0c05a07010f40034940d401014140c20460514003076941c1c02d05400c21002c82c0e905900050194000d4200000c200a01d607802807c0d50405042c2d8607585641d0700d04052280d10f10f400812056070042c100107070075580300b0303445000d86d144000c2c8a02e08041107904e40122102c030171601208450480e8042c081a8a55240400d008040c1c810080700c00e1700c0c104020515180301445440d9591066542e144005682409047d080c8000600200401001010b00030301e03040303055403418101d00510202c4c012042c411b0b40e408099481d54040d4032440c0d55aa400c1c40000c0d030000701180c1494680410b1078002802e405d00501d851402941d01080c0b41c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 10769017 1250 10767767 10767791
    0x608030c010e060f010312021606030c09290a170a020a0e06040807030f080c0d0c0327030f0203010b030708030a1704030e0103200f040305010f110712050909070201 72
    0x551802c8141d425a40c4550100305440e128501c1e124150ba51008140d0384600103034134142e00c0c080ca00f0811001c5400c00300400300d00c15074580e00c039170104102c1c2e84d19014070503030300c40200d8403a000f021281500022140780307032207410000400500c03212250389003003540d4000190000b418403d0076651014096000210503d142d640b0540c0034000003801c4540c5464185007240007a541c9809200081c0030080031548801802100026182c0403521041540c10520786a40010206a82c0e030004401044940c80c0803034135400700b03078818450f0403825034580c10301c2415516032002000c0b843c4800c99040d0b4907003503c8a070503101407196400400b0b400000703548404040c5c07c040d0081504113100c40c2000c2c0c0903070410000c2680034030030a40390300c1c0a0078005241d60460440030218854010010340884002070081700307d8640703500400482e80102d00130020580f190180a0907200b0080403e144844240720aa0205421011404000105080881c980881807000c00e8100e80200c2d4803801603559004181e0403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 10770267 1250 10769017 10769021
    0xf010605040522140901150603050108071a041d01030b15010e04020702030a0204060f050a09062409080105070503010312020607021e0c030303133003020306130608030c01 75
    0x14010509200303080600704404203c002450a50b01d5240460258400050a00c10362010301d00d001041811400c4d880c2a50303890b4040c2c000b1a0480020b40d0548200140061082c86520b05a0f04c1c08170103013054034506080000d402e4043d0500c3e1207101d00070000050051100b81c1c401d06502c1c6410441d1030113614505040d000c155005210020790100c3d5035038940705a078800541d141040003154010380340e513450700100c1d2508081c05030007908180b401c0c4001c11055201666182100c40803902c402100e500c61252505451562107140c00600d80c0c08001803000c2031440c080c082c4403440e460304004480d80d5200d11030a44909442c4000810350000060051002140d01611f80801c1ca000904a030f04203e05c00035511404240885120400d422210150360700601035240b19500040480717481c0c1c105030088080511000700c0854074414206100c180c5009401c452201950310020017000003040b4000580103944001c104e1988141e11013103610079040c2d035202c1d0b2030181a64400460300c450b032052007282 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 10771517 1250 10770267 10770269
    0xf060f0f0201090302070306020703050c01050403030f0c030204050d081e040b03010317070b01050f03070317180102060c040302060d0609021b12070206031807080607020c01090b09102a0501050f01 86
    0x411a4141032500c0f021940002c0c60030103ea0388210016940c0309542400c8a040c011600790100e15420101484103159140d00108d200d9000307030204100110381088141c00f203114920a49801c61800d00c00c03200410355490107050401c62703100c038880f903e2000e400d4802d03040d403190700300c50341014000c00184244010b018180c070100300314040b0a447c00c00140c803154260401407040500c602001071101c0c201d514280094001144e00c08a0504142030107208584943c001745485212119040402c00b80d0f50310000d400c03406589520308180c030342401d507020f100c2e5076880550103241c0d00780c6450001514070702510080580b2503036800e00907001060401d205042c42e0090313200c0d0711002d90500925000d07a941c601107a4105498260111319400c42a400508241c101d81c03207001c440c0108010884020303004501265441403d03a01c400005448560341c10b40d50185030001604a41e03902c5074031614a014030030a52412745501c610004481c0e83d4252801c107506401002ca4090351524288403d2004507280a8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 10772767 1250 10771517 10771547
    0x4050709020f120403140c0a02090c040b0f0a0c140604030206150a0b09030a08040303120b010801120303020a0908030406031505031c1d04090803071704080301140a0f060f 75
    0x140c82c000310921468900e01a40503811911040d103000f02d01050b0090381c0c40050740c071801d14174503110070360002c500d605e6051108090340100308a10000b0500c00e039200403203066032030301c2c0d520760f0070251034220701003040e04111042000e00c41c00f00113100120f410182d0705d2302c1c0e0041c03100041c906840c4c14a0b001b41401c90260200310003101100106030550b45610744202070b02e01c01c05c0707060307200c1e04c1f00c0001a180980c1100003500f8018005004414164800d1842240d03e420030410b01108002da401101c0052003481030903040030441d1100303c002486a0000d1200c200c007031038907810150f1100c001c1030031680541c1c041c502103680c80b09000b03003140786400d0800062108030064441d4039803119450550607074280c040001c22104040440c0311520400c0344048082d4043c100300682c1d078a0746003410441d0310549004010445500d141c00b820314503010450710507503114084a041d6443e2100000900440e58689a03010b9072000d8042201d4007031003003040c0203040d44d82e91040240e034452409411442c4040601d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 10774017 1250 10772767 10772771
    0x408071106030c04080f0c0a0b07030c060e0a02030d09030308060f0402070b0106120605010c050d08180304080307020406050d031d04060513051b070f03050a0c05010f09050705120c0f010203120403030504050709 92
    0x462800c1c2d45108c00001115621000b80e0f0b61101c2c140340494030710162800084c0001d07d004525002c01d03900003103a0001901c03c0e0100da50913601464160703000c42c00c0d4400200050b100800040c8242032402100e500100301410140c04c058142e41c480c40009000d80060000984c5601c00c0b400d010403074003501c401003e081c2000c0910340e1482d1039003516011107803068010700401c0004502e0011001c004207100c0350265080e070784c0725511016202e0300d80d44050402e0384102d081c40c02c0404d0618003c54842041c03a07054071691464881a10b5a40800b55220041c0790301c10340d6610002210785584008032000c40c20074600180d14542100410720715150800300c0840d40070140203401c006111149040801c41c0c1508165440d02e82c881c0c000c4416180300200100503508180e03012035900d0701d680049480a00c00c07019120700a0b201e0090105680a50100301c20300d500c0051146e956040100c00c00141d442c0610540f4500850381c14051410701c0151411000240d03280200410b00009212500c0540581f07038003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 10775267 1250 10774017 10774033
    0x210204030f0f0507030c0e0105010207150206070c0809100509030d09030209181e0102030f0a020f0d0f02040b03040c0303021504030503012105010609020d050a0204030206030408071106030c04080f 86
    0x150340e01464200d90080c102d0004030801e000703025040041c94001c42c0d1200c0400d1a2907101d0380c800180300001c1c841d55015203d40b92001c5050803080300990150413041d4020701c455030f6001c4c0c3c2180c1407013040e5400c0e21006020001101191501c2c801da008015268440582d2241544203040c50140d0b080140420044050400d02c01a5605070b01d09030412041b040f15001c6070106500745041030714203100c40e00d040d990412888c00916064019500c2800921800a00303940c4003070308481640315102c1001d01c82c1404110a401c000c4007507000194265050030f0040c05c180d29803280d00c40ca0703841654192400b00d01c00c00d042041560401500c010106509220708440c10321380c1c2d02800e1800306000310485000100b59520648000340102c281d07440c0c100f0001d020071652200032400035440500c10241282c1010001103d00c0824001c540440c1d50207000740e45140d445032120f46a580200c0002c03200740d00580022202c6d640e07807501650203441042030706940c0720300d0100201c0c03604140100400003500300b041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 10776517 1250 10775267 10775273
    0x2040302031e0f03030403110c0a050a120309050303071b060e0d120215070806010201060e0f0403031d03040303080106080612070302010f1101050405010e070503061005060a0e090721020403 83
    0x190101248a0b009a0710208000340314409043c00803900c4011107900c0080104000d143c0d01c10341c41010001e807141903c882c1d030145014480301c128180a1740d9004190300320304001c0740d65203401e201c25003400380c6000d07440540c0700c60000c0c2c11039200e900b00751035980c0d11855002c50755503000002d03001851a070403d0301000c050040801c0d07505a4080c005001c42902d00c203041c44803030003840708500607110080d00b90340c00e150450016103045419602c1c540198601200441c8071620b9583c10b6000d00d0103c43d8041c40c0b9603c542d0308501a0103400d1085c00b100e0350700e410b500001c610400c0900040c43c031913201c402039507051410003005414010803840c0f01e0310100300511000b520120310441941d030286040007800b061031034251500345403100319141d0744d80380c20100002c1c400c045d44400c03100c2e0703941000d58440a40c1c4034201035031102c0079924201240402031080200749809802824410b909040c103800b250161000590180d03822201840459850710094803402c3d00c1e03a40020b540d40070707040e0844c20241503403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 10777767 1250 10776517 10776523
    0x30103051c080a0f02070b0703050a0c0c03050315010309050a030302070519020d020405061c0b0103050111090907030504030e040e0d0306051e0f0d020301020f0d0c030506100c020a0305010e01020a09090204030203 93
    0x41c0c8810203c2c3c0d83d03180d030300740c500100e50110740b5001d40191341c02115050407039005004080844902d6102442c04100d01c0c40b081c401c20340750010301e0301542c40c41d04540324182140700d036581d10926a0f05240e0744054800c000340c1c0a2003103001e40e9000c1d440050712920582070950902d030180342d041096020004501006a85200b48807000c03a40644000078541d40780008225511085034510030804d5040e10200304002100303900c3c6058905c100c0003404000d490340c500b52590301501d448940d2041c40b00d000510040d1180c1c5c40706038028040c4c0b40040c1301e00c6010012404486114810b00601d41120908503122038050081c00028801640c44c13803044e074407000a0b80150124208018419840d5124501e169a41c1c184000e00480c1c0041c02195106000b80d94031101d0341c030044010042d50705283d07200481900a102c1d01c1c1c4140005000003024cc004041d00321070020b0300c0c4c10120780c811502c90b00840420401d10808001b90181c000042e510384d004a00904a03000c5a0f0110202600410060006172004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 10779017 1250 10777767 10777771
    0xa050109060309050c03100c030b0a0f0b0304050a060c030b01080601020d080705090f0a0801020c0d03060b0403020112090f050606010908070b040905070903050303040501020301050117060d02090a06030215030103051c08 96
    0x10300d000181e0f20b070546046814010307001020fa070b251141d044c1c02d98180e612584103171100e04803524200402100102030019910262149501c415502002001100030450003982d100744100d09441c080c0c2440d40c3c54508485d241c1c0b0008001950b1490002c040d960000c0d030540d0031990900081000040d01e960060a09038018400401c1060101d52852030f6150f00703031212052407008144200310740e00d0f4031895000f504045c1c038100700d5118498401c075403580607126036020744620824803441c19041d600156007030100881010501a40c0368031440c046202d004000910b284144042c1c810703401c0080006109401903000b8106642082078104042c0c90544110760483e007041d08081615030307a00034140c4143c8904d41c005011400700004020030090198010740c140d4809072610300380c01490381d51181c03000c1000c07514240c000704040d02c0e20b005440c2032180306a114072644004191203890350301050f07103540703161003000303007248080014003c2144c14010038401e074036401d80300403440050307070070041c1034141c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 10780267 1250 10779017 10779029
    0x303061f02010905030c01020c010606050a020c090c0f12010305010f0b0a0e07090e070504091d0a03030914030406030f0b09040b040b0a06150c03270b0306040605030f0a0b01050a050109 81
    0x58480300d050841c001c0d04189409500b12040d81d498082807007402d4080c0d0b000d10000c14140d442d0200200d0000e000e001504c0c0054450f50040032400d01c840b090060401d006001c1e290500c0007417000071900c42542004144a0050861280c115459850f015094509084020500754140142c0350100d44403c0c5507002111807a40940c5520348030100203032654001501b0a54840391050100607126070004002e20464401e0f020802c00e0314417105496000e1941114090510381005075030901091007900452040f80c06220015034232800509620f1131944558800d0010a4952a240c50012110712859200e0102640c2e10000c034030301941c5040c450703100104002d1488500ca00420400c04540d03000c000070300f0f109180000100c800035806005424200300c1140003403800d12441101500d0b2001c410712841406042c00041406d04420303003101d1700300030b00d00360f04141d840c20001041d5a0402c081c407a00070710240501400c807098148010301e01c40503040a4050502240c00301b00f1039078800744010454407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 10781517 1250 10780267 10780309
    0x6011406070602090306130c0f060f0305090c030f150f040b0c070f08040603140612120906130b1b01020309030405010c0609062414030a0f0503070f080306040c02030306 74
    0x7145044802806a0000c8903014442c07082040102c559070200200707041d0181c0c02c40f0906a036520034011030f01d2224011030300050141104801170b41d00039008148c0010040701960084644a0040380c0f602040800d54803540d40903092040b0401d54001c9084e0f0440000c4045030460700d0162520704800a000d8145860260001004418412000c0c0000c130070a62154800d43d60380d503030b10f0b4010007401c2103140415060f005540850078070300c2d00703e02104c440e0300c00d100640560480c840d03042c02107030003036503401380c10110402c02412a41d0041d45040302414078036808903180c101450a62401d031202c1c1d0544100c1d60720400c180191400c0c00401d480484101346414403d618182c503101010700300d01480241418100f505138800c40303400c0b00c421041807050403115408569108081112080400719480d05600040c0e000800b0480c0c404c80801c01c07030b0246003100c1c51301c81903540d10303c01100046419101194040305000c0750f0310f0540100c4281c1c0d5410b1000310b00754103082000508515000410f151601 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 10782767 1250 10781517 10781527
    0x40506190210050a0209010806030a020918030702060408010e07080706050d0f02071a0103020108070f08010e100807060503060102010f0905030306010e13020a030209090601140307030c020709020c010e060906011406 94
    0x51080121007860b40100c101849203081290713000c00a9008a01d00e6404540000c00040c1c541c240001c6010446070010302c0348016803200044502c40080702c80c1046020b0108000c10000343e203412005000030400c10000089100c1c1d4081d6aa0510400742c00c455901c1d0020340f42000b10603888000d458410031040d00001d041200c1402c41c0c0c000303200d46d0f003004000a40c015034451030b00301f904420324103d038000c1c0ca1302591941e403401c3c1180e0b443d210803902000b15080b840140b100307012007030440747d0043c910813204031440d071522030003031401e0400c0d401a000101c0001c00c0101c1540d0a0084080601002000b8400348009a45a80d00e034040101920f0410180b0210400c2d50742e2025003181d036103d840a002c5540d200c2510004010354000711905000390b4400001c0b64a65104207110b020080401d00040c3c15a102c1c0f00080300030b0301c5250300c0301c01144030304000810070100610003031500442140c00056600c610131042c50030404000c0288034540c1100f0010002c81c00c0c0321819900c029070403901c2d40e50750 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 10784017 1250 10782767 10782817
    0x212090402070609080d0507050306030d0e03030705060f1012080306011206150302070303140603070501050f070c060c03120c050f0703140d0e06150102100b0409150203070f0203040506 81
    0xb4020114043e190a0030301c000c4505010408000307150140d94880184450354406400792400d102c01d03a016070701680141c081100a40c07040069900c0345400405581c42e010140d00e0310761400000380c030346070036440c0503200340010554090105401400040b8407891520215101c0e403056010080ca4103040c00320a035403030800100c0c19407024000e03100700440c090b120030742c203000100250400c81303003100031170f01d00000d0a041c1550b44140743d2140a000b4010060035080030011103558200201000003c0c009012400c0003038109801c8001520f841d9503010051070b818140181210424120300e9038841c40c043c0045e0394590b00204540c5402ea540800c2a958140ba28040300c001074400c3c514400d006000c1550304c00412035400008400001900b111410384542d582c544d00ea03a0501e4045d405a8803504d00d00624607030940004600700c50043c40000d50300304913141c0f12044d500d002c8540d01080d80c00402c1210507900000b160400403042d100440c01d080c00d10003c100e9600c6816698405020004402c40314 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 10785267 1250 10784017 10784021
    0x2040506062a0f010905070b0901170c0d0c08040c03120504090e160605040f05090a06080607080702010c0906090308071b030516050d021f021c050d0c02060702120904 73
    0x202c035110325802da00c656240c0c0242207800300c0c0c640c03100103010345822908030010500441c5420b50300200079104852070701d920003a42e64441403d07981031002040058900134030240f12248281c1d118013107582c2d41c40c40e01003402e08941204403060180000e40090001085002400c8000d8070343c03003030910410180f90308041c0c4e40745c0120b41c00104070505000c95043d525101282c40301c000e0900c0c5050300c9140351a10001d03109806540591010080e81c0c044c10040791400d5903005400090030440012200d0700e40b0001c0342048000c69818000c03441ca0b606204d45143e0911808150440c10701d003460380141401c1006105041e148806015910086005c50901c580285050351020917407060b103c1c0a562860129116062001c0c000003005841a0009823805d08843c666502a402040588180f402601d00c2c08030cc102e8100d0304c81144501c41c915018841110389800c0b1480580c0c5415032a4000780d406401610548900c100c1150030940601880035000075800c410308400d41c24064440441d4008200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 10786517 1250 10785267 10785277
    0x120c0a11040209030d2303090d0e01031404080703090803030702070504050406021306020601030309090204121b0f0605040e01080a080313051f0501060f03050103031407060b0402070501050612010c020a0204050606 93
    0x10341801003c441304000b03904008243c07008242c4001e60480382001d9286c03002a0f010859003200380742c20603050300340c129102d107030780c0001007005040004c1c0381983c1012420002070100d03422203112900140c2d020616030041d803d98000c1000f038000350301e0761504090080d1502458860302d8060741d01c0b10046030400c1806e40540c0c101205004480d141f080e40c59100a41d10032007840241d0204d40e0900010884444c0d9000700d070190f034102001d0407a00b00c02c5a0310081041031641d81c0c1245515640f0003c107500f1070346a5201c00501c00f83d030380c0945440c100304900c4004001a88402215404460401c000a445000745d076400041004203405d070303e00c1821b00c182050001402c42d0544880311502d106a41e10942c04503058500740e6452a8203249041015421510280005008a9604c401d0000c0310114140108200c43c81000003050814120010509031b0300070920841d4940d4581c0c08004050411081011904d41000000d00c41c0c9540e0890103510b0720045000a80995200d8000070350790740f82c0408440c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 10787767 1250 10786517 10786519
    0x20a060f110307030804031b050c0f06130906050f1221040306020309010203040303140f0f090312040c0503010e03130e0408040e04050c01030507051c0b010315030b0405120c0a11040209 81
    0xc3d640d0101860000d1103808100c0d0100d0100342e2103c400009442d8451049000c10740c400010400c07081d80f0410406c030030303410400030359100d41e040121252000404a8040090022000100341c003400c200800200002016406000c2d20314201d01c0000d540000540d90300c1102100c403e6800c2d810300d032a055a0500c960f80016082c28000024045800300542c0110311460003039404114031110041c0000094409554401c3c102c442070001c070b08000254a031150f041030031642200c0c581420000100b1031560120303070695042c6610f0008101c981428040c0c0b000500481d0095441d0104500d6206641920750040c0000381d440309001800f00205402250080c1550b51140e0020340342500d4480e0742e135a00c9031942400a400c040104410f2802041592000c60703d55822030f4a02c0ca0b40480f541c01481807514050400d501d50000c0342455004000035005140284c4070907060749403a007411480e0410f001d20b80e80030044101702906000c04041039100d200c2d548200c50000130201800003901a02400b02c00c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 10789017 1250 10787767 10787773
    0x8010635150d080d060b070213050601030f11040f06030510060e0d02040504110a1a09010509041103010305070e010605070f020603041112030d1b0912030912060c0219020a060f11 78
    0x4a0600128601a0101e80104c1c0d84c144690307030321404861070741c0c0550300e0025000599240e05145151050f00956444001803600040005001c1074490035600e04444443c11524005802d214480c0200e800c180600f40505081c4181e06003a010324802c8590f40c410181007000c107119600d00c5550701d4600c2c0c0074081c0c00400501007030070310f404e084400c45100941280b1441400c45c00107002e008001c000d03045007858403069070412003042c00544480c2d0120740c003107501ca662070810134140180a0040c60185015100512945d818010b44c0800d02030180c21101c00d00a09000c1e07140007030400000c2980103581560440d80f01d4484d40340c1009520506412158001e50310754003807880c40400005000110010300742440608400c0d081102c000a034841620b0000e68410814007400c0d40040b035a5802501c03a00d4005610395a888042c85002003401e0115240d03521000c6101f14540c3c1009103103408040000450702c508901e6000a40d5a000b40c400d1400784144600b0288031070303014020a410b50b61054050b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 10790267 1250 10789017 10789039
    0x7030207080a030f0c0e03070603020705070e0f060109080a050c010c060209040e010b010219020d080a0c0605070503060a080303100e0702030c0102040e1012151a03010c0801063515 79
    0x4041e02414110854220300da151040017425144036036030706040f090000d4080c1804a0800104802030340c003c41b0280d51070300c1034020010b04044003513001c502c0360010002c5054a4240200010204543c541c0907200c158031003c407150200d5008142c885c28a5070900b440078481c540c5140c520701a0044581c042e07805868485121107800f0103401014910b9001d071b00343c50420a891050a82902c0090340194104a8400250001950802c01007407450a2400c1c025041d501075a50703481a02c800b05d50b1240000c10200500210741850746400010700009000b85003076141644c0400d00010700752040c0c1d0001110704012601c20ba009204890207190443e00079541c540e101d20703519100035001e940080115030b0010000a01e021b10400500c4c500754031800880c12500703041c0e0100083c0030b110000040040c103400c2e402e00140c3e024803903c10500050340715030003a076141000240c108850145501040031000da103e8003a16003441c3c1c95101d202d214050300d4020b071602c82807940c0701990b40340580c0c0c0005481b21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 10791374 1107 10790267 10790287
    0x30c0503011a040503060c0403020301060f050105030403030b12030d1a01020a021507060f05010e070906020313050411090405040b090f010902060a0309021302040b0c0c0307050a06080703020708 85
    0x41c82403c05480e18002800c14405a416440e2074400103800c00031410280a03100c024014140303040c2400f4940b00010b041c0b8400240028105a580d10a03290f240c0e85407840e20b00180c1c02c442c1180d40703811401079060010070101c4000e480806030384800810b1584001452440b85078054082c4505162910180030b59402803d000c550700c503260544840c42610707900c5514020015540300700c1c1c150800c20030180144401d0740282c003c40d002003117490600359202d001c0317100b15881a2400030706142201c08812050145d03802c51503001742090b05100134401c404510f0742c0590020010b4030340098503070659608a40181030025004281440380c000e60600990150308600d0028200304502c14012030718a0482c1d02a4001e00b1405001142040501d41c0400010941c90010350050000314104000180104801d02c0b0300e004000060700002d483c940b203a0155440140d10642260300c03100d40c0c039 = true := by decide +kernel

theorem cover : BRFrame.Cov 10611517 10791374 := by
  have h0 := BRFrame.cov_init 10611517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10611517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 10611517 ≤ n) (h2 : n < 10791374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
