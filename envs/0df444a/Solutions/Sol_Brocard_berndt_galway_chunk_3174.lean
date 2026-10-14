-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:48.048623+00:00
-- url     : https://prove2.me/submissions/d60ca9bd-77d4-42e0-9f7c-643c6f5ac94c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 570683453 ≤ n < 570863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 570684703 1250 570683453 570683467
    0x40903090305101e02040f0312050c0a030e01031103012d080106170120070b072d09140604090203100b0304140c03120d0923010c02011a1c03050f 64
    0x24014a218051301e0880550544c030740c45052814000c48060351141c0700c81031001c510f503a40e41020340d1300d02d0310131000b0700400344500f0003070340c804214248100e0300907541c2402c0111980005401c64541d8510b20002c06e108000510802035080c52040c0c60195a00484801d5018440da01c00d81440580040032254200740c40000c041030b03210a4814140310510080041d64184030401f0031044e400ea0342e5600e2488248100c0d4040740010031540e41c4903c450500301071804041e0012011407901c0b0f4081d40d56040245805440d0700e0740038810002030081d01c00410b000e4402c0c000041c0290080c1e2260003003c5400000048002d50001080802000f080074410344030304042c50607010740c01004402d40168454424030020a250025a0900d411041c0520030700d8008250070420241c4100b41084d034440c4603c5144501902c94001412014003d02c0000035030481c0c0ba090007403d40d0b6074512032503a5401c0c0c501700700f0f25643e240c1e5044440c403040510711f034120940d2031030300751400e02a000b000300500801185170 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 570685953 1250 570684703 570684733
    0x10030e03040f05040b040b0d02060d0603050303040312140702190314040303020d0f090e0f0a1b0207090605010503040819140a0c02040b0108040f060f0207050a05210301060e040903090305 82
    0x1e01d05843d000c450912404441d4001d0200702ca0b10301810f243e000318600707119000750900500070b200003101c641c0e000c10030315100d459041c50350f4000e0700c1c100d001401004080b01c40d0f43c41d0b48140390390401040c085049508010703170000d544a6021600c001c00181141800c410103002c0c1c0c6404003054641c0b44a10b0f162982c90034084e460780c044500c10008103110080341107070b02384104460340565525003115000c5813603448c000004207200801c000209596040717005e0602c5d030841800000c414807030340200002400d01015105860740f50b44041c0c10310006106110004a11100b69180d038a0400301e45060440705034400c5420191582c03201d100e010000400a461603071011520300350038002d03075007402011303028401112000011a0054000001e00e0321800000340c01380c1041021921001c80507042001c5912068140766030641c046a26038882da040c00065000342161501c0340d070142c4440c6095615142c0302501c80f54078452028490340d81ca0b6034140405014005401c082c503084011079070048000004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 570687203 1250 570685953 570685979
    0xc0f03010f060b1b06190902040f09060b15040311060a091205300703030e031c0203010e13020108070c0816030201020307080a020f04300c14010e0a0510030e0304 71
    0x3881000030644607088215000c0003803006e01038054651800100d01014410b10700400c0e0340d81e01240c1c055100c1d1a8003102030030a0007041c3d104c0e80604000105840c0741c5080242c940e000480107602107005002c2040401c0108904030300d140e500b520043e80d80d00c1e9148003298003a800e6080840c900b1261001c03442440f400141c0c1001c075000362500381075800c0110000e84004a5036070b9814110388002c0020100107031098002040c17454652044a0510703003c54001100d840600b1680119a61302000400160540c0c6801036001220403e11215170851a00001d03d076890041400c0244400d40840e60204501c08049030b030900e400c44d0020707801940501d4024040c2d4020b0320414000342e1034102054040d403941c42150b481d8640383c06543e240c0f40c680540b80001450304a0b0503030f11a0816210307c1e0700040709922000501e4858041c42418a050042c401c10b40100da03001039042101c2400704c00c2894803016013000035110103c0d0182018400d4107800c8001e0705001c1c0d9603488a002c0464002200c0d00d841e51 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 570688453 1250 570687203 570687217
    0x7050a0c08060408070219051309030207090b060415050705030a05030402121507111006080109020306071806080c1c050735040507030602030c04030201140a020c0f03010f060b 77
    0x120300550699400c01299074110950700942540070170440c4000502d000b10000304000304000c2e9400145603580f00041000c000d600000300c4154942c5000410150305001c100013601418034204090b110020100d0341300c1c0524040e010107200341e9600404458000e00a4071400e59200d000c42c0d59800034004000c101d80c00558040740a0b0f4146511302104581c00f242030030004141e03405030140e66aa141c01107480c840d02d900c402e1f50034040c0c00c803010300c05000e6010341c0c80038090707450000c112404184189403810000500e00420011900c114021510650f2010802c4036198a029240e0f0f0301c030100744408511a40007940038008200840341c191415940050748250440d072208290f1491130103156a03050b00803144181c20030800d003481d209200909070482e030424007803012902c00366200d6607148101e038000c3c4c0e00c4078050080854104115a400b8214020090402c00702608120820303202950303450ba680e003054801c0c0b00310541f41509860951200e07825048080052054569403031020200713600c804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 570689703 1250 570688453 570688463
    0x80607030204030c05030f06060f120712051203150108041a0a050906010b091f0c050d1701090207021f12111902070815070207260708010501050310020903030f07050a 73
    0x644c00240918010031708592405034400507040c1c3d40e440c4810001807054841d41e41c0d50001c850028500c0715081001800040d0140c14070300b881020b040e083c1245000d102c01c00410044c681081001500341105035040e8603010282890304013500c036131030f1070941758a2032407411a565816408020780c14405800080c02410b0794000da807000c0e41ca5000b40806481480d0041d90040b280003140c1400d200440300c4038a480e416841c11240c1750215507901814900c0d01d00505d400a4898031003025032a4501a8060045c00307001d004600c0c20010b0742c085403841d40119007102200d0040d170651031a0ba03004070b02045181075090001c2110020844254403190001d410201c074045c808144846c102c0e00008120041e070704042d005003101003403859010188003000709020114060306074001002c3c07158611042040079513041002900005e000154a0071015920014141e8149001040a82ca01081c80084c0d880d600402582d103e00010110385184501341052414002c00540354043c484086540d842940c422 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 570690953 1250 570689703 570689723
    0xc09160806030d050f0309330708011203050903010f020a020d03051012021210150303020f01050c090f0a030209041119050a0902090d0606030b01090e0f03071101050408060703020403 80
    0x420501d030761825500031500110303804008800c45c0d0340c5110003a42c0c4c85107580d001c41d011051003c0000d540c0100b003100c1c43c203a00d9041c5120050f00c6190022480d0b1244a071f1402c2c2010350700d4945254803403c2c2d0500c02400380007000894a03041d450a422044084114903025035a525442100a596620f501c030410002032a00300801c4102400c00d07006070488080f90100060902c207502044401c02450081403080d20441e0160302011a25004010000c4440710151948500c0c5040280c14100301954444269140c401007103125071208003550002d0b242501c01100780c940b007801007110120a504003030f60213034068042100b0440c41d1441c40303000c9002036402d8195420180b000f0041c0c641240109a806a180e0409200a11096001d0445890020f1103403090328203070340710182125001e0704103544401c000001405116140d01540500300340c45d0300101200609074001c1c2d03860b802494001421001c2140d02c1c90708580c030a000b603d02424510090f107815050090f0041c0081d0300a00c800c6422140d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 570692203 1250 570690953 570690961
    0x1b050310050d1502130e010e01050a09020c0a240e160b0c070612021b010c08060105090a030206030c04080d2105012105030f07061a030d0903060e0c091608 68
    0x1100c0da088091542c00718010030f04500c0071410001941103601c00961103001c2c90030028500880207007090007004030800b940802c4d4104001d0082c2124036070008401c180c010480b00c0801e160014601c0030094000e06084802c036407809840c0300c018045050144500c1c205201c51402810100b40c0c0c0d900262120b50191196680310640b501d0783c003581c01c010910f41c225000402415020f0000401902c13170342c040c014a040a410700e0f54004480f80e01c0b00c10210385d5203440060b88550003a0710682c200c1000d080c49820f00035110001007940d400e6020003030140320080007107031b160520a0140c402804002054a071a00b00f150307802001d01d000c03480d80c0e03110b0030003481039640303907072080c1c4075150507142c0151300f130313a59010015200f1202c081c81c840300701c48c2072000b0030940c402e681059025100c8544a1080030800d074080221664841100c01c101d00d209030005075a40202607002a61401103c0e400a030116915040c42001b50901c0c1c0085080c03230b04000e0401c01c00180c140c5507001c8030b90600c400d4a4a00250b15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 570693453 1250 570692203 570692209
    0x8063303090c120a110a1205030307080105010306141203160f050d05070c12030c020a090204051e100f09080a03050d0e0c03121309090f0507080c0102060612011b05031005 75
    0x31141101080c50300419481e002040300a040c1284044002d030020f8551640d4040b840b1f2402c1c203400301035070150004001c1c0040c02f9400038407240106070905e000c0c01010b0401d4002402005407650762881501180310302c0300001700030300654519400c215922102c0e070307015042c040c48848034940704480c54001d41040c1440c0d10300034000d071248142c10030340628072141412101594030030a45030660500c4042d00e54000103a4a500b501000743c0003401b40942c0b510310f0642803014105201e590151036102c0082e60100356210520f640c00349800038031b48101d03803008006094542007440d0308007206600880c0004814150030000604200015086c200000380104803050f44507046644c0036681070b00080d01c1550b0f803014031000341c100c0d07240381c1412442642d90f5404500480d82da0082c125081d071807004180003402414032000004100c8400a01224040000004c1d1281001041b5034070804421a41c1504410250301c511824400740e2000100f451040b10080d140381c10442c0c04d184031012070400840c040c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 570694703 1250 570693453 570693469
    0xb1303020a1d150607051c1b1a06060d020307030207030e1f080c0d0222050303180114190c120908030313030e030a031119020108063303090c 62
    0x25464000320b0303620f884190b0703030491110b0f490340300942c86107091248401085051003013880b0b6a41d4041400705001c0400c1011748090a034100d00e844598445540c840031600e085140c1965407a0954429240c0c0c0d01e0000092682c020001d122025510100c204240250140e0040c0a00c41c0261246403403a207110b820003403d003046a0000034100100c410f13807031096008903d4103400c416070303a05079814150b034044d00202700d0300070714283c1c45a603041801d284912403007411804082c2006030003940c94035221000d9004808041c088581c100501001c00e8a905a0584241d5141c065548108400010b001034020104225050b003914030144510400764000c1c0100403c2e000c0350000c00181d811940c9180704030000d1484854150103010b210031440c03006a40c14072107111070b07912035113851044030000b180c010714040030b0252594030010b03007002040260303810007106039002400b115501c1d030f07072208440007880c0151105c000f4076510440981500039007404001440c0f0900201040300d0154410f581000031030303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 570695953 1250 570694703 570694739
    0x1e090515150d1401230903040602031c0f050108030711100f0c0c0e0f0405060115080126060720030403080316020a020d1505060301151203090b1303020a 67
    0x700d006100035142818103010003009a802180411400b80381c10201d2400d44076a1a41c2ca12481003200ca0f020986640301c07030454005c06e03100000e505050070540301035030728465420038240410300d503528541c0481c0070f608040410b48a2000902441d40d4403d01103a49030030441003102c50b24a90302c4041c050341800510380301000708640d1219110640d0f4901581d940c400b42c1c500ba83d009440303050120702485e500c000e0b1030007208041e041c1521403401c1c2c20b0440c00d080043c0c021a101c00080003c6115141e442200307941510152140e000042c0901e860f000b200d0441a04c811400740030f00c5040000782a080480408051700c0408107019808540101e25140d00c15800000d0595400b880401d101c41d2464039101702450080c01290501203a075000501d28059081049401142c04280e00c21906058002c82d80c1290b005c2d80240045801c00881101005060041120301170042c9101410b05105108000050503100d585030759802c1511461240e07101d4500051740100649900003944440156009842d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 570697203 1250 570695953 570695971
    0x40501030f11090f150a020705120c01141b1507090e01030b0106050318062508090a20150c010e150c090f030f060f09031314041e090515 60
    0x1d000c2c00d203c00c000c0c03400c2c40c1c80c5002d600030005021002071028030100800018030260010301c4024503040811000002120200050ba00811008100c1381d8200081059940c1803045450b01d0301300e0000304400003800d100d1b8031949881040c42010040348041d02e041c2c00380c0c419607200350f10380e5142d1914000c0800d0a1200070022801c840042210909c5180915000b541c0701100560b1840801c2c455403810000392008084000e400c8003030001d508940309490051040350800c158140313028204030f82c4070003000c0005819500d0480b8101c103032150710b00c0e484a812100800c101d8a005240e41c0c0d0f1012500610120070b00340d0319180c140d1690300c03400104c11415030b40440c1c40fa01c856035880308401994100614582c1c0240030340c070358111030b980d0038080700074460b151380000e145507d0508043c82c1e01040117098801650020410201c0d114500300e01001620b0403a0443d00c2c00b0000080801d004008a1b49042c801010040c803000d180030701c54200140645c041d074121100c1c1050428070f240c410b4815100950 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 570698453 1250 570697203 570697207
    0x901050a08031209120c1018050a031d180108070b040f151e112e02030612030705060103060e06010b0702040b010e06040906030c090509060f04111302040501030f11 72
    0x12100c5402c24009500800140039185104017515010f030300d980042401c02207a03004441d1114407280702e4420307146a50812001c0d0200820a038490a1300c5540300d07000070b010810703104c03611386022004001d440c00c411300c00b170321040341c0540711881e4401c040303402c0c042d203402070088a500250b00643c1800747c506a9800000c402486440d02d221001c0e400080742d0750206020088e103641d0038540c40794100107190b2034580c13140403504000465443c00e0148207131417581040b4940300b0840300c602c0c0400c64131404006941c2d00580d640c44001c00580341d108030030030103000740c4030000e25a0308005020840d81d04aa201c0e0700103100c00071129243c0c5440312802d000e003d2001c0c50034851207000d880c0030f03000742444c0201814003440810541e80072030320700d5000e600210305168079000c04004004120141c80018400903400b0080784c00c0504010b42c039808007500105090320960081000e2040b14803000903561001030808a43c6101440c07440f01075086882514007092078140004480300c094042c4904070814480e81074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 570699703 1250 570698453 570698467
    0x7030b03121b03130e10081b0f0d0b1801090b01060e0909010501050603190e0f010c140304350a0c0b0112020a030605070c14010516090b0301050d11030d0903020901050a0803 76
    0x9052004000c1400380811740710000080c48110500c480008c155141c41a003020b40b1a13001486801960090298028110741c6444c030042541d04036200d4028000740d0704240e0120081d100355025000c006400340210a1180c00080c4054020601404092007039420050a030b40301080303242254400d20500760041c00400016030101104268040300c6c950725480002e1501580804510780b1040074141440c40e0f42d507401100c0440c1c3c1041c0b0b1407150361420b658003403443c5455030390a1000c0c1e0850010084059112900e0089541d140d501806244229625a916640781042c004d0000f03682000aa4201d0035074000807a681c02410390038160550040c20b19a00c662540d59030400a1900503c074604000091000c8400111800e40610030100f44600116017030900c0b1018610704803101d0682000e2141e0054104a008040400d07241110030458185c0e082a480e401e0031901e011182031510343c9801451380104400e908140b10300203a074020b9646030901d81c5caa40501c0841006409180901d130703c20703c261 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 570700953 1250 570699703 570699719
    0x6040b100e0405062d011107140f0301020909040f020f0a050904030e1c0f0c090501080d03090510050103060510050f0105041a0904050412020d0306060c0b07030b03121b0313 76
    0x7107802a00140000b00841561484045401446044444004000c40790ba0440b50380c040300c034590441100c4d024001c3c091610001c1844440000749c064010204403d030812903640a41c160343c1200c001600c00d251034641440c2106903451180400ca00c0b5548411468134a0306041d032707502c01a64005010904142c41d02d032400c0c2e0702c103240f00034100d5010710005804041c81480300c0d032000d409842202200074218840c030340400c810410b074110514152a140040004000005010340a0010790400164101090038014102100a0b05502150381030600000810100340c0c04244201e00802ca844101611030080004841d803448810340020014001409070280500662034609021002c241c50100a01c0115060714411502038804061003103980c040d8903014481880215050704c0d0801a0a04040020f40754505011001e45a0700c80d01001a007400d019501055546070010100c413282c2405014161180e032080b02c1040340342c00320700b01120f09010300000780c480d416401040c4840042c244080b0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 570702203 1250 570700953 570700961
    0x11070f020d0c08010c0c0c17071502070f060c03110105040209010b0c0a120903031e020a0803070509030708010507030b01180302010c021c0b01050f0919020a05041a0306040b100e04 79
    0x402e4031510000e0000082c140402d200e2800780e042e85440d130080c07200c6a410281d180061a600141c8690491680191a40001725071003041e9048100301045441806004907c1c0403843e400440c0b007100405800305032207800820b24129144a41e079a100001c8442c0302c504d00780c0790180c8000350002610700c010b200350400000030701048000e0030300f1500040f03280d4980d40118900041c140f004199004010f002307140c1d000e041c10360f45c0102c0802040c40b1644200000350390300078904001d00101004804500c0c50b51260046032050107000f4101d41c441a2114245802080241c440c50042864014100e10720350041d1807510b050900a01a11865840c503001526907000b46241240d1025a907900070840c6000b000400d51254000d150000141d8100300504c00b405101c0b590079440780782d40c2e50402c40c0611400440c415100e1858102503210400340030140c505014a410400b00300c24010940c0b000b80180303a0242d84113100884080c030036581000c0070b00c085591a00d210000054007111241c40904090300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 570703453 1250 570702203 570702229
    0x18010f030905070311030d09081f0e06041b1e050405040f0b090c0114120412090f18060b190518060f07060c030501150806040f0c0f0311070f02 63
    0xc01250540003079407110b00742801e5420844e404024038a01d0403050404120010020416003840b44640c0e0401540c16941d107525030000d00c680c5920354465041000c141c11150320300004c01c08481d072506152918100440c2c0324500340c100341c0810b01c000100c901c1a20043d650b001240340b44245001d003070038140006030100070300035112506001002000503160300c104a200b0098000940303039140022000400358070340205241107000091040141410718090000c2c2c00030f03488680103c000d840f00c001038850341016801400898002080012a80c0303001c10441c5807104002d004200c442c0d101d100d130408600803512920a03c0c1c0c0480140c1642078001d600503ca4100450300d030030043c00f40a0300103101d5038800d5140b540361040104429003044410301601071078020a00f014040f0358104003072540725100c0e0f80c111100300958000420026195544001c00446100705c0900944081d2540542040c0d020717100c0b0310010f4601118043c1d800401000e65048540c00f02c01403482280503020440c61102d046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 570704703 1250 570703453 570703457
    0x60f0108091204030807061b09090216150e0f0a0b1b090402040f06030b180601051612020706080a0c050f0306120f101107151508070e0a0c0518010f 65
    0x20029803031280080083d10056106512465039003030540303050001d840f0f1311800c2c50124104446140718480d00040079509491030303540c0068030741c0000b01c04200002c1052741c01034400c0000781800c0352a0302e03440c0c01c01d1846d0044101210241e200081c0c00da0f81c0d80a07224009400c0e04c5295003c034000e00020488111000e0748860f4050420301c850000504030b9209a00c2001e590720085010012244c0501500407000c0d0308641c8a00003d0b80b0f200b0400000200600b6a0304000d400900e005012201944c2c00e54a580c0103d00c103500d4004151002c0c0d40c6250758010b1001244404000a1110340c8601583d5941d4540d07aa07510f003062030300031030443c040d003001e04a2548002c03002c0014090b0740c07080140003c0c401c121401451584003217a5030604440c1051080009000100b0402c80440c448131117000f05800c01c5800011030030700350b14200c4107000703040e00002028010164001004000c040550340100c000f0b4004100790b4a0524007928188240f10480341066901010f6010075070190140f8815641c4034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 570705953 1250 570704703 570704713
    0xa0b070b180d030504030f1b08160c0909060615090e0408040e0f0a0c11070519030b0705030114121b011404060809010b18010e09010b15030f0f060f010809 68
    0x1d54121401c2c840b4450072030001941e0342e41003109040c2d0200001c290381c421b80c07c013031603e40c015030142c20902010f000050041c1900107480d120307803143c4400082c150354000c908162030540b900b0030b20024082d0b04000351012410141e000c180e0b0b0800c0340300c0c00d0300b0b140d15440d9007100c58640707610720f210190010015a4a8101448002214440b103551248a01e090305208019440c004842d0011110f441c030f4000200424201e0007008000001144010303030b6411100303140c10a115201000c4406a9604010901540d110034804555001805181070f40c40c0028905141c1c00e846060100e55070b24251880840c0d0311080e13040600c1e81110482d10710860040c9040f102118440380350b550664803680c441f6001501400810035808000e1003000140e000c21520000b48410340700c12400148030600840030ba5040b501c000c1120710b030b004d40c017000a10030040c01481b0100c1100401e2402c1d0340088030300d411446440d600107000050195061846150700422000c1c03074249481c011154040002e01149052041d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 570707203 1250 570705953 570705991
    0x120a09021302071101020610150e0f041419090c050402030a0e0303180c0301020f09010f0314070e0f1503130309050d050303010302151201051c0b0c13050a0b070b 71
    0x2a000610743c0c5405014180694840b400009240c40401008000212903080c42405062102812402480b05616045c0c640c2e40714a00090b2011909644090340685803903582d101114840c0607152260300c8e49018844c6808035910801c095a2804500509041d40c112090060b440c044e4003031070300810100c03000140d03500490703060b45c510b80c411303114891441442400c0350240c14003007181e0505030b04158025424032002e404c280d10030780030f440d4103141440003284519074414429440049003031503909a01c4000d060200c17000c1c06c080307103482e04140540103102440c000341c20800851420641c420710790a00e1640e40c881c2d910340414a41c1421000c010740c05078005056501c00d4918040c4a0240d8061903403075165104102502d1032083c000003100c4400c3c080f011a0040c03c11106044580070b40e0005540810f2514410141c0d0680350010401e421403024800404602c80240118040c0002031414241e112010001322090310702c44c14942410810088000804c0705101c250480401e0300201445c0760 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 570708453 1250 570707203 570707239
    0x13060e1501090e1315151208030103061e020d0204050a150903060b0d050106240f0e01140d020c0708211c0e070801020c071203050304060504240e060606120a0902 71
    0x20041807061949070b2124142d0382c400346c4008042c1c004000325480d20182d0840d603036508105010510001c1c00c500c4e40d80e600d600145220a42d41c0310701c140c034a60210740d180c1203440c00304001d401074082c05000d12136111020405030501c000c900815105503e0300c5c540c4c031f032540d65410003500c001c8040d1900543c4014244c000500c00740181c2010b058901841d0b031800c1c6910315000f0455411140842c1046440c501d51071245800107031a00d5549000e10f02021104079079005041d15106151520351403520005028a0210000c200c10341070312001001da800d0b1140080c5001c4440200305641c000c001020008030ae402c43d20550700046a4207039040102c0c40e2414039509078100705403644075120994001030f103468104000c1c0290030180c002c440511500b0180713901d0081942c0070082005154590fa400818240000d60607080f4071180b10303036a09120322f41c035000c136100a8081010078225502c105004540245031000c25102c60f4109032507110003680d5500c84038005004803001c20781c0c00580c49556594880 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 570709703 1250 570708453 570708473
    0x150406051011010b0109050d150b130e0c010306150c0c1505220f0909050f0f0a0611120402060708040f0b12090a0201020c0607050c13060e1501090e13 66
    0x41e0340c646403545141c8142e601c0301c1c2503a244040607410030030f0840086c0320b550b0300d4641c00301e60941c200301086040c0b0410681803000b400b401c1003031a88240a017084040c01140341d0013207540410000c0c2903844907000c4c04015000c2d50b108c3d000e85140c2d03201d1100110101c0d4446d070111075048e4064000260080e0740d58014184d11500302078503000056000405048e4400700c1c21640c00d1566480024280040ca80307034003820202014001c14400176104c080d440240001001074000000000c016100030f16940d11030155200c0c2c0c0d803d4100ca0750750803c41c40c8117030302d000320080c3c5248080018001c0708540d6a0340c2001040d40c0701c07080032203100c00248001318450041800c00006044091140c41d500d810b82e5522810002c0000d140d5041c1d40d01c681c1407000140d0f0b001c2504100300a050310802e4640c0c1180c94494281340c0c0d0032104c140c10a01280c50f1030409041500b111046964000c0088a16100d03001d41c12400344a0a02e00c502054045208104ca00c0c05c1d00c070490390000700018003503003451459554603010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 570710953 1250 570709703 570709729
    0x90303072a210c020310020f0712050d0c0e0306011203120516121a04151a07060b0a03120c03030605060a1d0a0612022a011a01140315040605 62
    0x221902621002d0071a103248180c001c1403490411845141290340069a02d110741c03212154241d401113a104401000c82d41642c25480c1e0000c44d02002c03002004000744507070444480e003402281024161500f060003031640031031030100580580242d81c200444c0702100701400c00300b01e0801c0a081110701e812619031090601840002c2c82e0310342c0c00061280010f200d02c01c9807281091a40c03274810300c1c03451000f550820024060080e58081031000c140040003090802d158051640403001000541c040364958000300000c5100f01c00800c542401f240500400c01100d0000400d005648060a4401030203500f06010045c403038500800c04e130780c686020440c2d54110103042004a40d90f9504c0481c060110b040d51031051500f910b002481380d1501200602c4c1d803100003980b0303480c0d030740c00280020080c40d40074100030040c1403103030715066a641859010b030007850a80980d00070305040c1079001d62558803072a003402c0c00d1001d0b40f07005406c3d030b15040312505030942541c3e401c550040d5200300004098844a40341c0c010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 570712203 1250 570710953 570710963
    0x1090b06270604060c0201020c060c0c040914070e01030b09120a030504080409061e080111090d150603080d0506010503060105090405130b090114090c010c0b0a020f0d0204050117090303072a 83
    0x1440081c1c1b0000e072511081103d11440780c00e00340301141103c02e001031200d1000004a80200c4e040c0c01600307110440c280c0d20f54192103140100300021858180c0c200b110b81c100c0b80300d44581075203680c1c1c2c001c04070744581e50391109180c204000c2004100c514440d0b0022030b0021b02890381e80d8601a503542c5a00300712090ba901c0f0083c0040d502c01e51407201005861484020403404009001c3c0020060600d21140b150540140c8034a100c401107c0078000d002c0c0c2100d035562413400c03041100d00c1e20381c00c001095400000c180c41045042c0000101254441d005882c0940010b84819082003600b0301040090a0300400034a02d10f80300e901000081038000b9402c6005030102c100000d02c00c2c84c049240e01c1c6100c030040012209a01000c80140d080c3d030321812100d8065004410030509840383d440c02400b920941744460072112010442d201001703101d130700074000c070f82c1d0980325000804101c4d400441038600440d90120107070401d00000b01814001d802041307407545949207484015590105038802c851b542c04003514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 570713453 1250 570712203 570712217
    0x1a04060507110105060102120d060911030108070f14012001110903010e1902060c100204030c06080a0c211107060507020d0503092107020d061401090b0627060406 71
    0x201d159003094112400d08000b500a212914140c03002070b668000c0c4286a04010b44001440d07543c144441c0d10410203410703440c0c020310280136061240300c066042801400c3c95070042807800140e1600103034409089640005030107821041220041d100302c2030201101c02c2034180c0303010110f04c083c0c081c07141c1c200d0152904211030315500000305041c00c542c07000c201d00e0f000d40c0c890f8501c0d0608000e4110710b450702a0307045440d1581c0e07640b000442824039050744d110081681c00400c002c4100f0610941000654200344d48080c1a5954101002e0685d5403040100010941e080600500c04500302c01c018440c4680368004a40007500800c01c021030f510803082620703207070383c1c2d5801d000e20340e54180806801c0520038079140e8103608000480c10303140c21a0ba2903100c8900c11031510300c10a41c0215003070f5052540c00400290f020003c506204028041c800560300d6050410000800c89100f80d108190b28498050b207a54107161402002c90114026900035140025800200c2041aa1400300520190026aa90341 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 570714703 1250 570713453 570713461
    0x301f0c20061f0b030f04020406030209150415050f0f0105040f171c05180a0308030c07110105030c0d02031b13030312050f06010305070c05060709081b090f041a040605 73
    0x1103242c03030300120070b03008075410030100010003549040d0f070b1300461401c040355240d44403840010024117165000940007240c8404200083c0c00c0305a801c0e14481c01554140001da00b420b1030311281400a005d55075001c800000080d4440c02d18041840d0309000c1814030030f151030f44500940f0038a072070550000c0c0a1408641d25044280004e209800b22009044001140d41d40024005042401a103100300020304400c112103506030365440d6101c0045801a807030310790300c0c01d00080b02800b581c8410000d80d12855150010301c0325520800c22648690510540b990900300114a200003a6101400420071006500f4241c40c0d94060318009101500c0c50b501007100c801c1c039518026117014200c141001d0003524150030000481c1104012076804142441e000a02ea560900240c030100000000603100d403044400304a22289c00001c400c003501d48442c116890030103080010156845000e1207907030480c0e460808101100424801188c000344680c24100c042c89410402142c4100c0840e026141152264144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 570715953 1250 570714703 570714721
    0x140310090e0a0807080d0f0614030c0102070303020c040e030c010615090f0302060315040f090c0614071208090717010b100c1208090c301f0c2006 64
    0xc490040e1203503002d00052061a2602c6401c0d000b8480c0c080c0000c60005034451504000307621000031243c0f8400c00700511a00d644a042861000b0a840d500074410807041d011690f00028000085130b034180c1c01008023500e0903040c40302921000d02001750510040c8844110f001082c050030740601700122008000c8510f0070401041c001c0203034810240c500c1181c0f810320241c6c44940850754821200808404224108004180103000240d071044406103801405410030070b1500c440ca04417811079075120310f00c2c10005813040c080e2142070401858840e9100309200100d00800310309601c079a10a0544c1d0f11a50f4600201074500d121202c003001e16507450703480507184d141400032203500b502640740c070807103000b159500c0c4e030324001c11038800d54207100d02c140000300d41c01c004114050030748078007038151009d880c59542801145a10014404000c450765421001c44420002e1030110304c0c2c511600d00603001e81010140b1005141c0f81c213210b0204001c2d042e802d048094603040203240c4440c0003005048900e498100d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 570717203 1250 570715953 570715961
    0x9020d08220602030d0c05070b040b010f080c06180d02060a03060602011107031b170d060503010507020a120f090e04051506030c03070902130503060f0106080708130b0714031009 78
    0x204001d80361440809000307840e8000700f628080d01d00381d03900007500901240195518010008014640c000000405c1b04018402000604850822410920240d00d480d0016125403807020381a40044081c41604543d0500ea0011104c009000d090070008010540108903190701030340ca5400804d489040410819909105601600c5038104100c2e0504a01c1c1c0e400030550b209005040001c850307100422410300504400c9400f5440404500c65541c100d4203079003502901c0c591103076610035460302000803031007400401c00e07550381e0307074820610f03410058000000d540b007002c50909881003103081079021518202441c1c0e40da0207640a40700626002e440b1491212034081c006086502a17002590803180315140050b12000b074803111031000d0b0b02c400340850300d04020461503100302da05101e0103052240040100d44064103a0750140d88450304c994502e141070712100302c2680e42c03d40c141c0101e40540f0104100800e040c1c0c02c0b107050b2501c80c41407450750300c1004050300155980382407030741d1b02581000402903d00c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 570718453 1250 570717203 570717247
    0x70b07020312070f05190909021b0c100c02100509040c0522080715020a06020d0c080a0207020a03140f070303021b011106160c06060f061205250309020d08 68
    0x7900741c403134000a04006000c0d020380102d200088200c0880403104c01d02488140d005007452030401c5440d184000c40b164100301e85440c0980a03405800070780c2c4120300b00451fa0403500c2c4a1a1070f0080c031441c2b55400e200e62004061211030030080309008000059541d4007030018010721070b685003030310b40c0c2c9036081c0364442c0c5200382e111454076900c0c003000304003800c7c0101d552011184400507002010f002150241d00703142502500500c001d2000511500c2c500099000101800c0789903240d00003a59900501002c034800c0758006980640948000c0001445480f00c2e202e2070070500381943c000c80c02c07080c1e48034542041d50b002140035821884913a52036140e580b4078215000310034030740140004002443d940e142c1c1405407016101c600c0180303003e213805000f0348889601c035600c07590402c002542c030025100b4180e600e008020020b44801800c0320255030a000d1240582d01d401130100c0d00701d008000348906140340684820034940c6a07018900503a403601c0d440e090a5004552007031b038400c800d408200300448011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 570719703 1250 570718453 570718457
    0x6181d0115050a0806060a09080a1b0806130809010e0402072118140609120c0310060510200307030206042a0b0304051c050903010b06090d06020f070b0702031207 71
    0x7200300c0c1220344e0f01444440d0860350540d8411703643c0810700340854030400d05401105003841900d40f070608100c001f00d0350200000061006030729491703d4070002038980606a030394150034000c1c0e9900360003042c081c0c0010407001d48141007100303564503900041420313a006003000f6181543c1c2920018450441c0321005100300038a071030801d405000f000e62001900180b0300910b20000e40040603d2081e07101e00080311582040140000300392112011650758800c007280c0ca4a0090041030b28412840c141d500900c000d0340d2004080c401716040c02542142c90600d05034400049505c8103410351b08041d070a1000f01340c07803402603000d41100d10b4941400c0d0108400d50540c80c1d90741209c50b04445e0800410018a41a00c0f5404007041d666100c03400c00d20326015014204d000b0350001c500710034004a0f0020001c09a0420070b800a10090b91034004121550244a0302035401800d100000c40005103241c3c0100149070007404820300b00011603c5500080500300c9a06006d0303400002c0802d58200110305150307100300f081c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 570720953 1250 570719703 570719707
    0xf02010b130509120c0f0c10080a0b014a0d08071103030a030504050c040c02030d09080d0e06010501080903070503190e1519090503060106181d011505 66
    0x4040800c4021140c018440780c40c503510000708410308018841c0c090610702000255031500b100307550494841410455a8000d40b04060b400c0101e810a003903080c801da620341d110760850317650b813200c488041c00d0829846810030000442c42c8a101140c0c1c880c00510707004810180d0b40c003060000590b075180c080403900421000300340d030341105159074206440b40e509900c03600454647e2141d00d0151207405414600036403500010401d0490300e42d15500ca6031040d80920700b103034034000760380041c082200c2e0201d44d9640160800c015902c21858203810040e40c441c42804040e2520902546902c115400c0d50f2000d031340ca07080400108117941c1d20101a5400110700c9014619200e600d59582d60382e481034000718065040d0402c0004040d074012490303804a080c0140141c0c091040c0d0700050f00c201d0b8406105a10072704d107a4884492428440e80700f1034140c990141c014000c41c0d09160b400d681001464418202c0705a103400003080c0c02c087c910f096441c48940360100708255041404081695981e081030300200501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 570722203 1250 570720953 570720971
    0x6020f0d09210c0f030b040b0604020c100506030a060203010320010f02030d0b0604083009010c0209090f0d081e06330c0303040501061202061e0409060b0a0f0201 71
    0x42c01d010b07040c00d20740b0001c41000070001d40c54469840b00081e4880340d0301c507400b20400004c0c060f154810610480c400c140c04001540c403013027004201e00501c0928103081e03100f4404007100e680309a00050704500000c0842c4e240c120595900001c0c1da000740c1040300d00c004100004040c2001d03a1010510009003420401c46a10100750001d40d40c0c001d10009403c1e440c1c65403050110f076203c46040382c0213403030907034150761134180161008841c802600e41d40c803034880322000017106034507184001e0300d01f44041695441c0f80709402c0d400304150b0b1000504a03000c14040e5041c404203c10040007410001002c5844a250b94908038544100b01101e44a0030032030281004204007e0f55594447c6992030b1914940355403480856540182411107451035030750b850702002074000081031002000d584a50310980c000d000071616a1074000d4000024a0000d4010009110503010081c040e60743e003000230742206c641810700e50b5070440b010903103185a01001d240341e00003610000c42c03944040c0040c01000940000d1180341e075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 570723453 1250 570722203 570722219
    0x10623030606030c100f0903021c121407060f0b030a0c1a0304080423030f0304030b06030d170916030b04021305100b0703030e07170717060703020a1806020f0d09 71
    0x141d445c1c003007000302120141c01598041c00565003d1500909004114040c552144851900d91f40049d100b1503603401c00a003209210301c005240c3c4803090240541004010b079030f840064414032403c0149903850b404081c4194908000d45801c403801400d0f8150007500e00b0044240c0c6145013440c2036980182003041002107114001114100d45040c50348200000c000710b81069207500d08400654075009800d6450040030000018000341da02600100703956444a008040e071700d902036034486c0c0109508908008003100482c0780203034000120b2043d9000704c001c1c450344000f0f0201c9500211886c10b010b20a10055042000041c091410207101c20001c1d41426540070040050764440c110910b2400145801054880d8011461010030001221405c1e0384a4002d4020b42e151703055007030706d1403007880000200c030303152101201c0f1481710300d00160105490307a0300308401940c0681241c406000c00f80940c0c455040180d0f035000010301d09607002d0200100c041d0b00d07640c148520604c1620070080140400c0c041c40c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 570724703 1250 570723453 570723469
    0x71e0b0f070507022b0f03090503010b010201020418050403051b060420030a02210f010f0b060a0e010e0d08160b0109060305061305070b0309010606230d090302010623030606030c 78
    0xc641c45c2950f1504035042081c03001c00704071070f00e000b4041d9911030440d00c10540c100011109a074400c030024070402d031022004900b00d004500c1015941503448001c4850540703641e104541041c020302e0150300e07040321040c0400102030202c003d0a100c0d0300205c1048140019003041078941070045036101400380d01c0100203556501ca044001e071003641c46540b44c9142c032406e0711000c01300405c0740055074039104102204900a0070350462019001d802c0c0032080b07220380740900c1154408415500c3d0003090111480c01150b0f0800603030502c0303420506181c0c040c0c001c2400c41001c0c01000c0b9440c8500800043d0b00d10f042c03540080180c1c005100182040c0040c07001540224a5a5101816101000c2c554003141032451600203613501000c2c440900105000d003140d0706401090540d001a250000c5078040d000c4e03200034406410120050005040c0202d0055030405c0d04540c1a00d40644004141581c0b14240c002ca5110201c000e6030031038060f40c1d9000001d08050080303642c0000100d000c1d001810078000410256 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 570725953 1250 570724703 570724729
    0x40503090111101802030c0103022104020402090a0b0d0b1207031104091a16021506010c060e030a090f0504020708030403050703020a080403030f17040314071e0b0f07050702 76
    0x101412401000c01c6990403c40d1106408a80702d0600c040f4004c0c4100794044d21124406a01034080c100c1001c050354040e008540102c0c1a95807024403040c51216172896101025204a078003070303020005a0815696003110001a2002108240e074605030600307c00d08841d8460a00f6015001d086000f5501c0719010440504030303500a04500303001d40c40080058001c1406003001002070b6403407803150705040c1118908a2150801c2d062190310203000500580e0346425030b80c9801d01034a0500006a0075510600a512000703104400120300528840413603811a00b05110460000780710711010030402d8041d8495000034401550114a041400d80b00c10040e07110082014061100000d60042010702c20040841c0381e68001d4511500d450300d0789401815420840458000554008801298100160f5480380115410346a00d01d0f010401c2030708031141d40000605484042070030090841da0000c2240800f00680b00b0110243c070381c40c1c410505105100090071660822800303201e1807006881c2c1440d41000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 570727203 1250 570725953 570725957
    0x30f011b05130803030405010b011404080a0f081b06370905070e011508060f100311041e05030601081b09060d081b0601080d09180216080d140405030901 67
    0xa2518604a02c12a0150690001074244000002c10060103019484085034140980c1e42c90f01e11007011000039403e0040d03000328840b60b001050600300041102d14482c1a56104209190a144420039074189a04800d007205a003600a00c0401100494200c0c26452440d003420342c800302c01120459560400c7c1080c140c000300250350700e9074002801010002c5200900c484d0310507035403e40e1039918a248248075a148140800d040e003001c500146084081d6004e034001c05840801143c800322030407009050084203800a9120400000c540d00c00c0422049107e2032420130401c400925140626103404016804110380350404003648601807285600044c0038641140c58400d9a00c132100041c00503032010714010111440000c818103288103480c8080c04a20708101a03c2561307a8801d126920741c1841c080120024031810414800c400307203450300444200e604070005040c1100d040b507804521034505415500500042507682d00303504075000c0c110030451031a03a03426607402d15a0364517690380070313903808541 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 570728453 1250 570727203 570727207
    0x25060207030c120c0b0a0e01032007111903051c02010c0906030c0e040204030b1014100c0f05060c031501052b14011203140307050a0c030e1e030f011b05 67
    0x2040c0100442504045c0c40396400b0b00e41e6545440ea0040d007403101c0503038454080303810422070550080740e0b50111458004582c1032035240030000d0b510980600c1c803d8031a20b6208011100c0b410000341d554200c10080c511690062400507032422402912140c1400340e1400c6a0611510b503280590100241c4110b80042c180440e20b2540b0000035110460000d07856600315101280c00401d00c0768100d02d05024401c01c0c0c030ba002442d6103680314040382c1c880004d4031940200a070042c804130b0b140320b00342c1c0500f00c03405210041411107082d950715082000596899042c4a070110034816203210440c0003000980003400c00034036144088546500950961282c4451140d00c6a00041807818070781040f0100810307424034003050768507807407590f000d000417140c190b00081c0c0c02146c61039007190000469000722102d459540c100304803014115080304030441c0450400003481076151803a01c544419198240300130400a003200800e00516181007901c8a4030100c44e070511100c003210200d2040d0804001c0004e2424a17 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 570729703 1250 570728453 570728489
    0x80a03060810020a1b0f1203020406030b010903030f21090b31032d03020a0906030209090606091201090b060907020a0c0b090312070602090a3f020325060207030c 71
    0x1000c9511400601040d034807c440d075660681c50390040080d10343e6601c2c104465402c0900446081500d408024003240090340c120000a00480c50361024201ca07c2140e00e80000c103a041d1000d5403840b910442c2e2000900c41480032a402501201921f00c040d0305030000c200700c400303059912980d50280054107001c003803a0403194170f40f03850000f00e00090044a142080c0b81042d14020025804030350301d80000343e1000300100305140b0074000c072450864010800800d54440008004044d40030940703d95000d6100241c400d40c8000a00074101018060b42000280b442c162092150040e0f0040006045400c10300000c1e002441042d8000c0c103039100c05880e2500d824041002c00e291503140d03462100d1060000c44c041c02000656001406560020b07211404895950016408209401b4042100d003011b40f44e0090320410002c1084010142521110140c2e0a196008a82800040b0100300e405c5158500c42c54152105003028500034007041c030042c040240f550315a0f00d200c0d0300e240205003542d15101240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 570730953 1250 570729703 570729713
    0x215040201031b09050909010209060706111303030509031209090f07200a050d0e13050601020115030b0f0105092707270b030304121e080a03060810020a1b 68
    0xc41c0e25a0300d20120400c1c40b03500d4040c00f03801303001e00d882918814900d050004040c0c48040c0243c1d0b070601c5001d0300d01814074010399994409081d2004900115540a016490b00b150b41c138120703000154003940312144e80740744000505040c01040c00341d9030300d840b40c00c01c00c2240a446003030a00741d01c51700320078920440d03480322042101c4000111107a1080c400c0001e4880751044404502040090300c920215100d10314074030720075a04190020f000c00d40c043c0e418105c0c0207440c1c00c550843da502100510000407806410f01d00c842c082c000c5030f0070548500503210100400c02c000b401025026020803100c110301481d060300c4801562a0664070701c40c0310b0742d0446080c1c03075104040008102030000014502c505072010042d41594207241c078911842e1500f000d201c00d103142404070031101960000f9808001010741c03516510540c4080e442c10b00603500c035200b061000324003600040d040c2d60341680d40c00300c3d46510300071005140c12010305c12400d50601c10400a9a1150041c00c4000d901032401c7c85040c001d05a4100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 570732203 1250 570730953 570730961
    0x1d010e0a021c020415080a14240d0f050d0801030b1501050405030a050109032601062a1103011406060304030311070503070c1a0309060a020d020706150303140307021504020103 77
    0x2440c8035250000c24007050b45d4003800e4480407010031568902545944108069041e0b6641c2c1042e15032446042c0b02150b0060000000184180c04000394144034044080206031440ca401c40309030b0b0100340b185070f000b040113414000da140c003085900d0400300550440e15819003090000e414107061800079a5030518590180040c3c400a00d00202641d800005908125010340b50a4000301c0000f01302c01503004003803c4001b00007095070401e200d5580d05030b0800030181c8165515001308450b1902452140c00b00e80c1d1400c86031505a4441d42d02019101d651101707060946210841c50740300c1440301d10402200385c0719101a41c0d8040d415280101d09440d82400201c03551056900103011404005009002d000406441c80200d99160b031211045a60782146005d0a0000340c84281e0746030440d001143e4400503070340240403140b08842d00103140040d80e07910314003100c3d0044101e26080815000400505405c25070b001c0c0700c0b4009000746855440c00c84802074031860f0081400d000125020003003020f59200b540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 570733453 1250 570732203 570732247
    0x1501031e06090f060e0c0304030507020f0d06090c0b04060e04050606160c060219020319022709190f120c15090b07090f060818010203010b041d010e0a02 67
    0x20082010603101c02040002d00900100c1605441c1405400202030174036110311403048002c008041d003142c54507581181c25031300900301070340d1104e910a4845080d9031480d40d08048a803141030b0000d982d0079071303161084070701040d42e00218040c90203100400c0728981109510300b003041e0894002450f03075141c400245003030140041c01c6c207038064210010410010340000c5d0070203442e034070b03001c03100f145804101c40d0320300941c03000d0000c0d0907400003454111100610203510070020b1004000c400c60005800380f07020404004030f484005092a04140941c40c00c09002c0104500c090850b81251001d0036180c082002d800c01c0e07070080c4005d0a0410700540c9a00c144045900640d2003200d048100c51040710150241c00f0341c40003500d440c00b0700d0001c2030b8101d0042d00020121b85220420007006894440140e0301054001c100841505103a036072600d400c10203100444c043c044144d0b00b1a1241c0c06c08103600c04e119079803003214024260b840018070280c4140003d295020b10b6000003d42d82d21070460000301040382d106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 570734703 1250 570733453 570733511
    0x1b030c0c0e010f0305100504021e1519030b0d05120a03090c09020408100e0706140c0610170a03050f09011b0c05131e0b0315010f0617150103 62
    0x1200110380c040c0341540510884e4052030844101007074032041503080319000c0e1402944040c12040d160000744030102429400c1900810396810505081c03103050f03007a408416980010510103821480c1a609449172600280040d10410028000c0d5a60196208040c892142502e031004c50b90b1010320b841381c0c121590a84e0f1011303510708407a40c1d0300315810194006004138019030203681c0c002900c2c0180783c41422000801400148200c0d403400e0310580701c0c0440740240c1520518104500700e550b05040000314001c2d5110701300182a5451b26002c03050101c0c3c3da03000010107410461311500401d5015095940c00b60741100000e40c4c9030800700050b11000085111018074039003c0308002e00f4040c101076813204646059462100c011840f181c03d41c220340c0948000241d980313410a0080c5044102d501c80c0c00d03600c402034222141e0000007941700c2c1408509a0014285c0311410106105003584400041d03444001c0300c142c032500d82030141710001c1500407034404904040d9600600602da0320100c50182c4520402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 570735953 1250 570734703 570734729
    0x40b13140a060c0f0e04050c07023003070515060d050d030f0501050411041802070b0a060515040302030c1203040b0c1605030303040213180804090b010f1b030c0c 71
    0x10041c0e1034000980c1d042e100340e03107040030b20010702e4000c480c61400d05125940f64080d4400c0242040000c28001c2c0c40022041e100b4402e4000685a00e08084107c180845606503100c01c0d50069185600d111325540b070094100340004000104000b0700c0b0003800d962580503a842da81c848010405444c11420301030040c0c814850301c0c4140603050390044d0800785c0000030502250382c940e000d020235681c7c0c0b03940840220f00200800c2000c46d42c1d0b070b280000007811045002d4900b48071a21580000002a1034403040345660b44800c0009181c19001c44041e05242e5449900f01840c1da0002034031207440d1001540210b14050503080b051609008481c01340811044031526008600c66181d50381d07108420130f000b2015880000700303c82c540002034070320032507008298115244c100004000601089981c8682c040c031440d01800000b041d40026201501044034001458540140010700140c00181708030280410b002d407000c001740c407903004040c1958050400051301340c810700d0714002100d01070f80800005410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 570737203 1250 570735953 570735983
    0xb1c020f06030f04030816020d1112040602031314090103020d031206080d18081c021501030b070e240903030904060308070b0a020405030307021219080910021203040b13 74
    0x3d10308a050046000e82d84000c51982c88035513031070852440b01040030160744582c50100304580f040d25100c00d01d07540b000503224041050003400b8826081504088056040410344820314040c00420710002d100044540b4030070560140442d007112411301010b03010340d0900d013122007414000c801560000040000400100c0d68600d5415101c007200012800000c120400e8950b1040c824a0f002c0160f070028809014180b10260341c201c008485006004194022012001000884841d000e4021405242c481c4500d2600c0d41e401080c44c000074801d64862400e13040c0300114038101c61070010b555951808000da48007030140000c3e20310701444c0b00c000d80c45400c084020082000c4800a850410310454400d1102e8940c1c01c8801c2c140d000d50b000c2d96415920501091000d8640200403403070604d02c000503100715580d98104d40e0302004194006694076180052880100d0622005c83c0301d02641a00c0900b208409030044c6041f107100c06480034045046c1d14010a40c2c8603545414200d800c5e50042c0a0800a0701c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 570738453 1250 570737203 570737221
    0x90f080d0b1216060201090503091014131815050f0d050109060207170c0c100314090f0f0d020a0f06020f030906071706240405060a09140102010b1c020f0603 69
    0x342d10f05100e0090504000700285443c014080c03151030607170001c040c0d8248030b110010b00541c0f2100b100c00d0750401c11780d41034181c03039100c80000030010001d0040c00d0000c2d00e030905040d884550406904803141038605400c000950392202150004c1d603038201c410006031009080018109030042e140a003065182014030030801640e54020245e40c0d116030040540004480b0103840388d4000c065144000f604000d2408810b447c00c0c02c2c221690340900c1c240000e001c1c2c030a0051545000c0d045818800903400507007424844513003002107090141c1a00010325190005080c02900e500011200070200c031b1314100440d0400a884c0c056681c82d20000646d50b80b80c1c42c102c100213075159000e803002c0d00496143c400c210008115990320394824480500314011450301c4841031290071700c2c0740703403019030790700d401d21002c034140d600c0c1c200800c169645075450100143c20070b1402c0c3c0c5030001d010459815a031522014241a0300c1e004815042554072100c8080c208006001040103559030f1310b036055000b4000070400c88044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 570739703 1250 570738453 570738463
    0xa0c030f02040e0415090c090506010219110a090c050913140c130b030c0a0e2e0311040807120615060518010206010605090d05010b030d020f10090f080d0b12 69
    0x580a00b282d504800781800c845c604844400e01c01401d61260407009000e43d220581003035402c004107204451446c141102c00d49182e091103c3c0888240300400c16500366484c004840c0005441c1800081042c0c8c8120344001d80107100714036102d030040c50150500d003440d04c11a4030517041040010241d24140c500b005180c1240e51025120700b201c00407100011a42003020b1003683d01c598030440e482c17807800d0b81c960010b132546400301550301e030f00941c0d0001c0c0ca02c944850b0f4a0062034122a003249416209034140e024040c0c0b182c2c100d0803c0c0141c02231000704912030000030702c0000c41e50704462002c050350349410102c016080b003600080c101c5c0040d4100040a030713802801488070a040304440000c0f1101140120b0703c4100a1080e0350000b030080c4a2400c2d280b41460740108140d10070400019903420340c0c0301280c1410043c1d440000940c100e813141e218002001d00214107414002d02040000d0388955603051240401c081003d0410300b00800e540c201c01e50954011107010000420103c0b60b008105503481d41e80e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 570740953 1250 570739703 570739711
    0x60603030f090b0a050d0b040e0d0e0102010b0603090a0809011701060801050f04050412180503010f0c08130f06020f041211010f0302070b060906150c030304020103051005090a0c030f02040e 83
    0x82c40810001032200e1402e0503240f42041e250340f840d1614032003404101c00b8001e0400510f178480d590740804000d00404000342c400400c065100c0c1074803103010400190131110901060350080d4010810001c2c1c00c540441c030780340340ca0380c07004600c1d481d00c20650048034210400f080d0156040c1640001180080c0c009100e07604075001121480c440300214803d000a03200180c0340100018121250007001038002c0b11072140d4485000060b000345030f0b951000a0940e0f591b04810109240e560061010031603002c205194032000d51951000d03000041c3c0e6503080034480300000941025400301341504440c14440031500102000518090030130740740c1c02d009140d00049940140030800c0202c108031094024020783d00c004e604440d4a910340c2c0d451005015580200070700265011a403800355080c0368a030000908080000c0c0740c003c688901e010310000d801c40c2c202410070f0040c09000c540801003035076100d60b0540d00404210000c540e041204c0b074150050301e00d98928615103030010a000c222032040042c802e100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 570742203 1250 570740953 570740957
    0x30c0a0803030604021e070c1a2a1906050133030e03130e090f0d0917011407080a0507020a020d020402070302011b030c0e0a050307030b090a1a01140103050f130f060603030f 76
    0x842400281c50429204840c41c006240000c02b135080e00c070340300c0101007003c0144a1400d0b9207400c2c0030501420f81000da0480300b103490540c0d460040c8441d83c40780f9455580400c025044209840000110400c05108142d801082646407589103950030f0040c01a54801060032410314903085c0c6821200150b003004507079040c060320a240c081e0700e80c40f40000304034610307003000d8403070004080c103000c800300c01000d150708520150742d00d136445000c3c03c1c0c0c01c46800340d108080720395800085060921450007903400203049041194014140940944c0c1ea096403c6a0789a044400596650103441c1c00e07405020030203480c0d4000031482040c41d0342c858051300075120b004005ea40d1490315658490410081d11100e010703903030705070340300c4c0805100040c1804503040d04000760400301c404424040c0d03a1909000f0034102030040107680080104440a5540d02c070026030102403c080c07100e46088a1102c0c00410000c6c51410b10100001041d0244000140a03250240c0c1142050000a40342c0c1400303480c000fa1403c2241c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 570743453 1250 570742203 570742229
    0x40f0504060e0d090b0d020705060708010f0f0302030c0108091606180f030c09050c0c0d230915130806090105150303040b03010b0f0405120705030c0a0803030604021e070c 75
    0x20000004100400c0b0200a0784075002e100303081171a5102c064220040d1040700d00d5081040d100464001c000d2203100701e44e5603407040510f42c10400c501540d504540d01010441d01020f01c1070005030741c003094078150000300307181c1040c043e070782d0059151500651005541800402c070802044050f8403108800c0030150021200d51b04507600c000124511000d4403000c0c0c40502e568009000600d0305070440c035000b20044a2140c140352109015030708017052086181c011034020416902d5520803060380700500440088024100741c0081c01064a4000340c80d1000d12250300050b040ea203d00c420b540520142400c0703000ca404900d840c1940500070324013034a10320720800994112851600d000400c850a83e4001c101e0641540d04c0c0c1014503541d50449507042004080c00d000c04500b07070300e548900c0800c046c2d1201c000c290985c580301c01e040c1040c80c1021150b004e03e20214003480105400401c594020b0f034155001030f9100780514414420360680344c00c1c90601310700020044144529424608141e52146942034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 570744703 1250 570743453 570743471
    0x30c08072d030c0f0203011b09050406090b010219030219060b0a141e0117070c03080f060612151f08010e04121b0b0907090f02210c0702040f050406 65
    0x34501d40c0800140000c01203c2c900d40000c842100c5200c20b24809800458101604083c03100c03800010f5018500080f45400700300010314090080c4001040200c40c00c1103107003c8003000075110740d4a00c0300c101d100001703e080070003014804c01a90054000301a40180580014540701c005090300701005442024860004035040d2042d00d1082e4500d600189148a00603101280203400d0144d0300189051200440088890320a020071030b9115603c0f940e22071031001c0aa1901800c408009080886c00c450706008002d1329499001c11521070004000c01c0b001c0603a5011031a103411594412100d80101e400e80302141070403030901c000204891503403142c0b0444d030780310004030008110880c1c1c01382120404a080500aa015040e406074420051085014050460b2070780383d030900303043d141101203601401d0100032455407481001451030880c0310552034040300546540c40320900c02c6030141c0c44041c1002180c250007903001151029540500284203000c510010840102401c030340c2a2201c3d0f05250b001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 570745953 1250 570744703 570744773
    0x1020c1608070e181c110a03140708161a13030509060a0e210c06160320011a0906010c02030607050d09080310050a0803120a020304030c0807 62
    0x2410303248403100074005289050007a00e40030300042c2030342d400800c0d404503043c24043e00303100ea0310307084403815908003030038040c00ca001b040b415001003c02115040755003048006030b8400303005105c8100360700d409522854036051952181c4155030580c3e01c0103000301c07410010854400d00010301c4001d201c0d40722140341d0f1803e5401c5e18441070382d000227000400400045029140c14006060b032b0382c1083c40d204041d061500c000c01d241741070b0f41e041c00c5c00c44404c04010b0b0408520401580ca007082d01620300733504004445000c282d1020701040000c0a1041425401c0c410055000c1d1050031440c0d010000d0024400d0070090740e40900c00c1e600c040d401030700010009191540107000544200e64007500518513999001d04c1103c941d00001210f0520b03a07160000d82001ca4038007400385001b0003503a0322040a5501d0314003040ba642d021580455407641042c0041e400c004000c5095545c001c500c40009a031342c1d46c1d01d29048651a200c0c81d80108080008110507080c0294052050088640e490742500403054880403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 570747203 1250 570745953 570745993
    0x604080f0706110706050d021e13030b0903090906040b0d0507030b150a051f032c010b180a0c140c0f0115270902060301030b07080c161b0f060201020c 66
    0x501021403c101f007007048030944c13a401014007503854000c0d05540305019000c2d06450307000305c0110001c2d6000030030500c00c1c451a80611500007141c0030007146040864804202d02e2400100720a100c3c0d5510320207071302580c07034481d08906c02940c40030545100076182e00e40120700ca14161340d40d45410903003500c41001c60902058007001e032000144129036004a07584c1c4e120700c20038021045410162924000c1c9401c0f21800140004249003404400e410a0118122400c43d00c030b6000c000d11030566028003100981060355030a40103801103074045020000d0b404281c076005102c1c1c6100790070a1001031400d90480001c54001d480c80400002442410844c41080c1c00001076801410b0034034640c0740703000c03d80000c04c5019001c0080031400200308940030344c00003400794100f6032081c1d40011480040020450303104450651103004800398034244078141c4241e99820800309002043c04403103211a09648614400110041c2241c4051185c3e003a120f510003030117074010013005840da01c0b615a901c000041e502c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 570748453 1250 570747203 570747209
    0x30318060912120e09010f0302031c20030408060a050411012102091f03231b07050f07140112091109040206040f0311090606030f01060e0604080f07061107 68
    0x1d0b5540c00c204540310b8100814030000c034001440100e04a1001c00e4490071455070090150100c10208a4030b180141400c0c4007080c0c0c440c540303008100014403401030708040d0320300710032100107140d00c81281c10750142840c52040760030032680341c0300e0b0700100300302e6032440e400c0248075501c0f1b18441e0504801c41001910451002425141d000b490b101c51400c080c2401e9014042981004200c1400500f10f02c000090400c0749003140700c00a91102c04a126403001441c0d0481d1034450305a90051614100314540084058880ba1024208001400c0300c01d000003000050b072410012000c0d100c2c89640c446030703d000b46d45a91001400309200741c0300140300703c2182c4100340d0b006420241e83d003002e041203401c0190447c070041049901007002d010201e2400c4250030600003851140550b0050010008104000c1000042c8503901c191000c008010300361400504013411607900c0d00304030403405511400599240226045010644103c2c100c2e042181c00c0040d404049070680d4484a22030740944c0d01c881d48412840c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 570749703 1250 570748453 570748469
    0x7020906040506040b1201050108150103050d050304080702041407030e0d0e0d0c030f0501060603060b09030319050c0f0303040605161e09033e03120304050a0c0303180609 75
    0x800096900e041035001180d004100600000f565499a000120b00030005a0000150f03075590700180041d4408010040b0841c07942c141e00400c0b50315542d45d055035401a141d03444100100400414100455002170342c100650003003040c00350a2240d81101d21b00c02d41100c2000c0000d0500d5030a0000c0080032504101078101ca5941c08106061501400131a028841044130006c100b0b18000000c40c041c209212a0300d480344c3d0000c200140b0308000101916034540140c400240c0802514540780d5002044a8113103000100e114240c3c20301d003005854078003a580561405d8094014009030b40d040c0800103520840c410f0030200450b0f2504000010b401d8111006000400d00680340c85100090107811000c05407098030b8a07000841c5c49031740700041e9009426a076070031000182c00e08400200501c0500e8020244400b0415001d501400000d07900d03940040a0f1220705400808201840818882c0d4508160454008040f031550b03072900030098141c500c82c2592100c00600e0204502d449003050404030703160f034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 570750953 1250 570749703 570749719
    0x190b040504180b090703140304060c20060c030a140903030702090a151401110105070f0521100e0a0204030807150219050c0f0c0607080c0709050103150e01020702 71
    0x3000c18803000740212200321890780000000c01c00000c0202c1240342c4520356820240850601c0d61800c0113108079458504821070308280b1040c070160780c0c08100340c1580d40d00300380b940201c0b02c094284032501c480601d00c4c00e9017007600040d8155526200000a207030b2041c442e9684125071b494545046400d0007201e41103a4180c00802040001d0306e4003103402e6802c00e4048000042c2c6001c1c0c00c145503da11001d500100c01280030840005856811182c00801c29460100a11841c40d01400040940000b010003406001c07020800e040d0402d82d140300000700c4100042c1100f22400c20207034840000186100d54454141c640340090200d041030f000340c600320390707000d0041810320881d84d0712090300c4524045681e1403143e00307021400004840d226444103020701ca0f01c515030398205040b0180d040030400750207618a6407100c8080481a00c8600850300c040b600030342c0407511030106c540c11302c1c02c0c00e4895002c1181e079030401001105120124441170040e900c1031070300f0030010b521407034910f090380600300003c1e40c400c601d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 570752203 1250 570750953 570750959
    0x10603081608040905090c01090806070f0f051204060e06071d061605061015030b0114030402031c1206140117040204020d020d02131202060304080c0106050604090902190b04 76
    0x2001038448401e03200b8410542801d481d10a202c0440b00102e030000300981c0419400940d951b0881e1002c00035002c150060400d604c0c003003002a2426800705450350030000c180201d413010511031000d40e410780e100c02c078640c1038074241800c00102504a00e148500540201000b00308510b028648001d0701c07003002150701c0c081e803150a08102c181d03007205107031881000340f901502c0002081030001c0d512a6110001018000341072402011146406a182405051030140307120896a049404010f440c1e029600312070b80ea581e64030110b0308001007801c01c20a88490740030108420354028103030002818007424204241d41e60355809018402a000c0d01d1808551011003c01055a6003910641d125002500241ca4440c01c5e0001c8030483c1e10000e0f00d940700702d501040d48140400135100401c014440d6110549011007143c00142043c840900002c010701d00c0000e00d0880303040d0039003103800148402410306481d190f907200311102030160007030224825490000ba10425641000e6400c0c180c802c03400c0d5175030416003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 570753453 1250 570752203 570752227
    0x70e100e010b090a0302060c0604060c090b04291225050901030c02120c0d030e060906160905030114010e0a050f0601030c0203041a04170316060507110604050304080f01060308 77
    0x2000814060f000700745004040056100c403070013008808c01c010020324141c80c01e4207205013120b40f122200010003040b03a40400c115540ba5060b13070140c58040513041408a1031000100000003c1280d11016400c00304501515030328142000744120308862207440e540303141d0fa030f044e444040100200008070302e080c0000d13001940303e40d01c4004c2c110a280100c4241c00f11500500c012900700c40c80c401555403000b00458501541030045010320309500d00104090308262501d01c1c0c846038000c29061584466100c0412800c5c41f1382209030042101030300812007018180002130042d4400d0007000c07070941c0314001290030b824162242a104070f412400c00746007a04d87c100114003400c4010a1801148170610012610307041c0c0c400c0c4540c020004054103582e641c0380107200b1a0001c8000c8055105410030f0101060013551400324681c0140d0203480001c00c0c6c1d0385c440080d60940c6c44240550030358402c2408220405c000000103005448000040f22107042803035034804e090b20a607000c01812002c0a00290103500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 570754703 1250 570753453 570753457
    0x2b020a02151e2d090a0902041715060108040c030c0f0927020f03011e020d0b06042306040b120906060d0f0209150613090b012a050f030c070e100e010b 66
    0x40e0400a0240f0f084c00700380006448200542003001c4066000408000c240520904c00041451781c20141442c03483c40b8400680410004040071b0510180c0301c00903007000300d0aa1205d000d164441903e10103141c444030a02812500c074000e12101c9032a1042061151241c00907074581e140a490504101c4020b036400e1041c0c0c402c0340d0301c44903050343d2202011100d0000040751711210703900700d0380016124000343c000d000c06c0c1c544041140d4011641003000740159840071041103040501002100409548000415964031803903010914600011884c940d14040c82d072a02409049101c00301c1d200d64641901304201054070443c0100ba0208040b00d91005003482024258043c0d8000f1004410f40c020034045a241d41c08001c030030401c13100201050004000910130b8034940b0341c0a1900c4c2801414030039008104a0302000c22108010040d40004100041000711075403203c0d04e602540c0d25400803840003652001c29008180c0094107800005440022070700e103107003c0300c8480c2400369250b4030f8038510031096 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 570755953 1250 570754703 570754777
    0x10b0903100b040209030307031725030203060616110112020c030a030905010b090103050d0f030b0a0308071b090218040b0d020d110607080a020606032b020a02151e 72
    0x5400b404007007907030351b020f02c0901207143c0a9221150303040708452900c03005440042c290101c26003000010b282c0c1141501d54201d410190303040c0107079030740c4444000510394081c1855000442032050810001c10035502070003a0640004e0301c5182c0003080f0818860180d0145078808017003680180020714601d4404d40100b01d003d806a8000107256100c2d42c00324542007000d0b0010384080d4040031003403031150351003501c802c5220b4107071038108005142040020f56034045844087c0284201041c1e24041c00304035000941c14149a2601c43c511503619512480a5085034100089803503064540395040e0419005c0d040e40100f00404200c1403c0c010707803c2021032075030b80d0000c2e6052034551034445869103894005050240c064000e154503540c84000c000e1a084008184d42d00942140b01103402104804180070341c441d02165a02c00300805101c0c0480c98280500e9029501c03400c1c0f40e5507581e101007010014074403d8070600d41c9030380c4241003101c0d00201d44220b40c01c03241c000d207410007201c403901c0003018900d1003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 570757203 1250 570755953 570755959
    0x150e10030c030f05070503161d27091e010213030204050c071718040b0112021b030f090102120a080c181905190605033615010b0903100b 60
    0x141c22840b01c8010448408a5428006c240d0020074810181c101548401034503049142a03044068100300c42d81805a890002c94043e8003413440440045480800140c031b980c02c030a90040c041d10305081d50580e96400f80d989030601d0406200d1840310041c040c000c42d4264001d034032f00508071501d180d0900c03000b070200502d045600c8405001103000030b0512580c501da403914403101280c680e40a44180082c1c0f03907503095020300c9580b40203003074502641c0046800c140b81c0c8145000580f80c00c0344850b800c8136040700d43c8445945000c0003a1031081011300801525111000380e080f50400030405110b07440c544100b100309000309090900188080024900518406030000307000070007925054017103a10100d400b24035041c42400004248590700341200d0b81d160740711490450645091400300058242c1c440600306401c01c1c8800302c0050005160079504480000031411101d01004030b1400894036000010102280e40d4a0b8900000d00300d10207100340d0381c03400c0f8014058010300d40d55009103401407e950345102e0f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 570758453 1250 570757203 570757211
    0x5070c0509070e0325050a0320040b040c020313301a0c071202010605130b04090f0f0312110a030c180906030c1203020607110f0304030c150e10030c03 66
    0x751002c5c041c0c54484122003901804a80800101d0031080304290030550144524000c10004200300d81c5482c5000110300b42c00202529440f004280940007658080f90804e05060780c0e920681c0d8000700030b00301030020422861900e03442e003458440c0c241c045010803c81d02142e149101203440f4080e6508000c1317100d036042000e2603a4240e41c01c0342d50801252002c007420340105003041840300c10b030b0400c5c0d610f1070184002c2020f60b08010001d18008a41032640485a40c6e8100d500096100c980c0602c140c150040420b000103e5586418081990349460450002e0600400561144cc190255543d000580b04441741080c00c100c400300c00506080c01c2c03040c100441c1c3c842e0030780c01c483c42c0495940586402c000105e5518214141590480e016a003c011011103d001d0800403035400b04038950450041d00d40503100c2c04000c40e03003c1c40d280171704002c000d40d4040028000200001d05400d0412501000782d8800101d02507102503500c040c030440c1c5503422141d5020086104c074401da000a40c1d41c201410001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 570759703 1250 570758453 570758477
    0x1518031101060e012706051e0303070b130203070e011a0d020d1131031433070806010804063204030306120f02040c1106090601060e0105070c050907 65
    0x5000f200303a00003100c0030b14541c684034005044c52001540d003002040c040c04028a444003085c0540309080291207045118058aa07040d901801118a007680001115030f030741c285030509159059406900324403d100f10f2031b0001c2c418001c9650325049445408101c40d0603a061070071003250341d010781c00c0ea00d04aa4200034504034503010703108480a59008004680d100c0a00c1c20314820030030304590000b03030b680d21400743c2c0340088034149422506590b032118089070b4450885c03841d43d1a08988070342c414980014031b45c0100501c940e44416a0074000d0041c142c04441c0c89543e0150344045050f00c5503400034400d1400203010640c9500030758025407450094520030038003040902085508004811081e188000904c81407603894007900020f4581d0800304200065213070703110070346107110703880090140e901d441c0e110aa450041900c1101103034014190351041c60444012602c0e52024025800440e60542c50740506511483c142c0e41d5450f480030b1207080c1941005d0800c060703800f004061004200d0514035203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 570760953 1250 570759703 570759719
    0x10f050d050307032a0b0f011e05060901032009090106081311152a010b01020a1101050d050f1803032205030903030406020303070809010903050f070c05031207151803110106 76
    0x505c050a0183d00651040d051091894602c0304040c3e000800d40d60a88071281035488808080e601100c100300e6038203644000c0381005802400d00c1c0e00c20700c06488400c00034041c484400c20700034800355400701d6800c00d07260b8891030140c441304400e81d889175640943e0b10398003002400c0c40c4071401100300c000b440d1082440c031468840130940d002100c003001a0900d005010050242220348205c041c0e04640280702c03007091000000c3d035811400a000d01094000151a40705034041c44c11280b91110142060001e441c2454050f90008004c0c0c400c8060220150074046a80c00c01005413401a50b06a5440c5111168400407003084601c19405480e81d0000300088089664100000c0c0024280b940285813030b458480d201400401d001400340c0c0060341406480400030340d01a040f10000c80c4500701c440c1e02c5030901c0c284502010041d070403240e058410b07000752850f00704c401c03009416018810032032440c402c040704012000b501c00416011006203100b4500200007800f40c9064201d450320100006101d0b69200e1003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 570762203 1250 570760953 570761027
    0x30518040c030f14130b150301020f0405120109030905060a0516030306080f0708150705070f2001051204080304051c030507262706040803010f050d05030703 69
    0x7007800803075624164085120124080c6402c04400425445024078040321010b800d8500d800c40200142045400509404080030002e4112000034000b1034031800104210b40d6258024002c40d84503441100b50310303207044014001c030007080e6403640d58052020b2a010500c080764000007a442d0a00009200075421800c1e0111681c881da0700a07a030101c0e080386413003810740c28070044450000e01034021000c18030180e8000614207440a000c0c0c483e40d01c55a84da01011a07241c002c5039001018403003a1032522013444120f00043c4c0c80d054190071030350100304a40c0015a86840b40301004c480d600030b1000044c0228010304007440e4842d001e1000c0e40c0c406248018121400c0c1e691054400c0860354503402d00c100c031988025050f140310004e8101030060b0260080d14201d51100600748180c0540c030380f80502203d540824540310403183d081c2100c006080601d040e4103541c00074010b80c8040413980c000061107160403030f624218150400301644c80c1404a0300d04031000300034000c070303641c85600c0390002607408580300344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 570763453 1250 570762203 570762221
    0x12080136060515090f0d0321090b070305090c0a1d0c16050307050d1115041407090605040b040b010804200d050d030b1f0c14070e010303030e01050c0703051804 70
    0x107003e50307072250124104a20510010b0b181c0c5c1c003c0d031350061200e0000c2c0d0006180011a03040440c501c0714500c641032103601500320001c0052086450805106003075415400440c0200c03602002c3d20030005a0b07070300f8001840800e01c9590b15039000029a41402c03014244416001001001001e1031308203551001319001c40d003000c08450540c40002c6030b01c1800418000c0c80b9160855190100e007207140041001da80340612008500c0ca0340e440c10108040115010151444001c84004c0d2001c542c0d48000d120000d206510420f03020b103003810501507040c41c0c6441801840c0310305071208100d86d26036454041403440c0500900b201641c1394101d6001682e9003036504081d552050004007240071020342c0040581d141184424015000074841e01c403c2640150042d6802d01903140c2140e41c80003d05010f00340700c0760503d90003801c0c091b007140030800200f0b00661744e050701e00079201400700c803001c070030014202c0e00b0440d48c0001c40d01e014046140042c1c130442c000c1070b0580300c080c0b000c0d01400380303900028101c614043d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 570764703 1250 570763453 570763489
    0x20d060b250f020909100c120506181807053a0c1503110703030902090f0f010506090111011e1401030206120403170103120801360605 59
    0x20618100300440348510000728007180400d004000000c0d0b071070040b100068a4024440c00038900001e00448082040800e50f80700e1000038010301c07040d1407010307005850704644643d5007402d02c2d0004140341011006094254681846840c180d40d90f50361801590384c80818000080c000c10310005a40d60710f1240d010380519190b4100c01085009045009602107071072182840c0005107801d40b80800d0100c07483d80200c0300d0074190103018a44d9100d0440c0100358080c441100040081116000d065140d40b00142291003601c0c42c907500c0d102c25020041411080318243c2d8030a91420041c0110b00300f1038007403d0b5202040c10440841443c03500789600b519030440c07105130508100d21880707207100114000c072130b000c0260b07103003090701c650458010580a01c20750300380101c130009050108003054850b500c185611140780c060410b035561a4500303241901c40d9a110f03900001c1180d400440c1500703090340560b090505209013064410b08a02307600040399441500725645c48da41c0c001c001031584822040da071120b4110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 570765953 1250 570764703 570764707
    0xa05120915030c190806030a0201081b0304050a06050f040b0129210c0703050405040b21070303020c0108152e080405150402010206010306051906030b04060b121f020d060b 75
    0x2401d41c1c031100707002034131410042180b050309000c0e4645003c43d484144680a10340350079a55a0f840c588a0044080c05143d111902e00004200900102282a2444602c50b100500c025102c0102452020b60140c1d40500a025460010050100c02c1c640d81040e410000030391000c0c08844030350801c0c058104400740d04280801e0038510080b0350031f102c1440d604c0790030322018906107030240e14020f103240102d001da94040c59a076505c1c80c0946e900c0080d24450407542c0a11400751451203400c1c00c0d2502030600c8120090720500b6440101036000351000351081d207400001200c030b06c3c980c200304041c507528400e25902c0c0c2400c1500b1055080d220008030481d050301a2142c8070141020f02e0170030328000e0340c001c03900c00e00840901408010703a07011803400e04694001741d0108840e156088011740c10003000180200152605000004000901465501c1280200e40410515840c0c0c0c05001c0c00701c1c281e0b81440310b00e42111810340d0b400340f001e545c2855071000c0b050f4011f00705a14065010304030f0740950400004900c0c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 570767203 1250 570765953 570765967
    0xd0302030702010908061e0c0c010204081b06041410030b100f1103030708010611120706050406150506041203090312020c09070f050f07030c0b01060e03010c020a05120915030c 77
    0x8049058005d004940c024480ba151041d602c040c3c124940b5040c001c000080c41c003140d00005000295044c11503040021503540c2c0d6680d040c2943d5500070350101e003498500c0c0b00484440e2034400b0546044400700941c00010142801c1044039101c984c241d04000e140c0c0e100d00341c8440c1d4940d00c404041482c4152901428a00e24030009048103425028848656004004020341d46510026990468401e41485c4500000d0404c440d802c02c2020500d140300c102d40440c06d081070005030f4000b070340140e00400023045600a03000400c2d820070080e008440c0c010904100421441c5159010108000d000b80b5040c0f10440d01c030754a40b0001103400708514011380c48841c18800b01e01c0c00012182e0031000030306140c030702d080c615000034001d4000e401d02c2e115880004240c1d042410701030201002401d911402c1c0c05103c0d0703143c0710702a00d12841004603a00039840c198202a0309400043e01d075202030780143c010140701e06010880c400f030768021041c0c00d030011003c0390140026141c0c000510b00030200010740c643c543c92 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 570768453 1250 570767203 570767207
    0xc09020421020307140d1209050f030109051f0e03070b0105040c050a02151009020c011b0509181f0312021b1810050a060e040e0c06030a0e0c0d030203070201 69
    0x2000100c58000e044404410740010303640010154101e4004403c02d02042030048002581d182041c840a01000500c840c030514041d441701c040001e80c1d0048841c032142c00740030028907080b6202070701d0080256210742ca21410001c1c0452410340304000c1110301181c80031400700305030304540080808449407a403420042c8203070718150240e00c03400c07515403401c00d0520384070400081d9a0303852a0b00c2c01c01d1810740c00c408594a41040c20b08000901170f1205d041d55940d00e05100c681c020300b0003100405500600704010b50b0300502c241c00b03c5140001c000c1c107012100e01555000e8480c92800742030f2403107a40c0380f0340f101d51003910711600d40001140660005c2080001c441c00103402c085010744480341c3d00c901c2600000c01545c400c0020701c00041040e94041c42982d0703980300c002022030203410050740300410072070010b0065400004401d030104203844c140324408030084600c0e40c0e6400c0500259100c039007400000d0402006502c00c00150140030110703070118219a010800c0d940c064482900180c00000e41c09095517 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 570769703 1250 570768453 570768479
    0x706021507030e03070b0a0b04331a0c0709090c030311031e09010c060e0703061b0903030507050322080c0306071e1107091b030506010e060c0a0c090204 67
    0x2840c0b82014050044114641a12441000300c000e048600e0240030481403060707903000d503460702130117403080101170310115154454042d000f03050021000300c6603104801c2c1c80355040030411560420030a0903107022042e02030215410a001000151050a80009158010380038443c51280074203900701441c2d080d13040c0184203904132801d0759000c0d481044508400e444003ca141c101c080c0f5540a142c8071070b400001244c0440c42d004000e0b014a040180c1c818005501207000012203120f080100075100344007055582e03001c035841000002c1079445404001003802203006107485445142513030714001d2072281000d01100c2c440f001407100c510800090000c3e0702c00300700302198503c044004041d545000d0310002d241000300040d0805d264101b96841d14a980200d085090088a0806907103200d92520036100041c461107009065104900c410158107900900c1003500548069640d1461500008140040e42d4481c00e00b003211849420110b40c0442c018550040180603610f00242ea03551500c0d501040c42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 570770953 1250 570769703 570769711
    0x70921020906042408100c08040b04031103120906040c05030c10111e1c08090a1b0e0411120712120e060708040302030105010e0c0d0b1207060215 64
    0x48122460010269440d070703140903880b400882d40820040d5450345603101d00b10300e0111680c02000c6030440404e0b02c0c0c2c0007180a540c3c140c40d608081100c005000c1c01190300803000e031400b6107100c0036200070a010910405207141f844d00610212864a03d00b1484281084011240746020b50414030502080080e102082d01c0208801c80080c1070080311040010f00d607100b40c444000a0090456612510040c24081e41d024101d088000c180c1c41244550700325100c0c40c004038000d9512006101125645000310301c0a4020000c00700201001c291654400f00780d0b804803001d4203000002a000002c40010b00d400c0c061207140b042d0060700c820503c482c140300a2240c0d02c0c40c0d80c811a0805a01404031490380d07004801c096411089407000080100d0058540110300c03032080c1d410010010f50710040c040454000c00c03c5030301c2035008209036030740c400c0000d01015051b6090208003804002c40c43d541c6105e50000b01d1038117002880707140d541c02c0c00c0071801e00d0701540e03501040143c1c120240140541880000185d40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 570772203 1250 570770953 570770999
    0x90c080f010612240e010302091e0a0c090e011410021b1504030503070b090705040204050609010806032b1b1101110109021509030c040c0e0f0607020402030709 70
    0x20310350404a024001030160000c2c0304035250784000d0550043c8401ca2520104103400f10035038142512900c08030108002404160b00605c4004003041049201c82c0348a0140001d803501c64841da2110582c010142200b18030030f00410624800101c0d241002140a0303008003402c0301d5090b00f814001041c4242c01b40c0a820001c203542065681d180c50321505c248582c01c07140111480320080c1c026050310b9a80d0300a41d08040e000e0b106c0402d10748100300c00800201d024030703420300c1200c11141e5503508000c207034810790148507003011082c0f00d0342900e54013503011281c110000505a900381100c000c3c10303d0b00000889028064a25885411002c2e181c01c01f01c1003c1070300c4800503644030505140c07a628030700300c055000030341045541e0960018100c0c00790f100e100c030661f0003800c070300315007444140031a0540c02040341c181c4030b400f1300e920307520300b070300d071a02c1450366094040d2107601c2031900b540200304d18107020782c031030340d030403a208103e200300580e1544019440791040740c90300c1200301d0400480410700c2408220040d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 570773453 1250 570772203 570772231
    0xe011406090c070c0f0f05030f0d02030a120b0312091c2a0f0f0e1501080c03070c020d080c0c2202160f030c03030b01090e0f040219090c08 61
    0x495500d80800040e4882d211126140e43e80c4a40d207403a0b030060000d03034481d451104030004042200c0c044403251004a80048049429440d03076040c0480c2c84010300c440310000b59004002c802d410300d0140f02011306e0307a840341900080005d40c07600464249140b200311103504000005040d0340b1890030801d00c401c00c04070724040010a0100380d58001074071005000c80340804240312071400713001407c040010003411011041714a0303180d4412182e101820720307014009421503600c0c0014032034400b100c20641c1c0158141c0d615907081d140c0384500700c0130390300180002c01042501c00b0140f000d80c076003c003000c10140c850a0343c15941c401d07402c0030f0b50030010024078003407088007442e5074000c10b03d8000102c1c20034034562000040e80d40480440d00082119403180051401c0c2c00b02e42070170300389500003034036041c4103010752000d02c0311300c444e20300454481200e030058254100e6064040b54a98080005e1190300034409401e680c00324140014043c0c4541c40e0380d12903000b540e00c03035000e030800d251b02032202c9400c00705881142c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 570774703 1250 570773453 570773461
    0x30f03060f050a03021e030d020304030302010c211a031603060e07030b1807050a15080601050301081b150f04080d0e0607020415091e0b030c10050a120204090e0114 72
    0x30480342113403001a1040d03000c442415582d6007203010301b40341c2c21001022224a000180b001039280e1b08140b01c1680175500c1e21081500d07442c0229581c866440043e074003400042810502d2500a00c0304030b07503501824030569190100c60301d0403c256070703000c60078111950041c0c4c81e6240842c00d45540341280c00361508007007000c1000420710000075801181c0b20b40d240d42c41428071035841d460810142e109540c0038803da0070000304810070f021415036281441c0d036500e58076518200103441601c000c0c840d001e4694806c0300182d01401b44050002051080100107001e030b10181c01f0064050341004007414940038001074100031510b030030851803142a0039410071000a902210000b40e44d401004006030085071030301004c82c001c000c5541c1d1007001d400c1329101044003401c2028105040c8800700c02c1c5a1a492a01d550300d0841d01c1c00184044a600c0003d105486884002c1c00846564010a4180d0305011030001c00903400303d6280041c0c80a404010000076803045d02030726403030946d40141850950380b85080d00740 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 570775953 1250 570774703 570774709
    0x9010b2b1e023603010c1e0c05100e1218090a060506030105040b0d050a0b16142a0d021501060305040b06091306051f06080c030f04020409050604030f03060f05 70
    0x14031007000d20418468105500300f00342c0f0601201140c41c82d41540390040046010340c110303005590113240d144070490b564000907400d0301d4080020348040e00640c0321b0060070740344541d02d8101c0c50700e5104050942d440707581682482c4816070811403280580e040210001e000c641001100703681e01512402081c46018540400300300e6510060045900450300c0c0c075400c9605485000001ca203866100d41241c0c1c4c0c0c0d2200b0f0900100444040e20648030740f50290440c0d0010034450240c900e400580344507003d103003050507002c40300e000c11450030a20b1212282c0400000c203080501200d5600015500580200c516a241c05495880140c0008081c035103040c040c0b002050403000c810b68888000c1e54100e0060325140c07400701c400aa02d42005140c141071600300104411762040500007400000d00c8600010345415069070360700000c40d5a0740a225090000490480c1b0312408580c1080c009440010840300300c0e1540c0c3e0400c00221000d50100744d80c54041d207811030f41445988010014a280c05000b18189800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 570777203 1250 570775953 570775987
    0x1020f031e09010309080a110c0103020903031204020d0f050a17070f1101031523060c0d0f0905060429090a0303080411060a021e070509010b2b1e02 65
    0x740081d0000c10701c0b26060340694007035446150000c4100b515401c0000c0010090b40c0d620b12041aa402000e40c40d103030550080c02521040701005000d54144150001d5816030404020002d0740d12000c1c103815100454009025a00454060000f81800c8412414200442a410030385081e803444200280000703e4840e030245090280d001031540b9807203003070000490107400c82d408092048000c15000203100e0740707aa03c20071441c42804001b007449000440401591740201d2915004c030380c00000b0011040f40c8100307915600035200781072407007966449201003001c0f90003503048406d55000898480e5041c40c1d40c003003007160b6041111115450107141d480400c2c1054031510009083c040b400c0049410403d1200055150b120003509443e15401c10b688000c2d50742400c40341e1000c2e14035000c02c105020f03410228000782583d0300a00000c1701640382040c10301c202d50154492006042c4990b0003962584011440b07152000701e050030200f12200009862110350030414200344d11140704000c08e6400c4000c3c56a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 570778453 1250 570777203 570777247
    0xa140403170f130f05072c160e060f0d02070606091803050f0f090d0c150c050a0305030c070c0e01050f011812141002041a03060d060c2c01020f03 64
    0x21218011380c6842c000c3d19211103501700303c0501e000c5120064443d0050b0140e0b001c0e0040c0090401c0e07681d122210f030070740079554a40c002e0001030400c050000070760030071034020044803003090b040d946007a049008034070481c1c000d1901291040c0e200c0c04200140d1031a401078810380e038039030862580700040da590060228803460301002545003000c540358144102010a80b2606a80a0103035095070300c96141880b02400c41e07020711a2480c0308a0343c0c00c3d116520403240c1160840d8030000400400701591815152500f0041c032a00508404015140000c0d181c40400c2004203d8100b620782194102001c01904030314980071141040a540b915001d00201c400c000c108807040c5c54182c0352903a0070b90414940d00881c403002e01429204100c40400ac01ea00346d40148102d90610500602d02c2a1100c0100094402602c001c0d5020b842d80d1000c5012a01660160f4480300c0e8a0a003004c0840d40040d2803c0900c0d240928840940c01c1c5c00b801c90010358040c04000c0c28002c061014600e4038440003500390010034a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 570779703 1250 570778453 570778463
    0x60e1608060301110d0c08130c0605071e060b0306070318021e06030906070e100f12021605031c0c0f0e06120a0203060f09010501020a0b0a140403170f13 67
    0x8600a501c003075226204c9100710355460303540d50702e5580c5404040c00480211000050341200021002142d0340040c1100b65030100b03444c51302d03d240800c103c4598200f9001500d6034a9a50204c907010a42d04103410101e034480c01d80484c0600c20384003007609100c0001d28030018142000c0d0111407000b4514030441314682d045500c106901c9940c81510100090841c059070044400003d01648050018070a0300c034078002d076651140c01c03c045087c8080c41084061070f03404214880000b50f58030380203a401c50507000a1080c01402c12040e10b0a00300004440001519140c00010784408138240e04154104900c003003407028080514141c1000f0298003030305e01c0410400248030104020ba90721002207490109141d98410401c2c180040740f90002c1d401590554801c00070380000302c0d407604200c0340e141e040311016000380020510703c2c1c50b01c00340100c000700005015580c840d00c0000400340501c040e80250701130368031640e00e682c2418410041510181c82e000c049400007041009002968207041d030416405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 570780953 1250 570779703 570779717
    0x10c0318022205070504031403130905090a1203060905180a0f06110304061409120a030e070801060b1308010501080a02210d11070e0f0112021302030a0b04060e16 71
    0x410411800b49280344200341245040605000000c0e51120113841030764020041b0109440800301c0182c0c0e248030f29503032814040c0141c41e04000400c1690704c040c3e4003a00c4c03c41a038800c0c101a680744200589a00d0003800420350320901444160360f0703840f86650040100241803011503450010994030012404000e152540c500102001c020154100f120400e917140a02511390a062801002400d104803007052118058800204111310020b2500080e1105055441c40d103204c44408901810041c90b400740780e88100d441c009489036003442058028820349030050b072106201d50540700340b4130090b800440140e0601c0014031003160041406075026078125229225131040022070307691800751460342c40c5180540c00c805402d1396000b10810000d41c401400356082107849501d83d043d200000e81d1959068103d0030014040c0b5000c04401404c01c0340000c00d041000443c041040f4142c0c4d1044404007041d984800c0c600c1c00741d0805008000282a2991107070a4602e007103098007401c0c10741411420204402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 570782203 1250 570780953 570780979
    0x15140f0c0a080319050a141501091a030a05100f090b0a0b0705100c020d02070e0a060b04170706050a080a0b0402040518100608070f0323090a0302010c031802 69
    0x20004184000d50211045481c0e01e8140c00700c128220560203101821420200001d54801e0641f189002c40300111480300075a4070b840075083c40d004503071602d49041c00402c8038041242003e64003a50030310f0314040e4059a136450526000f03002c2e0703038000e4250210000300c02000e2003d0705411881c02c0075505004c1001500200308000203010140a81c0b003031007017800010b00f600503c0004552000c407401e510300d0900c80c40180c52004c990703460184484c10010381182c0d030700b8444806071400103070300604840b0303005c80c0d400e455175208242540305174000d507500c100819107422201c0007848804018251800e00a04040340710001602c9900001e00b51141e0310b50761240d91500da580d560588000e424098001524a250030791140c400000603a001294003460000c00508688105203184c454612543c0386030380e28013040d5040d0080d100719904411808200c000e2810308000b100c0c8080e110f0b1b4001001445d60300920305010b401c541c41c404000781090b041072100d85802030340c2044550300c0ca0741070310b4211030070032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 570783453 1250 570782203 570782227
    0x406200c010b061c02091f0c050111180f0d020301060602070806060a0609090519111c0c022a040c0504061e080711010e030708090901060c150e0a1a0115140f 69
    0x1070010122000b10741f5a46814015445400d026005100c1c50007044034204041c1c0075022800f414001e02041d88000c0f080c02e4880c1000000342d00f00c07050291100f224000d69900090a45146411180059000c444104441ca10401517150420010303141c0703400290600000a044040502480c0308540d283e00108000c02c201003844107148a84040400401104062a07007465105008110a2010042d020350b010003040c0310b099031200b0390390001d0212409001500c03190080c1241301342d100e00c00d103103098219600c0f6070080841e80851642e8055880e402c0007000780c406a1800c0c02c012082000340c424000054000100c641c1002d030a09040d0b030101c880ca0070940c050042c0201c050602d01002c101e400400c00c5c0d040140024020484243c0d11036070300d03020111402d1159802c0a01081c01061223015412443d40c07103d000c0711801d4080c4c0b000081d450300c0304d0304c8190003d9100c8074481c2030100108418001c441e11780700604040d142c01154010503c0c8001407900403060306800c0004005210110a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 570784703 1250 570783453 570783469
    0x30114120d02010c0315080a2303030c0403030f02013308011d01060e1303120b09092a03030301180605030a080409050c09180406200c010b061c0209 65
    0x80035441121030440480800034081c1c003003a601c2c3c0c40401d0400d102e2280c0072440141c20400d40f11103c0080c0032206d496110005524600c12120b41c41900591020105210900c000e42c0700d07007103c00c00780350703201d00e5483c0060251081e01c0f02c0c5e01c11a45001519219000501141c11610444c0c000b041d01307039020084d0703c030a14100d9034090369036036281c083c0c0350039074000c5d40160742c80c20f1140300001c001055070740030b008111080407950a4800101400c0c10340004c0c1c061049a180c5d0343c0703520300000380d65400d8004581070300300a4481c952154450844441e0720603056000e0441c020f2541c4000d0400c002c07440c0401c0d920700060141446000c800813945900108581c014402800004c0032500035001508140f0300550103401450085c1c1c1c00d0400050001d038209080398169013025210541c0b08008100d10100040d0251049615584403070b90b00c3e1820500c0c01c82036062000152185a4940b00e60266608440025002034045c080c14400b0011006501c5420340492400100260791410b038100001e0b0b0b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 570785953 1250 570784703 570784729
    0xb1804080723010f050603060609090d0f0c0c14040e0c03030901080a0e0a080c0f060705040308090a03080f09030f0f0c060304031b0b040b1308090d0c0b030f04030f0e06030114 77
    0xc1d864241d80302c4c0c001026030840b038080d86041c4d05039401600d030341d8148141c01030102e404503c0383c2e00c40410ba0600e68810b100c08687c140c410f00e08100c4c07140131552000c00c0aa0035600c0302d04100c00e104008250381c50a0b20400340d85501e00001460300c5402540803a0f04e80c0161081345050202e1480051060b007010740041038910b1441d002d81d0301c0b105403440d0101c4160031003030400c2020b204d00c03420300000f03a02c0060350500440450b25064209840c55513807260560040111503003088040600100203840b01c0007412401c0c3c40d20607695160140c00040c50303d41102c441c1e0101e5241c0c030103404003003021000306042d040048142c41aa81d6545e135410b0a640c0842c07082030355000340c610b0200510038000c1c4051541e008070301c102d83d1614140c075448420b240c200c2d54904003a00c01c500410446040380381c00036084182e28170803058074110b1a81ca201e4031400d60030440716440340211100412040640c07002030741005041d1800c000d504100580080b03046c0f4001409078800c500009109240150703940c1d00e1004c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 570787203 1250 570785953 570786023
    0xc0e0d060e0111190c050615061201090c140f120405030c0f010504020108010909030e091806090c190f0b090a150e0913020603041e080703030b18040807 67
    0x800000303c0141644290314010200700103160060400344150403141e9140d070490002c100315124055000000c43d036040401d43c1c004010850301581d803003030407a80303402444e80703c0c0006856140243c000d40301c604803601056604100700100141074601c4401d95460403481100c10300d0a039a9858031030b265100b1040c01410314411180018040c10741508064441d5100baa1854941d981c0d920042055420041000b0f02058401840e801c0d1401e000318240e510032442804004017504100307640d402c21500b52183e00494101640109040c10090b4001c5240c0d9503061a82c407589240a04003214401d01e405100342926000502e00c01075540e50305441c010304402c0b165407543c1c08080380007a1031000c0b0000310f1402000036500251000b000401403185181d005000e0f649150b5950362135881414035800d01d10414a41680c3c0301001c520303210050401c0324840c1d10001461000c02042140700c40d030550401d81481d0751101040000307901b00c4203880800f50302941100f07000d40e10000103880c01c10780d0000c12032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 570788453 1250 570787203 570787211
    0x50d2102071802031506040608070c0203071d0f090d091205102a020609030702010509040905030a020708070806060a030308070e190302010306080f0309011103090a0603021209010c0e0d060e01 84
    0x801002c0d16402580030301ca85500028446207104103000c11400ba610030710001c6844000007521580c060300d69030200c28401020350300300c942c13115260303001a1980150f980e00201c10104100c8040410b400310344e00f1802001c01020303223151886d00240000c03100e008050758000107201362810081d0800c4060a400280e16080c06445103100310840101103d40c0505001ca0b5500c0d40c9440e22400810118000d031300120156140030410b80043d109c0d6030098480d03d80081d510311a1401180c03041c0083c1c0003a030890b40c0680392140ca00999070346040e10980080c141074005005100070355994010100840740d2504104015035103818054414103826119250420540d840384e0146401c484040000e8038401d0f00c040088a485240f100e94413280c0d02c511261507401045400029801105001035000d1008122031800b41c108011400e8681d05a21510101e07401241c8541c100c0101a103650380540038900810a214105800078422119828020f000300801400c0e4024840c00b43c010881500d44c101c0240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 570789703 1250 570788453 570788489
    0x1f110105010e06031902060d0e10020a02031216020c090c1b1c1b2411030a18020d08091201090503071703010b0d020f0d090c050307050d210207 63
    0x140909008842c3c85200f400740360051116400c04410700b102194010713241c0c0f03003482e1703150b9a10802491880142620381c8219614001107002c5400203000c6020564061522100c2c1e250341d140007040054010200d5254802c02c203695a980083e404a070703001d04884030940c44e201e00340948928490204410220429802d503080c075042c0015000305480414640c04089510704402200d04035602007241001100901005000c5100c1e4030148103910445080540b44607540384481081b03400c1c04852000e0382d50080108020b0031480d2090340025503400c2186034040d165603002403110100950700030711404c408940b4026948030400c0307244200304903600030000105181401592038112010840c0c07a80b843c0c0b01385a42c1c03480c808054a04030307440c10400e50308003011a203406000e900185120902800144403600100000f800f908050310301030440340c1c503c1402d2800b89820841590086409240704d05840d400141c0c0803451041280c10b82e80e00003144182c0000102d0808600d5440041036405109800c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 570790953 1250 570789703 570789719
    0x2a1815040510090f1e03022707090311090105090630060a0506030a0f0303020702030c0604090f0b01210e0312040b070807091a0304020a030804060c140703021f11010501 74
    0x1d00560f481810b01c501d41c55030702c40154581c0d0740d060120b5840705c40410801c00050400e0180090400d01c0a504c00110058809820001210481c0c1c5800001c60302c0900700140844054101c02e03000c0d090700c0e110700a40c1801d012903000740000d4403081c050343c0020001003802c4240c0201c55103c04410b002d1080104403260016070320b41c4165a03902d6294580781c00701c1e81c540f9000450401060788200402c2102c02c07143c805178002e41004005a805004841ca403012a40d1124014070181501c03450010302c1c01600031205040302c02d00d030300c0c26051000300b0074549a45811546560107240d214140440c0a51580c0300c503c1c2580504030380303401d4412001090204105c03140303203401c3c0f0400665444210316540c001c400c680b14002e61003590507407941310700029401104240210f40c807600107008070300c20b542d4980e6003001d550301544c006400254400eaaa500b00b08000c5402ea4201c00500001e0000f04d003190006a801000d4a481d6001409a202a040c0e154003800710b10003c03c1c5048020410f940e518460 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 570792203 1250 570790953 570790967
    0x41b180b0a020a0c0f08190c050a090606030b240a030b1002010c140702130e1e0309130204140108130c2303030a120b0102010b03062a1815040510 64
    0x70440d10450285400b198807840c0c22012805c82e070b262401400c00e011f07807201494511103030038001d0320850754000c1c0c0801d0720344800c0a83c100400b5441000181c01c0c0c035014004040b00d034644140e520406020341c201500403880714504010b00e5404102c5992200c0d0800c00b42d0050804041d403030b030000503228507042402c0c3c040d40060941e414a8851004068000e00d016020f48540b2100a5000444825084110403290b0085446c80110303c00c4038202042800d242e40c08a0b0b14614410607540001083d10b1141019072481c2d0070314090250541c00d00e401c11103440d083c02068840c640c100b0110320300090142004036542000c0761b8201c42c40b400556142e22070300305402d2000381c81041103081c0c804048020304000084480807001640d5011401d108441081c020340544280701e4115900d030720319100c0395541403012501410300106003a07040351008501e11441108403009810072102031050405036107860719044075510040b200d000e40003c1d0025070a015024075000550444000e4421202450300280 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 570793453 1250 570792203 570792223
    0x30e060f04060f0f05100e0606071203020a0c05060a0e0706020c0307050402070203010b1e0406050f010804030c1407140a0b0f0301140409060c1d03070f140a2d05041b180b0a02 77
    0x24980c2150723a8042803000510990900030a412143c0309007004080c4a03902801603040b052600610542d260744400e46840001c1c0c500c1001107603900c40d17450095104000c40310081526002a02031484010002515885144143c902480e0009114002c40d80c003035010300341c20200140520f81c503a15031800900c40c5050700d0103070b50145181050100b1503140010840e040716805a4815007a9604e507541120100e1203c8011102c00455213000c8040144c280448406031000f002a80c48699052003000003c400b07940c4408411001080107034000040101102c4c1174a4110483c410b00c0e08e1914081401040514000307016540790000000760103038404000071145098a403250541845442050b407146a6480f4002d49800240701c1008620b070183c0e0310080184009100c00b140780d94a00ca02c60314280c0c004140151b0029440c0440109010242030704041d100607502000340801c9003070100305020740c40b8812001c0c0032080340f01402c100c01500e0598090018a10f0300781d110441ca480181d0740e820620 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 570794703 1250 570793453 570793469
    0x50a0222060806061606202d1e03070203041a0301052706011202120f01170111030f040203030c07030b0604061703121e090a03030e060f04060f0f0510 66
    0xa8080f804602d4110f0980c0c0400032501101c4044e4042940c0d000000d20710aa6694114043c1100d001e1003816518050701c4455216103020030501e054400c100d103e6206141102d81e81202444241c842d5000c1504040b01040401d103100e40c0c070b8544160a900c3e6024a601c103402541d960054420420301c2900558100c840903188003510300c0000011140b4400d003010319215180b02c4e100050207640c03068168041a16544100510300940d940616400e09012240300240204100c010800c40d40405c19640103800300310020001000c158113001520310020344104820711885000c80c09559060017101c840444200c1181e0314544d6a240007035089404032540b900c210718020740002d464100300704442c90300075601e0165243c09080740100c01241009084505481e800400c1e01000d907462484480c0602e0703084008002d1503800e4075000342139030300b101100320a0390083c9080c4150110700c0c1018541090344000045140041c89001000420078149960582801d1006110300e084a814418041d1501c01c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 570795953 1250 570794703 570794717
    0x112030906020109021f030b1207030209010806090309041509090b0109060906030201020c06070c0f1d1509060111030d0c030603050c0906030601031707060207110102010c0819050a022206 82
    0x30300703416030032a0790703944000c2c1d00301402e5081a0f5032104500c20904014255040020b000208000400c98039440b02e00e03408085d611849082c025498814592030041c4411401804c0c917142c40d45040391240500340a280c010ba03250054200b082803110701c00d00107001d9001041050340f6440c1050720b4002c900b8841c02030301914240000c6485080350040909a07038068004282e260f00302403d00c0300c00d030311807001a92810504080800d400680d9882c110007413251600107480303100d15074445205443c015250310000e401c1c2e0008181c4a4840e0032205600c00024280140c4100d040c60180741140701c2c80d01241425850420399491954155005c203040e02d00913422a000042c0c600b041c410907190660360b030b9905900c501e00400000301440c0ca26901daa400706802801d108030b5961b9601681c0204104444a07012591a00d05a503030900c03071b1000010313080c601450541040d04080054101d1a41002d500c0c80c0c442c40011407000d4640c0441c1c200c11a00c40003840e0b18086040c0b00c1e9290021805042c00042007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 570797203 1250 570795953 570795959
    0x30a0309030b090c1c031e05040e1b191b02131d0607020f100515120304090c051c060513180b15030607021c1b050d120b1806040b120601120309 63
    0x1c41085900c81f01d415488041c0303418200014080300e0310340103101e525034408a29000300e021619401602c0c0407442403003002c05c5280000c102501d10080304020312011121200d480016035075a00d00740c00f0310540c007180000c12003400640d50082040b0145003c501d441800140803640c0d82c0000c603481e10080303210541c2c04403800350400c2c6003500e0f4261a500442c3d2400004030700c4038507005c1c20141001044030111b80c94217607240c82d9002a04c030814803000100b1000b041449140a903000c80c4202d032541c440c41088000c0c10000000d180a139aa1070054040390b40d86030342884414000301038051560405100c58440c50201011105000d00004940c0240070b050080b914080c00001e13500344042d40c008140c0b02e0340c0c030710b0101194400c10040b1503441c6860031340c0e07103400415000d10440c0110190340e039909425141400945003584c4010354000d016180c07204410620110b244034258105c201113902003540e0b510f041c002414441154102c111301e004a80000440b200e402ca1035100452184c2c40d4000304540d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 570798453 1250 570797203 570797237
    0x1060b030f01031103071502010618090323090a090515030607020a030c02041e0603120926031903090203060f0c03040b041b0b1305030a0309030b090c1c03 68
    0x2601d20314221090840140009031003083c03c2c00f00600050308842001d5540c50f1800864000c917030140d80075075514a400c0c81100810002c2c1c40400000c440300344501c807405da9001742000f14a507108941c03c84425100320b00802e04808941100f000101550070701f60b299000c0030300820301903942c10031032007105c040101c0382d050120f411881000c89801422841003151400c0e00c550807203d40482c1c2c450b0b07075401d0107051060420a15207504089190019519003545000441e16100a00213000d0200310b800c10082d42c0018151017844a0f270031a030000ba03012488668600e54020094800405500c1c115181c0d4040da00d688504c035450f00031001c0301c0b0a13841d0000700c5040c006041d100869081e03c20400640401d4001100307641140c4102842510b01055800841c81074a941d0090100b5681c001442c44003194820030f1100540011130203400c5003c20307950040d0ac01e07a0180b100400f24400e9000060003114140440d0f500560081c10403401030f4880c180e6182406c24940c2e003100071452800c852a9981 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 570799703 1250 570798453 570798457
    0x10c1214010e0a050402210f0c03120a050d0f23060402030403080f040f020411041706060a030f050304033003060501020606011d030d0807120b060d230c0a0201060b 72
    0x20300c42c0005501c090b11400c2481000d040010400c1e030704210300107207181030840702840d031032455440e5501034101041c1c40c0d00e50324100b0900c5144144258000642c081c1c02c0c080c4c00c0b040741e800c107850b0700b1b0940d43c82088448600250140001500b146403404003040d03031800c0c10890303400101101c02161130643d035801040204070700044e200a00060902070000d10104031800689410501407402c2418845040c2d0004055482d0031407a0407030744001080c104401d2400350b9421140c844a40080c3c5028175200010684d44c5d0a00d00c8040c1c140c440c1031640781c05003d000d10456003d190040d5400241e02d10350310030405aa1500002007000d40700024524036032900c641b00f460140d910507405840c00380c803200c00440350281840407000102981075034201c46550104280000740d0459100c1e00c2c641d02e000c20014001c61041d941c44580b075420603011032990382d6050b045aa03120040c407400560020314a03c45200041c6000440c640754000105121189904801078444200c8a600034001c490f140c6005c03001714 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 570800953 1250 570799703 570799709
    0x40602060403030504031803141014060906060714030a0905010e10050903070906090c200d0302030711010e0a1104110706090203010e1b010906050a0c0b070908010c121401 75
    0x160000d00100340043d120f41c22071074005001c0d15142800101c2c0403018130020b802c95004488110030711880505040b000d01c44003482e00190300040010760035001c285024040f00130315580c402c0300e0801c00107450790f661009a500d026048800380c000a40030303c0d00070760307245d104038454030215022550000b4558803424529004640241209000190036141138a00c2d0f0024100179070306016410010484056a00c0703100d00400320840b0200e41c1448031039003c0c140c41321a4010300c04178884451220005500000c0b4001c0202c035a140061b030740e60769444100d40c42510300050703802075402d14650080a00000419442450048400780c084218003402c02044448154800440440c180406408280c4984c4071014141c000340010408e03000d41035a030b40c200105816404610700d917810300341d959542e000e0304c80b41c0500682c1c00c050b8a042c030020005030080001c050018480c120325400110440d02c12031010000305101002408110302000014000000440740400c3e4280740503a45522a0500d031031003412 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 570802203 1250 570800953 570800957
    0x1090e0d1809020d02090405100819050102090d1505150a03080c070506040f140109180e0708030c030a031401260114040602041706061318170319020406 67
    0x910465096410510094038100c0e403000031000042c02d208140020041150007000050390350754544104400c4980281070314a440d010b1070400e1240c02000903101d081075800410075603c2c0f4040f45402406032050548158000004d4220700007000400c0300ca130800e11038a43c5092200341d8501151614580c2031010450f407100c40c8500820124038014024100d2400300420354041c00d445101041030780d03104c1e80c40110110044041005180c00c5290308816075802440e110300e203189008400d207854440b40d9200407039256070340c0301085015030401981c8020320010080d81d444500c0d01404507282e41110300c414010a0030021070304084400c81c04018182c450020340c0048071107442e11140d85c2e010100b060345e0055941e803401000040d80d107103200e520440c0f00d1500075a0301d900709024200d030301c0022a0080306950080003130080765a1076080c0c1000c00600f604001030083c881d420a10303c840040000034021303a88121a080841c00b55900552041d000b140d0f40d031002c4408241880124840ca20841c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 570803453 1250 570802203 570802213
    0xb090a0b031906090618032303010b031906060302090a05010905031504150e0a111804020f0103020f131e0605071707230106050130140f010e01090e 65
    0x7040014100ba0a001c034003407500001d42c608140c1e01c40044440c1000c8854410118020b4401010303880190035022102d810719414070040303081c81000c0c05000c10301446010400110000c0c3c1151444c01002e0202103a102e0240b0010b5503540c0050000d44c051070a0342c2c00340c0708400c0e000c561540a150420220f807005401002d0016244050110b100c1d400b400886076183c0070b104c3c41a54004900842201e0b0040e1000ba00080c4100d1400c0d0174211a1401000d000780701c00110b4901c8000b41c05082d5500c0381d0180d611070743c10b201c0c21004034020b2040c115500654940445c0b5142c0c0320740442111000c2e90515201000c0a40d11412a0804585240300b810009002040f100c0c0c0003460b480d10040268035000d0140b400c0074400c1d500d1158070701843d0304038492081d8031490b600300d1035070901410005107400c0c00c0410403040199204041482d803e044210100c0502105c00c103080042c0c0d2000e040c01c402c0e40c1701c20400d030030300349500c01e181b4a080c0f00d08241d401140c8000b041d5680c1601c0755034564406100105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 570804703 1250 570803453 570803473
    0xa060b040609090e0102090a0308041e080a2409060207050d02010e190507050d0501051005060c0304050114040f2c0f01060c1406100e0109140f0c0c100b090a0b03 71
    0x3d084c0c3c20f0070340c0c05155000e02c10180c0d0b603100c03503000102842c4186007003910f85003081c80c5820041c0f0f0501c0c802008086070001040350b200701150607202c01d070700400c02c0b0640c070707a500459140900e030485c03501c0c15242c604016002800495030240004a1098043e140d48021005089080c4c410300501d812854000404009101c008586030540d618820700a5a00b1035594030000341c1c200c000180169860f0751902c003042100c00305581408082c05080b01e2450030300e20f507a50056601c0c02070780206814071622070300e0342c0074002c0b4000644000301110b52501110b00e8550b0000c1c0c3e02c44044010348680c1c4d4280f550000414900c04c08003d200310304a22174107a0982c039058044410083c8a902034501d00f41c00c18400454010510025100e260780900000c030039460241d41803c0a141640039500c41854070507044030000c1e61a580d90f0700302420107100c060346c0d00e400400c14820310a06503100c001e131164404601110080703401003400d0040440b0081c078507a5551b8148010765a0011417581d160b00b02038030380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 570805953 1250 570804703 570804719
    0x3070b0d091a0f0613140a0f0506120706030f14040609050609030a080c0f0702030f010c0e0102061303031d07090911041b200105040b010311011e0509120607080a060b040609 76
    0x549006041714201242c01100003031250300484080c3d07036160040d45c035070030314061400785401200c1c1c00c003c0070355900012551030a8102e40745c801500405007056100c9401d5042c0c9042d17504802d9605840d911406080d040c586840300082c80350301422103140c00781000285c08080d002c02921052400c94461001c15a03e9040b0551607078003982e400d12803a2400e00c18a070150320100140e0702910146800042d0b0010b030340340d024080b024180c03840e81c1194082020010720080c0700c00075030310003540360601040c0c240400f0190203807501c007050429010310079444002203d80a9412030007540b030050424810860140003030109580c11a1083c10b030f0500c44c03010008080f44501035140c040a02d2000d07650513035480002d000e081d10000c1d2816546600c098005106000390600030b442400b03024200b06101658540d00c0c1d0700c60381c0b41800340b07030288140815000000d4071003407100d03108544070000382c400c185043c540161001d201074a80b41d01da030385400c4020072217440d03400444098414540750641c14614145071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 570807203 1250 570805953 570805969
    0x20d02300c031003110a03060207030905150702060f07060b030a0503071502090f0f01030f0204030501060f0806060901090e0304032306090f12030a020d050c030a05060306070c030e03070b0d091a0f06 87
    0x106131b800413412400007010501c503101a00e00588240d4039080842d01d00820002c5050103031007034484000341008800c006948400441e00443c031424016621001c0900302076008100111711300341c05000c2c501c90b000420102100030106540300305080b080511000c1d0f5000201d0041481e05500866141e0214100e8036118a41901d500014500030417130030710b003006640a0740c01079170003200c2a0791151014400c051640302114090510301000303040c01e182c49000141001010f1180030500e03030780c40780403c2040c1e1092084801454015200c411901d9030700791141c0e0054240d031030800d40ca0107048007244c64114086030140c0c1c0014081c0c020602011110311094560340040c183c106201e40c20841408140c5050141c2031051b1100c0036441c1d103900d8815401010760b40c008203c54400e40050041007103003508207076042d64130340e0185440e04483e4034960100f4a0004241c011403200340700400e4000004030150412040c10f841080c40031035002c08000705c90b8007000103a410401c11242d00f000105070f4100050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 570808453 1250 570807203 570807233
    0x18070303120518100b09060303130e100b070c03030206060d0507090c020705040608030a080a050c04060c08090a090b0307080106080c0111030f120429010603020d02300c031003 77
    0x28004020381120f40300149400d00c1c141c422421607841c1d02c461001c600e4405525030f40581c060f40550300c1c14062094480b04d581c0d250083c080e4580c22a4003040340300d10071862074005030039500f6085aa8103540c0c141650341d0b5080e48170480040c450500090500e040c4410710032402a8044020400c45042400c1000030b070a0100e400c2e02184540d110000700c41c0e8540c05150014070014001d583c0e64032005600405182004000f1804103080c030301405a4840080111000c030f9000f0300d81100c03403094610703001c1e81d20301c94484503c4d8841400240410030a01c1d90b4012007000c4800c604462103555156802403c0ea180c612840c00e840e08128124130240d4040d402c0e0719000300740c620a6074175105061080001c00d802c07525107800007141e004108000c1280602581080d040074807900103640b16080380344021070740e05006080805d50013181600700c089440d0160b0794070307400380201800404020f401802c00f0454118030041011503840c0440c41c6103c0c401d00301c074002e03440d242c4000304050968480001c080c010075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 570809703 1250 570808453 570808471
    0x40f150b21150a090314130306150b030a06150c02030c0409020a0e18010b0f13270f200a0b0703050717030702100e100b0a05040204060206180703031205 67
    0x1806022801018180c00d20071038a4210014003c2c844c0d080082c000344d4a1b88220082c0c840410400300080380d611500d20450b43d00800100340806d1038800b40c64480c400d40c2c407503100700001100707004940740503812001c10b076620300130100c2c481d000307200e02250707401c0c08840040c5d05508040701381c1080e410250040c00c24140090518030080b56a096113030025032045982d55584c10404903030200215080c0200502c40d47d04490411040300d80c000000d40001d589003942c03a04955520040042c085140c1900f8075030b0300c800b4500c0885660f9401c0000415000c02d6003110b41248010701e400c20218090b0502d007400b030380070b454070301054244203a1105a034007002d025404e00009001c0400081d030a01d509400000d25110301c075403241403490010340350440e050002c04086040070310201e0b000000298800482803007002c003003080840280072500d8a0141d800484e007160001501107015600020b010340119100c0050705083c0c2d0340034100c035450301c806020050004a068840c006c40e4003058000c41d800c0f035014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 570810953 1250 570809703 570809713
    0x405190806070203130b0405010801090b04092a091413050c0306070f02160308090d020a0b12010f1d0601140d091203060f0b09012105040f150b21 64
    0x201a03107850414215410302c0141d10006801c04074440d0044924014440003402604003401c00c800a040e1035414020031400c03545c1c0d54020340c520340e200e400c005601074000c12503030311a42c451001007e41580400c0030320050040c035030300050f0f261039a10910b41c1c4210074a042c00d940340c50340380c00b03400340001c0400d0aa51038400c8010707100540d50b0900c29180180615141e00c0c2201c14003240181c1040700180c030540d10302211240400108140c00104e507a5490203c0d40c0d90300f090070034400121296005d41110100c0400480c40411a0000741c401c50f068460802e84899495501d281800b0110542030111349040c0d084c0d000f0030500d5005211004020a0103803459041580700031403901103038140001618901300d040001100300e60035204a00140c03c0c61800c1b10552824031101e00c1c00340c0b050b000c68a04106104c240300d405d900c240f4030740c600c81240664050055080a0030407404005464501b5140a510341da200d0045500718841c140740724202501c006407200e43c4804540c0040e6500120500d14019 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 570812203 1250 570810953 570810959
    0x30702030a030c0302101109090c1201051210110405040501270207060e10050a0c050711090402030f1507120e0c0405191e051e0406240b0a1106060105040519 69
    0x220303000b00d10194442c800b40f951a00703694030030480e402c1c00c080d0440762621400c0254418020802d044581590401d8401949102054ed01c46103400b03007840c4030700601c9141401211760410070400400441d00700b2902840166266507050350302840c0301d4142e02c002600080c41c40608011600505407240c0207410008040301480f20742810400c480000d50601070f5a4000c200700242c040c070901c180340c1054600182004519562600d8901503120030910666840001408545e020411038140f074080d102580c06540b403519190f2144081070395020003081e0400480c10762400603115203220901460018281d61408005000080401405a041404a0803141d03032089549000d4542400d502c5a0702c2e40c2d20705c24409100084520103818540c3c0c1e000300b5010408184854104140c016400480000c1e01c8400050065144840215910b400c0303011840d000a80503240701c00f9145004482e00c0b00c5480c600031440702a181e602c00c80b0641d001c50030500c802d0056043c459950394045412101400c03101c5d403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 570813453 1250 570812203 570812233
    0xf03060b0d09170309070b16080c06070e090f161223010e0108070314071e0e10181503020a090506151e0c21040f08030702030a030c0302 60
    0x711050241d400c65031126801400c006001419a80901c0c06000641c00c5080141016464170402d104811300c0610100f12000312071440c1c020b00280c40d0340400d52680c0e4201c0320a810341c80e80000c0701c10360041030101641450342d06080d004513100707074000450920641d407a603181c0b00c0f541d01000c00d800200405901d120424071428403651280b2100c40040c3c81e030141ca03084080c550808140c002001d11510700c001002003100015072101038940c440710000200c00014001443c00146922403024810007801804851305004800029115044071295460b9207140e41b000311a1894414001d142040d18000e1410442c5580264510006243c46601203592900007800754841d90300700c0f506042d910010b0103110f14000384052044284446014108a94600001d001c0d211003003140c00252800203010100c41002c2c0f10b03050250240989400d1507074445082c86103980c002e8000c6040807602e1000124003d98000143c91105500500805240c1d140e5513049680741082c1078100e065100b0352090b401001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 570814703 1250 570813453 570813457
    0x201021903050720011e06080616050c15011a07230a0501021207020d021b06031005120606014a030d02010207020f060414221a0f0604080d0f03060b 65
    0x84d1072040086070070034100c1100c03403011400001c1001c00500e064030422841a020079010360048c12004c84014807220702e60107580ca40f04100c0e0100d02802200d0103032000da496481041d0680314044100000a41035500700d00007031041440180100d024140b0707006034121440c41948440d01c0340c8050b605090040e030350340c5080e42c00c5240a1884507a4004c01c003d0050390400805110b01e185200810300700203002280c481e005240c4c842070b4014080000002c01d02100f0341d401d2001840c02610380d42f401400a030174191151410381d01039001034214058120f109400600540c04001d00c1d00d00d0600d180c00102c800d440300d00c910b4040e01103800e00d81e80318003104d9809001845001203903800145c1d80345040c1c410450855190b03800c07a071041d0300501c07062000c0c00c500349020410207015642402c1c076108480e0140e110101e10815400f20714200341150000b25809110510f000b1016604003039294000b0382044500d000b203009910301a031110507180c2041c0d1086000909114283c1000178000303840341c514209507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 570815953 1250 570814703 570814757
    0x31303210603020907030c1733040e03091c022b05120a0923040c0c020306090106060507080a1701090507021608031c020d050108070e0702010219030507 67
    0x4141e4900c420001d40c103200141942c01699031900b00306034032858502405c0c413121040280c4500e403031000058a0924030007140044000e41c0e40f424070311100300000500601041444482c011030a01c80c112440ca4800415070720600c50042000c0d0118079508a43c2200c0040c104040c0e03401004074100340003070600001100d12914040c100090a4515401e0851401c40001d840230344402c0c0c104100c4858940c0081d0103020303907139000e0703001900c44142403090701c401c40c0414001d54010319103a88155010340095115805034425003c0c0d60043c1c1c0c0300c100c1e05081f14a40d2091001041c010003070240054400e400400c11705266003840082d905907d03a075070400100c260403040170951354400340640e8036010064201e1a00c40b4400c448130560500c0c50240d1240903142c688421a800b4890181e901215501a500003518850f410002581d4940f80c00f0707036800180c840c10b5100303200200480c100707074810700032104015000c803086500c3c1004e01c04110000d003001429402040320b5088100b400d205200380700000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 570817203 1250 570815953 570816017
    0x8040e0408030915130201051c33030c0603020c150108060703141e090712050705011b0c26100f0506032a22050f0c0906031303 56
    0x807843d000460501d00700d10204030041e858034a500b0040140c4503503010880c0c142d428038107a1345034007440c1907514030011881103042c141c605182114022011344e60b0194400301c2200e02c13050700c00b0121005041c1001c05404058200c651a81d03050101c6d5000e50000c1034058140c07070031103100f080050000c803810b240a0700043c03c44d410230030034004156414041d60780f000c0c5500062541c1070034072090b0203141c140c0780c03a00080490740404c00142c0004c02800048014a490744100900503244d1406540383c034940d0141d64041813600c5801036980003154850743da60765020225000c4035007010300411400001c40c010300c00001e0b540a0a130502c0005014000400c1c00c04940032514480d603207000c40c00d550300204900c5c0203074004140790100100c5420400f111076600d0100b81142040e04010035046d07040301401030035100c80050341885400450303004910800601503c0031071910b0f0548200001d114820b0721541c050014404191114a40d00c00551828401c0c1404809840b0422000e1120217408110820b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 570818453 1250 570817203 570817207
    0x406030605190b0712110f06091006050108070e0a0909060203040506071b08030603160803030118050403050f03060d02040e0d020f0a050729040f0816140d08040e0408 73
    0x1003410702c0e210758402c800d9881e503000e4140f81400341280300d5001c0d00c2d43c06850108200c40c102400b034014140e501802d162041558490020100501c0d41c40c0d4050f941e6410500c03940d05e11100d844084c1c803840050300c2c016520903080d501c0340c842c22511710300540c4056034800302d1084000b50901051049062280c411000580c0700e00d0142000c500709000244032109001c0e02000d808a0090350f5002c0726005688120102c0d140c3d00c0e10703404a8a40714100507000204080b0f81d42c04641002c001011f941211252a0150801e0801700e041801703807407003a41d008020420500c042c9d0110100355000d56030003103000d014582c5e0503020b9000101654001c8122a03815007100619402d0207038140b101515a0123a080182060711a039034840396030311502d00c02d8000d1110461104984990300d40c0d100f906500100d010f558450b42ca0341d20b17011070240c091142c04035031700c0381c10071300c00c05070b015240418102d6020311a08000140741400b840b10524416a00300c4942808001c0419a1040d03410001e000d280283c2c02c0079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 570819703 1250 570818453 570818459
    0xe0f0106021b0a050103150306020d09050706090503120c0c04091101020c0105031509070c0f030e010914131e02040f06090e040804060c08070b040506190903090b180604060306 77
    0x207410040d070b0440c1c10200caa40203041d8100e544400c043c003804c5075030a180002e1150a80c00e950060b4500c1034000802041c00000c0d40042d0342c046402460066024001391044169558803d55507505584105d90305a0080a03044a01c1c1e000c0724054840b80c900003050701c0100300c1c000006000c640c440502101c01100d0900002d42c1c4d03581c10030001010000030b0030028a142454143e10004008404103184510702900018008030301c00c1d2415400300340c1c44811601508503900d406003a004e0701d0b003d8540041c81000703001403030b0742c2005cac0215075064002d040660440f181c4080180030b85049040c1d0359501e8140c07418181030030300383e1000340010551020409012810260000e0001096a02c0552104481c000b0300011038465012034049918034106041c0c0e0b2807092400f80c0c224000d1040150400d0700e44800c0105010300070680b14400d075801035410740303403660303206842c01120009000640010700201080c0b00d201d102000912500c00d400a0116800c02400c0c00101e00d98045e41205c4002900c2d00c1c410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 570820953 1250 570819703 570819707
    0x150409050109151104050307290307110d030603030c0f11300c0a092f030a05090f0717030702040e0304090e1506130e010c030209030c09071b06060e0f0106 68
    0x40050035a20b43c11691400b40b0b000c0000e540d911144c020351503800c08140c030302740d0050034095081d60811000c50000b0f0b20380ca00020098020700035450305a98030300400400200c054032a1140f08103880d419201d001070307254030b901c0d5015054440b07001203805114041902070f180c1d864170000c0748400c04005c41140c0c050760303d10035040102c440c5040d00c5d40781d921000903010603036540758000e8141c2d420090000b0704582c80c101e00b28000255106e20f1075602c40f1074400c403004100983c006510031442c8060620075070b02c803074408030303036802680b14600701039040382c8002d04c0036008c4010f41c3c200484c0404112403c0031031b240c0008080300c945441d00d9020350701c0094108540340d01d5004080a95a8a038080c2040700c41410b450720084070028481442803c4c500781825590404d6840540900d08010082205440d8403101130001d5120040d5544a031044035481d904c0362500c3c2d0452440342c80195101c41024401c050300e098840024603007211940e0b154100030600c0700b2050a200e20030b80040e200b0070b005524180c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 570822203 1250 570820953 570820961
    0x6010b0f03060a0e0108030c012909190c0e0f0d0c14011e0e0a17031b031c061e0b090906010507120306062c06031801140711030307020615040905010915 67
    0x2b01c032281464041007074481c4c602c081c91a0201030a4070014800c2c2d540c00b5013070a44051030004942881d14145408004a41c0402100e906074070503200811207042207010010590b206000041c105804080305109000103107426182240c030605091a4041100c00c107062007102c00b004c003c0005050003d020820700e084002e50005180014210000c0b07005101c109443e881100d04201c0320000c00080450001d0040045900320f03031101e0b0701080304810400d000c402500c80c41c401c07018150442c81a0080da0098000004100d44524841c1c3c0d2410800c44203000c0032410040c42141404010310400e0301007505000d594490001300d690000b1350714140400500300d144074040610300c0d054a007088408019405801040e0400122142038403507450b0074108072180310b1020b280e5070315400d280720403624481420240b4021030454982840451440c0b8940b9031300d000444140f07005030310800100b014510441d00c0c100254101804c042494049600d60b1820764a0070f5070708507418101ca180b4251140c00c40d00c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 570823453 1250 570822203 570822221
    0x16060b04060522020310080d110105010515070f0201050f040f03030815010c061d01020a030b090105030a020102070603050c070f050c12191407030516080f06010b0f03060a0e0108030c01 81
    0x4901a4204554140b43c610030055a441c111003503000002c61000c2c002182c0000c0100f040c24202c5090310901400205034140d22428000550300b0078001056074135009108010340c0250440c00d5042280544554105800c074090580c103101c1c01300024032034021000020405005804121034801e817440c64000d041c880c004105040014685200821903a0322402d1081040e40000000c1054a8928090200f511807850039203215031000500100381390b016001004424400c41d403801060380e803030b0305050b02ca101160000307006030000c0205200b198041ea0050350800215681b00e405c104142d9278408030b0341c40c00d510544995008452003100c0c0c0c070344030076041040f007185009044c40140080101c0707006c56080e00b009145900c0c01d8055250500200300e500001d41e0020111203070f410111f43c001007501a0b500988515000e400f55440d60b44600042c3d1074100c0f5680e9007580c0c40c1001031100c0c0c140a81000d449140d001b0f10031140020b040c2240e81c0c159003c0c0c031070807002c0c40c1c3d00e404408016007100c40b101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 570824703 1250 570823453 570823459
    0x190212070b040219231215010e13060c050903010b0a030b0c0702190f0e090d09050f03010b151308010e1009080403170301091d0a080d0216060b040605 66
    0x108000000d20704003480d5411541c182d40000c94a410f40c0c1086110f007080350402c012250b05414920140c440c1101845402032003612002e02402c0002e82082e220030301c034141980e120705140010080404907010391603100c4004a50f00020042564600080d25840010200004c1011410040d903150030712a00b01e00d520205d4801690501d1980c8068004c00700900d01004203002140303200543d100d19074000500b03006100d038421407540394041008056075500070301e20b10160706000180000c10000381408800a1780c0c488004c0139241904000c0c10b00407000c4010b41554a13080413040d6619001d03a41425085480c01040d01d5123031040f0030740402a66039000d600203a041c45540303023841c40b010840d01c1560325400804101191079007400301c2035101c0c80d400100003040c0c200302040d120741880c0203181a12051002804400481820100d100b041117003680026008083c600c8001600d10f401001032801e03c08000d4141812000e03105085c4110714800c0e20348a44030a06440a86414401d480203010700b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 570825953 1250 570824703 570824707
    0x60f0f0503160e010e0a17010b1203070219030605190e01150506160b0c0a08070e1011070807060509030c040203070512060a1703090a060801050114070c080102190212 73
    0x105480b40a00c0303480c0221281445100301040d90301da4499050ba0184800191001149640d60004102c04070648400c017015075181403200400c62030022003075034913404070000139410801103400f0800600044003561841201c00035002000400e07a015851040c00505d01103004100406071817415900307881e000d041242d14102300d40300c03400311100349007041c0d5000342d480c00e03103c503c0002000b0240382100c0c400b80c001c6440208010f48103008c58000c00c182c4409a41d02925500c9210003074580c0c0e141c9859056011a1a00444000340e2050719400380d0803801c0c0f011a04107507603da48103814100180c1004000840000c5d1220040c101008021030300c1030103030341c11071541c41d12800c000e00c28092450300e40c4544070320340003099990b0346003410940980519401c500410703441c0c5070803690366407081d44082e000300c011800000320603001d160b01c0c80c126101a11001c910417081808810340d503209080031180c40e00c01e00800304803a28248040c00d000c140320b1008006940a43d80701a2074801088055001d0b0842 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 570827203 1250 570825953 570825961
    0x60d171206060f0d051306181a060a06390b06030a05190311070b030a050901090203030913060f0303020d021605031e150c0d0f14150d0804060f0f0503 66
    0x144404413960240744510010751034454500703407040a01341100c00340c001d505055040d071203101030f11400003846e4880c01251ba0700c0c2c24200d03071269081000f2601d42c0e0f404021820204003044c0201c0c901c030a411900304040921102403450b0440350007491025210207103108801e407082001d21010117820190480042440490a90340c03140e0f1403000480b40e43d4400310042144041600920454490140402c1034840803902c0d135000c0c85c4181c004581c0702010905200c0403800c1c0e03045c18070402d004c03107401401840c0b45c20020002e104a6040081c045181c0c140c0c2ea401c00580003541d0003010000c2c40c442e601421000f400d00000a1500c0f9001030242c0c803554186408002540d0006044c2c1c0300e50140b00780030141404e10040c42c0c2d0424181d480c0d2003c28001c6901001205032008008010f20a15041c0c10480101144500c90880c0d000301443c646000e82c00f80824541d4400c1111900d51030b600070b000c0080704d03415a80d41c1c07403103401650005010400920ac41d010040c3c00c0711182070b22042c075140441c15450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 570828453 1250 570827203 570827227
    0x80a02030d0f0215010605091005090d24020408010b15040f1802040b03130c0b07030806131508060a0606030b09070c0311070f140a0b030a05060d17120606 68
    0x12041c03201c0074081035150300d2a985009101201c01c15500c01403803642984c1d90f010191095001c8455584161301d0000c00003c0c0c40d001e035080c1e8083c0e84001d01a0389210181e503440701030307a1400c1241108041c410f1a04028078002c5800140b014208030000400c043d01c10100b032284940490f510150110030a02083c0041d204034100c49044030320500c0c0f64000c41e218906003000902c1240c2045110400010411800d413803503d68034030701984100e0301e04210380d5460411a105000340c62000300041d800c4000310326245031480c4400b9100308141c6000031300c220320000301c40d000c3c0002d5000b014243c110008014580e1800d10400c00140414203042c040141c8000028030803060080c0b45c90180165800340c035082c10b11036180040c140d034140048a01085c0c03560800c40000071188540c919008401c0b0b14400c250820f040c2d000c0884030301400c25411512030300c1e0480041d1400615441d000fa075042003020101c2c100c1e00313040720b07400b03d00b03038440f40c0e64100b94207410080c60004084c00d0190748200f00c810030402d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 570829703 1250 570828453 570828463
    0x30405040b0916140d0617060a020307020304050d050319021011030c03010e040f02100c02210d2607030b030c01080613150b0c0f16050f0904020f120f07080a0203 71
    0x20f00920300074103452078469000585029020707503060040c0c074216001c1064000948151621f4480c042111000e555888071031040c1d20084a0007070042e042030000700540e0a260304160002e610500c1564240100213100c00a66000321a049006901c100520040d092451103101918811110554a5407510740080300d994030040c8174096060480c00f001505016462001008655008003408500d442d5a400102040b00700742c0283d100c0d00b44503656102c1509210361443c902e00304003014098401640005a656600007a01044d403112400c1158590100a01c10b0300d00c80c0e00386481c002907401a80041c14a05074805c115176042c00000b03000c2c003216640701d6203541122000f80ad03011a5600d80b004510380303507030150b038002c0101c210082035581d0000c00210301c2160381160b4100711110300341c4100701d0110100ca24880d06421156070041c0c0241824000c0700710394002c5c0068601281c100c0300c4000704003640c003060a6840642c106020020050b00b0a000c8040113001e10b000420345159241c001a85038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 570830953 1250 570829703 570829741
    0x111902070509040b0a140a0617010b030601061116061d010203090d15060b07050a110d15150513090201030605030c0f090604110304031214161d040608030405040b09 72
    0xc0740700320001041c104075500038a1261000721150546c0b810305101c1040548854014817010000c4a02c6400309000f0520464a071242c00500074411a4070700101501e1460320301180400320302407034050710507a20080004000a2000740c0d200000901c9545202000d0f50400c0d205504640040100c52507a95032403000110f043d402c43d00950448860031920401402d6a50181c034007181c000c42c110060260100d50001d401d40150241c40301d01c100c2d2001c009248034000001080c010844408050250fa564891254160100682560ba030344070070000d42e032040750003401d80b040790f140c841e440300715649030249400401040d0020b02d10100403a000914a4481d03140d02070241c9240e02c0003501c181e44a03046503a009040840741552401c1a081c02000082c080d00185411400d102510b4070a4809031007092288200d160880130703504501904035100150307400c181822030005146001142e65912815005080b20801503a4a903e08000e00c816142c0c0024030b0740c1300b240d42800b000483c1a44103800020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 570832203 1250 570830953 570830963
    0xa05010f080a11040503010f150b03010501020a080702130509030a020706030b03120d020702090708091b01050306100207030c150206250f090f1202011b231011190207050904 76
    0x80e22600b03d200d00e1901840d80a00d0b415800d00407040108080c80d0700101141c0f81d41c0400c201010348501412a180c0301c20701c1603038016031054210801182d01c0901602e01c6510003400d4803441c400c070307a0032002955020703503010204c0d0304002406a4038980400900c0010006d03410140f10b0700f03c10b44000b03902c80a400748070b143d060100080ca0242c88240d075044035a41640242841030f141090040103180403012988003000e4802c56170380000c41b18002e44000c2d090101652901d286a51301c40c140440b003003214000034158442c000d03000c0001410030320703804050514504034404d14030401000a283c00380283c00704c8080c2102c18a922240385c0c00c0d4550b056003015034104845c04000c031038070440720306600d40c0c005180d40c9410240410181c0031241a126071034000d90300c40885401d0746081400003100d6200044c0001e40d20002e0040c007484107400b40782c503d507480b415101d403030102954100a41e07040d001410601c4a00003410740c0351240f41c024030410004036100500e1500d0802c4c020071124403020b00082c0c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 570833453 1250 570832203 570832211
    0x30b0a0e160b0c0a1b0305070e1b0702040e0a0602090102101e0905190501020909162a0f1218081b04060b0d060807171b030102071b050a05010f080a 65
    0x450038804004c6031000550100b1840310a1410025090706020b1500040310103010f00034002400780d020038540d132300441081020210f002071000c12045280c3c40240200d0300700c0c0e2102c10304000f2007414010881300502075400035039a0b0f400701000900b0510314500e000070a518000018803d551040307520400b0f229950400100e07907043c0d0902034501903807001c0b56111228806584d40801c034040d0042c00420005407601c441c2078845201103290b00d0107284401c0d00084c54044c0c00219055040f4a400d960b182032240c040c1841010b45a400d26800080350236108107481c410054906030744040b81180c1542c1c1c04100c0100c1c1410800708545403010042e03030176020007030310342490826a00c80e440b4100034980058415510b01c8560700d84030140205201e80d10050180c144006407060714018000c802402080103001c01038002c60508581c00001c001864040d07600b40b0968000480c1c02c1034902c9040300380304e481c100851400007003203ca83c81c250421410072a2180740c01300d850b5001858240c0082e49003002103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 570834703 1250 570833453 570833467
    0xe01180213090b090a0b0a060e1f050607230109080d0906110406180509010810050c13030b090606040207082b050109060509060607080406050a090906030b0a0e160b 72
    0x1000b4007807210019008690403001c2c02002000082c0ca410058440c00783d8500320f949800582084030b110b0b10551107000881d200149480303c10b10401d91220f1b10201942c0401c0c0d40b45d0f0b000c2266038020740400c944a002c040b00f541c40e805409404c4170b0881003100000e112074001542ca046207030040e0551041c05c0c9071604044400c0202c0e60304868000600c030a00179440c0c40d41c41500800c12151060303035000e001c0d4090b40200b0181000c0d508a07040c0c0b0341c1000100003042d10b40b41254014180105501e5822030b052010350010f0b6034441c1a00c0045005114030006418401980741c205800a405da07480740744108030010005070201c2c01d903440c0b13807028510074042c500080b01500880803585640c03100a40391a00110311020968841000c0e1007080d503070300c891641d8a0f01840018415400007030b003007141c140010003605104d40f009100c401100c2c038000500c540d44003403500c2a522541c100f16412081e08007001039101c1144502e07400d0f000004010084214050b540d100303134100354003ca4620f16030002e122 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 570835953 1250 570834703 570834739
    0x60c0f110303030a09060f09020a1505090402030903190c0f140a151b0c150b01090314030306130b10030e0f06010e0601020f0a03050f0d090b0a0f0e011802 68
    0x15140c48020341520b50b42d14001004c0e200401d10003804446061501c0102c00d8001d80038402c051a050780500f40702d82c114140550100c0e146003d950943c20001c0c10000382da45a02c2e50300180d800749031024000d41e11415079100d00420044440003200801003960301c6807000c00e010804e41e184698000c004202c81c00f0b03600c400b01d4142030340750318081c20440d8500c51041408403a40d0085031060003070300d082c405007040050221507114118030046c1c454400e02a90940f2031307081e41d000041c2d0800505200028681c0da41e206010348407410719005941e01302008104c00381c00c2c44d10403241c100300211010000405035000040c41b41049104c0e250406584491501807040200850711195450744c0403685190381d00d81d03204018480488003071340103000d00c88200581d070b0380c0081c2141d2000e5164483c00d09041c3d10807500d41d6a40c02c0f078030482c2c8400d61942c40c81c0c000301c0c40600c54a0301410222501150502c500383d040e100380c40d840c8400032030981c5415211044100c25100d02944194104c0704c1f4840c40c0d10500d51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 570837203 1250 570835953 570835973
    0x60b040948051e091005030c0303120a0203062808070e0112030c03050f0c070311010311030a05040507051f081f030201120902060a1707090e041209090513110901060c0f 74
    0xf0b060340000d182418005140c00365010001100e03012012180340890f41d20516449004584409540d8408600490011621900516400040a044029544544e88820031a0001016030009016008009202403202400808058482c0c03040c5080e032545009a1880c90410130755001d402c01045074031700e90415214504584003401c0c11042c0302d03141c44032110b1040c1ca404843c40220380740403035886c15890740c0d40680110300c1c0440702c3c1900b250440d55421420030103803400800450b9540500000451159910300d25680c900851900e80700700c081118a003e40041006801480300c4103c101008110b11080e44003081540d07420318007201c0307002c11000c50802400b44200000d502c14004140c004090354010017a08034500092050740064480b0202900c1040642c020701070f03c0d0300300d5800103001c1500e4428500d81c4050503d0038030180382c0e490301c4080845209460301f40c0e401c5603215130300c0b09200c4615012600d0314001c4070040500c0d458010040c04c543c004210040c0090000d0300194148024000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 570838453 1250 570837203 570837259
    0x106022b0201110d020901030b032e020706110406030e06430203090102070609081b12010c180602030309030d0b180906010509150904060b04094805 65
    0x140340c44da4030050550001c4d400804001340080c2c644101c1e0407442c41c000842003003030201c940d114003d046910340f5603141c070b1890b01f1340b41c056503800300842c0b000a9150310034186036010109440e511141092001415694110f81034901c540c0011f0a000c18455040340d0050300701041d00c90034014415010340341c00ba80d11103403c0c3e40040381c0441c011905003038010009000001003603003943c2c0100e898107015500b0740528000c03041c0c19840501e01e0161078000310410300c080b5100821b9407908a01c04401c1a0945040040c480c00142c2100200307022507040c0d010f001e01800390b82c0041c5003140790044041c0c4d900c1c040c0c2550748804a40b0f4400a20b500d4542c043e03240d481081c0c3c100301d0305403071800a6416507149420300c54540240701e0b0a0015182d280c410780e043c10b04036002000400207465076160071018000b90030410382c0c0640d40300132040c00109080b4181805103d21305000141100c44c007141c41031b59070781c2c0b03140300d8140104c1c180215040d40110b58400039210211001035640c0341d188032020240f01d0000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 570839703 1250 570838453 570838481
    0xf0903080f030708100305030405040b0105071b03021f051918060f080a02070f33090b0907060206221202010b040c030b0f040e0f010903080a050106022b0201 69
    0x1100c1000c01c100070000c5100340855101c00406032241c041d0700d00284000d10001d803540d0405c1c00b041c40f0524182c0c2207031415100515065042002d65100d20900700318100b104040014888410030842c00c24805072503403030f01000d00c60344101da0152000391041c41024040170000008281c5104228069200074001602c40411a0345143d00c030f00000d0310800d4203488038004504000c00180d00585c55000700c902d800e078030498031b01c8150f089580d01c42e910711701e42c041c64041c0d640040d540266100001c4845e208a6034801000c40c50754401d0904205134000608007841e150011081030021940000b40d11b40c00901c40c900d800002402a000050116400c0a00822040e408500180d10743d6054103c180d400c1c0044500304910310543c00d0550848002010254125001680c10001890705d9031005a0303120b100070584102ca281e0181c06821104a00c0013100030510b441c0603c980301c003040c801d5501412040c0010039080d0300e401d1034000c0310502c3c4416681e01810b10014500c11174401c1d004038001e40200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 570840953 1250 570839703 570839707
    0x2030612060c0301091a3001020c0d03150317030c070807030818011505060a05040305010f0606091203020a08180306090327090624070b0402040c02010c020d0f090308 73
    0x240c0b9945150750080c880c2050f9141005812a64100d04100102c9000c070010180d05107500205244295444116400746184861140c090f210010a00007005da44030410090000a40344190241c1102c10706100b48041e082030751414000606e890740081c40450f03101c03070040e449507030300d42d40d1080340d100d0240c00820070360001c01c002080541013041d50f409003154040b5580ca41d400c0414441c02c881d4641c180d03090400701101c040003241011001021704020364503201c0c0c6065101d89905003500e020382040000595a51000c001060303001c80014043c20380d041c4220003100294800a41d10180740002070100da40014810700303d0701e40c20a00b190642c5018058940501d401c0364001d40303c4d002005104c10704000b680b18910007103802c44a81d54140b6004154141c942c0301d0300300740304802e4100b1030004515007401e210100034803541360103000f0300c5200312695011890240306210507034402d0404c103000d42e030405644250b12034000c06c40100c00340d5149011030030f02031079100071078006000b90300c060114000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 570842203 1250 570840953 570840961
    0xc080a0311130b04031a0403020a1407030812011a0a3c120e0f1c03020c0f07050319020d06050c0d020c010e010e150103030815060a02012313060203061206 68
    0x22a4000d04120f82c0904864440b090070070780551b021040c101d4004006030230900117000054020b0304454070a000b00b0003100c00064480c2d5901809501c8404801c203e18104c00041107262191150200c050490b003032407600f064040c1d100500004540e00d00141e0a100c03a0742c003046801001f1080081861140c1d1074902c0310f8204010141414099140c0d0401d801e081c0182078070b013582d000401508500e041e00040c4280341c56142144000d1603150342e09420540c080081d0103641b10204213202e01e404c55240a006260300d0041014a401c1e840005240c0b400041c1b0641000740e034440b0720141038950041004145030351044442c2d4660300c51307100d00340c000c248003040303981c49440154080044100d000008108229400c002160340c1c0120b11203c0c2c2c3c810b01180010710010f03104560440d0800b13441007080306806407071000948103411a650000050b95114599000c54120003003030000300041240e89006070074184095000040c99a002408050300040403c4094443c15545581c800300d40f0203480030307410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 570843453 1250 570842203 570842219
    0x207060209030610050a06111005070215010501020d08150406050306130b01170a0206070503301503060105011b02030102070b0412020105090c09070e1306150c080a031113 75
    0x414803600b4081e1052000203842c900c48803c840741582c400a00003000c02c0d02c0c1541c11103030000d0824401180d4011011220709640440c021030340110381c0b940160034860428080310501310416402681194050b01035400c456400100540c2c101e640c04004122040442000c0f401500a690000e90544524000c0000814400c000300c508103110321100d45a0b41d990725029804441040e44d601c1d5030b0307004044410018a0050001d00754144200c059900348651b20f512082d48000c2110524004184c51110724005808251540e070b000c038049000d802c41000d010b010a03a103c82c14080c0505002e41c00942299200410799030794501d680c010003d41d80d4022a2520b418034074800e940880351241e90040355061140103016080c49080100e0003050600400300802a07031000c0602085c00f40500c41d02091030a807203581513550102c030301820200b291454007a040c0f582100c609006d008009640f00108001010f600c215141c8120f5403801040d10181c41d804601d040c418500c490021072218007000501c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 570844703 1250 570843453 570843457
    0x1e07020616030b13201201090b0102210a03020408030409020c1c020622051905061006080402100e0a030c030c050d0305091009120b0615040501050a051c02070602 71
    0x5940c0d810028140040c118203806940c3c15000042d40311451003124206494036900520744250016140c03a001040c2c1900c0c5c461035482408100101003491006115241090240342c3c401c0000b0f20080403103422035a840303500103002c0c6901218101c00014000840d602c2a01510050081c400949a5403603461920070001c0d07201d04980d855034040c6078941c192140d06001030810310a865000b80075580da90b44440c9100001300721070018040c50a03450040821001c001030440910f400280380e0050b009814a10303e400b4004150078544882c00f8418403140c0e6214030b45e640c000b50306840801d8203c80e003403c1600c2005041116039040303401e9900000920002c1003805040380d00078524a154143c4410a200c003a41038024080d0101c0d008100300580c0e400c0040308c4135607002d4180703485400a61160520100703803442c04815601014450140852860311140401e4000d800c0c44400b4907244c070701030001e4000d02503064044240080030500030300c10340b182d8001550203010782808550f40c0a040c50040700175 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 570845953 1250 570844703 570844711
    0x11060a1e020d1d2805070f030308100e130803090127030f0509010806010c05070f061116141e0d0b04050f0f0715090b03090a03120c05121e070206 64
    0x40c010000480c112200c0203c1c0c008404661280c54501101145503a4140310002540c120717120301c614240010f41040031001103018510075a42d1800c1824500b00a02c4032a1544c2c0180d11485480b400740801420101c0c00440c81903880b140d0241c80e40c1d42c040c800c0c0e005200403d003052005c0444000d06941003126158640100c0c843e84651100c510440c4c02140c0e41c0c014450303050f0200d04884040352541d030082100d92002c501c43d030101c0d000306480b1204054090f02c0d40d400340012034000b0b601030100c02801e0098000130034046404d1a805031602d200114540b002081d204d006111702055010740005503036510114a40142004109c200c2c14903000d5145881103606841d6401020482e00c424540030a215100003d200003c10029040c501d0041c030f9428420111400d2001c0110f00040840007440654070840491001d0b1010840300c3c28064100403606e40340f80c01d010b14103080100b0b1340d41c01c2400d40c0c110098130340785040079949018082c1404040d5440e410754452042c405c1140c5a43d00007105481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 570847203 1250 570845953 570845981
    0x60a0b060c060a1b02160e0c071a01050319020d080c030408010c1713020a03021002011d01140105190306150503030304140708190b0901110c0c01080711060a1e020d 72
    0x1d000d42d02d04c0c1280c6880a140e494806842195410441000007071880740d0420018016245000841d03521400141c602101010010300180c00401c4103141c1844081044a11801070702c0310201035078001140c462403040028070501021a864056041c1042600c02814401008200404140c0c202900c150f00d03446006000c80c4140300081c0c10101c0ca010a806003e502030f0011400c0c074156802c0206030b42c130101d144d2085641c2c514800c00034601612001042c00c008070000200713040f01c0c0c01c0520707040390160042802415a40d4403815403a01882514003107a070808000107a011400142d103944421aa0019174507100200a100030f01c540200201c0e40401ca0384112481c050b030740d0850548604001404c4a403480854410308085081006025400145a000010382c107950f03011101898000803503058199001401c082d42a58002040a80048990030180d00010342c00003400daa50740700514031030a49456004400e5100b100604460080d40d081d44259226817100030345070004d201d50160440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 570848453 1250 570847203 570847241
    0x303060f0f180b0f0d150606030e07030f030c17030603150105031f0b061b0d0503190c032d2003040b130501090b06040b04060602060a0b060c060a 64
    0x1104000320034040308454641c5620300701501c1d040380303920040c0081030480d0313040ba00c0b10f00d4101c0240d4407080c101301d58520a0500c25400e00188054030200c40c0140c0015003490b1820150202208002442d8011603030321280c4040b20440b84d103011141010490002050224a440c03107110007001580a0b5103d120250121294290b44e002c83d40c8107241c0a124598242e00018a04410700c2011801c03610f005511250214080c900c0c500031039015030240d400d0034070a00c000307140a510410180084000880349103040c50560900c1705587d5140c00341c0082403030840d507483c240075800a0080c0c2240300000a0402c0e800303000d10707403581e00300d48140e00c1107a5607510030b04c0c00c018850107044103c6039045150010b21560304541e101c0e0340b03d000c0c003c0e0103400551000849141310780003520900942c0c9519104e19480401c0303003000c6080c04161079104542c64825820007105100460780090380b40d5001d004118040365102c0d81e170b808070b08144601a0b590300540680d408105500c0c107603400050f412900041801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 570849703 1250 570848453 570848459
    0x240f05041103070b0f180901030b18060c090d051e1b01051608090102031204120f111b24040305070b07050d120f0e0607080c070b1812070303060f 64
    0x2d03464901c24010145001e000744255a000342e100000b41ca2219045680d0184501110f0001501307000c00f64012900c000e00d00d030422076619100031003c1d441540ca000100050700380b040c00217080d8000c04601e02d0042111103041401e103c0100710340c0c409010b0701410000a05850603070307a5159a91904d20881c00800403280c00309551103003007154107462000e180d60b07110400680e501602c503401030000764114801030103091524240c0440043c05030b485284011400b40903410050191401e603d44407044c040c1c0e100307a0010031a800300b0440e1142440c000580400c1c902240066414204500c0211056a042401d10100480c25008105817030041084941d044c0c2d0f030740e800d481948114100101a07410000e10401e00078094800240791084056011540008141020081719115004900c2580c0301c102806070071a0410703a690340000d8003004d664641805a10ac40310508009070000a0f000007400890024070420300811007040211881203a13600c1d200e08004028021034080c611182880c4a000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 570850953 1250 570849703 570849709
    0x13170607080108070b0906090303130f05040b0a0e0703050a150905181903030216081602180603190f0602030c04150c02130506010909020309030d050a05010e04240f050411 75
    0xd0401c80d1005c403c420b00c0c0100c5241840007540041c605d868241c8010312402842d00d038010203203c0503103601001680400d01d008204415556a2140ea901444c4120410722103190031000d02907200050303090110b02d83e258003640070020814150000184241d4040100c2c0d815010b4001c1c1d0300403500456a400031400010b1f510b51115030030349180d1803103940c85d446640003d000e60080c045501070044100c0241ea07141d203805410340d00600a030000034040e004104114500603264100034601801240c03014900400807076036400c00030140003d4901250111800c0054003125000019400b440c03c0d901c0b818a0340f460101a0440e006841c10280d00144005a451065181d100704680003011014800c0703010303d00000030071014045604200c003055003c41c40340d603217000850280000000071641c40220030500c80403951b02030005a00f990400004200304851020041e030004d802141100254100c500ca0b07035000c1d0300c0c810b804200c6038144100854011615400b0074411030207030308216000e603410010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 570852203 1250 570850953 570850963
    0xc0c0303060801060b0a0f18060e090f07053a0507090b07020307031101180608090d0809030405150d1b0806030d0914040b0307033804030513170607080108 68
    0x10702005c1001c01d020309900c1910a105451034440b550901c9900041c01c1d0518208810300b0750080b00214500e00701a04a600388070014680c000824400001c003401c004e0030052a034802e051915114003004100806104004411902c0c0c99045c40c2e0840315104200c00700d070011b482d04490f040040703000d55a00007800c526840440b0203030341c3c1c000d0292040360b0660780c0d10100414001020b504100d000c2c1d0046681c1d00d240c1d40c0d0303c40a8059611550b1007445c280703e51500d4101f8900c0407004111001042c0308645030000b06070f40584c1c104603245404400360320b00741e848034000d282c00c075100d5500300186100032000300b001107025441699141110390345c4003020325a403000d00d000d4140000717840b10b070304100c9a00d44014070749901c0c200a10100301c40c2c4002d40068a001120313081031704c581c0c49800750010725110b00820340c44804c0000e032a0568042c0b04070400d0341c040e01c0c02007001c0d080c01000a0034400d0388413007080241c0035241d0102410008400c00007141d54800301100c0e0032021500d8400041601840028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 570853453 1250 570852203 570852209
    0x10609062c0f04111305180d0507150207021c030e0f0609091b0a02070e01050a050114030705040306020c0309090901021806160602040b18010903030e0918010c0c030306080106 77
    0x1400c900e482d120301584280390300500c241c0380400c2021202c0084da55200400c48000064500815182001c200c0210066400c031030704080741d8440044c0b0104590803c3c280c500c4190007940f200c1908501407400782c042d11a20320000d40c03040302d10845004107507814000d4041c0501070390750175200b0500c04060007501c070a2070418980c099130a001c0e86240345442c0400b90b5008240380c1c40203460001c005181115a003001c40d6000241e0400407047c842c840102c00c4881c01808202c072000b06040c0340c600080d042c1c400b81100e40500100010008040d036014400b25001107900160842d560804d41c00015183d40110300218401d9031281c01140a0203414001d613002016000d603075495801502c0104005540140258a105408200c03441d01003032081c40500000e103000d2080e5a42d99440203144503a109d12041c0140c14401240403c0c80400e5101000800901081c0e4200186448007403640000300d641903200b181c907608207126110096881550903011921076102841020780712b0721580c0c283e0351a40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 570854703 1250 570853453 570853529
    0x708130f080f0604020109030204090201110f0d030e0d1e05160f060f0e0606010e041d070806090f0c04020f0d0510170105010b0f0f120906190b0d02040b1201060906 72
    0x9503082c2301625040d4401c40d4401c0c41410007a41c6404400d4155082c910080089001c0b90840901001c0e0030f42c01d030046140880880c1e002d0004108030000c084c1074401d41040b40b07092007404000e403002642c069022682e03240e1002d00c0c2000084014074107220341c2416200f0444040d4280040e2040100c45405101c449501030f0014010641d100b0700110749142002e011254420b4840b4941020f01040c458082c0e01c038080e15010b8444a82001886450302d6009084990994041d101c50324042c00b01041e480e5811008940159444051301d6894140340207041040c0003c0c2d140c0301c1403000c00316280e14a6001c8511601c17060383d401141c0a0902c0c200e0301c09229001811301d04101303641604040000030048440e10322011401e01d400185410078050040326180c9250b400102440005020340010981c0c144007804148801d800d00808a05241052500240a183c94009282c6548d858144201c07403024000c00812406a8540341c2e023001d01914800c00f2228460101104c1c60400c1c3d034204281001c41030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 570855953 1250 570854703 570854717
    0x50d030b01090b0c01051905161101141608060114071205040503100e0f0106060206042306040c05151908040203240613150303050d020409060e100501110c060708130f080f06040201 79
    0x66041c3c1c3c91a101d2050160ac035540d07046282c0025011030f616901852012001c0e009204d0501005400144090001da040c4061812100030000c000f10454650960040b01040c4e071031002541980d040c0174580000b0340c107000320b2580241c44042540b01d8403e50071607200300d40442400380c071424220341040c069500103811200004000c110044590310285201101d02400c0f20b070001c56440c208030069508a82040715410100010301d8070800d00d4080d12141940705207090741d07000c0e28451407a60050000240080c4c1c6000400b550f50510018040ca105502007048003e081110445004011109903204019480010b404003010348580391141c20040031a5000c1c600315102565241c002c0e0b500301b04299001c00001ca01d002e181c2c02810010003140c0500c10039424800701020200c216600300a042022003400c0740c04007900020100120a02610319603916405800d25480601c51462614201e08041d0400250000d02c0c010110071200d00e1402e07686640318061180d41c41d203030b080e200a4001b540e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 570857203 1250 570855953 570855991
    0xc0f020a0b090f0f060115031517010e030a0c1502340602070f140609070b0d0e0a080307080f011208090103181b0b030103050d030b01090b0c01051905 66
    0x65980001d811a941c10704850400144110301464a002601040c2454000304010004c035461f03d02140c03503104413810b09100c8283c0a50024140c0e802a1140c480d840c0340055801d03005401c2940951580187d0301e0603240e0750b0032000b0000e04000c0c0f14090072034684000c4008101190800e01c00d503401000c201042120041c40400c0787da80e8546c80101a40c400c420344104840052614030040040d240300d11050f0302c0000250a20010411100c2d41d0080e05800490410241c000d001c04c000c01a00d4041061948030307020644d50b18000c0c0880303265191584500714590082c0701d950301c0a14407a030869035130a06142d4401c00d81038032022080c4144580d071403000c80d881001481302006058007003018900010110040c80d214002d801401200f96800e8030a1505102e0762504c03900c400b800303440344981992a651455031415500c0f88046000c004161b903401010195078440c0041000401003c1507403512114009515802400b00b078440d11466a210764a120b00010f141c01024402c02c00300c0c0c45a80d074550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 570858453 1250 570857203 570857213
    0x809060402090c0c06090607030b1f0810031e110d030206060603130b0a06031403161403042c010f120b090304080106170c22020d06051002100c0f020a 66
    0x80040c1c4603052000c81848080c80d84c413001c2142c0ca01c1100030400905041c00c01950280031a03a1b1031132120b000341e004e0f13592001c09040e042003200035a5011f20309007079540d494019a003100c907425040240404d090400c11441c1c5006c04440080311030040c0850004107071000108901000c0031407005025802c500001107040ca8030300c0185a00480181c040c04c0354980c140e903141016070003200c580700c8592f940d0341c003403007407010f6403104400503201d40c0001c5240482e000c0b01602040740400d0001c0003120b40021520b810502802030354003e1035900c00d02c0024500ea07484040f13241c82c000c03244165009007540000b0716111001d07035100403101e0114422a6445030340c2c6510151100090a0784140d210800000401e841e09200d248000d1084031029400c03d0040134529050054142c0e019224001110b890107420342e5100000d012903405100040e42d5000581c00310020b08070a90010b030307200703c15000417941640c01107244900001440d504121002c00d028003607501c0003440c0401001a440b00300c80300c002035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 570859703 1250 570858453 570858469
    0x609060a03061a090f040c090c02030d05090309150d0b04060f0603020313120c03090801020901050a0c141518060c030c131505040f060806061903180818010809060402 73
    0x7010105502e410f40244004203000e03810903a007950405c1014030422007800311a0345000042d250200c010b014000e042c41c802075490080b00c0c3c2d150042969103012600300001001100d0070301a018048400c0c1101080c0c03005410380080641e680f00f1800d1000300751281c50a0b2043c007054580e1a14041030860501c0005c40003508002c0283c1340d0603401c20300b840003151018120011728007196070b909400d800b040c84c00030481d0480c0d6200e0031844e801400320300102da0f0040c05507042803203949032968401300c85080c440d60074024581108168003602c1f5004060160182145210b01001d800780c0c0a030505180c043c0b943c900003224600080d1505002040031180310744024011804210000180f081d2902e8090303003918248031000c0045400024100721322102d00301c405004128508260303080341b82600c0844c940b4031851444085c1501c2d0144111901c0c0e000b640a0401c05903941c0c1c3ea00441440d61405d581c0e01e42c0440c000c0d441070750403c900b0110a46c400da4245100e030040704050300c0b0980365070342401040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 570860953 1250 570859703 570859721
    0xb03070807151d03150a0b0415030809030a08030907090606020a0308041412041d0105090f0103170f18010e03031e0c03220e15030d0e03190503120609060a0306 70
    0x45443e0a040e809990b020040003041c0c08a0103c0c0e83c565007010070b1580c046542054070580158140814030000c460641c400a045a401205a6a0780e444490001e4184601507800408001001c024400c9050740040d41e541034031103100c030400419855440a9aa4445010000300000c2100c00040c0000b2407054010444404070300071a08180b80e06031408649421581140300c4241c1106040c68000946c0d90240d4010179080e60311151131704098100c0d030141041404003030030211002c601412889001c00813a10401440d1041540718500908140d280a0090030940e000403030f90424014980303400302c202c4000d1030310081541c0d203500b503c01007421241c0050000f0507081c0810700608003081000440401820410181b02c050381d13003080408802c40101a000ba454280083d501c40f03a0f03510005808888040d550404a988003080780003c1d207400c40842e00844080c680980d080301304840000640000c2031000d290701d85954404040c0704100b40200c44055000d6205102040401e02030303803090b181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 570862203 1250 570860953 570860987
    0x150904111207080118061b0206070e03031216020106151b06150b0301080106081207020f030a05070807030b0a0c050a080c0403020d082503050427050a0b0307080715 72
    0x503450355070f0991400c5840342005030b1100c00700100480108002c0788038040713558907000f0301c3c01d0011100c0031009640710001070500052040b00c0c0240c525643c1d0030019100200c1704507562804528108092427541c2950070101805582030610100e01800c941c2000302d220441d80d5900795012185448480e005054044180c0d80590303914125000081050100f1011341003440105580354907105c1402d08503075541d880118641c21452240030b001498070201c5004c1350301215041084850407002905050481100608900c41c80c00e002031148000f01f021421203020324928041956075200c00c00a8030085120725001035070401c02205118010880150404d98032900a030406860790b0200e0036031000035809940403500031481d44134026810340b00b049681d2025108040d0f0101c540d038060301c240114013807411840003860b2a0f252044000010740400030003a00b0600142c20044a01801050440c000a0090141da00c0106401070000b569804445020a540340e080142034001c842c030000d01c07011010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 570863309 1106 570862203 570862213
    0x60f0e041512140f120c01152303120307180b070317130b1503030d180507050111030703031a1801050126010b220e1509041112 56
    0x4405c0c10160039251903014180c890f9014120051004810741a10000021001440010410907901811f9040c80d0030384000309060f144c0035041c040031041602000420301c81441070014511481c50409000c0045841c0c1400c10307001da01900c0305400058081c0906603142c6903035000241c02498002c8036848642c401d54484451b094000c10200b5034685c040344c0761481e034130b0034022a0201610040f0411681c3d01c10148861040e1510f80300343d649108042e0045183e5000d03510050590210350002c600b0a002d950f011005045a60240000d4285000e503883c4982c80c1c01d07105440356210014204160740c14080010710041c101400310020351580480c0040c0101c940313202a040d0340905d00300e25035641e03080c0f07041c4c203040e11507600e6010070760010400051030042808441e03000391204101c0110030541e076820400d1000c000d8a02a2014070000712030499480c01c01d208801d42c2c000042654 = true := by decide +kernel

theorem cover : BRFrame.Cov 570683453 570863309 := by
  have h0 := BRFrame.cov_init 570683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 570683453 ≤ n) (h2 : n < 570863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
