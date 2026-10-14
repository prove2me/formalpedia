-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0288
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:58:53.260295+00:00
-- url     : https://prove2.me/submissions/d3ea4c6e-a782-4955-b773-249ffc4d19ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 51618708 ≤ n < 51798565 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 51619958 1250 51618708 51618719
    0x6060d050c12060a0518041103030307050705010605030102040515280306030308101a0a020736090f0201050d0b041401080d030213060509030f03040303020109150b0112020d06 77
    0x581441072050522454455507821100410a00020480c80c40391030104814420360741c8480d110103e0b0196404c020040b0703a580c1c640071307070082402c4031681c2d8144000720402520642c8000141540c6208800074425182e8a4040c1401e074005c50140541c00104000403400014480000d89644400c4201c1e5072800e41090360041e01041ea00441000001e441c0d150900034103070401c10203130b0030a03d0503906100140c640400300783c000e401c0801d410700e0441c0000b64000010710803c03155019006c5c20000003120111ba4000c2a40711070343c5842c4042c5e0040048180d0002c01c5a4860141d045801c6940424803100d1031303004560560107000312609607555141d0150715902d40e8480c0c4070400e02194110900b95040404103071030039001d8071401d820175004000c002c49080454256030200d4000d401c1440c2c8413520f10b0006800c040030b2403500d03140c520003c280001455815049403c4140c052980300201010000d0400103075180554424049080c1100c2e1104054040d802083c1202105e0b400080268540c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 51621208 1250 51619958 51619961
    0x30c090b04180c0203031501030f0e030d0203090f0703030f0c030507200301061e05041d060712060506040605030f041103070e09060c090d03050906120a021321060506060d 75
    0x41d003001510100b101041d6400c60002d01c00e80140d07500c0d9000079402d40c9040e01c0c4003c180007480c1c640c11304054aa144a1040a0303040e00010720100e4041c042c0c2e80c440361400f581d003000350011208041c141c410000e1260300740801084500640342c1581e41c1464140c03600c1c2d0207480048840c1c4044080000c10440316001c00d82c0c001101c2e103502e1181200460540500042509441a503045180d140f0a110304241d40054001d1080045171000e4801107000080c42d5000c10004494180e0b0f17404c140900b60400080700c0d071000300307031a2440707071000c1c02c104182e03c0f0014002c40327004c0c034025040403800c20400f080c8803408207107189510610030041440100740f2840820300b003003c10703170002025074541010b11001007030a200160384648561021070500700d0000004206c0b050051014060000c0000e002100340c6850040301e2100c25000d00c600241d042440b101c0000754481030305004640d070400400f250505000d4901d24840ca0300c88606100002c2c16110540280760140045600035401c010034070f18031115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 51622458 1250 51621208 51621217
    0x16020604031419030903020c0306060d060f09051e0706050f07030810091b120504020901030b090c06070b070206090f06061306150c02010908010606080a1e24090605060a030c090b 78
    0x10f90350b0220740f9000b00c0ca0040c0c60041c7d6403207154481c0d000380b8100300b41619051014000385412090200b0400c11214051000300f080d408054001e000e0080020b4880440c410f03000801c00d118021a81041c1c0d80724070072589409950f0f10310b03020210801c824030209226458443d045054041080d00c5240e482441c60215042429500c00325071039864054900340d0000e6141d1505003820720244203602d0b290380041c0604c0030501008080390a2180032507444070701000400101e8030041c1255a03240210700345058100800c540b000014442d22002404580020030321900781640040203050b65103800007005261442071b01c00001c8550303a140000343c8032008920640c031040e081e40310342145a910313000051050000350032001c401d0381000000c20170709502ca00040c0c0c1c040c1e0561030000b100410b956000444a01c5082d90901c11400c140c3c90002c07112030080715018114a503299054065518181c980540344076105d00c541c481c1d01448184c20543c0250400c4000240f40d1070002e00d5540c0f01c007600c10940e0070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 51623708 1250 51622458 51622507
    0xe09071e1206090204080706032004080601050a05030d020c090705090a0b041a0f090f010504050d060f050a06030302070302060c03070506010e01051305010e1503070b0406020a0506160206040314 85
    0x81c4080301c0d5100c0c40d0144582e030090030605100303602d03180c2801c102ca03549909511400003010359840b00070042d91999404c80c491500040c41e91075443c0e560380b4805070344a40c01e01626100e041c50701c200041624001030392084203001e60b00600500900c000401c110494005c0420091100802c80c100160f543d03d0a01c1d0042c2c0016428035482c2c508040016100c16209802101c030110104801d40c5560250f1054510500c001c542d000044903000004031014015a80b10b150803075a400382c4081000308075000720389840386041c8100101c4d99071805081c02da40d114030019000d81c05c05001400942040001010000c800d80220387c504001039480c01c0c40c03c0701c268000d08460b4020702c01444649860f1501500019a80c1c806000f254100202c2000011b00900031f0ad280b4001030443c076200e601d0a00015009101c1d888080f91110f5552801a490f510040401ca801e4000c08001820140c1540d000614809040c0c2c0107015960b0f42c2c3e0350503602001740c0364070089011410310890080c0350681005203020301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 51624958 1250 51623708 51623717
    0x80d0203030f01080703051b040f02210703020f0a1103070c06110607050403110906031e15010e0f0711010b0a031101033812030301030308040210020105070e09071e 72
    0x1c0c2c201007240e00450306030441000354102d01000c00c089000002c0040519803c1205006004440d100080041100b61400c0425030b0011030403c0e800d0300705410b00710103407010048820b80c5036501d0501b181284503900c9080e0b5256802d00900000621641201c50445900c000300ca00d0107040c0d850b00620902181c0c024030025614250071003e4040500c41700380c001c2c000382401fa080a086513116007600c548005842e015050352400100c09a074104010104040c0381c43c0b641002003d0380107026200e501709800c8070350f81a100d000000d100114403c046d88a10061880c0203184e44801d6030481e090300c210885501c0540d01c5d14080140b6503284440000150322810b0384a0441d40104005001e07074000243c003281c008507004000c41d0b401c040700d160b007180c203585040c4812200c98001c00101e200c0d080c81040320281c80013000110405030005a81d80c0610300803145c0661991240d4012402e80b9801c462040005e50200c3c003c2c0001c3c109140d12a80005035801c2008070f0b210005a042c1d44800d21060500004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 51626208 1250 51624958 51624961
    0x40e01020307090b0a020a031413030309052b0f08041502030d1a01020d050d090b1005120708030708070c09020c012f04031712070309060609020901080a05070306080d020303 76
    0x143c0c00440102c010400c1685240c00c1c12501c00000c0d48401ca4104090248001101024890340d02e1100700d500740817007030b03d00d031204c181c8038240140040e40a000789030040c00009800d40c00360301c2d404080300014121581c0141404065070b43d00082c41c4400b04c0458040c4000d001c0850720308204642c4a03216189a4011502d841c6600c0c569000c0d19a0401c16071042850210321f103403540da01040c82e40d0f485c1003900700650303a48200c00100c002041d10f908040e250321010030511003000050100f6000700c940071514449404480c0300581e49440003440b400c41103900c2041b2000010312507202802034503005000d5010460341d02e0b8041426603018080a2285075928035080c00002e031040c9030807002d09084044450080c0300351610380c1c0319206034040a07244607a100c440c1c0e02c9aa80c1201290701d0400b001d1041419410000005001b03020030050840d8418100103011805d1000c2c3d20035500c81600c140d41c3e403a15a160160310034010030002e803450040603103c0002040c9001c0400c450103c3d96005d600441e541e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 51627458 1250 51626208 51626221
    0xf030b0904050a060b13090b060a170316020105040e04050c04062c1306060602071a0f0304060911040c05040f0510080f10030b010902031609180209040605040e010203 73
    0x1118105400584100368800500011507400141004081da002c040000c1140c510340000d0303d2100c2c5510718020003400e11207004100200702c04514002d400039140c400c065502c032856101034190400d461500d076401840080f14909100100384151801810403914080d00d80328070f2445004c040314166402c1c1d1180d4041d080c1c6041520a210040c43c0b03c002140c0c2c01c00c49100303240c41d041d03c1c43e00d405107245582d0000c20002d9540480703412560350311000030400d6a50b210700107521b9406e2807051503c07403001400b60f01b208861843c110717007844510b1f10243d40b8694071940e071040103040101040d078070300b82081c20304056500c3d1449184184481e54444036190b40c07504c20001110780807504800c0c01140110750a221040d003110a813500b00d1440740524140e42d403841022100962503900150002c06040000a814002c40e0300842c0102102c01c0c03a103ca040c036000e01503078000200e00c52a2196040034810034a0501d0f00d038058010010010310205805075504009810340711180440c4040b03035800003d2218 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 51628708 1250 51627458 51627461
    0x4140f0109050c060d02040906080616021b01050a022104051507050a0f02030a0b0c0712180608070311030a0c090602060f060402030709050d0f030f020304050916031104060f03 77
    0x2a101504028008600d195507074546070400006014018000443c03604030046042c0c050701c015101403c0100f06c45a515604160390ba001907030601d412000c0e0f4540d0b00696403010903005056242480100c0710004407000440301035000d44010400c6010700403a10001900104150702d00315114041c003512241031408100000001c1121042404030810075000060000300d80d0b501d0307942d0864280c4090180300d001090829500900041441219104000000070184054028580151110f5600302c03001002034a551400903101540000d031410100040ca2040c14100e81c02001c034500403400d90040c0d800c0d0340040e0420303900c6100054481c202e0040c040c0d80002000014900c0748000c000c1c0d030400325116544001301400703c1d070042c2d400000065905004108010003808054500c40e510784450810103910700c0b40a1084001032260301d80d00e00400d20001c140c50079190002c0500b40c0680791a03007034460050305d2065550905890340300d500100e4081e41c01400c001d09940d2a81c18180c001d4450050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 51629958 1250 51628708 51628723
    0x170411030c0a030c1205010207020a060513050418060b040204120f0b1e012306040b12010e0c09060d1d070f080a030906050702040603210305130519031202030414 71
    0x18002c250040c000c00c04100c2004566040340d10074903030703040c401e80b4604080380a44224180603410091115000401590001c02440e050900c4184610465120010001074402000c5042403907854111180003142c1242c0c80040c1c41d002c018001440c050743c8070005140100140402da4444480c07008110a00c549481c010b03511441003204501030346554150380301c5190040c041c500b10115130307803840d100007520901440c00d1034000030030441d00d90b95100d8030714001e91301100ca00140c07044840e00014248000c1044030b401040e0081402e0f003031041b20000e20120340c010424032080c69442e4605e0a0b640b04d407601c501c0051100e2480a4000507050070704080300900b040d03005600903441001d58501180c3c0c0712171482d00f956250314105a84100900014010740f0560700081d00d800c05640c2c2e02c207840c0c004403004c0d10044000e034600388015a10044200304a08039035402421076044000840d00d03207030a4042d1901c015103c0d0a00194920500c00c41204980040310b045500610100512440950400c00300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 51631208 1250 51629958 51629983
    0x40506040e0d0807210b0f010e1e060d05180d0c05030703050304080910030e0c09060a210b042603070906081003020315070305060603011d04020117041103 68
    0x180000c00c024101c4075a559202c0310220200280c10010a41c2d9070300c2070100c4401c02907814628101314164002d0340e40280a400405d502c9103248420602855002d00c540c03200d2980024004001038000001400f440d114100f43c07260b000104101101c0401800c6c0f2800f03000301140c40c40c0b03c44c1d8134128000280340041f0402c0800600041c0c04070000080c0000046440655251908075160345039490410014011060b0b415404201c04c181c076940030398103a0023114204610000c5503244010300c0140b00442009592540d003081100d80140881d0800d144152503030f180319004101e484400d0b8450201d03c040c20b8504035844c60300c80c2440b204904030740c86c00340e103001400c2499074035504103d000908001e405203c0c081c00d105d41a000100ba5171000303100707140155000307410340c0e9491580109105d000102110220f003c00d2908001c18900e09001003036906071501d0707941e11105a041100540000c41d80180f0407410085001c803c0507d4010040507640960303c04ca20480103440510701b0076060204107580d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 51632458 1250 51631208 51631211
    0x90603070e011203120c020a15060e0a09050a080a090503070e01271e0f15030201050d09082a0105010602030903070501110312090d32031e010602030904050604 70
    0x240000e00305009154116020f80300000294040e03460b060710b4041500800044191030074201524090f004a005a2082d00c142d101c200c085500b2104881110f03101e02450400d0318240c000a0300d8282c0a5007c0816107024404440d820005681c0e050090340c0005200c00000f01100c1d07042006007000c00541c0b010f020035400c40074803503062200c0000010189407000912048214031501c0303503a0141c0c040c0d4410240e0508502d02c2009101580028110360104240414500300103071803c4200e03800f044c004d4a07070507902d89240216102d8441d0144c148004143d50b108406c00214800040008030400d1a03811125440020a00d0030382450844905900c1001590010001d81407240d401003400e1042d01c0c02420411110005260f6451441c0105508003a41070b2200d41440244240017610038407a500c140d44d011415020351a00d910307180c3c10718020b0b0703913445c5c84005814154580071014640c4404051030503a02e15540c41102c1544150031307442000580c10000e000c0030705040c6401a517501040a490 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 51633708 1250 51632458 51632473
    0xc0102010c080a02090a051c020f04060b0406080405120a0309061b09090e031209070305061f03080307050c070f0503070e0408030a0e0a061b0f0215070e010207030f0809090603 77
    0x30142c50710398020403072001e05038000340b041c01d80d5442d00301800c003810340901720249512190300303490740450414005a10031841161481c10500d00381c001c00081c1c1c0c003c0b4903d030f0f08080c070b0001c054418000281c0111542d0050450640c8103d2089000e03140ca0845a9004102d02049007000c10840710b45c1c200704c85800c0c43c9400030014264026000c01c081380c1021100103030311400c500c411801c50080c7c01c0307261040c0d9400c0050090a9000007805030a87c0e0150040d121a80c81d0100a181d400c0e840d241c02c4145200a24000c1000c08c214001841e07002c0c1c4141000c034900070402c1000c5003401c0d81e540094411500d0044140803601b001c00841c1c000c0d2170403034000d802038209a2207452860000501256090344c45540d0800444030900541d80200c0d4003007010700000780301000350020742d5034511089001881d4622010038185c4001884020307840391a40c2d03d115521440012903035100c401001605510450714008002561503102039502805184036607103507071500c0d041003007200000e01a2803080e0f01010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 51634958 1250 51633708 51633731
    0x6040c090f0b221401090e0609030c0a03080615071b1203020a140102070b13061a01050a030b0a1a0c06070903170d23040b0907060e0f0a09060b0c0c010201 68
    0x40d40c3c0400b540c55540054800d4241c50b450320140106000c949148100000005003903d003e4024148291540c0113407455640c0c2c00c618659603014080d00c656041d403100d81090003280c05504110741045024000210180303a120038092141e020803000c541c84c10704190380360007110301c0303442d00720190051910f510000003058900030341c0d0b100a15409441072a52802901c022007096040b00d5020754024415001443d0032503000d20340c80390425090758001d003003c0282200c0e140140d064221f00d081619114180050004120028840d0b070584070f802a04000c400724a01c800700640d21300492000e80001e548007582d0250500302400602400e0034000c3c2c800043c00010040d41180c20221a0010b1080e242d00101d601280036240681c40c02c000c03e042a1034400346400d1501807130340300394001d4848100c11f4407003110483ea1580d1611640000840d1a4400411403030140320000070107500030502150b45403030307454110468110f40d001e42160040003426218003d801d100c5803410a000f4002040a040c908 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 51636208 1250 51634958 51634969
    0x42706060c02131431030804060b18150a0b03090607050f04120b04020315040206090609011202041203080a0504150c0201021b0714030f0d0f090806040c090f0b 70
    0x264028461441d030040c0188240e019841900944c0c5a090110305030f00301403c9510184e41c0c002c500d002c44070020704c4038440c4500d506211134545941656541c1d03d40c0c0d200d8440500521403081d046600c004105a480050304400001601504199030100000e200c190700b00461203409078440741078414203000300300f00c064020442e26400b0819052640da50817041081381d1041c89036410201c400c442e80240101070140c0c2ca03405605c214801d50031120602e00b10038000114501c2207900a512990400a02005041500252581c03c40605000c10000c1c10540f000301640c000d034102d0001c4140c405503050034158003050881d04050b65035003c00c4203090945403251802d48017042d0000d003503202d2100040c07451003581124001280141040c114005207082680c881d00d1500c110011101c3c284007a40300380c68007042012094200c0e82c020b00900d1407100050f504142c0955018061041803080090240024808144614031803441d1090203400c2513480030898550b00102c5800600c0c0000a080e243c451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 51637458 1250 51636208 51636227
    0xd090303051801050417070314040305030a0809010207050a030e0f0a0902090102010506060c1504020a030b040506010504060906060203040e070903050601030807050d0e011709010f0606050903010c050a05180d0804270606 96
    0x11b449007a607503141a00342512908584240401c0710000050000b061101c040003a041d0399586940f088455100c1001140c246d00809501801c80d0b040340f4030040000707000e86001981e184026200305100441000029150b19255100000d45030700081e08075099079080c800d060380b01900302c48403414100000074541d9610300c41c0c24407404100d0340c0008182075642c0c55000710001c3d9488040480b00d0301d003502e8540c0e10b480c802e02c5160300943c00c00740049010000ca009107426249554010b60425107041d01940030600301500c25403d0024400780840400c1c814043d20703004e13501036408036544501178604689444080015081042143c0c0700c200070581e0311611039840b81c1c070700951100c425102d000015004007402000c2d0051589015000100300ea048005400c185000f14000c1181c1c8100c010151484d00c40c8111001c0010403c01c40c10300300704402c10a030100014041c2035001c1d02445a41e5800c0346078040d4101d6030714403c0c03c00302c0280310600c40c07a85a00c00c4174424014003019203040d00c0501140740 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 51638708 1250 51637458 51637493
    0x1d01140a05040203010609090609050d0806180a060312020313050405010f030303020a03290f09070509061b060403120b0406180b041b0e1009060c020111030d0903030518010504 77
    0x460700085015540c09400074006050441c0e800c1003844203521b072100c01040821012241d40c01544000c02d091802400e00c144030f200050034502090081c03d05c14004e0403c01004408903594030140803010400642c540c64050f07400d44c0066580d1b0007000100a43c803108d5a005034804d508140041c400b00b29000b5181c2c00300e82d81401d002d0307108d1041c0402580585140c00380b120340440100107101e5031650401400020010640c2c20200380641c00c81446801031084440c01c02085040203035588a0821800418a82c10700c1590394020300105c0b00200d041c000181c509800280108036000501042c91140d4001080221401c000161400380f104000d160303055011801c5a607218103000458486400000c0c002501207842c821103070520801800c04208624a03500031913220007144000d90280d4178110680d005522403079403120543d8011540b24200e05440c070100c1c00280120348000007140240b064080c884d80f00440c4ea450203c4943c0d44188a801a030300d07090b8141814000410b4030100700300403014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 51639958 1250 51638708 51638711
    0x60a0c050405040515040e0102130806041e030903050a0501021206030c0901030615030804080106031101080114150d0e0604170a0507080f0705030f071101080114010f030b03010e011d01140a 83
    0x1c4d03504000d6107240517007500a03500541401c20b141d00c0d00006500414100404078141118951201180d40d512a402c440007407485900600c11100002040c90030b4000034464079106e012651240c0d03800d4100034800000b10b805a40206010f210422900c1c21540e014906400170310381080240300180e64100c0c10306c805044079a0314640781c4851408038040030080e503000061250f440d6a250b003041c0c000d001c540304c29030f85540300800402c1250711a1021034102e0341e6440003d0508400d4508100004c4005483c80082d904c042261090f40c03401c9004010a80d080c900c0505500e14080c01c1505486840c2800e00071940020080c030985039410000380ca0140b900016091f407550305040802d80140305018001d0010701c400705841d00d1105148004004451142c02c0e03891414046500540300c030b410a01560300c1c2015002e140f00060751040c070301c40540662928020a0311221640803a08603404c4400a80c0103035158244510701500e6100c80d2000c41c20404001c0002c1e115203501d1543c1118080c041c26000ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 51641208 1250 51639958 51639961
    0x3040b06090601121a03030703020303010504050a02070206071e0c080f060907060207090e1005010b0a180b030a0509010906110a031a010503070f022104170703080f09030a08070501020c060a0c0504050405 89
    0x322205c001952002c405400c682d500c40d058100030350741c3d4000740318983c8240d040400103800b000c07540c020f0307510b0154054890350503c80c007942c401015140c610b40d0084805400c81000020407070b13080d00171008150450141a810010131841030503d400103140160035448030004002e85540018444d04031221108001150011448001e0400356241c0c0800b401501708400030410959140041c14007600301e07241d680101c1d042a201511924482c85800c05006040c40001c0100c0010f07040154003403082d100014000b071075542c45200321082c01110001c003c03800314103800c6141d014810603501c0c0e420102100c42200d401c81c002042884003d01030303000c0150b51003508405c40d00801489000ea1030501e40903020b1100100c81d04500d401900c00d443d03030302440340317506200843d0200d000c0c0150703a000114245819041190315040d50710154206030988201406d0348003284009000c2d04000c0d1045001617920204135040c1d5143c01c60241c02e0182483c9081c0d01c2501081d04001150204c907400e0317402003000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 51642458 1250 51641208 51641231
    0x61a24070501050106031e0b060d090609020907030e0c0a0302090105060c070f060509011e080f090309060408010b030705030f07050d062406030c020a02152d03040b0609060112 77
    0x80380550300008156608001c00410f031241c1603084003032965115a180c0c2070040210070840180d9821070001e5400020030084c40c141010b25400840d4041d004140104d19070103258040760312140c1c00c462041c0040d80e10f060089440341d0900541d02d0300c0100301c0c0d04c0901c2d2402d603000542c200c032040c07290500c56900010000705103103051082c00c1c02445034140e284810fa03900c24011f031580e8088a409800110800304901e01d444810300485c00d03290440e41c505080c1e43e01c198000004520140c001c07c0241b0080c0998011552440000d001030f24003440042a400b00c604185450030f40c4a8200910a80000030448600352002030100c084800c200ca500390755540b1803c0040040034000c4845150103955034000000a05090010341160810754040280401c0103400300d0711240c8080000b0361088105000307061129007400a0940169601040c203901c0400e02650a03554105140310900140f0210070401404414041c040e842a0152081442443c0100c0020040302d91103141c0c40005640d841301c480d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 51643708 1250 51642458 51642529
    0x519090f120b01180b06030f090c010504030503030a09060204091a0a09050708040b06010905090c07031128020f101d01030506060a03020a14040611010e01200307020115030b04061a 79
    0x180c540c5d0140c90079640c0e003042002c2c1b1010302d60482c0c811541d071044820b06180b5510400841d0112a001000b5509540700d10020802410700101c050b11503d0b000c0c4008221120684510b01c0080d500140842d001606031040c814108030b02d9100d035600c98030b80020050f419410950b026805035010303031000f0b00e5660304401a41e6500c040d40005410081c1d03102080038003051403004000003402a00c824840300c0c0104409983c4d880e0300010450703024031034058920061020f0b6509000113200514641c0801d11007004030b026690700049000c00520350403111040c000418400702c001420070328007484146080f202061341d07407164420807010554005140800f043c400c3d000345020f540c0d4141165560342d070700e00009105500703090400c2400d510744a804200c10b00e0500c0f6a0358421104032482c0d404d42c1403d60000040d400080c0300b0802d41d52204e1402c3c0c0d444140b40514006940701c0d000308100b0341007901300542103a148540448408003051180c80017599802d4400e106007200c015100a1040007044460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 51644958 1250 51643708 51643721
    0xa030210140a09050103050906150d03030e06090718110a120e101e18060510080105100e0a050f01032402070609020316060503160519090f120b0118 65
    0x1507008000c103806016680c000c0040c0b003140c0099070144203d4980d0f0800304d454001c159024415100b051100032098200f1514010083c0c0c041c1c1400903140100408540c2800b100710340800d1310ba00704d010140101c09182c0c170280b0f1410040c090800c05000034405000e040c0c842c0143c6e0f40b09106007001014091016500495460305916099954081c2c44c80c2c0c1d0746011b070030704840004000c0c0c0d503105550802c45440c410681050740000348044181d807a901c603a00142000b40440b410b40c0702041d07020480c1c2900f4003409020740b0000100003000c52410b021030100e4103001c1e1115003010b00b00f00c1400400045800d90314150b030b8000c3d000010614200001510a10040910342c031814004200c1c0401d0112951000c134000f0300039400e50703c51341501c4420750003066590003084042103003440424003a101d44c049a264000d07860404624041e50007403d9210000b03041f20203000601ca001b0705210300300c00c81e403600009203c91031b0b200c9460320090751000385840d8140900034602c4801118000c1c640d2480c1c1204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 51646208 1250 51644958 51644987
    0x21060504020711040f09030c02060a1709060108060a0b01050d0e030c010c120c0201140a02030a1503060207050c01020c1302030408040506030f10120803040303090c0b0a030b030f0109020a030210 85
    0x4540e9000c96250050f61880c01d800f840b4400c5262901d100c0fa90341150140824032a40350359452280c0100d6030030024580c01c00f451031030401c405141c082c58603065284030603003c0c01c03102c40204003e624000210780380500041c5540d404909024489040383d0300f01085d1000176101c01d40106042c018030003054918040c424506166600301070381403030442d80109009002c0c00281e0018804841340220990031781d200c2c000710000d5007000324000340010301d203540511b40044d1002c20205007100c01031401b45514900d6082582d0181d03002401504000003082040e04615080c00545540503c800000c2d14084074190b00c1001260000005000c0081450440c0c000d490024000c641b05d0a10014107000f80700e080320f00fa000042c10300300c04280134010000b00070340950b0084009166940b5070ba01100030b054400340c00c40710300c2c2d072004001c1240f9107104003501408a40d580d0000300044800c0816150116042200340b45924101d14000540c451050107420343c4e805580740c440d0507070042011101d4032040d03e0725 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 51647458 1250 51646208 51646211
    0x5060a0c050d050a0e030a03020c0108040809210d090e010b07030e040507091d0105150903010f05040b0a11040305031e04030f060f0605190e071206080c0a060f21060504 74
    0xc805503180c010f0040d00114420b175461050040f41d4000b0315566003011603001d4054ac3c00161002d081c1d600c1030240ca58050720481030716003000f000c90040340011f50a40c0005195104a4526102421040007074001e50003407442d0081c0418680809012412010301030322950610024040702414010740c000b6a0707010020384100150320300a48010031840031400341c02c40c0001d0441c0800d135503d40690025044c1c5000800340700c2d5000d00c1c1d08001c1859880440c2258040d5214a02040d9506461040c9031240d0b0160112000c0c504e4507aa080c01100c0d12071004110303111050005001040001080c4c0c0e50542c100b860741200035001d0811055540280d51000304040484001d61080007a10b03048202e5040075a603003440100e444504101041a42c14941c0d561075484040c02c00150000740480342c1c110300e10741444899205002c0010040d90030940000030103500c00500040300342090841080200428900740b800c2c89811170f401082c403200a0502d451800d0380402c1a10300400580c040e40040000a10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 51648708 1250 51647458 51647473
    0x504030506040b01050103200a0309060b100c050c0607030e06070f020306011d0105090105010c0f060209061812030c0304032a0306050a0f06050a05130204030c060804060515090105060a0c05 83
    0x3c0c021490340c8240146800281050000d90000d064440808650260070301c040b810005540c3d402c070020180c885040e1415503c41503100c0d442d845140070300c40b44012030381d500c402e400a2410118900305119081c3d5005600410250300800e510000340700000b04101c54850307440a05041c40c00c3d0307107601d01e00080d43c1400b135540001825604005c5240d180c4441204003103441e80d8500401c000e920b001d200f25408141c95140990000c2c00410383c115689102d15401810300004c0704c00b10f14145c1086070040803040094070018920700e4180307002c2d05c80c0e80600c40107501c0e0402030035000780c0343c0c010340c88024032403214000e1a40003107291545c0001c28400034140402070300e1b13590611078040e0906440e260121460304240b110300360807500451041e81c0001d45000603c2d8035100078400b040a541c4900219180c1c00c2c4000300028040015038001400039654064840c1131030b00b814812903d01814003c80d440c4600140241502da00f0701c01c50444004450041e00c4020300c41d410b403040901303800000c00e076014010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 51649958 1250 51648708 51648713
    0x7122904050d02070605160c0b0c070612090f02100302071a0103060c090f150203250b01090212010302120309090109060f0e100b131d01090e0102030403080103080a050403050604 78
    0x5444600c1280a901203406070b20001c501643c40300064026180010410040500a48041c88142d204107200305110a116562000c3d05889500020300c0f03100c10b5044000c007006036681c800c40d800d0740a907186000300008281aa0340390104417002100074000c1765618400342c1c02a01075410b444086800400001000b600000c0a16401c102400222802c0b46805807000040d032195a54034240d0750160849031035230f41090b008104418425007139504520040004007000c002c2e1203a805e01c80a41c0c180c00c001c01c0d00c0c20707180c19004204140c200c61a850b1042c0004410302103000c40150440e17406450044811001603d824214030412209a8105000030000a9110b01c15401031044480e0b16403200c000e6a11484030584088094440e8880c604501806014a941c140001c00c0701504003403102d9403e81e6511482002901002070020404102c60010040000503005401000382c03000002c6285180c01d540250a8100601024002c510041031418519018401303c5029580002c22108240350a1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 51651208 1250 51649958 51650033
    0x180a09050a0605090a0207050604022b0501090b1b250f0c09050c071a060d051608010518030a0c110a0305100e030a0206040807020d0803090c01030614030712 69
    0xc3c03154501440c0c1ea6000a4100e08a901c01d4800e015404030152080c1c1d105c80d0200030125910104500111034403525032800c04203048102804240f042c000400c0050302800d04500c2208020000103008010780c013604064510102155107408800c07801e4103d09040c0c6001c4c42c0520070340400144100c50340065201401070b1036000004840a1000501c629a00d4824013a101d00072180010002e0301b01c081c00f940d404854110150340028090b0480c0030340c091903111140707000030b80c4d1511802c0b0618606c051001107400c1c000d191384440f203e11064490100180c000f40c0c0c070710541e00c10a0400c4000c0000000f0800000b00d5030004d5000181880c151039200e003000c0d40c4038080d04103c040c1c65498008115829100030080d80d02c10507560b0050103031940c881e00c0700007a41c1d222001c12640481400410340003d510400a14010240c90b00203101b255440d400250031101c29400c403010000310440541320340e580c001a400d00b502c048070000c1140c001d852814003034400c200080342d1b91811807103c0240e004207a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 51652458 1250 51651208 51651221
    0x1e18140307080c0a0b0304020d0b04230307020d0803090f0d02030405040b120705150c010603060c0e04050c03060d0f020a0905040c0e040506010b0c0a02030d0806040c14180a09050a 79
    0x450030354880342e40d503900840d83e03440b141c0305031600700c0f050b0401007090003c0f0602850b0b201c7d0010300813071300c510143c0e07440c1d55004508450031591001c601c0304070100b6101c4000c00608035425a001980740c00c1440d00002c60342044a00300411800001000823400d0a0034040d03035a071446038034100e074942c50320742d0006516a0060300a041c020783c0350040030300c1c0c9803401403034086045032190301802c03e1a040000748000b914402420008400341004803070098002403085400441c02080009044102c01c60001c2c50050034503a43d43c8124180801d101040e6414422030307030407550440301ca0b0240c890b40e1802d20100000c24a020750703c01002c990004004000d0b0300618880c51050114107201030701d46000100010b800d0318090a0b60b03002c100148105180c07240240201540d4100b00e076054480e59001928045c490801140020076031001e00c81310341001c0c020000058018240560000b02c40d4007800c42502402e100540c07050b5014004003155140c100c40c980141101c20300500407886c02c0040301d005804c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 51653708 1250 51652458 51652499
    0x120c030509040c110f100b0105071119210201080112030f0f12090b0601030b06040308070201030c050405060c0d02010e010903170705040308030901020301081506090a05060301020408190b070905011e18 88
    0x10481e80c42888e40c07158049601050340400c0c1c5882001c0000140584401581a4800003507108007001c507104010395a65480c1003010035409032180d00501c001800c26506034400c020310240c55501800281c1c0210749810300c00031900d09618400e1b40410100c0d4845500010002c41c40e2803d01c0e000240030600301e00d02d01c2080d0a80741401183c02203020f210041c442c030f00c80640184002c8c060040158802d4202300c242c0600b0749002810547c9420025940354051901900c255200f04d0001c940240c0a024004078584241d000300190b540396140501403c20618090b2101c2e06004005204c00d40a0010786e005540c104412a46902e0807014160007584280524005485032200c28a01c1c250722070059841424090241001c03600d411214401600e405401568155024840404d4051041080d00445081262a0740c2c64140e00d080099030003c016080714204010303c030b418013051b44c1011000c40d140c140c440940d1000016141c0449540040c0981c0382c07401001b4810015040804152514500c032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 51654958 1250 51653708 51653711
    0x1b03030605040b010906050f03090709020a120510050a09050915010f0e0603060c0d0c03140a1a04060806221a0f07030b0f06070204090503070f120c030509040c110f10 73
    0x102c0c2c1c2d00550b0b2180c0c0702d1281b000051010051410f009080d03d002e5a0028910412161007644034500b61043c2d07040071183c08009084045980506000f44c040d142c0c1022494000d1010343e820200450030050003030050548903500c034008601c407048100f1041810307510400c090301440d6154100a8003520b11482106d00e00160080401e006180202c3c1050040101c0341e1003600d00030b00c82c2d8002c4060f10843c1c4040d01419a50031140d0580380312003c0d041e00c904444c540025044002c3d01409042498810407240120301c1d0100078000b201d000646160000c5a0344c41004020000d80819190100700000007004011a8a0a403014005071200903000f016817a20001403943c0301c070400c604540060180f41d078010b0021284c036070182810b40090881ca03002620104405450741c1340c0a28540c0562803c40303c22101d02d00001c207120301c1c90700801d008032203403614030005048c64038010114043c6610051050b03603616a0b801c0c0d0b035400307100d6184003c3c8020003651000618054042e42f6071600301c2100c210310303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 51656208 1250 51654958 51654971
    0x1005010212091806030f0a03020d12111204301b050a08030a020f040b09120613020906041d01090204050108150c03100f03060905010b0105120f04031b0303060504 71
    0x100da4481614103000e80504559039001400d806a041c00f40080c01454040c02030300c1c0785042024003404000c4185c0d0194004003204101c0d00b07001403071034885121030000180782018001000b8000740440b1000c1c6c82c40d01c01e503e0162207900b854076040e058040c01b00702e401003003011060601340e59288200614042e44602070640020704c0c0c41505c00080640080c0180c01c50745020b40041d0900001c0c503044003008200604000d4007000f10003150f070054001007418640400c400500e4500300400d00d00314892034000c0e140c0340c140000c07201811805403000a00c5020f515002841c136031926480643c50300c0b501c2c4114202e03190300b010344da8001c02421005034003450400e030012030b41e1580001eaa11240d00300040c60780c0c041c0e4481001075201e4001401800d6501d4403160009203807a4520380720000756008034000aa0600d0500e4180d00b140c0400d96a641400014800e0b0480f104000740c00d107520410300c0c6583d00e41136880345000c031020400c80070441e01c00203c4203444c070203140e0725030b0007002070b280c00b5103040001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 51657458 1250 51656208 51656233
    0x3080405070e0408030406091b06020109050c060a020d05070516180b040b030a02040f02130315050915160905090a020408010509010207051905070e04061b0311041e0e10050102 77
    0x10004212070140c40440e0170004580040d025501140200703000744a042000c00920341c000c0c4020580f603001c44c0060303449021103000d201051245060114007180c11900c0c01007402c001a4a4007000301c000401d000010401c0c90030f000041c00000d480e40480801021050f4555035003090362145c2540203000b0134a894040803050805101e18222014010001d016034611170b070070400508a4140c5604c5a20703020304c401801ca1111100b200007552107060045203200e084a9140708840f4003c061407029440b69200b511000a101c407185e401000c0150b50402241403e0f1069510707188907448141c210114508001501e40641d0140040d16140c0000b400b6548580018038243d00410501a102e60401410346441d001c600d03400101151084094946550fa036050b2049242000c55081d110070380c940c01e1483d1603401944001c03000c02c140b81003c202100402c2042482c60045000b4803041c05810006843d131003000f15584030003444d81d00013011407441c0450700017900e007202e0b1188034054800c10f4010840c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 51658708 1250 51657458 51657479
    0x10f06030506150613060504060206090d0c030e0d0b0901060503010e011b030b210d080f07140d060f0b07050d1d13060b07050607020706020c0307140316030308040507 73
    0x4490700000105407948501507108041c000e41080f25038041000c11a1041c01584a203240b0011300b080d4a0b2182c0316441c003d0003a08240d4000c0c6081c0c8240c001c121440c914940101800f9070060301440c040410308000000300390380c00c0c00320b40040c118141c0322040020000054008500b510070a83c001e00074400d8071840c0d10300307031201d45850400c444034000003608220b109900c108030522004004e0005004c01d4441c11014280c50540e0501c03a40091a00025032a00010400c3d00440a020480028600b8510040c1291a542042ea0b441140014000800400e541040c0c001e05140d003000c0702c00742d54565442150354407104c0708842901074000e0001c6c0d040c0c041c4264221502446206a80c4410707501c04102d40e40107103c0d070030480c8580e11400807484180c1003029240c00c41c07003080241014145040c0181c5051034030792040c0215449511000d10070b480c0411203808443d84504401000c00203280081d0034103e000c51300f04420000c060001045c16071080c1d0303032401365004000b0f036041c9641b900a90003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 51659958 1250 51658708 51658721
    0x201902010e06071109040305070c0305010b041406030a030c0303021b0a05010f1517070306060b070209010512030d050402040b120703060608190201110a06020d0204030c0e040201171015090602010f 86
    0x4005059200e04c50086007807402c0081d90040c860300c2d1103484c05a0f5590341140211498200340c2d010380d03484440080906041c481c84821004406c0344810902e0420700081d6681d54058000301003000030f84c4113008140c041e8040e0764582d00c4481840a00c107c82215050b50b9814410042c3c41075800c18000b50799021203849258600582510482030031810701070315102c6100889440c0e000b0303100700c08000012034903611403d00504500d5000c2552645240100441d030b1a040e0006c42c40b40502003803250790381d4000011145082c40c4c0140100d000d0b502c0f400000d006186042000d074200540c1541a900d4071004a41801524400c03a01042071688801c4041c0c0d0318400e1801d144c954205440035840598050455001d04100a40807170f40903d03195900c0d64181e802070000c2840d07080d00403c0c24820054100d0681020f0000e2549200b401c3c40e1540000382144140c42c9074621030301c011008511040d82240140c0d002d440c0b81d20a00e5010030310fa12005115a10314401d00c8015481c10b0300c441c060364140d02694 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 51661208 1250 51659958 51659963
    0xa02040302210f031603021e0c15070503030108060403020f01050f0c0309030c01090809040b01020c0f15040806090a03030b010f08011a04030c0b0a0807090312201902010e0607 77
    0x11205842e54842c90342e14200c0454160b91148550b084180100001300002c00f2089a038852008a00c41d0600d8081d01d00300307219042d80090f00c02100300d50340100300001c102d18024000c54040320024101140c8940911940a02901c1400b0000002c280504006640b03030040388207078200c2c2c01d24414a0070407402c840040d0348400e5190349504c0482c010f2680100a540c20480fa042600d1610100c0c0d050b80703007124161041101c2d0401c000c80c1440c13003480d05210b0700b440001c6c28000340c0481710341440000c40f2401107004261140c9403500000d0071080720142600c0142900c2411280c50f414000042640c40f140c4407411400a400c004c5542e01c29485030000103681619030321100e40ca03908241c14240494030b400c0c800d02c000c107002d00000000c0344501e80d06c40d000f00724100413290b456104070b8000f0248040204000e00340711045104000248010310203072000106460704010003544c50380c0440c0700c2d40c0340705a038500f240704400e01043c12901c80460030f020790b40700340c81b6070b0039071907400b000d211142c014624013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 51662458 1250 51661208 51661219
    0xe010b070c0510030f090b06040f180204180b07030b0316060e0906270a060b040305100c02100603110f0108070c0224040e0a050717070302070c03050d020d080a02040302 74
    0xb088036042412503c180240d050070301080314a20038413000f04a5040b681c05641d4400c410050003141c3c1020f200d1140851383e40441071100707064550014241417484040240256a150410b4000b01520000f06e4440c0e54051891019030070300b400001c014145200e0040d200340101145d0450700c0c00c80fa0b00740c4013269442d4a035800803003284810031004e600010710030743e00162504e001001c5070340610198511f05115000903000e034207001e04404100c4529801150200004100520125200040164001140c59000b01c0d802c0d914010490503c1c44100f04442254200341300401001145180050004801d0700d0741b0315484000c200444440070f0545018000c00c0100782d4800150031f020541c020a0503944004904071409034100c01410381c0160300044201c00e011090219030b41c00c0b402280d4104415140104005149804030411403001030f00712010301d0350000c1d0703680400080403180340081d5000010307160140a9004041d4607000084407800003e11030b0300c005408018030344203035816170750041c12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 51663708 1250 51662458 51662483
    0x1c140105010f110f121b060423070504020a050403060c0e060d0903030207020d0303060f0b0703080115020109170d0f0e0a02090c0f0c0c0909030c060f0c09030102040e010e010b07 78
    0xd0303500748141c00710f05616000d881107600501c041049254030f814501d1070159540d0440e13040300d4050091a03498000c03035421007014070010508140000344100d5a0551940501003c612003e25104050340180d8010340007103042c440c1680c0040c05482203038000d840030300c4595a0070900701d8056801002c0564080f8062280000c44d10300350780070650a0b0300c2810b00518110440d00084e0304030103516002c038006503d410003448019816040c00004000c0c3c0e0b94424100249a038025110440501500705110441e88185803d540700b5003200c4641070b000104c4a4090700580e200e0640340d48440d06a401c00e5091440d41400e01600e0310a5038440b5000c0b102400b070032603240c0c1c03c220a060300940340c4484240b040c443c1c0452090000010005284200001e018082243e01404841140241481c295030010301c40405ca01d100030a03415404080341245004940ea802918400c174024542040c0d05580301140100e041c443d100ca075a4141d4076240007070b690382c1c0c0eaa50b9400c5200d120350703003000b01100349028 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 51664958 1250 51663708 51663737
    0x105010b12010905090615040b0a030606050406080703120c170705010c091505090607032102071a04030806041d01020c0606031c0f0c080904020c100b03030307020c01110f01021c14010501 82
    0x910920081002403012420318001d09c00101070340580c1d001603d08990790003041141e480c1501c074a0303004041c0b103409840c1440c81e60316007500540c043c20080050000c00c003484810030002012241203100b064510644802c8203040246c02050707420b17181e03000b00e44111400b081752000740007903048040090b622140f40c2003e03a41400f80e03c0d08484012410b21074042070f00b0b958440c019030f0300100f1120f41c000060f00e4185600381400c4d154003180385a04c160660b2400c0c0004680c1c41240203511503010740d40410105058094034014900f0780800c51415403000c03030040c0480c180860440d0080c001242100c2c81000d214281c2e800c3c6015640682010480b070343c90007402c0d18052032000f502140161a1282040e5003c00450142d03070000211841c0d0307030001c01c03029203480c0161151080d00541900198150710f49120003035600d2400c000654140f18015060002c0d0f100308006c81184a03203031100035034403299903021415050801d908605580350502c81100e500104000049049840507903405001c03000f802d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 51666208 1250 51664958 51664981
    0x70303050c0f03030711010f0c0504090506120d050403030e060a052b090605060127051216061106130507060e0d05010509071e080303150102030c0105010b120109050906 74
    0x150007004207014004120040741d10510240d407003141035842c1d2006026800e4038003400c4a00381010341e45000d20302113014040613441411349058400071000040d580e04c031b0314005a5491828001400035115422490f82c01c2688040038108030381c465180d2034101c0c0070315000c21100e03000e48810300c0c0029509018a80502e060540c8055004820b03074130190a04038459482000d58003490404e6420b03a4a500905c981560311003a10b01d0308211052100d01c0706881c1c1c032410007410205e48101071068980a801f19038400c4280500520500785410984880d0790310a00a4a002d500d4002c01c840c17401040001403105040c000c603800710701d61040280c40d10a041000503100d01c440c3e0251783d0317089004429044002030b03092080f940211502402840b0790f0340b401008d8182c40318400301318a1004d1600c141000708010010903203401462005c1c20203400042c0d640100d00e10300541506003031541c01c1c030340009640c1c0071540c010030810303004450081003682c80c0c03142003090301e00a440f014001c3d40103030300207050207108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 51667458 1250 51666208 51666217
    0x1060b0702100c0507060201060608090109030f0305060112090b06040c1404050d0c0305010c12150501120b01031107030f020c011d10140a091401020703050a0f020301060510020303040c0503060907030305 89
    0x941000d14403d0000e031101071525036503400400160f0f40d5004140409074121680340e42c400d403d04000e1106480d10f80d40141000c03400c40e030907c20300d07440700c001c5419680100318004507046524030800403006a41403d08c0b85582c19980240510710f41458801c00c0d80c403410a440c1080d0803c0301040c03400e45898240300714409080c905035221004504044002074013801180d4401060341d903020440140001a9011a5440010304003c45000e000810007a6000316482503c003010400010340c0401c0f80ac010f90260910566214040d400054204205a005040031140c599580d00711000366980c00700548101d50790001044600c00c1c000c02d01145403616440c0101b60302258503001003100412400111242c001d110f80e0340126441c041d040c0054804160b201840d400c0c02d200500c1c031107145469040e151300e041d04029094a40048003441076440c250800f40c001c22b8080c0ca150f0041c2040d1038025142e40080d9012242195104400101c1d8500024550f01640c49400600701c0300d0b107940c0c2c0070ba0ba80d0b0700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 51668708 1250 51667458 51667489
    0xe04080f0319021c1b0210020d0204080f0d03060b070804050d140106120326061c0c060507110a050a050409061808030f070f020a060e150103150c0201060b0702 70
    0x300c512007095280c06400501240016905449284c4030340900d80320030755902140c01000a5040001e41c00b0017680080c845401040410340142c1c7d80c4443d00c07506001e40f28540214117503101e070351146041484000f030900d4081070255820411252501c0313801400313128040006d000084e017444203001e40e107841550310300074611032010040b181c200f084919003500c1d1503601058418031110825010715070030400418007007540d50b11000242c402c41402528041020b00301c0c2d401200d00507d0600d40c81d489054400c1d14542180030000010340d07800d0020541d61108608480945d0181c10700011341c1050b6504030290f400c001d018113401424035003070200520408905941f0980c4801c11510300c16040907000c1c209500880c0340c40e030740b458200c03000b880e10000136024204124990f80e440070400c3d404200d03114a103a209a003c100310701c200c18210719201140d00000400f401c8040000100011040f242001480500c42807140912240c4264201c80051180d1101d00d00208507807030061918000703070a44404e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 51669958 1250 51668708 51668731
    0x5030702010f09050d11060f0103140307060f0501050a08031201060302030606040906090509010e061308091206090a0203160501020a02190e010b07020f10051903021b160e04080f03 79
    0x207a00c400d44001e81e42c003008181c0300d0790001700ca11314506034030500340000754006000038000c504154203c0d40c8410b40521021302500c9580080f004a0041401104c848603005401408003003035030900c0c90000c1500380316107841003018807030004042c0408000c0c1c5940d51030442507900203070300e411030946c0a0342c002040c40e80d010318100b0010951900d90b2160a0182c60f4140300082d00b86051b111142c2114100003102c00c01e0b61017803003080a00711003120100c00c040e038805006a01c416140340402c645d1040704c5240400d90091404003c00b4100c0000d00410941c0200c040350507043c1c031000040452056801058010380000021901605080c2d610500201d010100c5c00c0615a981880348038401302038104e03504040c400582e240030b61403c1d8410b000ba031601201c1d0684034103601480581f603840f403000e0b81c000c41d901c10f0381c207051145e000e541551401120111010443c01c2c9421042e611004a01186500c1c414824004a031102c00040864401c2c0d500c0b500c4185804d0f00f4020300d502c43e8000400c0f015448 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 51671208 1250 51669958 51669971
    0xb03041104020d18020f01090e040f060f0e1b090c1e04030204020304051b03150403030e0f0f07060206090d0203040b0c0304081e0d0305070f110a1e031b0807030503070201 75
    0x80e0f110702c00c0c00d13421245403003200b42c015501d104100007a460114070350b040102d006001d100c0300d03620b201541e8211340c4c44810708008840d01d14290000c0c02131380150384c41603890a46c01c1144c0d8000452402d10028298940e0600040c80754100440e00c9000d0f1104060800144030424224200c0f6054807510b404c0e1307900c0c0318106940c036400070b01a030340211402c903116045900c0022405500a1601c9200141180681b41d80f600e52400da541c1e500300100041d042580312045915580402e005c0f41b80c4414020040d03460902003442000d607110340510580c00113105e24400210340450104010b2885441a4007541c07819107810b25046140d08000c240c24041e0008000c00101d81004100d031051a6091981d40008071507007690040c2071101c3c0480401c107042c1480308100300a45d120813804403981983c10070000014504d15554940074030b08900038404405492030354103507040180c0450003c0d2007a900c50055000650000d048000c08400007420110107010010002c0c0c01000034591004280c030001548 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 51672458 1250 51671208 51671227
    0xf041a1519020d080109060e04150f09030302030603300c030d050a0b0406140108240402030a020310050a080c06210711071d060907030b03250f0b0304110402 69
    0x440ca035041e10025038002d00304480940d03001030b01c950060800000c2042103519001d44008480002030000b004100c60803810070a01d07401e90300c452228118407500f04030304051494040d000313610039a05d0a1203440b07004900b03400c504002010100c0360b4501488400741c80640b03c0300e0016074008821480860109100c0300c1c00000c41441818814000c0311404a90a012001030004460041c0c20079890035a850a0444890741c01c13180c801d400038415000013260302c2c080014a1096078801c428940d000e0300000900c40342c0480da401a50060007a40200800c07155103d080103010030b9544134a010980012240400900e414800b6085803011140e0304100307144088150011280b048078100081101d082407008035280401086002c1c142c10205c1c145030003044a10b003100e40d00c009100511804101d8000381070300c1c0c440e411158200c01d001d0103e03910110607071501440000218000d400c00d04090000264400d4840d01e441d00b180c0103250494a10348881e129421b802d0703003101e5240e4200e41c00700070b070090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 51673708 1250 51672458 51672487
    0x12030201020c0a0b0f06010306061b1704090203060f06030708070e06070209070f080903131406160309140102061905100503070b0408010f06050a060518040204090207020f041a15 78
    0x3c07510b10903208107034036107042007009540b8280036060754105494288140700150308a112488186207001042d24461000d1402443c0c0400000a01141c103001190001d015180c503006507000b02412100f04904035814414090240012070745040014245070110b540f890003903460401801e03002c1d000c86e1402d40541c0210340350401c1541e07490002034405802507507455200715101d410041c20006140307000c1d048060038880028034001d84050348402000c00c0d207941c0d0b0300d000b03c440c5c804c0080c80303c03444281c1904014003082040c0c491440b60b40596814000c2c5503102150040c41a0000f03020820a440d44450302c0300200300081518001d41a204c070007040c2ca0340c00300110320081c07a400044554a07800d1030803817403c3d56414a00180514204ac40038042039803a241c03882c040d1201e44c9025604d8000c03860039514180006170703070b540d0894800640407520100c140c0052601038020342c0d420f1012010b11045c0320465030840341078041410000c10070045072614508507240c0c006540d0003103042503030302c0d9407211 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 51674958 1250 51673708 51673723
    0x902030105010e0109050a0501060f0e010c05011b110304050105030103080904020c100524090a05100e0a0b0a0501021504020907030b12030a0201150e0a18080703020c01020709090c12030201020c 85
    0x1c10f010300041050315928007855520000c1d42e0b00502940d498640c010f040402e00118000c02d101061560405c50b903c80c60001e0401a0400c00074080c00401380541c03016440c4120081d40000c0e90020001401c04000048030100c40040e0360300e41c40d5078a540c8038002d858024804860b031140d004c000c41010481c04001d110340f607145501000800d420a080400504c4258600340740b03d20400244070302080e0349880342d03640c0c00b1042d0303040802c1a40d924013500e0f04102c0c450b0405200c500840b014003900300c641d580115400842030701c10420f070036112001641d40d15400b0340060101c84841c1c00040040c00c281081d00d03086021b504001c100344d4101c20003c0c0302e0a980e400c524007258000300d100c3c0b84d0305609019500031541901c0803220810300303003421a0003050008100c13412103903c075a813040594412038058015241c001507240c2d05c1d40b02c2464000e44038044016018010f2051510100f20301c215445541c41c00c580c825070704013031b0360b10340040a0402c40164500b0380665609002001301620b080c07003c00d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 51676208 1250 51674958 51674969
    0xc09020a0206071206050102060402040b18010803130e09031903020f0a0503040c05010801180903180905090f010506030a02010c061d0a0501140606030402040b130e0c0307080d02030306090703090203010501 90
    0x104010f00c1c0025000b0006070304400c95401d9141005000c02c03242c0d07001310b03c0c260410340694011074007803440d001003420850020707082e011111682c0300010b403500001c8050048040764041c0c041c0280d59908210008410940d4400344d150001c0011042524810400c00000c000606016040070a4a036040359036410650407040420000002c000400c150f002c2c40704054402404c08425550600c4401c4108030041c007001e03958150348092280030b26008058110401048681c41103626448000c050042c1c8030580e1b030f181c070307511030021480c506182c10f00a46100d04c401030000c1101e540c2d5500112074100441c901511899510450a007016280307150203801915000010440c0c03581750706d016421120a0740b03448190384403003002d1142c01d0b6a000d0440790803a07011100802e081c006180001c803214025600120124503000001324900c2e0045811040004120103668559a6030710589890362607024152005800400001e40c242c03800007a20b603004042460300051020440d13001c02d0869000f80c000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 51677458 1250 51676208 51676213
    0x6180601091e03170c0604081e0f12090d120c0e030105090106060f050a080a05061215100e0c07031b050114060a0909050d030b0310090f03140304150203040c09020a02 73
    0x24400d00c10220f071940401300660003a0380c607001d0502515601d900c800f03880145100c9000070103000318044800c1048021600c110143c0d5074400640d502090359220300081c01c2c0804d01e85000500c0400042401b040182c043c0d100c0901e055943c040040c02407103c0b030510820301c0b02142e42c190b040e840034402c2c00d104060f01000000c0050500c203024105070447c0713171400c040010401c00c840c2c0b0558801c1c0a903810081b03201000c1509d4581d07000194070040402c01040c0075204550490040101c901c013402c0c01451b050b04000301d069102c1c6c0020b041c05404485810580d60204030640000c0d02c03801d90940580c007071911180e403003070f5260380d907909480c1100703c0351036160100b4092000c00d14100c0441d000401211a0400c810403940d92a07a0f21071500540d09400e0590301d603100416070724140319001000c1070940003040100780b5442c001c494010b4605081c1d001840000102c665030304030204484c05140c04c05130701c1c00c0316810300104602030b40c402002243c40b80c015820000d1404c54500150118071080c2c3c01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 51678708 1250 51677458 51677519
    0x21506040f09142109012307030c0b01050102070501020a0f14030408011e020901020d030b0123030411010e032107061a040b030316020f0402070804170c04050618060109 74
    0x15103440e056844110f842d0340c6400c1320741441c20305840c0d01202d40c0d0f88001e003448407400c5d032100c694098141a284c030404038044006442400c01d0790002d040070800780f20300d042403407998840d001240d03030348024040d00d030250340324164040100b1030b03400060180a1060021402c1034680d00109421074120b40e0000000f60744658401c4816410261821210880004114281101c4c200000d44d5100f0a90f80b000038190303661a600c50591268050b0004502082c0705e002070f020003042c1c3e42000c1d40c07013110141c40800f100f80c2d03095450b601c11030b0f0b8080140c50040080c0401102c07107821007030800c1d0011490b42d15240410550340059940e000e681c00e0312010a00c038019401120050205544030350544502c00d400401100c3d20f6600c004012065280d010b4440f030821441800103d0001d04c02c10384040d000142c0810b000501000c0101c0c0e1121032a8075005590f141e0700004280826104250ba00e03542c071410280c013a143d010300c00d10300c00741d003d50140351083d101a9200c16089030b0b60440e02c05c07042a0015040d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 51679958 1250 51678708 51678743
    0xa020405040519030c050c09040309180b06030c1209070e0402060307090e070806030d090308040b0c2d16030f0b07020114010602010506030d02030c070b03100f060201020711030d021506040f09 84
    0xc440c3c00680070230b5990a0092800781c1d0000c05981c0f090290741c0340013891003009680c894031680a00300b1140060030f2155642080b60302059942c0000d00050700203022000000c0c01b140300885c1c040200c03462440241103d858541c01c00208d504014906010041c0f40c040000760034040c003803030134020307400c54032080103504051007414104400c116038801070240018003040043c0b18241220200d40100f04803a403180100040c90b41014903003401910b9112640446000d0040040d00304100c64218504441074515500c0c074140c0c4085540c03002818240c1a804188003103919074507450b40c0f01d2a140300000b158940b41c45003400100c07083c0c20000040c0c0d550420006d49007010403164419059500086060001100219680302c86a0003010344114000c070128901c801101e030b8070360261102e07418052440f525000028003d40003600d05403070140d00c252403414a401c2c045100070a10070030398080c00700e84a4203035002da0f06600240000c0c0d042903403080c640b10260b0f094810000113911ca42c56000c060300c6680d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 51681208 1250 51679958 51679963
    0x41104050a050601140d0b12010c030e0d021504060612240905030403020d0c08060411010906051216050c07080a0b0a020a0903140a170702120304080a020405040519030c05 75
    0xc19400e41d00d442d0070140300c210780e08511100b4074031240030009640c1c0c882c0c26601e440541130780c00303116400040480000d00501019041104582a196001c0004649a51a02d0fa0712501d80031060003503003040070244130f0428050511540b00d0300690020444c01d81d500c04580c10440115410790321210003070700d42d01301c03468008403546070310300c10301c0081c00552510b85990b40ca070320652100078401e551001c4403c04000d11444200020030140d01950b4180c500390030503049c900318000600380004c1c0d4030f0f400456814011016580c10350030000822606a8504074cd1019446200b00c070fa2090280501c0700c0340007400100404001b60018401500c02d0b5521460640390310980940204c5480d8014801c4441c0303a80e210f100c5c02d0480c2c2c1c20081220140350041e0155003414500e41014003070346500b01240586440c0d000c0105683e41c8255803105100140c1500c0795242e0103640a8032071b03103810600d440405840c0c550071442c0c10a0248040d10700401c1d02e480390b005010120081200400c00002c42d55051000c00d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 51682458 1250 51681208 51681211
    0x110313050f06150607020406090207030c0311030a092715030501050c1809070c0606030b040b10060504140a1d1801051e040501020c0105150a08010b06040b16050604110405 75
    0x1080001c28140c140014511500f42030481d003140604030204241e0705550326600400001c05007610210f64034451401d00a00c01c0e07003100c2d4140c0210b403040310729481f07001c1e00000700ca0300e8a03007507581d80310b865040c00b83c41002e100000c611134034580080e44c0300b240422002e100c1d126080f80940c8414034001e00d5858080d00b0f448000301500c1a804060140f8088212556104c201c050800c45550345107030358111050799200501d15010b448a807400201100f0411401602030050780100f030030f040c0541da074070684c00c210202030080c240003610501040000c4024008031000204c0001c4c42c40308110345900901d088400480380389054041d0a000b40a2500031074030507070401caa007180084c002464140c3c480d0105118040b030044641410300005800d00c40c1c2907040d5121460298028041d078103110440c010485481c3c22820b21030001c4000005071003c0511509030429400740010781814541038040d00c0540000c0d0384144031200002c500e45c00590203008030740c411441140c6d030034401c01c01142400104c580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 51683708 1250 51682458 51682483
    0x607030b012109031b0503070314180108060a050411030f0112030819140406050103150e07050918060a0e0706030207030c0b060a0f08012405010f0c030311031305 71
    0x107200300060450308400101820034211a0000f00d0304108901d03084810060794603021120004035100101008030110051800034004c3d0b8841c3d9018001c0c0003203a40c0c07881811110404000722500000b01540583c3c01c031540020001c0400a0b410707606d401060644264002c0804094000820840000704101105003d8521540e00a00841036680d024080350406000d007006514081c0c49113508400716000901c0d407203949001480141030515284015000a00044170400d1100001c0ca448141d5440f4010500888000600c051803030031040c4000390740e01500a610780c05048a10a0300e400080140341e000369034013500041c6190105200c58182481504482d081500411454002c0b0f41e00412840145412800c5103c194541c2c00020344054481c1c1c0c0030300302d50f240c050301c0016250010750044592025080800d41c1104240c440245000b046001d002d01180c1443c00c0b100c5650b01c981949201a4441d080c00601c00c03485445140050300211380e02180d5010341e0700d8981c1000320501034840d04d41d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 51684958 1250 51683708 51683717
    0x3080f090a050312060d020409080913180f1e1b0801020a210b031002070c08010203060a17030d1103040317060120190309050a0b0306090a0903020c120607030b01 71
    0x80d50baa029124403070402504070070000b10011902981d07510010400390380e8010030801c41d02d41146418111a04a046520304c00c15610544241104403801207480c2d0381c40b00d228003000181680c3d20002e00302c4e00b0100c1694500f11060990704105680d004040d400743c00303984c6000c2074410800da902007028894002d0071030f50740180800c0050b10b810200360090701000064072400051620784810042001e410b12590612031140c4818403001d4541c002c0800c1c50144417500c49c00c075101d400c402d00344e11040d141560403e1140008001c003020076143c4040c601030f581c040d6864070030452014000d4071000e00d0000041c0000205020030182c00c040b03804090040260340c1c0c0080c0c40d0140003e00055040101710b641880800e04000700301c00b05105016003400400c2034810728085c0c03801c00400c0d40701d980c010240640e450f0100401c070074090341e013506c1c0324010050441e105030f950340082c0300c040c1030001421410744c4122615615541d58900f00001000c8502c0c0080c0660320700f1100080544d4540103c050511 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 51686208 1250 51684958 51684973
    0x60409021e09030303010e0403020c040f0b0102070b16020d02180405030a0e0d0302070e09030c03120703060e0f13020f040f1b0e09010b0714030307020d02070b04050906150405060703080f09 83
    0x640f400300c152411038000a4502e0403981c0c941c1426820803010f00340e01c61f0302c140382c440703160b0040349241e0080c0034808080c1d08a4040034cc0f20001c6d0b01d024401d454400c06091b100d10b00b8400185015140c490a50303202401c0c46002c45092416071100400035101111075800100303040740040c0d4004035900b001d0301e044403424040c0c031650324041c5d1a21003a0203031030582203d43e000100011420002c0ba072601000700100c0b0b541d403d0307040c645000b030350f41038130920006800d1800001d4030915005030a40500800101010542c40700c2442c0111401d425104a0b0403503640c0700740040c075503614490035030614503429003c030f80090b0141d0650320760000c06e4103210520a2420140e0b21546031649094151144861225036980003030074491440c15000d440504d151200008000c0700c103502080700f004584464084405a42d1036001c504094000c41c0a01c9400c402c0d80d4000030300518000c4060f10304d698010500c40c0c076080d02e400114096a000150690105003250b0600100c031001c0d55070141c0c442170160182954 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 51687458 1250 51686208 51686227
    0xe16051b0c041104050f0d060b0a080601150201050106020607030c2105060114030106020a1707020d03020f07080723220e0c100f180f0e0109141510030605060409021e 73
    0x44030006c01040c02010801140380800c0701c40d500c900c0b10700034000c0c00e0740c0c2490390362801035550742d03024040c8020b010b420042c008a8240140152416100560040c043c0d9655200c01100103003801d00d40381080003540c881c0140c2e0880011800741e1110024800810540381500015000c002e07181412401458100010803825502146003295640c3c4100441d90649101e9511961402210000ba50250304c100040c010144c000602500a44284e010340708019503c404d001c3e11804c40303215900c1e00b600300c280580b44c0402c04004503e81d80c84020000340c400e002c1072082c1c16070340030b908001d21480d40c0d03038407080705100d8030400004134455001c40b902c1c9001481400001c00c1829000568004e201d4202100310440c0d4000354050080c2c50302c440c03401c4916030b54115500c030b02d1200f8407420348918a003507081c2c05480c00600f28584103407110704032078802210b803806001140401011035010140c2c0c445010815070b5a80740100020500c4580258561198004840c2030f0894003030406200ca504000d902c0b0f6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 51688708 1250 51687458 51687469
    0xb1209070e0714040b0c01051909051504030519020c03010b2202030915070f080112050a080309070b030a06050f090112060f020c010f0c090501090e16051b0c04110405 73
    0x900011500c0c03c1d42c210b541002e140c4540d4003468001541e211004207000c1d0301c13600151700451090810134415070a0451544d80303502281c1400300702910035040703035103908000100508200e80040c070910b8218541680c0b4681c0d541c05003d4082ca10005030494500c010003031409005a64416500711144040c0c00c06c030b0000b84000f262926501b4a51a4000c00091140413080c0310592481711040380c2c0c5041c1d80b50011000b041981c40d120b400340800c1c0c03118004580c0d0707004c0103a217002c0f00340c2c460024010031314591507010407a00020305502240c820403501040840c182c0014502440c104c84000c1241400c1c00c040000803408080c080c0d004102400c01002580600486500840e410102c0011030b10486040230303000e4464910440c61541c203002c10007444801c1a0700c00f1005c3c41c0a60359400300b540e01d4400445200d28144134060301e0760840c2012a0481c01030b50b0f95181054444e00701149800c150700b0038180c6c08515030710203000c90b80124810864a0419020709035898000808007031929082000042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 51689958 1250 51688708 51688711
    0x26180f040c090e04050703080408030d051806060906041803051207030c02060109020f0d0513050c06030603030a03021303020a0f03050105010801020301050607120212040b181503060d03090506040b1209070e 90
    0x20100f511403003c0744c00c0c82014030512004d5a04450884ea44a40701d20226550354498982400d02501c0d00c0005100240c4417503c04800280e010050000c0391200410032200700c5016006a600039992514111048412191010414825100c950716001404241010304078000c0c1031900f0304d8104005080d00e00d0340856580e041d03d40074a0b0060f2514000f03c1000018020940090030692400301400808107000325040b84003407098003160360244520003400800c1c0429120b41e50954010300c220b40307895000760054224107560461074104250f681d00010324601a07684003102d0100004810b0017841002e00078180540002c800175440c2d0351402c004154176105910014100620100000300d10070300c240019a0443e1465410b035460f151a002510156070104c1d00d200d501810705402c0343d507181071510f4a0032030b4001c085030b03081c110f036104824020300551102c000c4040040f03101c808285a0380344000f0700060200040110b07100c680450422442c8200900395800603400300708100829a4600c000a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 51691208 1250 51689958 51689969
    0x306010806041e080307030f0b041512020f0301020708030405060108060115080c1215010e0409020d02040504020a12050703030806010c0b011e03060f092a0326180f040c09 75
    0x1151240380700100140d50383c4031140140400c400209109413243e141e003240c64120032044040001003e0001048111240d0b0041c002a01d14900d804100282e000414881c855001030002c17194049030500081c03c90788861000c032040c16000c020301051260403c0b6031409400301e480145415410482e10308485090a02110100304d5424009000d0318520020343d0049215105064141e05000c00c1c10b0204007200c518550025200c845503035030a14140c0948c141881e009030046503408455004d10001d060014001d9800840034013000039101183d00d001030b00240640040c05080d0705601d001043c7c0d80000d0981d9041002000400c800b007255000c0590440f41c45810442440f40d046101a908103010f81c4050541854001806d461070110b800c0078550912032103e40303c80c0c82c032020301e001030100c48a490000c9038a030f001d010310000c1c00034140b0b0b10f0052210115410900100c1c0e921030802c1c0d0183c02c41d40303a40042d9181400082c20701039a140c50504040302c0c240407408a0000c020103c0525100790b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 51692458 1250 51691208 51691223
    0x190806030f1216020909060a0c020c06040312020f0303070503040c0b0301051c020f03030d0e070b0a02070e07020c06030910050106031e110906040b0310120c0302130e01060f060e030601080604 84
    0x1515840190350003c510b00e40e0b8040c08185061410001d02d58440c0400c07120b440e44542000f00c00300c0d040d4408101c44641d044001d241c3ca0a02d400c0d070b154070494001c81040c2c4000c0d442082c0160084800c00c00186200711150754500741d0324607041c80c000315030665070351240141300d0042c07006100c80c0d6200c0548101c1c0f41c0d80c0c7c1c1c060a100e030205000150461461030301c00c541501000500805a19003074108281d406084c0003120302481d070703407624141d10b44105109480145c001010902c41c0c01050406140c000003107104880384015940000f80340f607807082d9416522340d0301001440c00da05250b0300840e4014001030400f002242040c0f001c0001c0c0150040c1c40c103211680d0b0b07203c1900e1982c41e0001b550b16100000d0411600d50f516007400c0b84103a80305450352407038034201c1e2000040c400603003000044036603402041b40504a24550902c241c13244000041d8140c1500c507a041002e011017480f40c040100110040104400d00d020400b80c01100b641d20480e010380c0041005002000000032034582081e0f10554 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 51693708 1250 51692458 51692467
    0xb0609040207050c06040902130f0501020601050108040516060302091036080609010504050f070501021b010516080405010f0c081213081303120314150105040506190806030f12 77
    0x20210f08000003009405d41c00540850082141182503020f00707a103100404140c0742990311100510400d07103031807041a00503407005006000d25403040c902d2a400ca0b114408660f0b91480c021104920b86030280c03c0503001a9011401e015240b034081030300280380440742400d0030342c0000580b42144003c0c0422081c072000d090000c80b10607604e03008214100903c540c4040d10620b007080000c00c0c0c042c04c41136405451511565210556200000c10b8850803204160010701f02d085050440c829071820706200c80781071050601c00c940d50050b800b0954a0aa031140d03070301558a9007800000f519010101265004002030491041f0005880508460080c05c1d5480a001030744c0c0c0700010345110148403440180466004100b604a1a00f1042c60340140c86c0709060100c20306040300c900324201e03078040070250b910004550114100c2c22190b40f9070301e60440c041c0340c928a007540394008500700f0390000d2800000c62203056031858601d0b5200111541007002140038210001c0514005030b500c0c0d61264140b1800c40c030026 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 51694958 1250 51693708 51693713
    0x20313031d03060c09030106060504060c030305070318030305040b0a06050105070f050a0c0b120c0c030304020906031606020609011505030604110f040c0309020306063012030f0106020706030b0609040207 89
    0x5020300d00348004045805616040d9400c1641d1781040810500960030480085400ca020302c00351819a2030307554440342843c15686089010f044060310540c180b542d5107002010f881c90b45414a443d26009071000700f00c43c00c1610b85503000c0d80300101540d0900c0d15201041c007480c2e82c030408903816141c210b100002c03030000e203081240c18030005400052045000030000a2813101d9503015081148000d403000c4e60541d07410101c5a028454200d40404540082000030018502000503682250001d800c0302c660728040d82803050f00074580e40041c40940c1c840000c024528100b4003a03024040304202801c28610314020100340c2d034103c080d000403c1400c12800800c81034a400a404503440d00042040c0500351340c1d080050300611580340d00368001d0050400203042420202e00210503a040640b298540030b02c00c00c00ca554000d0303140343c680c6680c00381120141d0000c01c024017440c0a464500700301c6100b54903112010345011441c3d845030047c107041160702e1240d50b407200180e0b66503601c107480151703413504e403403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 51696208 1250 51694958 51694997
    0x8090c01031a1201140103051605030106060e1e0301052a0a02030406080c0c030a21090507062006090106050a0f0e0a0b0f1f030608011802040c02030706050c070b0a02031303 76
    0x81740d01e074003c1d441640000b0a20000259850013131111132401101030740c5070801d01d82a40c0d464080c8001040490002c50102d00341200090110342058808480c2c5c020305000003400d649050702c004404080e52180c54812502d04544c00590350803403030500d4a407501d0a40042c2d2a0f0255120700020f10003030b540000c000e10b041c4012105544100015240c0d24007520f94040d2440c86001204600700c20012940030201c03070b07540b24440d001c1d0b400100601d034052500d0f0044610101d08852a059150f840d14440d0303441c9070400c50180924030407000824250f05110520060907031607031100794001a000410004902c8204a00750004401040400c0e80786458021895901c400c0c900c2079004000514000b101c0f202c0503101200050080d0350a20005a03100310b141d09840743e0012100823907119150301c1c001898a0303401700442d940300703006580c10102280c8481040300c908076a44980076100090340000c2000c03000031541e200391400f80850840c140380202c08031000300948001c0034848070013902c0301c015036007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 51697458 1250 51696208 51696221
    0x140c09030f160e0114010207140307030812040b0f07090501030b0a150206010602011a03060c0a09080d0e0103110c06040f02060d0204080309040c02070e0a02070614010608090c01031a1201 82
    0x103141124850601c4000000809015100e50040d031000d041c000300305174451449000410005900410196003041c08940c008082c444c0300139494401c0d0100080001c1040c000b40840000c02d12007800c2510b81410a4070380040001e01c0b24012040c030314100010140c012000000395582841c1c0096a50180e1011174800f144540291001c811344090101d0703101d030700040031810b0710304650080c4101803c00b0150010402030107400c3d60305402c15400100842915005019501a28640101036603034420003281030004039038400c030000340c0a0b024600c8558041c01440603040c004010300e0310b46203001c022180c4440015000034404110b20340b4070002d6550703180a607040500420700842d40d07565102e480c1a920361041d9000f5001d1420021080041030010071400200c80c848403140100740d44000480c0002e510942c005c9a0540d5198020b10f00b1860700620140070313040076121506c1505000c5081071520035481c0d181410103040848800b841f9803803100c0d1194030b05c0266110111080440c108034058240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 51698708 1250 51697458 51697483
    0x105090402032e2303120a05070506060603040f080a030b09010f05010e040203070e060c100207060203040221100c020a0506070801031202030c0604020d0206070c030305090a05010201140c0903 84
    0x482889061040c4481e1000c9a0b030203031903a4403540180071101d00041c1c0301e610400d01c10b050501d0049089002c0c1850b04541040018107541100c084046c80e00007540014100800144002c036401c410090200328050700070608864090075490300d030344c1c1c05850215810008080c10000303d0714032144c40c003a801c00035105900130011181581c43d494281c080318140e100b42c0d1f0002d543d2425900c0076003054030803a0b008071590b40e542000e046180c070600207140d00ca0090030190348a40f002a41d0354401c0c51010f4642c4521400016070b0b2400c2500400c5511204010813503c1183c1c3c00c446840b0b141400221200c0015001d100890019400502a4100b40c040703240078100d07020310700420007040c0e4441c624034140c91081d80100e40c060814170007281d581c091400364941c1036101c64003181c054a03080840d1101948024011440d1030026512402400c8860744220301203030000c100b03072001d450007400d1903018010070302c02007243c0400380c0081058290064401124410001911348490700c00b0300c0100040007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 51699958 1250 51698708 51698711
    0x909010b0c010c210e0a0c09060509090309030d030c030b120a030311070c060c06090501020c0a050f0a0f11040b0a031203050105090705070312062714040c1401050904 73
    0x180d59409020050780040c500d060103500c2c2031004904540a05012401c100d801c2c4892003101810000d03540050003e01c0149000d40305244146000980800c2040c0152102502c04200e451400303040c48078103400544215116002404940c42e01d890008414260b44410300c0c2c0492003290840c802e400a080d50100b280c0c00400c100312100c03c8103000640302e0841c034400e507002c0000c040e207410007644e42d00400074002c1419402441c1000790500c2068492a05070054100107100100ca64819089901202d01942150809807086040c06000d012081500d21480050072a1421540e20104080310058009151085d003060440351911603030b12401c0c51600180415841a132070307080150b504001b00811400290500f0300100b104e080030b030a400d010358290307140e441c00e0004503642501c0002102c0301071114156500000604a42c00721000c02c01d0042e010ba10101840c5210007250644d4908514800c0c3c000110040c000040c031140180c404444641e01c1d0050240c401c2c000494071841a5100c0681c8503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 51701208 1250 51699958 51699961
    0x71b0506210a2901021515010f0f0905150c03031e130c030209191b1e050a0f09030b010308030a0b090c0f07030c0b041b0902071e05030909 61
    0x514441c1c031100d805507400c0c00511555030709800c1402d40e1480c0c0f0340c804100b495218548080343c80034074a594250014010340c0c0c1d0030802401c1ca01c001d080c0c01c82d658564000c071180300c64000e580000d44982c00d01494945501503d54400024081507824400d80340224001d401b6241030f04070910039a44100d020300160f035500d0400e4010303903040220554000800c0b503014000306284245070259004d00503444040000124503507000c0100100c4001d000d00800e01400f2541400440244941c0c0f0402502051003a11503141c41c40080402001076101c1a1f802e61448800342c04980003c243c955400042c60700c1188030070480000c41d001d002c1940014035a42c42c890000c420000301c500078500c40c268124003003000040301410080d680c502921a440d0100d801c005074200310f4028001400181c1c0241056002c0b03440903034400902d944225805d58070401000a2150b0388400100d54000070140c500e8290305103861030302c0b030521012041941c0c5220f003640c81440d204101040c002d0b00c4092100608035040c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 51702458 1250 51701208 51701227
    0xe010305010606020f150a0c0509040c030e010b190e060a080115141801030204021e031801061d010510090b0a0201140709060e0405040201020a02030604030309020f060403030203071b0506 82
    0x42d0890b8002c810250048418803c48008002840c500c0c0da200441e204d03180e80c03150b81086000340f4140c8503400800100304060070b05910b65000302200040c01341d4002600341075410849084410150106201d121694100c111650b6030140000c00d885180c0c1c188034054860400184d800704403940905443c0d400d044000c2c2ca280d500c0040c1000b1a40d00c088c0420f4502501010403c0c03100f1034445c1c4e0151200258014009400c080d40030b00300000880112030b030311450420307003080244c00441d041210703a2201c085030300321404207010b008020040601452500c0c404034001d844141414003405004116000c81d441075241300d0070301003000700b40d4a800181d030342a1801000f40039142d0034211820217440030011a69040c480d00b414000c43e20306039070351b00700749408800300805040d005d40141e046200d440104c4003d43c1d010300c1b140b03006622907180062104164410312566100385030800e4403c900620080000c203802008540b40c2c2940508a6841e0820075041c0c440c07248255088581c1256020402100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 51703708 1250 51702458 51702461
    0xa05060105160c0f050d05030d0e0f0a080403110306130f0204020904050f0f16050a050903030409020f030907050405010e04020111150907031e050706081302130c0f030c091403070e01030501 83
    0x94481392107200d01450b484205100c0582c185001c01050b1b54010001c0c2c20240c001e80c0d106424840c4080c00391000b0b00d40700d51100d03281c60748441041d1a640710001c1c00300100a066500d00801807416000b4165070b01d800d441e1b20481218a01001e0f1990340d0110035101159101c1c0e0403a500c521004108102905000e503090307602800886020000381561070100308946281d000c6907501512a13a1441d09d08400841c04468503040741000e150103100c18400850100e0749070014215545080341d8582c0c4070314042004902d003110702e500082c015071501006010040e894085a075004d502070800c1613150000c50131f4113242c00080c2c0b0201d2221403070b01040c00005400881c24900b203074004d83d608110160084115001c0b641003034402803440d07011640400089014500070341e4019104070f8116280190358010503104000701c1594010195114180c0c840d140e005400c022181c6102d1a0400103010072502c05401616680284030410462800002d4260380400551014081d0601850b805503501e281c05070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 51704958 1250 51703708 51703733
    0xf1106070806010e0103052e090e06041e02060403110d0b01030506071206050a05040507051902031903020a1409060c0109050303101509030b13050307050a020310020705060a0506010516 81
    0x40c009154036071380da00198402c0c0101030056201c907807030340b2203080440202050810240c0b0300345139017942c1c41400141002070380b00300345002010202400442c0b401c1d00e044212610503040c00d80811810303202d69000740c0c80303040580b03040d02d40c006508890b102c0c40c4c0700081c913980c0800e407004110220610011003040000302d9080e000d00620b86582d4141d00c00d0310b13044001d4551030301500c3d4108284050070005445c10f508019002180750500701d14103880103800c426503d03800c2400401503032002402808418a10340b07110011042d5180440c00c2816440780200100302c0d0305041000010081403102031b6540d042c1c200e0764070601200080103005030f985000c07901c0340c0048800c1e40c060382495000040103c26881084480b1200da0740f91400e450466494101c047c81c06000c20304440f000554020010304108010700007203000c0c400420701c41a4610406203400c0c546000e203c3c82c00d0040c80300c0c0001a0700000c1301a005070000002044660319000100c9141c05030346014039040c45c000700d0b4841400490700203031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 51706208 1250 51704958 51704971
    0x1e0302030403050f130f1a0d020a0306150903020a14030c040c02030d0213090b01050702031009050106050a030605090d0f0f0503040609020d12020f030909041b050a09020c0105060a06020601060f11060708 89
    0x6003503031a542d6126004911f1800740c0810540c2c01003164800700c204942c01411035640030304001920329190342042086030b96010303901c0041000d00c00140305520307228a04400400008002c64030340c82818020a481d0001800c4a5004584480300700b80d40d0742c001d000b643c40345403035024219261021010b00700c00446443c461124414540074068145512410440345280e4016000f848100c0b05504d0450080200d11020760319556215000710315951402450402940280c40120740c6040000b1140c0c02c00a8140f030b02d0b401d01c8100d8205407030003034100e07800040d003010a042403a107a98907070400001510400b0402544035480750a143c04014030180006005000f0780e08079003003860749010003a078910070b2103070296111129000180c001004003000f407010040180140b9907003580d4501207026441240c2101d08541d40109006100c0c000904c61141d2002c421151161024070b0200041c0d242ca5041c06103004101b201103900003854015071903503284001d184125800c0303192648000340048003d4510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 51707458 1250 51706208 51706229
    0xe0a0204060c300c0c0e0603070317071208060f010305070e010c0809061603021002030c03040f03030f090506011a030c071209080f0604110d02090a0b0d0218040507061e0302030403050f13 82
    0x22441c1c1001b00e017102d106a1016001340503945c1140c5a0014101445440072290b000800510b40010901d02e00c3c02c503243c016440300c1c2c010b800c061081110580e09045c0303581c105840d01d020400d41c0781d80020802c3d0401c00c20b080c84a900143c9043c0a900c510454900c5900064009240c41c20010808114480c69000f075083d2444050114680c1c8142d03c0300752030741100c001c01030002c640440c41c401c52000c04184039040020302c6e1840c218042084c1c0c1c6143c0816186500711100400c28483c01c0761101e003d407c140d001640ca18605850175a00c10301880030701070210160505205071050180781c040c00980042e41c1281d2030f4148040c0f109545100440e000c88480580c1c0d1005200c81c28440c45500c1c0302503000f0000003030b55440c8650000140010500664401d461051031f00240e00e84002c0d00c04880d0400710208518602424030170715240b800c0e44110f00f0400c203a103205040c0d030701d94400d141c4210400e207405030b500d86603401c0480b4180900b03200c030384c01e94000049401b202d00000c0700086c219a64600c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 51708708 1250 51707458 51707483
    0x50a060c0207060e041107240c0f022802090405060a060603180201080702010f020f04030b070e0a030f0809060417010b19031e0602040803040e0a0204060c300c 70
    0xc120388800c510b101c0d400204024001058980c81c0c15001000ba400d003003208542011441d84074040e4030186111510080c004000110540700e80303600174070304440402c0c01c0402207501c01c000001e50380c0d902410700c0d0a400006c0141e581207000300c4000034081c81d400416480141c2014105140c95040c10b8614400d0789190110007c3c0b914028002c24907100c0405c003400e4444012074006440b80c0e040107142000719580c44c94441401c160b18400b511844804020054031a4211310b0315003080300c030107442e02c0d0501090b040f500000340e45400c0100b080c1c03580000320303a41480c01d40c0380417543c80c0201c0300380a40c403200100d0045001c00203034640d81101040b050091155020000a01004000c03080c00b811040100d5142440801c0b80a41d260101c0c40b42e00266822010a5440303940407030308140c102a00e9904000340410001242c800041e400c0b0058032821890649015405064480c01d9400100303225030719182c802c8189c0601200ca607808100e0078114001028481d03009080c6034508070211801c510101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 51709958 1250 51708708 51708731
    0x110d0306030b07180801021602010e0405010b03040f030302040b0712030b090f0a1d0106151d060a0c150e0706020f0a0b07030e031c02090103060e06090402040f0209030703050a06 78
    0x1540d01100d41241454035079450729001101c850f190090b070f18580c2c0c02c51040c001403400c001d1009001c00c44104000640119451000501030510f003030f843d070311580c20b110050205d1007821080300d4120342e0103059082c080b186c0c0d18069019020740e5003c1542840040354100601c058100d070368222602d20750301009050805400c110388880192018a01c6110050004102c3c100f55404000f071003100c0d82c1500041c40c040c0d06000d095400700c1d003090160240d40540c103031205030480c0802c11142800300c90b400c504110f01000c1000c038050001d0082c104111030040030700f400059250700d903c03049480414028158030628466860a00e44129001841501c090304500304011030081d0004e68801000143c6841d01c0504a000e0101d03c051040ca5020401804010070700050441003940c8a00c3c401584500407007001500302d0704582c0c00080ca400c1c08000704280755a0344100e0aa0183d0304690001c0c0c03014403401d41500a02884185035050b224482c004420700000061069509201c1c800c144400203001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 51711208 1250 51709958 51709961
    0xa080d090923060909280606080604110f0f040e060402030706020d17150d03020c03010c1407020103050a0605030a0b0f0903090901060516080a05030411010e0a05010e0a050907110d03 80
    0x11244141c1e103000382c40820080e180007515983c1082240040300c1d80000394414484000b05242c504424864a1804200401180f03024800090034008060719540c40d06440e00c910070080300031518407580c0f42400c001410380d119000c034100c4500203071040256134840c4288a54600c0141c0d420380c4a1702c0780c5070700012454070018000800036410382e9140405001c001600303804000190418001c0c401c0100888003a49802d81003600d5140603500608030500c10302c0600d400c49070390001c0c501c200580d2407060203a5032030400441d0981582868006115600c60003000b00a0040e46c1210398507011740c1d12117000f4450310150f110b02803000c9411003615a240d054400703607a8840c501036550494a9100100603450140e0064003413103104c40c80c0c0d000b03400042e540f031021541c060140c400128601009020901014a950400d9a00d0038200440c031070303005100044082055100352810810002480f010544560510800402000e060b01d032481c2407580014084010b4110a04540e10501c40c0b800c0310140310303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 51712458 1250 51711208 51711251
    0x4060807050f0909010e0d08100518010b13031502070201081003020901050904050102070b07031a030706050414030a0606060c0b0a05100302060a030e0706050d0f140c07020a080d0909 80
    0x1060030408038000b4060100303004005041800c0780d580c50100200c00034060000008420440d66003090750302d0310402c90955640711b5009940102c10002041c180c4400300c400c5141075900311002c0d5500e80c0c480c03140c1210416450b4000070300014000113042c668000940103800020300c01d1700c2d00c0314195038000229043c815248000780d80400044010891420b01605280d04180980c0000d8580072054480c91078035001906d42600190342c2c0e00051141c08496100c00740c6161040b80a07010080c034100e03004015000720702400b249401e2b14a440c1c0c4182d80c04005456101e5800070303007032040507910000a00b5010480b20306030354051883c070005000c0724691044501c00c014190032900403034116002d1101580050007c0d030149540e82d00d4850451000300312540081c03032a580c60316a6042a41208004c3d01d40600744940018100109411484034501071070b030340141c104440507151405400082c13038810f45c952101e4403601810415440341a40100d812041d40c00b0300c082405111080e10011a20002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 51713708 1250 51712458 51712469
    0x60f0302090f04050903041d0601030c080603060f0c0d050a060510050a050a0305070e1201060302041a031f200a09140127080f03030901150602060c0d0f0f090204060807 74
    0xb4080300200b801d00d480e0340704a8000003c40100e900301600c038442c841181c056104003244071480882049410f40e40b40c002c0c480070b0203161400303404608010010a0345d030603014160081e01e00b04035001a240014100a44001c11581c104c24403841c28900032100c01071082d0302440d4003d62600e44c0e903c03500e50044046440007089583d5207450710400803001c80c003e0402074a01000c01004500900c2c0310343c0c400c9111401111028000586586184100300407661110001e40d072403d02d04440f80f03615940425031f140e00b0301c1c2d84102d0f4010107030070130300d004000c0c03800351110225007541244290342120140090442140a034480d5002c65899841c0355090b081c21052060009440300c200c1704400c0903495403a540a405608400b00854440d1103032820040702d050040c0d503540c0040208100c0f50402d0161400061030a502d40c0710050401000070b46031080105402c60001000403403501915541d03006215040303003000b04001c2c2d00b003038008180140046c420160b12031800e28501090501c2d0101d84c1e00100c98 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 51714958 1250 51713708 51713719
    0x1030807170f18030d0e0a0e060f210c1504050f120d0201090611030114010818070308030103061a03031603030f02070602120c030f0402131d0601060f030209 69
    0x1505aa8105801c0d100304100c40d44008244a900c51102e122000b40020402c0807060341244041c5806152529650f05407071000c000741c0041c02e202984402c54000e080d103800202d1a2000c5ea50100495010320030740c02525009007881c0040b020900b91240c81040611100e01aa0503000080c010850602400c0c0300244110704104800c0025103485501591a103402501091507102a0005c0c1e60804101c05a4500943d45481b025410004e451281010b00c8441f0070103542154148592259900300c406821814011400046140481c1201c50720390780c061118201da500645900d03082606410a200495005007021400e1000f5402403070484045072014004605000344094148880d06101da030170381c181035a0f062801c5030252280020440b45d401802c000da6030703c403004004100807000500c0d84115120a001b44000c22a45001c0b16400640444102c02d504800c043ea043c000c0610440060498034a01d030350aa440601180843c100c1d501c5803a5042d800e40c0c0d40100754141d200d004442c07540507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 51716208 1250 51714958 51714967
    0x9140a0608151003150f030c03082d0a14030426130e0105010e0306070801030602072102010b040b03010b03100c050f0d02090910050607060c0516030c0c0b03010308 72
    0x81c4103106065000c0506896003841d0128407002c102c2004450b210100000c0c0c41e4035000702981a240c03c074000400500e8100e2107018510307202d04014501e10f02000f802c000000032051722088000300d0100c1104a8585064071404100b2001016079000140000c00b09084c281d250750000d801a040e01e1185410401c409020b90084a207076000c66540c081a43d0481020310014145803800250080a4441100c1d8440b1550414002400c1c1200d41d9214074401d5000d42c041040c0598041482070440354845001750710744200d45040320004210f6203001941e20240307002101c503c0d90540040c1c031118000d030303001c21100301c003107042c1400d955070141d01640580c03041d156204900300d66845a001400384d13140080c01c2114807441c14071075620023016020002d40110381b0305568981094401d4008071104107444200f0b01d000003055250184400c05050790381d40d5030501050b90b01a4040b101e554203192820f118217107052070040d181c19450702040d07a5608043e40c0108042e0703101c03811241079941007201203042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 51717458 1250 51716208 51716219
    0x302030a060b040e030a180f0303120b1302220905060d0f1b06020a0308150a0311010306030b0109090c0909050303040b040c12060204061d060f0f040e0a02070309140a 73
    0x40c002c103200490b005a910301c0c0350303070a81100340b000e4503407401556075800205465840008000440d608166400181d42108000190300b042340c07035100c24803040b40421042e6031480010f80030a40405440d180500024189240c0702d0070004852002e07030305041a80d041901c510b00401140c408448054004141c48040c401141a110121b41e171a031154030500388048403803c0800d01e101841e88111b0159004500d04c13802c1540018821341e10140a02548003040f1039040080c01e15078003448040c250940320a034105003a403003900810080c40c0c00210050095a5801c0d0820081800010550f117038800414086080c0e003060007103850040c0c00100550039511640c403070346080303600074100312000d1100440015142c1c40101501400c7e03405140010303203881c903090001e015046980f55180b19484183c402811030ba5a04095406801d9500038090300c0d998196110b10700c0d441260854106c07a0030081c20040c0d15140c42d001814540d03c02d58458046079a40d507840c003041e0040140c4543c2c041c01c00013043c0700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 51718708 1250 51717458 51717461
    0xc0d03060f05040f060308070b04050d0c050c0108040302010f050c030a140903040611150115030b1804120e06031518041a13060e0a05011802060711010c051f0b0a0302030a06 76
    0x1007001010000201103a49541e03070a050b0388000409c881580c000c0e0108018048184007071414032a080c107055400c04100c2e03940070f8441c2075002905e414088424045010305200b540000380480507088200040d00349805441c555030000c0f41c0c095440ea00b000142482c60382d000c02154014240d03680198101414000180d480307036070544a4180c2445507450103c54104000c070721a008148400714103014804c4404014161000740b48042d006440781c41000c84070020020441d6400340d04503407141c04409064008913060f4403120203550b80300001005100303200e0340245441d103103180c2c1114442020261010100360800c03044402500b01d10050000302c0005030b006401030383c030004060401f041181203a4440089600c5103c41c66460707881421518100002403180701d8031001ca102e0302e110007004a50010740300d4070400b02e0090054407412121006640580480c1e0b41e155440000d440e500d00302840c10080c02e03e4080d0b40107401c203007004030380c0600e410701000060a603600600075003414070007501c1380350 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 51719958 1250 51718708 51718721
    0x81204180509010e0303070e010801140306190f0e03090a09060e070c112106060105031302040b120f030307020105070306030201140304021503010b0c0105090111040510020f0109080c0d03060f0504 86
    0x12603039504c84485204800301407008610410301e68031040d01c2d1100c40e0780014400e58058010400d41d90003441000e14603500002d843d544280700907070013760204000900405032503100760700d052041c00d088848070380e1180400a0300b00d07141c05070b8103c85241da071204ca50050311424851406410099004a58030520944520814901071080942d80d800c0040202d0108080c0c3c6400c040c91203007086060100c500c0c1404980d401036001d180160131400c5c40349006281e03203440000244034030b5840003442001e4441c50340030021400c04205881800030b00c00b1029443c2d0b402203690311b00651a110000e640140284903410a81c3d4040e036440c1c0350002c521a04480b070741e0015000307a81c400c20714440305c9541e00b8400c0066003e0032501441503210f80314501803d00391840a008580d1030790522442200c482104016a8210f8900305d400f215402d807190810381c240903181c84000e0155003011610001d02070301000030141110b0030700440d0149011048120201d40c5c56000300c41c0f0b1310340a03540c2002146040d0b003008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 51721208 1250 51719958 51719971
    0x60605150d0b180f1806010b0702010e03011e0905011b0c030809010515091e04030f090602120f070f17040512031306050903070f0305060402031218011407020d0303060812041805 78
    0x101d62241c08420715038640b46c400d074041c81c490180014503e0455031b00c40c0c0e07513010805003039000344100a12580001407004011142d001c441d80c1c2d0307403520030500c1000d41205a202581c914404000c02e0503510050501d1190318041e80480c0d501808200c945005100715803042040c0d0001c40a040d10b1142040f468000103460f10506620640300317441d6616081079a9400f640c070035114081d40194940014041c460f46900180a64120403102d4000187d803204031800c100e0800ca0f000c1d0350f82c0c00c03072070b2014181c2d000c01005001d403816244030002c5200b4010060061722400c403085100c00a000c50016031b04d100324000c880d400042d900e41002120701400180c145000c0c0141603c0149403901c0603826611225070003584c003070707001209000541c10180007030400c801c2c020050f80c1c540000b12211001c50b035111125075040080700e0036207412146040c8150780a40c3e41c010008241120903040c0140945924000c0c54054007415410850020003401120102c503c0c01c14581ca141c0001c40100e0000c16008045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 51722458 1250 51721208 51721231
    0x307030210020f19020a0302060711070308070201110a1b0e01050303090f0f030a032303060102031207031103040b04030207090c0903020d08040305011104080d0306061407060605150d0b180f 83
    0x4000e545039440042d8507890031145c0c0107040781002d03818001e00d0058054070070030500042038400080c0050110f140000c0d039030042d03921613840304030b8401207400c4007911324511118011481c0c440c0402c40048071080500ca050100440c800d5100c04090030500c02c02e120300d41c0d065208000d000101c0c00d2900541981d0a001000850212160700c04641400d0312040c0807000100060701a40006900da0140b5040b2445c42100c01e081d442c12000103945c03885001c000d00c110385944c0002402051081e0801084204910450740d124100703031034000d0b4007042c161400c5026000b1000e0214135035596204a40c4a04040e94840500a00d90b400b4000754501090080c2d40000c2d00304000700205809026265110000c9500035940d9480c100c0302a0400400b0029031040509003001000500d5200d9240380e00183c00c98019030341e0b0340062030020024040ca511507034203c0701ca004035a0488130018090310404100610900c0418076180c200580e04000c0005105c0e954001030104110b2404107514650243c40b4129 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 51723708 1250 51722458 51722467
    0x61504050a1104120c090606090e090309060f09040b030a150f02070803070203090102210703050a0c0218011a040305070b0a20010501031208090706030e031309050708090307030210020f 81
    0x4002d01c035071058011054005042940208100e0504104c1d002044410010000035040a000800c4032103a88541d03500c5100d03490205840040c18021070b80f208030014002d5503588c9405440e0381054012900a0f0b101d00e140403c012001e01b004550199060350060004588030300c901800030082020000d14980c0507424810100015044001540a07604a80040d600c9030000707000240703030075010354640c0851310f0342554114a2440c07610540301401c0d814100a0344550605804460960002c080658400d02000705a060003240c800f240d41039031810240a24800d605003415072030f510032031000909a41c00381c3c400300024040c1801400c03c0c0340380d500e030170012031001080e400c1c200c2c2380107030a06c41140d544100400420a0405028222010078202a06103107440d40209456030401d01c0348a00307054850101c1c40f00f842003401291413610b4201ca41c1d000303d0b4ac81e00c1010009160840340c007404212500c01082140400006131a001523040e8004c09011b885143c0510113904440a1255140000e01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 51724958 1250 51723708 51723731
    0x1a01140a02033006100c0312110d05040b07020706020c040c05040e010e0f070f1b050304090e10150b18060906040305010207020306070807020d0503040206040e010611010608061504050a 81
    0x100c9007505089141e03a40300311040307062810340c040400707020144aa1940d41c0c0515682c0d4004070b61005c41070b01420010b415a82230300c0c07100090f001201e10080d582c60002070410007559180d00c05405140503440c0101941d85e0006c09a9603101c6500642015a2180c9008030144c5031035001502080024940b050405985901c1062001d000303801240108a0700350070440d4032041c080a01d54810103d2510f484410800003014225143c0310a546215101c0360150700c05008041003101c0c01440c0c403030010402e194448042c281c90f1400d01122007081403c0403280e01c17055204c00d0380c0d941038031407032400130380b13000300300b001064001e094152050f030000703018400200d10703684500142c00214003030b00000da03031400144101810414020300400600c5000e00c14001b4899001400c84514221030400b2130b5262101d0000548134000c40c0e100366807000920300045100e03940304e45c0040301c4084090080c032100340c0f9142d03840c0c1c954000300c80552819040c000d43c0300c1940780542000b0341101c200d4031700080d41a100d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 51726208 1250 51724958 51724987
    0x80a0209191805010c17150307030503030915010e0906070810030609030801030213110306040902011b0302010605100305010e13020d05010626010b0306040b040812010f06031a01140a0203 82
    0x5019142c1281032510344401880800c2c000c1d0050003800c4c1c034100c010014906c50350040c62101400a409544084e00d10980c0d80d1020404203000c0e581020840341c903440e05107003150741c1b00804441000c14800110000680c00c1c0b482ca80d440c014075014000c5e005a503514542103810440c01841500103007d0840000003003486031143c000414001d40d03844031a503046005000000c0d142541224000e031030311042d007c075801d03d4402d072030308050121008102c3e54150700040342c41404c15110014009800e030002d600b01b58055000c0c508481095400840c2200c030340c0000e8044440910072020800d4070200010220002101000845480181000707030b1401c0545865003154039a4024010002c020300a0580c60703010304001b1080403803054024031030f5142500109880d200050801050008010080360800c42c2080654510b0074103c620318030703c0d42e5035030280e00c920b000b00d20490700070900e4804201d2200c015107400301059101a143c140c211b0300c1640c1e00f03410035032201d203200007140814090030202d00200c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 51727458 1250 51726208 51726221
    0x90a0b0f040b071805010e040b0a0f060f020d1710090c03061a040f0b030c0c100603020f06091f0201110a080105040c030c1209020a0f230a080a020919 66
    0x810382461040e28091428a05528026003084288242a01100d02d48205424400300b564400c1ca003080d02c00e0f80b01d4004c1800b40115190603030784100c40c0b01e0042203504282c403d41c0c0445802d60f032030080100d0081710a980307030007032000250001003072149000075030860b000803d508000e1414804c00c2c407650301c1c446407048980080000f00000c3c1c0300c2004001100d00d03840e4204186104140700e524251900841c016513006038482c0106211002c4002000d103101c2c0070a5030f0310382040d081500d1f03803a0313040700090700108843d0000301d20405412010107401d007003140c1940c2c4000382c050902c0c0c1c0320340c0c0712000010107010003908007421503480f1000900c1d008001e2010f0031004401e900d680c07a040d4141400c000540d60b0a00b0341608042c900042803c13410390140030900c0160000b00e00250004603800030072082003d40e046417426000552000409181d4215465400c0741041c604000a150074000c01180d0704091107811459400301001c0800340c502104000e404c0740000b6810303c03081c40d0040410301503401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 51728708 1250 51727458 51727471
    0x408070602032e050a180f0603050f0105010b070206090418022808030a0f050a050c070b03010e100305070515070501050c0403170301050a03060b040207050604060b10020c0612090a0b 80
    0x1d118034500d594201d0f03c248034202d41884903801210b500307141c049501e82ea02442500c07141035508040342c03681c00c43c540c0910b4100e4898101440041d44078201140c0d40d1410425440f0315618020000943c0b0b2004810303580041d40c001d102c4d910301003502d010400502510302084000040300940e030b500603608c403241d44860310500e010100351103502c50054046481d060f400704502da04108400002c042d409800c00c0d80c1300c1c8403820101d1311500390399000c030b8890054a500404501c10034101040f20310030540554120b4031045004000e80d90390400c4441401101d21004000c0d80c01010705012514080540044644032946554140035064840f107083d05c0c1c050700d5140c000b5100003024818010f00b4240844d101c1312180040f07245501d01000700b12020312500c0003170b00507581c800001e107441e6102d4040701c10742900321048401c039040c1414048020160784008a10031008480c1c490001c03400442d200c1a40c800c0208440d017083c40440e2100e1402100415150076401281c0007000090010040c041c010350 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 51729958 1250 51728708 51728731
    0x1205090c01020c090f0103020108130602040b1804020721111605010806030d0207050f06070b070e0a050a030807260703030c0305010f1412120403030512010504090804030b040807060203 81
    0x880c03140001e0700344904625000d00a60120041010414a0703041c2e55044036820b180c0540035a80341054110015101d1030020141e0b0300001e000151004135078090176000c041c80015450f4540b403081044201d21a0160040841042b40b2100e04203409004001015403100d0410b5094008403d802c2410003000280d01403200038941c90522017940d01182450b40700303909400038681589450400b81d0ba600e500c0c400c0c14440c070146100308041d611050166124540d10580780402c90608281c050051203001c1d144500480074035030001101d140402c89081101c0d00200201d103008038548600d1004001c5a02b140381807180d08290000001c401c4008040f868001ea90008083d014840d0090527900103a122400401d60303d0000d005501c1c5025818008850031501c1c030f004811341000075820011035070154010000003050000915410030028040001c00d0000003585a80b9001004100d0b000e2400c00307000760340d05110500015441c1c0844613001801a21f000b41803000a680781c0d01640c0c8200d5203060f800d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 51731208 1250 51729958 51729973
    0x10606111011070b070203090604060806030609060c0a0507050a050d080a0e0604080406050310050901060908011b020a0201140c19051c0f0c1103030c0a05070b0301120605040201120509 81
    0x84014003481071090281d16080c808180845030040d142c0c010804043c1080204401168400d4020001c484981701f028104c1c41d2655a00e41001d4282c86c4115a0f82c2d019001d07013000104801c0c03001c50b90700d01c1034043d5800d0605041c84203500302e8071a080100304440600c10124000041401000800074100559a802c102c80c90710034071031400c1d9100d400405032258802c4060000090402c001d480684296150050301d0340c0c1c0312a201c1200d902168030481d006080a0b002054407a070011000382941c0122000307001031b260208808041140d072000690058000c0d2442100540c030407164010020300c0e1301c100b5814141414010350030100e940120500040f4079070340180c10000180200d40d0340250101c000e900001c1c0841e000b800c0031070484086020007041d128014200250806d48030180800502103e131180d4454803a01d80c1e40d40d00140c156958800e0300030000c1c484000c070044074103a5080c010341018400042e07403060060320020707004038180108605689101501807140c10b2080c0f60364402040c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 51732458 1250 51731208 51731237
    0x5070219050f06090f10020403020306010e151008070f021b12030c030a020303061206041a0603030705030d020d051b07030f052512020c0a18022b0c09080616020f010606 74
    0x90007240031091b4031850040c40200702594000c1411390441d081240031244c82c1da41d8071340340c1c83c1025450240700e922052800241942983c0424081c1c8070b100c56441c1c10701d08100b1000d05a035121207000c11383c8800c400741c1c0750b901e007141010703040c10b5142616075040301c5c2000c0d4484046070031078204026210050348007004010082c0b4240b61034224424189010b41114102512840b00941404211303150303020100002c03800c42d440810486842a4004054070f803210043c1c2c5004020350b008082010a1600701000f06c1d034205126540781d0020070380c403a419442c01000356001d07590500b4803072010003841024000740000011000f00503000050210380e201051035585000e07001182c6d5000307050110f6200160040040c4c4410318000140c4582c01c465500081d01c00100340041d1041c40d440c2d014103c0507850510203907500901e101d000804032007013030145024102e0100d40d040d070f0510a0746290707407047c80840c00340b0480b08e454000c030043e103105480b800320300d0028850071f441e140d9215000007294141c09612 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 51733708 1250 51732458 51732463
    0x3160312020607030501181508010603050606130623030106151707031b140409140f0a050403050a0509031507090e0c0304020a0302060a09030204090606050405070305070219050f06090f 81
    0x9103c81c9a040070002c550400668454446500300c50b240b50b10355600359a00d04120310390414000300080e50003800307501d460f131801c0c0d6107c9206039166030042600c0c0041024103c890300803034042e43d4803040184155101c007100e00d017024600c245003a03010355840c030000c2800503001c00700c1c51540d20142c9500c403225944c02c0c03d022111000401d804200746c0380c02c02c1c211311801d2004c4040c0c80c076906490070702c00e807d40e0700803107218030f22485d440701c0701c02850074448078001c0181d09003035445200301412201c015550f2155900c1514400c030740047c00038404002800b0010300500103400000c00c0a001c651342d406400820f01001802a151480800c2c0c04800401040074910f84441d448941c03500441e065041c0740e80460188200d80c04003d104050202e00f4501c207030f2042c00b5040045030000e000340a89071450030b0440050070f02c4d00566011b241810002003809000b40103450050285500034180480059801c0c04c04402164007100e40e03002d000f2080054500402c02d0381d00a80100001c0c100030000d0404042c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 51734958 1250 51733708 51733711
    0x3030204080c01020105040b01060c05010219030e160f030b1e01060e10020a020307060309150c090e06060304020a030212070e16020f071206050712020a11010609060b070809031603120206 82
    0x43c116070404041000044100380200c0c11079100b1f0505580e801010714040e4064010000469012070b072a00070201c000d5071640241c084401d02c001034841c482c150268007040510540039070601e070382c0030980410008045132001980110a4840ba1010440c480390200c1c40d0319003a804203000915110381c0700060302d400030394072103800c84d14001003000c45c1c00790740032a8035800148100c01c141590350a685062241000f01000081407100041000d91050a4054104c07660350180078880c1c00c900000072a1410304004990060307070018500a24145141c0c01c1059080101c003000c0d002e402011000101d50407030090305400f41c145407011001d272400552000745004000c0c1c1c0c1d040001d5000000170400080170a842c000940d40050001c075140d0748a0b00c086d210850049840200b040c0f001503403600641d4080c0e00c5400d0440241c0003030100542e507500a45c143e400901920f0041c43d0108132107000512068014084004060103445103a5201000c071252303040300d030384113032150451f0101c6644c40031360600080c1e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 51736208 1250 51734958 51734983
    0x90403030c1103040515071406090303040b07030c120f020d020a0504051207150c03030b06040320010503011503020d06120c1401031104120f050d03060e06030a050a0f08070602070303020408 83
    0x644c2803e10304400200c0300d00c24000d50518200703000610340d0600040003400c503020f8040c5403c440040c100030300c00c603590b83e0048030241c60403075101002c1002d040c0320b8014109160700d80c0d03865040041860101d90004d001242c0002e4141d5070800024414513198001303000c220045442c0d0540301c40c03500040c001d1203030342c09900c1000c603000034405102c0100c515151128401c494a810b840b016020315090b4000d0032259001c0c2c0e841000401c2c00010002050b0141039080c1410f401550014001001511540000e0144940e03031030701800ca40041a10913400f602030404042e41c04111141e5480080810300c888060941d51140009805d01c40d40124060820603508286020846001450b512198500a82c0034070304030042200341c95028044030300548080641c0140999120b91440d2030702800902d8070744654601520f070180010294603010441c81c256582140241c014907806940301810009124001c4683d0402030000742d02203002c62000d040c1311403003a01c0046e640d50910f54500e00e0a07a6900d00c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 51737458 1250 51736208 51736213
    0x170106080607091703040b1b0d02010606050409020c031603020a031d0906040b21030301090c02030c0d030506010c06020706090c09051302240c01060302090606040e01050d080702090403030c11 84
    0x10b101c01c031540305002c3d10848a84084001c0d00041c855840c034158402d42d4014250420042150b181404d6854074115440030640708403410540e5200040c1d0a889091240c580490300a12081210112940060030124042002d4034a840c00005440d000c9481d0300100f80e0040c0d0080700600d003010781000502d00e19039038080c0303540825a07800f000122000303801426136014a031190652112529543c200d01c000f1400613403035480030f00d80c50010950701c0d08248900c102d40d5003006a80ac42d014000300480301c030020710b0409840001860b000079000303081c0280c206030422010803903000100d50b040c1f01030300b10305114210110300552141026100e101c551780103d2005407a00040c801e86418504035000c4c4981d0590f810101010310385140c170420720541490481ca01e00000350903003085819407121040c0e80c0308a4002856407100700c00d1001c3d50245002c0c5022030348410340140540c0c80e1104004030041d1007801c030503281100e0350380450420f40d4140c0b0210040b9441d081890030054008102d514019142d100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 51738708 1250 51737458 51737461
    0x9140304030b0c2803180b0a0b010521060a0b030106050403030f080c0a081f090b04110909041b050d14010606030e0705010e060c06010308030411030309012a0c1701060806 75
    0x10068070484011030401c1d80301e480c103a11300c0e07500f0301079003068401c40b0310b00310140400c040d06c0c200501c1e040e108841c44d89134076141400c030502c05c1d030113003007640d020511030801c0c3c0c002c020448500307018901003e805a90700420080300010f00e011420019400f81c00076a0380c080e161441d519000d0902e1110080b83c40c2070181940c00c1103140303000ca40581d03c180c40c42d4500741e291500c420001c2d0805407a58402e07145032510405010648820f0b0f6000b074626400c0555081001f03200d081544031890080c1040d450b80184903902203070100e042c914080401824001e0700d20385456541001802420031018221a02d242a01805001c00b00a00c1050300918580c24203128042402c261543c60b4055801400d0500040d80d10462454603079038141d8040081e040100d689a58482c10f000416820444003140c091001070b0892040c1e04012056880c05041030f1603050307400000300d11706950081950790304241a14404e000c030000c01c50503035000f00202000e900ba1103402c03500d80d180c2420351b05a600300050b154003520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 51739958 1250 51738708 51738727
    0x70c0e060906010305041a0106030606110102070f0b0901110721080705031603090203030d0501181103060103050a020c0105010f05010e010809030a030504020d08030a0506010806030615120109140304030b0c 90
    0x404168800000d01e0005080e591b00c1c50101c201070000c1c0d103600e8400c19540d00104e5010f4059000b10292120303074481c031404146090403a8280e200e603c20041005511240440014200609154120714103800108422240000f4500039410540c000e0f0307690590211021400c4d10054038884200600d442d209503203252110b4050a01c0c880030380b807403084290b80d00c201c0ca441403095100040e17082c1d00900f0b9030754410300c854194000d44028040e0100940303292030000c6880c0c00c14450105169040004d0509683c1e40a0054006100c014508034078541c0810003d1000c010a03c500c50290419141d440d00b0b41c3c2c100f02c0014a080c003480410360600c0b04142c18400b0386000001511900a0980340100d5070303070390303c1c4003240d40340272840c0b4000c0c0741c00e801100703100d4408495085540701c1d240c203a03644010744e0380700350416aa03285d0994800110010071220b8080c2400c00759401d640d5403410b4400480c0401569440803004054166401d00c0c03508041410300c00c0148116001da040085003880074103209122 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 51741208 1250 51739958 51739969
    0x31b06220e1e0f070c080c1b030a0c09020a121404050105010503010c020307060c0519030c03050c0f0702090402060912010501030b06060909070509030a1a090d080114040504020a09050c070c0e06 85
    0x15040f034000d01008400280c039a480f4102c1d01c3d16403507204c0000354031101c16103121951041c0244000c0c180c1d040b038210b081618100000c10b260300740e400442d0f9094452802000c00004d61240046008010201c0045040384205010341c02503d1049034083c4501d1a00e400c00300c0c00c40e001a000300788a40d06140f0151181640003059800031504040001041911100b00b92214403c2105541542a00e00441900b00790950b2280c0218001610306100aa0300e000c1d6640f5281f2076208942c2569105000d96005130a0502007254018409010280341456040c0000d14a410040c0186450ba4441005008112200c146650001e0040d9440d509060500c07000030402c1300010058010850041074610703c0e0b40d0300704004840d081e0021100701103050700990786622480103d9110500c2d10078106001c030003600c0b03800e08034122010300c0ba14580c000c0c202c8003000058034000d801039a000d0319260380800e48032000d11940c1c3c001c81100c08140d58560340c0c0d1070100b41c60347c0700341c0c84a115001608100021034a84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 51742458 1250 51741208 51741211
    0xc040b0604060c1103030702100f030605030c06030a1d120403060b12070302060d09020603040c0602060f100b070302070e09061801090206070b07021912021b031b06220e1e 75
    0x40d104c0704a02004d407000c20f1440c0a0700c84041d6001c80c0c10392012117034a030007890002c002012560f080c4052030f01c4000307041d59003421190f443e8001c2001c10028007410400c5d0301c0941844291041011541c170b0b04856640341021001444000120000c4e041081000c0b611843c014403000791210702c02221040385440d1a1416880302a0042c04006000380c640c012039807041c00c005a005003c41d03200d0400c0d0500c4802004c4a00852000d44604004500c01d5401d4002d294441c540e10000c0c5001d45003820755400054000501c21415403140f001d020806800d030b94401c51050403000001c01c01813505011808800a001c585e45106034034000950000d40c41c2c617022184140d4101c1520b40850f111107400b00d01d46200060462034214590821108210142d01c034424031075031541c22103102051109824410080c0200f4181c0c0c10343c00080001e850702c2c00c47c01031030030708900281840d0030543c03c0070025005165004c03002003480e0318814184215a46e030503800350414113900300c0b6a0320b0301150080e818000030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 51743708 1250 51742458 51742463
    0x60e04050124180b0706050109050402030703021002070e0c0a090b0414100903060f0506030105100635070503010303090b0a020c01120209150c0d0816110c040204080c040b0604060c 79
    0xa00307022005008203d02160075018900c0301c1c4015503640c0c0c410b03455400903c0c00315403607410100001403961860182c54061a0014041c2c020f85155508004040e065004194154050308000082c0d5905d0820201d10420959240716610901c0440040291245400121200c030302407000b0700526003405921516081d0680f0000e416102d600e200341d601400942c0000c2000b4246900c4a08004042c3c200300c7c0901001d5009000545800702000c140880074041c150000e110f100403102e5002110302609482c070b0500103a02c0850079901c44001208204079001000704000000400801d6408100e250040180c14002400c0100340da8000b0344078200422524100040c0c01c50130a00a0f410b581120400900103200c10851841120940300a42004d0514032440c020059218001d500907220749224061a1503c894504001c1c482074699031210b000c80e4090b0310401c86023115540312440104054101000206221804082003106856040340100d000300010710081140640000f00c41da2450b1303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 51744958 1250 51743708 51743759
    0x903040605090303190309050d0503091002030a020d140702061018050403033c1103060108090304090603080903060901141801020d050c040f06020a0305120a090507030804060e040501 80
    0xc0b06600080d245005800d0f0311480c58000541082d11150141d02400c00c4902c54010b40300d0b1900a00800e60710740c0401c65592226801440e003024001503181e00460b444200c0c0c84006090a01110300842151040d80a07190390210703030014080700c680c0400c103072644a180100d80102240c100186200750f0041140381d11520b03500d4801007800c06000b030300b159000410504031582c0800b00c81842d20314503108440e645103014481c00500010b4000ca0180c001403101c051030b401c0c038507102c4e48011a0701c844020a818014002400b000c1580f100030302450700114001c80e40c8a0300c4112207408c242c00c020002d400d04240740c1c0b40400480c00380c49100102540314203440d0b814000800412000c5000e807081e0006844400d1400082000307980e00e0102070f00c25100c15004c1c0b01c01c495281c0c0400ea90310707c0482d5014020030001e01011640300701c0c1101e41540700700700b00300201d8801d0301036039440d26001c8503810072981d000c4046410b1000581c48030300d0394201c0504450a002c2945803911031019404400078030300051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 51746208 1250 51744958 51744967
    0x120309030d050414120d0b01020f0303040f0c030501020309010218010c02030a02120f0618010e0a08040b0304060605100e040b10140c01020412110307140105030a09050708010906020318060903040605 87
    0x2c80094052090f14088405581c0120103001000c0281e500c0a00c0b00503a191408624601239480007031200d102442c454015455612540ca031010a500495800c483d14400070802200140083c00994000da1100c0005a10b81040d41e5164980c02c4000294030304000024240e807002da6000100c9100c515019187e0440351900503070070f2800c0c001c44001c0e071515403007108248412040100024040c900100b0000c03c2206411040706480300ca6405029104d840140800c1c000e1000900007150428801d1000288459440010490040c82c1056010104000360f06241d51810140038100410307100300e8091114a52400015040c00064000c0e204040d4010030360000c1c1c404254105c1d0043c1140140c102d54110180c80c1454010b02a444103e02030b004454001504100c0800109040e1405071100e500316075a03210410300500e10307418191176503c560507000035546000e10036802c2082c081c80c4050703501d14024803520b040000003154800c05612042c20807807040804010f0728262201071601503500c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 51747458 1250 51746208 51746213
    0x40c03020c070303020601051003050405070608070314010602030d05061f050f1b030406030e060c0703050a0c0b07030207050105100506192d0e0901060207060c0c0905010f0602120309030d0504 84
    0x80c095000710016500c80c00101005240e00000d20714102d803800c503120039480c402441c1c11015a942914010b0030380d44400c0c4140000c0307000b03524903a400303080c524002922808a0450703510300c1c0402c1c0d1084025030400111186020300394003070030f50300030025510030b040080b07801c0c6d4021039071441100050400c803000c9041404003082034101c1e00400307481545c010030b968151002030340f01c3e0301a00c111000700e4500540102d00e0b0700c0200b151441a1000390402c0d0500d0007644080c0e410340d004000c541c0411445c041038a00250b00c10f90700e18000c4c501c55074010f0302c807032041c9045408c42d8000383c403d80d841040c0807810803040c1e0f9040c0c21070b0911400b21000130000320807042c4c2a10483d08005c6c800000880140700c0311124022550521045c3c00d4a603142034440802074140100804280a48001a00708502c01e00001d4010307000201500d1090220000e05030b503a004c0303a41126400c3e0010281d441e5011410402070390704001811000600c550f40502d907040498079181d40340b080c0301c0420803403038446000074103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 51748708 1250 51747458 51747461
    0x40b09060c01020d02090916020705010c080c010510080c0604030b01051c060c030c03060504150e100801091208010812040905060a15021c0906020307060509030f070f022706040c03 79
    0x881c100c0295181c42c1d11202c400c0203034002488190007000315400003003041901403200c54841c0c0d000d802a2660301d05203001103c2e03070000e010080c5c400b00c00400000c0d408000c01d102c4e6500c0b580850740c14100460038601441c0c141035451420610418083c0418404503c0d10701265045074001c40e04414901414071911401d81c2c1c00200140c106441c0400080c6655056080071290725020350f401c008040d00c840400c0102c800e0a60486144110204103210441c005444140c02507110148554403503921b880d81401c0d00c0f10b0100031030b0000001c0800c202c0750354020610b02d001d0300220010b02411f2191507403600c1c060140b4480c0a034030685600108009450310008070000e81010324170a560b00904c0d0102a40d1510038180f1041303207000c41540d540e01e6911030205a0300390362440d4041c1d46851034a464107000f801c0c019000c82c072140420411034544044110040444520501400c100502d0a004000410881042d61800050600c030005803044034002004d60112040701d0000e009480c4070000c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 51749958 1250 51748708 51748717
    0xe0904030c0206131a040b0703121d03071202010e03030a0c12060605120603010b0f01031a28050307030807030305150910080f030c03070f0317041109060301090305040b0906 76
    0x940100c0001442d40c2410340c40c2c90100203032121505c040b00c4480e40c1901100701c03440390b0301c500129a8030074031500000034491503c4070036541c424140030440408950b0100c4078108000e02440090f84005079520410010b52a510356070720050000b0810f4299403120140c580c80020a940b54403955403400d440740300c0c042c004000000b00c03512020002181c542d58040c045038000623903c10310921100000c4c003245014040d204400f103000d0480740144000c1c100640c06030400013035007009c1101c2840e0f240d100382c8070001c03211080098604000e00c0c2e80300c218440d0343c00b02042c0c1c212900030780046000b8808600e0280803140717842d615180000c3d4541d1130410b40202003664280342c40d80f2403513003c10300c0954078048403c842943c1c0d0500595411200a00710a40d0303d11030700070007503520f030010701c00c0c2d00100c0c40210050741560b0013801c216415503860541c81030307031070400c5030203d400401c07038442c0800038108042c400b070b40001d054008005500c0c003038402078900d01451240302e0b45040c001a20001c41c1c0c8400c42900c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 51751208 1250 51749958 51749963
    0x92107060204060305040203011a100e04060e0a020304030f020f0a0b04050c09090c0a0b0301180c020307063801020715030b0607051b010507171b030307020105010816060e0904030c 79
    0x1c41d1240c0d1110001806840280c40c00d920960a010448040c4201480364410320341d0000d26425110f84082030039070700d0180c0000503913030159a94400150038120304603054860b0810100050ba00d145c10718001e40a08403010b810000c6600002407000500d0f800101d2800346a004a600b00059441d0310741b0914020f622110290030682800911240c8000010b0340a9801c40482e030380d44483d5196064103110340001d1185500c881c1c0850b07800c40421079103a0245c1190042c61060701e1030070815403548419180c80302036076000da209080404103403401c2642030112410701c5102c3c008003d0070110001b540c400c40c2d07009010b5a2400f5141c0c540506002c1d42c04101c051a000d003150381c8540442c1803a5440301218040c071000007800c601104d586610881c100c4641e60ba000b007213108511f0700340e12401d40a070090403040504000310140313280c41e207008002661080a15600110341d40d07050060040c02d08201490f45420700407101c001f4442182c0082c0d010740144020754078050a561141422541c0c0d040f5030402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 51752458 1250 51751208 51751211
    0x170a0503041106071b0f08030a0219050a0c0b0c01110a170601020106050307030807050607050412030309080f030901090c091505010e0d0c0e0f06010f0f0516020901090c080a020309210706 82
    0x100c100155a80c042c00704440c4130f1346c94201d2007a80c810b00a5102e1040880210058108684003110a0070701c40781104101c0c0503030200c5100700165a159a03a402c036580014025030f501117000300b41010240114000c0b003804404003410000d40c50805000b40e09048a1a01d0001c0c0b00f10004550b40d100758400e10040000804441c03440d070340c1b070a00b442e6540c0000400d42d1680600000135070810301450454040b52031446000041c690180c03011401081c2c16502180c020808000001741c3da02084040c601402171346000081c400c582d85494542220240e0250600390300b040c1a0b0011040301c0300682e004c0710801e080100c1d4803042c0c00e00140c5030000c2d0310380040c8007084000c00825841c3d1500320b00c5108051424800709940c584e8001503504407542d00c402c400080c0c1d0170200702d074854071074409050300031003100350742c40c0815107036001614a020980003221a00d40d40e012000301180e01511161300b000041c0811469800e080c02d00c1c580310150300040d910300b1207440300d4000004680ca800c652034950000c90 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 51753708 1250 51752458 51752483
    0x21305040633050906060f071b0f08060901200904020909040f0210020303040b0a1107060c05030a11190e01050c030a1805040e060105010e0609120109170a050304110607 74
    0x120702c80a080080d2807408019091401040a06041c204103000e4140141054102104011059510b50011078210b03208a405107070314100399801c030700a0000e08001c0c45600d0390340742000011494148000d11a05503a81400300036140d00c2014a8094020441c5240041c6d4a402002c0460080d22442c020650089290030400c424000601e01244442d8404c0f560b890b06030040340c9003203a89002c2a01c010f88030390f2505012900b0111030b54424801d2801c0c1401160604015454400859001042603c0031581c00420400c0001e964481d0b201101380e007240c414100381440f000701442140d07031407010080c04010205805103a000c3d038140c6a07014400350072a55245000380000303003000d800c25188074207060301100104140c40e103030045150844c00d14006000d07503071030030004503900302109440c1a04010304115450840c0c540364156180041401f00200d500341c2c142c6011801200076440c1540300d501c1c1441060509907000c022241c100750468040004600c2c1140002c00741d1080c0000200001184031b13 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 51754958 1250 51753708 51753761
    0x20a090b0906010801060f08060a0b03100f050406030309090b010c0b090106030b0f0402010c02100e03070603150b09011403071403010303030b1302031b16051515040204030213050406 80
    0x20403445641005480480a5444560054645400030b00407400880c078206000000c0350300c10740f0025880140100b100c44081c0d681c45513508250f20a4030b01c84a03080003030318180102090240c0c1c000090500b03403410440945562001003100c011405000784e401d0701d904411856a00c1100380301e0b5050b17040743e4140382506054007802d0080845100803214922140f001641400d0003105403031103540c040e1286641143c2c16070800c200d0440400960702804a40c000451944d2810402030000c2e0000c0e49001441e02204000c13448950119400040c40740010041d041040e40d101181c2c45c16800300324504d40d00d94584480c190703100340c5c0341c20740e48600c02c802000002c240350349a0884030a030441a03032600d4200380842c500205030b1008a508100d032445034401503042154070002018103422504a0391100707600c40d81c542c0e05100400d102001e6003541e05051006070304000403044021001150118a4107180d03502241019854000070071038030350341e200000c0a02c0299001499448181c007414894000c010303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 51756208 1250 51754958 51754961
    0x408010e100509190f050703050607020a02030601150504061805040218090703052401110114040b0106110c010c0503091302030703060b030c030c090307150903030f021b04021303020a09 81
    0xa0000c0700341c10300303001c1048040041030494603c0960750158510540316100d00b43c240141ca0303000c86851003000c00010100e14180009405450702e0317030140401d5161401014170380300c4107811402c2d4240c410409100680d81001c202c804440035030810046401200720090300c3c021595110741d801500010f0020b40309013400f0b0030a090410101c803018102e4855950407022180100c0790049010229039031840301e511000c0f4482100c0c541407500a800007c1400e1032402e441840203d0b10b2048442e0050004000283c1c115a002d4000ca1500c003407058081814030b80d031407207461411070610291810480501c041402110303160000a0552001041e56004078402940304680200000e860030a001c20011540c4084030b008bc0f03580300050f811900c50418050b285e0b841010180c0d1305100304040050700f81e001410700c10303507508079490703a4904034035505014002c51343e40c440c40703011504840c088001c42205c0212a107281ca400344c0300180c503108564480c0341c0c4410740d03400180d03101ca104400000d020303005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 51757458 1250 51756208 51756223
    0x12070305071e06030b0a0504050a0f02070807020109120308070c030c0209090c010e040b2d090f0708130b13020625120f020a03030b0f1203030405070f050609040f020408010e 76
    0x44031000442c82e9107220480859400610740b9600c240301c100304103c1071409030001c94119042480004680d80721030f440d40101d070b01c500d008451105011400805640e0404c00301001400c00803a40b100f44030307655800800b020401045c1005100381e1070002e105061152100c0102c0c1c540c00307410541e0790b040ca0107003c0c0c0c1d07030391769040d070700380007e0018080081c039040500601e420800d0141c4801d5a12a180c0403294180128810091607182c049180001d150b8a0180c07290080074061650b946030700704818000d1030804000c082202c1d1841c42664080001c90030f103540e99205103103d06100c8141c8861000a00d54490004070700d05a182c001040c2082c2408503420a50b01442010407042000f081c0d41c06603401e020200481c00560440485540424003030b42200c50603290080094051115030400100e4581c1c0c110700415082e44044100001c00c0000c0044134090054080002c0b58140b908000894507c1200380c50340c09962070b2540c40141c0c04c038940503100074201d444020b100200001100541c0c4101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 51758708 1250 51757458 51757499
    0xf080d1505060406050f030903090307030f11040203042004090b01090c022b0807051306090323030904020c0a0f05031306030b0604090b011e1e09050904021207030507 73
    0x541080040c0c1c034a840c100b101c080b0344a50704c4181c1020456001c1050982009000c2000ca0100304017001d047c1e6024003c0f4009188518100003550041e4181014050788085805000c0d5104005000101d10440c0c034110030030b000e80030700c000141502808078029104036400106072081c04000410351500720b8004000f40009030f801c0f50130403802030703844440071640700304042c0c01e104441031070071079240c480d048059000550f41011450100e1056000e800d264035580f0090000ba4010070920402c00c01024282d10844111007542c0d60542c1201003c1e22481130701185d520a5034002200c4021344020700c88040007d41220b804004000c4d142805a201c0c0d11200c1509401c19a01102280060092040d449010409024107042c90306042207040140001c200040c18031004448c5083c0c28030091440001042e000d0380c600320710550800c10014160445124813042c00203105051009403100382d02268400d80440708070004141040201c0d040000d07540001c0c01a008011001c0b6400c0001864610354ac01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 51759958 1250 51758708 51758741
    0x7150b0904060e0d14030720030a02070f08030c060f06010c02030712060b0105070b04170f0a0e010f020f0c061305030f0102030601020606090106020604030c150c0210050c250f080d 79
    0x950390501101d031002284c05c3c4244c0d500062000c555440d12442d01c0c2d55a01d5081d101c49501510381b100c0d03d070f180d600b01c0301040d401a0700c0140140b100003a000138940c01410030b070000f10f0810a2400410341c96080017403016460003030a20000d01c07580c0c8210b528003c4107801a041e00c00c0c90b502c981100e1122160b5078401d1380e640e410300040040d65449181200c5036140c0191030344c400b507121580d4003441d0f0082021251006501801490100e03500000108400f00041d01c55224801e8a0300000d0802d40c0c00204110954100509660010b1004503408070040811a1026610164a0107128201090f81c01098051007850154455201c055004500507102602129034940d070328800c005100c41d090080c400180c00800c04140020b0050307031342815040c03141a0903c990841181c000c4c00700c0f080060100010b0303014400341e001c0500144107581e04801000b4000b80352201c8008010b0462803034100c0f4a1600216480440030300408a11603a00180d10401107a038955580d03980344060240402040340c581c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 51761208 1250 51759958 51759973
    0xb06040311031204050d120e0603130b060301020307050d0b0a08030a020a0606050415120f06050c0706050c09060a0c110414060f0301090506060d020a031208180604020607150b0904060e 81
    0x100c000c01c06913411581c1c02403c46c801c142090344c40014030786101c580300c428800061040212030365004042e51007800103001405070450b072401d0000c550300d0041c0c0003d009910400c2030015540e80202200d0005511041c04180b840d01c41c0301007000c90059902440d0a030002044420142d540410042080c50180009000d040d44030000c00040b00d800c0c041051100072400010000300c070a0416810105000f050120b50324030064640070152807003201c02c172141501c001402c03801c0000601c2001d802862150b9464100083c00001c00d1062150202030003d20165040c0c000810030000d11113603615002070300034007000c8484440b0240303600c1c080c0c441030311070560b00c0443e61340c074101445444919504a002007a482d01c520084c002c1d84401c90750242e8121f4425000070001c12654500801041000e0351400c0580c6015800101c16075100749000c106030f00180e0607c00035030b03128002e4800d82c582141c08403003100100340e0110010000a003060b500304900000700002c2c0700640e4001c0f042e010f50380d0b080c0d4209 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 51762458 1250 51761208 51761233
    0x706020601081212040f02060712020d11060f011202031e0a14010506100e03010906020c060406061e03080a091203020a050f0d0813050102040305030c07140603090a0b0603010b0604031103 82
    0x10b50044c4550900c59083d0800003e0124042a01c6202d0032800a400c2c070b440c108007600c409200c181754044a001680c046030851221941c0b003004001e00d0f03041e003c041c1030641002c1c010400285018814250401e01950841040d90380c01d20422040c02c0340c0c2c00003a040008000300d219211b80c0b508070240e4161940040880c0103180601806100c1c00380100103115003038128600781c85c0b4000707542c2890b4156685130803410000c2d00502c001d00320b0f0f040d0280200220303d007034030307048007503900035007204200d10840510366071915018a02e410907698060b906688440d49460f08850751825036200140504a180044080c90f4020481014a50092080d01c0d00300580c035006a60312021faa41044c00512000d001a00c030700c8a2a10081d4140c0c850000545007980d40d4a40b01d2454100100d81c1c2442d41245204100642c981041004c0060080d1021030031442c1003100703d0f46800150f02c0241111420000103409507401b1350050714100c80c000c00c00394490fa113a0600c0e0b004000b07641d01d40341c060b11401610340013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 51763708 1250 51762458 51762493
    0x90b06041e050a0b120a11040209150a1b030c0209070201021c0b0d0c170d02060403081503070e160909020c0d050a03060e0c03150118050411070203070602060108 71
    0x80300510306035407420315402403030680020080140b4042c00d41d56100c0d400c0415a82d0300e0048001700041704000e240d14580da0409072011784442da034003886644100f00c000d14545403450300c442614003a070103039600d58010300740503101c060303d1614a04000310000c02000406821403200007405000383c415842e107035a04030b0264200e02c5800790f02002c10b00010700c00195034140750800c51031007402810403694607501d1343c3c64a01405158001348219201190006d40078072041056084c001802c0c401002c01d82019203004d40820405041003c1e42a52042284503507142080700d00b00802c60b600703440e909403400c080340140c0310241140041c00901213210000b04101c5500030344d2201c2e100100506194110301c08180c074076901c0301c922802810317100d20000440e100c4c1611898131139001c5042d010740e213180c02c0f42000f50700008040c40c41c0c180f001c170079400c4144a88800c0300c202501d0302642c000813801114055803406000e610402941031040b03400118444ea80420a2812a500003040301c81558480001d02c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 51764958 1250 51763708 51763721
    0x304051603020a14130204080319020a080f031f0b030601020f0708121309050103080a030b0613090f090f11120304031205030c0d09050a020a060908030405041109090109090b0604 78
    0xe41c00031a0f1a010f1003249150032102d085044018401c214201d5480ca10341c05980207640310341825000440d2011145860a075080b480003650300c040c3c040b40056645412185c0120507042a92110110008d08070083e1907802d054500f1a5020300348540f030b51220303140712036481115001c3c01401b4503201080b010380d0004107041540c031220f014054103148003981c1c0b180c0e6040140c244e84209079105000400c09100d2140da0301a50141e160a9543c014400c1c0c060151041c5015180c01a00100600000d491020642000352440480c0c042180b00440d040d4001414400f030024000044642d00001007184003820703000e02501c05e82e800d209501d1103000d081c0c0c80e4011444085d0000b1045080e070710056100c1c800443d07101240001c0d050030310500c0880701c2c0840f20503440403039555100c42d1003423003507240c41403c9000902c0549442181c00c0d09181e400c0d83c40c1c3c01548651400b441e11407007076042c6c0036454416101c007520043d2442c201507075202c1c03807400a0144c00c0e0040e01c0502400010542c541050701400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 51766208 1250 51764958 51764963
    0x601261506030a0914070f120f0b040b0109150e070e03070504021602030d0503040302060403050304030207031a0405010e07210204061e060e03010b0a03120c08270a03030c03050307050405060403080304051603 91
    0x4001f52403900700c0d0f601c200000c903003045412518070041070000802d0f404000c0d0141f806a918541e496041070000c0007100d842450051055040c404204501e113a03a0301e95660140c0c1510b40030705000150f50100780303440c51607000140d11500214040d62580085a40d1341e588a00880440380c500700041829110381c0320559020300140c00c800002004640600011500071380b00340b04460f00c0e1956515204000702901b0350040c280e604810030302050003424062806070303144d58405012080e280c020b071058207404100070281c40d211060343e01c0c004c0d0341da0380d80b00000402e020101c006140141c08040100300c000c6010310004034960b01350010b0305003014840d4410100c000b0307003055806810350304d8482d03a00030906052010031032074504d540c000548050181c8980c10b100d12280715941c400c440c010014070580c0320b80e00e0013846030860410200740d0107480a2602d50301820002e603070345c40b0600304542600c9107400075030f04920005000406c0090070350040d445035015a00350781d151450144c6002c032400b29031001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 51767458 1250 51766208 51766229
    0x20d0f0213210c0b0309013b0f010e0309030d021209040902040207060e030405030c15040e090a0f030e13020c1b01030b0d11090601261506030a091407 66
    0x82c03008490b0146100000768444103054050b151550700c000c04600d403a000384a602c400030042c45040c031801d019015202c1c250714034071003021013200c100c0d00801110b00d8022001c030140c84040340c4c610400780040c070717603903905d000081c0070000c4440005903603079110b00d0007075019124a402039524180b0100e0700224070320a90030802d2400d0200c1c000c00001c0c00d00c0c403005a80c0564200024030000700e040c4102045d100c2028065922185803804060030076801103010b900884500d45441040c10b08c00040b90191001c06090400715114030741407034500150980f004000c22100c4458000740f40e00040c00d56440c0e013040b10544800d000c030b0090001a4040e101c0b0284d51580b1540d01c0b00d03101d5540003d4815110418034000400e0a84000001c80d030925511040d2000365070301a80100505000741c01c651f2002d02800d100814031400010500028001402403c409076100081100c40c07203001c14564031400001c080903140d040a541c03c200402842000312084850705070001c548110101d2290704407084c0e2180d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 51768708 1250 51767458 51767497
    0x12020d08090604060209040b030d0306030204050709030203100903210203010e0112110904110a03061a100504030b100909050303100632040b031303030e2b0201110409020d0f02 77
    0x241e804c040d4001303030002135100d52603100c2d0501d951020800ba2800c038040396000b01d0301e1846d42c0180000c90707801a1071034041250005091000d07032800101c0251815844000046029490808455180400360b25020b24620150142c00001a80e0003450507905140c8880c55030341d0381d0701f60a603841d41916a009000d5800642901210b01e03180c0034a59225020300c04031542244800300082001c00d4a4104681c034075901e2880460900c4807140024032008250f503c01c11100b10700388040e0441c050707440001d01044101c00041c0003182540101c0d00203202d1a807040c03140c0701a40c903100742c580d00115a09080e1800021002882e503210300e1014080403203541255001001080c0902690400e8004080042c03034100700000c0c07401441d100a500c40d150990000220150b10b28004003070711440f00c3d440e0302950014924201000c22124006402d014820241d42800461041a4050015102c00c1c2c0c00c0a0001308000803c0034894000f03050308d030309070300003001140c904a221004900400f00b6125100c4800c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 51769958 1250 51768708 51768713
    0x5010c06020307030e060a02070b010f030c0b07140105070e0102012415140a050a090e090c040903020a05010606030c0e09190203060312030c070c0b181003140412020d08090604 77
    0x740199040701c220b24011502c5600074064502d8040c0503100b51072101da0000720142405020203019026001c0704014225080c41c6850b0660111024050750381050000030f24102001100d6001c0400c018500d8000c2c041880c0c030303440c05000000d0b840e030743e5030265003031142032018007003004444604002c0b8010842ca80030f003002e080351041503807101010144107846007403895032801040134200c04103450340c1c0d03156610200305005200100c0c41c2d0102c45070704584000c1c818004004250769501e100b0503100080d0040c42401d00300e10702041010007410b10751912402003080d55040d04915038440e555101c84036440c604105000c0c240e60308451640807406401d0011105d0703029a0019500000c0040c222042801c2401f580a8141c0c010f40340b140007070324001100b40800840741490001400b4441c49039003458801c800c5009800091140c0c1d80c800d210200c02d40c03402c10b010350721420406100307400c134a049203800d1600a4030b441400440d10301510aa901e0380c28000d02c5003884900c02e000c0400a0112034646a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 51771208 1250 51769958 51769961
    0x21507050d050a020f03120403110703050309060f0906030f010f05031203060d0c0e0c031b070203030702040c030e16030b0a0b0d08030702011d010f0e030906040302011407050105010608040302011505010c06 90
    0x8020440c214000c0c4d1a42400c1c0c3c5d0350030000380049400d8102a050f090503e858060203a61818000c81c403143c00c01d8000b0008140084242e07048140c0559440f03540704180380c8607036a640310b150f903113070b50221000c000d206154080300a01c3c0d0580b0329170b1344a030428948980805035118000a4010544041000040c0a038141080c40d41d000358070421964509940b50030148c9040340c4202e91120341c844020007000700d08002030610031015900e400003545420001e03000f10b6128468960042d001e151203040b2400380d01e20982c02a030803c45203805941d20107180b00513414071085580f00c165085074500f008120480300c40d1003443d01a21006010b103480c20101d07510484582c2004200c042555645d001d019032007000c00c901c2843e144101c400014107498068400700440d9520700280b4099481480b50005c08c1c2c6642e41120203503a02400c00e80003011041854229a110b4034a00500300e508003000007403d681c026242a0066120380c0003800300030b22041c3d804041400341e10850b400941d00c0484800400c0e4217 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 51772458 1250 51771208 51771217
    0x2090111070b18040e01051806100f0e07020c040c0201390f020f010903080105120708031c0603080c01090c08010b060909071b03021f0b09010603021b060403050403021507050d05 78
    0x4d040418900c1400c10a6401c58104079024840c1404100081c813014009100c40c0c0e50000c0b081110411050426640ca81c0e1180d542c0100c81701da01c403805c0403170701d03450003040401e05070b40000b0424800c203024034400030302034101c110380440a0240c800101640070480c80450b81d40c0c0e14100e00e9402c6110100314116240284042d1020940c080c400621030700b824203000e00c40000780244c8444066500d0070017071054010540d02c03801c00c00c3e08841e0381441000c034044200c1e14441d066042850085c1182455400103141952006016800020342d26108000c10f42010f40c4041c0907400020842e580c070f5007200d0030b8400342c2c04640d900a100b0800c90302c0ba880d040c1d0f819500001c041ca070004580005281c5014254281881600540e02c21866001274120a200c840c0d000a88408144094584d01000c100e0b03d14060241d4010306801040c0c81000d1206280e603401020a11000c035007440c1054240a0141c0d4001d0100b6070048107003800254242040c44112040c0b03079030140c010a1034007142c800c01c54a42d0407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 51773708 1250 51772458 51772507
    0x15051e0f0a09090c050a0501020606030a0219080307050616020703030e01030c0e03010504032109170903030708040e060f0a08060a11090d060e0105090109080d021305040e0102090111070b 82
    0x80d0144007040c421402d1240900440c031913200302080605103805c200783c061203507116034110741c001d00420600e5200400c5040000f58146c520300c1412031110800d61040402e50051101c038840403a82e03030240140010510f000e1a0311a035002c9040ca400001203031515142d004c05004141407802c028895417182d440710141e00054989040417650050003c1c0c01d4403811b5030254006055140b448007030301416401e2100c05a0072203400c101004255032111052046450500a4900c0201d515601a213007842143c0460b07a04c5540307180da42c0d0300c40c114050020010b0721914000d9820560451640c1000c0c0c14a1094803800e0005100f60b6448400d01c00103401a5650103400000074000c000b443d0b141da010340c41c100e5204840203e01c905120003a2402c4a20081411586031f0400300c010340845c0000e011214810350341d480150307075600c41900202e40145641d001540040c80c15201c0060802e044d03010300350901090381c0354611401200001c40d5110082e000340340401d0400c0004036002034500300440002d44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 51774958 1250 51773708 51773719
    0x3030f0c0703140a050d032903030d02071a060103020a14090406030204020c0109060b0a0b03010302010c06021e07050f070506090d060b0406091b03020f0307050901030b030d0315051e0f 81
    0x2e84070750302c543e40030b1143c800c603003155031007880030404001003071010600f42100342ca130070480300b03840141410035005046140130040f207209402c080e242e2410b0045441c0d20141c1901550750701d026141a4266904400042d12450f940501003010303584240202c440c1c044042e555a00b401c14a060106c100b40c0c894010154410782d00e1790001f0058595001038080c040b140f20000450346110f04082050f24400211a40f00c1c1d2100c80301403014a9400c01964107503a028605520b0b00d0010f071500b030000344184100680a4070703041880980c0d51100c20000c140f1244100e00341c0340094030f4190703d00d58914807406450740c00701c02480032003412f08000441031200c0d4003a1030042000818107002c1411100b10b6009018425140c4610825180c1c0703464003c03a0403009480d0452421582d42c2c03814a0300d000240c09041003103000900000366031f22a41020079030b440c00406a0340ea1808104024008154000b850b0f070780340c2c91100c0700144038504888400d01e06d2010f07242a00845043c0f030100034400807071041195024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 51776208 1250 51774958 51774973
    0xb010f11030d050108030306040b01021204030b070c0f0501051e07020c01180306020301090b0a06080106080601030b15031e13030207050d0c0f060e010801090b1309230a060c09030203030f0c 83
    0x8159074010140240344020246d036890620f1803d06c02075400414800d415588903404100a0258290480f800c0b61340040c041c88044d01c64007008c95814140c2013001d050100c01c80e008800380403041d84401d006000825034205031881d0801004e0604104582c1c0c031000da0030030320008c1007650007810601c0311050700d13806030444183c40f82e03507d000f26002a00164407055848150842504010024401030129800c1901c159890007100400104004008030304043e100d0401e9406500c601000d039241038803600e02107841c2d18141c1c4e44065115039420201c0d04500c0d403040842e2418130000045100f168269014020703150410b424003540c44204038040310600c4401000040c0c84640d911044003070001503850302c20084c23081c1e0005000c400181c0020034000d2405c401c503001543d0301554809103444007000411002400c0c20142e80d2546030010005100c20070400340c8003d604085582d56140d403049800300245610a01c049800c10240e001c004d42680c001c000c000842d04920000e005d51748089800c69420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 51777458 1250 51776208 51776227
    0x501081f0e0f071503200d0204050d0b07030b060405030706032c06040311030a0c02010e010e0a18060803070b1f080d030203180d090b0c03070b04080306090a0b010f1103 74
    0x10301155504801c0b00e5040350009014000c1d102c01c1c03040c40103960707280038081003001540f00d020800328010014028003000410116503103460701950020140100041d2801001d400c000d06145003c03100000042d02e0b0810501e902d02d820400d86095440c00360090100508002042e002820f110110480300c0780384c940070209100c4d0350340398100c043c7c510b80702925503402e041c40e014103622102001c1c156290020300140f0a641d0340103482030000ea40929103100c450704c0e070340010780f500c410802d510b03030700440e200002096080044032417032044800620108000b6070790300d12803030302c0b4099520010890884400820403e40346405070040741d424900b9081510307a81e0300708107860240a01240800320740c01200700f1000000a0b024000c1c121050409014442c0c141200106030606038041c0144103000840c0005192108000750f40d00568400080101d80c00c05080900c5503400846d0668810280040054032601840c007800700780004c10386420720503242c1110240c86016114030b15440340d20050000140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 51778708 1250 51777458 51777463
    0x3240a080a1a07140d090506070906021005060d0b0907080f0607090608060108010611030408101d15060f0d02030303040309080601050604120b09031614060a0501081f0e 74
    0xd00aa00041055080354035000c440c00720340d4821482d80300c0ea01e208110200d5080303040b03440092240306000344c3d0b07082100a6000104410780c009406e138415101088021500101070300c003540c259408a40e544400b0814200949108a134060f800105a080000c005402031013101e4102c10b0b00340961318480e8440c800d9074608001000e8010071503109a051000564110004101512842c5080c40d92840e01d0000642041e2042c440c120070012101c032142d5007020180240d034080c000000984020311f0040090034041c1002528900894068448010516400061050000d803907003c00000c0b41d9207400401660b0003089510641160201c4202801660203000942c8680c3c403c2d2a00003200c0c1c10b10408928068058000e140100c0307040105010181000a8a40141364000f46194159582040c90350131070085400d424681d245440345d01041143c01c00340c0001100c110002c9070466910081103a050f61402e1140b102e89402403900101181c4904c1e0002001a00c50f090200700d44910a10341071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 51779958 1250 51778708 51778729
    0x10e09040506060f09011d0406021b03040905100602100b3705090105011413031a01030501050a1104050d05070509090c0111011103070f0c12030b10020706050324 71
    0x1181c03034115008100c2149009400316906120940c4c05442d10f6040150400c10002003c850f564468095000981000005d404413203007107200c8030300c040c00240d01c07401b266600e070411b029104049041c80c1c001003482d000c461440303044520a60042a09111003840d92005000744a0215044450080d00c3c410300b080001c09081c40c0030300c030309440c640d0b0840d15003011450641d0383c000340c1c442c5025100412090380e21151944074207104900d596940d0302c80394000f045040903a07000900700802540710003460081c9404650489001d43c0003030040d80d50744060b01e01200d5a141a0601c0c5103424002404141082840c801d1020b2062040750744450b1140d00107031171441c00300c4d070080070360340b09036070102855903c00080318215406800a01c04115031040c0300c681800010904820400b1042642380c4031440741c0144454590002d001442c8201a1103005001d4103200c3d01032805480e000c14441d108910024019040f10056074820341180c503450740002c6110003802c40d03041040640c0a0750701c1e90b40d44104100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 51781208 1250 51779958 51779963
    0xc0515010f090c080108030301090b0303070b090d0207150903120201020919090b0105090d0206071502030705040e01060c0309032004060b0301050324060112020c01090f020901092306010e0904 84
    0x204031580b8142c418400c0c2c40c1c0112102041101500041216001c000706890541e0341c4482c001c2026903034940404d15502070705001800b0700c80c0f0f00c03050054160000ca14080001d4555003516045074603400e07014010a200600c460002c0d010324410000300e081c0952142c0e46011078400507140c098020001107118200001e4402d02c10114142044030030351a2081000824081c01c01030b00344003445002404120018030041d000ea8800551034041042281e044692071084520031900da0a10600080c10364026000300800600c9c68000441e0036802182642002c0d0741c0760307807407010041c1151784020484000b0f441e9562050303100e0758107149655039070003250080c1c0f00d00e07100180c9961614042526021010b2130f10b20f840900d02c5881c040b542903d21010358014404c1c2890510309544903c240000d115107118254554a842080010441400341d9032420324000c903442005a42c0f9502c00b501210900942010b02c54418481e419080c581d6040d043d9200c281418400c20103403400f40820002842180c08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 51782458 1250 51781208 51781229
    0x803090105030a0e0a140f010b060f0a050903060a0204081b0f13060803070813090b0d030507021309050607090b0310060c0f1a0910021305040902040e030d0b0103050a09050a030c051501 81
    0x10102c07906c10400c005901030102c000307001000408001c030f54248078029402020045c00a1801640c2d4040ca046801000c4094120307084e40c41e203201c1c075000a40140c0540c5185024580300242e20500a04d21a100740344007c01c202e181c40e205ca4100f1000d541c540061000700380e11100c0001d0041030504c081c06845000b0a0003d5440c000501105c83d08000e603040403541c1440d00c5a0724143e5101c400301c6100c030981c1400d045580380c40e41c2c0000341c80001100c205144050400c041c11040101c04078203680503001c551181285103464102032155030004a9500c03c0107910794504014070340c4181040402035002e210000111015a121500004070350b48042c030748040000c0600010303d42c00c00903012100d10034007013103042c203802040402c1505420700c500c82c412910b502119040d036a40743c1c0601406c400706002c683c2c2d01c0603640903283c0900249080351307010038944400100040c0c15401000845548400a05880340e002d82d0b05451187d4584e000b0349041c81850040e00c243c0c0c40c89000b5501030401c8140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 51783708 1250 51782458 51782483
    0x13051c0302070c05030609071502032206110a02012102040506070f020306010b090d12120e010b010207060c0206030c0717030109050f070c03090512031201030605060405100803090105030a0e0a 84
    0x380341c02803e2059100038000d0748010100312420780301003400c4040d104040442143c0307140100c0208c0c554042ea0303074080248110710f8883d540306810884540100c0b21036465544c0c4c0072040c1c1c50402d80b42c1103030050103408106800001e45180306940c147c422000c180702c0d8018100f688802c0461540d810060b0201e03100c4d40107a079640190705d01004501d0041a031045880d2500c0c5020011032503000440710001e010031700015070555424014140070308582d40003101001070401c1321144c00c0c00f9102c190750a5025000c0d158012500754420f0280c03601103500a41b46d50319540301c1c14400e225035440550295480f007100303466241212600c3c0b0007035000380303a02c26001ca42800d100210001e0148058501402d010300c8046c68400241c10403d40c1e81225012a580088031540300501801c0d40f1407019102d4590140304008400c10002d94011405000140c07020485903540244070880900707180102003080d031041c01141c1d5150305c900011030b485011024041a0401c4400c5054605004034100701d078500315808 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 51784958 1250 51783708 51783713
    0x7080d050603190f11220c030b01051801050f130810180605041106040306020c010b04060503030f07032102190203180f0328050f0102030402060313051c030207 70
    0x40d5504180118050302d40d81260007400302d040000c045008090009000d070035001d201c24081a20f040e07a40280c84115441101e0300b070030100b40f0000340c0aa205c54600300405001c82d10a1007031700341d0700c9410f03114940303401100e5a40b104011800c0b0600ca040110410445503115010405049482ca01522512186046c0a142401e14480d590b0750316046150015909000a083c2c41507115281c000200049548540c14600e0580000319085900000b00060000802601b54003d000c403c60141c020030071040031104100a441c003134030a03554142d005011494004011380c2c000d11b2242e11034242101507020024400e215414900f5244a10540c04150056481d03030100c4c0c1c020002503a88007a614281c10014408078207040402d20602421000071842c0c1c3c01d0320300b0482c000e220030b40790b0b03148440e8403406400c000080620074030072519400307403049403c410300050080e00e0103243d00508040c250303078400c10300c035111090071071040d1030f00d2160396200400720319591420119001556030140c0d8450850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 51786208 1250 51784958 51784961
    0x8030c0f06011e050904050f030c0307030905090601140a09031a0105040c1713030c05010504050a020a0b040e0c030a15090b040e07030c15180e041a0f04030e0d060207080d 75
    0x164851a003505070000d80c0e81c50f07a80d00500502c01d640d4125181c00c2d040c0c840b414010b02d4000c00d041207044900c00001c18000801000024004561199072140112502c6105201c200320342551418080f8107400100d00c3c0126009020b401d02c0381d0507240c0a040b096994484042d018804a4501c440021400062105007060300901c40402424100900e030540c140391010b600c0c5100900072103210496040c0350302010301c10002c130480150008001d110300d08040c10040e4034bc50030001304034402d04510100040398082c100554040380e0004031449116a00c0840000640e80014507504607143d650400340c0e00d5408203030b00300000d00000070f0300085230a5854180001ca0781a00c0030361420fa0322920301000040c402c40a9101501c40403001681000310718401038a1000b000e2600300492400880c0110702c00c0c00c080c800c02e01c9140a481090b000100150b00d200700d042e0196103210034031040000040119005600a200c0440c01400140c1002e102c1d803101c00403a0000c0038201c40034a000a0f440040c01c015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 51787458 1250 51786208 51786211
    0xf0304090603200d0209090a080c0303010602010605011b020f0105040503010c0917150406150302060412020f04020c06040b07020f0106080304030c15020a030e04110301030308160306050a0e04080408030c0f06 91
    0x1040303c0703100310b09a0900051004910808024840c2540400064164406004101006500102d076503107030228001c400d41c0782d030403d0088100562811000081e80e40c8140815108690070001c8082c1e004241d03002d000d00d5040821440741440010440040e46840c24460782c03114000c15903c81d40001d0600c1003a10a021292852819941c0485c0155224441c5ea821407038119038071000008048004665019400d010b6600296000001080029040d4201210303601224400c030b484407400850001084201d014803030189000d9403103100080c0018060294150b0450064011103140d00e0340c5000890a603140741d00038130b2260301302007006c10801000c0055180500009504494080a03048000b50345250050740a0304200c409540c030340341503d8a40c42038032464505203140e603a0350784900700500301e0002561200c3c006041c11100380d2100303100c2e03c100c0b0300b601d10041c1044015440c001200c440351501600580d0304c3c04042000040b00c0600700000c049030035481019180d8030503445490703400d0540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 51788708 1250 51787458 51787493
    0xa05010b060c0d031a030f06010305011107080901050703020a0c091401091b0503150a06031a03060601050d09020301062409060206070e0105071104050a1a0619110f0304090603 77
    0x182070002c12100c14000c2166160340d40c40b481c0010b14401d03a400c0781e041c907010b52120180c250041e03c61719040c1d10404160b40d4103803070182d4024400304040000b50001849a5580680019030901118499601c548020010a402441111b56002c143e4841c219005401ea0000c402d4550340d0741c010480c13000d810b007080c4c010301c0141802c00c0350394021095050804481e00c020b00400000000042c0c80c0c0000050030821400e02a0800c0c0b140c41d2107003000303802030003000800c074010003d4a0305c0c0c105a1500095180c4608010b9540741d040c456080202401340440e204120b9055403107000c04145a1020000b0020070708060042c0000d9145422014000c0301140d0041c40031500b01d5820410090b810803051500c0a00070310b0700030341c0c41c85103080c4507101c64845da0741e40d80e201c0d00b00703410b000c1408400d40000352550b142510801c03d030104002003060310303c03c0010f18801c0980183c1c14400250040b01c00c403000c0440242500e007514500c0306c50b9410f40d030040d04083d03007813075460b5414400c1c021800e40c071031710024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 51789958 1250 51788708 51788719
    0x503010c05190f022b090b0c07050108100306020c0c0906060309060103080702040603060c0e0102010609021804090804050603010e27030313050c030a0c05180c07080a050f0c0a05010b 80
    0x403062110000001010302004284441c203c01d00c80000d2003000310030f143e921551003002c055008441c90480d070380d410b0b07407400380000d40c50080414090218400c8420f012140360040035440e140100540d1011401084072150104100002010038401e0005007118482000540300c048451410014081c0b0084c1440c1e0003104188200000352000103075881c103403504204501d880b94882d20000d005401e0700d800080c030382c40c01c01144008051300801e040030100c209030024000300351681400c60807030090584038003120b02c0583c10a641410190700082000307014601c0645000d0f2588089001c6500a0b4001c03100c19000384c0800410392000d4581100f9849070208040551110514071656808041c1650386150110002c617401c01c00200300205e0f411030090107480031044603090400710054207102e8a401003200b40990300b50700c6903007014203100700001410740e4140405a180e2103096008121140184081000300c198070340a00c101602301a0341d9a00280300f02e22140c0b0740203003540d0f858080d250045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 51791208 1250 51789958 51789967
    0x20301050324010b0304020609060417060624091309050307030e030312041e05060c070b090102030603070b0c01090204060905150406030b160c0b0f01060f0206043909060503010c05 79
    0x600b04059a0741140c1c0d140144030344035111400000c80d2031140440d03266000c0800280011007c038101c1b01c0080014099040d200b85940702d00c00d2100c4400304900705a480303a0384250740351400f9520406086034032005003d9600c1080201e14090880f200c405e0162160f41c404175510f0105a40300103184801202580036600703152941c51714000e0f140001e00010004241240c0c452499240c5e1180702d400d80744c0200481c1c000703091030005c1a102d60701c00e4405640c1040c2e03c0001800e1038405000302d0f4014080600181003440c5020104040ca0300190b206908554881545c807026a50f00e001d01c401038100039000058a0400d98980031180c1880070460340900c0c00d040c1c0800200b20328901840c1c0c000140141303202e6000ca8038208590844050030001c00508088040c09000034100030030300d068030030a45407181c0d40c0030080001d0303a039548201e80c0104041c0c81560790204107a510081d0411000441d00403982c415071b0035607283c400225680004000e6941c60808200520b024019180c0d601854117045d441d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 51792458 1250 51791208 51791263
    0x20105030403030221011502010c031512081905030712090b0606031009020705010b0306180304031518030201200a080105210a03080a0b0603072c0a08010203010503 72
    0x9404020005014940d011940d00000351564482c484140700016601006685561791002c800001241e59001503181c43e10010206000c0d110307500c0860460003000040514050303c81004080281c0d0071118030606011030b22550b080194011840600307030300d842ea00d03403404a000130218271200341290b25950a010900001c2146038108641292003650215980c1e42e641204100e00207256108210482c40024058140041980811012130382103054034983e44642c40f200e080d40807519180d2409800c2044104000b4014078100f00329510f14503c0031407548444841c4800c030200070030090300580d4569501122101c940008066594105a40e45007004c0060100404100c014003c10b8040c150850307030f0080107242200c00c0d01014400e00c0444002c1c070210f02e402441e9200075510018180e082c640b8420492901c00240d921841d12603075103240c2c058003000207a0701e0250101d200c13481b001323000200304070585440400b0409000201d0001d40d507549400240b40c0b811010070142c13031b145098032450440303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 51793708 1250 51792458 51792467
    0x50a0b0a0c08150a15020304030c0504090209010909020a0f030305030601174305070b01050303210601091505041a0c030a11010f090b0402030c030d020c040c0c02190f080102070201 79
    0x4001c482045003041015003480440d24000c0e076600310705d01641da07254201010070341c00002042074034880d0f1445124650b5543c18841910001000254011038000041c0060501c0f0b0340501c1901d40002c000c00340e43c3d640c8080c408401001c0b6041500010030002c1080b500756004100c86041440c9000404881c0c64a100303010200700900011120740158512604805d0301860042c807402d107151092142d80e401e0780c00010302a64001d020485898124000001d0300f40b40100a558074005424006506080400c40340c00d1400ae0081456040c0b04942001007964450205c42c68211507007070300c446587d542408404500c0328010600f0000c0312004100b4145040804825540d001c5c4d00b43c108960340399140c545640c0948040c900b82e0b11102d1500c040e240070302c0900c1e4003d6000f640240c081d0782c041140442032540703540c00c42c200140980d0068120511900b440d40c440360040c40300345460364504029900003108180d40c84c2c0356250481403464180500c01d441c80c546001450400d008501e00b80a80d40041d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 51794958 1250 51793708 51793711
    0x40501031401081b03070f06020a1b060206010b030a0f060801020306030c0306060f04110c0102070302010b12062e1205030304110a060c08091f030e100e070b03090109080304050a0b0a0c08 82
    0x10b02211031101a051178034204001d1014110022001c0040758541c0c3c0700969030002c5003000d64003071180551960b6001194001c20084d6042540681400e85c00c000c00c164003a8409010b00900b10354600120071a04118855007002d000c50000150b85c038108030742050b02c1c0c54402c0b040148640c2010013407060a6075601c1c90301801c3d2a00355000b24800c034014241a4a030700410203500ca2a5000140035410564194045885064200c4204184e0129154400da50303240407506c0400c500c51711f01000c105191400308602c4a101035600c1d5070340d42900e44401e40c5040c21584e000321141c0d44044240000c00c200c4141030015201c090b1207101202c0e1910724014400c48909001402c1d0010008842440c0e071122600c2c0d0800501312108a002c0e459003190080007461244c100d0400350190100c40c85049903140210205a0f202e00c0003000924205128001154005012088a50750b500d40d400009211040a14815402103000d080002d0007400d041d9041c031b5009210180c018a00311130300c2c031840e81225105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 51796208 1250 51794958 51794983
    0x7030605060f19020f06010e040314090d14010b0a170607020102090612040c030b130302070801050108070515070b09030a030e030901050307030504050f1f0b030c10050f07061104050103140108 84
    0x10f601204903608140d0400100100c20300c018000d401c008100710300303100e901c18000ca02c80e540718080e00041c0075981c00305008803e000b40c0e00c00044402035021440c1601c040c121100a40000a40800584009000c13000240e0140d58a0550601d120000034001d114075076004410740000d501d031644074800176070b1512450075072071001c1c031301ea40c04101070000c1c0791400e2003d0340c1c0c0a00d0070300e0340d400c00510700f07000300140c44804c0340188149600031603e030b04103000301812200e5001c010f001280c02c1600f0005104446480e028900b0b13410310120010400361605180200d40103400303035507202921030000b410b482a10600b200c940e4002c02c100c04099a000781101e51090243c41c1c00100e6896500e0203c0c10305005807621041f034440e16010310400120402480f1520710140c0c030800605074483c05040e01c1d00504d00c11554040e100e60300124404c1d000798001c007000c01160700800d10b0035215580d510116034590502c002030000c0484c061169503058400c02084550070300075548039615200480d982c954049200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 51797458 1250 51796208 51796237
    0x70302071703040f06030b0906030d02121b0601032103021e03040201050c0a08130e0405060103110a080307060b090c12040809010c020310151203050d0908040503030c0607030605060f 80
    0x20280607024020383d0043c00c4514905051281d070b48000901401001c56000c0c0710346201e0700859424600000e5150701c20701c82d6005440078070080d0440c40360642008010b101c3c2c83d4449880e1030f429440074841c07980070314414402c0106900305a055500c0c02d0801080480925204004018a120304010325a0002070320440d400c0d5255a20b10040301c49004129610744c443c4179a02600c0108000d60000c0c0c584015201e0007295170660f603907000344d840c0d003080d540070704190090001480400c400a003103c1680d03001400c194981a034420606203154400e05041e80d055a96043d0303100681b0f0540c1107280c2205030742494505041165400f540c0c0781201030001044010009014030040c3d010b104d0001c4070b00c3e001401e540303044211b560f0860181c14040400d65004040340720115184600c00340d00c801040e003541e03d2a041c982c045140d6402082840c82c291350380c0506000000b00b650302000140035019020303000d442d103410f00e400060240d9800d504100d00c655018881c80030300041c80d0040d260030000c04402c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 51798565 1107 51797458 51797489
    0x12060f0c201902090702070509090703050d0c02030c1014130306050903071208040201050706060b0d06050a0602030a08040c0905040506011517010605090a0b03090c0a050607030207 79
    0x4a40b411000720542100241c00c1c0b2003029640b19400d0b004407448907403110001101c400d8103c03101002c81d80729210510810100707000584005106003841040b0782c011f40d0009ea1030304418081140180844c3c14440096841030040c8203000c490402000c2d60b512030441c07407001010f928001950f00e00e060802280c4074000c0001111032480d046600c914012441c813000b200c8801c03016200781e04110b0144511404546180300d60802000d0411880307a444489447c42c03c262940d5a1040e4410280510100f01d0240c01100302d4810303514514081d900c550300c83c542180309207031a402c8040294542001c000030000c0000c0c0d418140c0e4030f400c032621041c8000750012100b031000d100840b030140042500400c1103e015601500070801c00400d840030058840d66580382582040303901100748d41c4048030001950502c400210080d01081e100589415150386007e0b594044c2403103001c06107261480e = true := by decide +kernel

theorem cover : BRFrame.Cov 51618708 51798565 := by
  have h0 := BRFrame.cov_init 51618708
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51618708 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 51618708 ≤ n) (h2 : n < 51798565) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
