-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3384
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:43.268909+00:00
-- url     : https://prove2.me/submissions/6fe7cb28-2817-4734-850b-6438ea7a5685

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 608453237 ≤ n < 608633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 608454487 1250 608453237 608453257
    0x304051c090e060d03020304150e1306050414062209050a0b1b040e07050a02030d060e090c06030f040f021c03050a0305130c0302040f060302120c01021c02070509060105 74
    0x1003080c0d2a5400900000281d00518030005072200000310b03a80b42002401149642540241d81340ca410098036030340701e0f4941c2503a0720602044040400c0c40341c0300c20b14017240110040000050300c0e801c02c02000f0681f02c5400e540050401c84a0a0040302d5807525181680c2c1d03202d10305809591140310780014040d1091039005402030044400b11014440c41c0c90a0a03c10511203000d0321000d0215101c581d654019030044203245081c1000185580b80901c00070000d8650780d00450341400ca4000a140580d403c07500410610700303100007408101c4034100409480d943c3c00700c827514110314100070f02d83e0180300000c00140480c1251403a1505544504046062542440007816600300881c02d0283c480c0e40000400310000780740400042d03002d0510808406010340c8008503c82c51461a002c0102030411151002411542d403103000005030380d02085030b102086090042c10025200f0f00c006410103104c130b008000b103088205803a03005150b000c180301d42916402c64507071a4580350080100d0b42c41c01100b55032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 608455737 1250 608454487 608454523
    0x33130506040b180d03140a030603140a060608030405010e0f12070e040b060405070c06112a1203060d0b0c070b13210207180b0303070b09070506120c030405 68
    0x1141038800100100f4107001d9038128810210048800c4c4800700040440141c00504810305104106860304024500c104103490040354154581c1c42e00c070004284414815007613030100030603008004003406a58000e2a40c14003941c01d05182c440081c2000c290042014400c0d0569450700d203041d9030784421600004109411146e4541d180c0740300050410040e01c007074695001e041c00080c1c082c45e02d401449d1145507141c4d104582c1032907a07510305000d007056102c0c0707040800e0103114014924444045404030f80300c0e601e01085900c04d2a20200b800c0412800584802910420800002e82c0f60310325101c5071310354801c00e540c26641c0c84030805026802400401441205a4000e01c21007101440840c6005401980215181e00c00c00c0b1041c030360240c11200c00c0000d030300400410018000102c0300104910709c205008071706010840006030030340e844081c0890300340d140340301440b41119081204034054030041d10a0352030502c901e011480e440800074503400300e10000100103004c0103418409a0605040300305c03a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 608456987 1250 608455737 608455739
    0x50a0b01030305070308100311040f060317070c090608060c070f06020a0e0405072a030309050601091d03030714181201020306010e040213032316053313050604 70
    0x14455408410250001500c000c0498900108007d40c0000c5949c8034501804c4611000240710240170400e1036200303e103541d90000400b04075501002c8180e4100484103a94841e1185130a43e42c803116504003107601303481c1c050244018440010300ea50005440c1030502d441d15294508071036649584e250090241c0e001040c2c00040079008182d00289240c00c5905019079520307820b00300e840382031246144600c61035a00040c154041e984104440c62402881d0208101c00c0c59200c05281aa082c1d003c4a00d46944185600d04d60b03840c81d81140008141501561450503c0301c00140301e4041895002c000c1440050f48009a0303a82c0704010308100000750500303001c8c20300c44010301c3c001c2d08100c4405000c110a881d00307044e039203898422629209105055100e445096884506030780c0d403100c0080e54000e032003071400b0302003400c1048004140e03032041c100341007007600305401d01c0f20310b00385111525088c80c0c05107642c401c40b103110483c6400b0307200c03e5000c3c02c2c0c03152100d01e100c40461071365074805504503400040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 608458237 1250 608456987 608456993
    0x3c0706031e0b031e030904020f070506010f0b120c0c060a0f0b0604030b18150c04030302010b0609011e03021c0b03061e011401050706060909020906100e010c050a0b0103 74
    0x2200000c10000389400e0448480d4100e00c400342d44900241d240c1c540c215400f00c0200d14030407018994039400c0001101e082412103804a000c9034400c2e2091000700c280401c01c0800c0010402542d805012f80d8807041003160b15005483c071050051140c55942804a140002c01c2c030030407002681c2d8030005000c01c0ba101d43c18a080050000c102440d04071070254140300340320200c0c0c200001110b080703e80c041c0c940070190f500c00382059848121404903c80a010b5042103c204007404640c0c1405500038900341c0e40d4881c503500c1c01a0031078000100c50750090b03000b40800e0145a8200c100c0811000c001e2001c0308052011080c101c5c028805c0112110b1030300180b00d14603030080c0644c3d2050b41400000e80c00c44002c1e8039041421048000048000303201d0409400060110207a0121031109012040c10914100400340c1d660105031807107900316001386039032100c8030b0003546800c0441c1e58000009542000324040500c1d401442c00901c43eaa040c14002008119010080b00300200c02c0d07e150445105040341d44c40b0301d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 608459487 1250 608458237 608458241
    0x1e1602041406181009020f0f071a0907230a031718030c1f03020405060d0c230904090f12030629030f07050d090309173c070603 56
    0x180b4814025114030640704940428080e2050081000803141303c81d440c03034035070104040d5114840c2c03c01c84050500070411242008000350202601c03444140036020b541000c3d800544000400c21005039001c208104183c0151000340d0104001403c1c01c0c0114914250224800d4441540010180c209880f5102d0384800800702030121000c200c001311079804001801c06580d4110030454036030262841700c245c040c035902c5114041000b4a607040c05400e09a071313400043e8a0741c00c1410b00000301500c1d0300024181652043c5451601c140f02c0c8808200390000311070782021400391800490190380e1380e08880c2c051140e1050008102036001414032030780d008940000f000307094a840303284143d1581e804580c02c01201103074002d090b03c600996203030440d6217081c200d41407108068a107505014082000c1042751040b0700849114500075141d111200d07182544a00030301c0d00da00407020603504181007124007800e9800b0540c0c0026000f2140c4d4003181c0800341c5044200d072a800001c4601e200746030380000c0c4d481d055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 608460737 1250 608459487 608459491
    0x1e050105150a0509060118170d0905010c11040b0301090803130201110601080a080a050403020d0b01030c091e0c020f0d0e0a061718100c030f050a021e16020414 70
    0x541d40800e04072001e40184040b68074079015299208107850700041c404d500c2000f0350f01c5500340310061038a000f980c03041c80081540149101c030752140c000c505180481d039000321201c4010b20083c03070720f00040301c1c4070344a5065041508010f240b00d25100d480f0054155000d4102c0800c50350412501aa00c0c140118280c608122110040b404184501c2400d640c0344070201c0da40307040340d103202c000d003940e0407441d600c03180740303034800a01101440b00334800880582c40700c1c030300541b1040c822800c2514650460070b06182203503103648104803070307402c3c8103040815103487d1030343c0401c64000c40d0022802800010040c0d05001403d6075070046441070502d1100025400110710b0481c0070152609201b098468400b01c415501c2020986034510b03405002c10842c6000e03021000f1201c2e00e580980c1d510300321110baa1020745821000b41d00c000307621060741c458000000c1c4285070b000300005004501e0700c101c02c1d001c1c48520010901d4014070b501d020031842c6445080c24184104a9070041080200025101780c1d90340320081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 608461987 1250 608460737 608460751
    0xb1c090c05190f0b030f0c0915070303091502091e03030f0304200301020304030c12200102040503071205062707090204170d09140613080a0201180b07030c1e050105 72
    0xf0f404002200b0002a04032800381510480b0f1810341c2d501c101c3c2821250344101e24480e0403610380680c81c0a4103088402074100140309543c04542c079121402c0c0040c1912210380c4202c1160301c1008000305981c1d4001c0c1c40c103508080c111500c101d0807000000030703040d8080e9003072160700b4400000810040114441a106d0304140410b1600a050341007828503080f404104e4006010a9407480070201154280905100c1c0020b6032400322000d008410203041022070200354002e450f0340203d014030036482c0a01840c0003030020422100c8906005031240c13a80d90340f000e004980c400380903049a161078a02d415054550740e01c03030811103006070307512900e4030000c2d413041c401c07920074203a90404804024008a0200d42d0300c1d0b142d540d031710f40740c505103000700000590700700403140e01c600c0c10480c03207410072604080f00340246030050141c00d80c0d8809000260900d4050458030344103040e02c01c0d00f40285d946420a60307420030b4152a08405813041c43ca03040c038481c0c2d21001910400c40342c2c1d4031603400300b00e41504100d01c0b07550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 608463237 1250 608461987 608462009
    0x121204090b1306031a04020f181501020c13050705190e0f1e01030b030c04180201090605040f0b0f0706140106030e0a0201120f0b0d0c0509010b1c090c0519 68
    0x4025540b09003207800c82e01004060203030020031048a0103034681c1d04e680140c00102800c10340100640080c040c80641102610000d0300001000000d0390303d01030003182d803c0700380080d026981c8400b0008100c0ca0101181d03a1400b9502c07000309440c41d102e2401d075410034406070002d203000d40e85c00b04042c0c203103010786100314420301c1e900300190703018202038000c0043d0355590f41c208850000f10318015000b038501c0c000c07016007500c96082c140201e40c2d60760080303100201905450102c03880c0325000060040c001d6400000a1000422041158801c0c40f2034507002c880b41c541261ba00e07042c0c1c41006010521a542c00580710904190444c070510400c2900706040300c005da00c0401c0462641b014840c1c50740416100a404542010585405030205402c85210024403d50018100101e0000640885004103080d02d040100400c1170203c1d04150101e2400b401400c1241f9040201d13034503e540c2c42400d49004035141a0f01c610703009080200070341100010700f2004211b0803402c119a4070064041c2010f100e1100c0c020307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 608464487 1250 608463237 608463259
    0x403061514010c110406090b10110706030e0a120201020903011505220e03030c0c0d030b091302150a18121106030c0706050106050910020714121204090b 67
    0x84a80448502250900300c1e14041107100c0c48010b44200f4900361040c0d65000315034441c01c0f5955210320600c3c002d085c031503d00042404200e818080205480d0301001c05000f01c4240c0044c80343c2d00069204100d030f003d86004502986641e60071401d0144030f8000420f8070700c640e0b001c0201c3c140c040d0040e00302130600703400801c41491415200c014010040c42242d0304407800c10541c1154900886408404104a00f0081a05410201e1103461640126110310440c0ca0102d070400070b211041c04400798844403403a080c0150002d400014415003030242c015070200e11031061610454035942c503603190408c8452507540c6c0351601100064240315441d21241e1000e22004e20100f00c1608080441e0380345a041614950441100014003040d030f03001a255004100c011b201700e0740003604600605004c1d28081e52915151110388042c40040c41e00703a00f1000542d00400000e101000c076042c01f80d01c040c00700716860507035020007050107410103400642a51000100190100e1400116000285c0c10306040c0c130a08015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 608465737 1250 608464487 608464511
    0xe0c0307030b07030e1e0c0a06030516120b0306010f080f160e10080111360f01091a03040201020f031305040f0f020a0c02090c09090c0706180602040306 67
    0x1a084070700008100140c10404556240d03c079a10030350850800d14101d0b080b10508103040000c4c1c0210680e8000640c0c04900d00862605000e0a500b00900d07150800b801242044030b004226241440c84800410600e0803040c031250305150030402c1014006400d540207561201b0251001d00110f005010803440340c200b0200c2d01100000326111080030b8038141c6031001c2c1c2003000d9601c008030701520031a500311f54074a011032169004e203d000e6609100c03a540c16601c1500300b8003000c2c46107503031801c40301000c0d20400714505074035594071095040c0000c0303501905c41e008036030050310021079075000707082142d490907140b888820450000f140254001d80132a05404840383c40e06130b880c4110304401c032030030003040020001c3c0d0800b60028110040782900100e5503100c000c9413282260090448103000a40843c0030000350300304801d00641055840d284c3e82e141403904800f098206401070246010b0b40000100308041c046a81c0c0420100c00c10050031008480b258100500071b900140010345003907150014640b20303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 608466987 1250 608465737 608465743
    0x30c0b0f090919110c032d0406030209040b010f0503040b07030e1504020f0402280306030b0f071e020a110d050102041e06020601030c030305070c080105010b07050c0604031a0c0903010f0e0c03 84
    0xc005d02c10004502c1c002035010340001b171100042c00c4000351040c0050144035140503802800280c005581d006840e24010401c01c41510742a205190500032901c0d81041816880003c40354081d8002d01190441e03141e02c80114002e040700e403108a1305004401441d420784c080025240e01440c000c8544510820445040100700d10980000190028400e440b2648555503541a641c010b0305505000410940d20784540201e5601180c03000b40601c1c8600c03c05c0342803504540942451014100721043d0311240c400040e50f42c0c1c85441000d845115402c50050722551600e02207510607512200940d01d6566900300a15074160081a0b008801801c0c400410381c01e20005441741225000101c01103541d25648082e00e031907001d41010f80381070000c0c01011030990000d00990307009100c4072801030b68035001c500b003160a010f61106854880d1604000c01c0000c0386c00c41403124004c406403215a52030b5142d00000c1d82003840f03954105d54055081518104602c5955403100d10308091450640e090303101071104044e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 608468237 1250 608466987 608466997
    0x1e02010605011418123a081b0705030c12030f160e060d02090a03150f0e0a020f03030403050a0303140a09050d08090c090a051b0301030c0b0f09091911 66
    0x50458581c401341e88030b51412480e01c0704a07500007016510018080c0ea0244d42145140307502040c080420f9403000032003210b5002400141a030783c90907070904e0030310741c0e9180d5111540e00424150002d000c505801401818021200c2d11503040007100c0c0b030711a40542c00c2007550002c0b207194641c1410000090000000034001003040f021640e151406803a4800811050b03030008076050040e80da007448888030070340f121070300350000e54002c1c440e040759500a1080001036482808112a03184c5c2071103500b01e9118000564600030b140d040312004807000c1d442d0301003451401a94070240c5940300d24204c0d0400c0c0341c0c05074401d50403400101400c00d416581c2c40013010130303680074042c004c00340ea1101300c3c0382c1c4009100c0c105440c5c101c41d025040e03882d041100000580020000e544c00c050003680d8105000000301c0d00b40321004940c1420340c0782800c0d58519201e41482c41002d1052085d01000003440e807590022030001c0341c0da00c0f0f400038140b4089080c4008810700101c0000c00381d0010b9490030011204101c40f07601503c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 608469487 1250 608468237 608468257
    0x2030a03092102010609050a0624051c0204080c0f03030307030506061318051302090408030907090614100203031902090a08190b0705070f030e011e020106050114 71
    0x545040108102140200264842500e1080308000607030b00d1925900460802030301103034000b040307050503c0c0405080300c0c4080c140d40c4e005841d02e042000b0800b074030b44d001420315180f03d0140c81070f1449240d0666252241100f8080203442c484a030508080d004c0c3d003d0720660f203040085501500e501000d10010410300e401643d45035006000041c031031407094120650000c0058503580c2000d00000b49444030701040c1e0455040044c0445012441d28540e102c1c4542c0041c1c6483c020040704d00325004540d45003405000600203c100200003202000c081207141e000305059401003103516076841000c80c01e642d80841062203818850310702003040788000180c034002c0c184c0e081802503682c68000381c40007c0d4403c021403074104015040021394078070184008076403100e000c0680b0081346a07a10b894440c0003001004141448000d00004001c100300c40c01032001d2940c07505000140d409a100181c0c0c203072040344002100c10710142c0a0003405d980c19007200313040300c1c020380300d0480c2c4811300320010160703006d2210a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 608470737 1250 608469487 608469493
    0x708100e0c04181e061811070201082d16080903030c0702040612061d0a230a050616021005060d0303051b0d0614060c07032402210105030d02 62
    0x10301606418120f034040d2000720301c40014090310303050300254038089101c00c00e00d01d803541d80c0c0040040d45521901e411614541c04010810164482132a2145006940d4044e0400c03503241d0000c0c4030507600c22200c03620305945558203413150a041e6220740d140c0c0d0b0100c071920103007040713401280860741c040c0310403038010078903240550b05694480820156940101000380da105480e01c0001078510042d00d513901300c46005500100300d0404c4d10310104e02c40070072844480b0050340030a540b01d010407041000c0032014400704400006070414110390317603e040310310600500f40c0d00500c01440040156000704d107070308035640c2c0c013910030300b4181c2c0c1c40c02c0301113480c11101982c0141011001c000020310030b902581e8071141d0441d140c0c0c15540c40380b042c81d016401464042100540e80c100a000400300701c00900006001142c115240039400204903031076010501c801060080300c2c0c41001d94a0040c03100311403a40383c44020864690707011308024050460105443c240b00900350300046100e040209680766207052603001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 608471987 1250 608470737 608470739
    0x50c0603130c0f090e07120b06040209040e0c0301060f0b030606220305010204030b060a060512060406120b0a0516090b0a0504150305090c010905030a0204050604020d050708100e0c04 80
    0x24000103038001400000c0707503880210490001800149044050011640490400c501303008454003110400000509145e0001d0405c201c42000c2c010f69020b0b00b9486040030300305071501004034018ac000c0da10016031082c2803110842202d000001c01c00e40048040f0000c1c46200d44c1c48905501010f150300030b41c2c00a060800c0002c205080000c000e252281c4030180c4501001c50880600307490000d04d8000b101c840c0d40014040060281e5403526641089084a00c200d1b49032030300d0000b8201c0d125a0900c1d580308825600010030780e5a0b6984101c0081071090801c101c16000f9203401000007108440040d6000e1800f0041881c4003210124603100c01110b03180c0c1883c55043c482c00300031a401c6080c8943c2008010080810f188107280c004c460f00001549000c1180e0500c2c0a2103810401e10b0131010341007180d008420800e55400180c0c1c5442d0b9501600c00183c0c0d0385481c2c0210f0082d1081090320700c1d010b4140814050065446029140f01e0003220706692030054881d031110103d030205452050b80b104003400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 608473237 1250 608471987 608471989
    0x2041d10050618030f01050c03040605370e12130807051011070b1603110c0604060302091503010305070f061d2b061506090b0a080c13180b030307050c 66
    0x280881d403c1002001c8446003e9480c1500c1d083d680304450120445070007000f4401080013074029182c12000370036614441c222440c03a420140300e0f80004002e480749608801042da01c145600044294000d10261100c00300e9114400c081d503845201030b0076070100c3c49400000c0700c19010605500352040209481c40c21008000b04403100d0703400b6454040d043c0510301c3c0019207411744000a03c01000c032088081b103440341500b4040d00d00541344140c00000d4210910000c070070780c0c0720070494060b6031190500580303424846021031100302c241048046903034800800441072100008449080b41d83d0300c501503481c542c40310401c440d9101100040c0900c80140740b95803c69103000304214441e080852141404407901110340081036441d50000c0d154569107a120102c182c0820030500003400301740c00d1820b59a031800c88a21181d202e205d50302004c0001c0200070400b40e144003002c48903014901d91030700716503a40b0389444540040100011504140c580031162489040c0130064a00264100c0050521412444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 608474487 1250 608473237 608473267
    0xf0c180509090d05071a130b061002251715070f0c020607020d050a03120e19120e060a0e0f090f06131b0801140105120a0b0a0902041d100506 62
    0x1407040320f654441c180c91000c11403800606c58030424019080c145605a982031080022401801090280940c0342140509276000505d010010440d0380304000c40400341c1e41807401201407508101074441000790386022040d40080d050703038605170001d100c49454030791751016181c1520076401000460b082441003005450000b001e0500d450000e04810f503140983c0c2c0d250b0381081d020400c107e000c9850807486c07034183c851610a140656031130400038203044030700814403620b014030307904e006000724044802102503c0c802c22181007041000b52415403201c0c001940541104072101c1c4a500502400d0100d48141c80d1140c070b158022241130310400925182c041c14840c50a141d5988c600e1041c0d101c04a9252f00f07920182c4161260b1b400b555481d2b4070b035060116008070100c01c000d41342e04026080c0905498280c0326020550030141203140000e0010711800810180d904903030048066510210700015080f0068801c2241f038045507101401968a01e1000281c2d5500d0340900c2e03400040610906907401640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 608475737 1250 608474487 608474497
    0x601111504120f211404141203010617060d0f0506010e0906011202040507020109140a0b0a051015020c1801060305100e0c070f06020c0703030f0f0e010509040f0c180509090d05 77
    0x241074003044031000c0a4401005d0001a0350440d040032040080d1070510100b4445070740e8845041c0f032000d285500d044001081140320700c104400442010002c00c01d1607503900190700320554400d90681c0c8001071810f003a174455909200304403c0044210009041c0c080c041b4605040e105a01203449440300a6005e1000078540184004159981d0f0f41e90b060100d180e1400410390b040481008111140c194030f400c62880401810b403803185030800013440520003042c0024425565005a8100e608540240482c900311114441035080381614070344000701440301200b03030f041e51801d440520080c1c1352504000050b00e6948110040d00310f0603c08111501e0b0844000e080341d034081c030b100000300000307501e0307100807a0b0142d44854250780c0002820410980c2050400500502c10706000d0715003280120050269811102c3d103a04008000982d00351540d1603501c0b0015240c40404100021010504068040c43d00c0700c0014210500441000406103040300d19144500d0300031002e041840026038050340c035078108d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 608476987 1250 608475737 608475797
    0x1e1407030528090801051b2b02040f08031306080c1c090302010c140a12091e380744040b0402090601111504120f 50
    0x40000080d940480d40c444420400242e0b660108088500000f5100d05001d0f40400026410a020410800700d00b500700350550381842c10181d40e46106120072480281401c8103c0c002d40c4082da020b40311840194040c0041d105540ca1500c0440c0c0c440e021a50f503401000909610001600018002e851050090356084556a2002806c104450304010301004007031503d264002e42e02c01c1044141542401100072180190804400a005205103903150b407040c203644100b41b0604042c9080c2d03601190340460885a0042c65607560300c03001e1400d00001c22100c0c0c80c259043c10800c0400e0706645900e44034070620a602c01c2c24103d070b804084644d01612100182820140910314030040090140325400c40c140c3c0c10041c404013a560205081c4038414a580f454142414080c03004007c00918a00c0f21650801d0301156448201d58440004a0b01a00007050000703450189600c1880d004032600e5200307010b6031140840514078881c0c84403c694103420003a00c0c0c4c0c000b034184000008001d001318400c081e4805 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 608478237 1250 608476987 608476997
    0x70618080a08041209182d05190608120a2a0506010501080c0d0510080f1006091503030c0212031804110304020a0b030c0d110901020d0804050d11010b09161e140703 72
    0x4180156071030240c0c07d10000e544040c0c1c99400b0041d600c500c0d162010340c018112502003000e1410188a00d035150707050028058065000900b940c0f041d4001d4004a485200c0c078a0020040c2c120002d1041a04106e2881250a440760500200d12580502005481a2808018941000400b0002d2005810050001c100c401e0135414045139820b014441c03041d81d80c80c154001c020780600d2241b00803c40728030fa4401c0301781074a000c12050701504403507490802c581d0946080c0c0e0001109000043c0c00c81240c501450329480002824480704c03441040305107049504840801140102c0742e040c0ca001d100448000390b0103602d070701c410701c50090084003541d0040d403602c00e040e00300314445140004441d8101d07411a400903020800118569041100904c00d06e00d07440d02107d1800c02d03646542d9200e070315000600c2803040031109070000100075441200d0079400203020040380d060580d060320341010350400420010380c181020030740c0d4050304003555503440ca80340d41e00682000171401000040c2c002c6142142081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 608479487 1250 608478237 608478281
    0x1d01050403060207030503041205030408120702030913050115090f062a030801210b010e2806031b060e04020304020a050306070f23070618080a0804120918 68
    0x101248084c1110622907103070340d9502d040c1420000c000c904200503400400004104000015210b4801e6030000b18880d0b02603600e546901e01c0036805c50007050005600481548441140715205420060481300702c12014100c142082ea0100c5000701d1034014070756503400050040164920404040000c030307a400b480050f094242036980000004001020b030b000032580e0005011400e0b4690244081907200c885c9000c0014542c0e68a001102d0144078460100b0001000140030020b01017807031507507a80403424008500908a03600009143d5800b040c0c0740110100105240502081c80102c00e41b44036031103001220810b0000c000203580002d200700d8200719003082c0051140c038108201402000130380c0350414000a1014000d21340c40000c00c0010380d4200f0a0f0030b952071520740c80200c415064026101081810f2000c0289414160f0b104c0001c14090b00000d8a10440745c0c8000e120b4001c078031a0400808a4150b04422903a641c041d00507031445071084103c1c0100703668260300180196203040c444070144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 608480737 1250 608479487 608479493
    0xe070201110313050613030c03030b030c04090602040e0a290f090108030d0c030b0f01180812030117011407080a0905100b03071a0a080a0b0a0609241d01050403 70
    0x550025240c20f0310b40030200c0464820420b090228641c8082c0b030040c022500f00c0f0f43d4400500e0846e800e0405803c0c1a5521603207121920b00307200c3c00341d00700301c0030704144400905490120000e40c002c0c07003602c000b600d080b800720f45298411700480701c00c003100000103411308513004011510412104d0266070701041d90642013100f40c45014855000b1310604002e582c41e2481c040003081940d9140303c040041529290305c03000c0d5541c03500c40d03042140c4000e20f0498440c06c082d4031641001081030300004238034031508185052400c010780085050380e102201074649058028055400e0b1000f40403000d1504443e400010b03040e6120300000c0b0741c003000041012842d04a070761103241c00c01e450012e01d40c0c05591a0301e403410a508082010b0f40003803034044500d5091000c80b18044a41d400340c0c0b640c4100304506030300454040c0701d15402c0320b0421500200801205941c60001405050340d511440b081c100c10007040c006110000a142d1041d0038007512802001c04680400e02a2515403048160510205200100c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 608481987 1250 608480737 608480771
    0x305150903130b07060f0b06041418040b250206010909030318030201201e0a090801060e0a0f2c07030c0311090c0a020312041e05010f06050105040506040e070201 71
    0x400f000c81c0f040c0d549020904111065404140e4000146401c00c0160354544e19020700301e40494444031601c200103940360700010b10382152808400c0321600301405010501c030440342080d01130140b80c1d00e0a01c100b007840310b0001e40007054005c0030015030846801008030075881e400120610f8030900e0700280c000c0031000d40950f5078141e00e00a600603035603002c91f82001d00b0140e040074400344a01c01840c3c00c0c1941060711900c0c00c640041e81500494001c15080380c030030700441241003d40040780c021f01c48240c5840582500000c100c41c3c1940c21814200003041c00301552107040b0840f9110300e820b038070385014070305040601084c0783d4010107688200748000011070741c44040e9138003441c0b0a80004840c001c014082258250019204c4a00514200500b541103034000046407902d00d040801340042c2d541e2410441030600018075a01151400202c011007000b8065000d07420041d00c0c02c4c400c101302512000119a103000344c2c080c00c0c3d000381080000f032106d58078400300c08c3d51241c010720010650728904000d07885 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 608483237 1250 608481987 608481989
    0x70c02060a1d0f0901030219080604030309120905030c0f060d0204233c040c0c0b0f0c070f1502190f020307170903100c09090e0601030515090313 64
    0x104400342c0ba41060018009401c01900102c1d03090490303141e5480000c1d660071040c03000a105400074494a141d500c1d560100200818490064602619160501034003400014104848410b82c1060b1181071501407084003054440c00f41c0144000d241290a01401c071402c900150351200060140910200a9000a00281880501d8052821301002c1c285100300321940c010b510038256005440043c420f403040100741c8035a88002113240380c1e42040343d0a130703c0f52a0360045812501f0582a414802d03000603160000504c118400711256444c001100000c42c81a24090100c190030010000801e80e51400e8407203c0d03014503a0215513460210170a81280d02c4542e02e40514980041c40d081d5180c2c2054040000395540e001551030002c19030b071961280040011032a440340004207401c1881d8404102401403410324050400410b103c4640c0a08800c9443c4a55201c0504040c040790a01e0004544103040703e900c88010821210a404042c00c0004020901304140c4010300c628203400042180c428 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 608484487 1250 608483237 608483257
    0x40e0109051e010f030507150503070f0e030105010f050f03010b012c1e0117010b07140c0a0905012603070627030306090f02280c080d02040f061b030305070c0206 71
    0x4c10f1041c510f1800c1c5041c01d540b80d00c1181c42c41c042c0038126201d642c02000b107a502241600e0b000340c900b260010180c6194002c0303019141c141d8a01400426413541c0325401c00151303001110104841e0b88800c0825090380d035001d100c240000c002901c0200c020808454024544a114100348440ca1026000c01c04800107400d03540c100803a41d14100400c0c0d6004040840c000d0070f0480b1619441d0305113800034050740b0a5000060074dc103d10262104540e905004010034145c0061010044503074540508000e01000e000d507004d45007913281c5040d91105040342802d40c42c040d16000c7c2d410514180c54480091903100c00d40403290010141100160404150112680c1e11907200001c0305410310380c2c80c80c1280c0c5005500301c402441001116289800c1d64060040c03217220907034401a00304000f104072010241c290300101282c001084040076880c480c2c02030030a40e1428030654102543d40c1d002101c590031582c40aa48200b20f0800c80d1010078440c0e000340c0c3c2e01c9100750500c21b0351400f00b580482c1c4030b680001490 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 608485737 1250 608484487 608484509
    0xa110616030e030c0619021b0c030705010309030c02090618040602120a0626030d020706020c10060e0a11090d06021e0901200f1504030212040e0109051e01 68
    0x100d02915010301c01c1e003000c8000c80005504114014042955a17000035120350b868184542d840342c6c420740683c04803a4107154400c071031407550100f01c0c140c55484c1701460381e030781c8a405108804105540300b032007040c403001d40507590324194503455001c0c0451094003801054000e0b00070b00402000144044e40036019030301c6040c00580e111000d44055020000c00381100f110141001c10402500704074071401c61848550880f030161284450300d4113072440c861048803041ca0f90001c43c80d042403100701d60141544203014402da8480080121521044030b0701c5002e0a15011a0100071408130341d85540300390040c0e103044480d1450704000b000000c040e0740d00030800b140d0540c1c0016000d629a40c4048203ca00248111549428034440c1d00c00a850786c00140f54218021100703261190505604102c2034080b0040c81003641d0b01c1c0c050102c40d28a1002c0d084800f50b01500c120500c903080104802d01310750450342c03501120000c59081892900c05400064002540c400d41c1788071841c00380040807501402400d0f22504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 608486987 1250 608485737 608485771
    0x30203010e100b030304050a0608100503070807030606080312072a0f30050903161716030f0f02030a1704080c060304200d080a12050a020703140a1106 66
    0x10074000d0f190103407601c0c0d0094100303000400c059203500381d13441d060b1580c60038007000c0c0350307211004110802e1180e880f46a0510500c0c40000c1c611702c0c0030500000b500c1c0074500500a09884c3c400b116504e2240c2031880b0280ca01e070a001409440c82018003060003010788071010584960804a0303100310702c052605503201480c10901c507080244c1000c00146030000090b1400001e0f480902248401e450080c4240a010300052841e40d103a40611540484404c062008845680c40b0036000c0e0351030b04e91030340380781d014403c2d0040701140c551900e005208480d8091001c426000203952001c454820b481c2c0126054401c0011150005a18909140d0603511440c010b03a10395180607001443c288511255500448041060001254000030640c828000748006805440d07041400328000a164080c06415004041240038481da4400c040e0325003800b481205100a482e01c49051040380b00c2c150004000c10007244aa80e03c0c001007034090600c0181d1400e241e0001c9450103e4242402c00440d80300c0400e40800c81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 608488237 1250 608486987 608487013
    0xf160e090f1f0c020607020709020f16061a03070803030115050d020c25120206031012080405040c050a0f120b0301060905090615100806030a151a01110d05030a06030203010e 76
    0x801c89482030310f0b600c014842030800701d0380a5240c51141c000c0c501074039000620608841145000c5421066502420360009901c03420f103480142410300e240290311003240e202c85100d1400040740000c0d00c000c60055851a4a001d42e200704498450300c00e80d003402402d100103a4688003904c082c00041031480060240078070220418a00310754604484150030690f1101400041d200940d2180c6603641910a1541c85e2100c0f0030001841c052070f07000444105004040008100300580980121041658248040e0924480644160269055220000300390481c100aa0b0380b050300307802da40d14240380300040c01c0c0c0c031020007007402d41c1d00d00d41100035050b8607a0240586043c04003c0e003603002000841141104404d0030000d6203060b0060301c09402c10000e00d020500c15079040c0401081e0550040c0000d25840c0004070080240c0b51150380796400c0034450410340d100d03501400d10950500380841c082c21401100000594041e00080d004801e101d40d034070030110040c1c909103e00401c13698400010440e44034012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 608489487 1250 608488237 608488241
    0x14060703020f04030807020a080a03050d0e0102030f0a09020409020a120b060a1412071805060319020f040c02030c0109061b14030402150c06010311030f160e090f1f 72
    0xa81400101807041140700303808038204003903505030380d80690610b60310010350000480b000d00d95002410f5034012102c40b03c0401d6002001084c42201c507010038019080014103c908030702003100c0ca00d16003c504800034140e402c030340d40040351443c801440050090070b2034000c62828a1507030862002e080c0328070b0b215400e010b883c440855000d0710032105040070310304215880346441001e103c0e141c0103e112481b03242c00c60000703004101c043c252440e45400042c0514801c20081c02d403c3d61400d0081c042c81e40300c84000c2e0a02507840408907005805801c0c441c3c1a602070000801c1c0b1a40f00b00210700050200c440603e600f8000c4a9070203024407404580e502a80d2800c1c50007040c0c002902050010150380d00703101c41c1150083d40ea1140d0121010310007803010656403603042c0301d01600315500d40500c1d8004810400107030010581440c1c140e040310203025041c091242e841c1ca81925100701c0c15044c0b01c080000f581c0200280d680314130842c01703540905030206105890010010131981e020b103504034014502843c14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 608490737 1250 608489487 608489491
    0x120f030a020f19062a03150b0a080114060f1201050a0608040c14041b030615050403050a2018010302011403071b03051b071802030f0a0b03191406 64
    0x118020b0f000c0075004401c07036101c01e503900724020800342c1c8031243c5c00c030000300c4079032a4181d80689810303005000f146400014002d0001500d80202c6051125020036641c06100030780300402d2181d120f42503a642041b000c01100c2d1554441c440c0d0180301048008078036040b407005002d0240302d1015014540d410312040141100d69034001008000e0801e0070040031424101c228811103080740561180c80e0310314000300e0050300340030419048013540c800710368110650552010080300c60701030403401c21481e0404102c90b01c3c4218480a09154000b4000d203000c40d400010325040040304501510012900601299084040f031007400700f11800303980108190350300700b0406440010b80805043c503520740088041d00c0012043d42d8500082d80c090001810107001e241159444440503054644805629052650301c0240d405100c03c500d0607003c020010003194000d48ac003071200c1e0400803032160b4804041c040144019500d45a0521442c0700c000d40380d44041c03030000f07221400b40c20000c21101c50180031038907001c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 608491987 1250 608490737 608490763
    0x14130f080d17040305090a0b0f0703020723130b040603080711010f2c0a260c030a080a03020d051005090907080712080f0a0315060e09060f120f030a02 66
    0x21000b5400a481440450780c86039040c10032680340c244103000702d085880b071038102d01c012110002e440000d5821040c003a101c01803180d401c0702e5606407900450241701040301d51080807a5225460b00710140342428805143d800705101c0003136003400e8000080c098400940c000d07115400c0003c0d400003848003215080b1001282030a1080980e6007500c001005544400b00c604140d40f0010794030782c0500c5c4915420b06032007a000300100c0c0b01e66103401032442d80b002c26041c080703942c091490303140f40144000f05d5080d01c00c61000f80901022030341c2d1384840ea940c0d44a40300000416500300248901c00081c2c0c46624000c00a04002d1840d060030041406002040980189202d138042e000c10040b4000004100302910301e41854091035201c1752502000d5409042c81c04d58a90001080550340d595141d4040320426850800386000c80d981c03154191a0310001c07a6805801032803074030005d440717810405009404d448000d80f43d000503d500050303241c101100541165055000011141400b5038100030721541c55034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 608493237 1250 608491987 608491997
    0x110304030f020a0816050409050f0f0102030709060c0c061107080a030305071b020a06110c042324010503060a1203020a030e040c020a0204230f0417040608040314130f080d 75
    0x20300c01089907400617841c0304e658456a01e800c0132500300b010034850300742400d801404581d800c240001d8814041e40044800500045100500146040c030030280070400e681c110001c81c1005051074004c94124a518a4100062040c50b000051300b00003002a510703294000e98000030f1700c0c02e004000401c0031a806e00540d5a81d4941e00d40c241c05a40c9808001e0200c40b51400c0c019407000c2104900c5003440c0004030300c0c9620610b0003100400c140069040642c825080c088404603503030b0b0b0114002441c0032807200f1440c88c40030302c2c8034034100d65005400441d040680140301c907114135914002890005c04401c421001608038544041c201500308200d03070b81640003100e003404041c1843c00004d56480d001c410185c4999190600c221050084907220041d00e010010300d0061484c1898031000004c1d0290307801c4407840d200380a89038541143e141039074140d60072039072154101e444030b44003151308604100e00300f40703200010402405c003c000b9a0340c0b8070041180f1380700000514038103005242403540381c0f04280e007405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 608494487 1250 608493237 608493253
    0x709050103062315070b01050f03011503060528020d0605060c0a0b0406090b040c1404150e0907230f0306010302010e0d1406010e091b0102100903110304030f020a08 72
    0x810030240e000030090790120308000b0460703400113082400001d148040c0114005012010b12120002c0d00303068401c146c0b003081c0007003580801d1608031607081d00445a80f00b0021024000604941c101903008081c4040c0f081310030381c194000d404583d0003400c1035030544c0d0780012001d01e1040076014400c0102400ca074200d0400040301d075015151849500b0040c240302017000060104059540140303031058004403125a103140ca481c2c507008a48103800b4600108012a40209152409016440380b03c10221681101545840f0313084aaa10001c0d2990301070780201078000c1207286000d29000800c0e501d480100a8100100041c00282802d49030441c1c002d802000040c009130342c00030342440160100351285410306c60942000ca18000d501d05d0000e40301d020b4a4000241a040e14200b107000700710310800e0390114011100b1200400b4050300032240580c20940300c010240010b0f5000c221a107000381440030040064001c107506580c040c1d00115081c0c51200f0400b015801c0215000c009000c215000b80034813 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 608495737 1250 608494487 608494499
    0x1107110d05030d0209010306030c06050c07090603050a02010c030329360c070605040606051309030206010611070509011e062d1103120a0b0301060506030a020d23070905010306 77
    0xa103d86201e980c030003a00010114540e91003603000c0710055411203c114401612a1401811a031002000314a40d00c0f0f1810080b500d800148103610441f41c0c484001c201c440c0c0994015194600e1010041d418150b40d83d10341241440742003aa04804481151600b204281c04010001c4054401040c10103040c40d120032100c008007081280681946800c600c901c165541001c1e0403107c1c4954a40102031608040500c0b08003c40b0741c1014060710412644242c03e40c502d210064122000a2806130050307100c40010000ca5002c1c09400c000090120262207116072079a0110b00454420303030101d0742450603075007140742050850314014064811464200240f040ca0a9800309c41c154030321481111075500f07901c41d15110b00412001001807800e0054a85607260040d50103002e52045035540c1100341082c03034444a40c50184115019100c1c0106281d0030342e00c42c2c10500c0d00135000700309000c42140d904c1140c0707030b01081050403500e103a00d0703901c0c65003906103400080105107a00f50f5104a0626003030031024441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 608496987 1250 608495737 608495743
    0x8091e1c0519050c10020c03070b1624022d04150e030307060e010902040c09060c1103030f0c1006060c15051e0109061706040209010e04060f1107110d05 67
    0xb1404410201c1820b28050400742c0c10440501c807101da00500205000142039004107a05050303210450541e5190340d514212008180700b654184204181618081b60020303c2c11828000008100b803900991800c050388940100d03801250400c0c0807096049040c81c01c0c2e003115003132840310120403000d64109440c0030301d12008000c8121440e014841c4c611020711450300c0400554a2003508203800380002d58911b21404c0c002d100305c4105074041c0d41001031080050b8040c8101c02d003219095030701c0d031109252644407005000d15000f09107506000c10002c0307203c00d02028001d4100b60703c1030390243c000c40300c2c441c1d529002c603049680a081404010008800401c00c0b40a00b01189001c0c40e40200e01a521004844804440e008204c800751000000200e0000d260781c1c0150159100f207845425000280300340e8135a5914200d0b402540031a81d0303070047c81503240f41070800c0d0b003161168801258041601c64031000741c642d148948501141c02140b035038180610b010030382d030942c803065461410250003034079842c0d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 608498237 1250 608496987 608497003
    0x109060b190309050129030714010c020301020702030105040c180b03071a070b07020c1203040b0a11030f120f0a020c0a1101090503031308010e0706020c040908091e1c05 74
    0x4080401080c024401d80d00a803ca00c1005034003500030003505901080b54811000100c2400c90100d580c24030010301030600081002c1600c002250040c40c4094480045800358121002243c042d5024400038005071403d0098602440c49001c441107120308104028205403950000001003a084c5143c4550300e46000c505501611410407081c00022402c0042c0c0d812441100c8004240c3c081903001c00400c2035020589400300c81d01200d07446074149110903c03580d0703402640a001c83c0110108417054986009114807004e030900c03d0166410031303030380300340c007a403190890920401d00d9000700c0c1c1002002c840b00d0080503400403034250214204940d0200c0c0550f02c0b051900d0041044268941004040e80103c01d5040209070060880380c2c0d990000c8ca065411089520818900703600344035440d40c00140c041901e03000da8207554001c080e40780180e402c010180107240e038150b880e05800c1107030300d480392112544000d80340401080240400c1c002380c180060010f00401000c0142c12040941001a1011450390 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 608499487 1250 608498237 608498257
    0x718030b0402191806050405060a1a0c0a1202010b010f050301030506060d1e0302010e01060806040503030a020a090e090c011d181503030705100b0d020117071112120109060b 76
    0x3803020544010f5228035510740e40c000d0034001d141e1072880c16180009070400c00644200b44c40038041605c40794103102c1403c0b00d074000c0719012060f034480302e05960007940c00380c0b070410f502030708131900e403601c0e034807400d40101e512513919005135114214241c003940c01c02c2c0d0064002200345000e074039541c0345481e0951620b0020340001e1046030141041f005000c0030030070401801300c5404040d00d50390582c2c50701034020302d00b25071401065400d14100207400712010840610494011001d1851542c5078100344000354007240c03480042c40341c1c8200c003080180b0013102c2188074254607001808813100c0d481c0050012808808590f2580c0306c40b1901380001c0c0c0342c1181101c41c0c04d0750080406100d0321294482010320590448141d090302c400701e0743d4030502000003415025807403945000c00034000801c00740304003607135144000303804105041c01603510040c1d00340030070f9809402440c0c856006d0340c0038034565003020f843c407130100c10031007010450708d2800c5c00d6041c19500500c0032150420170646406072003039040c011002a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 608500737 1250 608499487 608499499
    0x2211c120203180d02250602190602120c120a050105101b020319020901080f190f1b141e0105071b0905070807030e0c1009030605010e0718030b0402 65
    0x710f26100382d50351030540c0c030354420340036201c4440c05404020750301c900301d0750b8076208040e510080c0c1e400800b803140407009580f1240c0c0540001d0125074060b501206240d18121890344e400c0060000fa034007030054160154034040903050755040110011b000940020f4200b00b4120700d000b0040140369100c9480b1070307410f01c180c24460109462401c4104075600c010102a4142c0142101031187e401c1c0102c044006510886000b00b250744c131802d840744e403000c50341ca83d010162320802d048016040540b0316056050b104040c1d81d00d02c0589965a41c84d420001c0c030a000782039000d2402030040c075880004094032810b050340e00079000700003401da20388140340004034141070220005107030051050800340035160365811141c40558550707920022004000c1114030100041001d008590700720b101c0d000f00061019a07900400f020001002040301030030b14074005109010002c04000b0014065000f4a4001c06110070a9905072034082c101920010128841e031110b04801c250070320008030602d0100c0e40007030701510a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 608501987 1250 608500737 608500741
    0x2060712061d07110304030507030305451e12011b111515040c030227040e060702030a050a0c0807050f0705040b0609060c0a02211c120203 61
    0x1100107150540200c58640351255800c40e101c030200c42014003903012507a80100003005488000d84a00650000800c10f802c11001040402c0c415400382c17803d01a1480405166284600d262100030455032400541e11031015203080300114011082c8100141a21140b20340110804030054420307c2a070068032401c001c40103003c00300f0b006d50001036003501c40100c0c5c01c4180b4406d600601401c20803500425035201e00c8000c03641d00510102c80600a0302c202090040d0f606001e405c11000c0c2c03d4004100d41056820300151000c0001208842c51b0682103c040200c410960414801520200c07146201c00c0c4c1d0191050101c440e5000085070349140c001e1500d00d489802d007170401ca888070416840030b00384c1e440100d030702410700c000400c01d554581200070451303075000d030b441c001c2c0400d4603501d000a59000e48140130046081c24204000c21294210314140c4803140752070703400104d444203c041001d1603582007107022000018200220240c1e040801c1c0141104405110014071501e0080881e803403068001c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 608503237 1250 608501987 608502017
    0x4060207030b0a0f090c032108071b05070f0f0b160b070201060e182104050f0102070e0c070201120e0c0d0f0c0303021c180e0c041d011a0a020607 64
    0x405540f1408000c00c0500c00c21400d400c1c4902e030300000e400256600000101038200c05a00070408c2e80c140c1115445030703c0c00c2d5854010540708045000c030f40011760001c1d2101c64001a90a20086028003104030042201c41c0c1020b40c014069021500034070b04004c4200000d000a08604d040d0f00031203940a50003001c0c0360b840c04012809054183d01c031a44810340d1b2014020008907a20802ca00d02c20b00304121440200c0c0c0041d140340c0046001e92040207a81c1c1040309101d40e041c401c49603000c210741801140c6e10305a4503149460000012108034443d603002140d031404543e444081c40314481c0b440c0400744a04001e500d060b545800c400c041c910301ca030080280c400c1c1008294024114501d400030b1101c8440750b503900b8042d403546000151451403607c0303a61554281400780411405808a4030715420483e0300380060400e0300074000d08055102c031004d01000440310b00d00e002c100f0341d008032460f00000551400ea2a004014201500314961650510080b02d8556001800c2c075408111864aa121580c2c420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 608504487 1250 608503237 608503241
    0x20603060913080a0c0b090c1305180703060c03060b03040b0f07210506091042030212130f020f01270819081606060510022104060207030b0a 62
    0x4014009900401e20f102e22581003030170080d0207400307003881488984d66484225116611940c0c800e0380402703d00340c04894804641d00c20740e40700d00400ba102401820707103d1a00d20380003182d1320454220b0340f215041080194103001c1c1c4001091006070b040e0a40c24160360f04110f0140013407001d0300312840d440020703075860f201d4a1403a40b84655401302c52b40684283c812100034040c2211100d02a0708060080380d0809001d480c134000320703400c0d01075100e8942030b0220038991104842030340e00c4403071054920802020582401d0511a1807094a0050792490568102082c0500086c842030301c407049001000003084403100c5078240b003070b41201c0550030780c100740e00142c903089003204003880e100c522900c0d2141c4110280b40d07041e0a803540795007203829104c96000310801c0070140c1c60000b8282c04090040d501c400200c048403940052040902090054451010417100f00044050500580c00030b050b00f2400950707580c690403510401043c0c00d20380790a203000030b580c40c0c1a620001301004550b800040c40080e075a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 608505737 1250 608504487 608504521
    0x307021c0c06110c060105150a050c070b03010b070c0801090305040302011809020409020409060b030c0412080405190510030b09070507140105091c030b0a0b0d14310206030609 77
    0x2c082c082001e502188904050750708540401e10030f074801c190011441e8900001032050300115201100e02d000304100007114076800500364598940308207800410000f4800015502030900d16644135212800c0303081c01004c1d60b44980c84020395034540581c1c1004a9401021642981c0d0203007094124040381d22080902041144c1c04000b00c2031010402040680d815002441110300718030090001310380780c8000034100d00c011b481400320400200010030405075001c6074201e9860049032001c0c2020f54410201d5822121180101141301fa50b4900307000328540820201207161f824a820801e40f900ca4020901600d03001d8480300038403002180340300411032461070200450311018000e200f24100040c20303a80c3d40031450944600034540c03500114195129102e0299a59002414010407900e824400b8075680d105ca0350448050340c0311a130640140101150f10307405460b80d1440c5809410030388080b030402004054000d5440c0590310760f0b00c1e0142e030b0b0741402c0e41e030800b500719071450407038074ac41541003c552a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 608506987 1250 608505737 608505743
    0x5090309090a0204230a03110303070b04081b0c0a0b09040906090b04051e060406050613051501080108010204060e060c0703052a220c032705120307021c0c 68
    0x3a280030428441100d0f00600200c40f205881035404440002c1d0101203c00d07440080b9800001e0130804001142c504039200c8840c80c0003600352460030403151a8220710322000c903825644844001442c0380a2000c485054000741e1080001c3d1200d0030000700051400e510911526000b49008608031146590b10741c88000355540c010010045400b0500e440c0d00c6101c000c0314185c0b5580034440c0596010a040c905405521030401e014021543e11984c40e07100400300600104d402540e504001a0b100009100c2d041c00388004c28002c0c010001c0f01e030001821a035050304502c0d1580d0041c4410416280c104281c04035a5400302c3c1c0c860348a000b41c1c1059441c00d076080d0f201409a02c0b4804112000481c3c48440302d824030100132002c140d00800506000f00020f00c5150b1905810164045c52a540903503805900c20003811320340030074543c81c1d44034064034054105400080641e861030400003002020007955400d42545d2410030304525207000041e403594504403480890070b05540d030751030140784035010988000354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 608508237 1250 608506987 608506999
    0x601020c0d0c03060b0306060d0b0c0403020d06090212030f0412080c03040605030f01080d0e0603060f04020a0f030b0405010f03021002030705010606080919050d180314010b092805090309 82
    0x740e50070400b450b001e0520054600b41e282c03950181080c100442c00a1181c50301402181c0c00c42c96580d51002050401051845a2401840003000580e503116030b038030b40349001c1c0c1e9010904102c14010001403a01c20f0030800d01c25071040040b68030005024081c3c80841c1d100200e62020034415050401051044a580d07008038007000401040c02500400910f0040440d0142c0c2d140342d070b07214203490341c0c0c98022030359900100328000303d49040b610746231004644c030010262100ba4010180c80218045e6044106060040b50002903013040c0b469061165a801e090112420710a5526066003d180100c160001074082e2104d4a0315041e86030003001129001940074008010f45580c500d00200301e414140c030462160b000f40044d40034400100d8400280c11a001744c0540f9181440420595410090f208281140c16440d2000000300300f94107070b0003031028000b10011801c2a00b100c00c0050019000f01035403ca000840e40c014141c1621509600000d203c2d0703800080c060300c890070094031318003c041d55a5442030b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 608509487 1250 608508237 608508259
    0x306160e0d1a040b07020d140301090c05091009151d010c02010c080c0106150c0b0c130e01090f0605031c03050703090b160908120304061107020303040b0705060f09150601020c 77
    0x3240c00d14a483c40340b00d1035070030780c1c0240320b61f000112640340e01c1aa0302c65080005100510400b44164442c2c000d036003803400c219280c04419808075015080750820f140100e20b00e03a4041060341654095080020701d98a0080403449032400d041900ca84000d0340141080801081c19045901444c3c050281c5034000018540302c3d03101142c2c42c0e01800340d600441000080c030450096102c1e02880d8803d07101940925800790303a070303505410440190080740005210040f01a800076010501c0303407104d8080c00380400003040400c0c2c0480f101d010750781164410f0f4001d522041008000c0340c0480842d0b00c084000745000700d495115044200c0180030020307405482940e1180a00201014000c0b03240b00c10580c81e15228030342983d414106490340c4104103000254001000090000f0785c0c140c1c040b24001c09141c00c4181401c2c030907000b03e45180c0054003c42880c07280010a1014860304111095110101d9440d100e90352600700110340c1c45d0344074403c2da8020f02c2142400b0540c903038028000343c80e064070098003824101d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 608510737 1250 608509487 608509493
    0x6160503040311040209090402010c051f0e1b090106081e0c1b07051c02060409020a091806031505151302120a06120308040c09020f090306160e0d1a04 66
    0x2a50042c80101c07060201016245442e04281c001d4481c5100020400c64282d6625001174480030090a0200d403a40203010300011680c05001a84c541007219910000d4100c40003941d0301e180012241440144201d1012907000d2665800402419215546080c8045845460318604d00c480c00a03076142c4c10382c004900f0041911041001303400090714a1240781462005030081c20b88403081d6001301c5404c041c00700c960100c08034505c0c496006807071000e413030b0381d140541d940440d60803030f000380c5484800661031510800c01c030341c001141c2010740d510341c240801c0000d1070341c1e0364a804240408a141c56043e241c1c0009241d021070302070448403414000c0c0200c041100706c01c1c01200250b0080c0412281100444085903955219210300400c1c2c500c8094202d25031350301c07030701d05450164005104030343d00c002903000881e4075003040c0090064141e020f0a495201d4140e5070406003080303001441380c5896040b45040c900c60305d90010391191a40010ba40a400703d030303924103100350140d00c90803488008a001038140420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 608511987 1250 608510737 608510743
    0x30e120a0f2c21100b150a0f1e1209050a1205030106270501050304020a0f0305100e0606100f020123041a15040b0a03050a0308010807050307060210020306061605 71
    0x1000004503501407001082d00c04203e41d004082c02c41942540c0103056928041695501080d400e0341d009050114110b0040145200faa00805180001a4031860b420103031980040030001c1c0070112007d9408440306c01000146107207075043e945011103803282c5a803000d03c801031014000454000b201000e110084000c060310380d610070703c201c000180c40b807602102404000101142886851410145034a10b08801100c840c3c0014001f664046030110b0300007224940c00806c2d200841c03145000c1c217000300308d01c1601c4044034007806290515030032981c100b10700781c0e4070201c4d003201c501282c0c1071007070304c5100c0d0f82405c0f80102000a2082d440803482695181900c01c8001000d10492140040c40b1901042281c0d0203207103402501c0900d9141058140718101d80303440d4120b014041c102411481d4011754980388d8919046001c4000e0340418203441c01131100160a1001030050441038000784686481c2c404025683c000c01d0b00f50107065503010011904554981003180d000002d10002c0d110f40c112507082c4291 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 608513237 1250 608511987 608512067
    0x40c0323070603060509040f03030e060a0504031d1f02030c070b13082a0d06020d052413090809090c0d050105180105270702030406030e120a0f 63
    0xe14400e0030800900507101c0e00034902070f070764003034002c0c04e054544e5661018511003408085040c50384803040342240040070030256104891402000c111414942009080041007018608401e180c2c03001d1031203c0e49a06c0114a00000e070040c1500700d000c46140300302d003540140315800c205800b0381c0c0000101002c0b074101500c08500054a11f00499980300c0b101e5a5845d6460340031000440300002038800390000c0c000c900710015025001c100080c040b03039641d5080703a0051010121039907441040c040414220345080f03101180440301d00002c003444500240821100840d003000c80c984401c10b01d0200403108058034022503000d411000b503818403588000c40303038010301c0c41601d1040c036044c0001602e2404420107050008000c180028990910007441032007100c840840f02102260313140300800042c40c602c1e00d44158015409140c4450070440010107a400c2607002807100d80c408150340003c0c1040e0011110601000d08050700070f80d50215040d42c5091030061005608040070308d00c007064603c4628225 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 608514487 1250 608513237 608513303
    0x2a090b090d02060d0b060d2703090e0405100603030504060315050a0b0f2205150909010b09031c050405030c040605060f09120d080a06091802040f020904150501090602030c15040c03 79
    0x82281c8c0c09160210701640070004050000340d0100c5d0708000a00b150f402140e00030780103c050311095800303030400c14250790b0240c0c030071800604001410802541c0c1440761900c100c5c240d046200101d4601070000d11050307002d0280c09174500000403045034500c41c80d002c0364006650180701c002d08165600c0342c40c00b01d0300940b152a004120414100d011003140c0022280d0140000b04030f80c485034240000661036403c0754640c81e425105204e90846d04c803a80080c000c40c2c1254a07555039507128201018103003020a9004180d000b1030034a6424000c43d0758000c1034501c4009840403654490388008001610704130b02840364040d9000d0910716245956214124901c02d180d42c400030b01915940e890800101c0700002c0302c040072002c03103855080c010300e003580060076244a5a0009402c2c0308994000408940d014400d5255610030840100106e50308000024001d041a001550401e94001445500c4c0c0404040d0a81010341110000c3d0400051032095400786402400d030440d0000001b0522613203441e0340c0140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 608515737 1250 608514487 608514521
    0xc03060c110f101404050d0c0201090b0c0106080f1501030b100b0a1d010806030a23070f0302040507050a0912030512040f0b010b19050d2a090b090d02060d0b060d 71
    0x4130702d44111000c0501960f8000014540b803400705100303c5d40034007509012030412840c0700000501e80201405000c070080c11400028056140c84000c038544071080b4488401a0015440c80002c4540c0b441200e0460341c0080e40c0b25102c0c0d40c0d05890055001058001111a000214030000b0a40c0d000700704800307103052119103440030300c041300041d110081c046800741c3c3d241e40b10820380800a110081c6e40001010b20000205400a0349441c0c181041107580000ca800c5140c94010015845c25014154101225042151910703000200c001c20b440158006c0c24010f00300c03614200f040601c10801c95a2402990000d6071403405d103480d140d920740d85216401e940e0140c0100000ca815580070040b200c500f039090b80700c101010b80310002541d1715003041d42016003059940402d191181e200001d41001e101d69100c08903c58155200040e00c4000c49800c000d40e000c0040c481c960058441e20356080c051038048414a85071340194450002030f1000181c2c440c1c00034800302d40d43c000c00c030f01c070703082404054104010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 608516987 1250 608515737 608515751
    0x8071208150a0605090a05090c0705060c13051509040c0804110909030901120e0d09061205011809020f1504050a09090503040618030c0806010614070c03060c110f10 72
    0xaa00200018820850b0301c0111014204a0030740a1401403c4050018089601c15551000041c0c3c00740300484205141c110f00003030400820030144110759019181c40d44071420b05400e2484484040e03000c1c01070360f0069036407040790400d0b10aa07905840c11014000d00030300500c184480014107a842c1543c0c04ca6518607240060306062400300310719442031494078029418075882c00b0044891100684007220423070764400303082500315001d1040c0040303180c203515084081460104024260044403500c00281481c11005021040b100041d0442c081e691800200e80d245048c000074400900340016030341d01c004450318803021220828050030450f181280c41240c241c6e950100c50040d202c080c00003c1031078004010030300003503001f46407420000304d5915480280795101d5a41c1d50580364550000543d43d40310034010840b10394021001074400201c010f041e82807040903540c144006c05c0a020007017219440d00010202188030b501d03482801e4a6081c201e0740c03056a00c84070a0744854440c1c030894502410014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 608518237 1250 608516987 608517001
    0x140f0d12091a120f180123060102070609270c0c1202070e1b090904050c150403240e0114040c17060106050304080f0a020606131104140d08071208 64
    0xd031900140760f90500c4050382d03101c0342c0c64041d0400c0140816140304044180c1802440b0920403000030900205698a4000a005040440c0300004001c90304551141100303104103030b4081c200408a0b4600b00050845190f81041d643e02c0f07141d03041140c01280e151200040c6423590106505040602800c0c4020300000200003c0341c4072555402002c244030203c1e0702103a0507205903988009028180d450450030085207200081d001d80c0c0c190740546060703001c68010042880e000980800017039200c000302e8030341071841d030750080c080300310000c18448011000400414050580c10682a1010480081004955050420b2041901941c1c01c0c2c524040c1520007060035880c000044400c0c8411500401140e1300e44442103410380e000800c01c0300e40e60824008002600305460190003114917a401900306407400c070040c040208001a0680086401c05c851078240d041c91800f124251044001c00800000c02040461068107000704028a040e00000da2070050050307001c600560b842050391780e05040d4403008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 608519487 1250 608518237 608518289
    0x150f09060f021e2d06010501031b05030703060e0a0903120506060708070318090507030b0d2d02030714130b1f0e090f060102010b0a140f0d1209 63
    0x10051030250b4016a0005000f030040004218500000d03000c49000b0031410348202411252821030f882d011040c400220410401131011a000d404286003c021030303a13201c581c0d0755100c00d00b4490310701800800804501c419110703802500181c80c01c0c100c40d40190800400501c01480d0a020940014604205c0a0054050340c000d09002d2a0005e007402d05184490f100c0300403076448410102c0c148402c0f85c2c078403104880c2c401e072010018814078000241398644620b01a0941d18442c0c0d6240c0300d146075100c0840007444000c0d01480030038041507151041c03d030482c242800010b050b200070750f1510510700c000a52085200b80902d00517001e540b4465a01c41d00310040041c1ca0b42c1415161784100150303480341c0700b00e0a284010140994a2808203282110840403c800000c10794045008080c3c0b002000040e580902400004000580d100d0f1181d52504000d41180d9240c803200c50311408101c50103400e6640c400c948262600d40000340240c00c1c0109803005410007502d4840c404002c004008180510300440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 608520737 1250 608519487 608519507
    0xb04050421050d0626060f150d061107021002031303110609060c07050a1710023105100c11010f0221071e02030d030c0207150f0906 58
    0x700a542441c40c450355448240c410441150408000040c88070070740b44689806500300501c54050740204802403512101e89495500070030748842d61140c2c0c00d02c00138003075403c11f590b40030050701c5d54a0419020b020000f103413034102460240000c0e040c42c01010101010100411b051442115054213041171428166100c2c0600042c40e44d503000403e1007000484d0b81100b0381080e208004041d00d00d05881c040000c0d10a41100c0910442e81c0d000403030238001420002101006001030503111000030704110300711562421250a00e2504c03075001700e244601e50b0301d80340d9082010042c0e001880003604000d1558454003c1c903209992007001c03140c040c079040c180500b03150701c2c0d0386821500203411780080c9001521030500b109481411031140742515491048417407042007010340080325030307559003443c2d0038003101851000b0482c0c0554040f00910707100513a0006040c0e031003179659003408210742d40041d509a0034400954045545180650501f0300c065a021800d9403031094030740c5901050a45510080310080a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 608521987 1250 608520737 608520743
    0x1b08040209040605090a0f061d0601050a03060b06040504020c1b090403092d0f05090c090a030b190906050f090a030f112103060307060c0309090e101e0b040504 70
    0x400800c01040154200c10392114601045808006e12951040f0603000c9440c0183d92050b41c41030302000c803d0b8902100320a40c910702c0c0051465506100000d0007500301c0344801407500c0d0391401c480a5644541c0305550051100070011900ea0780110b05a82e05c421604d00010a0740340e21181d0b188462074214156405150140e4480040c5400c1c0028884808003008182c03481285d20b00c10b4100c4591000390001c0604500b241d000000c52804051100324000a0820750504c41c090000c00c2c0680c44100701c00c400c0b0394104100e5003042c2c0714402c40c01c40903500d244c601c802c0f4505000f054003d10040f6040140a551020001c0009944030300015440d25100b40b8024001030005034440031091041e00c50204029854084d40c0c8544010000040383d0020043d0750703030302640b01004000300b504c0c0c01d00070307103000f40001d04215111100741d54000300f4410310b6000e02c80460340e03100451500c2c240c0401030003d420301116001c0044400b4010103c081c5005075004101c1541002c480c109641004d01843c0d0281d54 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 608523237 1250 608521987 608521999
    0xa060f0903110f03010c020f0c0901082104091506140705060105151303060c090f15081b0d0b150a020c04020a030212070f0305070305131202070b0d1b080402 69
    0x708556a4103151005121035540c44000c401142246503020720a011400c1e0704ea40060110840389403540b0700304001c424400748140d881000402c00c400d00030400d482d040c00d4140d41102c200c034610716a0750036401a5080883c83c10718040094034410100083c10342a5011520b815121010032003c4698500c107440d401003441d00050300401282c00d00c1001c5082003203d040c0c4040c100300022400c8043c403003c82c2e0041c0d5446882c1c10a50206076001410003002d0488155150003150521400014412382d0702c8680003048034080000e1007240c50310740c81400c900c2196901c00e982c1c0c0107202090b405080071030712880c480c110f00200001002c030070604072042103400d034011b030907171300c0d0b0120400c0000e411018024003070540800045403d07024840f0001d10940850b11030300754402c2e20b03400c01001c540004164106040c546814440c0d41a1000443c01c1c0ea035601c200308200b036078a40001242007551542c80005034590118200f11095040c1c0c00c008200c1e400300407080441040c040040320000c50940700030350464 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 608524487 1250 608523237 608523239
    0x2712120219030e041e0e030d0b04050919051603030f0f050405280f080a0302250b0307031103010609060e030a1707050a0206310b2b1503020a060f09 65
    0x1080c1a00000821031185c0c4140101e00182c0195030180d4400301070360703811500005084420b503030243c881c565404e10283d0b03041201d8904000416681e03640703c0140c2e0702c60702248040104103c802c00c207100c8003121070750030182142ea0780c0c90041c040c01400481c40001c00c084002c0c030b0440303911a8042c1c034101c440050900501150314013001e0a401805405018040e0070700d500418500b6148000200a100650081054000d035007070085c1425071041d5035084480d00000500c2004107400c0300341c0c0c140c40484075500c0d0b6a0b02e5440c4184c2c02010b5280f8240c03050b000120001824a4200c1c80041c100d621607100d10000c1c58004d010541c50f040e2009000b000a1440000c4808410015000d000d00d1440744084912102440d000030f04a0380014010140100c02a00e0500240b00440c0460182e05007801d000c0c45110309109040c95540034000c1c0005000c6801b0480080100c4401110b400396035030504100700101001c1c0c1083c000010a0100342c0c040c82c018000021618402d5042c0030789400e030380c2c2d80d04401c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 608525737 1250 608524487 608524489
    0x2030a03150902040f031a01030f12030f050a060609051816210b1807080703020a020a020d0f060c0f080601030f06091406030601152712120219030e 65
    0x14008800c004140041d4054042084800c80c80104040c0040316800c3c0c4007545186000041e200209000180c90600d030f00040000484445130b8000d1a40c1c0001c4150b03007074034180c40490040a03030000d511051810032050040c511115804181940d19594810306000c2d100c900b401203880752400550322040304600002c1111401c101684000340f101d1806030003013000c01e100039486105c0f0005c0c7d80c20140d80c42e100100a807400c1015a4289070740d02400304404d1400c4200075046240080010381419000101040813900c04e01601810540c02066107100074000d0900e1142c054102404030380c01403402e04161001406503000a80d01c4650381c0d1074001554a10004401811500035505403d68507181c000c6000081030060000da40f481c4186080645050750030940b410506a02200c0fa00d235100b111114078583c400900b1503002004c84080c240081c07a910110b802d008103910040c113031541c8100b0340040050120891442c80315076030844031401d02c580920444250725607002804150710880d54622 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 608526987 1250 608525737 608525741
    0x1a09060d020604230a0806040f02060c0d050c0d02150103290c0706060509060303041202150a0c05060a06120f111e04050c0a090b070f06020f070203190302030a03 71
    0x1025402030440040316146602103061a0032541020386026030020401802c0f070900d04124210740e0080f00d021242500c3e060794a915010050f00c051b0050101e414103000f5916000c0440c1e1040d008a03003100c52514102c1001803c641000300c0f1000140a040380160703400340f002402d032140e0990b11111a0b07050740781d50380382000502c00300400c200156600546000400c42c84000700c2c80b90074118a2a9035400070f51030014112030107138200e1842104000c061025985000040d10156044842c094400d0030b0107000003026204481c0804c3e5420700300045040c0b5880d48200d01c0c142852154080350b40c03a0311881e1401054400301e000718030128031209954008070f82e42588503042140141030f0b4410240030b480104100002644d51075142c25803403843d00703242d410513101d40c80d84048203581d884d0804113030b020300030181826031013440c8081c6000300380071003801001c410881295910000c115034135480c440080c40c0700e406c0003c00764401e009100350805107075000c0400c1d104450b8103902540c079040c22413800b900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 608528237 1250 608526987 608526991
    0x1606091e05060a0813051c0e010c0305030601030e010b09010b1201090605060706090311070b13140f01050c100f090c080d0e1905030601091a0613060305070509091003060b03011a09 79
    0x600001c40070142000c141b00f8007184542404a00300c82006840b610b102404241d0a00c100c7c0b410044200c40d03010221f68400140c80d044a02441c003c00d1b410009482c4a02500c0341c0c00c002c990080507200001b070041c1c2818009c00701448000d8080e0030076039803030751a20b040302d14610503150050420408000043d49943c0115840f43c1b290800305c400e1b000c2e56088a2815107030341c00c00c5001c2c0c0f00c001080b4090054640405004011f5170840e228148020008911503443c09010030b418041c01058048001340c0910480e0307603405510504100710091207840c140944503803035090780d00390704130100030808a8000c26078000b8000c5586070725190040c01024040c000240054800301c2030b825032000310301549e081c0a41750080c1034000e004146041082003015000800b0f5030350900c121810003408943d1403510400600311a690300f40042d00360b40e040d40903102485845125a4410780340305c20084502c0c1260740d5081543d02900d4200501da486109141c2218150410541c280180b007609001519040103056 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 608529487 1250 608528237 608528251
    0xe1206070f0909020d0b011b0c030809061903051e13021e030703050a0203190b1b0405042a0206100905060d05010c021b030a0201120b031606091e05060a08 68
    0x2414640c0c030f0255900300e0300300c1d0304012841602c500c0120110340c1d10680c50f01c102030584000c0107601985135140002480d00d4480280014004034281c0c2941e900c03d41900c86017a9080425803017450100801002000111040650003c451044000f0398a440d03942c6841281170403038500401d40c040e002c210307041c4003d0300300c000070b01e4000ca0008041d40f014400207000f1803040c40148440c141e140b040500b41402000c081100951016925011400000e041c1e6040300034183c04900200814a0f140041c0c42550800c81d0460304250300d40c40c1100b00f0404a1100d0031a425103281442c4a011089860750b20996a51034a407403000c6003480083c0250744401d4000d50000d140f4030b0b944240b6170300e090035100307045e03e1000507030881c8040c1080f00d20440c038503550301a021000f4041e1b1031100c0d400030b80640c070381003012405180d46090340d025a450030090049204580c80740d4686103651128002d180c610980030b01480404031016080c8101700841082082d00c0f40141000d051034803480e400c80300785400801300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 608530737 1250 608529487 608529497
    0x6090708060c220503030a0504050f15090904030903051c030c140d020901020106030512071403030c070f05010b1207410d0c0b09010905030606013e010c0e1206070f 72
    0x4c69a80410040c0004146a11803640b03452520003006001d8501492450051201004100d01c010a080440700303425011070b00c03a00305484a00341240c1c00030203030f08020a81d01c01d45400848490221107022002001c80c1c5d0309124011a4403c00c1302c6c0c40c080741c210340790458401c1c000c900130001903401903c02c900d8184000250265030b5142d1915050500440f0241000002421018024030005115901c000320004500d903080800d95240640700d905030240221044c51604020001c3c2900020720101008180e18440b4080078049a01c948040c4248241c000040003103c407283d07843c0718400c41111101040702001560201c4140000181506182e0702c0640d10000c1c100054001c0c4480c0042c0c44401480c644544000001400d540f00540020b4400e134000400c001c8982c0e407040407107202408440c00c0c00c1e031010020501c158884244885804e82c44c1e104148400c0a0030154020b1a08400d40d5881030030b24081c0c8000e014140c2c00140f900303001a0400b400142e003aa000390891045009240b400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 608531987 1250 608530737 608530739
    0x2071a0a11030c0301080c01090b18131a030c01021506060307031d030d050714070f05012009030105010b040f140a0f080105090124120807020307060206090708060c22 73
    0x540107032944110f400442d0f041010005120b00c420030886114003803000e09107000c0c0c00b41490700420907801240e220404050b4441d000082d0354440b10100c2c0c40c01941c0c0ca000744504d503581d01c4019499051014000e00910810521405541c4005501941c1c00405560b103040c03a11420140312982c0d100400900130306484905c0c00e43c41c014030002d01e00d021141c0001664a07030300780c0000e1001f038980250203042000b14030744c2002d080701100ea048510540d07101c00c148a445049192003400340154100ca40c94041168031041c00d0102420020089144110f000308510782e01ca05000300075000c0c41c058102c10301c0618605100030f0b50200956544084001c08100d0250b1341e6079420b4041e41120703000418140d44030814403203510700074010480f1001000c0e103101c5d004444a0102c46044101d81320300d1341c2c03800c00801c0c060180600c3c1070448003110740203000c0d0ad0302d0903100c640280d9141c0c001d840e8908180300e9040000760420012401e1030040340c03521082454003a4242c8200c81c400100d41100020001e0248 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 608533237 1250 608531987 608532011
    0x925031a10021e010203070f050c1216050f010606050a05031f090905010510061b0f0605040507061d1309240c090f0807091d010e071401020102071a0a 66
    0x1515070080401c680c010594611200000080c2036031a402c10910340e8014002e0102540c1c0241c2c54041000c2d252400c10744a10590004503d00318070442c041e20360180003c0c00800001c4a0404450240d00079400c07590b510b00700c0d0304424202c6096209040010b5414011921380b98425001160080403031741701d82c4240318040c2002150b035160340c0e000c145819569500030341000020301600303600031210a044070046241c01070180c840702c80c400790b0031129007142e43d03182c08105446c0903004145400800030007003840c0c170346040c1c0d545101c1230203404040ba5440e0301d01c1c540b4880100181180c181c1c080c00051840d02c88501e0007018040d0500f00301c683c40244080c1800400016050040140c0441c1c004100c03619a104c01034900059070b0419160000c240300e0034442d215002504400325071503203d00040c0c48520116264021811030116250755003002034003404080c0002c0c0306000d66240a18807100800c00b100164200d101d2540b005190554880854003038481010700130307600c20201003001c00e80d200100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 608534487 1250 608533237 608533249
    0x30b01081504091511070c14030706200703050a050c0d080f0a0903061e065d0308150315040201020c060c071703120a1e020a0302090925031a 62
    0x64030343c05050b00702140b2030b41405a803052600c000d140110030960b0507050300c004a41c1307a8050f0b015000611003448000c40cc86c8207107010680514260070300740c0b80550b40b05e1034101c1d1181c481c01c0d010f480c1403194100b102090b10341350703039010000d50780304261f42c2c074014594032440c0c403607000120640c003406081c0c40000040780e0240904441240c00341d00c03d101e58800740640700100c580541142c1141c03070740e03100066540200c0c8030020800c14401800800401242c1e0424031051a10f0a80d49050300202442c1d89013001003004542e02d164400e49038101540e98011508600f0740c2c2d2008400c1e4164401c2102d00c3c49400d8005546420038011b1042d41c0c0924581404203031690301008081c2c0d000c1c0c0c020f2100b00100707424141c0d0141c4000e128030103185842140c1d48040a094409860820159564001740d844501408917907912485201010342d207c00301c43c0800742c003e40100000c10b010303140b403e0018084a050005c034006200c01d00008000b4001807100c1100144808421240f141c0d0845096110b1540c900d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 608535737 1250 608534487 608534501
    0x30d05070302031906060e09060d14060411100c15091b082a09090307020306041a060111030a030b130207060204080d05090d030e1f050a030b010815040915 68
    0x1074401503500c2c18040e000d08008150b42a040714058039148042c08007640c07203145441c02c000111081c407120b03107410001454030340c102c1c00020b0070308400e00c0241120100214010780704501880034040c0c41900e460500c04240c600c01c506200142c11902503800043c0c20622000f4554040d4800048404643e0f03645074181c0700c103503401443c032100080100141202005030841c803401000c0d242242c440115540710f00c0b2129444194403a42c840c000041903141d04109031052182c00a045a42c070741400d04182d04d02d0324078080c95224010024002a0035940079840030102c0d50346103c0111726095030120220010a103000c0040c1d0301a08075840d8072250b413994006480058094040146c0ea03074a4080300b9072030f11a140c9129814404180f08290645c0d0398107030990b01c90354040c204404004042c4000840d4203104d61034228112112417400c0c4051603003c4080d1403a56880c1c3c408012020130301c0019101404221162065020503120220503800c25401c214496441282801c56060308061410103803080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 608536987 1250 608535737 608535751
    0x304110904150b03011112040305190806090c1e03130807060213170c090a0e0d02010c021e07090b010e120312010504090201050d0504110d03020c04051b0301030f0203030d05 76
    0x490001d0100b140c2d814803458001010480007000140c45a81c4506401d024108403444804d4110b000102814003600450f4900d0050f200000200100c0b0800504400810340b40c450049090000007101201c00c41c0c00c5840c524240c00c252806c90022030310500032a03000801e1820b810301032049c000c0001e44003801803d625840344002603114031010000c0d241d2044540e014404401d41c5440035400c0780740101e40404030107402d0314070001c15903800b04580007416101c1600ea503240b20b0303101c1089840f41e065006480fa22501d9007500e81d40e4500180c50504005c0c0f0920217490703604400c508001d4158113600c0b100135030700d040c10800c28550322213001500c0e03903208041590041d0000150040c000c5038240a590240034102d03810002142c403a00000d00b6406040b102c0c203205542c820214040c80103403400304c4984080100181110701541c64025158009805414021420000466000f080c695500e02d0140000f01c43c0d00e045030303c2e60b21a01c0191300341150503030f01030104008100c0030385094082c0f10300c1400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 608538237 1250 608536987 608537003
    0x14010e07032001030507050d0f02070819030f231009020310080709090b04120e0901151b0f080a141204050f010b030303011a09060c0a030f020c060304080304110904 72
    0x400e0051106400b0302809040b03040519080c100030366550440c05540d030005840c0d00010f4030286045882d0300034402e2000140c40c010010801000c2461030300307092803040340301e075401f0310404200800c1c4405a816002648107902c4142480c0041d4030000e90040380d00c140d00742203020105e41e442e00300070200d1344191090741c040d041e800c4042c481c1c142c040020000401444070200018030080c1c5503520001c8001e0002042c010780c00d080d0003030842c070500c1c004070ba07010700a041d10580e503540c8120300e0074982c80f00400fa002c1024582032800c4010164044000140c201d46000850741c515556a6540d41c00041d454040c04004c118140708245940060501d0070fa040030748251904250074103171710b08000840d00d0300321a07040c452401843e45001c4283c0f0f0450340010650420311800c40a518a80d000b610388081d040000410328204402002a0440005010791941c804e54408500701302d0710b070000c0d10507080e01700e0004c1005c90005160440119445801043c040894207052800196606000c4c1c41c1918601 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 608539487 1250 608538237 608538263
    0x9050618010f05030423031b01060815040f0303020903101a093301020a0503070507030308060a0e0106050714010c020f01150810090c03050a03121107080714010e0703 73
    0x2580203000791662500038180581103285c1681c441c06a6200b4441e00b20340d0707428110003406212010815610201c002484001e041203e2002c682d000b000b01c0d00c6070801a10549055224030b40381c0c485580c2c05560400c0c060000740b001a1400d40107540502c0201d5014421101042e0041c03010b840b6100c218070540b40040034507105c0c1c40c100103e0640142c80320000d141e40c030f01c04010406000e80702d0b032601413a142690000846190050741800c50b59100032b481c5000000c0c00d20104600801d40e503090b81d200b91948100e98a80c0b07014000c181c0d0303490140c56203c503d64001230004038081c1001d4054580f1441d6460075000b080c01c0c01d07500792040c8038900740140e07000c510184103120082c050085960b002c1d0007410340072071070004d0941d03450a0540b48034003010307501c4214409100542039684e0245400c08200c0384a403500d460000c12400f100d040c034001523440c24003000c14005801c81168462500600142c1c2082c4080c0c817044c0a140d02d06030100301940d81c1d004170500504090000c04011409612060101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 608540737 1250 608539487 608539489
    0x40c05210a05010e060906040e0309030d020c0a09020c0304091109120a11040b22150e041b0506041707150e120606090c0a12060b090f0f091609050618 66
    0x240b00181c00080003030078510304000b09500c566000700d80c403c00c12500484e40000060740c903400c500c120418980c146c003954201008450300002c020410000070b03943d03003800907030320005407040740a480103540d500d8004100030405d02050360071484a41c6200304569262501103000111042d50030000c01217150000101c2500b4400078449000704c1c01c900b5901805010100400194035105940560301d2000c07800701130714000303910783c1d000c00342d10f24040f07061013401c90302d40e0410507002000f19000c0303030310700c1440411100c0f000a08961104075000501410b00301401c01881c9481d64094803a442d005100e20b8070001104c400e84c485c3c58030141c40c203865102c64540c3c0038082c0080500d8405403842c0719802401030003460f4480e14690360780000b0782d51403261910000801114440c1d0310101e000041c5050a9000c241d04002c44002c01c5a140201e0710806c0c0403c696081c0104c0d03410507428a94412101d20000e800410010703074089162038a440c0c05416183c4520005045400004080c65180b505030781c01962 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 608541987 1250 608540737 608540741
    0xa0306050103050a092310050103230a030228020306070914090603060126120318010b0d15020d051e0c030103240b09160318050c040c05210a 62
    0x12001c0202d06200588503074a03800104060440301c1d000c0004589030046d0f9a81d0300b403200c503a035084801d03814807441d40e41e420700c91340c0e060b803147d1010840d0405003100040100000341880e036480e41600a40213040912007030400442400300e040201000000c07603400166414480d1500c115400c0d1100b004850604501c504005003821105004084034020b0207115940010098111000120440d80a04190040b2508071440c085100039070700c5464803251001e020705d000b8502c100e040c281d0a20074090f00c41829070980d20700c4d01c0b00c0354120103030300003101c00300d00c43c0d042c24041c0d1004060091300d0703c2c078641201c2080f500100c1c0c0821103240d00440000c01c1e081c0559000c1c0c1c1044a180010342076504688070940c1036416451080140b0125030f207030000065154001a010100c003c1081e84540303451000c4144040312203d90400082c42d0113070721540090b10401102005400100401840d02210180300c014070446000c0402e01c10107124142902d20742c42010b556540e91841e0a2b140b03400e01c0c14000f42 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 608543237 1250 608541987 608541991
    0xd14032d0403030c020603101508010806060603041e020141030108030f0913020f0912120406050c0f01020a050a0e011d06131724010501081b0f0a030605010305 70
    0x30040340421041000c039a00030400c405081d011104242e982e01c038500080c6600c00154060301c00c2c11000c0c03d842d6886c9400c07000c1141265000030544296035500c10402540380300032100101004c4010320701c0860030030348a215510041c41810401c81111600c9440d1044040000641040d4442581040c03014400100e2484444100320340f042c6c195410302c00441d07281d008406c18000710706004907203025640c3d10078400c3c19920701c3d034407001c55590b003010021003801e07444034042600030608a921020805030010b102104100c03510b8000e03081500300201107405601440c0c061040f4030400c44011b190345028802010800036030384403a079503000321010141c2404907a020450602000a05240310404080000025400100c2d1151360780c007095070001141c03030f80139000b4541c000009062002c2d92000098a44181c105400100100707038041c500c4040250424000c841c000f92400000c1f45450b81c020151269820084242e00c3c101602c074031441704140c101071449030000c0e0b2500340070801560188102a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 608544487 1250 608543237 608543317
    0x2060c240c120a0b1909050906010503100c02010207050d0f1202031923010f05030118050c060a0c0b070c0303060602010b0f012303100f150e0d1403 65
    0x12055140c008490402030007040124481c900c0740d01c0000f11140c1c21580864458500102410f20481010203070110300c5038180154041c141c90032022400ca880c0000381181200c1000300103060740054501e107180a808240104803c2d0364081c868078000417424000e4600003611692071b0400c081f20040c00a01d0000301000a040103441001070181500561200381001d00d0f8404001c9400300038080144100d140120090713145030401000407a420545040304003c03140205c0003840076607902c1c040c080c01d42e11020720041035030b070005110305002c2c00c0800c003030300d07204440f400d00340d2a50354292140800b45204643c5d400024030301c030358040e0800d41c15200c0c01c0050051780c4003c0100801510101d110b5031030540c5840e062040018070070f07540c0380300c481600701d000d103411403044d1300c90800407101c24503c030450264200300007105c0c00110f80d614401c0403580a00c4029603a10340b0340403c260a0100031303a80302806a0300030014000c005202c10040008190300c00c5900f20725803403004c00000110002500c40151 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 608545737 1250 608544487 608544553
    0x3060302060f2107020a0b060a0b0309010e0715020c0d11030a0501020705011d030913060f06030f0e06040c090507021203160201150b1e090301060e040b0f060a14010c02060c 76
    0x40701c09035038002002c0070b0442c0e1018440a2507180d403030000700d007091952b100c50052000002040302410040d0059402040344200310780c10039031110102403102c03845405a2005a00040405250340380a0002d51a001e004d03000645020001d0b1021a0030324001d50701c00c0d1800ea40000c0d240c41001400d00c90684070b003000320b856400c11056440a40d85904c00c6180c075520420303c00314858541201c1e83d006100504150000c41e80e07203580d42002502511440140349503180c503000014004110101d512482960b1080300030090030704243e510f100420b0054140002c62150039203d80722520103200440c01748861218440302c180100034000d00751010001441840020942c040007440450001e03a0400024400500c04420300001034211500036400c44680c19804c0840005100117941026400756005140045680d540c0c038041003140c80c0e0640d4451703080349c84800d040089116000007000b40c1481403400c0310f21403c0c142c0018019070807012400e2001e4001007000b100d170030403030201203561019011032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 608546987 1250 608545737 608545741
    0x801061d1305450c010f050c0a0503070606080c010f0806010327030906020d03020405060405120114090c0109093c061d0a1406040b0103060302060f21 66
    0x100c0d1604811261540c0340c1500c580c04103400036100d40300e114400403612041032a07100e6031403142c510b900300c00b0300f04040b45041c0e0140c030401c000301280c0403600f840103031a60070680d5242d0701d08440039406280c0d000c2090240101c1d08000810600c002c1c9022409102d01040160034440383d90300b070864405115050088144070441c0c0c040e00005c41c980c1c02803090800043d1158a101007416004002200140180050101c5000c00d50007500a02c1a00c0c0346608407a444912106c05500724896400f800340e0140d024801085a454403401c00340741c4aa110307002250040c3e0007451071281d044243d5000d40d050700100400301095a015840c8401064140018020443e20700e0f40c00541860300c03030391506174101c04440b824007039888543d240c210403c03886007040071641c2c464888444903c001420792625030581c01041c5284c1280c000c40503244054540711607141c403641c08000040998010082c10702da20307420004050781e180005032070480c2440c01029070b41c1c0c2030202d281421010724400203e1094407003007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 608548237 1250 608546987 608546989
    0x109060e010c060b04020c03030906040c08060103110409140313090b0a0506040b0d020c030c0a020102060105011137030915050c07060c030309081803070b040602030d0506130504030801061d 83
    0x18050b55054004200155100351500443c010303101c1c0c0c00461089100010078008002e000007407d511550046031070b2910552100308017a1074050a1001501140c001d94030810740c0e19241d80320b03c2c6568030440714160b140520035042410750300700801e1818550140700c0204410710050007101c0d9451070403510903406c80d0518002884501039802681090440887d095058480680c11920907040117012603841c1c40c203121850359241208813040f4014026000006a594043c408a4421004010181c080c46c02003a2040c1f50300724905000d075511030850250341c00f002d100c1110303400030203001e552140422400c1101c82d4080103c1c220f0b0300410020704000c600c1d24490046007810640c0c210340b600c11010005414220054580c110000c3d00304500081d4183d40c5d09103000e2a2107810000303805541d07000d9507984408801d40960b100c2e0601507081081241e44541c02d950007258003280080c0b41110000740391181504540f400c85084020608641c0180041c41d040304001740d1248040140c1c0000c209200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 608549487 1250 608548237 608548247
    0xe0606041214010203040b16030902090402010302090d150c08010b160201051804061706060114090f1908010507021b010e220c08011401030e1e070308030c090109060e01 74
    0x8855140107807194070028041100b000380458203284100000d6442c0c1c00c0c10f08100240c4507041c1c4c0c1e880703000c440060b007503a401070003402901c424580003408800d403644c035900154080d502c8000040e60280c1e03541802d9000601404440c1848511668000b074041040c080140c05010706800840d20840c00f030013040d148021081d008c0d1505a82031a21949821030f02d810a1405c03031840e40507991080c1050400b0a5515000001d0001c80c1c81000854140c1e07241c00c401558450041d1040c011102c030100700a10490600b11007961841001a204690140c2702400c48070b61006282c201d01c445035110310910104590420075804d140400e4010800501000720019002190502200b802026201c089640b9100100c80c141142c100b103101c00d1100302c046070001090240300340580343d410700c1c0d040400700055100c4c6c4200501d0300c0d00b081c02000d2207900070718244240ba03001d100c400714034070980c5400720005070400051801200c1c44c01c5201c2d11446a0000902480368a821a0f41004800c20560229030703030127 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 608550737 1250 608549487 608549489
    0x708150d02100c0305191d0f090a05060d05120d05011a04180603080c101d03070204020c0a1a07020606042c100c050306040e03040305033c0307090e060604 68
    0x40c00e03c00360041c41c13442c0a8030107003d80341c400302d0004c07507800301d00e44220780081c0d802c4019421584013080c014143d6080042e080d401c2c0d007aa54200068000013402c55106074000ca0700a44020594600000c0c2991003600d07216811404886031080807860041c9241e40740a020b01504003c04040d070006e00c2040c01d041c140c004c40c810032030880e02180d10b03a0710806095100901458100000d160340e6100284c100d6500d019002e52000a0740ca452010f46e0080c820541102c01045444d000d1880e1058580804c406900040d54071001c50041d9009580003c040102d0b403525200807201c0183e0340e140c1400041e0030108010f25090166061081346400200d400550b008082164490050155503d4650515007081c0203401c82c1e1683c90550711502c05034000024500c5000203d605120720551589083d1316401a4400101030b40d005004441c6080107100d000b80240c0c02d403048540380c0110390113500020342e0383e1403d0709072030900000c20700616030780c0104142cbc0500140136070800241401004110030f4816 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 608551987 1250 608550737 608550769
    0x206040303050a060b040e070f08060f010c0c0b0412030e091618090c030e01150b07020607150609020928062615011e0503040605060f090708150d02 65
    0x186000142082d40190f04c04406420b8a10321030340c403243c65003080240c0310001d1f51020702081d160345081440c01c1c07040348124481c810241c01c07071001d00e440c480155010700c0303501411200443c50a0300440c40b01680b0300504014142000c00050035016424082c1203814821802402003c00c01c0421008042c24100c0b20101c00c0c4504c0c0c8280164104102512150707041d401a01240b410120468500b6038990410740d60341c4010002040307098540240118001c1ca00c0c07060300e04001c010300841c000351601c940941506d40c024441030711420551aa200e089410300e4001d054415800711704500c041c141904c035024401401a0905e4100c250003840c141c000b0342c0c0344620b0081003006500c8155000c2d002c440c40c200072640c00f00e00d28040c102400f01565116410940c140020000a60340c542c5040040102d03090210f00d4481918588481d00c0e280042d010003002c0540081111251002c1030f1900d4a0051080c600c1355100c0c00740e401d05502c80c442c40e603040003a031486482400700c080c000d81e83e01e01003801c00c41c907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 608553237 1250 608551987 608551991
    0x209090c0f0714061608060a15021608030301031727060c100c08100f051323070e0301020a1205060a0f080a120f1b051c1206090207030206040303 64
    0x5014001e2503001e01c10003400414400008503030200450307001038200e010b074226495402e40780036a40b07401c55000504552995012a4504013000b1030006880c074514001079910513540420100480103618041d80c2d0f000d600140e00000040007840041a0300000405603c03000c07a26119a60202d05a14140c545070300d413000c580f0050b040040d075162004c5400911241c0242c6204940d00e00e40440241001990703000810807071000a81e0130b212001411050b07640d241460003199041c1014005040c07191040c200e070881d91000400070b06400b0f6100581e0152204e08010483e1400340c600800c0c000c0c00303680c0329000707138010305c000e004c0315400072444400b40300404000501f80ea90310780000c0804166520001c40308555180100d504000444d1100030301e8062260542d0f4400400d00480d10400d807000c0e1034001402c199100142c16261013082c00c42180264125240001e05244075110b03000d40c0000b40c0041401e80011303981c0041c49000e42002405004811400c09040c1c1d200651540002403004041507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 608554487 1250 608553237 608553247
    0x9011109010c020f012a050c0f01020a0b060a0e01080d03060503033402060703120b0d030905060c10060f0f080102030412050c030c07090b12010905101505040903210209090c 76
    0x2c0d100b81ba800801e19060500d5078075042c1c40104000c40d40c103000340207071180d004045004221781800003483c502da21041e4000c01000282e9214a003854002801099000101840014a50b17050001580c040c01405024104841181c00058100d400c0f550180f8000e410600000c0c1d40c80207101c1704880c40700c4660400700074801580f0301c4501e0540c000c0c0402540200086a00010700d58000c03250340d00d048025104001000c21202004446c5c0c40d041c0300180020381040080c000c90070600080c0003092910b1040700c2d80c40a40714003103000d940d500d1b0030002500700414010032004040315110380080c950350b402140795007404d450b140c40031906e5490030420b11030b000812410740c1c3c4080040756031021541040c0d4107400c0c0c4a80d5a00060315030b0800c031920540240c4010741e031010040c403a4100b050741c414000c1000d88060328440c0064150000b030006c1c90800010700080d2504c1d207000703102043d07110765114480c40003104241c0490b40136802d103501500d803050101034000d8a070860016040940344600c96210 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 608555737 1250 608554487 608554489
    0x3b0304030f121b030509120c03060c13213302070302010b040509010506101106060105090d060606050d060b0a0c02011d180702151003020409021c14010b0102030a02031207020703140609011109010c020f 88
    0x1042d02d0381c400c0341d1080794a207555000481d80b8001c0d0319218800c11130241300c4008800ee456440791101c1c820b0aa91400c0c907030402070a030645e8010404c0e144240008500610b02100013400c59000700c0b84240143d468074100311a500d03250700c81c4154000c3c6803c200f0b450003108403c42d03a460b5401000241846800205d503c029541e07908038020107507100000380011500c0b0100104990001560a1401c5080c24004180010580d041da12507000c1c43c1c0e1450b2032803089800440e4241c10700488495a44800d001c00001612038425040031112030060302203d40c01c0c01400280350900503602d52107403034103038400e005112510414100489404840c042900a072038000540d000141c0d00156000c00b0750b01d9040c40800144826488004600000800280e405200107a07140e2003521040310042c2c004004034501584032001250302b03d403062044508030b0380c0f0b0340d40381c50b562411004100d84a91141c0200b00c0c50030030034064950018483c00c9030310704019866001070b0040e9050000280b1074820f80d0007200e01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 608556987 1250 608555737 608555767
    0x3030403020919060f080303070827010e1c0f05070c0e01090b030705010306290c010504081312030c0b04063b0304030f121b030509120c03060c 63
    0x59034004050b480c0c1420100c0075900c24150792484401c4540c00d0601c00200420700000c0f140c1140d01d68070142d840d560b50190215520320b4002c0426181c01000c130034044035507100750401e0320860003010001030009880502c06c0c1c500080304428010540c42c52490348810b0b9440311141d00301d007129040a40e10b40300a450903200e500a1a0866040e210010000141104003500b2400d601e000980640c0d07401500c40c801102550307402d00076a442d003a80200c41c201d4a50504036101d0040c2800c0203000d0800038031800c0720b070948030280d509450700394001c01d0000c2e0350344800951500070480c2480042c01703c00950381c041c0c9a94142200034101104044c00502800110b402400442042c40b1643d411100310100040c004050000c4180c81c0e98041501c1c5540c050001084506680d04298203003581105a0345031222220744060150412014078035030016a41d50003000c408061081d03c4860701d4150030020f01c0443e440c0300c003642c04550310424107105103407004200107070001c11151106544405940c080d00e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 608558237 1250 608556987 608556989
    0xe0912031e070801030312050c030c07030c021f0813050a02010509190609090e0f0703060b0105070501020f03040b0a2a0e0604090501030b07050316050a1710090f09080d0902030304 79
    0x4000794400c01c19200e901141c014140c82c4281c9800c6880da400c8203800d022200112a1380740c02280800120b0b14610815010304002c51180c5040390980700641c0c049601804040c410314010030000c5101103925400c100c0c20790b4070404c00306d040710a0101948590360741d082840c1300a41803000000d400012901c0340883c1180b030718000300c000304146039500b00090402980388107500301640f806807007025114012a202c0e03000100d6000600109065455200083c401c012825060000800100c400500d080c00500081d0110410f0152a40303020b043c0340b140200010110589103182828000c8400d060840703c0540c82001c1c03485200ca0030810a09480c810003802d1101d6000c400400d0000340d007039442e0489816644120504149626521001c0e542808151950040c5440503e03400b014039100b8005800c130341c3c4440c90484101507140c0018050300c00b0946019420000d40d25003841800c496002e62542e91840c44000c1007070b40d81e1a11001894000c1c07046080307c0580b101d09010643d82c080040d64 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 608559487 1250 608558237 608558281
    0xd0204140105010f030c170a02040e07110118080a110708031206040b01020607050a0c03050f0301062601140f030708060c03100803040b0703030b010306030510150e091203 75
    0x109040000c80165040800d125040c0040c0c00c00c2080d0018502c20b000340c12409074991111080c4407041101801c0c110b41c02030020240c1a428840041e003614240585401000561903000c0c580d90f50441050a48001c4140364008400d10401c0304000b03424001119255101450980303400c0790001012414000b950380092158840441c0410600d40407544807806244100c4041140b100319900580e29024125091070101d036050041401e22400703284c0300000244280350040c070f0310708407108002e01c0340c1080e04440002198041c1110000b040c0b11034040e904c806002c0074102070f600d01052420b02c0182288058060080b10013204541d440401c8418064041141034840b1480c0a80443ea100e810860f03200790a10007950f0005210003000c811541030300c0c400c4200e03900d070009507141900035090310b1510504056940c080000400e40a00880072010300040010400861882086444d20303440e0700700020417000d00c000e2040f455800107843c60110301d0307500c0d580d40302c0c0c3e280703a511154240444100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 608560737 1250 608559487 608559491
    0x115031a21060106121503110114090a03030c02100e0a180e06010605130e010b0a030b21010f150815100f0902041706040f110f03030d0c110d120203060d0204 69
    0x100310140c10070344c05e02c803c4140010400002c490600c3e04001558648000b03030192112201c1c80c4c0155208800300c14100303801e03070003c0d40340c84222400300741500070540c030a50011b40c1c010034940451400c1c000306c44101e943c40c5001c0040c003004000040c0c00307011501c220241d0680c000c9042c2c410b005107070000d65900400f507065030080d40e50380c00040d04540c002000c21503620304e11131011418400c0123a80b079040e00c0d001e44c02c4500b8100b0741803003076000b0061001200d900c9035903511441445e8130112104480748040c4400401e10010a803189401d80d20b07040c0400160104102040c042611f00140421403e104007134500420307190081c0224801d000c03070b044035034129101c2c000494a50410b4004000700c407805484001042001c1030f015032120002d940081c0b40004044c0c6a501282070310150090f01c10700205243c5c031030700c40400002c0c50355100345c504030000780c0c41c1d06041c1803d81c1c0100c40721140441c40c80c06410a0501c9000041c2400c0c001400c1d0120703140e021001c581e2544681c403200481c158045c000b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 608561987 1250 608560737 608560739
    0x4060c0305041a1f080d090e0f0c0325170a0902280b070807110406060e1504080f0a1703040c0b1e0d0b0301050a02130b031902120115031a210601 64
    0x2406072259000a0b6042c00b00d4081f04000034251104404140b080c44030420121054540c1c0c1a920426030002d032408005014046c0d03200028184c3c0c03c10301071030b956140c40340e0407040d030050745c446c110f02e034000d000a54052414212401581301c009241e21701c00f402040788002e812050200490801c900d4100b210004030100b044000c12164030001c2034994050b00e101000b4000b02410001641c60500401000803a80c0d0507440141c1003050146200c0359094010178141511840c2880c501100d04c600c042e50395014488060034001c808100842c20a2175480452951500b42c840100d51060361041c0080640001024946008800c050395031441820b00c05507515207441c0503e074060300c60000d10912a51030f000108034080c00b80c1c800c0f201c0381103800d003d5500061910030704d100355030030040055980c1d00280000d012030a41034401804c2110701700c000004503506061104142ca005d051411051500c0c1c21006407000720702d101500d0061034100e801e10319040d00891200c0000a40300100d5410f8031039500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 608563237 1250 608561987 608561999
    0x9130b040311120414040f060915090e011406280608090606120d0f0e330a0206060d0f150e1614040b0a08030c0604060c0305041a1f 58
    0x200e502c0d403046400c03100d810840c041d0030000d9224034420f40c0e404c03c3c46640304800a00341a00b01c1c800e40404424005000e95a5007054801d44000c0c031380c4c4a154503401c80090001d00000d00c1408840085440200440b10910002c0e8410000183c9910300c2180d00240d05030f0084c00341c0e0b494a403901550054144055910800905090801e58070238507076001d0342d800100ba0b401e00c1e030145103446040310000e10119402c2241034a914140700301100420280440542690302c4001191050307442d0303002d0200b0942103040c1d0b010203600d034070300e81d50a0021080240c07c60f000d5000a00e1900100200c0703034055890070500d8806903d240002009294a00e040c1d01d1503400c1e60954000920022007100361401000200c41c00040324849000c0e250092040741103285182c2065444052840c8015250500035510381c4c0c00c95203103030043c02a0005030f40c4040104010082c0d540503040c0084202c0c141030019083c0350350740034080240440c0b5a507a8120340d01c00031b141c2080c81154803449403020036103510015141c00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 608564487 1250 608563237 608563247
    0x80d24031b0608130204110d0e030d14010e0f0a021b060411060a0903061d03280e1c051212040209060901180207020d0209010b090108011703040509130b0403 69
    0xd0340c0040300301c0d10354000200c680c01824460f200d0310000d090a41502516400c000041c100d031019411031100c20300c960f41d0400414410005000c5e82d030030040d5200c000301c4840b001660351100b240c1c1070643e0748000400c03a464440c80f003030360002c0c048803001030a50780701001d0000a003e60040039640500e10300b13024255440c0491100e028900038001c4501190607102030010510501e50340d82c3c00101c6800040010900766408030040c5d008800f142c21000401d01c071018a10f40040941c0b0040c00c40c1180301d00002c0c8800078010300f241c440b50404501c01ea0b10a8000340b0304070000006041c42e102e07110380308801c02c81c0070320428295044442050780c41f07a9007040352090b40001103c04a014112102c04034086240041c030b46412218000151a0072040ca45144400f0b5008501c040360007043c9000f00c4001643d800e01b2460103000030b51074440e210700054000501601c0180d0000912910b0040035402c4100c01108580641e182540c2c0c020507525040480a510300601b40050700032541c5005000030582d200d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 608565737 1250 608564487 608564513
    0x360f060c120609020301180e07030807080c010b0f010507030e030111041d0604050f2d010303030b03160302060901230c0a02031209030d0e040e0114070207080703080d2403 75
    0x100c0000c2001c1c0c0c0e02e6a00c1c0204038031003802200c0000110187c6100c1c413403a5070300480019103280003500c0c140c0307030391769036000c1d20350090389040700d84500109a55112a03c00d120340551110100d030b213a41c0030f600404c00070309079100e900805800c00502031442d00b02a2070942103142004d11105001381d80740d03507a00c4100585081c0c0925a00124051004140f481c5080c6c0210b42c090303e400d1601d981a921981c50b40e9030351036a00c4540340c00144141854640c0300d82441607050081d0300036140490040d26030003c15040c2803214a050050100c8541d0070300250716400140c80075007000303003008540e5450300d01e1030040069800400c3e040d000b000089100680700017162113100c40d803090741240c1950032240005030203030156240c00f0750180c3c840014011140c0c481c5802264590000d2f000003002c1130340740861425120b214080b1040181d2003000d2242e0198100001c400420300007014011090440c1c0da07003083c6203d803030701c000301c80c0d51609104807413446032542c00030b45a080305c60303403445403a40d84c90000c109480d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 608566987 1250 608565737 608565767
    0x41d0d020c0301110405150a0c080a05180303130326040f0303090f21140f0c01080106050408060a020705122106060306011e090515030109360f060c 65
    0x3407010384c034580c644c51020b44050f120020f0a1788030500051a0076009a04455001c0040001500036640843c1d0f08074018004040c103903a400356039408414001c000340c0551407944d0b0096000b000312802050240e01c12006496220640074420300c44011132400c0b0b070b018001c1c201c0d00080c00080020300c24002c05845412a4425141ca20485a660074844120340b8603205002a00b20462240d103103031004d0f000049905840795180400042030300c00703414500341c80d030846286280d11a881c0c420182d07803c403e0060041c04c031460b1451034a4204103849480e6a00509894029a0042a0041000800e0258441d4980558031250310f071000c070900c030a0229081044126501c401c4408504141010001c0301c3c880d410684403501022a00d0a014002c69901c000707034402c00c903500102090a9850040003c0c6010f0414041c0c0c0c2c403541006600011680c03500c00c8800030150342c004841114900032180401d0307040c280d014414040a03410f2012811f840781c040105002c1c9000511103005400411144103500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 608568237 1250 608566987 608566991
    0x50c060a030f15240c08040305150603030f040909080903121c0b0901030809040618020903060a06060c2a0909150c020c0d02060405150306030d0e0a05041d0d020c0301 73
    0x90004100d82c55204540103c54954046190319038250b0f0000b00701c00c01351407480c540240c10004688410f107a036009500704582a4010480782d2503034140c80b1102981091040703026624201d00321000401c40e1080e03111740c034290754a9402d040d00340582102502d401142c0a000e49008104000220b00d080c1e2201c0841250a0703200c1e012409883c0c2c03184100512400701030440b408903400d603120020b96401c0652103960060b1652400302e5000f601200e503680344210601e0268503590480d041604101000b01442c00c00c919106040100640c0642c1401141ea00700c3e14000d8451600818480c2c0a45100103011410b00e10100005605950b940000c885600800c9408068040341c10001d059503956690b920050b80035510354141468040c3d006e03001c080c801010686002c8d80c6130042000b003132440c4e407005024180402007040034282401306940c880202d15141d60188000d1000407190803590203020300850355a00c61042c1d1500481488a100007100100c40d0307a0b00107813500942d61428010b0380d9000b54 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 608569487 1250 608568237 608568251
    0xb01050405031509061f091e0f0c09090b0d0209060d061b11031e030703060e0f01050a080a080a050a0c0b1602010c090b1818070914100f0c050c060a030f 67
    0x4980c038840403408451b01e1640c0c1c007883e45428505c601500c80707507800c4110b04075800400e4151107034a01c1104456014103c01060202c0503580241c10055030b60301c4000003504115507000035545000616140d02d0341103490728615160301c8082103000c0c40d0143c00510070b61400880c8083c5000c116144020340c0c8255584080200d148a161900c2e80070b082c02500c1110441d440001e00451600042d41c0c0c0302244d80780005615585001d80100702e41c040e9041d0450030075810041c480750130004102070207012507100401050149030350301c12803071085a0505d01000808158080224841c40500c1c031029048403d1040710b0610b00e461031060021241d085000d0741c0380065411030980540d80b8501103628074401d103402c0038401c1a039103403425020f030b03400f9a01944c000150b00080f41c2945056001c1d0300999540782600c0d040c011940c11100742d404126100c2c01c0111540303c88940c0c07103407190440325401e00d41b0400310411072506500c0c2034510f01174180e0110300481e80c50061540f41e40f0104441d251680240005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 608570737 1250 608569487 608569501
    0x9020901080120070f060c050d0624050f030408090f061c1a030a0f020604030503040b1804150902070f05030c0d020c090105030a0f030932030d080a0b0105040503150906 74
    0x10300c90424010480d8144c101710001040300e6074481e00e40d203101814064900b8403040c800b00100c079641d0300040c0c803043d145c08200b114448040407140c02040b150810074504046800200c04601000300020040a0300042c0c155a03511185502143c403030740900b0b401c0d1101004111034045030200c1040c0c0203810301d444d0154038101c0e01a64080100c00c07000d8080c10101c082a200c1ca907110a1851017680c1040301000f001002a00c1000280010442c04c80016110010798080d80401c503911031003640b0480c2450b200d10101c1c039180c01c0c250215400004010307620f80040c03603d40c98480038010090580d0001003007150080c4000f260031910060b0039425580f04070490020032544c0a003c0c018690154010000080040c031841070400703215000b4244140f40175a181c2860800b81c02c0840a403540c880f281c02074400d20107400c5001c14021074114050f08824007507a4004003400320060141600380c0d200c085801c2281d003e50115005410060251245415000c0003078400403003d031303201703901442404001504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 608571987 1250 608570737 608570801
    0x6021c020325030f1d060c03161112061005010309060b0a0f05010e1c020f010903060504030207090c3b06070c0f1703121803130608070c022101090209010801 69
    0x140610300079950700117120316001e200054106c034041d070320f59110400c66001d120100140d1920864410007850f01e9017401c40d818490544400020702090354494410300000003061084a0141c3d6428a4001810125030903d1030280c0101c1e400300303400910444021904821441514068880a80381d00311180d0f048400d100f180e580c00340b55000501d10000d140c0d401480c0200300114000c0052501d6002c0e0380e1662202401c83c1c0c0141c804a01507800010200030075040b6000d18100004e4070b050005d4010514006a26400c1c18051403900043c540e0782c83c0000d8601c01071244039800e802402040d2034114516040c54400403600802400850b49180005c0400c180340c034104030740861202031810301d9440c038144071421300090214681604c80310b0b0039561710502007000e01446076502e0300712888946002c601500009001c0c0002c2c08001c50b03408280f0246e00c4104900c4000c03034202007502242012060f00c4c0340144081c46000354420880c200002e040441504044000c14844094480c40b00001c040c44d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 608573237 1250 608571987 608572007
    0x30e0f042f0a0c1502040f0605190e1804060609020d050118091a061804050d0801060806010c03050309010216051b031603060902030f160905010b0406021c020325030f 73
    0x80d112032401c60024894151803031419600560140c1810703150b1a0100312000c180e0490000154042b9075004c104889100442c1005050b0401074100d20603c030209102d00760080781d10710302500803804138040010941c843c02c010100c00c14115215509402084050903007846850100201c840010070f80769410320400f040254050006091791034001015a9101d03801072500f640000703400b400c22460044d20b11094070440c070400c06271000503200d00e0050a041010303000841002441410172031280d030030255940c078258050800381d45035a204000030b4060701c59404107421140018102904000001131502a07a8035001044254000e400b402d060381c80e44038083c12010f194541c48104085006540805c1d0001d0014003139684c0c0f81c0c2d2004220b454424250300d03d0700300c1030501d00c042100e50080d205a901404450078242e16103032a0600080d5640e80100c185048451051080c040300d5008208451620200010020b83c141000d00c408503141c00f80f8070158040f450b40510f1300e44003031040300198 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 608574487 1250 608573237 608573257
    0x13050a15050301172e0f09021e1306150206010801020c0703022b030e0406050a05030a080322120905040209030d08070c0c0f050406080613030e0f042f 66
    0x381560719007a80303004980700d13510f69049180100450103d0380c000c50f0307007600341c5007201d100d0a0121401186540d0f01719403000c90040c00c028900401e201c01a520717844076a50701560100081c1070701014000140072001c2500020380154a13110b000903a516071000e1a20400131070350251030850b80c1c1c074407240742070b441a0482180385402a150500041c54013011801e0405800e4440285261040541c8114104905401d50100d403601d4090b900a00c0c0038060180505003e40c1d0a0b13917441c1c80c00780802e681e0550854018040c0341e0110008550004609842c482d21204842d500c18486543c01d0203818008010b0144000a62001c8049014145030003110302e2608003800800c0318118803038084561500c0038040c0400c101441c0d106501207540022100c01405103014444e07150342c5040100700031a025a4007160a9030415001c019040c4a100e001101441e014140342c0d0211003190b00003030a130000d82c0440c40e0f02c2864900c0398141144405807001c130995801600c00c024941700211190b040c09040424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 608575737 1250 608574487 608574497
    0xf0706060504180c0b0d061502061f030302120706270501060f061b03050910020708070e0103080d0c2f010b22021303061103150604030b0105010e1513050a15 69
    0x420500f41c5010090103006c01c0c00e03400240d09611135060320000303600141c0000040c2c2c0100148101d00013880080200d5081c40b0504880440c51541e0103500c948210002e04822070740402d54500340400d54019180d07129500a1035070300852403441200321720054800984641d8a0a5000304072034041904400607200c003a1606006c2000400d40c1116800702034204804021041c4000503413502c0380940d8040c6544070303401174500542481040307441c001d0b0703541c45840c0e5202c00c10010404500b504007103035a030401c0b0000c04142c00341810025035044258044803903080d0802c4c02c0c90b803205030b800380c3c01c0c0071542001c4000384070310f1414500b001003020b0b00098020004038601c0c046007440c200c80d40284020f811007200e40c3e86455503910b50a0464205e00c1c1010101100081000665981080c22a0b081c441c100d0f00c490a05045031584028200c05010342d070305002c68103410380003542c0d40b0b41c0719a020b41c01c3c04100c030303540e5281903905808002c280d1240c603014000c03840300032550b001c583c080c840103903881c1d0b03540c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 608576987 1250 608575737 608575739
    0x403020105030411010221071502040e0c07111c060e1b0d0c05030303040b180105090a0b060613090c090b030c25050a05070608010803180103110f0706060504180c 71
    0x1003c01d00f04d8a1404241588035610061101580f210750341c40c8080010300c01e1a444031780b10f041504000c10f401055800c014810402404a021070041103034200d0b81e000c03c80703a01c030000e61400301030301004007013050b034001e002d00c1441010071008110105100c0c410300061002880f4034114a5a0308801540e104d00c0800d94507015880d8200035109801e6a0300880380f0380b20381555000460304650040c0e60a860b0801c804082000e030032a0080e4034850150756800070440e9240200d440c80c5c540b54010b40081002d1003060225281c1e580f02c01c15661a100721101e14581240d0f592410f000070b00344c03900c0810209880100c000303004480300007900d10421030b00700b250745401f40c61079007402000c511004400800003189001404110108128441c0c3d030711030307402801103c0c10240007400c1108140d1002c3c405900810015568401000084503c41803c0c03c000c558114106032104081c0603040204000503804200e02007806290341144080702c00036101088601c0d0741c580400d40c007500d0603c020b010182c405c24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 608578237 1250 608576987 608576993
    0x5041506031107061b020c101407080c011a0901090c1704050111030c03310b060a08030d1a091b0d0b120604030e03031c050a02040306090b04060f0204030201050304 72
    0xc81c1424248030009140b5005482d0341301c0044480d0510740c19903244540800041441d0100140c40000c0b200b111406501c15150314010502c4880d201140c05802c40482c04404100e0144103a0711a080c0c1c080c024866521405e07900824500400041c0303100f101c041e0000143d0010714400e44007508130b15980c2150800f80503a22200100e00a40121910740d6100c100a40020003040511300410540080c0c1f90340c1e007003694280100039180362000c8021407500c16040c01c0c599194030503200300303a130100000d04641d545c030b0001004018217901c00d400c40c0c00001030103240d0701d81c40e502c0a90440340c00c00706450843c0040301030181c03110086408071024035400404855a03a1080040d20724165401d80c00f003003080c0c004c00403842000d441d4160295a901c4882030100300754212200f580c04840980046007803481101e0148540c00c0d048030303e2010140c4e0781000c81c002c0c02c5603030129005550803410900692419152001c245401114150b81161400300c24113440840b60084400f100d805035581c1d07086481e070f61 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 608579487 1250 608578237 608578241
    0x60e1f02030d1a0a0e180106120b040302150907030b0c0901090303120b04021201050f041122030c0602030c0607020d0c03082205100b0406080a140703080c01020403020a0504150603 79
    0x1110740114030f0342d01a1410f0f589965140016240f4801c00e45001e00706002d07950350403688454013480c0340c0d052242c10300c454034800081c04801504100790814548542c14246e08014a070880c0c2010b0b816604100a5511800110314049a204901903001035640840c105100d0007010151800180427400030000700c1d10038412400c00c041c451400007210401c1c440006c089a00c4441c140444071061001040741d4640248402c0c1944819102400000110b1906140c248a014090143c4500858000350314142d4500c4501c09142e22644000e605901c40da80695a9000807882c000c1c44e119000014514070f10100e80450358507400d8440040346e40c0c260303a00751240039000300040001d503c110081043c00da080a000074401e40100054103008400c1102803047c4c4141c840f2560041d41055801c0052020005000143ea5084079001152100109020781042d1aa6002030030392080491600140c010640c0180200c910899601030116620b03028001a2203455041c266000c075450b004004160080d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 608580737 1250 608579487 608579501
    0xd0203030d050c0c06040f06060602030304111201180b06091e0103150207120903031202070b1314030a0314012c0a020903071e350115060e1f02030d 65
    0x88003c050524560202c80b914060741201c0030707680b0b125400b584006218007442000060031540c4045d40c51441c254030360206401804803120701400b40140e5800107c1402c1d440540061030a001d00390340d44405013030401c403075003040d9242407040ca0034801058903039a149014000c00c51030701030340741203c0e840c5880307a1074000d1600f80c00e00c000c29020880f01700080d030b0801d0402501c03c01600d50900103401c6040c000e02e500d44510401c503003684100000307004a0003086196902070580c00400030400c4c1c29152180900600081100b000c5c0700200741803200e1505034001a01108009140321101d07a40c2c1d01c0c02c0c0500015110125003a01d90307030350701c03030b8040d04144030102d40c00214164050f1034403a0f2440482e281c65425845402c8039006000c03c80442040096044000d0443c0c15103040f40749540c2034640c2a605401058010008003030300b1080e00d03404c0c29002070000f40f4440e44108410780d52643c001e4000c509450368203100311203c00342000e107008660300300080c68110358015400c015480b11448020441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 608581987 1250 608580737 608580751
    0x7031704110a0303031401060906020714060d020f03070206070c080301030f02120d09081207051207060b19060f0305091c0c05010e03070510140a0203060d020306040615050d0203030d05 81
    0x40d9584074605911140c0c07070b09000354032980d80013502080903c0700b2104002e042c1c005600f0011b41240c10414194009800c1e010b44045d6040b100400811034002100d074400c1040c1801500c0c00454034850f01160b19001e5072140d20b064082d600f055a0740300044522042503800141078030720500051001c1201d161101c0d141d00c0c4050007580000c40c501c0c3c0d2082c50080120409400140c95100078000c0308018010b1008501064401c2420300009a4405848036020038500c2c41c070201c0440e0220602001c1c0d084050040c2010701040c100d00e0b001300c5000d000c01034500130781c0c0202c0c0c0344001c02111a4464400c96114252042c00340608d802004e032461500c1c5409048401001680101c92000c14020312410041110b80c00c000c60350b507261490000d00b48001d0030524072515103082040c02031049a000b005602207403149006960b642c5200008a0080001d4000303501840740300100403c2050399840f0140301e03608000300c11400e50343c1c0d504202c90083c10910094152700180114115889240c014a8003c03003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 608583237 1250 608581987 608582003
    0x17040602090d060b040b01020a1203050c0f16030f081006081e0f01170f0c01050d110a0f090801020f0706050402030f0a05030403020420072a0e01030b070507031704 72
    0x102010002d0072100c2800401d85005075251640303200c9203060b00c101c03000c0d1242030001c1d0003030110300d8882c41c0040b09032009081c20b1540714000900ea4050400807140c544082600c440e8440580c1c4100748480f041c107403c1103010501940300c516900340100001880780354410398603800302e810034108a030700110182101e00b000d21071354591200c440303007801c5942c40746d10201c0d10401298076100180c00e071b50200e134203540b4450304820204011000049812200c1210a081050f50f952065a04c0801000d081e141141101d5002c151080c0c0540e110174049048a1300d070369000b001c0d5071968007080c204e00c03030761020007140c100810a4800044040d000903a2081c0001d003038800301e91305c4001c110b007402507100c0c0440c0d054200040502c1185040d1041080786a001ca0011202210700c0e0440b01103442841e00141503403800c2151001d40152008620b03010006410300301e011183d46000d02c00c00d501007800704503a400d1450000404551080043d0b071081030b051b0351490740f40300803050102d0b08658082c00a0301c81305 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 608584487 1250 608583237 608583247
    0xc050a05060706270602070507060e030d0c080d05010b120702010b0d110d080304081908042d050f03070309050d080915120711010c09030819020c092e0617040602 71
    0x1040c0502c55401c0790f401805c0c0944d030385580303103419400c26019411803820321150306154010340d2030009a05807000c14908103202a10341d0341c02e105c11503010f09142d82136130500300390001c102840c40d5400b4080d41c10340c40140e40415292500203a0a031000d040310a500281d05240e005e02040320403c100c80100c1c005040740300400110f49548425070f00440742914008800202071220007100302084050312024540601c4505103591103544000f0b0500140f1a204010b0484030030b184103030010004615804421512809107644449440c1e8100c03c2c0164007041c1010b500003420300706880300c0c184d4180e1003115140341041950400407241c0e01d44d00802c2e002c1109000710246986d10714800c038010039442d00c40b0103000c2c030b508420a007941d24030440001003200242003040001d488009907240d00c021203180c0c0c906280702c40341c100d15180b1401d51f2264812040c13414040c80c0744d03074103241030740c0950300c072900f07445c11080c2c00300394001c0341014403c07400004e00d81181d000380c4e030503d010100d802c64440e0300054501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 608585737 1250 608584487 608584541
    0x616090306060f1d0103020306010b18191406070c0504020a0207080304030c0e011d011802070218161b02040b0d050a06060e0711120307090e090102070c050a05060706 73
    0x120071940016810b2010400c050086009044404d400803004594058980d81140d001c42d4070b81006200302d509242d008921414140d00b100e503641384011b4007074821404203d0300f100300031114009210740ba43c2034581e24494242030a041b0708540c0100d822558042c150b500d000c0c03d10000b9400355054500314003e000001c1049103040c0010b200850090001d208018144910380641c0d00c0b0690044414888088480320b0034900102c1c03880c1150b4042510b844400494004131010f4070800900a511003481c0701100700400c45560a10701428180801c0c05c0820003515013500c2c0800620520b0003114501c0d561100185031640100724004806080c400074202c841e03850600c0c0c0389003024100c9030b07180c0320070f000c0c0301081440500552004030391400900080c161243c0d103468581d0b01c0040d840320030000000500e1280100c00402c02042c0c2c87d181141d8034600013038054001d400210003143d420008480014281c649401c1000aa9400611403454032000b03a880b1030050280034000d52404195846030341e44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 608586987 1250 608585737 608585741
    0x314010b061e16110405070509030d0309081b0f010e0c01091208040e071d06031e15060a02030a0806090f06120f03030108070f08030304030e061c020a050d0c020a050616090306 77
    0xd0504c242007481d00d1803110400c000039250b00410b000c00308501800203201d241d0b030016414610700707590300340041e040800742804510b91040018800607004083da90030803050000442c169051080c10013000226071800702d464441c1c9500ea10940011443c14041c020100840500510b05100e40902c0e807500b966010b10302e0f940c0d141100c512021070314159280401c08110f1540154016048840c0c600e58949451030110151000d00c0302d06003615074000245001e0040c1c04520000000100225254040c460001b552548200043c00010301100c001c1446424500c030304600a10448401101e1941c2c3c400c03d209024000000c08030280c811000a00070340c51051000718042e103d41e2000d041418140001d580c80802c1c55800b40e00075600410412020035403100b20005000c60840d10715644034000b5048011005800c800c503e40184006407070031070582c114004107124165141d0604c85100003040c140e88620f0b00d070101800d250005000200228604901c50903c00381908044480540301c2e168841 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 608588237 1250 608586987 608587027
    0xc03060a06080a1509151a010c05030d0b04020c07080a0219030b060d051509030c010623060714030409060e06031903300903031b0e0906060f130314010b061e 69
    0xba51503a01e03210f100c110704150380c40ca12004000e0034102561121540d5a954034410001201d800654370007020a01e5a9140c046076101c003c508200e461640d21501c4164440b80c11200c01c910540595540311446c40d00030590004a0f034000192140036654a400c1c0030040d240c4020440b6540160b0240e11240c051180506000e086164015500c0c2c0c0c040a078800c0c2100c2031500044048040b1001e0380c0308200a280000a00000940d4280d460340d5107860000c11500e42c040030341505000104010030810395642c409003c550306208c0741d08a988424051580742c1003182d4403000c09050a18442e00030030301420411140c66005000301c1c280540b10107103a0300c2c1c070006508142c841501d60606405140d4107020700500d5000e80b801d03600500c4a45071020701040c83d0050390304d00500200c4000340241d0340c0d44043d1050000d07655002c030390311001c84014105809031400100c0b2000c180d01e07418102c103101441140c280360009001107140180c0d448940c4c0152000c1e64021000d01c030100102c0e01036107007080d1152 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 608589487 1250 608588237 608588273
    0x10c0213050916080a0206280806040c05030903070219051c0c1a03010e090304090504051501270b130e15070f050301090b0a030204020a020c03060a06080a1509 70
    0x1445040034140340b420300d0050f010b0152103119480c82840712210215510000c41d504441c165516508200903044800c02d14041c0c8110b01150341c07683ca1080d4010551a1203140308950810000141d403105075880e00040e24200d03415841400000d00608104010341ca06d4000c1038030024549550b40c0018603560212000317980114410061b40c0c00308450701003140081d100071680d00f00d0070503040c500c540c03c034081441210440084900411078983d0700b40704540c060401d02c03805100c070f460f19040c015511114190080070015242c0300000e050b01130402c0450009071224548003504905503240f00240400c0e164141d071000132410b880c11812081d1091102032031034407018180e0750301107441011807000d00920703e5091202000380c000010354404201c07815101e40703000019440c4403000100300f4102d84c5400003900701e4030000301600c20f550009011480704008800712202035440f07142060030f8512600c580042540102c0b0203a00084940c080a99541c0075100d0010300e24a250321140644050240ca030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 608590737 1250 608589487 608589491
    0x50909040212120a0e030a02060a120216080721021015080a0311060a05090c0103020a1718070f081905031e03010509131523010902040f05030d090303030b010c0213 72
    0x901381980c210241c03011041088014045120307060700465494442d00000070700300600c61803040b420032119810b0794400441045550380e0001203282c03400c5c0303641c060030060362514008901b4000149401c10b01540c107036055405000e0103004600c4030006841101840544003032945000310740b07407c0810100010901994400c1c0c2460030080c91127080c1500070302040a024104000c1006046000035192401c0f602031030010f0303960990100450318000402a0b40c90080e002c88280700c1720f00c1c08101c01390a2010306000352a0b495944d40e20001e0080b0040c0305458064000300d4049180020303045c80486164001c00540f07140c607071740d14005450520071801050b5002d02c00300043c4064103040070320300c0d8400110600982640996219000d40b00250080b200d40c8a80300c01002c8500c400e0074131502990b403040054030441c0c1d40c44001060180d0014059250143d45140000035a8980041d542d6108441a150f13960005e0554074101c004c0c01000f414541441912070445006803105400a2101d80000e100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 608591987 1250 608590737 608590747
    0x3210c020906031218040c0c050c1e0607050c120a02030705150405061b0c2707021c09050312190807021905010b0f01030605100e190e2505090904021212 67
    0x4100451f107200003600104005030521100050002803c1110803104a03804104604c0700604410010b0003244669007244000c030755403040100000c1d4103a070204048408401e210504080e442e0380d9019554040d6043d4000b030700030000780c180740510801c0d04000b4071003a45003c0c1c80700c01084003903201c00a0fa140d40c0f21000d07114a080c44007448945043c01c0c0868914240d100d0080018a803080b6503c1007500c03d80d0100d0210700802d000304030309800241c0c61100603004080e1034002410039185445018028003c031565000d0070f5580030222303040100c080c90259001d40c0228011284220001d02600944c40b800408014110100070600030341d51103600003180c500509400c2c81120314201e4020380c14541049800d020540e40c203286c203c000d020600d00f03041d17040c030b103c0c00003518410030040502d480c4010550100d0b00303150001c1c0c0284525100d101c00184100c00b205d505107100c43c015042c1e400144140300001052501d41002a003050005151000b07652040003030030b0400d80f448070010400d40300028 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 608593237 1250 608591987 608591989
    0x10e1309030801090e151906230405090105070c0b070c0b1003050f07030804090e0712111203160209130c0f062003090603190c0903210c020906031218 66
    0x940e041741c480c2a405003c0e0702d5000340302d45001560180c540840c45e4a03601c05403448941b981c0c402c3e0010b1102018113552200c4109209954000455125004608080c000f40c50742005000e924080d04081c1c0e50039119184030381743c6480e91507001e40030100300083c407020b00c40881e5901c040746000b0059584510112855464900e02c1c040a003000040300c2d412040082010400362403d44003140c00300d80d00419407000040d212401d080d00c540002c1011006003a03020184490b9080b00b100300c440a035088010b03040020245682c80c0100c01d0140c0700c2ca4002ca03c4a0014207040018030342108540030700600d076011558989803492102d400c402c40c00344c0950000c104a584c8241c06032030a5503a415840755040c211070031952284603402c0030030700030440000824604c4200034199210f042104e8802c000708040c1c2c650041211059110680d1000c440501005800f0041c82c42ca0b20825101d8031100e031902c03466401d100c402080200070781e5050140784509102200100d00504040d00c0040d8511407481c502c0e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 608594487 1250 608593237 608593241
    0x90803391f0608011a091506030405030706180f1e0807050c0316121202031c0b01080609060d020112020d020d1d01060303140325020610140f010e130903080109 70
    0x64000f4080e603052400c0100e299084c21843c81205000392048210750780c40c1009800004101c26005400c80f40c00420042400b0020000c0c042d6203200d0310303003070082101d00300c4000c1c6400b04a040103031a45510084100001c6c407060018840408920500d41c1e00e0980d60310340e000c40da0003420050f5402c3e0404109241c0ca03140902c01c40c2c0e10005c8600183c070540e41048198041c040200070002d04220034401158100c0740208181c81204403020840e014441d44107540c07c02030000d001c510790124040c58049031940c903003000c42a2103111302400d01791004290313800449040481245d1100481d90030015001d5114040c001000741c0740e400740c4082800b4801841c14104801c44100403c43c1c2d07450301000344002a408500e81400c80140304005840c0d07190b4400c4c55508d4080040403807550581c00c0c50604005801007074142c0710340c041e20303445401c039540c0321441101c2c460007084843d170000036050420029802180c02d454050005043d803a060038450b5102c0049600841c01900881d40310380c010401200742e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 608595737 1250 608594487 608594489
    0x20d0c062003191811030705150d1b0c1b050901081e190b07050d020d06240f050d0b030318090a06032102010e011407090803391f06 58
    0x904100100295500309029165521000500201174109001156541088440c0240c0030040070918212101c030050b000f198070801034652200d0908204255101402e0002c030030701084c94882841200941c4d0b104900440c40010305a4200c141150104190b1503100703076180a007a1401c014018682e0814544910742c0c40c445135070425510000d20403100009202c1c1956245a000c0d84103140e980703424100382c40340d0040c501000249407010070904014580c94000c60200c8843ea2080c03c0fa040d5040040610071200400e00e01c00300b100310745400328180c4500010920003407514000950030020000103070541d03100c3c802840e0640324182d0060140d01e040e00e0b5103900700b68604410005035284d90395480000c1e191520b80c1c98510a100c521413081030007074020114420150000f04042c1000039040441040c042c0e80e0382c0000340010101003490766001003210440b108000500f1094981d00340340c01340300d44c00886032640c03004140c4594240c4007020018094402513041e115440d89070900b105030216546 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 608596987 1250 608595737 608595781
    0x60e030f061b07020303070f0c050906060712051305181f0f05011d090f070809012c07050901060c021c030e12161e0e07020d0c062003 59
    0x120a02c80c1001820450510a8007030100c03040e180c1c00c2078000a07065000c0c10350007511414a040a02c8204091005100c054620480e441040d5884010034010940500320005083e081c0010880c0c1482e0300078809000018032403554002d16a4440700414074088504142c080803c9010741800005a54595800c0303007110440402c9904030314011070707482c21894510030941070005170480c0ca01c1011664044440b0341902a04818030b5040001540e400e00c10203c0d20100040c45000106014440c103024440000003442c003c01c141001c0304d00f52034640c03201c40c3c2c9207915500c03072894001880e4a900c42c2440c0244001d4480d039410002c54014041d2240c444030b6840d101d24194060400000d4121510400c450b00643e030007600c1e59000d80b02c0a00d041201104103a5400c6261400522052a03003441e520320048208448801c59403002860300415080d41c000c0e001d81c001c0d052040e1502c2c0304070250b1407058010140031a100e5000e007910700900600700e1501c503002800004004220303a460006603180e00d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 608598237 1250 608596987 608596993
    0x60a0e1e15060904030903080706060b0c0a0c090b210705030d110706031e18060204090b0111070e01120305041806170c030303010504020702030709020a031b110d030f15060e030f 78
    0x50130741c0d80100103929038000207120307041c04500d10080c0b100b558003000203007040c135a005964100304034030345941301c85200f41110f10f215a16004690019540501880d0b64806845882c5420003240381410b10440240d40a20724070030138000041940d810407550b006000c10380c42d900c00b4500154055400c02100d50056410300d41002000300160000f180010008039020304005000c01c501e104205e20081c400d0409049240003040100360244154052030b810b4409884203405103070540600c94407402c01c0d200e110ba0794005540100582d160103d210046d0f64401c0c580071b45826207400d402105505100440d01e2000d540342d00a1114429000204442c3c0380d00c2c40050a0710300c0484006640c1344014010140a1074010460004640342004032002400300c3c070b40d0540d210344081c90002c00408071a10120003803144005501d1146008011654500794104082e001200c4100c5003900a4038100f07042400141d524941d03c1140111604064003805080d501c0100355544042010319108888090b071050350 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 608599487 1250 608598237 608598241
    0x504030201021c120c2001050910090b011502030c06010303090e0702210c0f030316140f04030b0408160f05070b090f280b090310020408060a0e1e150609 67
    0x280c0c1210440300d0fa15013001000c03498003d034040c00c8445038008441581d00d8801c4500301801070206402c0715106035810b40490306c1c580995001031040e14025000603100201c10710061103c521240860320250006004072490644124501c91621500342d1040c0d00080b02480709003d010b84811019412100500c006c0540d4140380880d100d42944c2045001c0741e0843c00502c50454901c02e2001d0302e0882d04142c2039a840389042040074900d1280c00081c1c0e0001045411103001d0f0140d03603802e940c1898840380b65103080c642556134a201507400644161071408040c80802041d45042f142c0759801c1d41b00b0314900e96078154030300c1c205151045681013054400005d0003444850b44940e42c2e41d10307000008480d103203040300d40030b0201130f2090214144a00060075010010590310460b400402050105070300302c4201c03000ea01ca2540807800395002c0c01000340c1041c00414607020302034028441905019003515a5100010760a01882400b2130021580360416a0b02076115001c181c5420340c0082d0a0ba1030340564 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 608600737 1250 608599487 608599543
    0x6030d050a0e210a03030f0509070e04081c0608011a09070c03120603060c02160504090f02040b130e0a2d0f08090907120c0905060d0c02031207050403020102 69
    0xd035249000c0701d0f008001c81c00384181941480010540c000b25800191103d800050500070041d0078102040c292882c00d140214210310000035000c011242d00b175480b840b103902c07560707200301c802e6100742d075462041d6100070280521014288905001400303413900001e40c040c221401c00401d80d4410180520441a003010804a2900710385242c0c0455403610700f4074000c17401c625850300140304d1a00080c0000d840c0c40b003019296a0000f41c1540800401801132401543c1c84c410001a9450f42d0b0b00180300f000c50345860001810b240d040107010380e100034a000e40081d402c0050030100c0740f5024079001c5507032040030040244609680b00e109240e0790031300101c00c02120310424040300340d00010300400300045441c2035004e2001d2442034030700003c070041484050342080d140092a041000e00201101450700c00e40d40703070740c07800340031100b0031500054802405c0910407114000203100c001c024109601040003007a605808042c00507200e940706880e8542c0312415400024942590404040c00a2324004070590070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 608601987 1250 608600737 608600747
    0x81501030e030906070f0501320709061d1003020a0e090903120402010915020c2106060f06090d0606171504062c0106030308070c080f090a0b04090506030d050a 70
    0xd440810b69004e0f40c0c0c5d03d602c1c58040c40140110b00041d0555180c026516410058417241840c091b500c040d1076410b0741c4414240301140c1c0c1d0152401e002061a242c82000b0882c060038404802138122828004442a5400130580308100c81c1190000a0b03030000e41b0020a5070040300c0450000b20560300f03141c0900d0076140d90f503038078402c080d541c111034003078400001c08681c13141c00c4c4030015102500c15070b0b07010780d580e20000e580c420642e8034a0b44290130800309203052001140a04d40d0052502c1c0c024111910b40e0424000b4071680480300c1758000600308580c0a05440c0c1800e072940b02071160b07000141e900d1038424180507000d11500d10002c1c60300030495413403903402c100f644c1075001a0000300014000c2449141000d44502080e442d132500c8a18800d80c2036450410340c020800c40f4000e455200607540c582c6021510b2200800c4020070304601441010020b12184001e000c1d0f00d4401703085801029228007011026811aa0200441d15112000c002c900d003014466862211058108241024182000a44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 608603237 1250 608601987 608601997
    0x1050705040b091306080a0803061c020d0308060103150608150904080304031101061205010c031b05270306160e1005090d0f0605090109110a050117070c050d081501030e03 75
    0x1101e440e403840c514001d1306007548098001c0616104851102c1d03158030340402d1580040310524440d0790710000f03617400800d5170008628660b90050a0b45840d40490390250307250300c07001e00204c3c105076940400510707468a164881f0b0103409952200b04440c03910303804040b20000802070441c014040300090000089440c411341e60040c1d0303d4101002040100e6038400e0041500d0391001c104101191009000d002c81917008080108003503606020000c5181c0741d5038001545403a408000030400c003c040c0c551300c981c0c10400500b8a41544504108000e03000207403810318142e0300e8070703184e40300110414080e940040e620708007104182c1c0c0c4054100034040010b00180502d103801c1c0e000b0704400005200f040101d4106600240d4050002c01c01814500c1c60103000f840381070360480b5860640c0d4845141803802aa5880488005a5518040c0c101b01e009180c00094064440800d0111420f034100016406100171206030700696a007044a29010068001c02c2c0b18944009051500e04000c08020810100840e2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 608604487 1250 608603237 608603239
    0x90203060619121106030109090b1003051002070501060906060509031e07050d05030702040f0522120507140a0f060b060c0a0618060614090915240907030e01050705040b09 75
    0x4030010f000e04203181c0107107540d4000b55002c2400800803444086039400300c3e0009010700d62000f0075503141002012810614000982503500c8007004900c01e403140d80040001d00e114100114400341d81d521400705684d02500118046100440c01d0761680c01d08020729a60340c0402103450100c03499107050703151281654002c140c010a21001c4407418000704000321444954054820408507507081c078000c6c001c042c00e980041d800340748800c0d10800d15040d0f081b0244009d40040c603030440a807584105981c04ea0050b5400c580c51101d103181003455a2003840303458021400791844000042062400e802210142030811340f140d00b0601c0216500b001c00101c40c1d183c83d501c6040090080381c20b800441142000d00f200030012401c01c1408114840c0303c0c805c00c88103800959078600141c4840d035440e9124402540280004a0380b03000042d481f08001c030560032560807890030301d440c0d49210380100d040180f003141c00311701103502c468441302130b031000348251130b0302070f446140c01410a4100078001190b8480c0500f66 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 608605737 1250 608604487 608604509
    0x81b060406080105010534060e030c060c1b03031609050d120309080405101206080d0516020409020607060b01020d02060613021803030417010c034209090203060619 72
    0xc4e850290211841c00e09000710144d58418108072240f42480d0f502408908171101c1c9e061801300307000e801c070000c187d802500e62100944629a00c619500381d6580001d00d030200310800d46500c85c0241001440218010304103510004644613101402801d080340311340c0118050303100340303080001041c40c00396082d15261700d0703103800719042c602400c1802c814050f581185511007d40403c6070903890f007140502c0c51704070900700248003442d599a1016195210302e019030000c40c5040140f2003925804d400c611103241e10051000440300031a8010504c0d640085170200c0b10680da40d190241d10f980c0400c004800c40c0102d10041c00649000004035001c080c2d2403074103205107a0080759001c612101807020300e82040700513080700d4a0300d40e41c80314203204207400d586200c0d4035403901561840b00e0344a40a040013440c40030550241f0f13000c01407070b07850600c4251f241c2c00138003031600c0e25100301040c080103580004100c903034404141e0040c680101800d004010784078070b02c9204007403507000c2006003600f1580d08a07103801040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 608606987 1250 608605737 608605747
    0x4080a03240609050301050a0b0a1712121e010315150e0f011a04080304050d060f0515130e0601050d03020f01110d0612020a0e060d050304081b0604060801050105 71
    0x18550754419480051a10609aa03000c21010742c45401c4034100e0360110002e21654031482248401c443c0b07002da5660308003d150205100c0322422180704c01e8203c0c1c58a0460758104070b5500d465205400c245d481020300c0314420b0030700840c914508401c07212006401c0c40c0001651450352a40380113409074a0213101c6c5c0da00c443e00196081b00c040460402014200500c08082c54018002c0d150403509000e0340c521199040240319441d00c480c020b45007034982110095140505220801c10303181071110302196882d41740c0c1140514a03030303140244d5010b0540c02c260b840d829220003042080c00d01d01c501110000d10b00c0c0c009504125940060400d04484040e208044a1f110741d0078203d041082c0360300ca104007503003005910b40c6d80c0020b0b070b8010810910b4070201001420f8491400c40d00c040c000b9600a540800792000c10b0060b0700e00410019003103100100080c0c14440f5954401d400d41d0880c1d80842c50542041440d803003107080c004128040c1c0c40048842616050900101422000e01800750904004000c95 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 608608237 1250 608606987 608607011
    0xe0603010b0a1509060c0302031c1e0c030c030209060f0f09090f04050d0801050907030c0e1809210715020f071101021c050906090d0209042904080a03 66
    0x22081071070a8000d070846150380e0321103051020008020007400b00041c006000059041d1040e01e9000301d050341030f03015514100014001c043d502a0410100401e1584c404440300c110301c1d039061007440b4420321300c1d003c81e02104004000d07045541a05017201491300400000c540382c0d0360b860845035107144041c0c00b0354442900c40c24240720303801381c01441c68016102c034081c011003401e400d101600c207610a0080310031461881c40110341c424401e100385d5802521100c04522301d14040d400c801c82c0b8494914100044003e030314001010344043c038160900d02c1d4103100c1400082c41090150f01c3d81c0000085c40354204150f4692a80316501c01c0d03003006409060f4078800c2040c00071840d01201d0710295441c0c4101c1d210300e100c0c188480301d1652194054054421544000c80040803802c040c0d440d6040760b115981442034280500c5020b901035074107160b0001c00140b1850042c0c3d1044400d5000e14010b280f49487c954003940c0300e0042d070780d1302e803001d42d10302c143c1c081000002445141214544441c501e00803480c1c080d404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 608609487 1250 608608237 608608241
    0x50f070504210204060f141f030207060b220f051506300105010305090609030301060c05030906040e070f0c08030a0c03020d0903020105150117061002030f0307021b0303090a0e060301 80
    0x1602c002d40c030070700f030800004240c000c0d0310130039050342c01d0340c1c00e0001d83c44100c004001c11b04804034041890381501e00e141035043e41c00b9070f002e0150030f4050306011502101000004080842c0b0700201d00500b01c0050f42140110100d110343e680001107488100480d0a00c480b07106d640d01486a42c603441045d000462040300c40e02005041d440141c14804032414100d03101d1604e0000200f40240c600084c503240021380c5c221000140345000d1944200598550303401c0c0901214038034450f04099545110401030004c56071681c1009100401d1640f003041e21504000d03100604007218600104200010180d4040101d82c00f4030449406c02da44000000c0c4440d45001c0540c040c0c09100f0040c841940b40800c0380b428550190081d034800c907044803940074040c4c418001911082e0012400d11110300c0d02c0d000295250411a00c0c1c001c82c5009401100c0c02e00c0d51881c6a9840e5910483d00c2d00f0050f00500000021609048020312080404070050340c00c000c0b261010507290b4407588a080144282c6401080d05500d082d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 608610737 1250 608609487 608609549
    0x6060a02101e0e032109070513020405150a0203040608061c05160504060f030204020c0f160302031c0e0d110d06050f010807030f0f061815050f070504 66
    0x600c0c0038880d000c2c040c450307503410020480455080c542803054108045102200702c9611051681300b80c040681c840400040e0b05c3d0000b45440200c2c41421004513581e0b0380d484003d008032403462400341e900c5042c101803040800d00304608003a103e20500203400002e40200c180c80686265140044450f0b9a180011302098004c608003541a151030380789109008000c240c2e43c0c1d56640415020203110341d0b580c103000840e01c441c801c2c0c40d945480d180040c001442c041d0000c008501003901101c0016800703006250808ac00c030184108181a150010411420140f24071400090032200c5141c0d0215201c0340a0311140301c0d100d17480d05c00c10420080700100401001001e4000350003401c41c0c103d01000345007400040800362044e60342d2409500c00042e0348800056084240d940c484914122103019565a01b410403821004071040d035151560070300c0e0100e21400701440c0c1c82c060784800519448145d203003070440d5400b40c041440c01103032804001c0d40b40d4002040740d0444030314a418000d130f003039a0100756080c0ba0031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 608611987 1250 608610737 608610763
    0x15260f191515150807050c0d1214010e04110607020603270d050a021009050a080a05120708060108090703030f1421100b070f02153703050f06060a02 65
    0x1480d40420070f50102009a480c0600c20b44450006440300b9200369500d0040700e2101945901210b1002070300c40c801c1d60b82d800c48003080703500820f2950700741c4402c000201d0240c120502200041e0100818080c10b064002841da034141c4809207001c625401040e0b0b030348801440c008100c407001602596100318810411032000c100d0054032401907000800030f000b03a002c0c2444200620840b00100d440810504c42c071a02250f101c0010403400d241c43c0d0310020941c022018020034002d060101d8110440b0a40c04144103002c0daa031070b14150303c0c0000001d4020769024091038034aa0100005000080d04280f400800060504141007892241c140c610014410401040101c851660103190902c060909840c040ca808100c4405c003c1c1d220304030300c0303154010795501400e5038205410b28005401d14400f40c000000400c0f202500d0100c14210b00c021110b45c150000c20380303010350035000c010a82100c01c5800007101c2840c0c02d2125040071010340308a24000360070280700c2e4100142103c100d40c000c00105002c981c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 608613237 1250 608611987 608612021
    0x622090501020a0f050c10052d04020a0605090a09020f1611010e01050f0a0c0f0b0f1027020f070b010b040f061b030315260f1915 57
    0x124900d40346010b508902128408180e203050200c2045014009a910f460000b000400400c511900c28a01521001e80740f40d486d03443d102d039031400c2402d0400c40d40d140785103820401c40d0903007043d1042c0042c03035040c5e511030303420400144002e00032507aa0360401c008581c0d85110258884c100181080903d00c25003400d00001c605800072075041060040246135921004d03201c1182e103c070302e82d0040d42c46219140c002c54920004100d030301c02c068002e842180b0381d98040c680001c103801c00b583e030703101000405803841c0e80303000100750420502ea0036400801300901205038201e0010891118510602c480d4282c4a044440d0007007508141c052040c1c05841c1d01a4000703903c4c14155035035200d40485030740140101c02c03100b40503120100c2c059000d051240025000381d14048058001620110018500000807288000100b48001201000d03040d105000000040f100001810030351061441c003400004407844980003040b0700700409103048003441e1529000310204260403441403014000f44620203007041441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 608614487 1250 608613237 608613251
    0x4081b011d0a0606051009060f0c060c020f0606100504050112022203060506100806130e030c03130905060d0b1302060301090b040c030516030e070f090e061e0622 71
    0x10000250080707481d005003c1002815240c0c1c0900000c0c4250009801c04151a50010844140f10b410169a0b0546614203812420442e5442c003080c0e601200c41d03200183c3c0410000042803034184262038000b20210b4012800445603400580a8011441158140210b4000359117042d01150121001000c003281103a84c5808140840c0303003111500d01041e6850340c90b01c800519281003a43c1400006c3c240d42e1203280941d501c0404104551480d00342c41e450103607c0301e006001d8010100b02519880c9503210241d6100d911480901c5c111a4080e448600c03024140382c244078858035001085150503800c829421030701c0d52465410034200240450081d00600c0c000000074000301c1303da2004500d80300894090219408110048040d109c00b52005804003103603001c01d240b920b0099002140c004946804c0d205401e0751889a02c0900945078860151161110401c0e1007000b400e102d03c40e4480000000c1c0d028031a1114921241c1d268001e1003680508441780840e01e09030070300c003c072460344404070000384000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 608615737 1250 608614487 608614541
    0x21c0c0f051c08010e01050f120d02300d23040c0302010e03010903020c1306120c0e0c0a02070302010e13020d09020f27060f06040816050904081b01 65
    0x41040b031414000110000c6200a4040d210f800c0283c120740c50700510b040d141c5d0a0100f00700c200c0c000c04692a5022002042d95080c0000030700500d007136189690090001501056603807092020f000e200c0d1064002d040d032001720f4400310030b0280c608100b0084000115400e48490703006078415008803080c0d60303034024400c00c400c00c9015034078501524400c0e80c03250703031400b1102c0a0500381e4644100090168001d403503520610b0070700d1004818020b00054000c6201d56a40c0b81990103800940e400b42d81d005c680c0401800045aa080310a4201d458003146500d4100f03d5040251a4480c07408000d04000c00b07504c40034919652801c00c01d49004260108540e44e85422640d000100881d0804902503a0180c911948074601603170700081e204202e00014540440d080d40004400100902d25a80a0000d41c0c03410070740d840e004060006460074600610031107920000f03c8402c0b00c5142d100e60306c0b51030079804010009848105544520043d5020355039044940103031140589000d010401007003074000d101d94a9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 608616987 1250 608615737 608615743
    0x3030403120c0b101e080c0108070e12010207140a170304151406010e011805040f090c03050d0e040612060519050c1c060b040323030f0316090501021c0c0f05 69
    0xc0344c80005c50314001c04d140324550010100d5501c80e01105410a103070803038040d409005990b80c003100c107103004c0b100d0b000c56100144d001c045e0841c42910343d079404a03603001000380c140f4440300101c8059004001a103000d96401d030100200d4151100c4540b00070020030104445410052514003109109000b80b0500c0c10790034414250440c0d50900180031040c80391060b5005c1e135042d101008411b0800c40c0c20340d0911087c032006c3c0c500c441c4401021591034a00401080ba0143c0510282d44280081d11000c461030500a00fa0031104034a540704600d4001d0410103117591260060609a0150700420160f48403260407250b04041000069a14108003c024601c4101c0c401445c944d00e0003c0310b4006c502001101d6000c0341e0b101c0c0251100d0b154100400d1021420040407194130000e2181400c0e4060703030b010341030390841d000103000050200002c41480411002e07805000008020791401603000c82c9003500013540d03031070319820909407685521a4800018400c1905e1480c0a07005505103002c81e003285410f6079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 608618237 1250 608616987 608616989
    0x11010902090f070e090f0a020715020a02150a020f030103060e03160b090d020105101a13031505011502060c0a020f03070803010806010e16050f040e0a2903030403120c0b10 75
    0x40010080400c5085130320f0201482e1b030140e0070801c01d0035450760b2042e440900950164a040c1e03100744100344d802c01041107500081c211440141d0240c07123111002d500003c2d100c007000d84403c2405005110002003000d5000a99044a03003140010890146143c03425003188a40500c1140c0d84541d8501c8030148140280c0d150300400030740040381c5a55000d01c0c0100e0032210295203100c03140c2050b400400c00e10039000a20004102000010761a0006104060b011860960310444aa4020781e00c40040000c0a01c00d890041014140c0510164003441d0001d4950234014031500d00708001080d43e0311110b200f041801e081da07141c00c044940e41d0a860038a00d009070000d10031f2140511500c0c0000c2a42081450900e020b240c4038089050f200110300001d450940100c1c40b810400f00c024040000d0b00403400c00002d0192810b001c000800c03084410791030a004990140714420b64000d101c400d84581c40c0042283d0440390400724503036541100010444d18040d10881c0030b13218007004c0040c032888061a2540b44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 608619487 1250 608618237 608618251
    0x80f0a020f0d0c0209040209040204140f09070b160b0c19030209031b0a03030503150d0f14031c02160501020708130f050d060506040b0301020409200408060711010902090f 75
    0x90202c9964942210031040c140c40080d04036202001040050a2550070590807620040000c994001c507054202c0b8081c2080719150030740e040507000d01c8001c42040c8007400c098003850b00550310b04030988150407450a000c80000303150a1110002405129000007900d540004c1e02c4075403a5200004e242c010069000249164400c2c0161400d07001c4d0390011524a00c50982c014008a041c2441c1d6101a561034000501c40c01a1517440280c40e8001d6444540301c0e40f24610031003009001418070304255210003540e2106c108154020015401c05904034000750b00c0c0d03c50185000359907240c8440d0803110203801140020915070000c18403008111411000c1c0c5000003000e40560b85850750f0300c0f91040d07011000e01c0349541010000c13040c6030116115411055003c000584041803000c040008a402ca03030255000c90308491752000b40c0e00e100100700c04000c0180310102103450070306040c40c80c03850f201d010150001080c000f0b804040c003078403882900494090b0ba0001c009011610309244965081c0340115409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 608620737 1250 608619487 608619493
    0x82b0f090b0a0b0a180e120a030c0206070813060e070e06031b061206040b03070602100e010b1813140307060506030d0c0b0c0f040902180d110d080f0a020f 68
    0x82d0754a9900d12030f84000d81001840700c1c80091402104100c07540104241c0d8040d5604d910f015601207401300320000312420051041a039800c0d6400d40103007290001d610110854110205120003e03a1280ca001d421981c2120368001c44c0f02d0b18580240200729141030340b60540100d000000301c0c110702d0818984124410b809688121000212842c035245038100c1a661051091203040414103010b1003190703000801501c0000d4498031b000c006842c0000b51303405200181d2002a007000155103500901c940340c40c00d08000e01440001c6800141c00b8200820641d00c4003400000144c613251588140e0100250130000304c40f501d40c000c41400e5165070008000741c2d180360420012801505000441003261103050352502c6000005980da11a40c00c030250034003280c540c050242100100d81c0d04000c000400f030340701006903140b5106840082c1740700c05554140c461000001c00703002180c000700b00c0305c00b8500300311441c24840a0364600402180180d501c014010380000c03504503002c070f40014001c90032271101c00c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 608621987 1250 608620737 608620741
    0x60102160f030219030f1707060f0b0109050a050d12020118080702040b06042121020309041b020a082209140c1c021605151f03082b0f090b 61
    0x140351030b45466100007030464002c41c09010200c0c1f810460718940401e644900303454949561100c0c002d0703c104122306030302c03156141c80a000d15a00010440c0050405607900c4203101d11300300001d020513521030809014003540100a11445200b136010b40365910032440008440111030900720181c0d003001c4c400302c0c0941e181c000c2000700d0b85003c006840846015070003010054060300842c08480c843c0100465080d00d01c5040030048644d103a40c00c480c10303180c9500035615110240104400d86c0e0110350140d031007211022301c9006a95000c04c3d4809040d41201c0042d0fa40e050501d10050f4410480c4180001e401e108040440d000c5901e8220098451803185105210344400741c171106140310341c2c4052a5021001e5220341101c0046401034046040340d41c0900c0082d03031107038598600780600715850410150f1400100000b1404415551038095114402440c10600315a0303540c0c43c910880f610306d50a0701c3c01c10140c0c0424541c118015a583c1ba480d48103000c1c114140005102410807400221048084040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 608623237 1250 608621987 608622019
    0x11070309091404030e0102010609230123100c02180702160503070614040302060706090b010b030712090f0203150901061406121003050d0c110402090117060102160f0302 74
    0x6040b0301d840928aa555494a969509541040c50303814002e0542d5240d0340d00141030f03091803240c08d0f40d0200350802604800c4200a141d4200481608111400240341c814008540011104034004010503075481d01e04a0351311405903414a40d4400084d884400750885030080d0750203801441c000e10203502140d00403034041403140c0d0b400045009503501075001d05010005c2500c6420071084c20401c1000d03c0e40703400e4407034000c14401d900c4024280c9440b92207070040e104110802c00464014406184201d086092072100102600700b01d043c480c0c0d4035a114590901489202412600e00c942d00604688070030080e00041658004200c400c1100ca5180417030018461180300800c182c50369000b48002d1800c0040550400c2d0588042d000c540c090108220201c0040d000b00281000c2c011b05407100f40070381d10f240c035003064410140000780d801240144481207041e41c000d9041d5030219425802412745655403030040386460310444408210751654100000d030b00340c0400b010700a49009581391481c40703400b54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 608624487 1250 608623237 608623241
    0xf010207021f140a03020408070b04140d0803010306021804020310080607020d0207150e0a0e271c030b06131e030b19060302120c01030f050705090609040209041107030909 75
    0x402560302081c0120694141c0301c400d43c00074108110241401030410761039400b010324011227508000003003a00028280820040380761880b84e024002c6800c1c0044400135500d5207494001844014400380d004030358000174410081e040c01210802420071500c4e481d0030442c811940c1c0701481030607203170b0280c00e02080100b480815086080411070f002481c0300d600d04400d4420411820014104200b6035503940c00080d9559907a0300b0083c280000746417080d0400c144030b5251402030160a80030046044c0c0740f0f0700300c1c5202050109003640100b240c9080090001010703005060341023515540250b000650544c070300c0442c8110030540300044400709040004070b1a06101e02411b0001030300d0054007800141e800000c01d02d00c41103d503080070b000b0a5490303490340412807400f09104202d1054200d1420012030f540d0500c160070300e41c00e400c1d02c144070704e00b4000703000340081c42504007541c055040041c0114568895030121140f1000140003040f80ca03040e850805d5041e00700742800c40004002c0c820015140440f8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 608625737 1250 608624487 608624539
    0x90702010203240315100303140a0c0b07020c12070819020924031002120916090209012303010302120d0906050702180907090b0a290403050f01020702 66
    0x41e0490321940c2e100710f083c086280a00d0700c20f1981c984070381400c1500c5032004003510350051082045840d1440e08500d0003402c10b4010b40c1a09444c1c46003407003018103096000c5068400141c102000494540351205d040741040914218140c00540340a19140014400946a0200c1d58034106032658503070b56040c0ba40c940684000701a60002a42020075201400c40d00300c1ca5066945860a03c540000000801e040c00c1c1010034400c0e04541c040388074035059041c400065800620103018000d03851031607000c4d4441e60220301428203c41e60200ea0b01034180d02075141c0200c1c0b480c20420b01c0c015898004184c54584d402400128000e001d950162030b001c1e00e0009500c00d0050003900c0740101c890400750121020381242109903404034503800600c076024000305003180500810070141400c81c1c1801414400e0340c80c00140360340110382005080050f91a50f00d110152a0186508822850302c2c0f0907000141d802550000380c0f10b03015070961089103d07415401841403c0c0b0994000c1d485200042c4882039259134 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 608626987 1250 608625737 608625751
    0x426070f090c2309030f010504050d0f0c03080411030703140a0606060c05070e0601030f05070903050c0111120a091a0d1b080403030e030c150405060901020903121806070b06090702010203 82
    0x314400a800100307040d4054030466030054110341b4601c210503211800d403041a142581c95801c00404440410b03400001940c01038024209080501d969560003000503078001c00c00352a644410410b90b459a03000e1144200850b00003426010b5042c2901031b07a0f40310300c0c40c200c040b6030251400000080782070003000c9480b44150804003400e141e0740f402c0a034000e29500107200707038100b680da1102c480f00e035641d03071061a000d5181c681d20150f44038194507049113482c0c01580c2841c18001c2150405150407000200d6000c3c11140314081500c49440104c1910300b170f400341d000300000001e41444407040f484080090850900788400902034000c1403000d40b1480003440c850403000422034000200464025001694075400e2141187e00d403115803034600b4103200c2a1000d140d10340300002c00380014002c2c204071081c1c020424500861401d0040307000295240307c80801e801c024400826200300c621880010404035200280c4a15a61a0ba500e0103030081d4408a510034410081c038008215103a01c14402c1d00e20480f4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 608628237 1250 608626987 608627027
    0x409021f05180a18020306030a0f061506021b120f0609150a021804020703140d140901020301260a0803010b0a110604110f0a1d040312050c0426070f090c 67
    0x1044d0410786000c0c0d84028001034051140e4501b08001a0725213103240f4001e03009810010320340507948803d8032100c449034003060441d0b01522084581d204840d00320102d0080484e45c2c94401e80c0803000300d90416444240342d4000d800741c401001035101001c83e60b45115058420920003a0340c03080002c1c0100c1c05072040e19002c0f1016240307001e606041c254001c0a109000c0c0c100303c0221a10082060081c2c1d0002c500c595406440e55600711101d0386901043e50040502d01c000d506560400443c0c041c510440d0440781034401120320005e81c00350050040c41c1109411980140e41d940c2c4030200401c050340a03a5001000604040f1204041000824030034040c690060700d807020b404041081244541e46c41c8040c6511a0600c50b000900404810301c0e80da41100302c902d541c225140c242000380040c40c648440030096814902081100744c550412141947d03140c400d983c0c02c0c03540c0c800e205006c0d071810130b00007246841560804141c1449618080c2c0480d030658500f4032610325048030444001703d1801c4a054860 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 608629487 1250 608628237 608628269
    0x70c03080103060b01020a051e070b031603230f150d0314090103020d181421030a06231002010606140a020a02030601170606011b020409021f05180a 65
    0x743e0345400c003c070413580510459900c0005a261682000100ca0f4507035284d89407400021840c0c41d00b44420801491a0001c003411403038010b4107150089001c0c2c0c409020180d41e0320300c120300c140882e5546000c00f401109540c500d440c3c001d031b0506542a059581101240218010000c64907000000c1051243e060742c448140c0340032071007050300070340148507000d040c5a000d1000520481c50340c0304404040595100d0a1070096041c00c028000e0fa410740d0440700aa041460201c03e042681b901001210000d02aa1603480c0d03036548600c0d005140d01c0d0016101c04001c102c09074064100e2600c0c0350060f0000f1581c400101d1890403050f0700300c0e01c1602c42c0e04041528804002201c005040150045a03914010b81c0d100103ea9400641401000d0b0082055040d1070043c291141030b00b0800e86910800a007064240503443c2c00d802850401100d80092140303465199503400c42d101c101003010b28258201503c8289024014050095041801e21b05c00c0105c00342c01090803454180321010450b000743c04031800b03903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 608630737 1250 608629487 608629493
    0xb09060f09101a04141f0c02010c080301081c02010225150c0f090f0b1b010621020310270804050a06052101230d080a030b09070c03080103 61
    0x5038000c1560756201d41524000901c8180080a9000441d2a4030030550304d03810400401051015641060f01614100c6104d159002a105141c03207160760901740340c0c1503660944012207902412601c014941000440001201140014001440c0c4450160801410a81507080f800c0f40140f11040750701c03041c171000c400d62421170004410052402050740048003a08202e0780f400742c40d201c0075410002010040d85a1210b41d100088501400c000d0110011071032901d000c00c0510700400c0c104042e103410125003513643e00800d5000c14020103120345040c240780c0d240d1010708200175400d10185e0207809140b0f429100e84401d84540b11040d507501d406c00303180d80c190b00380c4041c4400001c0c0c003c80d00c0c40c400304404100380d91502003020003841203548480da21154510107403c2255040c16600800c6407002c010b121a01c80c08090983d0006210a0441070800768000250f6400c040307180a0f00e980c01c00030f400000e03140d040d040019884001d90743e0038140c1e01d4400b0100c4d000d94400c0805000264048018400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 608631987 1250 608630737 608630749
    0x207030f080c181c030e10020f0c0405271e1515060706110d0c030b0f060f0d060e010504060e01080c1903120c0b150a030b06010c2003010b09060f 64
    0x200501c00392842075120b0f100440350340211000001a404506ca4034000d105601e44600c405a00c0c024500c0603014886441880d541c0c1d92a00c0e04c0303194862034403000010349141c1d0401c80b1500c070f0382c2030040003040d001c4a021240d4a48407103100d603020342201c92000269154001655900980c00b507084c2e15980c0d510740034503071041d200b41490554090801c0001101242050045c1c20312440060000366540c100940c40404075090715170480145418120042d03502d0340ca00c0301c041e50318541a11040e550f40f21a030480ca24030701c5004000500b607841d10402094080b2402c100c54180c800a541c1008410303154011401d5031070007445520000da100d20140e03107050426003290003100e01398070f041c00b40e400c3e00ea40d24040205850001c800008002c03000e0070040c0311208990300d400c00d403080080306d052006140801c115010f5800003034865210301021900903403013440e2001120390859080584e00070318280d8090300214001c9114440d40c20301010b103d81d03203401428507004801c01004560040551018450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 608633093 1106 608631987 608632027
    0x30f030b010309020919060807090608072103050c1908091011101e090807150510050904060609020f12090319080c07050706030207030f080c 62
    0x158132801d400315008401700401d4486d0002402c1c800c00a80825408101d951140010000d01c840761742d803000b810341d01c1e40c030f040c0c1e928140ea411001d480280340080a14840101a1500f800203004900403c3d0010032002030302d40203005034012400181120302d058030301c043c00217070b1485545001950704000d00001c2c28a002e0200580d4010f541c0c40c4040764a00001d19a64a00c5201c2044043d0340c21691000d901d40601c00c051031032030446c0b00c9400c41c000482e03802140016620b602c001a0080b0343c4903e40c5810b065171014900010800c0c1c0c0c060141c410346085c1c0e40c0c0c0001013030440d0035000814940c5101a07045545003c405103e01940300014040403c64000f404101d0120745020f02d400904000307032428465584411424852034031407031100030000e00c00c816002400c17942540250402c54001d03110710000b5080c8400c141e540c1201115200441181000110040d41c2c2c0003450707203 = true := by decide +kernel

theorem cover : BRFrame.Cov 608453237 608633093 := by
  have h0 := BRFrame.cov_init 608453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 608453237 ≤ n) (h2 : n < 608633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
