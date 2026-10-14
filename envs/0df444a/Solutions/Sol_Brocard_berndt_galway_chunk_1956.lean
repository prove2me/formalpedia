-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1956
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:17:31.691223+00:00
-- url     : https://prove2.me/submissions/13cf7fa9-5285-4e75-8f14-27630e32f399

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 351618705 ≤ n < 351798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 351619955 1250 351618705 351618713
    0x504051903121404181e020903070308072102030c060a1107081c020a26070e0613050d03050c0c0a03080a0509030c12070509070306080706051c050a15050d 68
    0xc1c841c0650082c10120a00d0402d0305503c0018025500a4030841c0340313500f44d4611284081e00b00ca85084030414003440802d910028250981c4940780aa541580c8040d80c20400581d0401c01042d20324040d4001905001c038125500c00b160380070916120050b40045030b101a085801e01c600d40c1c109002c48400c101c40c0c1103000100c041801083c0011307180c24804110300301e00c2c2490345a690301c1c00d1b0703560808650750941801302070001003007007425911040216070929140e25032101c5080c0108465128040040354610030003049902486a01440d0a110340c00043e181d180d051940e03960310301c6603c0c0c06494a0b03175100038170310f00740e902d9502c00c0c030682601c042000894500c01c00c0b50300b008003c0c50159a20030400700440e14043c184003500e0b41019540044020490000c982e04068500032681d5440c036880b44007040381a203003280280740e020341100750200100d6029000410f41e07403130310130380f0403016550f0400c0280807a40c044070f4002c0304540f5000500d4601c0c07401c040007806484120b40c1c144800e0f0b400d0301c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 351621205 1250 351619955 351619973
    0xa03090302060f1614070902030c2a1203040209060103090308070509010903020306010810151505070c0320130213051c0b100501020c0a0806060f06190504051903 71
    0x200103801035038005098040c00385034008882c00b0344981803d43c81da10a06103045e00340203000d403111402c20f000d02680400c00c1c0307105000b101d01a600c0d8024081c1040484448900d095645107510b1540010b400d41c100007954003031018142410426101135201d00c0c00b8014401d166200418460400d0b26000301c00700026000b000ca1900940285001500e4546c00380c0181c8100ac01d5820181d41441607400010341e009000800c0b03165000c18170006c3c4505a031b106003411440c5100d001c0e003a1344010f0040180c00403442071000e003010a0240348503004040c0e480c1c6400d0315031040c0c403400781c0b03100c501342140d04141c1c2001c00160b9801c81e001c0c40b04510f0916661842c007849900f138054039119a00301d0042c030000046c00790f1200c441c5a0840303211042803e04c8044905c0c02100f0f480380a026000360340e2804058034111942204440c1d241018090aa6070101040078040355040302541c415018004613211050080c00712042d04085e460b020b03500c5040100b000b1010410200c07100c400d40d101d003020301c00036030700c1c82c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 351622455 1250 351621205 351621209
    0x160914190f0e010e060412090f0618171506091306050c0705030f0c010e0c010c03050a0915030603060501050f0315070e03010507031e0911190503060f07110a0309 71
    0x4100040d01e180031451000c064500300e10000002c3d82407072040c104100003c1001c9000303500c03c003101d0b6610b20302d0070002d640241d4207200c5d1071006000f4000c1088840e0007407a44843c1810f062906020458586584894a55140e0b04a104036806400203119103070740481c44a4102c0b00449105c2000d01d01802311550301c0c000404000d02d6aa150000315040c081118103445c0102d5000b4162619556115020803094004018101d425030074075114041117540803030005c411481c180e42d01103895015483c1501c81e40d10103009507042041c100400160140780f0508202690201da80c0483c40307528500700701040e2081030304003901c1801f203403052160a0380d000401082012041411005543d075075601903a07488600c0b42c500c1e4040d42802c3c10400040c2c0e06074450794040707801c0440d80f002007052071003040407501612001400b803070b03c0c840300707207494542034100440259070304226295454a41c004642030807000c2c0d6011840142e51002c0c480c1103500002274110182ca140004d210b0300c40c1e81e8400a00c0c0c81114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 351623705 1250 351622455 351622501
    0x30d08160e01021006090e100c020c1017010303020105070306084204050105061201020705150c090303070b0a0b06070503040e150418050111070201080c0912160914 72
    0x20700340c00c0164001d00881d5100c0003001001c0201c6640c0c1c02c2001d003d000c10043d401d03990b000c0c03985a4550114503100c3c901020031180e00525404a0100030b0048500c40f03088100305010402c00724035940211480301078080d41c0b0903030010401e0308041c10041c2c2903945a030440801a08000c08882d24205d003118000220021031010307404001030600440002185601182c0c40c00700920204001d010301508094000e103820740300541c5000307074280c002d8201d00902a00800b1130f0403003050340300500c150f03030b98040e0083c024003602c5241c14000b000081c6180c1c80741e441207503507910410070044650005c0c4078185003000d05940c013614285807a51007a449108501a00b1200001c000c00f241d1584000f580343c03141035201400070000d81e01002c030091030381e0080c001e048070190b00f40701b61032110300150403e4070300c404d50684404c44252590048180030350021800903402800303c900100c4102c10411482a0840b42c0e54006064141042040b03002c3d07503164026034804160700428082001d0007507034400d01078039003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 351624955 1250 351623705 351623717
    0x5030a0803070e0909070302010f2109140d0e040b100c060f09021003020909060103061202011b0f0c080d020703030806091302100f0905030706020c10031b050405030d0816 75
    0x41c0d040300b51011803c92064036008511402003000385040080ca03001500d00076201c2c80358450300014101c0398100480c0c042d00015240c0b03105060b1840313494001c1070301184114644005480758001c42d61402e8040b008820024640e1400240541041c1c407400414020654487d1006d0902c10ba010301524418580141030641d58180c02c41c00040e2580321014140d4001d020903075a040c080b03c02000f0350402c1c15000d1117a480a808104150701900c2828220b4062181004042c0085c0e0015036804107442ca80800480e000b01c42e01002a042c4101d524056110f110081d040302d00745140301e440d020300c1e50089400d42d8800341041c004680c100401c594810007c84802c52140d460100020b14103440c110020740014040d100d500c42190060320300a070140c180c0e501c0c0c60711203030764008155441c0b07003078030030100903810203e00700000341009031300f800203855542800324800401c05110301012140c001c0c0400000c13004901804a840d0500c8207007042031551800e407415040c540c075404c10a03800300e4045014082 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 351626205 1250 351624955 351624961
    0x11060406051c090503042606091c02010603061b1214040605150d030305090c043b0a060b010e030c0a0b09030f0f010c0f02030a090603180501022101090605030a0803 72
    0x42c1d540022003460703804000e0380d4407255580b03610b4200444202c04602c081005031103100e000d44000a0346e0348580d10080c004c1060030b0901081200e0400e165101c41300b1035494880120100349240143d030b20208810219410781c0000c1900100548008021140d0040c00d1541c4180190800401940c100c3c0e080714002410761545803c0c0050458400c20598210400c0e1a60b2002d242d01584131512424030081a145115150b0b82004110b44007001c0c040c01d00340881c80d51a66800c03241225262010054a525400883ca40e00c03040c41d101024800700c0320641c03034200d80c032115603001007200d404500540050101c0f0300da00c4c000030400700309030081c0701404401003641111503504001000e4840594000e40f20a2003d22203024042c140c41d440340c10100718100d00c4420841d02c00070440b60b491040e55911000f00d820030004801400e40500030755032910711030401d5004903200b84020001c1401014a01c40c603100d41030314a0f82c40c640e05070b00c0303000761034a0701c2001c0106417404640d210169a000840c16039a83d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 351627455 1250 351626205 351626257
    0xa03080c0d090609050c03060702070e04080c011e0501090b01030902030a0b090c06070317100f140307030204020c0312010807050109050d061b02030706110325091e031106040605 78
    0x1202c420090107450800d012042071100101c3d00d04075468082e4199074250b0346d9200e007607941760107030f00c924044120403800141c04101d50314080c0c06480513000c008514400c444a44031840c0f8450792039032148517a100c0042005145c50b12610515041c00c0c03c040c00398644580009846240750b204c050805042000043d41051061141c403138001d100508550f100c01c21800d006025099019840e850001050f001c01c1c414818804030104545058500035000c508046070840315000302214142c16201e862170100061780d450000d0010403019500a6449100302144440c1d54041a445491143c006003001d001590f4051a08425203905440b046407d60140c43c0c17400007444038400603902a900061410149980032004000b0359001d21414001b000454800c1c465a2200391061900c80301ca4841c158000b001343c0410541840060806008040d503e0b004d800000c440b5030880e0403000e460100034001c12040100c4024081004c3d03966505113800c001c2c0142c5544242d81c0302da14036003564001c084003a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 351628705 1250 351627455 351627461
    0xf0a0903170901080a0b0a05010c1106030717071106070c080c01020f1c061d07030905070603020316050418020f04080d05070201030515090604050c040e0115020c030a03080c0d 77
    0x35984880340300c10342106803200440d00e0b0408003200d400140800c0100395006658010242e0300c401c02001030044500c1e10005459844440d9012500440700c1428204543d0300d44016601c10f070080c0e01d80c5a202c2d00040103428a41300010b08460600000d1080c90310602d0000980340c0e03200440b400c200b50440402d09224406e030240d500c6208030f0f51f000080301440130100740090b1482507032001f00c01c3c40c100854450364081c1d0b03a440c0902505241410308010f0345012841c855a081201401c0000b00c0700b2043d198581060400d40028011940000a0140300900c4403145810600c2c40e10b40306050608004088441010090880c0001d0342c01050060801d0201000c0310700603c1c1c907a00302e03018205504e00c00381060f0040702041e4042450440066400c0c0c0070000b00c402041e8004000c45125941e000811006040181c20540d43d4802400040b503002109416103018040b010301003034001260402c020b143c203001c1c01c1c0860081d003125043c0070000303810401e01e54001c40c42c030129540320004a9600002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 351629955 1250 351628705 351628709
    0xf0303070525080a050708060c040e151302031003030e0105040612020c070b0408060a0605040608100c020705031609231302040b0406090b0a08070b0f0c0c0a0e07030609090201050f0a09 81
    0xf841c0981400b4104008000a00da000c0f922070a00b03551290361040c002040c54011481801110000c03c2d00044c2105140e4a440054040040a03402c0c0b240c2400d0090040f0380080710507c00f80140c01c1002e0090542185c0d103c280340c002480c1c464546814024024100640004110300690300072414840318041401450042c08000003281d850f00c0d078400701d540e5104815181d2042003450044040b4160415010344001c3c2c454401c02420b0301d1610641080c000d0100d20402c600714040c50701d000c107a0780e03410b1003500603040b462075454484900f030072052412100c035258810303040910a81001d1400b00e11003026903000107030f041345800700c10581c00460060588036a005a000c1d20301031000c943c55040354040409820169040c0018a8455200c1a901c040340e00a0354001c00f41800301c54001c980600083c0315a00140c07055070030700c0a4820100d4034045040c0c00c01141c50146104200c4490350500c40c1c08000d010b1403070b0a1040f0f424a40028285104852030088008400140207081e80d000c1c0b081100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 351631205 1250 351629955 351629969
    0x50727030b103209060406210b130f0b13080307030f1a060319020903010207032c010806090a0b100f03060603150b090d0516050f0303070525 62
    0x118518182e10800c2d2956914061100ba00d80c655101c01900f01d10420888100010904040d5241070520100041600020403259100d0341300e010200d02124003240305e20305240703903408880340b04800d03142c00c0f040c00100514404990b10708500c00c8000c181586066100380d600a420900d4a85035418a1207c240d00b1780000b0709a800008244010a0b92540c0310010710001c2202c1000307203801c07104004003c2a07a05040365481003052005c90382d51161440700380c1000940304001031a01102802003401d81c1c000c002e040c1e010543c400094040400c0022342c400e440c030380c1d503c0c0c051250310030040003070000580074000038021815440000d8130b8100030b5010b4201100014120b0642801c0c2000003030904129081c00000282800000200580a4080e195680807503403034041e406801c0160070300d0302c0d030002c00c5080e0340039820f20640c2000c0780c03080c041c070f007a5245c0d1013181c0394000d0b04180501c0070310035045141078000d602c00c2010b08041030001c50ba50282241445d42481802200c000c010241c13811500842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 351632455 1250 351631205 351631223
    0x212070318120f1b030905040209040f06090b090108070b0414010512040f03030e15010504020d0b0d080c060c19111e060a060905091b0d06180302010e0105072703 71
    0x160055044010015520f40d2552101e071941100038090728403610a650040200380118414491460107401802074010080d100290401400d240d00381a100d06034000500e69584281c003400d2800c0c0010454054503070354001307081407032604a19208502c031301e1090035109003110444800f268413130f5080398800300c44019002c505060a0400581c24882424214007007442c15240304810b94010800802458207a40052507503031038181400080c0d40040c07100d445155540d202442265920320321355809074001e0304015150000184864a0100007400e2514065000c2c00f52104a162940040450713107030b603103000740c1c41841d4070800500d000706912200803215411859118155800540b41d485246513160912020303540702c142c03400f249d0b02513132280c00e60740040e200c191a0900194010083c100d02801c021055100c54840b074084034040b94081452040480154080c55424000c0d0391040108800801c20350401c0c1c00003801e800c20311070420228201030702043d9900c10008603400021500302c0896 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 351633705 1250 351632455 351632483
    0x120412030f14160206010614070c080105091e0312041b0b030112030801120b040318081f0f291206040f020a061e033b010f0212070318 59
    0x41d402d20b4044943c0040a007000340c8107024140700140e102d04030340035500c52002c10841c0d204000c2d50b55001d5203098408000d1444001a06503091103828811310a120103002038805006024480b0006212007001c030b6230041c41001c1070040354102c4560031640c484109100312000d40c2001c01100e51503440100700080c08400095810714110002e4441807281d81c446005030380342c00d40b500e5074200d80c800151a1406800008002a000d8070307000c450383c0f40115a040400f945d40c81d00b14036003041e51a89a10740100059580308d5098507002d16080040c07552000e010200c580400c40382e00042a089508807035100980d1500242c5800503941100f5038001c054034101e107005e0a140404800d2030b14124001e1008a500041c0c00d0301c51101043d580085808a413501080814201e000d41002c0c0031500700c6818002c50106100200443e4160102d44020b03124004d040d108403490031101100410f01d08240100b003803d80c0c1c100421440c5901c4081d038100014160070b4001a010158040440185403100740e42c42 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 351634955 1250 351633705 351633731
    0x20303040c0608060d123f02071a01080307061a030d140f071b1a07030c02040b100801080106050a050604051912080310090209010c0b04140304090e010b0105120412030f 74
    0x207c02030400804000210a9400d0401d6040b07402154002c10a500c071204440d220703240070b9030010011240120303518036480380c580d1810405001d080e40070f81620350000a82c0d41c10400c880c003950034195407072904d5002040305800480d03100c25400241000b0846503905a0380549910380030340b030303a070201032070440d4039541203280000000400b0707805454250b4070380790000741e0041092007130f50b00c2b500521260b0b0304108d0917940a84018010701822a802a10b07083c401c10780b9100c0b80d8041d800d202d0350faa41d03141c855240c04151030031214031384c10040c080d10712020244080c6c1c481e0000c6800300c42c0700703a80021082c516146544100302850704180880d41e00d47d40d07071400b8071160901450294000c0d501d200740050782e9006102c128894000e9490101c0e00907540c000104030a103075080d61007400396600c03a0000d040b104134a801e580c46a00400b91703840d03840e100c0b156901d002744146d16105800f0f00b4280c0c900f03400e24044411004004000500c00040c09400c608094400c1d00600040c2044036400e00080b010303006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 351636205 1250 351634955 351634967
    0x61908060615130603020414030c0120030f0a030c0e04051017071a040303110705211005070210050f04050a1205070215030114150301050105070f1b05030d020303040c0608060d12 78
    0x2241c01d0a00c40344200740c0e41079240112b04080341700e005855035030b121401256003010100c104030060046010038444038094400ca04002e001da0f06550754002010044c0c0c3e1400340510000722040340c0650724050800c0f800001c00315030b1806903001142c91038407901002608624007071031034000000b40b250340c01304104a04004000b510950f03209072643d018400030000e03132564032034007440341940c841d50a03c1e11603e4252003c0c001d1a0030f0f09050151038031164000004419207034290b440300d0040e8011803054581038403511549812407120b11032950541030503203425a44000d00300000d0700c0080701900442c20103028004803454103034041c041640c202102d01c08021076400910400c40e2030b2544403141a03062400c500007005282c24400804e0a40c1d00b018011240c50b04080d800725091210030062401080d03040040441c4190b001d00b40009890800d800e02d8204002d0b0850041036500c144203200006010900c1d240030b942003460b10070065a5600001410300c80008800351454201c000c504035075541c405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 351637455 1250 351636205 351636209
    0x30a14030310090506060f070204140f0105030106080604080f03130c031a01080307051e010207081206010e03280305070b18010506030c0d060c0302040810050619080606151306030204 80
    0xb0040e103203000d03a03805000c001e030380d412501650310070000c004c0c4c0a80110800054034601e40080c0000848603400c4a01040d5503030103a4280c05401c00a1004022600e02409000003800084000d404641415500c40c0d0f903070b014900d12014148000b0001491000c800c0d0030001250740c10030404030f0115074a040c600d541100c80214404014034007030001c04c0c030840000072110000c2d440b1004200303611980080c0581c015010b10b10003420354082100b4008196200b02070881078294030182c241604043c0005080000f000c04514066005100d04003080c00e01e04111703040201e00500420703001d175442e01c7c0880700c510031514001c01f2080c05806100b106800c078900d00c0d80d00000c82000304400c0c0c44034820146d4400d6400602c13035200200c1004180001c140c2c0e0400e1100d10158100903040603200c80302c40e818800014881d8048907691700c01c101c0d01d0300d410b4402d011001c8071145265000b07820010140d88865000788814060079040c8250804a00c400040340d11100f05800024402500e444008003e0341c0f1034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 351638705 1250 351637455 351637471
    0x301090503070308100f0602060406090320010e150123130504030c06051008030703030b03030c01060314100b0d11121e0705060c07170709060b04170c090c09030a140303 74
    0x130310010400c20011041d0505888442e0024449da035070720396511f4050b08255500f14104514034500340341ca900300790a80800510b0fa40008503107020600026454400d140700d010103038035142e500400843c607081c0700b4003200d02210b10000380904500e10101304004030480c0d00c20722581c503103410081450781c07003268070001c42d10400c010311403030b00e078a11305081d00d1006010710503140c0c0040092000207400b9901254143c50060250390914081001c00c500b10b45403039000341c40b52020115420a425810b10180002450b8482c0800c81940040c002c43c07801170032060000c0019250451080b00d50b0f0794151400640712444040ba4044084488101c0101c2000c4480414500c9110b00109080c82c0480603a03242c1c071401c000401015241450760340f4001500c5440203140c0c010b071030010030034450600880014003031010895649030301c0c0c0300048a541002e40b905054507000110b2941841d910101c0f026041503d8016454481d098000001e007055504400282100040c0300785d10910800800070314428608 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 351639955 1250 351638705 351638731
    0xc0d0801210b0604090314040602150a060f090504021908071d13060504031202030a05010e07020f0d0e0a0503100501031a1506211302031b0603010b090301090503070308 74
    0x1101c000040d08103500c1c000740010061800a540c0d0b0805a1100ca5024001e2501d10010300801c0c0d0030660541c4150000300058001d003252031509030188040340c1d0040140c5c5420086945042d035080711441c1180100c024482c0c40300c0c0498155611102500905030100f905851403950354001e0542d00c1059206803030030341000c038005900b00001032044503c108020011072200c0f45081d5290001810003e104a00748004101c01e1101c3c0d000074805140319040c00c41001aa03941010301020001c0c00003030000c421540045850380074640c02040503401c045603820150074180301900050100e0445400c5a17806104032030800700146107940126040301d0042884414400e403a194800c01080100c0780c840b00801c03490b68002c41ca0030107400800c0780c4100c040c4030010005014155400c520002d49401110700c02a001c050151301d02800b0450100c410000c145607440c02c66000b00c1c0361400144180e551910011a800c046a10203400040d11141d00405030b27507440c4103034030b800b501d02c6505482d11111418 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 351641205 1250 351639955 351639989
    0x1308010c030921030905061f122006040503190219050a120503070209090c010e0105191b0c030b07080a02040501051c0905010c11010e121606020c0d0801 67
    0x20192184070384460f0040003031100b941107524501e424840c80d1404408040d5280110070100b603043c0300d554090740f886100c500000e00405240c84150341140c000010f170384a0704001c0720000f42d07000d0440318808914030b040030510040b080007425502031503004a8250256082c1564008005480c0e200580d10031240300002003202c100c81d0058201070b0003440d8012010b80404d010035005450f030000441c1c401e000f01e83ca05001503021030050001910110842d91100080d644650b8001c80300d00341c40002881c0081c00d0101105000940421100b00310060000c0082c0d2045a1007441680d1902c49801024500311260b8918003001c0f1441c00310b691100298021000c07034000c02d06030003100c1c2180c0050b580c4030f040c40b429004e1143d80d6040e50074a000d40554826140d4001042030042850b2080d0710703212030b02c1c0080e604280a007564084003408805d07400190f6440341c44020101030f02d1405500401621030080d141c90440020f00c6403028030041c9104d01050301c5000d0754004891030680301d041d40700240d80c00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 351642455 1250 351641205 351641207
    0xf04110c01090c091a011d041a1011071203050403122f07030206030a1d01060503010c26090304030c09050412020a0c140f0604080102070c1d04020607060608031308010c 74
    0x5260407110300c1445c10790b000726060030743c81001800941c80f800c03031100d51389056500002e41200c0000010b05800485a01d01000c01c0c58001e500b003501240381d08240482013044e40e0707829140c030700a000e0f0704100725042010301c00741803150040d18040c0d980601654051001c5501c003030b0140800b4507100600c403000c1000006480d0b1002480411812a140140030032402d43d420000507420040c41d4441032641d407040480032a1224800388500d100107400000e40b5400c2034241425901c3c001d00b00070502046491090104c08501c4d076080783e0032040c0440c0191030300c42d42012030551146a00140840441c5d00001c92210b9650f407000d400307240f1483d05031454100c941c2069854541403403020b81500301450003004080345d005110003074000020200d450800b0a400000c0d4030350042e802204443e0340c0441c4180402c203882218602070a48260100155488040d0001d00100c0052009004503404210201001131303980218024201d804185c1e9143c1032020480762403400d20340f08003400e541c00c02d0301d141402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 351643705 1250 351642455 351642461
    0x204080d14040e06060903010c08010306180209040b090309190e01060807020d0f0e060a0315050f030d050c070e040f02010f09080712020609040c0c06150608060f04110c01090c09 78
    0xe01e9041094a091600c1c04a1040310f11400611003130701300e0340821018440350b03428800e040f400540354448002c99411400c0c11030894103282030111801c9440821000560398210419501c941d00007100c400c56990015400d0441c09144045a00100d0b4480000c0f94111503d810005658070300c0791203540c680c6d959a00b101c1501003a60404003681007030110307002880c81882c44c54007070b007018242000706076407103804214176501c250002c0c00020f40c3d60a21049500d011700f2240000c01c82100d0540040c075003400002d458041208036001445000035010107220428003400004205801e52210a490070307040070313200c0e202215422030004440310025049180280240c00a48060740f00074908039017480340c01407550b600c03aa402da03030000f0103001a00300c0d641d440c0103401c0c6402e481d594002d8041158a040401e075071807604c001c0c1c51407402645c280010b40d40450b0041d0300c03007402c6840c1411502200c000c900208000401e51080d90000a410845494150800b40c1c0300c6128a20504509998020754021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 351644955 1250 351643705 351643727
    0x12010e0c0a050d0506030f060a02041a21130506010b070302060601090e1612020a090503100e030a030203190504051b0102010504080304030f170130030818010e0f010204080d 76
    0x800c4050204040d03d039000e5002961106000d8110b4003c0d503a020f5a051802ca82160816941d9800040501084100c28400c400100e59118542d0234912342507103003640558003002160b003043d00103000400e000d0300c09000c0c001564200382500c4007544c44011103800d0303900411040c0d000d449840040f80803948030b0441d4004a0780f655900040c0b94603407140d842030f1118440b4040081110300718001900f000c00741700a0803000459210140c0e80c03444c2c907040c507080c408106408200c030351804c081c01c034241801204071030350fa48287c0340041e0390303543d44031144401b9508115003c41c01880c05081004002d00002d0683c408200030080e58a561108030049090320070880c0d00030503441081c404100041e02a40e007059405c291030a04c000d07449510848070a0a920981c031550259000b40d400410303104031000740c6500360210161084440185031809400100040c1c403074420a800700c2c0c030882c3c07066400c3d407290b45510030a005032080408071040d9603000c0e400a0040034072034091560300110aa01408102407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 351646205 1250 351644955 351644957
    0x1e0c03030614180601050708030906010501021203010605120a0f09030206070e03160306021b12091e03060403141e03150301060e19110703110714060708090d0812010e0c0a 75
    0x2c1c000480f103521003a00c10020b032209051100500585000a150302c0245118050b000018081d03989084002450941c08041426140c980ac00060021940c032404640180318920051030441d2580d68044004041d065100c0d07030002d150030154010140e01051250081c004c955450030300245040815445004078601103402d41260707401000040d6044c1c01400181c0301e940282c4000c50782d50840705040c9201c990841165420000710009181780c135007a05d8680240004841b900180c4240c080f964134600504080c040c44000c9019541100d007090444105070b44070040011001d1140d40b10702c103d81c105840e0300900c2d15640380e030118207040c144150b0b0115401d0346c01c5240713031b030b102c680104800b03400a1030201e90654a41c1e01458440c0030200c000e01503c1c1c0710395222122013540042181c140b411a40100121010f80c9603207100700c1d6a0642510f507065000043c1c0b540c0c60680030001090030f41c0c0c6040041901c0d2010519255110076600300a04985100f00c0151040d40c50303100b0010342c1e1080303001e000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 351647455 1250 351646205 351646219
    0xa200301260c2206030602040b04061106040b22061107050c09040c051909020403030f030b0a080d050c0304050a151b030c060507050c15100b040b07121e0c03030614 72
    0x1440c440025455080f01c03075004040081d4840d200c0d11400241d90007034020407080600000d040050700d13071104c1d4100b1452041d00107008e00d820540e84400810030050100010017032106150406451051078000c64194015000c1241c15280e01082510341c102e40b00507101c1d802801015201810720700491481542d104000c4e04006003088200304c00c10002d0500180300d000641400300da40a503070303c000d00256010f0707265582485049880101516034900c10940940b00c5080200400703c00040c10700c02d01c00c1e00741080b035142c800604140307241d03020b5503101c654440d106580001e00454100c028000d16180340d80c688038030083c40d940c1c00d8420500c071500280000d0be0f1075480340204115600240e0070100a1820500d0003181e02c01091a1050030400c80a440f507204041c090000844801017004001002c032150a0601d41810700106005680000d0300d1017001c14200890780d403294094813038101001d51840c8428442640040100316075540840100340741103004075003030725241131407024038900a00748 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 351648705 1250 351647455 351647479
    0xf01110a0501332c0c030a0f0216080a02030c060423030a09030f1a0a140105030706080a0c031103040309180204080c122119170a200301260c 62
    0x24594141a84c84080d01d460391101c0340d54000d41c103035070807140210122024030340c9909060510310110384515040800e0306104101c00c00540c0c1c0310407030b00303060290841e0040e40c5955465800740e00354851050b01180741d01902042004200e42c1c00c0c0d43c880700c610007002d1080c4d480c03000b891035a624440c00314040c8c0866140325040001038000180c02100341e10841d821070113644030904001c003200050b500c001b05282c4400003050f8440840016600511003100204200c81c980341014044850140140e40d0359500c175442e98072500d000303030441a020a4850350703043d03582c5490f0800900860103400f4500203551704804c010840941c0b4000e44055440007405401d406800d00c080180c9030304141041c3d501d40c010031021504101958811034040c203d001c0c0c415680d40e5004540b409804024403c00003407240c1181ca030002990710b030300b00b04d030702c0f90002c400090602c1c1c070704143c9a2140c50140942440201c0000080703900089054242e00c03410000c8502211044150b42c135580700c0c00c0103c19150010044582 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 351649955 1250 351648705 351648719
    0x20a0b0402060d020f0306010314061302030c210403030e0703170c0c04021c0e0106060801050618090a0b010e030a122d09081908090f01110a050133 65
    0x264a8100744000c0400d072405005104100a0f80c11000940702003041c080100300301560180207404000e42100c2400c1001d00d400e40c0001c0e1000c459034200c4201c940c1c0400010a8240407900301d0303680408a2541c81481000c080d6240c262520486007200064100040341420b031900203000001daa6000400d0002080c61000380c110640041c0040042413080854036546a150362000703090030100c1441c3e6406410008205500795446882c00c800680e02d404010004a90321503040c1e81518811106c0d0f560b01d2540040c0180511074041c1926404035041e420701114188592198501c050280c03200d040e0510302004058880c3c000007405403105801c614820101c5200340504542d03040301c181480d5500300448072089540310104038002c0406d0703840b8002e0054082c00c0050030100701c2054800b080280c0b4503514180d040c0034158455000d50405100c9034841d80c080c1c0c14000c400780340c0100300c403201d0099086c068060106400300102d102c03602081454030003580c02d2015000b591200c450701c3ca45280c050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 351651205 1250 351649955 351649973
    0x3020a0206070f0c0b0d060f08030f0c070e01120b06030307051c11190302060c210c090603160f030b360721021c050a0e03130915030201020a 62
    0x3243c5050b0001c0b0800002603118030100e02502d15840300c2c6403605103901100c1c04444640d00300c000150542c92080002c0d020001c103ca041c003001441c00c1e078031200e004901038a00101c50f0010507500059400101c3c50742c11180d40b031078200340a0a12403000751190b2052586030310841b03c0103801d90300002803a0300b060100640103d02c030402480c00308c1c001c1c201c90180a04003444440444800d03451a0802004d040c0e0400c0055044611815014508910386410380e087e81501e80044000342c024000040c111592002944c07048030b40a040c0701d03900c0c0b4244007a900345c0307a0301d1881c0d031002c9002004480641480703031041c0058400003802038421b030704c4e83d80100910020310b024141291450b400c0040d41c1b0407420084c082c090f010a071110100c40c4107080c201d2040a000b240d811007000d00c1030040c2d04207420302e01f4180c4180c2c05407600025081e00e46051800191107109800d6403180300014024180c6410f0a0f140e9040358104d04040240b0380d1641407456010440707100280c0141c1c02a400302d00815007240d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 351652455 1250 351651205 351651217
    0xc0b040311120d150f0509130512070f0506011a0d11070218100605030708040b0a150b2101030c0302060d0f0507030902010210060e1807051e1203030403020a0206 71
    0x10444041c0ba107110602603040e40100e1860750301c142c5a120816245400c0e42c101c0700a84140c88003c01040d003072002081105000030f000b000c00c5940c100e252424810700340310810b0b581c9548803134540e8a603128200345013601400c8108544078892080001446804101e901710b500458007040762801200c1c00e450009040c03040c01c20320a014003045074500580c3c0d6800ca041c00e001c003003c107070300d810700e03052040310302080c425030000b014000200100414254800c12003030780302c0d5000c0d42e004003544450042c10000c10089008820f031030101c0c007001c5007030fa071503001400d04010f210002c01b8401030320a00000e1418820f11000f000180c0e07403002400149481d5024241216144030005400310348103c04600f5901e040d1607600c04650349111000035540d0502000011500101040c80003501d004520a02131100034070210098a285025103d04d040a00c112802014000c1040610040d8121141200201e0b5000c10740308040107500d0144825010090701d21840e0981c01401c0c100446400340401d0354004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 351653705 1250 351652455 351652487
    0xc0203070f150206060109050d03020309030a0b0f0a09050a0303051e0906091605030d0f05130f030311030a09061b0203160602071211060306180f0a0f09020901141908060702010c0c0b0403 82
    0xe0014205c0303600c041010fc01503034015510107030107082140c8688410b001c0034111100650904d01c41d00007003800062590300b410f40c180341c001000d9407801d8081e140140340c2004880040c100609120f060980044c400d80691681c3e01566161189c280d20320301c00c0d02d0300e8881c0c16011b0b0484001090098010760b10860321288c6401d044d40760114020f40b03c905a142a0815000700c20301120074410305500c0206d07038040d221040000c5107442081c1300040c00d1000b0714841c507001c0001180642c041030340001c882006099024003254078142c0f900d505600300044d14056103005100d6510001600303502c125101d84440e80002650803042070800074400c1c2640014403094020032030700150707007001e1030a07129240b242140d056085441d091107080b0000303503001340141030820344c184005203025a0300d5901880c11144106689455031400e400071404408203006100310505200d0000120503a0100c4c246118941682c001c110b8030b00e03111416680c40d600e410b005040c0742210000140024054a5510088191 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 351654955 1250 351653705 351653707
    0x2150d020f0403050d020c01091215180f12020303060d03050a0c021503100501090f05040b04112206090b0316090e1003111c120c0203070f150206060109050d030203 72
    0x1d810074001c600c1d441a03000710340d42d91106420640f40e50341806001944042460110700e15441c09420940304846048003508480c940c400c05005191141e104060180c0007500c4501d0444250030828504666400700fa54558150800f1100d8a8404012a840b411000740b1111404541da2021602038001c064480b0501c008403001001584e40d04940c07900042440842581d01d1030300000705460b074080c90348054140b0210420a01017205020078401c11f640341030b100007645008150004000d0100f81090098040001030080d0380c41d6258040c070b4084115042c1c00740840e560300c0008072031310a100d104a140f1100c00b031010407101095101d2564100000d0700c0d110520b161251440c1c41800c44c00e90b908400c15581d84020020041103201111003a2030841e10008447c010900340200d80801c118010002260300b407002c5030b81da0107000303000740c8580c01038110380c0c0c80c42e12801c101d1383d0040c245c00303055800714007e42e0032042c292002444e14494681a5255204d803840c050500c000c1c000040012000c0d800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 351656205 1250 351654955 351654967
    0x10c0f06090803040804031b030201120c0c062c06132306190606090b0301060503060a09020307211803081003080d0b12070f030b0a06080f0606030106050d02150d02 72
    0x40d00005035000750301800c44103a0b079925520f0281800230340019000901c1400030010005030781c03c5042c008a19001c00008a0240c2443d14200d40e25003d0000041c41e2500c0c121511441e25801040c8020107407540c0700543c01001a224070380e6803043e00f101d400c550b01c00004140000a0603005c41c4200c0051800a0119400b8030710703110504000c0c044906080341e2a031902d82c0700750318490740100d100402650074412080d80c01d2061070042880140212003c0c00000001300e403e0745c54142d00c02000300306010b000c545a0800030401020054200c80c03141980f03148507030844001d2614450324000200306d1102102a416503542620300d010020140000000501000800f054041000b0468403410150000c4c0b003c00c21801c0100900c0310280075405903201300070510112070784d001e600d804c0d03e802c440d0a100b155980e8050038044c040d950004203c80c000c40d9040d003000c4000041e01802428100c000380081900da00c00c2c840c03000103103d4060b600007034010110011062040041810110000000d07217004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 351657455 1250 351656205 351656213
    0xf07080c0a0b0901061d04080903120a030c0206010e130b04110307080a0203070602060108061504151206050c0f0a080a021b03121605040302040b0d120302090f0906010c0f0609 77
    0x701030905682d020081420400c06000030311400e0041d008451080b10580701d41d010032984402c00400013440a00c000480350748a9400304a003a809528000315030703940b01051705008001d0450074414001501c210b400104141051711500e610951000703ca03127a070744c507898943c010b1007200071304282c40d00020f55600c2071164a060200102a0000d2802418040001d2040c9450b1a400780e01c02c0301117404c0ba6006212100002c1100c03900079142c080020b451150324400140240012035104508070341b90100029682800386841002d28042d200802c4076543d555039607a268480d0300d20551500c0020010383c44070318000d416542c1c02107402a07005040868028180074000e2528071000701551010640c907041c0c03040044c2084c0c0c0010074034500d030103400301e2a2000c3e215000d40d010081c802e50b01c492000880c0c2d194810701401c003540214480310f24211000c00900250b111401c41c1c0d014811800c03030807a4904044000601906041e914150600101c0c0c51710092003200c03c400311000e0f0f8031400e0f000085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 351658705 1250 351657455 351657463
    0x110d0204050a090302070e040305030615090402040311010f02010605100f11060c03190c0c0311011b0f1701180915110d05071107030201051803011d070501050f0f07080c 74
    0x120b40110000440048504003c1c0c07418616910070745980c01c2210402c03000a6120055039000b074810303640585640e070703c5020700400340038540c4000d40140c804075001080c84030040f0007400c820001c1c0c0310a0065040b140b0200e099078800d0090f103810200f00381d80c0850b41c030300c40e9a0300c030740d4006146441d543d45203c0c00006402c2001c1654005031445012050041c050250b184411410000c07180806c81e00a00c048003602503854000c0182c213001e07028025a400540039009007480f4468654100c104070a40200030b03140c03021a000c2800040c0503488440c5100036004c3ca468165000d9404000e1294a50502c0c00081c2c4062803007203071260904010740a0b10784840c003a0003600c850040025840f003104281d03550071602c00a04131420801480300041c10100d0100b000350a890b020701c0c0c01541c41d2680801e103c02d0720300841549405619001c6a40034031a515410340003400061030607155640d94410044484d4040c540e014150b10000300101542061101c00901030341d0b2080550303a05002d0100501d60034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 351659955 1250 351658705 351658711
    0x10521150d0b041101090e0604020f09121506040608100b060f0a030b092d060105040f030f0b07030e03161b0e061207081b030f06160216050607110d020405 68
    0x10b5200010b0108110110300d200312000c4080c0b800078000c0380340c9445124580009010a4003036136002990b0f40100343c4c181c0c200e4010f01c0f406030880d40c1d00f103040141150b03100080b050380307041c1c0c01440010901c81c0c54113004032400c9850b4070000304903052a205e0f04400420050211f00c0d804442004824410408100600360788422510002107611241d000e000b48448010110402c110254400a11804801c5881340c000c1c541c41150015039591a001a00c07180705a810011019001d81000402c0158070024185890310501d6200602c0d01c030504154250340c0400901d4040b50070a0000d8041180c3c42c8800c120228000e08841d802c81e1441001c041c4511001d401c0100e8140850041141e541040119012103942303400050100c1d518190741d440d04d9200241010f4107500e5055402c11203942c0811400700e100e1106410b0b98200d041145080c19040403107015400503024100c24003030a6141b40d210201290b00103400289000c0481d65102481c10503016900e40c03180aa108142c0961201d1141030701c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 351661205 1250 351659955 351659963
    0xc070f050c01300e0c0a0611070902090108010b03060a0807260c01080103030804030c0b010b0304030219030f05070c051513060c1707060f05010603020405010207080309061e04090f1406010521150d 86
    0x480703010300301a40e040003407940241036038a004028cc50351699101d4007036411a1b0400164135202c0d00c4c3d202c0060b410031141e03030140090b882151804030309085800000750a80901c8244a0b102046c03200045071600000c0005030b000c1101e46e001000824050143e060f4084c0c840e25200010081582d20324a0031502a00001c2c6140c2d03010040100301a0104203d0400c6014047da02d000200582d42c01084d100c0e540764004c040100203e025010401910404406494014000d5030702c43c0c00040350b84050781110b024481c00c0c113100c0100080c3c49004100c2050301c41d8004822540802050200c210b15034010300d0300b120242e66401400281e10802c1c49054060911a54050703551840c0c000020720b000d4031900310050b250003c2201641e030741e4070003080b11103000b070204410001d80c1e20565200172074007899100840031801c1901480b00c075299036210640c030740e0b985859004140c441d0001140c0e1405038a5161100452940205924203946075805030300215880c03900b80b459450b00d01042e01d0b0002e080c8111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 351662455 1250 351661205 351661217
    0x32d01060810090e0c060a140f0315060408070b07080c0a0c090c0201020a021009020d15050105040f18020d0c0f0f0e010801150e0c070f050c01300e0c0a06 68
    0x12000d0340c02c44041900030315810f00c041c440001c031607406584a48a20100c0c41c46001c001a914040c2401100500c0112415000b101d448200e83ca90341201030388203c03044c3d1405686000003001c00e00c0c1c0081514180d0360103000601106081081c0a819540036030410b45002d0701c240807401021a0070061114658410414031a40c1c618140904040d128040001070035640103109501d0031a600241003141100700d01404512181c2c1400031880045281c5809044011082c01844144009401c168100c0d00c0c140d4041203000c505003007642c00c460aa109000d50060401e840e14098604a0300e8004c002d8064072140364a1540c0390300b8030071002001d51010b5180c1180d0b907810400c2c50b98690f18a401005000c00074800d0300c90b900c114a2800c0000d0085500911001012440c44003051003901e40c0194841c00c4030402910380d05049545419403800140090003800c1010720302caa1002c0035101400d00d00300e90900409402c4010000f605080301e99090a1240305c02300c2041340d540c02484001400c0e652519 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 351663705 1250 351662455 351662461
    0x403030c0602030411100e040b0102030c0a0305130815190504020d02060705010615020a020307080a03020303060108070306090c0c02090702011e0e0f01021206180702100c030209120d17060303032d010608 89
    0x1108c246c841c48606a4155001803183c0c800100c400324444440d50b81c5803a003c2d684116030311201d00d40d8509600400e40901c02d0740c103180360300300150805034007500c101030130301d607841d080382e0b64036015642c0c2103600a41200d0311601810043c101000a8807050b0701c104004520191a80300c41c40860808981c0200180d001da0710841c1507003428008040030304800009031000b40400c0d100039542e403001410031410841c20400180110307109520a1b40546060002403204a101410040806e0003d50707083c0e126405d000041213105005106415540380f80c04071010348078415a2202005101900140c141405010540002181c0030b1006205200e0441541e8442d0309141090000b60300b41030101003d05200801440152900007035541e214090300800070412103271982c001c40c040c1c05840e035801e42000152444400340080825650507102540d954804010080d09581c0c01c80c541c00d951084d019001040442c0f4228803c1e2502c0000c0300c6114040380f000c0741e403802c00002d058000d03406200014805028 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 351664955 1250 351663705 351663709
    0x409050303071808150415051603050108030a08010b090109121a071d06090109080a201c1401110705070311011e1d03010608010b150403030c0602030411100e 69
    0x81c9500030203207840b80364030f0941007801e1941e542c01280f20001c18002c3d420300040030085d03111000d607124000180240041d04002c3d004540ca000f51614040200e801c000001c211100000252800ca03603203580c0e65202640380c00e0348d8110681c891000181040340d4840c0206010441c560f6142545120355000103080c0c2900703d000e0614032001c2d104c1000c11100301c28013480302c8044010040c0200e8100c40ba16622400740380107884029241d0b000c0a0140521160081800980c1460420414030140c11200840d101020021038280c3c090074021104280103180e00070400b100c0902d500305480d00c0000800e1030803a039480009802400040714a50b104131001d0080120020881c0d415400130b0a02c10480d03211210341c032500324050300d0044100110b2116240300b0b03042c50301d860030070400041c00801c03016880c2c0d03900da40070b040003810190003503030720000c2458110500001c903402c82c0c0d007559070840c161280c0e40d1540e0195101130426201c000b00c0307140c0080d0590740c0a10580200740c41c2d84421181c1900842 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 351666205 1250 351664955 351664967
    0x12070b1318020c071e0f06020d0807020c01050403080f090d05030d1a0a0b0c01060302091305010608030705031b21090f1e011103130608090f1c080411040905030307 72
    0x124010745603005100d00512684002102c400769801440d82032520454500b807040307181416800003840d02a84d90000a0302600410103113100f03401952060500e5039205020b85c1d4404282c07134844e000440c2000200007148003003000c0e01c1d06000e0445040d16000340000040c0c0744980485041d2415040005d8205076a40e15100d07403055004072040c81200c0711101000101050440e1241d103d46400018080f001c0d81e00a520510103107600a128004a04102c021301d2070743c18158104a80c158a40f00f0042011400042500c00450b880702c001e51820810f8240e0000d8513a10080b407540b80c2c41000d079100d20311000641900d80100e4840c044a483d041d49000704000b03030700d003948014001d080c01141d004903840c040d00c0c5040c21423001c1c00c01e00301403511721178030a2641c811654600c111181001002c01c240380d1010b1003502a030072450803100e850403040c00c5281c44201c20116904107440203040781001501610b0140e50060290b248900b24650120104090312144074040f1540e41000041045a603000a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 351667455 1250 351666205 351666239
    0x90901080d0801080111030601050a0219110f010320250602070b060f03071e0302040515040b10081512013902060402041d100e010b04020306010e12070b13 68
    0x2d0006e1120304d00780301801c0d0340d510003e44030358100074000443c0240c03640208205081038407105841d030145499400e042c00da0421840032640308030443d51303c1d06070540c824041c40e12030101c000322019030f40c0c0c000002544070742d1001c11540c05c0700c113000c494030006070040aa2180403a0086d000544c2da42160714000798500300052a280c4580a02801c0f40d4507a240010104240c44242c024480d641009950b040001012a032000798406e040004220307098003a0b80300107807204c0c803c2c1c03000e1001403410310411011181609040c4001802c031000104450503200c0c82021450000e015444540d824848240c29030f00590f10058100548000e460035511000030030202880b010004918101c400940c02500c4000103480a4403da4440885180030991a000007686401050841c0c1c0f03488062800400940092032240f41c0e1540b0303000346020036051a00850340300d804140e580804034030070441003044500f60f03c13010014901c5101c9002c40c6c00f01a07140100070132a0782c0c41c0c00d07501482c684542e440d0603411071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 351668705 1250 351667455 351667469
    0xc100506010906080f091e0f0706030605130203040201030204030609050c1203160308090c0604170c0103090804030b0703140a0915060b0405060703031503030c110901080c1302090901080d0801 84
    0x26002c1048400d900c003100075003140c509000d624031038540d160303d145000d840c0c030291164030300318aa40000510001607010241180c100075188076550f103c0c002d4044417030500c105a002010782a201c441c604069000b1030f4002c2c8141001030820352652550710464400120446860b40402122000b80c901141900c0a45405100440c40d0031601d03103d00500e1100741d8030041c00c3c81030400102c0d9000106100981480300e001e07200640740d950f00c4115059103038030204569070394014140000c0755540309000e020041a0480c1c0e0392460185981e0701c03051410b2008008500301603032241b0812070500070005081c003c0d0301102c40032030110880e091a074804004284001281854044208461103205c0195421100101c98040e2107400310f082c103601611030b42c84081a411070b8560b001c0209070300036203403403511030203600e40843c0c924142c1c080c80b100880a0280c0304140c0e120804e140924030b000410380740130180449000d8208002d02010850000d800c2e00700407040d4220038a40d03071312554071100c21380c010002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 351669955 1250 351668705 351668717
    0x210f06090a0608032a0d02060117030403030c0f021306030b100806100306150305010207060c0908030a020c060f090607150b01020604110f01090e09010c18031709150c10050601 77
    0x6050480c0b6a20f105288110350201d12001c0c0c07200e005c822152001099058400a03101c02c03044060009407580824000c6607040154a01c80398041c100004c02e640a680c1c3c0758480301e02144003915205864010600c00b20703880180c69906030180882405110011480f405194500342000300b07180040480c1e5400070040c82e409201004101514072101008481d009400002c26030461042c0e0390b61829542c01c0031703145600010f015401c0000b103a00c5000404070507a10034203d9034075240710302c0d200d10406e4044801030344120711a00062900b42c00400c0100380301d5000718038207880c0401141c006c0e00022030548484e80d03422400c14003001a030080c280815401d00c0900301c00d140950701c00794400015002d03c2c7c003c040301480c5000c6a4001c0c8046005440402c800c02e0700da1415050031030280035800031020000b5040350f9150000c50300b100110f0142c4e035001d507407100010080c107030702c48441e040155219408048e140503002c4102449008011246511002e01213044000b82e490040d240058402410040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 351671205 1250 351669955 351669959
    0xc0d030e0a0f020d030e15040e0c1c2a09030b0a090c060e03031b01051f080d0c0203030d020a02030703180605090909250302091614210f06090a06 64
    0xe00c50032903082490f4122800045140c5030705003251481d1004800310340041c94200850742090589001d4012500c0c0c00b2600d0381d440e90740114890141c020110080e035104180441c500e50381c800341e00000b5024100c1c90007010241e6460036980740036522410002d0205e2500d040c2801848464030030035520441c000c40900070f13100160795001000340284207060030880442c4210365070303507014411100c8031110070202c48400c01004005a000b010203489814034043c410508500c0d95150a2225040341c0310480540313200034055100359262842028100e900d030104009102a05050744060300089070340f94021a116011440c0140001002d29908540d55004400401540d94420100c0e1000c20b01510308000325200e002d1480d141207900f410400803065204040d495210040c0c2444040302d002700e070340c00c6182c1c903044400d100100c80398107ca00080d8900d00704000b100c420b0401085014142d40c11140f21440c0e40c1d041041c402426581c0c1c1c00c0302c4c500075007845000e18002c90b000c0d80000c2c03044802c00100f4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 351672455 1250 351671205 351671213
    0xa0e030c0f0d03051c06080c0d03020c040b0f03100b10020a02091902120c09040b010e0901121407090507030b090603070519054902190b0c0d030e0a 65
    0x51010069184142c20302e8100342c1c1014450416260f40302c40c0800c1c03440800002c00d2151018002900a6020f40d102e003005040c601e2500c401c0c07800301d250700742c0c004d01030a00390002030001400241400c1da411058140103a00c142d1002c02180d0030000550b100090340203841010803061030907240001c82150f110300034000250340e1b40107085402c4400504500703180c12448683d10040c7c0038461602500108000c200700184280900070241120111383c05c02846858500550384205604615a000341d110380040c407001c0c640ca110b1404103030040e00c1c9500c60883e4541150703e001815002840c00310f48070b4050048150301401902c21810089541d1180c61604c13002003980c5070528454181f00d41ca9410300d42552902c0341e9460400b41c00b02510300c0441d810801030301002c165000c2d04529203801d42c280c400120310010b000314410003002d120024004042078003080f40c076035400b02f084407426004c03400024500300c1500050510704c4d100d80240110400c850000740807a003a030700301044180c00c5100e40304009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 351673705 1250 351672455 351672469
    0x1110d0e0d0f081501090506070308010f0605040e0a0504032706080c0f03060d111e0a090c0206010902030411040e06090d091401110f15090c01090e160c0b0a020a0e030c 74
    0x41241461040d13002030741c000403111650168001030300004001079a07400d140d400494a41624610105070803116503800c41264035218030b10030b04000c01100408641d8051041d0400c94209000745005041180c00e001600380440107484a2241740854101c100080c3d500b081515070710038290045542800722a948101c1c6510008102d184500c84103285072081191a00304950040b0018000580f4481285440588500030b5900c0c03500c501800e10001802c01f07907a024a040c5005140c0c05800103918021040c0041d40006d0700c111070031400381d00544402d80303c6201d07850b441d803100700c0100b2640c2000c40609090142000060042002d0050140401041d180d940070031010f0a280101e80911080c1c005818034070f9001d9400d00c0ca000782220b04100c0c45071650340034011400803042c0c540507070443c00151000f005c0ca10031501c000040d040021350501d0700321808140350301c00e400c0000b602c0d0900d55840c50b013124211116449503501240980555520000684200c401900107040450850001030300c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 351674955 1250 351673705 351673711
    0x31303030b01140408010605030c061e0708070611042c070c0602070804080106080f031c02180d1202010c0c1106030c12161407020a0b0c01110d0e0d0f08 67
    0x2456115081c0641e164828050301c1d440c01605801c441d21507880da0807144c040c0c0f09501c1014800e101e440d0760b0400c00e251a00c1294805019941d07042c244004005056416400481041d202d0303800c1800500042480e40c00b1701c48800416051542d582ca0034512188040b0f0310200001d43c2c0c0c440d0001100203920914440282c00401c40d052503c040002454550f02034810900c000308400ba01140014172aa815088002070798006801e4500d80c200c5c55100c0d580c1c034050481e240200c030100101f12020f44116a00502c6581800f01c20b1704d85250017080412a50030860504a0328884080b040e00179942c1e0a02c24034000202e240351050030400a5114515150802d45105105034000404030366001000c800701c4082e110100b420445500d002502d461900d000c2e40c0590010548031a00f0781c1a513110070003280d13441030b4014620f004a50400e4071141c510b42240042100d00d642c3c074a2000b41100c081e401901200d4010280400c12017440c000890a0154220006050041c3c1080140d016608030035040d80c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 351676205 1250 351674955 351674957
    0x3040f21020f19030f03140c07060e120f07090623120f0d020609060708160f0908031b01061502030313020a1814071b03050306060d1805010c0203031303 67
    0x5028845440022a8000c03400d82600007020003c0d0004100302170810b0202840f40a619000620b0681c0407400019124544206407580c000c144207000741401240744203e1f4400107040500d04103c0070700400c4c6002191f50001d202a03110510402c4151207901904015040028840c03280c01c020250390942245200d04481c4152410302d0b009130410b00c2041071500c8c2d0f809040031241890310304030019440d0b08041e902410b081c0032b40000140d81c030b801080300b2809180e9040039100e030034a040d481191141441028801000108400011007a0003040680800e0b6410260b0049a900d10001701d400c541c81c0d079101e101d1110002c040c50303000940100c00c1e29484030341e00d844501150340620010303100744415003043c01d000b40310040100072940b03280e010304007040228006604c0c90b1030340001999601400703400c2207003000300c3c000c020300028420b101550300030b007000e09003e044c0f54010071580140c0c2c8121015031000000c1c0303c545420722800b4080c0750b200d1900c5001451440c00c207410065800d0540b400c0c090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 351677455 1250 351676205 351676219
    0x3010209011d1302070c03050f0a0c0b0c010f0501080304091b0206010e101d07020607080c04151704060905190201050d0203040f050a03020d030e030f03010603050c07080c03040f2102 80
    0x44001e4030303000c4080c3c2c03008910341802c40d0746440602e00280404403d00056a03035207d01a20040c0c0b1001c0018844880f903000b0606108a034603041c80c9901c107030301450000000b03540f616400840c02c0f540e40583c0d8041c0450b14060754480d8141025102140e0200609440740100a01030481e0180c012583c0f030306441034850840345030707a038840b21405c1000c441d510110300903414a10304025940614500d60040049609403281508c0d203503070444041c030b010341d040b251890080204000d01024000c074007101c1041410259001d0260b0040f41311f01c8030040300c080e10415141e5092104121052000a6180c0380608980c164071401fa00001c00a004202460b51069030000210f000d0080352010707005415404000c440e8460380c20729009444000c9000345c1c80c00b003810312240382c907490804001e945680205150041c2542c0c680310049020f0240070b1301480103c03904018480105810300000c0040c0c0c80c07820002c41d510307031600c401c011050101d9484450307440e211494500c4641500501030181c5a0101c640c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 351678705 1250 351677455 351677507
    0x10030b07050c150106021515151201030f060e0d0e0f0102010b030f101d0a080901031b0e03010510030206030a05060d0f0b0708010f1805040c090e06010e070807091707050405070e0a050301020901 85
    0x216081e00c542b001c6a00c560001400010421005042c0410068868a414071420302d040903040c0e5201004907581b80070917188000d142a84c2050300080001800510000c40c1d0b240c03841000c03c1c149210703100c541c540364008c1c030380b1815008442c2c0103110041d80307400481c90320410a000459200c004a81c00288414400103492003070740c9c842c0e00822001c4424180c5902d41090707903203011700001503200b800c500075401c02c0b00290b031283e14822090226074001d0072192540e952402c916008010080c10254090a4011920003040c1001e141250b640e01c070391100c07801c6061045002d005148143c3c015036000d40c10007000e00c44101d01941a40d41100010740100c4e054446107805600129203030011a4120b2030b020014000140005446040324a1040c00c1a55a19941c000301c40000342115075001044c02104c0412a1546203d1178034400380440c1c2c25100792549840c0000d003600d800381c4a1000081c9205140f05075464440400401000110002c6242241106c0040d007541250801101800045528 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 351679955 1250 351678705 351678739
    0x506161a010f1a0f0a0c060c09060c0305030903120c0a030e0705060f0703030b060319050a0b0603040f030909050a05040b061801060f0c0c0303090f0b0310030b07050c150106021515 79
    0x44c1c0340304507000701901c2d481d1052030000130000131528a081d285136080011000045004420030030aa4130690307540151a8070503141030740d07140e10140500010b48800c1014404100c088024a8010f490b008809544d0f00000700740102980c0039400044c0e55500070000400403036072684100c6a030a0b4204900c41e45850041c201a002441d09640d015046280041040400c0150381d13180c107040454a070013000142c9501a81800711040441a0390300901e080001c01d0200e0110003241c040d0f43c1c840d01d800d20380c4645810004050341d6090310000c1d0110740781c00c03c6c40100040b404134983d1150098a02d40700170345502d4030303080131050103110b100148040014218980b91040301d001c820250001501c0c00056528503000b007209103a485000000d0205004c00300d1404482e0301101d0003007048a10f03c88480703046440e00c130010b400280c90030007072100400c890202c58505000b0540c4402240405180715850604080d042c107030501c15070800880d0b240104140030300d40710507450b124841601c00f0b088800070005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 351681205 1250 351679955 351679957
    0x3010612021306050a030f0b0a2105100225170903160b07052b03050a06051e0301060b07230f06010b0c070f1409040c0506161a010f1a 59
    0x4480205002c4041c0115900b80c02400600360003625942c20004010301c3c82682046170401015640e100d0401402040940340001c45200001031056880b18049035941d1203c0c9880c0011031040311392074002c03483c18054010580394000607408609105d08900b09650348003c81d1102c0070070a060743c840414a030080761400c0100d818070644800c8012050341d01d558805c1d903540c010340f00894807449001c00c00c1d0381400c07108200e0380814895070038421130b02125800a80260400818414042e561080300203541d84e6090800c2003d84404a0115000c8103000181401d4800603045010709407000c00c941000a080340f80b0003400050000c0d0750f41c510000c481981d600b4507240c10468981c600c80c070740000c2480398804000380f8140e0140021100510356034a101d5100c03031030612401c00c42042088070840d00d410500d0560340e005125243e103c01140c1c0b20f200040030303a004800004017524003510b03818204401c0d18211000e51241d0134102d000b40d0303d40944009010254020f0101e10f140c004880710001201c2c1c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 351682455 1250 351681205 351681217
    0x607090602070506090d0f061503030804140c18070e060714010606091a0d0f02070b10060f0c11030a050d18090501050a06051804020a030c171605070201050c0a0f021908030301061202 80
    0x243c1c1049c107036982c9040041407050103440c20355561481006a03140c1e10310003d052841c0d0070001e01704500421201d1042d01101d04c000f0100c105210406001f00c0d40340e80c80c41c0003060014803c406d1441d442c28945a00c50031600c1075001007046c400400014071003240d05480090001c004e84001582d1006a582141c0c05044503015000c1441c0c0085085010030507188203582c070400031121500d60780366541e20704031045e8404c0c00d80c0001080c00b14400f04040b0b1182d49541d01c2002c0c02a0886900c8a0555a11840c04103035070104c03000107000411090031001f90110800040c035111100380102d50400000442410840c4200c005028000600c00031307c4450030714112400a00400842d127904a49001402401340098824006400030045001c0240c0864002c1d000d0105a503045843c42003642003a070300c551002005074103022044c092510503038000c0090340c510134030a4000c2191000a071050203034094008081030445809840b05220300c104c0002a030381125040c0c9016400703110100d480300001d02c50302c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 351683705 1250 351682455 351682481
    0x9090c0b070305040503210322050708030d06060801030203190302070f081b090f042013020c0d050a0c03080726090f15040b070306080607090602070506090d0f06 71
    0x4580c1005250f0004042d0085600540070384d4905448036071085502850120100c02c011000d1000c90203e4102c10440d2181d01020300c5000a40300e40307600c900e8504ac10b550300c20103180c0d0001030200e103010303040d005031401410b15082c41d01c0e640d41140d0009499542d0208a5011040391115a40901d403080100100506c2407a0111030810b4070707045110f80b01d120032000355012484646c00e00110b42405ca41052150f02e441d4107440135501c841d510b508581107008103c0c010780c030102031809440d41d02c0081011820b440d580c001070741d6070110303500f0341c0c1083e11114180051010034020201c0050700140410006585481c00001039500c01c4025203001600c3c1541d80150380a110356a00000c0f90109003d00030280780d41100c840c01700c0c1c1050603a0314241c4211854402031144e011800040010040c2c03a0030010354100400c520762100200c3c0c2c942002103c4080000b881080f0070030440350180b0900700a010b05503075081c5080016404601d42c010400002841c1d100c14003082c505000643d03102076408290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 351684955 1250 351683705 351683707
    0x504050a0b090301050c03060d06090606090f09140f103803150631050907150f0806060705010e0d0906030501080a050712110d080703030f050106080109090c0b 70
    0x22602100307840d800c040601406913180002090b160300204040da84180c80c02081c0320b1900d90190703110405403c00c8042150100d0301c5940c0415141011b009200401320f80c91400204d440c402d04101d83e00d601c0e0030b540c030340d1960003170240012501c4002c100440401180140880c035850180744d00f440c2c0c0035005804060038400e410b54980c01200d4a442101c10318003c808a41c40c200444100d2100040181c4480341c0c0f01015140e1300390500020701992982039610f4621030814035a141d00d01e426550700b121184c00c1e5400040050010789920310b11108806400e00c1c00d40c4274040c8c0340320090420503016000c3c6106600c082007900c01c00009401010070860001e05841d01d500d420395004c0c00c3c514213030140f0404281040000700d285800011a880b08540003c0203022180c40c000444000014004c4140c841c8d03500c1c0b04030b14105886001c2c4c5111039510503050256107813a2820024100c600c01041c00e0300c418100b178010407100381c0c8650341a0540b4014280016488018a0007521400c2143e1068000c018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 351686205 1250 351684955 351684959
    0x2091911120609041e121724040204030b011712030c16080d1508010b030c030a0314040905040c0302090906070c08161707140715030b060f071103070501020a0515070504050a 76
    0x5614459070b440c0301c0354a03104e0a072003c3c50703600720b141d9004030351400042880b411081c01c0005540c88c45d0f110804e002d00010b00d0281c903034840d4010740000741c001010b150a00f5804846040c0100020741034000c140c1c03d40d900f10b0901489529544c416035441240341c4805141180501056804441d82040e2003a010080501031072820b20b803188a62203074060310b500e0007070b00c91524140400c4d4002c07014030040c0038100c80a102c0d501910f00045c4440001000b44044c0404550100144542c0d070103035005500c40102d003403840c030420125410007400c0004540001080c4500c49410001e2440c02d44c0d8031402c101d844a1020300d01c415900c56140c4007030f01c580e0a000d80ea010254101004024031b030300a1078442280032284030b1181e0340b220316110f18440d060007070320070030101446940b040511210003003000b854070001c1452a05203030840e600540306070b1100303e805401883c0410001008080c00c0c0003600c18100c480d03e6154460102c2c20740145181030782c40c00144181d100b801240d0117004e0050698681c0c80d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 351687455 1250 351686205 351686213
    0x30803010302270f09010b01020708060a020d0207021201021c020403110907030e51070306050d1a18030405040b0d020a0b0406090b1317010902091911120609041e 71
    0x1202a14010810f5103451f2060b1043d502c0415400d0a4403000742c0208403a40b0341c40e5410b402548081450080181c2c20f029040c0165510399130415501c03401c00c000b5031038080d0700000c04c4d0550f110054090485204100030070004501e52410340182c030084408404a45d20b0b0103046c0d001e010b2006008000340600145244c10314901808080c200121030001d070844101495680b15401c181e200140c8045100008504540098444641e02c0349542c030f0040344980d602d0703002c80c0c00c400c1c0414003260058607550841c43e4400f80f03016800c1d88201c918807400818030380d1a140a803a44503500856001e42d44450080e80e2035103070180201c18031035028003200300c15540c405c00c260450b0464010080003480c0300000151075040c18080d903804030444250a4005454401601e055200810940030555203075490100176031341e5000d02070302c99041007031a0781700e101541703011030125210440f07a640000c0741409205c413040c02d0f81c0109507001c201074800721025240c50505201c9801d01090180d580c1544110943c100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 351688705 1250 351687455 351687481
    0xa0813030303180506010e070c0501050705030f070c02060412110a03050304061103070507050105210702011e050906040b0910020f0d0f0b0d020415080f030c0d0903080301030227 78
    0x4038002e50b802c00c103407111942c0c03100b00d6100046016100c5d1744031400500810f480709007000d07001030a03420100c01c81a025910f441c2502c40856403000812000f0040004400e20150040d5010003140340050007024598000307447c40c0510b0003035aa0382c00c0c80b21071110821843c01c2602508803802020580120703907070b1800c1c42d070700d074040d019010000e29580b285d000d10000000a6074523282d80000a0001c440c2800c0c01150250061b160b240c0301c1108000d0300d16500c0389205501d5002d00015800420b85c0303608205401c2c80380d0310b4918084602c502d09420402382c0c58010640e2600b10b5403003500c0e42d1190f02c0740b1805510f06a6000710745c107103c40c030000c1c03040da4802c0c80c0001002204002401444952001e95100f0200c03035000a0064000c070800601000500e0154403100501c05148481c0403401d84861046180149080c0d3b400c02c5a0310028070f44420200c100140303201e201c194030b450010710707003181e550180c14081840020302031860311007501548a0140c5084002d498075035212805841c0c803007064004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 351689955 1250 351688705 351688709
    0xa1b1e030302070e040803010506090d060f151509090b0301141501090b090d0609051c050705070f0b0a0e0f0904150506012c150304050a0b0f01050117090a0813 70
    0xb500c00d01c1c3c800036101c0e4081034228860307a044011303981582c0c81c0c1410b1104da40d000c911125030001d07008180c3d000090541c0300d000310341c5c0240344c8009000c15402a030180d174102c45404c42078044500c0c0d121545c03c0c44d4002e0000c0305a4240300c001060481c00c580110b40035003d038140d201042e1000c04c04108c00582002e101e200528400d90b03a200703155a8403c6103486600c40c100d0b2039500301d40d00394040004502280c024402d26417003001182c10100e4032651204031440440c2101000810008a402c1030000c1005404040c0c0340301512400128a4412010914410710020740d0900080c00c2c80548a035440c02c144003039001004d40444118039061a02498441d0243c0e60150040d183c0008a40254812600d0408502c01461080c813140d05510a070b48424503280c42d26680300d6041c0081c0b1650780c9010f0081c2d8026031080008099a000c2454440c4155000822400a1210720001004039aa102d01a202101c541228017030040c0c8130502e5050401c3c03260034024088160008061031103c001c0412002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 351691205 1250 351689955 351689957
    0x210050a1b030c0305130509010b0702090604020406020a330c020f06010501080c0708070204020f1b0a02030a0b0405100e0706091e0308090321120c0a020a1b1e0303 72
    0x240403450310906040c0d080c075000c40940020b0008a1140000b80030340010700400740c15528a41805070f50b8400a43e031207200740c100c4103400c000410600b0450418009442c0c00410454041d4142410013100a542d205280d10240601403503150f8004501d1041c500c005096000d03001401242e1084180e00340074000c264021401032145061505850001207070036070580703005075184403407519540450501d503040010103950501c4200000300069907188001c004080c103850f402030711081d80e84540c80c0690200400a04960080e021160050f600410781650440e48103000c0e94070350310313241400c038503040c48050205501c514044104001c92400a0402c007147c040342d4444501da5120700701400342d0100c20342c5801c5a1003400e0320510000c0d805030007520107518060102c51000c450b010b4107013035082010708401c000b048001907500b00c12040e1007803240e0280010f03509619180d62500001c0d130395103021401510303082320300c6030701a02d805941420398000d29000381e0450040c1d0140038051500841440220 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 351692455 1250 351691205 351691217
    0x1c0c0606060206150409030f030203070302091e0f030a05030f16050a0c0503060a0c0813051c0c020f0f030a0201030e01110705070f0503010b0303160c0b0f0310060311071407030210050a 81
    0x130503a151074040c3d641000e505660b02040c2d0708512006038013a42001c1e0543d400c2c15000d01000300107440b115070110090100000107130b0324041c22018401c10308107408110740641c01030207202e0b02142002040b5800c503646a52070907541c0b03544465224600100c004010030a008003080581800000d040c0c00058450450941c0d0580e01ca01c4002002c030350500036190045110600040d03803c80b6102c0c03a034040c3c3c5000d00d098400c4005500720900719103800c0013108002c00c45010224080d81801c1c09841c803c200103980b6410704000d0007000030b0703031038414400080c1090384078101000d068400b90030000190013034102c0c003515450980740441c1c540c40640038640e44500b03940400142443d050080d1400700c0e2019020b540b0f01103007010402d001c0c0110742400c1e1941c0d00c0c0d240000854901580c013b11900c16010707040358a905040c000b5030304c0c0390f8160384003400309420079107c00d9100c0381c408200c41c2c5140e8081400d043c1c00c04020301e10b80c141070050340b02035400319030900000101e94000c1300030809504a9641c603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 351693705 1250 351692455 351692491
    0x4122001021207050a0e19030b10090b0a0e040813030b0c0d050603070f26030d0f0506090c09040f0b03060703150b0c150705130305210c1c0c0606060206 67
    0x301d84c140555402c460001d50152414061401c08070b60020050550480c01c6242c01d8403503d0325042c0c40c5083e11070740200021604100103c00306071050580c200320445040000034945441102d068001071b0014103201400180004c070300c00303a602004003c580c00355807440309142c802c0100c100741c1c05c103283c05214181803030005422864085400f40c00d894031070600e40503a60610010040d001a202203200d1300700220004501e010340204040c0640480881e00481c00c608045403010039500c01901c860300800c00701060119009514066505203001a100003a0b40080240000c000d0440214959014003520b814070080c154940c0003903200751190304809901c581d485101c28450700c40d50212640c0364002200c002c1c8000110384049801000c280750044c1000026034010113802c00a51044690b40e00072030b403510f040c130300110344132061003560702c00103003000340f416451a02d410110020111340d214003c2103011150081d004a42d03100d80106082181c01e03212180a9a0340070280c45d40c0403400403058807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 351694955 1250 351693705 351693707
    0xa030e07030503250213020309250501030f020a0228060501170d02070308031f1d190e070b0d0617030309060a05060d020d03110a0b010f050402040501020604122001021207 75
    0x1140e06180e02404440c240f0721b0f000f01220013500041d00140040c00f484240030403510080c4091514032510352018040545020000340444c0d9400b01611a0303140141310140105070040388500225203e4212050300211442004c0c1500f0110308000303200c0b61512300041501100054800480b1190b0380480703030514400d03041a40c3d03401e80e5100041a28400300001901c00e8041140699008140c244d2440c02a48a080300300981d940906404c410103a51010001c0140c43d00b00d6100425180c008100034002e540c100190302c0d94810b024405006030000b03400c100080c00c55000c41b0061150000310301d055421080c03034580707035030040e00c140120b44101000f186006140f8801c01d40188001480d491480c9083d41c2844052054480c0641c04c4c408203903034901e0304050510040c401c0912031a41c406480d81846890740040e5029007045000d60310622051003541d030001a00c54000382c01030103031288042d11003012036214010720380254021815130041e00c141d1b101500a4003203c800c8540c0d00c421a900c0182c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 351696205 1250 351694955 351695017
    0xf030c1e03070c06030e16060f02070e010b2d1303120810090903200d11030705070611030f13031509051b01021e1c0807020c060a030e07030503 63
    0x80c00300c00414001308400d80c0290f200780b10010a103011390700c13602c00712045101c180b02d882d4040c002007542d0903140b102296050251401820025484400035410601c1065450085501001c0180320740c035129520349030701c01c1c0004006850886507a81c1ca20b07648602000300c1c0050320040b600e004900b015166254002c180040c0314080c2100200102131402e4010006407141d42001e9040c030950412141c40200c0200300c0842061020b4010b01080c0803c1d2401840650401400c2009400612980c000928041590011603045140c401d203000a450505415413040c3c0707071a0404018002122840281c00040400c01c0745c2c040c020f466428000c4807549c2e02690050a002030898010708000850002c1c0351040030000315040c8129200285130621129000e003e459003520140e008188103501484005400a4901803d2504885078149450045d585a50404055106107004100e41062920945c00b07000e0321054042125030071036503418559101c6c1d000452000600c0800c0c841d45044400d101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 351697455 1250 351696205 351696217
    0x20a090c0815010c0209010902041406030103020d060b030f0d090e0a1e020d060e01080f010c1e03180515060103050c07020f090408040806070e0913020d030c02030f030c1e03 76
    0x1803110901035585000002c03603106030044490611941024650145c0c03510070045000e00b41c9540700695841c142501040503c213403a5080d0701c05c034810001400140c8075040b01000307032070b4000b002040100b20480083c0c1401400d40004000c1d11903980c2184540b03038031038410400c54a0a55054020b602c030800c49100740c8014a0011f0640141681c0c2000c10800f568000d04045181a100203400b946034018200000e5003a840000c440d03205480240e007805083c4240340d0030100c10b003451600c4540c10306a0200e04075003a08100709050380c980070170516250102200c154941d102064034000310104040240d08001940d44600103407400d40012050b0640008603401560010700c1400b01168120030014500c000030306c111000c04c030a11000488540800c8101d0261440c1d4a40d0a090400c0c1004c1c004008001800011501c5110041c078016807520302240003aa601450a09004000d60011901c0c00c480303089040030034800003840d4420070b01c01150000403d01d2a0403143c00403848040150b070b0b42d000340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 351698705 1250 351697455 351697457
    0x1b0a0b0615034b0705031e0402240c0d0206072a0807050a030f05040b30090703110621040c0902130608060901061b06090f0f020a090c 59
    0x81010503110f203d00b409042c41448408030360800c0d41203078990006481034408181154490094568a038029040d0207581e0041c0c4074508242189440d1030005421405142200c940000100105044d92103071100a100200c4075500711507180800109050700e1b0f0b00c03245458010b4002e20390005201440490954000c50380d0703946803222072904400840613218801041215410203816682c00036803264050309103d40a403000d0030350340000e424085c0c00e65244c08158420404100000d1101c1000b540a03518926200101c1e1601541d280040601c1103074001000b600700c1449078100110488001802800e032885481818110040c3d402404100e024102c070390b003400401090351040d20351070580311592007405080c00c00480c80c1e81d00e04013800c0740e214480e580070b640c1890394184005908145241d03007241c42903856a1141d85402c400401c10700d5260406d008015180b40001c061040340e41143e841640c0003283c0803480c241915004854004201040380140314450000420f21420b10400038600d0322 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 351699955 1250 351698705 351698707
    0x30d030903020c01030c11060a05070f093b010905011403011802010c170a0905121507080c09040510030201030b0306091b060d18020301060801020a020309151b0a0b0615 74
    0x12043c0154085c1c00d1030580d9100f0085188405e44074100708001840c020350080400207894101804010078016445124100784003140500f009071200c3c8585401c03048010158030007009010700040080114841c510a665920f01c0001058903406944168101d5484802e22901072401f06c041c982070351441e842c910041d89404a101c805075004110b11031a41e03102c3c072400300340c801812100340f140e504060b149074001942c1c400103109604060018091400e540c40043c0341e0001d090440991815004090104201c0a0408500c81d0b2403180151444204001d0060200d458401c840400380402e61009900182c14100300c880342d03040200b081c0c0d028081010140041c40101607103071000124408405400c440204180342f02c41c6900c1c451742c00b42c5505190501c42d1219640101800d4840c81d400040087c0d1040161412040d0000120b41840c18103440454000d540b10004c0300e42130080b50200480c0c0130000c0c900141615004c81c200c1c075800d101e07030207660b41074684030144101d41d2070340f050300c0706030f288 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 351701205 1250 351699955 351699973
    0x3060f061407030905121f18200904050106140f060712030b060a05030412030216110d020d06050709060518040e0309150a090e060604060806040b0307080c03071d0c0f04050d0f02030d03090302 84
    0x100303100d040001d040c02000118503027010480030802d80b19088070107a039140d40d00c076070034421404c1400403603944002c111159141009400e000030b07150300c2003901c020120a00141c0281000d402600704c0082d0400041225840300c2a0782c0010304035a0046800701c0300c40c4044444010810700070304c01e85010000a16039205280070a0381d485120002952009500c140240071110042c0d599110556240e8131450020a0a04045a015082103070f203412200510105201c1d01500c0140454410010441203401040b05041550baa5086100701c82999401c841202c04003c00380c0405002011480f503d0780d240e6050507601d2104882803031085d07519950180e020007080048078403c0c4901074002d040244006000f1009034000380ca4010207034403001403604000c808030414070301401504000c003020603030264041010000c15003110b10060100d5549180880d00140c5003081605882c00703410081c5c032400c41281c0c40d081006001e18003580072440307031064510481c030700c51080c00344464450b416001402c09003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 351702455 1250 351701205 351701213
    0x80304060f09120c0510020d27050312030610050405061615060f1a03040507171e01020d06080115090b1c1203060f061407030905121f18 60
    0x458181141070800c11080804681d0003000010450601e1040414400181c50503040c00001c2d0380e044410307001d41d006100351100d900c3d0420803c0c0b54084c44210807550b08144e24405116810040e000160148904c9004000c1d03218406d00a5000d80004c8941c0b1440d60003d400c21141c911490150942100060040000703510810352001146441118078515180c50340c501001110742c42d520a4420b40c4d00c805042003d010b2100700952080b41240c01c080c9140b83c0360311038642c0e0340c00506c1440b40740543c0c4290701414150a00004003403114001c207001405800d0610f40d0f010790031507002030001615080c000034403620140300b0008200260740f045c2c0350b42c51500720964002c04c0310300715481e0000d03c1d00c040044007508584264a0342407007040d40740795282d03041e040182120b81030b412031036020307601c400c06000c4182c000ca0a039224100031400c5640d0303481c99280c00c0b20078041c154440b542000046c0407902d003410010440b0090007aa80e10301c0c1c0300c3c0300d0b0325149070400d440c4a1000001400c2007480c80101007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 351703705 1250 351702455 351702467
    0x31603030516050307060b0a06030902181b03010602010501030b0708010311150f07060504110402031e071218172a03090d0f060e03070218040c150201060303020c030708030406 77
    0x21203040002c142d029890b0300b03065502c410740c111102075a400ea04040d52070185c1c1c3c4003000d00810728041101e03041c01d5002c1a60642031024180c0100540303000100c414101c81e10f8101c1582c0c0e8141d00c107451356940d0754081c0c0a03243c03c0c007044902040250000d980d0522820904d030480e50004914654809480144031080e0040c64448104104c2042020051101c5c48018034585218001c00561880d050800c1402c00e2a0401c0c9140714500410503c1b1058440389082405083c0d2242540c2198462020650f0300c10b4045c0181c040701c904003d144600c08400a1004010b5802210b240f641c0c9035601c1d1794078540d40b290a004865032160301c5405184003451816002140c1c82941c01c61f407410710410000782a140d07581208888001c81c1031000300410500c0d008090340d00c0c107100011800c1035119800100080c20a42d244007410300030000203014054030b078034402c00030040c010082d075407020202c90090180180b0b020030341c0540700700625826642070000d40309045039258005141070a00781281200c0c0e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 351704955 1250 351703705 351703717
    0x40c0501030525120612120f17041101030b010207060f0c0302030d14040c140108040b090a0213270203030a23040803090907051303060f24030b060316030305 69
    0x52460600d0a1418201c2c0440e01e442c1884401d413107030101d01094034a154141d900580001000001c40c00c6200c000504044244a100d4451f0424180c4c101c522103046503105008101c1c03250750070801081c0805c1c003074055001164480207a81c1402820003840047e83d550403d8440c82002407481034401202510800022105034420b1041c2c9103090b0b100c2a40e44150341c003c0316407800314170601080c4010854070301040001441d11a92484822002d00c0029041e15801000036094240f4040002c02c03c20081c02034541d0076600400303070440701211481040083c40c9000b030400c000b229800711000f00302e14484156500a60040086140a8490070304440002d03150103001c86000009108c40d440030700750000340c4050314800000756200c0845500b00845081c028000e0f606201081044100c00240d00018106490300f01c60003043e400c40c6580c2400051001100b02c40000c0e10802034410b51516007418942200c1c000e142662158550004164072904000b050741e0400ba220802040068014070140c50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 351706205 1250 351704955 351704971
    0x9020a12060e062e230c3a03021b01051501090f0315020d06081e0105011d1303050c070b0c01050c09030d08060d02150705070b030705041404060918110108040c05010305 74
    0x3906080c01004c5c0f4003e500502c45490568002859001202d410002500c1121101d1406030b414030f034005406406032200781013441c081580000b40b10200c000c24101c1d0b030082d4800a0020020340c0303800d40c0d0b00c2001440c00c008140c00100880300004800040c0d10110042da6000b01e10a54146029407410001794080c1c25022110f680390100060005004c0c0195004211210000b80c9803080140059007100c10580107110115101480d0000c0003407406c218540c0a40000700b05101000300c0d003030588643c000c0e00c1c00c04403540300340742d80032808070340d036101400c4001d0300040207201c04d4a0340520500741d405510f0025030140d01401e0100b99552007000e005800007806060000d038400c080e0007242201d4040301e160304440c1c02c001a04000c00c001080220010420b880101d400c41c204404018002e104d90f01c01c54540c00b00000c90354810b03940c0d69010800034842d140d81000548500c0b855004680050241540c500b80f1640c074540c150350040103043d04c60740e80080001d1500341001c005400522003e81101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 351707455 1250 351706205 351706247
    0xb040e060d14060108060f1303050a17070e03100606050708030a020409050a02030f1f061202090a0807061202090108010513090204091b0b0f0409020a12060e062e 71
    0x1c0080381000310241c0c0c55100c200d01601180d8102007265183c4400640400345000203007080240424800440a0809a0610b481ca42c1c036145e800c001c03181000c02c090004440e04480c01400141c80c0c1024182800d8402901503461603e40ea01c41e0608603416849000f0102d081003100200080d0758800540e8040e61040303006091684a060400c11294111800780707a655000091249800b1800d40582d0f000e140c58442081058107040c8520002c011417180000f8000e00104445541c00e10b50191150924040c00e649030441d07440c200207a03541201d1103a44080b5910900b1074480b190107008a030f03900704040c0c5504000341d1a01e8140800c00684014080c140c9517175203d81e400594450142511103400354480000340c000062220b41440d10320b500c074100c2200c0400a4050007610784060301c08484409400588980b5080d0b800c0c2c58400340c1d4004e040c0900c2c07030601302086028044001781d000704001da402030139040350400e1441d0380050720080c0803203410b501107001205510801241d000009280d0503c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 351708705 1250 351707455 351707479
    0x40203130803150a150e01082703090415290702030303101703070201080a1503290a0b1e0f040e0303010515250302030f1908010902040b040e06 63
    0x34442d0019949800c12508400020040b89813590319040940101c507102c001c107283e403100161400107801083d505014050380011a595000c06c001e45001e0020b00d812003020041c1000c1a44035400600d48510aa142007a06180b2010b0141d84905503101500c10301c2c1c0d0300340d52180c1d6810225010040300091a01000864016101070014600414808171012542d80c1001c84040e0810070a2641000a0380306000700b00243c3e9021741e0131900518041f0000a10b000310f9048030055008030780010380059161146012243e124080b403140c900c88a110f09810f540710481c420054607100f100080d4002409088018500701980140d1040c2400a0007a01070400d900049401d4400c20948102d0a4101000420060618000c1480d00c60302c0c1c800254a42007a1084d5082c041d01c410800e101c040c8058a500300400d0300030012620001c0140d0541790b01e680c40c07905d407020380c5c60a0020b5040068285c0740009003248083c000c9d07805840c180d81c1c8540c1414181075800e07210705d02c000c00d40e55000300c00c10390f9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 351709955 1250 351708705 351708713
    0xa1503140c21041b0608060310051b030c09040608100c1b23010606030b0f0301050408040b0304030e130e0c12120901050d0e010507080f060a0501080a0915241404020313 74
    0xc0c20000c0401d17846041c89840c0a00808d810600311001c4000904c1c01c003001c00c410840c40c041001c0c2912810288980c032500d4800c0c0780400d5000d00b2000a0300030f0714008000c10a088002060003851103440704c103000c1c440d410030003142c00c2e00898510079915106085004001078801d12840c0e40e054061070462a100d211314411404c1da1001e41c40000480d5686240d0419414245194044814103070000e000710b0509684000e41803003540f00f82c0e004148040045001c041c407a12060f01601c0c1c0085c25000301409000b851030080080800c1c4440030321660a0b100564145441304400720902c50000e030095810b00040c0c400d480c0d000c0000b05040000c2000b40c141e0040701407044191145400b000020b0b10320b001a00a131044c20090a80074843e164402007020315a03480d160f103c1924021310b00030340285c03650f14800c80039082540c0028503c1e0103a00c65031981500540c003a006e40708400c01a60740d1642080d00c200e45503c56401410701c0014946401b04603410240c00071600a460303221480d0307580780b09072a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 351711205 1250 351709955 351710003
    0x806040b090c090a0609080307030c0206070c03151406031209012607080c0f0702010c02300c0105070f120e0607110f1c110a1503140c2104 61
    0x242e03602e034810010440980301d0a00500c0003000c5c0403a0b0030901c4029082c1110a983e0340180d200090802004d0303803047c6c0171074032864140d401d1135601281e14280d8517141d103414400b00c40b00c005090105494001c110110480c29584140655001750182c075480a1007841c1d44078952102100506111034401c614480341604031551070580720900d89c0007001e00701410020030805014202080f0400e00b40545a00e00022608444803a68242480360f94642c1d82d00c0030072100e14905000d02d12003481005861070003503000812800b080258015600c4548200d0010f4800d030103100c8020b0800f16035928500d0010b02240380a40201e01d00c2d0402401100a0310b0000e00c16500c00c45c000c55a040443c211041981000e01240c54002011201c15603082000d10780c4010340d0000c0d400140590440000c89102d85e100c21007642c01500500d040510700c5a1380600150151083c26041c0e040b00e00341e000000d1105140f00700782ea000400c011a0249940c6034a081082040c1e005270003501c0105041c104d400c14200718003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 351712455 1250 351711205 351711211
    0xc0d030503040b0f0408190306091b11011a09130803040f0606140d031b02060c150a0e070b0c0111030f1503070b0301060c0f320a0b070806040b09 64
    0x280da42a5203241030301d8030a480c40000703801109804080414040020078800a031001404180c014015a2007035078012405000c9030741c010303a009880d22109460060040c01e039031604401d5525480c2142541e00401c030701b01d40d0f0b00c440a001c1c03011001c84996070b524000340340350b401c280480c81e40340f04104181c840c55600c0d481900c1c2203d40059a1040004100c3c4a0194400800440c08880160b0030f003007000c1200340c200503200404020740d590384c9041000103861507003d982d80251841341c4034241d0fa6600742e07954801c0c050201070805184c0c0050319414041c01a050204080e002914040740303010301c40c04850300444040049035407a54000840400f43c0d001543c400c0c401100103e09900705030005071011305103a00740c0d0303009800880d000d1046548140489044601078680409801c42a04060400c05502c0c00001c1c80c1c42e600a003411403403651808ca103001d5000180e14454220144688603507540070082005010102d0640012191806106000d5204201400100c1c0714080701002410b0a1400c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 351713705 1250 351712455 351712457
    0x90406090c050919120303020307020f0604080a0e0307030f06050c07080f03010302041b020d2312090c030f0a02040f0e0d020a050607031512050106081519110306120c0d03 75
    0x401c3c0d00c905407401c40e11842c425119428812089410b1003840000c16601660103818140c000012600c81032081018004000b05001541c1080c200303450442d24070342c40540f00400203510303950340c81140c0c078002c10803400700c80e409140f070700c45140581c2c2c03880d0180c0401402500404010311145020034287c50042490071900784282d0707600d604500c1044100d40c40c01d51030020310385020703200d85401900000e61a0030407c06080001c80c6003815025420362100c1442d91500e030803004a04421803050313900001d8000c40c000401c0d03560400d2a0000d146d0b40e14410403004c20664010494080581010f61000b09405032450300030030401100d1608a00d4000101c9003500140d00514a130024400b0520401e50020a1454140400e19031441e9000800310b1b940241c040300082c14020b41c080040951102000b091900c050b00c0b2108855045078501c1c02c02121901070b51811f84080521801d504c1c45051058884461690b0035500e402050010000f000300344808588180d1204030069590608401031441c82 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 351714955 1250 351713705 351713707
    0x3062d08190615030206070b06120f01060312020c060409051b0c0d03060611070302060c0102190804030f1404090507090504050a0b040b0603093403081b060708010b090406090c05 78
    0x300c1e15050b02240d80c040c01a4141c6104141c0030310050b41ca500446401c01e0708150441084e0f02c80c4000180e8260081d40d14030080d10640c45215809801034200100301da0181c216400e00310304503c03060382c68620394403982e86d101703500300070a00c0040c4c80d47c0e0006800c04414800c20068104000d090034140c0e09c03000e511030300c070341c0030405400c0035903490f00415015014614180f50303100c4ca81000b190342d41f051804024800c42c40070841c010000303001d6042d20264060304140c40300700c422521000c2c0144005031015400a150ba03903510322140d0240c2344205c04006284681c46c945481c200000d001040041c0c941002c016202c8000611640c590042c43d01a800403480003c00900150812088820401005004140c00d10420401c0c42c008242c40e02c00401c845a141d00b601440c2001c0c0385880380c10000242031740c900310804801c1c42040405880c000c0780c01d03005420311210f2004a0755580d54100d07031110000d00000014800c0504c24405004241c1e406000070031a66114083c01c0c00351a40303500381031b002402c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 351716205 1250 351714955 351715003
    0x1b0e090915070504180905070506222c04020a0e0c13060e011d0a21080c0607080703021e0a18120c0f14040902060f1b06010603062d08 59
    0x20000040c0f80400010040c100208001550b6294aa250324401d03a40304ad0030100c0c1045078860b0005000c0e01d0480c6030902c4c0e400454407840003540b1078401903180d4200c903040400e0303040c82c00d8083d20024003031600240200c40c001e00e817200c0c0440d00c09000b000c8080741c4209200742075041280e03207a2400a001540c950b415104c04e500001401a0b002c062540060004c0d40034410103a100e05e030040080d290080200d01d00c412800160b03ca880110341d10050940744006459207000c2e034040340141c09110103035035440c25034a0305542207003a4000e08000301110b0500c0d0001840e00d2584200802024100742002200b401e600e2680d0946904d8036402030100880e024003250400c14111442e4000d0300d07081020b50306e03450401c11705100c0d800d0080c4003940504c5e03552002100395992081590026081c0d00744c5c080da204454181e99184089000030490a4841c640001c50014024041e01c015035090070648040741f00c000581e209072000c140c0d0000d0414028a0020460b19400e00040280c0c0b0251104100b03000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 351717455 1250 351716205 351716219
    0x2202060d0b030f0321070507120201060603051e240a0e010503101e02090d060204090c08090d021f02120414071d0c0c0106080d121b0e090915070504 65
    0x58007035001c8400c2c2c3d0070801400c503000349660f0300c0600c56804061110506e544030b0100b035881c0d00c2803100141c52840c0a1148510051741500114180d0300156001e20264550184542c0d112007030544030109065200c000840c0310b80380e20001c1008842c1310351510196101c0c000401c4100045800038040e81c45904010700803400e0800540b0342c00040a1020010030740d00b0244000400480780042040700d400144500f1107a68040a04082c035400c40d008666075507413452184020700f55034034800c0204101000044c00c142012490001010305500a80340315030411115150b01040e5191440c0c0013076080c011101400f17101d803c5588151b1043d6018056000c2031b650207840c0c810290300050b2095000d4159403e03140c12402615048082d0021194840030250f1910740902120740200d449413003605640a100d41d400480081000403240e000c004200526011514003000201580080b412940080c0e2090805c841d0141d403086818064810500c0010802084901c4c1900c1d0080003640200e01030202c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 351718705 1250 351717455 351717463
    0x121060303031103151002030409110a0206100f050402090103020403080c011e020322050f060f060f010c0b04110a030803010e0f06030a23010213090218010c03082202060d0b03 77
    0x40d183e2025504500d40f03d0315201c0801c1e40302030264040d40c100c9010a503058020020345000d0704020030103121489401030302c0c54041c0c0200406600620525010a54064060b44000103660b01e01c0380c008107440c1840d09220107548041641030425a0810000021410060203400b682210300c001142c001c40741c04200b01400047c180d92100c0c5031042081c0000628481460a401e2062102c84039006520741032017420a6003a04008555004003030402103410100b0140e584200f404031400740d201d07968003004407410300741c0000090145034150007040110f00c0104191040c18002003001d01d82603220365443c030040e0402c0e070196003040e4455050002190214490b2580b0180a400402d9003403440d0b01c41007040c0510390303031a0404802045818a140d4070a404549200034507500180300d1030703500d14a44000354404050102c2032000030041c0c01c0a5032256000b00c071215011303a906556030300c5809a4903100c0c2056800c6001d111f001c14150401611080f002c0e012112000710001a403100100c241420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 351719955 1250 351718705 351718721
    0x6060504080604030c0317041208011e1e030206040e04062702091008070f0312020708030a050f0403120c0506070801080a0b2e0314030414040b012106030303 69
    0x502000340014400540005800769010ba0180340000d11407840e81404c1c1d0740300e075104c003150341942100820132040c0001d0116102d240782860365203000c144ea86100341c521160242424541403219054100308003404229500d220403041c0e112905071950745e81c0024600d62040e80f0800c043c00000c030800041c40780b030b0f00c00c004a06914207a40c02c02c0500300e8003808800d5140a90080c031643c4980042080744c034544c0200800343c5408e808a9880a8549103d116100054802210741c00d840890b2980d03018400b040344022101c5281c011402e1000c04001505e007508000421120703024148000404030304400c80e041d04120745600c0312120381445081c020300300940101010280054440100140070000801d000d181e07400c00341008180d01c1d0650110400a0050451074608682414060541e04a03509200840c0d106840c0300162640d080e0000e03407a4000c0b80300710303210300300d10140740000340c141504403c2c48140140b414020310b685260b0904a00e48803940200c90300c0365102000d10402d6054801c1d180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 351721205 1250 351719955 351719957
    0x43308010e010503160924090e010e0c0d0f0f0c0b030412020607020d030911130c0810050303030606070602090d051b040207170912010c0503150f09010614130f0305010606 75
    0x104100014039520985086846034640c004d0791402c41060345400d800c46421000c40e0f000544031f22560b60b5020300007410820030303014013951038003034810401c210020340503940c4031001e4051012a4010303244c0322044400104207440071000109158001552180d1100140603484100c40e01d9040504110010364001304034601958042030a11600340c1e0000b42c2162040454038010031306158502d04440801d03001c400c3d03903400450341e001380c49002003542c010740c040021550303450560fa43d0394000078807000501d111740ca81541003000490303540c2c00c0600050454602601c0050300e025155404074210850a02041d1000c0d00108003148805410401000761840112030940c14150181c842501202e01040c07460340c075400c001690045901d031a0b4070780d40b51360305000007040851031080c0058982d5204940e03020758075000304644856880c0c2000400400a0040d012026603030810605541aa140c1045058034100a1126400345107800310f902001d000780520380c400091861070301c2800d598654008134 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 351722455 1250 351721205 351721213
    0x16120f051f1d2e060f12030e190302040f06030b09060703050c040b16020109030b19050a060602030d050604180311010507030b0315100e010902030709150203043308010e010503 77
    0x2d03400025040e40c0c0e079601548200341d03c900e00000c950800040115600844015080b2540002e40040303031009500c55a00a031518650320840b01d00304003008034110702c02590080085418005824680c0c40102d02c030020b408009800c81c0c594807140102c440449105a0700d91048042040f050303410700a0030b030841c110309040f500f80381c01c000c1d242c41240a801c003451284904105410150382c800d051540003540c0014443d407030b50602d000d50035141d042e55000307400000c1c1082d001c6040c40101c0e2261808842c1d80d64040e50600c0c991102541c00344c00060305c0c466015490b2424a00001003082482d603000d4400e4480b0f194081c0c101844600b550030082100302414a800304860507a10046004244d20008942000c90740c0c1e9030780840200c44156411aa041c04400c01c0007003140441d5500442c003c40841e15841100f55484c00200340605a0341c15060042c1c00c00c0c402004401e01e41442c803580610f011180c22400d8a80c07115070140b604041c100c81c4e00183d40c0c500100030340d5050091850241c003040e0050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 351723705 1250 351722455 351722473
    0x1120609021b21030408070b0138040608090c0307090b0306010909020105070210120903050909090604030912021309030203040f06091a030a0209040e070816120f051f1d 74
    0x100781c0e51400080070741143e80700000010104a40001103403201da40c0200403d9103541c60f0b008841d000c461142c0c014208241840003110000b411811300c1c0c640013444103506141c141001801c44100002401240c0c0c14412048110499541441a18058503420f10001601c410b442c08040c9021010390007103a4051410b064580580d0340202121880b9805a60600201d00c001703030304590f92104550160a55454a41140304041d8440010124140c0440300900551241e43d00c0315142c050a85001340400c10b565810010f181040c0016103c0714001400320a542c055580707940280c88105c0b10880047c2c1001034280a10a051605c040281c54545020015141010120fa000d01001410040f034040c0110002d2202d07012901140c203403107400341c424807c3c8459407900b00c0e582c0445000320a401d002d64102a61b24041846d140000c4446100034140010b034079440794803098000450954403802612000364030501c07040c120380111440b400300003d100f032180e0041c2410f813070a642120401c0d0071001d21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 351724955 1250 351723705 351723733
    0x106060806130506060405040b2409100509010c03031e020d0914070b03060d020f0d03020109050601060c0305070209070c0c08030a0e120d0e1306140301060501090b0301090b01120609021b 82
    0x86d41d0a031041542c0000d030b0840c001c00090048200d02e0380d12050714480b0b440341c102d40006000504601070044d81c00d031500111642c800e86441c06400213090000c3c11950041021a1098002d10f00318940c072803140b0000702c440368244041c1c2e03000702d90786101c59480d40c903554100314100d2020700c14443c44101401425040c0b110790011880064001c1d4400c4284190800a658a41041404901004100c0c031029100c0e490080c0c06445512015202d0f4015080001031090098080706e04c8142d055541a19203c81c23035081110350304021b842842045a1034000301b0014485841c81d5015011200c0255143c21410f00c00410000e04070a40500502040700b444000820020f95100410301506080030494098008903203200308a0000561040c1007a80000b00e0947d009001c94450509500070b000550301ea80041d990300d9524450440d00e2002000104100c1600b03030720010b00681c05240400280c0b41001c495001c0c0ea8498008864040d030002d5200d240107010ba9100e69501c41d80d002400c89601c103068 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 351726205 1250 351724955 351724957
    0x1906080f0705120624040b120109020109090b0d060f1d07030b0709050109090b04110f0a0206090c0a0614131517190924060303080903031611030c010606080613050606 73
    0x1205d0152110150007076140c0c0e00c40e0452181c0c1c0c42e014200c60143c3c152940518082e141c0301b141613001c2040c00c0f0022a500141e40030300d11207e040601004044082e5503290b800800108140200c4995110b1b000020102d8503c0782402d0f060151000344040b0f800c0d4100101c44001c00b40c841001c0c05516802000141d070800c0500003198003205001031000d130400d022501620b82d000000700700c034900042241c06200c1010181140304201e03400c07107284d5514030038603a50b1982c4a0f00b86e140d1120345650200070180c400d4014010004c0303071801701030501301c800e1310501081780784d60071113040c19400c0d89103082e1255020000031500200d55a1020030b40c02c25001014401c01341011690304c0c0d644413001c6009100011016149020404c400d4140c1108411a014000c1490b40412000601d00c00b01045500400000783e034020204094031170101d0700c402c402a5200d44814040e16114001032101d903050742820b10842d40108803544a1001c2440c02108202010026010409000703242509000312921024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 351727455 1250 351726205 351726241
    0x5030c060a020f0129040b0f04090218041a0601031517011104030c080d11150720010507030b030a03020a0204021e1308010c0503010305061906080f07051206 69
    0x3603003095403688030200407400c01107015503803c00c540c20440394500114490b101503030310840c42c1040754414040036041105481325005295072164440201070320303501c0c09510008c84d5501c014504e100c64441c00c100020001c000711402c1e2558541c80c1c814015101020a000b58031036802d180070041820380c0c0c0c072400280c901034014600032148015207080c040380250b00002c1c0298481004030348031790b45e0745011404103019000305403850150644c1c42d0300f6140120106600130750501301420105003c5a11050b80420041c494002c00403c1c00d00c440d160b05070701694410454040c00049010700d45040054141d410700d91029000745d0201441c8000300b036020a94001c0b240d81128050317076922010031032412050080c01d590440b000000784900189070604200c40031142c0f42402446903054004050751030340424480500703280c0180001030b1800b002180b14012191a8034400519580c4985401d0310308548070035000c040d03501c0380c0f00921035440d0032028614a280c48100416241c43c00101007000a0005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 351728705 1250 351727455 351727459
    0x1a1c1e03170703060b0d060305010c020d170703021e090a0f0f09052a1201050a120f0f12200a030e101101050a05061801030201020705060c0703020a0303050a0f050405030c 75
    0x160120b10841d20980212000700741780b84c042500c8644074485c900081605120841d905d600e4a51040e14030f50021454110200c840e07120321815074216207018030364400003015101019801c00a503142002420440c640043c0c2413000945c940315a03030103214024109070400a09080203090800030704042007088015205143d1000c10a91202805110480c00c440e208081402651108030900c6d41e141010700f050507032210487d542da907600c80c18020340c01402d0082e20151040c440c1303a0030220300d5645003040c005114200c9207050703664030b454019050030340501007400500103502940159105042d080504140f120103040f07144405da50107022203080e4030403203018040d0071a020340c0c0700b8000c0c102c0c1c11850100000901c070a1a1030f500400003000f045840782d01c14210180e40983c0390302529000341c103882d41078008100050900042001941114000820034071440030003000503110031050400462003a11034a07103842c00203002426004c0140b401400300b0400780410800f1f683c0011b6000c0c41c520742 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 351729955 1250 351728705 351728747
    0x3070c020316080319170f0907090e030d090809040905010c0f0806030d0c0c090501091b05070302061b0d1a090f1b0703120c02160b0f0d1a1c1e03 64
    0x703110960795a01c07403041440302401c3c0c1b581008021050811098414503048060703426060b120040d40c0c003241d1151740807422941c02840420b00c4503080e50b00480c5984c0c0240213030750070500c400c00010103648200c1001c480e0399450b0040f0500305c80d00421040c02c80700d4903062201c480d18100c004695514404101e000070400c80035059002d103e0303d5603100d400380c941d0071014000d56071540500800383c61001206500d140d2389200480013140309500f956141a4150b01400080e00c6440041c000840c556200008007001003103891164841c43c400d00c074101c1e4003100405200c5c00034204210f43c2c004000c00d003a8800c1c5403901006094040b44000c00a4000c62030580c80c1c86406504003241c0e50038103914001c403075034940742c290100141c000031451003c0321001c0003c00015250b050300103060040e070b11820343c14941480a110100020b41008282c2c0c2e540a0301a401891020300150314600b040f21403209040d02c88107800c2c1800080e411030800c0050a500210000308181c1d4010718080c000420050419a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 351731205 1250 351729955 351729997
    0xe0607030b06180a050d0c030b16080708090712060506030d03090c0911130324231506040e01090516051b0a140d110c010206130309090203070c0203160803 68
    0x16130014600d01805002e40108030001c0d69241c00c0a08118602003940c4d020392650000f0b0130144074211216038490160740d9000b1586903000242d540f550044c0a40002e4000d9410102c1e00c48000c071a1240d142e4041d52001c0381ca82400001c2c181022440b41ca80c4040500307000c0190041640001840c0c03c50f8100c1c84002400e580141c095036a501134840d60b204484016007000017484007100e038184800003801c1c80c3c20710410011070150f0840e50900c5003242c03603803411188551003a0741d61340e0803070b800f0076882140d40780c580850001031070a41c442c1c0c010f0b2690042d008018048901c0520031181d1200700c0300d0002c0d038051040c81c03020f0501d009544c080e400003043d5443c030728100c1000b44481c22010b0340c808100b40003070003082c0c1000d449070814440b00c400541c100c80d48002c41c07100010010000c2c54180c0151185858107010142c1c83c0c3e0020b40240c00b80540d035400000c4102061004611950075595080e80110b850710425061403491501e002035200d108209010b500340110480e0f0b8460035002d4100d003000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 351732455 1250 351731205 351731209
    0x1b0f030209131b020c0a050f06040e040606060206070903020a050d062d0b0a0e0610021c03020304030e04090312021e070609030201050f0903090d080d0f0e0607030b0618 74
    0x44075107041a03800480303010014640080c1d6401403d415036180740f4407081100c10785000c0740d45840d541040b40d171080040360100201c0c1007684400c200c58401500e414a41b80d11104010002d0b1000d40d0704075881650340004226480d4103018094014800d8a4804010b030321716000544040c1c4103000701032007250070203c2c403002c20070a507200160076036128009040d10b060060f41c0c020a440c0401004c8590360412012440b98907108105005407040520701d4a0141c9440080c4030052049520b0001588a00111304031198004802105029a603544c0540d503450580b40007000040110403950050b820912a140000d4201901d41c0143d0b150305001a200c1c0710001000008003513090304002e104000103a05001c0c400704d82c001000e10b901031b4000b030040fa1101542c810480c40101c3da000115041400610800e142c00000c80408600070a9200e0404103800085000c03141030b41c103c9210940e507044d03100c600800511810f80c0c80042820304210040c00382000c5505441200078807242e40745244501e498903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 351733705 1250 351732455 351732457
    0x82505011b120c060c08010515040e0f0916032a08030315130905011a0f0102030a030e0102040905090604150c09030204112b2a08060d080d0903121b0f0302 68
    0x8a801000030322840c0c01c440c178083d00d444828001c450045626854a4040b0784e2040103c0c0c04030b644078000d1889581d28580018034084010300080d081d401840c14010301d80c08040c486102560040759070406600c103400c4e8403d0600c0030055400700c0000c070700f41308208400001c130907a58040045d00c28403a801110800240f203d50040600d00b60a030f01c0d000f10901808015800b203c0340420710000543d030540c120707041045035489400c007280168410030001c03048500c0f0740c02882d41003d5060015040c507459441901c181d80302140c200070a540100104414002422220480c5185c910710800c012188034900401032000340c00081c1c0079940760700318001005404403c071001c40038104c0407010307404840c03400c0c5602e0695070100003900c0b0307040034841ca483c140d82e0b0401582c1b481c10a05080f4180b103104106031703003103c40200703110360050505140e080401c002c180140380b0001e0b10b41300050a013007a80b0340601440c122021403c40c0d60b18200c4400a6490880e070140e421030703450300704040ca401001d5400c50103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 351734955 1250 351733705 351733727
    0x11120a050d1211070c06120b04020301060c03031a0a0515040e1003050f0708030706050405010219020c0a140609061e19030c0302090904020f0a082505011b12 69
    0x216101d00e01c07504203003607800704803295501c50b00b030400e002c8031804519501c034501901d03801403d031130507160041043d14050740d0281c9071f01a601d100031844a04900016040b40c00c240d1040340031030310100400e410580d06102d03042c211201d07568090071f00b100d00808a80d0000d01030090b98028461154010280310882003940d0050004290106151414020b20303a003954003440111003a01c24040d00d03104141012610205a540700c4004500b401301c151181d10143c0800340040d100343d5800c0104c2c0200c0030100c074682402c2046a0020300e00703407403000c06020240300140c1c4501c07502c22400c54110711545c1e40c80121200034608880c29074460710b00c502d07024010041d02250041e005d90014240d000d000f400d9a21031000c00403030714104404c0b180c044041d01a4850700c40c190b40c6c058900740000f0010720304039040c2500200040c051050241d103810342a40351910103402600c1c10740740c2c5882e0401142580c2586005010300386042d02d0084d01003209419400c807075050041c03a40a102000d550460b10544011003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 351736205 1250 351734955 351734963
    0xc0b04080a110f010603020307062615032508011523030607090905070305090c100302040f030303060302090c0705120a0c0209070302130e0601051602150c06190911120a 74
    0x544100b43c200900034441484102d000780120340b00010041d0041f142140103507071101c10b1112200c02c01c0e00181c0e13014401404034100e0900c8940754125620f00708640e40c3c140842d40880340b021241d0002140c01107a10341d0055203980e041492254a506680491000b256000d001c1c143e0941d5820404180340d03015240300d16018410801000110383c0e11105440c1118102e03c0c00304070320b440b40c060440503500100e400030f100d03502c448940811810310016001500b1141e10300107082503200c558003038481a0a91040d00043d40320350044c01035207480816107411444102450f40f07064a15900d864464070382008445134000e022131140916401010002c0006600504000c0707140350000001c0d000390850005200c03004407040340414031080a201580c0600d905844a50600800d5040d000280c00440d600701c0e0850100e644d81000c03020051301609140209a018103140d190105c2d940c0b4001c100c0c5109115010300b4046c040c03020401c034005011004000766505500c003c0303506155483e00c03414035030040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 351737455 1250 351736205 351736213
    0xe270403080a0e06010e01030b041502130518070f050c0111040e0f070e0913061d03040e0a0204030803010506090d170406020c0105120f250804020a060c0b04080a11 72
    0x1000301507115940521a24030b500040040021141c2c0c0b640d600d02d0300740503050000140c5030040c004130f281d04040d194040e1081112500e032201107070002c8281d80040d01000040a01d00000344000d160922400f10514414003a0130890b01d080d1600412a540340c0d045c038000d00a002030308040c4a01e082d044480303542d90002c942640e555685004005440084410600c01d40900c030125070624440c4242040142c00180ba22466489107100060290400401200e2580e502c0d20903c107035950715101e9000244518010b9900c0f546041401120920000e011100151040000323000246030309059905440c8217407002c0c0c0d1100340c203202040d080d0152420103890345d0680d4103c4140c00e003905005105540641d400d5030040b8100d14019030f210f001d40380074000001c0104001400038100a80056841010000d41100c0b40089060990070a2030621155001441c054100000d504111003110b009180c01d00e030034000c6080580314044800340260006041210015400c50842d11030742038100355429440a41e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 351738705 1250 351737455 351737461
    0x6030e25090b0301021e09060c01060b0c0f0607050d020f09130608010c0906020a120201060e07020318091302040c020102040b1c050610050304110112060e060306160e27 74
    0x4448260001c0c46541900c1e414442c500da140d0406000740c03040a281e03e40b2000d8070748074488000c103080e00116891508000203000c44000e022003406030314010904483d04590f00c41c12042520b0800c3c4c1e402108101c00e030301c85001c1c1700d030555110044620005030342c0c2006885000300c84074010070344504911183c1c01100e00c0c1d01c810546050764032806c00c80f043c0e400208907a003800c0b8000d803000000e0784100c20150300060340610100d40c41c98000078580b00580700004140d03848000c611883d01c8103450b1080164000700e21850f07250701900560710b00101c201c5030b02849e4a400f034659140013001080090089840d8001e11360940c1c000d4060720060a03a101c03a164a4091180ca000550f41701c010342c02410340e040a001c92040e0030003c03101e004010302076543e1442d650315900e81844503522802c105041288802c4100400031051280001409515880f40380d94202141058a8000007030700601005200301010000c154114210801440c4223175030084c08080c0d405824114580502850840c014202c010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 351739955 1250 351738705 351738763
    0x8040b0402151812070506040504090f0f12030e0c060706020d06080303130201020705091312020312070c030f080702210d02040609051c050601030308090a02121b061306030e 76
    0xe402c5500059901d600b84c1a50480000e582c1d0200f031244a400c800c0801050140f800e05421280109004a0341d07041d0801c01c943e40da0446140e811340035101e200c021410002c00310352500490541c07090b010f00610176010310000182682c8100000144560742c001005c01d60748210b81c02136401003009400341e0380c507403a101c0002c120f40140701000703d0050160303600120f6140b500d1b8400c107014043e070310003501200409aa07041030503c0120b401009500c01441048409040e011003030f4841c890300c0e030b81c0c0c91082c1c0c41803901402c9240c80c9041a01808041c40c1040a020340c0010000140347d110707060442440e210450301000c5200780d50003041100e000090200708550480075440884100766544d05002c9420b40f201142166000401812508017078010000b0030304c2522950340000d00070041d281c40f0b000542c00565014005510070301203402052061170712000900000f000101e06403039061501516094540c6807015500800c000c0c590743c1c10f040807407074808011090070302d15481c01c1a44120701c01c0c0f00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 351741205 1250 351739955 351739987
    0x1e0809030f060c030103121101020d0219051c0507030902060409060326041806050616020306091513380703020403020105030402010f03020c01141602070608040b040215 74
    0x11190103849081d410320902400002c00d5485680c1d501d003418216421551032490080c02c203c0c0c050304010100c00340b03580a02d820300c02480c804808000041e640c2a40405c170483c518103460704001070140074003011080500680c03040903040f0300c00000003640c0d40c51180075070081c00100f4029401c000003040110b0380480540c420820340780108000d000305405035030140c0d260406000070441d10441880100104e1a05442d05c40d41e407480d80ba000300e1015203c8020400d0f42c0c00000021038401e962034145011f50809000700c035045644030000c0c041030140c02068000112010b8043c1c1503815a100c0c0c80c81c28000b0b103003c09004000c0d50485400310145080400460380c032041c424001c06144c800c00b0500c07480c024402c0310100ca0341a11028107640e0755400540c0c222641c581990149034003000a86118102807007030080c001b000d0840d2594908055031318000510400564600b5135010b0300c000d118440d0000401e0703901c140c1c08107403c412036039140b02261103118001c8481c250064081026240c00b21250303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 351742455 1250 351741205 351741217
    0x1f1806020c070816030f0606050d0807060c2a050c10050c120a080f061f090303030f0b0603041419060b10031a060708040308030c070c090c0206070c1e08 67
    0x104a40304107860f100c400d40c6440300c0b029107296003d40ca03001000003607040041c03040424011302c07001488603a61000b0555290000302c0450b90140005003d40c1000381a00c00c9000103011480c00c003071000e400c03610f075000003801d00303041c0b03030b0f51400c030014200400c0020014126114030103410b1000c004200e10018040ea0400e484880340c50250300811005206080282c0b0550000c0703a50381d4849846800c2c03445084000603104940082d1114044480341d8102c1002101520300703540c84107041899420010201c541c84c003890340c0340c1c3d420601c0d0650316554500540390000d4100b240341c103020341100f500c0341c030380040b00c40c0840c041644003405100b07006c890b501c90240000c06441d041c81c043c4000504808907206034144000c1500303840c100c0c103030a08080000d881030b40d00c50b05106251940f203480d1040c1580040702c440180c8400082c8590810070840300703080040c4802481404001070140002c1d481e800010250420802124030550520440b01011000100c40c3c22401d031121095082500f1194840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 351743705 1250 351742455 351742477
    0x804060513060f0503070305130f0b01080f03090a090506030a0b0108010c0905040c08070e030307020a080c0109060f0801030f0c0504050406060504050601090302010905210319020d050406021f180602 87
    0x444000035440b03003e0b0110616000c0f281c4d40e40d910b15504c4010540007010007400c00c4240c11800c0400344002440100042c800a004141ea402035624010100d4540410b0b14080c0505800620a079100c80d1038003044107056500103400400c0a685040c042444c04071a000090074442c60345c00002910103065000302c00d0201e03180e0324274020f00c0c0c6800c10b2205851062584a0020b041c002c0003030321140c8a1401040c0031180141920301d040c2d821703000106100c4c410341000852340c1090030f28403925030308009080014507003820100b0a812a0501c05002560305100c0540240500d0380b2103400c04c010418481c0180c240207000b0003441c105030a1240c0148107030301495014501e06000b0412541c0104584411658142c1d00d0318001e604050611484820310303030310b44d400804460b084500807401840a0200002808420b0f0220203003014000d01d800b0103401d01d02c0c01d01c40704110038442554007142e110901140103440b802d003c0208074840d4001c100c41803030301e075110301c08000000030400c994001340205030307107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 351744955 1250 351743705 351743737
    0x3030207020f1509040510080a03021c09030804140103150305060603010528020d020702040501150e18010b0703121802150f030f0903070b010b19210e0a08040605 71
    0x52081803180203009180c00160080050260002074038282d040700c2d5000d81c0c401c0e0101807569523403e540b4544100d4101c1100960000e184a80900d104098080c000036110710f011344d045407542c0c440d00d443d8440c0d40200509062030581c080e0643e4007a40000c400c20382800100d41185a0301d05015848440581e13800c0c0c404d5081c100400c01c401040c00000ca00f807011091000c808048240820000750b014014040459070284a5140903a8075031040c58000d10040542c0e4880c034984039401030044240c441103e01ca247c0541da191710840100700741c1815945200580ca03a54481400d080e6000c0300000b68010005040c48000b6500852414091508600c01d6070302d140045403182e0030121030b0244681207001d04100b40000b415030b85044040b9900f2911680580b880c0241513100d60031341001c00d800c10304105030b000400ca01c03040100001000c000c131852500300041e402500328200b0703400c0f80d502e02e100c01584455a000e6901d000344212400e803540005804d0b039555072440090000e8000c101240c80b9051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 351746205 1250 351744955 351744979
    0xc0a03140c0307050a15030f050f060a0909030f0e28060201060b07050a0219030501060906060e1206040308060312031801110c0706081905090a110f03060a0905011401030303020702 79
    0x380043d80009070b1301c00901d50401c03c1e00b48840c032021070080b048010308158891201ca61140c58030321030b03940108500d4481554070701d0601c0c20300c4101c40e03840e0700100f800c500d003600800200ea8441f89055000329680b0b07040025107c0ca400148240c2c40d605007a101c580041d1900301280b680c40e800e1703042180d00580080c000036a845810014500038800060403e03000b45c000c10005280c072403081b41c2001c441124500300280c42e500d0311400c4400982100314080c0d030f0f6072010b00c4400d400100040e081030040b40c06c1100c0c606030000c81900c405015100806011407a00401d009540900c0100c80c0c04048004903a203a180281c03440448140850007444154a007013540701e42c101c82901220021300012009001c82c9181080864000100914aa0802504941803c000b140e240925405401501c0050034800c40705d041c1400070088a15145108448210800c450364501268656009040601c001014421750500034052f210b5181410041c00c00400003104058040d80a0f04045000340c5034802400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 351747455 1250 351746205 351746209
    0x1509090a02120724031515020106050a050321091810060302122d0403030b041d120313020a08060403020f03030c07120e1003020c010506030703020f010c050c0a03140c 73
    0x2402500860803200c040c0c4a0601d4101c0d19100325202c12444e5107000121650341c801207600c0e14010340c000f64646042c04a40301546642401401e01400044900c0f0b5649490100049d6956146849505000814183c1104007124040503581c2d0f4a0001d018042130800395500190b21120490f10711079a10401c6801098140c403038825100f0b0f03402e01c074282c2c034142d440e103003404102002443c0c60210381074a101c4102d0707104000ea42505028620030385010424203c01e100304001e1700e0410003040d5008045814000c01c000d000610070b00500c6084042560b20745400340016030702e80c145540650004d00800307002a072080f0028100d84128029401d503454150b0f0340020548a21003651140c107000c406101400c0403039900c0c2e0134900e1040a0f401c0c01e249208424020500d04014a6030365001720b075002c40d40b00311710f8a0a003c0c00e03600c040c0440c080d000c4076047d40d0004002403102c242d19410814550700c2e9008000c000c0121a06a02006200f003004560342e2a0174034400c5010655145140245080b65200c2c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 351748705 1250 351747455 351747463
    0x4150501030f060b22090b0a17100906020d0b101209020406090c0e12030304030e2205071d0603010f0308091503150f01020d09050405070302090d1a0906010e0f1509090a0212 76
    0x1890010f010348c515600c4e0801d403003a0f0b1811441c0d611070724080c080c6134540300d03c2140303e000115489040050b0301c900305400502c0450302810312160059144584001c07000c1e07440101000064584580054070148900105004014a0f0095107001e417500410701c8007503070031051740a41d42d0400c644103482901c81c80345040c2c5030300041c1c0300240420f40c06858060203190103000d036500d01030700d00a4208044014043c040c16110265040c1000c12540701ca4600e80080300501c101600c0c41c140d864505c3c6500d401618211031415100181954002085000c071a9490903084c40e02400b210310308e10703240d00300505860002c803020b26140e4400c4c800710f07001800c55400400c00c0d401ca0380c0680c80c1d0301046454003042c4009004c00034100400c15030308100020250f642c4041c03400f28940980194203d1070007461040c03664000c05011901c5581c00301c00100301b0703107079070301c000f81c1c2c6c84000c1c01002015500da516086140c401d0004035107a114882a003007020b101000945000b07018000c6030703402940c18000c0f80158803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 351749955 1250 351748705 351748721
    0x906050405121c1128110a170703020a021216091802040903091d090d03140420090c0702090f0c0f130e1e0604150501030f060b2209 58
    0x6054039520150f07007840104e038040e0764000300340f14000c0c1c5003045a90540000c800068615004040882102d004040c3d20100b00d60b041d5020600500c401c40454031614039518800e0490b480b61140002d2260415109001141402c2c6d801303071510303d0f138031000e00f02c0d42c0e260302c00103850b81a0000e20b8000064241303054004c61888cd401d10001100c0b9030704607000d00010303220030401a0144452010001441d40043e8494142500000c0c2c1d030401e5400c0001095040c00c00900c6060201814801c280e00e1203c01c100302603410136030001c804803200340d150300d2004444103480f03010f03030740980f01604000c0c000300000020f2000300d01c21510506140c0d5007140400c00408140ea111203040b800f0f00c01c928144420100602c002080c0d070403007c0c01c0640d02c1d4000d010341501264061484010a01000080c41c0054400c40d00550100e07018405210489504a00502103116142c1010349400c0d00c140010340e264021006008014102075403510b100528503c00e040440150728146110303140040d96030751511070700407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 351751205 1250 351749955 351749977
    0xb040c080601030f1508100f05010e07050d090506100315050403121e02030703090209090a0b0a1a0d0302161e09050405032203020f010509010f050d0609090605040512 73
    0x445450711070044008210740035159403000d80d40c0903600b5026a039546890000c0c00702c10018080200918030341c1007640e107510102c4441c64100380060142c4080c4800722a80041c50f40350117030300c8018441419001c1e10b0216400f5140380104428403a1010705000c218003038074064030304140c00f88204021082250303030841d0090300103062108481c1d681c0c045078001ca40c5124003079440321210195050350381c0880c2d00c01d96500c0042640c2d10076400c114142000c0507903002103e0805408092815142c0c40c080d0312000f0a0050460f40e1034103c00c084041132550381d041008090100d1041c0005454080d5490742074400a40600400100000f00308420901801c2440c0d0710661085d441407510340300c40090800500b08031840d0200b0300902540c01d2481c004c45004c25016021149503a20b0f40c018010424000029607040140410031a491642c020b01004048900c902d481591104195000d40041005400401c102410b100760300c01413003041c0c1c0015003d1406a41941c080e41c0c00030740005001d10546241e04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 351752455 1250 351751205 351751217
    0x130501030506010917010207020f1f0503190e06010f0f050109050f0a0e100e0c070201170403020f0a0302100f0204050312161e03020c01021b190e010e07030b040c 71
    0x100155100c0e401280d0007000604004482c0381d01c54070400303904049850498600ea6020074204254a40584180c01d48041a201014054024a050011070b2000c080340810300a0000204400d00320300c4c0314400043d10994410890603040716506500d0f41000e108520a8824048003ca08801542c030142c04070b9805840710003003103280406000e441ca401103c00c036801029410001424029014102e200c0c0340244402d00865082c480100c01012000d000c150081c0010b020761030040c0d030001c5085040c02d000a00c1b900b210340e41c901d400c81c500921180c07a14520300403030003400c0c10550000ac2c0360503050030784042800328616020200d422802188074a50f410f40c0002c0c2e8165802101d00d00800004060304048040d07010360741c80318044c00c1000c3c0480100c880c000d40c440703400d040e810b0084001c260024400b400c0000ca41c9003845101c01c3e00d01c2d00035841040c12a00b580e01010020038044010321300c1c00b00329035083da55120007258607072040f1842c03400f02c0e00700700266030b092620f88250b16001010303407a18 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 351753705 1250 351752455 351752459
    0x130203041b080c120123130501150914040c090e0705130c080105100206131e030c02010e0901030804180216030804020306090d020304150c020d080316030605030a0204090f0b0f15030313 81
    0x141486c54400b038074618203a1422944480482c1082c00b842245681c6540c403071440b589041100000c41d0b05820550210b00c122005000c00102241c00600031a9001000469246c42c42c0349030310b04028a40e4081030380407800e00b0340c0740c41e89409500101c3e4400460b032a18500d9a0381d50082c003481940440c1c0200040c0c01c0f200024400450810400d424035000d1200c0041c40305543c0c01d0b403410054050015030100b01c61040f090119a40300c2a800000c80081e11a030441d0351541c0e0321201d080c0603600030700e00a1218561a0030501009505070741024070f644826000b031680c4d40c18003800a140640301070340a409071400140c48030400140c46125418198000c5141c5440c000e03e101d003c4660494182c10007603014040b41c003607600d03a5242070345603003d440707920380d20f0401c42070703000c042d00c10f91315a40c084c076060a80c1000959400324480e9481501541c0102c4d00c9046850410503000b01140c0040c07501040200348141e2700b1a00a465101e4200f15071400d4000d40f207403041503580c4c000d20700c400c09900c1c205442 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 351754955 1250 351753705 351753761
    0x220b0a0e1305030409150906060f020c040c0e0405040f02040e0604050c04020a0c052a0a0b070204050606040515040f05010305061f2015070509130203041b080c1201 72
    0xd8807a409004100fa00c0c1001d45940800d41038503554021043c0035425045c05001c04441842102c0c0100024105407c182008000203500c414500f1100d910956984902ca0350003405940f03400080080100108154075080c40c0c48903425040c1042030340694038000c4840c4500c10006261b07401030f5080700082070f508992508100295000400c0c5070104034080c00303007000040303042142040549007a0a408040e00f84070940100c1c1f081c20104252082c1181c650401200400030111036110707405803404201ca940d00800b242e102d10030365000c0d942145254440c0040100d045001c1c2003075400d00240076214a5550004400b6207100b1f40d04560300c00e00c2100d0391111003841000ca919a095035003800c891209605004030103103001255000e186421140310103510000c00e00305030740e01c5a4036040c000d007410f0354075011640300715807861860401a40003010030284140c52842c55101c00c00c40d8028080c036516420b03410340300c180250060f0700810440920880209060081580c444400c0d24040303655000700c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 351756205 1250 351754955 351754981
    0x50606070809030127032a060509011d0a0308130209190b04050901094d0613290a05070f1a060108012903060f220b0a0e 53
    0x840c5606641c0c4504a900c3c4200b00001d0780b0107981e0310317200c44900340200d0501414001d184038400d8000c03842100c04040444140005c28500e035045680000c0039603890043d80c1c010a240c2400140c410301c400c1c00c24072300c40ca000070300c0c80c0c2162103036a8940700c9484003030350000b1b0540180340082d444840301c1c000460070480420001108c2c81960004140c06400300045421a4801d0724130a0316a5100c00c2030005000510722030064010140c1803456165908000c01c0c844032080c0c2000110610f00c0701c01000030b260300b0311a42c1400010003403284e40d84101e0840c500d105c0740362600c189100c090b000c6400c00c892904028601010b40106201140b80580700c6404a030f06600c0003200b11000e2404060f002c0100b1200740d140210102d8007800040c1c24106100050601d080583c4503440070703044414000001044010300615400f101e0210341d849440701310005da41204500109500021b10191403403401e00c0c180155000d500e000b40042220714450402c3c002028000e00900d8039044205001c03a40c40c0d90b0740a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 351757455 1250 351756205 351756217
    0x2070306020d140f15010804020d060c0908071d060303130302060c1504050106050a230d1a090d03061d0417070f050105010302010206070306061709240a0f0506060708 73
    0x40009080d02c5112a010fa0400c0a507080c3d40e480269108000e8507140ca48200c4402500074204804d080c61310b503000910607420240c00403d1240c840e24050704083c02076600e100984543c41c2910440d9468000e49401408407602c141000841040072560500703010088800c0c2003d10946182d50609640901055034440e844100c0c2d00d21030310401d0301464111041040c041d0340720340d0000ca0301c0391511040041940c000e400105512001e40c0d2807103c00000d003a5550a00503060720a446200d0160070308480541068200380b40d562b0785a8200300c6104800f08040c40e81e1a01502c04024441d01d03100b003081b1859000702160000d102d14804240070800d0800320050000450b181e06242250f19030b50300410400565084079269100d10050085680501040340e1104080c036040043c541380c520000c11004400401d40035010f03440c40801c0d0358401c18048800541494000400c025550040d440703885001181c20f803c143d803a10400210034620741c041c13140261030003861941442d10a440c0d501e0b6540c003135 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 351758705 1250 351757455 351757477
    0x406290c0102070f021306260102040302060705030307110c01050f090d0503040b0414150301060309020310020a0906080c03010e010513020d050709061709063603091206070207030602 80
    0xe2000c06809036090008084a5105060f018240e00c0c1074818050b42c980c4030300409070001d08208007805052008042641079141662240c2d80c010300040c0342c1c0c0d009120700d41000e03400c9a000200c0714184400000107502407201d981c0c03458403c2e0150f405040e210040f143d01103000038810000400342170721890103031218500040070701108c21070580d100341c5554866480344d0056039020504028076400d03000807001017482903400201c0841541c804054503c130501841c0c090596400168040d9181004020461940c1c940215503c0d40581710141901441d8070500000031180d90000b01d103100c00380146c9041315811040c0c88142c1e42024100420b00202043c05900d140d07003031001c204000018010039010b92219220202c865091604c01020010030100ca585d003414140180300c03070307800005003081d0700030300038145942f420300c0c1d801d90661501240b09400e00c116208086440d4540c8012000307102c2c0840403150142d10721050500c1c1d0351541811955000560825502040403824a4005000d50031032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 351759955 1250 351758705 351758707
    0x809060c070e010f1d280209040906050a0b03151602030f040b180102010e06010e0a020702040509071e081c05040905100611010207050c12070b07030804060b040629 72
    0x342c2c0a20010844241d0190052042c00c0408001c00683d444800c21500142400901c00d131402082582c1e04c46040b900300e51202c2081501115034444075410ba03400050024000c0c401090300f400d10070064503050350f10740b04003464041c200c2a1844e0010f02100c51103005145903910f543c41e03500e03058200800703100d0300065004c100070110016a45100500c050304415000c82d49828a50905284124000c00110306584c504000c100d50b5410006010b4111401e00d195100e10b0358400e5058400b900034040c009405ca41054207006140c140490420191842c0c4407a000c080000c651851704c00c0a5540f040d52401e8001e0040c00c14602002c018201e000310040c101285400c3e929044081222000c550a05c0c50082c0c2c1501403145581c450701480c5810b152200075400d04402d901c0e99512240d4060000348103654030b2044c04a913490034010540240550b04105840d11034500380500f1722b0000301c804443d0a8641100e0100c03d00d000d2240720280c64914580c90305006c034070340601c840d003924100314400440c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 351761205 1250 351759955 351759959
    0xb0307050907020a03030b10200127201005090114070f12260402040605030102130f0f0617070c0b010b0c0601080c010503070f0509040c27030809060c07 67
    0x16603004080c000c81c203d5000300481c0c1c2644c00d00030101c0c0d0b01440440d10480c0140c0f000101c1c140d20551070b1040d000c800b08440b9074001540c1c1803900401d080003c0e10660083c2d904901150680600d441c0340c61405201c0c407400c00c40e05100c80c02c40407407000d8552940240b41075001241c0c40d12a00191070071182c1814912000074408400e40300907000000121000e4410840c8007080142d006100c041c400b009040900c1503001c01c05c000b14980840c1c9050401d000b5000000500b5552030350000d10050001070300840d6100c0d0300d0f98203e841e1107a0740c020010401d80200c3e00150188040c4102411035900e0307075030220b0841092084081c0c4240243c50346003006005840345001c90f0f051107085000341006c02c19259a01140e1340c02a040c00d00c140d10003205a00702d00303101034030790740c0200c00c80e45d104400d4034045402404c00b00003965a80034400c90300e6003040c40c012040d40d0180c3c00c0361f06a48441011900d00340708523098220fa032842d4285020048c5409402e100d206046c0c100780001c2c100959106040e140495 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 351762455 1250 351761205 351761209
    0x30212130504050c031608060105091905100201061509050901090c0e03010c09081501350102040806100b0705070315020c150f090a030816050c0102130602070603020702090103060b030705 82
    0x540f00707a422041280340082070000e41c1715803980300102e081c824113141003103180010002e0305034041c01c034080780910302c4000340143c6a12100315000140c2001040080100b1314460000e0003000d55002d081030115607000c4845405001d0240e46c0e0464070020f0040340b07568240992396010f0249202540203110340d007442038200340d80c01c0c010b040440741c9a80c0d9064031f10740381004440c83e2606c1c9800c011003446a02005100f01c040c1600f14482c03500d248001c0c280380c034000751210b0485014801c814801c0f940f0104000c00c0e05a40032850501420013042486000d40e10380e06012014402c51a0050543e40070301010000203031200380380400c0403801003005040c1308241000c24108030f09011018610b5207250304000502103400c10a9030007040900040944071655a400f0381448806807a10040c0c401190112031524401e00c00c40d004419448002d540740c1088000d61225410781b4040c0304054040c001c00858200d02c607100b61801c0d01c3c2c006141c082140d1030743d142d240091545a5032685c060040312400304290b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 351763705 1250 351762455 351762461
    0x40e04060c0507061e0b0621090a0b09010b36040602040b0c10060909030c08030c21040b18120c030c06010b1e03041709030a02100917010504030212130504 68
    0x180381c032068a003649903003125035000f12105864100d225036010300440c3d1052410702c548000a12807410965200c1c3c40d0940a2751501114000082142104c1e0f01008106401908405804041a1841710b003103000f00310403d03c60007810002041c011210340b40c0742c5000300c444003040d4101c0c1c0103a40051605d515401c91240c0d55108951817421070303008072160340c8040304034072a140003080ba0f60000c0201ca092554001c00801c80c17100040c150540100201e40042414812038102c2140500d400d080019229210300c13407007000701c4080e2164030071000094032204403c003990401c4010103010345600c0c81406c4401280f40c0045048480c00c0c8024004c0f851000c10400c001c0d4040d01c0c00d415010f8640e0302c0f11020040034018840c0e20b180c1e05601380140400120440120440d00042900c1242c5030b510f4840440d2a104c002c0c00040e6104041034400342d09150442401d07815501c0c4085580b0320307290800c09160a840096400600580c40b12046a0000e026000503100c0300700014a4281103503a504001016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 351764955 1250 351763705 351763721
    0x20f010e01140d060501081e0c030c0c030403210801150f0c05151014010e0114070f060b1008010b0a0c08130b18010e0a05091b0d0e060903040e04060c050706 69
    0x3d980d5100002d20641da041620960b10160998100100840301c40d008201d601019160a1a0400c04804105442e11100c15114900700300c00c00c60b51600c0d074a06203850111511900b0030301c559105d03c0c81e143d0300351081c1410303416541c401c21840307098600e00e07200701e03081010103035036104200c102d6140d400022400d0042415400e10464005400d041c40b44060b010291590b1041003018640349514032a80d07040a060040207109090000090001c3c01d58030040b442484801404107402203003a40c00c010207540300911110090b1443d0240045102058569036828025036055520a00415268034800e01010051910520400b81041e80e440f4440c2d00d6004240c00801744510040b80007a40000c0462016005a60919185840c40c90003400300301a0385032801514050803c240008070080c0c03024a50849890600030010781e60417030711328144020040000c0304001c84c0076210100b00710140007c1600e09494801c503100766283c82d01d9641000806101401000f4400b042c81820040340300c0d4400c0e210 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 351766205 1250 351764955 351764977
    0x5030601030b090a38090a09050d2f0a0204020a090e04030207180b1c050102040f031a0105060301030b1911070b04140601230607060509070303030605030a020f010e0114 74
    0x1401c144042c0c2c1c1600311320816418409185141d6030010096040803415005051050b24406c105842e8645108041c0002c03d60103400c6116a20340416070903488040d095000801b40c3d015450b03510540e42191070400300307290f500015805680b0b40809807405500400e04074049041942c402c1c1e54544210718074030390031503058000d600b200c0802c0140034104044880034000440c0c040000c1c0601d0390000f10b60046a50514140e01400392a0000704a4254101c1e000703803a959145042c0c2c255030b071030714040c0304160014582042070060b000042506107001541e042e29030001c0f4085082d07403a4203101072641002c01480a4503a100d802d040c0300541070170f0061109500509826406107418141003600b110030104514142d030044004100800401c11507880191003030582703070940c480e140001442c0e409200c03005065140b5001c10304c00203000c001166411a840382c4c80c144980c0750b80700d00b050303140c3c1d80032840030b5004100401c40ca1019031149402444010b01414290b9402c01d140c04058496048283d800b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 351767455 1250 351766205 351766211
    0x90302011b0515041e020a1214120702040b1e15040306290a060917010b092e0b0d2304030801170a20031c0305011406090d0305030601030b090a 63
    0x2060003001a0108110f4000018960a6801741d174045402d08500c0d12580c81c1c00300d10000b000f0104442c2d18050304150500e0012903043e1106d0314903e82e415844824104d00c124a40360360791100781442180c0e207000b002071400e4000c000714200c003400742000b18549804207185007004040700182592065600c45000d501181c032280c10a60b5640c0008505501400e124450901080100e04e41c17224502c000e440314580405901400e592241d4050310168054941c005003540400890180507002c1030000704240591a600000c442402e0000f144607016043d18800208075014164520f90006140c40d80900c1a151008030200d240309184241a41c0c200c0001d0224001000010500000bd02c000e50394180034159050103540c030070501501d8220080032404608540032a03c0d5010701111640040c0b81c15682c00a1100c2c8a0040040000b40103070200d15441100d03001c42402c0c210b082c0c660907100508a410ba0901e25201070341c0359000103005904040d101e1018080503100c2d009001e005000114000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 351768705 1250 351767455 351767461
    0xd020a030306120f064d0c0304061b0209190534030e0a0302011b05030903090d0222020909060301020f0a0c03050d020301081506030d090302011b0515 66
    0x1015501c203984001d20f02007000701d410002c114580d000c920542c0c2c1c0714600007801d0b840c0f010250200c0c0d29115102c0380d40510501d5100c070364480000c0710365208041204503100c82d04090140c5c440c500503a500611a5407080c04203102c501d0040030203901ca408800440c0000449980c00202c400c00101c902402d8040c0c010f50030031940c40d25005079900507046d20424041c0e041111081002000000d8000c1c1150000b0a5000c8465010394006d02c0c1c0b824800068a45180c81800e02901a003020f4102c40311804110401c011150301c01e0080d00c3c09000c0c020055880c00140e42e04020854129810a0343c0c46a6401c181170301c0444141d080140309010610090386072003110381001090700008205078066401040352801401c1d0100484020f0011810509280c650303d050460b020302800316800c1c000e40c8000000300d0007460005000c12040403080070410b6559070042810f45411308800c0100101c3c082c00002d100540c040c5c1e0030344a54002c520094000c400075904d400703190950441d41c10301041894014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 351769955 1250 351768705 351768707
    0x90e0f061305180c0103050c091908060412020d081b0307140a0e030f211312030801090b030c0a2108131a0903190615080606180c031f03050d020a03 65
    0x3600702c01d0313003401c042003585070800e0345056910a0f080c1252096a01400c00c03e22500d0012103c00680700d0801229440d1500f481c0110030300c481800f495000d8820410b0710989503200c0c43c0400e22400003020340745d04241c000e07804c1e445aa04003800c1c00701800307085580c1010807043c02c0c0160007500115603501e4283d40450080c14100102141e2100c21500305000c09017446009590040045841c0b80c500345e0740d01301c81841645c50341c142d034024226141120050230141135000b00142d0581e020a2020414000c1840030107649209000003541c018034480c4080281400d02c0100700f004141103410b83d51032007060760711041d45504c641c1603943c1c0d00701d00c0001400320403010030650110100d0000c0540c43c2a82c01e0300000d64170550300c80a0324549160035900c0d01000700c81e4001c0d10052040400040d0780b10b0f110031000c1e46821003105c42da402a00d9041020400f1055091030034051520001381524689039940030040e04039002c4d220500e4241e8850700000014010000710000c0321803603010302118640c51030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 351771205 1250 351769955 351769963
    0x30c03010509100e0c0d1707080f04030c05061602100207030203150a0e030703021b0612040f02130207020901120503040b03090d0f0e10180b0a08041101090e0f06130518 74
    0x6000c40240c0c041e19080107186c0711348038069029500003000000c00b00c0c2030f0b000540c040c40b410a0040c103260340481d45101800640002d0300030399203e410310404103070700c0b038050107110b004000d10711900c003662021707c02c05401c1100405850207254819500b8042d280e40109261514211040741d4002860003000741403481c80c400d1020320441800950320700000c50310002d6444440307890041082010894150f46580c651003100c070103001402500246103414140701030380c01892442640134032520f8000c4800580c146c03080302c4659900601829859082500d4071003541c42a100c1240e1512040001044242c60040070718400c6442c5c1c0020000d5502e0b40000801e941d0b5507900d40818050b84250b021500c2c0d640c1c030408207001d426481c0c141000d42c040d040c1507c00541a5003c003d0aa5001500f9400b4076130040b4058400e9009403c80a8200049001195900280e101d240c841c05540004640305040503c038498004e04010051507419076100a01d0302100c0d81aa030084130341c0d444d25000d40b20044188 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 351772455 1250 351771205 351771221
    0xa0204050702070302030304090c03150810060602010c090e0901020c16060e030604020a06080a110d0b0102011d071505071b05010e03011407030c170a0207020a08010207021e030c0301050910 83
    0x2c8003a00400340755501280d078038081d60050f0701180303888440601d000d034400e5020720000070f880030054207116644c1d07172895201c500c0f101800c1466810418040352940c01401050b41c1c441c00c030b40d1441c41c01460b00c00d14424440c4040c0910f100b0755000c101c1d0f442814420008000d5840b1000401d080c1c4610b0a400a028034421560141c040c1d007004080001603958540d00b20110b611500b030261480d5141500c0400078003040700c105006030004100c0341044555a40700c0d4445030004c0e0000c0019810060300341070036a0082000380320341e9001d0350b8107000c4486070f00104204001581403160428545940b000b0102c0094900f680c1061a4110308112941e0300881000e01c024040e0020071030701e00c0c2210011099600148260145a01d42c0301d180c1141e8440c900c284150344020502c90f080341443d04030341c1d006e50312510080c1d21651100c070011800324410700c200d81d626035009298014003081c4000c4071820100c1c40b208113526000d00180c2001c2d5440a01541d4403d108103405420012080c41419007200d00705 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 351773705 1250 351772455 351772457
    0x190b03100e0a06060c02130b0a0f2105120a2102030601080a0207020117060a0513052d0105130b04050a051611071811040e06030d080c070b040c0f080a02040507 70
    0x840f80400c00746030032841d2800041c3c2c055803d0000d0140c10000100074100010001d50861120040010016584c000c220103507000003002c13075032280f10383c106540c072003502c290081d00300c0d009000082005145800141104202c6003031070031881781450000610341405040ea0301c05c1940000402c6842e40c1c0c071511041d4072011110b400c504104443e00020308000b5051001620b034414403010038103595425041c5401000014102110b1082d0b0000c80006071105807081c090184689429125a140c2c0445000701c0048040c1c040b5030310703842e000400c44059007003052980c19039600c1f140c124560b00d4030b016185c8980c1c4081000705540c00d10040141d018052034904104110511428956400340030604a0446130200e04441800c07509140c3c600c020252265510352180000400107200304450401a100e51011810744c1e020843d80300068407201c0b4200d038440c3c00310101300280c2c000582c82466041d001402115a61002504c5e0060280d9084580d002025070780d004104900c11460039014888d401141c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 351774955 1250 351773705 351773711
    0xb041203030c0c0f020d0203030408030d0906050c030112030e011407050a15150504020702120a1a010b070c050118030c230a050d0312140403081f0e06190b03100e0a 72
    0x450f80364004d43c0542d09100030303ca4812014000c4c1555020021758000c0c11100c801d13a580c234010b40540d01c0c001c20070000111802c9040c2000150191603050542341200e01ca0901c003044084207a5003169805a000c071414140255281011b01f02d40c0550003074400039104030002c5c426402141000c1c0024102840225142801c104180e03c68981181d0341d001105e00541e005a222005031001403119041c080508a45200d200180000d00c112980905002c001c0d0039038802c1c641c2d88940c8810000d210f44680030340120720f071a00401084d4412034424072424902d029501301e280c2c803070b541c034251940603500c03202340034201122411030300ca00c2031281a08280100d07060145d140c0f502c0c01081c44c0e4040c0302c0c006030034019511220301540d0040c0c1c2080d814034010412601e0b1610349860045d1400e18143d454480c54009503c0020900d1241a5050305907200c50702055620b54840c02003014030307908607e44400c0721084880005c0c2e9003003a040654068104182070b02981030900706031000c890310080540340030a007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 351776205 1250 351774955 351774977
    0x150614060304142a0a240302300109020a020a030c0510110a120204050a1401050d090b15030f0c060c0f0f0106050103140f04030513030203060a0b0406080a081902070b041203030c 78
    0x4004007801024500c00302840c6c0c0103d6000c2d01a8001d00075441c020340c04410719404031804426202c281c401c141c600d440482220f903214441c0c2c104034020006000c025038041e01440005c0f81c02482072081c6030b4450411280381d5010082400c00795a0f884903041c02e18030007c600001d1079a040030210024611145045050500d0217002035000c0e031051041c043d464071090146d01c0c40f64412000c44010902c80e8005000c9441c2a1414030f003615003c86417400c5886250318201542c1c50003060104035120410014800c104159040001d10345c0248284c1c0020321484c280c00791501010b0212a00b003410078400094203a1404001609484c014a80807200400190411040301c1c0c4110300240c2007509072810035207801d9684450109502c1581010350302d0f1080004000342d183d040e030485842001e09407014040300b035841501c40d603150300129004190138400d1008484690110343c04c82800a000d204031080f89544103440d070240d030311a800000c00c1c4001c86e42001e0038107415005a0440c003042d480c3c4108401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 351777455 1250 351776205 351776219
    0xb010311010c0f0c050a060c02100f120c1706040207050304060f120f05180d02070612090c0806040c1a0409090c03051207150614060304142a0a 63
    0x5000052252203084850140c0c0e0344500451040264809030094041c48076081c40080c40010340310303082c800c170302441d00400d4041c403d00b40c0020080d03000e40ba000d00c1d426021000d540700102400464104144501007010000036401005070315000303515004015920480d103645141d100914440c001d600401c82000081e01c004111400c4070560318010019582140048901243c0003201c018040c3c05d001400103609501d900180c05a0005c0d0b041c64168a007507101075803a912041903000c00342c0c0008008008140c05211071100020f190b05002690300e07001e69556a00e0311032a00310384840e070b0010080204000b2222011400743c10814142038903035500803901c40c0c440c0300d10301a0805041c2c58409036020400c90412650203140d001046e111701c010104034100b0b458101850580c2c11070500c0390141000c4a440c0b0905003581c180c40903c020b00d01c040400d0240951024104a8034988111080143c0d035030248169040740305c511480c000f009003089140b00c0d40c54030350f02d0070a100d0641100c00304403c0f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 351778705 1250 351777455 351777473
    0x1122180f0210020c091006120b10051e0a030c140c061501030f0606020102030a110f03070302071e030203070b060907081f08010e1011040f09050606071515080a 70
    0x32681110640c020602e0018100e041c007004003007590304080004184031250149041c180c043e2101a0388168032003a030b121a11064941400206410004421002100c80c2c403403030091254a5a0420148044400c8400310700383d80e10030070b0300f000002d90b108070131a41a0f07440f6442c120100403092072141040c03190300810740c036110090820904001c2524031790186900a400210354441d03407900c10884c0a41d2410043d020794811698215690310b003a10000400c5414000d403400c001c0106a01c4e070555450040607002913000343d00a503030000201010041c9131000804c1121201d07c2980a0340d10760f41c0300c0c0380041e00010b015000380e202d540c0e1a0100666a58842c03441680249101c050080045540c1c07030256001c3c509401c61851542844030f51201002c000804021104000c00300b01b040c000c2845c06000280900c1c041d4800c1104110006c00c28440c50390803203904190010300d01c5140a00d1a03071008400040c4446001d09070340c54620752421021134501c05030050400c48050320440d00b4641e286404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 351779955 1250 351778705 351778733
    0xf0608090d1b020d030f08090a08120c070804090906050c0301050d02101e090f081203180c100e0301052a180604030311010506100c030c112218 63
    0x4208154030008400c040c0da84641280070b0b0060a2404400d140f17040c000c0c5051610b0130410045000507000c90600040020b20b070b107046800c0032060b81403d0303485130444940c100140ca5074290745c2d024001c607000708482200074002005403000000748803501c2e241c80b5096920040c4100701001d000d100401c003c0c0c60b00404c51581c9030341250b8005003510628400c0d1080d803612900c1f08610081c3c91001c00c122a00a0103820035240388480c4000c42d940d8500c281c550f41c190140d401c01001c0c0741400414216410340480240040d003640680322500c01d400301180003d490411801c0008641200700080c2c0d04080c401c00d5040040d00c06064a220380010b01100419105000c210046034009211700404008185004641c240208001c1d43c40356642001000910b180c0e00d07140d01946048041041c0c1d1034003800300e841c41211920b801141001d01e032400e541c2070559050a55500c1012400c3c101251f49000c0c0c04500f507038000c01c03c515500c100c01034200850f0146030350310000b80910f91161004c100d903254500d003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 351781205 1250 351779955 351779957
    0x1180506010e15031b0c0102250201020c010f0201061e051807081902090d0302060f0f090a0303020714120d0c050405060405061b06090c120a2d0c08070f0608090d 71
    0x540d036200c581c000b41302055a0802c030369117104c3c0442e80300d1340101c0c190001c0c10a0110000c0c601c041070f0b0810185010403121980080c09030f4007070207110501e940035608480d148003060000003151640e40c04000e43c581101d054080c205d00707010500b80020320b0010751080c003c91045007140142d2510200c0600004000b0b030030700241240c00755000c9003020081d0100c0d42ca1a00c050510401020b9a02c1d001e951210142d85061440020b0b8000500b80d065448216200d0065113000345108211900c09074020b42c001002900c002082d10490100315104010010319840c00440f44e5650f0035081c080700c412507002503500d80821404010420860b50b82400362029224129115641c1d0030b08407140070090300940340c4150b564001c02d41001a001c80114585403c01c00a80303811450080c07468985031034110f54840104100036417000310300055503140080644c0180c41c05130001440041c1c8460300046070302c2d400013991340c0c82040207001c0c034204140074074020b0080d030070b02c5103a50400c990b41c240c42d4046100004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 351782455 1250 351781205 351781207
    0x1200c070308041d09031215040912091701020a02070b250809040b01050a0f0c0203210720060d050603030f0403080306120d0e090402031501180506010e15 68
    0x220012051001000035648140b615036101d64078018024081e50601611490080f2407001406403200030088620003607280c012041c440d0340c1c1610f19041000202c5000b0342040e5244c580788001280c91048003d030915070384170758203107a28160100c20000010500c2280d241d00501004030125000a8903105443d6890051900d42240241c1c68800080d410281500503103204881400d11110034002c0031000700c207a03400c0c44002e058030010340d0309204903503540d400600d00c40041c80c10b0901c900d040c46001403009040c1d4424035a10048510b00b04980030840900a8000070f24034104007030b1301540c6144641c40d84103000f0820702d8074002252070045c20701c04140f5580b104001029942d09004032140303c2d885406142c1c40c0c6031207013041c45d01c130780049907a18060380208800301c0710b00100003000817110ba5160380d0403a031400d001c0c061240d01800507000b2a014401c8141d64007148d00c040700c0c90b43c06044444201118221440d486070141c69001e4041410300043c09040c080c0c54540926522403c6403881e00c0b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 351783705 1250 351782455 351782467
    0xb0f090408070602030718060807080601031a090718050a030f03050705010b09160305090c1c050304031a071b08040314030c010c05090307140f010e130203010609030b07020120 77
    0x6070a51003501e00041045100008003c0b0a80e000640e140130b81240c02044030400b5140c541c2603c030024255440b10100c1c0b07607840010f100350312941060b49840b24250202c1c9041d4000303008a04800300654040e00811240031402066115107159100140421118000c9952941e00d840099144c01c1b003010b42085400548034041c0a000d40081110f041e0103840c1040741d207000e854010b8070907548600c10700024140004503010050000701510f8004004003403443c07070b14444049403c00324161004072080c0c00140000408141c4003052580d0310b09068503510054a4151030041c4480d04000340c040700300c003030750088a001c5104a030a80d401d499020103ea00441e0900ea01945580500f0b000002507608021113001040d17030189c080c0401c10000d13012542c078151030f80c500703c08086c001c002e116004010010176800940c0f29207600c100140c409008103900b90f42c4509180d0036a40240c0141000c186025400c004115020494a0303100340700c1d10003002030300e509001e881503081d6940d42e0285aa103010840c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 351784955 1250 351783705 351783713
    0x7120314040e0f0115020105100b1606110c0607110d0318051903020c030109020f190f0305060f060103020316030c091211091b0301060c060906050106030218040b0f0904 74
    0x2101c014016048003642c5520f000400c040030314400340105040d254580b0502d8216900500540c0d004a80513009461110306000c945107082d001000703004018900710403001c0c0407032142d01c03a05280c129203291041e034984800c0400d52502001030203a0b004c000d01441d02d019080004030700c9403100911741ca00418101d01d00302e104c445000f48250058603502511030794080c22070080d8a8555158880e400b62120700c0c103444200f40c22607601e2213019411894000000029181140c0303500c08016004101000c0140c407054102c4101e00242c00407103a6034000e909001042d151205841c0d8466001d00c0c09625520f0150f5245d012403030258600e10a06031500c980f401124040c044003009009102c014640011950a00d58489000c0340551030241d028540410702108042000d14480c03001d6420340c43c42c60b443c0c01c0c411151040f0018054a0003907035407000c00c0000d81c41c2e019550003800150750148c8c0761001480c071f0081c02442003160303a01c245e02d0f1100880385a101d45042c41107241d800c0750b01c44004c0d036407410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 351786205 1250 351784955 351784957
    0x80a180302060f0a0f0f0210150b0c0d090b090d0602030a09060219080907081e01020409090b0703051f0b070201050706060e18030301350114061207120314 68
    0x8020b40c01000450120b080700e00000142c07031401c1e425038031088108401581070b00c40140842500d80181c0080c4442c140c50300e1190404100e542c01504880c0d5443e40e1245600701c1c40e0000c8903207a1150300010080c2a40d1395102e0315003c05844168000380c0342850140000c0c04c1a201c8110041485401200042d00c00b0b14035800a0f10160304464190b47e504a1a94604400c070310035084000410f0001c404100c0001000038030340c0a4600c0e180061415010100640003960000741c3d16695035902040045400744090080150940c4600761082240c284000040c0c00d8680080804020442d101c4460326000c42d01e00d100c038103c03074102c000350b603580c002030004a415118109024050320700385603000500b14014040706101760041b01c0e02015810000300a591248428415010301103040c0541b10102c0b07980703804680c4003900d00030891411000c0580c5290039284d035a042800f804500e40100601400c1c5202420321441d49a80a004458149058070341c0c0a4080800079040108111160303441d004004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 351787455 1250 351786205 351786209
    0x20c011215140411031b1303050f010501090b0d050d0f1704140d08040b070806010c0609050c090c0c210721120b22020d0c050403060b0607080a18 64
    0xc1880d40415141d0007065070b0444145501801549040c010811541c180e01c1504e0040008008900c900324546a43c5185034000f084540e2483d41031070700000c0021010403002480c5030040c400800e032980b40040400480e4007035142c3c54003801e012410040000c0c00490101402034070350410341061804241c08030742c00304001021589043e800c034180310074842180303da1984824883c2c02c0300c0107152040301c101d444076010740300108a40100008a014180100c05240c0d202138103241080c85001903480d054280da0360130303109450607006841d10245da401c01d00f100c964001240d00c1040c0c071b041d4280014540d680e40c90200700c00c880c881610b01d03882290302c0340b045802041c0c001030b030302c2c4411240d0b4500c0024004d400d01e5180100f80d1442c84001c1c40c0c010743c0691400110010013403600c0c14a6151303640444101d00100c0f4041940c01c101c3d1700300920f918070914000d4407583d903445071620705600d00344c801c84443c010340d0b0384554014029040026400c1c4201c9841884500d80100c4074100e03104414504a85a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 351788705 1250 351787455 351787481
    0x10507020405100b130321080408030411130c030c02160b13090e0d080601140d0f14091e07030512160206030c12060a03020102190201020a0b090304060f02010c020c0112 74
    0xa41030080706108403d10305882c015071003201c1f00111080d2120ba0f80d242c1070140000710340c01030001008141404007031342c0d11500070801d8000354801040001c806a0150310519001981c440720000c3e100c0d0300d48585840500c0c1c0d0b00080c40300d0b0104003a00c50207040d0f680700e410b58102c4002914070803032144043c03e00c001c00b0100001d01c041400042070f940c5819082c050030300060344550005040350b20502c020340a11a544010514001d40b50301d030013015080400c0303012201511060410000c0c0701d43c0501c00c0c4100032032005408942c0448a000d620038a03d000740c901c2ca544200c1c0180f02040380450700c1030042c6074400c1c0c200d56480c00840e8002009202d058007130f501007000301c20003c0e10b0b04101c2c0144110f5890b144ea003200350740e0b008100202d03106c06020103401030b840080150030f08940c40c011101003074014012200305484e03e03551380c0c44441044400880c5a003010404000312031b04608801c010380c1d040e00080c42201e114020081d41c2d0340821044604111518180c1518071009500041004600c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351789955 1250 351788705 351788707
    0x60a0c0c05030a02060108060f100e092a150f03010e0702070b0d0c030513030206011e0302130603140604050a030c080d020d0c090807060903020d140303040f030905040902010507020405100b 83
    0x3c41c66029403038040900c2014258051400003810310401c144046106a1108103030740019400c0c120314070703083d403c001c121b03c01921400801c80398640342e01e41305508021180482107007964040041c01041d1030480c6142038840030902030b00602c01917140942c1d0566805010200b031a5031000c00807490902164894400385400180c140d6502080f038010348800d00850700d040c406900e07015501b402c2c3c41325008018006070004001031005002180d02258807020901d4404102038803500040c500d01d42d014444101a80d440c1010030400c50803000c2265500c03440c401030b0405103040c6e01d81030b440e0a0612802001c004d0440310107070400103c81d007500c2c007426450700115110107400011000400d031600c6010b0100d64070000000b484e440c00221281901e11b00da43e00c8c0c6200b844c56090107041c404201e0700301c070b5008817800c07800001007040000d18801e50040824440c210640d040281208649800c0a80a2801d00c0083c10160360040102c50481f581601d0015243d036405071a00e094400642040d072446034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 351791205 1250 351789955 351789967
    0x4020f090f06010f090302061803120a05070501050606040b250605011217030c04060302030a0b0405100e060604030b04030509121f05010b12010605070c03080417010b030d02060a0c0c0503 82
    0x801250708610904003038032803001e6001500400e498443c0b040c0f000a61040b03007007243c0c4c00017011080080092140180890351804409640460590012088030300003450105e40b02090000034004c00b41c202505550240c41d0038100400a03940d4422011101c0d0000706086c2e20aaa03c5444240510183d0700084200029619024041d00c1e03040c10f144269041c0c1d100c9001c1001118800f07084900514000c8011850030f03203400c0c02507000c0c0d0401018103404960720406a030700c0b52124011184200481105052440e0501e40c0160640402524080c084e44090006000180c030051341640c1194260030032503103c5a46100080043c6040c0003194a03038081c0310403030300e02e01c1d0007031500980110010009009683e00c800c81c4030810702901050b000e4040c2c1d508010000c15010740000c140950240081401254490301c5000e090340c00b603441085a010756002803042c0400030310407580c1c0640228090b1404c10a8020700035601d11000e03040a09145e03840c411035600d0360007000c02c070900650000641751115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 351792455 1250 351791205 351791221
    0x70e040504060903110c060316180602010506030f030406051213020d030801051804020f01081b22080a1101141608130e10030f1e05010630060504020f09 67
    0x1c1c104200c005c20b0886600522042011401d8000f030400900920b045540b9048080090030342c02c10304000b44484460401c0340c2d980d8001c0e8203005410250004151400d0003405d042c03a10040c40200d400540017031105020f2960300c482240d840e414008210b042980b900d005105c056501d9010003944040400380039410180c002010f28100d500880310a020484c00c41980c03c0d0303959084400a500c50207840440301d403580a0350455030041c0d101001c0f92400c0c08000031003c040d50000d402c0c401c40e0410741c4640280100b5242c1a10050000c030000307440040c140e42d581c556031602d0b280d04a8140030015114010f440c541d80c003940e503111008038502c0005d0107542003900e49a4000000d03a0350940c0c1038100030611100031810b85001d01003d030044c4e81c1c120314607210001c142c80d00101c112014003c0044c804519403d030316000d49079901070400019000d24241c864003c1c1400119010302d865903101c52208000d0041001c0f88415800400102c5c60303507101c0c40010101062994900e902c01802c070305100001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 351793705 1250 351792455 351792461
    0x90c050c0d09060831080f071b06090312030c030b0402040308270616030c0c1706010e07090b09040b040903081005010c020d0206090f09130519050a0803070e04050406 73
    0xb208284c651600540743e0034a024026801d1100c0600440c150b03416140c1ca00c010313003180790609030040302d9560802c903405003032400b5036000850a03910b02084055070140c1518845000004002e00c1c03c1441d619803840e95400c400000e54544c100501d0356409980c220b8a009400510250701d0082007103581d41d44a103000380d456041410100e080500c00c41c22100c04140052040c890270354000c10941c24501328a098890840588100302c1c1001109280c103c0041c0780c106d03803100030307101c0c40509001c0725070701100c09498058140d00c004810070007001401030440d000951034054a81441c0307843c0e074070070a400106014180b0000c0842e04680744c01404001d042e0701c130510728007650f805244100069583d034011510b0183d002c1c07003c0d610418540b0141e005140400c01080540405400f201070b005141d0000750310350008a43c0201c0f146a40354080302004400d1002d00503144403118950180289078032074555030340d9000b40003070940e000040800c9450380100c040c00d4266000a0061000345024540900a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 351794955 1250 351793705 351793709
    0x606060203220e0c07030302040b0703110f061501050c0f0601090c0f170609040204090b07081e09030306091e13030f02030a120506010905090c0901090e0709090c050c0d09 75
    0x4031501102d81080981401c8041004944464a050699440b20446000c0f03591190108034181982003000203020800d0030090400540207449015020b07100c848800e0030001c040307015640c2c980244d001c20402c2180318030b801302682001e18201d07031110360558042e03103000035101c0031601910074a00005805c004e81e41055a0080965442c040d1341442d2800642e001d1442c44210b50103580c454000915034204041050741c040d00062010540c01c2007900e036860252015102a00060710001c20880d40101c200340c0307420080e0022102c11110700d000c42d200e070740301d00010b4005482a00c01d1404181d6280301000c02103007580b4181090006820304002210000584400440120300383d4034440310203d0012065a0b070728045500c0d85440020000d10800013414010162030500c609890080b400b40ca4644101740f207481c1c0c0710700040d0355202220000d80544515809814039801c414100b1240e240e000420b101118030064000c545082e4250301a0707907501844034400101c2c0700d10b81d01c1580306036000155100b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 351796205 1250 351794955 351794977
    0x10e0904061a0307060f051e031f0f030f02041107050f0a03031d06070c0201111b040506060a0f05031003020d2303130b0c03130b040303020c0306071b0507030606060203 74
    0x6040300e04080c5502c0706130500c04c02020643c1c00b4004409a40140300601190080314440059881c0c4044402410b42003a5910980354800c18403400b04400030742c40c1c0c0da01070720950000c07107500c1e855540d50f0280070120680081c000d42d256200b0003960b0443c081030300c649503800000e0341c421480e80501266620488041038001034103040b40059154070700e02c055200b4110180c05411296074010090300d00c900c042c04124100960346445440031a024401007004c1011085c2c450310b00220202000280c441c040c128520600d4204101d402242c1c00c0b00013980081030500307080c1c2e02c075034501c03034038501e00c00c226031020750001a041c906904010210241c82903440c5400254007145684441d06a9030707004c2c6452101d2040d00c0342c18140402c40c3e100000c0c103021380f01001183c1c80c11030413007034041d60b800a580c03001c2e020b101c000c101801015014800c100400340150000e1202e0314000130b00a00c40d9420041d4044000c0003031468509000c006d06c490f501460700700a062150954070070703009669a000c01a420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 351797455 1250 351796205 351796241
    0xd110a031722060801050f0a0e0c070c0b041d1021020301050f040525090f091202060f0a020901031812170f0a0509070f0b0d1109130b010e090406 64
    0x11000501c91070418141c40107503403901005ea0a1400f40301e0b0164502040903400021003100103402c840e4040d4032846182c00f9030416841e86207600c0c4c1009ca4520070340000180c81824081405403410881c408119050b2190041c00340c0c1c8c81b4442001e2040c0d08540100044541040654080c168004000b94140d4401d84c000c10a83e51280010b0880c0300d0251002011604030411810081000d402100c82d0f1500813002040810390f0740540508480c00301c071a4201064030313010320b40d0902c00441c1c903c541c20301650000d07066515049640d1600c2030801020010015808590100d10340d12036484814620460500c016082200e03041480c0250181100740c00010070340c0c5002a400074441c9812402102124a4442c1c3ca8030340300d00088c0501801400001184600c02e40050200b15280d0141e00901c032040d0311554401e103400b90f207803c2e6050801c0103c40404204104407440d10b0b05010708480f0305003030340002040d04016004a42c6210182140d613401998101400140201a40f1000c8181c205403007803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 351798561 1106 351797455 351797497
    0x20d0605040603150c1b1b08010207140601060212090d0512032a0421020f060c06010f1e12170a020f0f0102090d110a0317 54
    0x29600c10b0307080400c045a0080600c240c00f10004c0c41d2525960045500c0c03103071b9812144c148001006174841c0303a6803188612039139400f0400390038000b00a40d1f903401181040020340f12480eaa03003d03140110000018101e0001a4440e000d011745105103091581d143c0c1004036008100c50142c071a4010400c0c1401401d01c0340d03005505c60509141c4000504000c0c1001c2c5017909480c075100b440d420790800040c880d8042c01075069a60b00e9405060071481000c42c4041544480400606c81d0444004208940580008150305050324008529100540e076102d41c00700e00141c0400265035461100700c014400f00c141403044a000310300070403601001d1079213600c290109900610705440140c0000c014082420000d002d8a01030742e0066000b54141a8610002901801481c200512090100e0714800ca10b0316802d40b4400159004080000b040c114900145c40c3c60f8000c404889038600c00d4458 = true := by decide +kernel

theorem cover : BRFrame.Cov 351618705 351798561 := by
  have h0 := BRFrame.cov_init 351618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 351618705 ≤ n) (h2 : n < 351798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
