-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0756
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:36:33.134254+00:00
-- url     : https://prove2.me/submissions/52f69d32-5ef4-42b1-b33c-c5b8febbeb27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 135791366 ≤ n < 135971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 135792616 1250 135791366 135791387
    0x60f1e040314040302190918020102120c010908030a0608060f04081207090506040801020d061203020727020307020105250504050d020a0b070807050f07030b270610050102240106 78
    0x100c24614183c0c81e0f17004144101080026100c94008481080140c10341512980c8030703810192401c0c000190049d00002d50392101420f0307500c05040001545402a038003503001171000c9510640994480c07034032103103041c000c020902c200300072030080c0340004030f415068000241c4561703800007104d0b00300450902045071170138004003000140700b42c504010641780d0b44c010141004200070b000260342c0701d501c00800c3c0c0c15980381c0d5125030950390314840e07980c0003c0d4010415005490184415001c1d00340f807050214940e40b03a505403400721a100109100c8000c2e41034008511408181c01c03000c079110000f01e500c008500700654540300080c0c0920040c4800c2ca0715a0b924465180000c004085d01503c0b07601143c070907801041e04641c0e03000000340100401505210351000c2c038400030702a000c1c41d0300d180c554241c207807130090030132100140c80c1072000c40c980040381080c06c468141400303e861924040382c00212107401401042d015201c1da22022003100d009610100c150b95980c581c08400b646070000a8843c480704 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 135793866 1250 135792616 135792647
    0xf09060f081026011a0603130303060317180a050a14151605070b03160507022e11160504180501090605040309170607051b060405060f1e0403 62
    0x501000241c100c4020440d060102980012040c0300d41181d03c4036007151884180700c420f11048071911015980c450080d20303841100c0030b4400b01080c0643c9012401041a500b0007400011217010f45481480604003a1aa20700f045001d030b026000e1000030410a000c45204196100504800a0040d401c90a82d00720180801070010001100c40312104070791508102840c2d42070b05503401c641010301c02c007049254000c2105840140c1395082c0280e5004840301007070304203824040c000440c041152150451882d11003c1082c5c0d01d562400300c1d02550a0540032180c2081c0055000310000c02140d80c0410403d110b0310b650290481c0390783c544001e0002420390740241d5520074604000a50200d0400c0c007440c2505840b4140000c3c442c0350a15000c1c4c03103080746811940300320304155440b05141c90001a099001001420016180c19010200130b211803201000d4000720f0090b6030034001007160004925001e1031a664407482c01d540c1c0e90407010600360b620610ba1404420001c00f06001c28090001e10255801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 135795116 1250 135793866 135793891
    0x8070b070c2d051c0e09010605090405040309050d1103010515010806040b030a0215030708070f1209240e01052211130203070e03010f0e0d1b0c0b0a0f09060f08 70
    0xb00c2d0f0329040d0802c90300540e10714900101d0700d410400b0b164000104500c42c10203e61200b541d5052201c000e20b0b40c020401051700480d0b9900109080c10701981c080d46c0102030080020212141a2920000203241c0c21000f500a600b00380102d2440c22103000079821740001a541c1b428a941d0b80400c000103800d0081145405000319005600541c581001c0341c44000b8054414660720b042420008000071401000b0b4810048018446004181c1c0507d00c0c400c190700d03030040400c007090981000e100306803200c91108080b800c41d035550510001207070400241ca259a400070407040e40c5000e44803240780c02080404404814508a510018800c050700745030707020317000c3c00440c5a00c4003c00d000040380d2060782c05c200401c0410001c031803986800d0003483c00c8015200707814080ba9100707881036940d81217000d03020700501000302c02403200d2000c51200e07903a1694100502000c020f944910b4040030768848240000020707400d17110b01000714050580c40003255076a44d01c1c450040d0340c3e2102101c41c0030340902460759451 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 135796366 1250 135795116 135795203
    0x11070f0c0509160807050a17151e03060a1b05030a02070c0f050909010c050306060a14030c071b030203033004051c02061003080c070e0408070b070c 65
    0xc0b9840c021500c210f1804128402c41032120f400602040c1c8024128410000104142440e490380f0800c81d8800a1550000412035210340050213a00380181403001d421841020300040e0b0f205080d6241c0105403003e400b03840f01a03d8103034891003601d4411481c001c886010100c580703281445000215230012555800604102d85a80c401184c0011603000cad20724003091400a00203450046c8019070001340c0031008222800380c0480241c0207000051000d84030b11004200010030900607001261125070300008669039142c01c000b411704a0700081c10960301c07007164000002943c0810307280345c0b00340c1c2c1e001402141442c0c00254664421084110449500741d045c88909521010515500b400781d441ba90107040114a034050030501603400024072001c541c040b000b80718040f880705401c003081e681c00c00c148582d14043311288518214540c0e22a501e0a06440200030503c41940054003100c1c1c8640d12140c0c890301e80c0750080b505020f83d070030050b00c0100c000b65080a004401000c080882c4998a011055035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 135797616 1250 135796366 135796369
    0x20a11100512010b0703090501020c010914030f1e120a0804060203040212061003020906010513050d02041d0705180708070305150a08010e010506040504080406050c01020f0c0f07080111070f0c05 85
    0x89083e4040f80d9a80c04c0414090300b05900300300102d028003420310040612403001400280503030018850300b50032105c1080c103d00c043c0c0301030040b070308021550811500b03120601d650b80d825164146440c404540a90325050501e50311142c2200e103001c0c06541c0b02740484d121a10354200030340c80584105e0340144040d0b8aa02803040511030340380700e030809040b0450741c54030b140107200c07404030b00070140380c1040070400c20003202d80b4a824100d001e4a1054403c1c00d45124241301080090600800354803d807041114102841c500001b240002d80307000b500d0580d401d20701d06d1800700c0c01c40c509413000e10110b1415000a240315119030312280c4d000504541c0c6071032101c410000302e075441d420b80e0040c0640b40d46400a10700441c10900503142c102d1400c1da0108440e00e080d4407811030300d0080740110b1042010000d10031440c10030940542e00c20f4000e1005980c0d441a690003c01e540e06407009131444a4043e000001620050600c5400544e00040c2501e524082841d03a89195a180080045600540c802c10200d00c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 135798866 1250 135797616 135797647
    0x30c0809130c0e01020705040e150406020c01090f1202011e0c14041401090b030c03070f03060e01120212010509060703181a0f010801020403020607030e0d0b0903030a0c020a111005 79
    0x207082c525250090300a000c40c000a0030890240c03c0f150282e4180302c403146c2030007400500d012008d6034141501c0c00329161442c140c0d0280c1b040c0101e90559600f0000c6c0c920511124a014961003071250070342000d107501084003682030f5030b003090030f17980c86020861000004000307540000000140e0751801c0c0500c1080d4011808050300a07400c01c1500c1961419803450551300118020081c2c40400c0c6020706500e03044070104d1140c0720040c0343c50104801c09a03441c1d2050b00a4120350f015014070f50468000e580c40d40300030581c40052450a03845000441130050362002c041c032a2501826240010788030940e1211401e60180210626000c600001ca2821002180620b002c81201075402c01d09140d0034100f0359803a0b83c1405041c0c000b00c4699204000820050383c45400b02c1e00c0075a89802c08241c40c0881e0303800500314061541c4041c20004001c01000080080813005620403e0380582c01c005203460310384120303910802d450001300202d60030000c6e19100d140141905e68264601e20303084d481d090401600501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 135800116 1250 135798866 135798881
    0x30c07080714030313032405010603090312140f09120c010f060510050405011b050607020c1e03060f09011d030403020301050c03040f020d0203070b0c0f070b07030c080913 75
    0x166081039505020b0001102e2040c00d820108030011410b0580303503001e0745807101a5200081581c580103151017006411401d248900000380c0c0d00401032981c0d104405000360092a00c103d00144403a22017800b000414400d001010039035004010700f90b0b854140010b818031014001413180e1260f03594028402c09800b0042526020800010481c1420900520300b0f03182d0b1a04042c3c40703217044131048010581c4c0002540d0484000f480c02824125240c08140c406000b04080641140544003c022609400280304001c012040c1c400d0310703400303035811680d000721034035410f6490b0715810400c0491010f241001146820503040390000510135000703100449a0310503104a140c0b29000420204298071b800e1207500d80c0407000039409891407400307507241c4507600d044401c000c2c03040b68140404015034800b04019805003d24100856841350410b00c00c907522044055031000e2032050800124503031090009403404a070b0316444060800010b80d540d5006904040011604140040c07010000f40e40c40d07000341c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 135801366 1250 135800116 135800129
    0x2609040905010b030708060118050c0f04081501080601120f0515010305060403080c0a080c0a2102041e081c11060f07020c0906130b180c030105030601080105100e040203030c07 77
    0x40c03403c50741e02c180340c10084541d000c0d500c1c1b0f8100e8001009480520000350010311080440012103036034955019403207010b050304002d041440071401007441d4400046445202d1a081c4101c40c0503030341d880e6100e076610001d00513220514180746166001413007060305850110f201d1019030300c9001401c04420000f034002d0340152801c0c6e0001d4188001d02d6040b08050780c101109140c414075154440c000603000410180c0724813a841d03000203807403004c5071140c5010544899072928000901442c110800c4c041d400501521200447c61301e00942803184044000046404440c00740c440e10614542011201302d6010b0501c05000b110100d081401c1d45c2030100318410000310380b10046c1c1e42000100240b41815041041e4003820459050164994451902c08800340040d5000b0418814040c0440c0c007000e404204140301848030002d00000303135180c0b00518160761701542252800e0380d0302c45038036003270f1076017581ca04601c001c00440034806031840d401e145074018000760849203800c9152004a203081c050340d0256 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 135802616 1250 135801366 135801371
    0x21605030a03290a0b0702011106010602010b030f030c0a062a03020310121502030a0b03010509030a1b0809100306080613060e0304260115060f030507030207260904090501 75
    0x455601d9260303008a02006101c80200c801c0003c4003000c150144014080c8030408075001c20b079007086a11540650340e82c11002c3c1c1c00e494565942e940080c2c060300310041a0341c800e008034645180480c000006642d01c1c040301e5002050460040d841e814000d004d0b564084410080c640c0d4140c2d4403e0110250389a5070a003941c0050781e034601030000c02203414058200c0c5007054003c28401010030100348240480800c1c0030f0700180c0d42c0c3c8030703148a900203000c850345582c0c055082000300721503408003001519071500651076007004103c01e00d0380650082401040104041400d11500105041c401c1a02581e041d140c02c0000710151a8522107180200484841c11560b107041d071500c080040c28001c84011070403036002942014149208050a003034020b4203030030400300c812003403d80c1c0c0c0c80075004030345104000030304002031580390000205110345024041020900780f40c04a0340440c404c4c42119561354215100040b00d91071800c02404001d501442c500b0f090340103208540440d0780303d08c116840d451041000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 135803866 1250 135802616 135802631
    0x20c09040c05090a0b010509040c050409060f170609060703020a0509130f0f0605030a0b0901091e030f050f0703050c1002030c042903011e09020409050105040b041509021605030a03 79
    0x10070522000083c8044009401c098417004666081800c3e1104008110b40208400100b18030072130b0180181d034401e41855051030030003c1e064032000306200a8842d2088405102100011003c1d80c5002c1942d822030700c3d9000b0790004141510035400b50000c00c10502e4142e10b0300e10090f0003d01600c519156040e11141d8460441140d03841510820600004070707042844001d01c1c000019444a481c1c003400390005640310000340c5001d40a52144100507440803030048204038460504004000020084000ca980d02c044800058000c000341c42a0500308229207160211658044035076400c180c2045840c0c2c407900b1019030010125002841c455110550281d4a891a00c040c4c0044811218030007450514040811241d03803020f0411070741901e10b4065080d2140400c60300b12100920180d1001101e5480810301040d10086600030034101c03441204d040c000603a051081000706c507501c0c045041c511031500c1041100c405541c015102e0540125581e0564200036190b950540c0e12008105000039651490b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 135805116 1250 135803866 135803869
    0x30f04090b0409020a140d080c0a1203090203030405131b020123010b1e071b03060e0c0d141603060506010305240904110301181101180e07020c09040c05 67
    0x340744140002220248603524680c0c010a00240050007110f10602008806540b6519004411202103070300c05074440d620425a06410344541075600220303401e1241c0c000303180501e44640144c5500c0354000b8069441c00345800c040104c41140030416500301c0361039001195503a078001e0340e90068040f49400101d030b0700100300d000c0c109100030766101c01c5da5003450380014448900400305541d1034010340c00169000c10030301107101d00d10f8019070a009000141003110740010340710581c4040200ca1003002d0038003101c44200c240c180c49030441d125941c1c1140401081d40041400045d151a5030030496094501c855107619800d40201d15a0300191406611001444460b5a052150903400703103070350102051004880d503292603000c0c80c12010301d101e66200d80115061011103844640c1400c0014001c01400115600c040e40d1900e1401003070302e070258080c410841355401014103100c903072030031a40310f007450381400c280848480020b40640c003144a0f400e0221160388850349024040c50082803e82c1c80c60340b0703000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 135806366 1250 135805116 135805121
    0x1203080108100204060c1b050d06060e0c0304030203071101200102190807050d0902060421150c1b080403020918010f09170d0b06030c0418090203060103080c0a05030f0409 75
    0x52940c0b4203104201c200440c030f921101c0c040105612503004010b40c0c07541a00f00781c1c1c001880e0490707540407007540c0d0b40c1410401150300503000c9410036901001290307034079010000c0e6030208a8014003d60810849540040c0703540f0807440c40d883e01410184c010018400c40c4120b41000040102c0b041e81d400607011a801c804031100380c10481491822103000d1a03e1400103026001e5080b5200c5000d444004d0f0004641d11841594050b0100301c0c1c0011540c040c0d29203844001c08800c0091b82d030001b0607030401c250500c107801017103010841520750312415000e1204822801150361000d44024034140404001660ac01400a02440c2d590700f045900c4a8040d0303156007116941070b00d4590042c030700000080026100803420b00c03281c10305c41d680f54640c0708424440004d004134415260344158000100200c4001e2400030300181c031518244803000b50700702e41960040b5101b003c0041d500d071b442440100700142084000b0580a565030703069500c22509940c5851441d00101848070b0100008a8284405a09403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 135807616 1250 135806366 135806383
    0x3130302070e060d080a120504060f0e01060e0c0c120708071208010f03030e0102030c070314010b0103020f030c0306031c030614031c03020328050403090e01030305120403091203080108 81
    0x442d015109051580004900c0c00c5040c00092911340c000c181c0700e104c02d014050204034461881800c2c071042c60701d842c01400812801c018003140302d1400340800303840e400500c12841075400a07107440340c8072f85614106000355040000c100c10305210b0089082000c0c1e03002405080b81520a0b003040d83c554480d45414075012030b0f9032400d00d003009004001000006101042030048a4050070038181d40340703900740100d0030f600c1751701d5034081c507842102400020400607019000407804c21030300030483c04000000440503841004c0c0408000c0d1401d10200c2c14911900c030045400c074000a0407101d4503903486400c0c0020301c00c3c40104a0201e661144200f003511804134601c00c00c68000c41c00788c031041d030a94401c084c00890015401042560200c0062444a484124810740080e084031550b0480445c5c1e00400180600b101c0480004e8179244002076407240510805060b42d606484035800c00541260128440303000410642c200300c2d41d4900083c60002c1c181030f20011a0003980c40100c0b540c1080610351614486 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 135808866 1250 135807616 135807629
    0x1006030b0c0f0901030216080a0c1502090f090606041a04030606060e03031801210b03010b10020a0f030306030c032f0a06080c0712110d02010501050a0605070c09020313030207 77
    0x4005900b42501500100c03075002009080c0140c4410b169409086004440d4000501301d940014402c0742041d0800e103031192943c4101803001951403c203d4a000ba40640d012041d00500c11710007204840c581240c19039841803000d4044c60910380d8498104070700b1810b030754030a00301e410006030910034404d09000c0e04001e0440ca007410101d010a0070042642d0303100c1d10400c2090800c420342c581f0341d107070b200d07104010907110320000d100d04a80503001d14100030088000010712946c070f080c148104600f402400d075580c8003c2e907000341030910542c0d281c9038514403400c1411410150344070b002000103005006150302450180c01c058448403e44220b008412901c4588000700441d0f00d0036103160b6580d00c4205606880c150300d0700c11150b845080c1040080c0c040c2e158001c141908204e02c042850340d0007030f000d1344990800003c0703c0925145010903400c07603001b0b00a4940005044601740031082c000d1005003902840b4500803200c1c20359501206040fa08203070f41b0403920b070030701211030018941d04000c100c028114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 135810116 1250 135808866 135808891
    0xc0e0a050408091309020909010f1b020304270f020406180302030717010e0706030b131104050d03110601140f03030301150305100807120606080303090a0201140c1006030b 75
    0x415403200341c2e56000d1010154800d4902241001c849091a08105041c91b80544004854107085c0c0c0142c1c060030100300c007411000d15003030000c610035414032021008035010350003031850503040a184007101002030030103007400c0c803064400030a859003600c607483d01210300c1c58005868600301040100324114084010241c0b149060040c0301607900411883c0440300c8201c4010003c20208290601502d49451480da41c1c0c0900000091983d80640060082d00360442c1d016085040c0900796008448501c0c051240c206070520043c84a0700707080044421880c003900742030340d03036994202c1600d180440036000522458040d21461285003440b401c10082e20702e0403406141958104642c10200484040030041011b46070004901d14903240400b010160000c00c00707556020351141d024010403d051441202d0389880d000c0300054100300031050f80c0c02950028007030325040c1780603001124407070701004010110500405c07a11001103020464466503501e08036012800c1b030301c0c5041c404650030004000194818 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 135811366 1250 135810116 135810121
    0xb0102150f16031a0f01021203041b050d0c1a070b0709050102071a030a09080f1b06062d0102030c070905011502010c02030a050c0a0f08282001020c0a0c0e0a05 70
    0x38190624401c032540280c400c040174424030700040b03284c1444088113440d040b5000080c030050002101150501c1000064918440da6440050145550f1580c00203041101461014800000907076442030100c030180d41e129040200310f460f04101408145c4d01030000c110190800c002e0341d60144002c5005148101c04180c404079a450610010301c0024900c01265603600b01c403100b045001d0080d11120034034000055281c4503a0400f0011004107001c040d1414822000060501e24001e8221f07002800c040302c610764822a0110611310074880c0c038444c01c1c1036000c148480e402c1b607242000350200408141c04045010351605444400c1012812140b208690610324024001c2c0e40000444040e03004a2130a1903584101285050408200003001090718407400c0300d03d424841c461019000c80600801c402a005008126140c2c03076181401103000440d42569020320b205144001c2c1449016400001500c1c00350320900980c01c0070101c280464411142d00c80a110805412480d6580714020100401190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 135812616 1250 135811366 135811391
    0xf100803030c0f09060f0c030406080f06060d0b03010b1c03120606020309130915050402040f06031709120d0207060f02060601050412050a02030706030e011802060307030b0102150f1603 81
    0x501c55070360403075030980c400240f030202505c40200b1074140095800103244c641034896566a22540588141c90000342d40a020540b0100301c55074207030040a00274901890510070004d40700181210100443d031555849445d20026100d1001c546e11006ca82e00d254007402d0241e00c0c0140030b103006111401d420a240100900659400204580707041c00700702d0742c8000020074120124060403001c00d00400003121441d0101c10388800e41c00a60280e842110b062141c103441c620a1402c80c0c1d103e100140c1002d62903001206284107000051400da0303000f402c0c0140814078508040d00e003800158090005920501c8100240d03680001070300015003032480a0103603402c1c0f000c0001e00a0080d030154404211880c0031000030847c0400000d08110743c050700750b446c0a51307244405001005100700001d129403d013100c0040001903034001142e0720364000e03d418119141c5040c12002455200d0929041d4440c45081110b60400201520b10480c860070441c4454035081800000500d1a41108000c0c14200400303010507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 135813866 1250 135812616 135812641
    0x8091306080d39050a060b0907030b09010e06010909090b0411180c0f0714010e070602030a020304030b0405011413020109050a0605032406130f080309060f070c0e0f10080303 76
    0x6050900c180c040f001c110a0355858800805036000070314902c40c40c0072060820425070480d1001c003800311030301c1966070350700c410a4068a05219100f41d01035040300050007485486a036440d00120f06251003002191034005480485105400540b0234204400c100020002d0000140004c4101500c10340c1014400056110300018040c000541c2c43d03101040d51042904590191103505800c419989540303d5100c0000e4001c00d0103400300c20442c0079090700456078500000032100c020750640d00840c50700c3d00d147c0700c00c10307a41000340c405c031425500c8100030221141d07804515402024500ca50342900c0e0a40d10000d00a03035800c2d0f000038025106040308200f6550824240ea0748804c1c10020001000004d43d052901c8403456418a41c0c80741010442108080c004052081650741e801000b400c032070b0301c80207043c3d540e026a03004260301200c00c00045040d0020003014016044c812501c506e4a907131159444640b24800f152015010305100c420442c0340c07458211510024008100a18558240301c015080f9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 135815116 1250 135813866 135813917
    0x909050303010603113a0204081207020f030a03050a1d010801030605091606110106091401120f0501020706020903190302030a20060c1b0f150408091306080d 69
    0x42c1580c42e00e2440400a515046507004900981c2e4810403d80d030202c0101011440c1d2080001b80e240c03018540020704035482190300f41e50b00d440003000c0054400c4185040e960140350126001071140c0e440d6000350720708005641c1c6240c440d4480540348c080b1070f103006000800c460129060000d103c0b05160075030340c000361181d040d640c01210108850780c030b41300c0e40c500e421400503402101c01811800041d4059210f0801e03e20220454000d000c02c907030703400002d0141c6000fa1100031810b51080c004014040d4180c0c250815a0310868008105000503100c407400ca8004031001d650080e00040c4043e510b142c01d200024280a00040006410500d40c84c001c0d66130103a004d03a030f01405182c1c094010000190a092300045000c05c1c2140e0b901d14106d1911107664102840d050f00203035440c014550203050200d440862015900b0042004040702c1c0c195480c5400c002c0d109842000d4200195101500c645248201d200c201d42c4012461a00c2d08540d80d14001d5210001803c10400d162a150400b483e10910036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 135816366 1250 135815116 135815129
    0x31e0c0304260a0209070c08161110081e100806150a061803290a1b0f0806010c060e030c010e06131104020901020c0907110d0f0c060f0b03030703080a06090905030301 73
    0x2081062603150910b403030320178550706901e13524031192140104607040101d6801040c04bd100b14101c50303000542640e0740801580c56007421918145569034540e0304150300355001003125001c4042c103030b41d200a50304080302901d2044d06804582c80340a00c0d0700f001d0f507503640101640e203000c035000d000c8a4003862001e505804010111041020b0a41e13000664460700c1017101e448030368541550030102c070718000418801c981291001810340c0c901e01c02c5c0740a404c2050b01030540d07443d15901660345030011910000010008c03212103540b001d414402d020100054000800003400000d584664481003620b40300c0000d041c0700c8a14000a010700028241c14501c0020140599000d61140e40440042c0e080040280c00142c10044004c10884500d038001a600c060341103805c1520259548480211141c0441c0351410012807081503480c400100983d11807418550710f12400906100c940303000900310351050100b90b00040c0d02c0c2d0207128813040140b16400090034028800c1215207003a41d00c05480b400140710700c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 135817616 1250 135816366 135816377
    0x3060c07080a0c0204150e0f0c07020901031101020307120509010801090e19050a020907051206010507110108070e0a06120515011e022e140405031e0c0304260a020907 73
    0x2000f1915250001d0306c1c42891004214071581d00c2e0744042020340011100c080c0f14504240c00301d0405512a42281d0702c4a402038080307646a800c5031108a00c001c040300c4e002d41144000c2018102141500100d007007002c0340c41d5903180e81d40030f00e4000181480c03010b0700041140b6151541c48a002d040014650000020240d84100302c4c4602e8100141400014072002c0d40040b45032040004296002000b043c0c0d1180000e910256622004011a01809440b00090085e1404202100c8030b6003c1c06450f54024100e00d0b20b132a000e0984408a401014254020404502c454200740030780c04075030041da07a1160120509180308401c1200080000b4601d44500788141e0039460f590080d14030034041303803500350785611003500d070030104070007000404408035004054a46080c8040c1e54254944007128040d6030004021810541d100030419802c15440c1001e140c148000c10880c0443d20042c005000108408124800700b0b98100b948400f4101440002c001550003160001c40160360384120190002e12070b2500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 135818866 1250 135817616 135817637
    0x160f12091503060e1b0f180109080102031003020d05010207050109030f02010606110a0311150106050d0506061314030312090c0405092a01140d090204060b0f0f25050c03060c07080a 79
    0x40170b0f0341c4502c4181c062000f40009011400c001030300d00280c03064a081c2e983c0c020340b03591006810300f02c1c00f050b00c0c0d035014540f11000803c09403401c00340104da00d60090340014030700402aa200c03070031600000c200314041903480801344202d680a01c610801030505081030010b03450010907903510b030340007103100406005d082d000300401c4403010030501f806113030007489542c1c1550312600c029207107030460807550000d40d0038030f80000d14034200442640e0045011079401e0603000d082030b6a03c05178003822810b0030f4052206200710a040c501244440c4e00416100000e1710f000e052110a00080d03d00081c100a802d50180d030200d18862144411803100400100c802a00d0010340f400484600e002e01007800142c15002c610603241903075a03404444603601c01c4404101855881c5000e01981c0174901c4540103a80d0203000142d0301e200c0340c000401d0741012070a94074140c0442c0030b050090340c0f44c0c2c00105480a90208001040710b040401c4156008101d0510f41c0e0b0a1001640d516080c51140089180810082c1e012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 135820116 1250 135818866 135818911
    0x20d0c03050f030409110f0928030b04050105060102010c08040f02150408011a09010b04030f060605040608030301150206060a140f03030a17060a050303160f12091503060e 75
    0x814095940141a1451114140c281580d6070b08540181c0c50414070b415000024a400101150121400901600e052101c3d800804c9400c4e0196002291445c0303500084081402c0003540c403201951094100d410b0900706820542e00b103420041c00b003810b580c945031000400e03c0c1c0110299500582c4403000d50b000c00c00d00e102141070440c2503844000811404030303002c41c2c860b506411071001e4001c0c20821010404010082107600c1d64280304104003010100302c2440811143c00d2030034400c502900340811711980e100082021a01030340e00810b0b10390008001840030000e452001c0c142c00c0c00394801060203003070003000a4003841c07891081007110f8503503010341e0900780c0764048a10300c03c0300c005007980c0d2038401e00d0102401c000d602510550001c0d20080c0041d8152400e04020000c0d0345014005606040e0801580320250289043c255070008400300c1d40000111a4482141490030710b980d059002450205108200f003805e0756628207050031300e2002c1c01301e005044e55003503100300360030008804600c540c130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 135821366 1250 135820116 135820133
    0x309070510050306120601060503070c11090901021914090405090a0f030201020a2a12020703050f150601081e0601030902040e06101a030c03071b200a030f020d 70
    0x2403045412001c00e40318049080e030424040c520070f000a440101090b410400700545600742401041c0210700b05001080a00c1d10900313a4801842c030418000da500404000025031301d60049403000c0e6141e4000560201198100e81c5030005440e10341030020030488942c4240f652800ba001e801401207545000149800c01d0030081d540c001034201c0788a098100d41c50400901030340c420344c100c0c0081900c060514803200ba07840d42d0a21034402c1185204400003c40e41c3d00f040f92000760300300300c0840c4039210700440419070521440900c0e16600000704841c0c05002d00492240c80005c080ba410712840f80c0800c030320340042c450b140d06941181030514410b69100c41c016030040c00c440d030f400b94029150902c0280c000d13600141c0c0900038269881c4010a8540d20043c03501410b9400700b0b4510340003024000b142c410702801c0091341d0031850600f05422241c84070031402001407030902c01030340c1d031412041040f900101d21f8491030045d40010b4500e43c1b180c0c3e081d9111101a000d81a6009000da46404501d00900c03100b00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 135822616 1250 135821366 135821369
    0x5070809060714011d060a050403110303090106030309050d0f030c05011e0605130510060804030905060d0c080106180506090f0307030f0b061806060310032a08070e010308030907 78
    0x4007403645030112803c040318504a5100000295842d2680c1c0e0740032440128140100c0c00b5401008101781d41e16052014080c0401078803c40902103010840c12921000344040c0d8401c030003890001907031515504008082d4051035000310700a80250f030310302c1d02003001e11500400d500c0e014101103441d5226071070001c2c0103090644506401128a03081c8010442c100d400c078000301c0314100c61640c4502d94003850007045440c250741c48424040c801e0403c00203c0c0c000d0000642c814000c0c10300b0000c0030340d0358000c039180341d008507800030019680c0ca01040099070040c4465000d40401d20300903214240810704a01751341c10704c1c052270340328490200f0321811954960405018107500a01651842990307417800081c82e10b0020022101e003110140051200c0c103040040c2c94800c078040d0601c440c140c60329828491660b0018001c10014110750704044049000243c0144c00c003168402050154007002c0ea00d41c400440e00c0e08201001d4002030310411002c031044008905482d0400c4540d640c0e920f81d24441440e00c040c0303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 135823866 1250 135822616 135822619
    0xe100906120b09060c0412060e010f0905010e0c03120f070606060903021305090604080a020f01091b0504060b19020a06060e07030516021c111518030c06040305070809 73
    0x4108001c622400303903400000c41a88150781950319500c400005507200c200469800100c003c0910040008042c2294000b60b03881c003a5000083c5c19008650040c00e40360461001c2c1e04a684030740c0c0d0039082140900c5410300080302d00010340070304900700780065210401514135028111000c503040d2000151101100c04290740f05c1ca0800450399104009444281c8d9840143e00c40c0c1c141103105800305015010b054171515101e00940500d039155900c5e82e4843d040441c01c0381c11881559028401044240310b910799031802100d408101d550401c200038005d0001c1d070000d50041d401d041040045140400948a020208407414a208190010704a1801c0c00d800e0015200c5820114001041c10400384414000d1503e03947c02c1c1300c181c0e10106889440c0c4140312112005a2224120480d521400c0d404915506002d2400ba05044d001c41c240901c1c0c10442c1000301c144a101030140440b055042c0b03003488140000c02c000d5800d1500e54240c903615150010b1014042c80000100712041015100c11595140300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 135825116 1250 135823866 135823871
    0x1080a060b1903110301060c020d0f0605130b09030726070b07031401050117060103050601050c07080105010810060302100c08040e0a020903010f1a1905091e10030305040e1009 77
    0x81c0010003041c1c0b0b0040c0807041c01080ca421001c1c10080022401c03241030390119280d40c2507d6550794240300041c00c040000b40d65068800300002c0006149005980c0242400800b01c1560229410400410750010380401c88a0380100001000541d40b40c2205081c3e0f8149415415000300c01512405544203030240141101c4c0038104004149815174440c19020003241403020702680c07180010740f07015038041d01d03880d00340d8100710002d81e01d5846904810380c0404185801404c04d003284000a1900c511034000d807003140d445400501170b03280c0400c690018062856420b105140c80e50300841da00310842065401002580b4500d042408405d008590023000d81d2410105031b0f16005000000a401139210f80c0e110b9401c00e6000d00c045406401400109070900c0c0e05103030f40c00300080400c035a400c0940000c0e058410b941d280010103680d086821f511481901c080b2203410448004210f806541c011300055801044d1541400443c0c1c1c09829201a60404c111071412603d40f5400d41c01000c8080d03020009060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 135826366 1250 135825116 135825127
    0x30f0a02060a0b091306020a030b1003020405031b09010b21040c030212060f070e15030f0403090801020f0a1202090907021e0304120807081201030609020a120f0201080a060b 76
    0x40d400200d2a109400c00352041103504802030401548200036120099400d04841e0308001291184c0c6c020040c800460400054130b12000b0b001c6503a10282d07015a01c0030960101e820442d500f401c1c00541482c446807007601d100d00c40210005180b1a206000b079141c00e14020820707040020b01c44080070b4845010710302451075031501d46014000b00c904c2c0d0000724000c2c590308413101000400050114024809440315060a5987c18070455008044503031859110301020308043c5500720a20045000741d003090703501021841d050501400b9821241c2c85151245e2041201c079030303404810f400303940e4000d140c5d140c10015000010101400b038010248161380c0304070b41c0401c0c00b080a800041c00d07120288096061800768401c08201c80e128000e5100f66009044160a4100002c58410051124521030380d10103050403920a2500f4506009030000c440060744d50000c0c409500e401e80300c001c004c10b59a44001008821aa80c00c2690b07007203031100a040c8000440400c1001e1213503080900906002c040300f070348a030b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 135827616 1250 135826366 135826387
    0x215040605010f0602030901020d08060d0204020403051e070e04020f01170901090203010f0b090f0703141006090f03080d05060a1701020d060905010303080112060b060406030207030210060521030f 86
    0x209001c1c85429000462210f0025101d4004410781740c0c5060140c0203800c8841e0807210544e034030030b001094164410b03040c0400c1e0005030784078800b41015500540040c291400d10225400000345440aa800984c1c4044400c10a601d0011342e0964001e6058441c00002404000180c90403d501081400c40c040000c0401080d0b51055101c00301c0707a4001c40c028000c8085007009171080b1200d03842010342141c0790b080000c20082d40052069000345031031400003003150320f411010519501c252658010400701d4a420809542d0089520014012045140585526507903540583d07125040d52000125219800188540d454042840041006104038080704444044840c000e5106070132141010745068000300e1205a64424981a2945615003001e141d00b0181c500c2c82170b0100354000c88043c4c0e00e1386103502042c2c4078040540000c00441d280941c54100500d0007070b050050000d44034600c14036005c01005560b40302003a8441c1700f02c0c551135440500d2a40322440d401c5108c0c0361341d0425016800188002c88 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 135828866 1250 135827616 135827621
    0x1060f020a1a0f01090515121c110c19060315030b01080c1c0209040b0a021e0705060711030f0c12040b03040b0901061409150a060801141c030e0102150406 68
    0x10f072400301e007030841c16a21410b04004036402520b81440350711107010440300a0400f40c01000c1400c2d8610104d4042c0b840c011100da00e481450210540040c40070081c00119800812074042c034900300320743c011003030b180b03591081c111868a8859401050744410aa0403882205280c4401a5070402c412001075038480158555480048107203a000d5000798810307108110300d2460b080c0c00c26600420341e65454a0b680c0304d00390488000350061100daa403c004511740c10b20600503c491440301500d19036225105410b01c00e0422500504003000e100c1140ea40840d80d400210840c9d071080d055048090307c68841e03040c154585030003000c1e4803040c004005000304045c2a4040614440c6100d805c241c0255a0344002c203030309a4a0504c60f010114a03496207100341450180b00303ca42c0540f0700161242e403000490f000500400380c1d03900c407101140c1c6840c01809213502c4c2e400c0c5c140c894030080d682d10165032502661510100e985100140400210350010301c011b07031013030100400f404401003c00c0c0700d604107410201f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 135830116 1250 135828866 135828871
    0x31409032d0a05061b0d0e060105090a020310150201021b01020405120d0f0e12061501030501090b01090e04050304050d030e0315010308070b18010905070807050a0e01060f020a1a 78
    0x740d00c0c0c006007020440c03100010320605896010020700a140c40c0c0c040c4124140100035010303018102c0500042e080c0912030720030b601e25a005a80105581d526020034802e0881e1b0181240c40301500400800102200c09484602110404d00f0842c050101111089009002e5600c044036050144803a5418001d015009441903030000c6030280407810941c2c0f416581c426003140700704045109200ca0210b4140a110740c20a80d45000d016200f0002c84170310141e09021080f42c2031440f103142c8182401c099685480f80501402c1d8080d4100b100c2c0301035400282c0181c2c200c0c499542002e8100000404124040c004e880003800080e020070051126860050503201d04c207a8054028824501a003c8401c49088403a040b650000380c0c89140400a80b15600002e1000704403017542c5001c00b00d294024442481924416402400a0000b80d424441502d0405d0015400703288224032045051105c410303200032084c111846418025140c03564000183e0078403288030700280500031440e1000f00ba8100100c502071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 135831366 1250 135830116 135830173
    0x1906060c020a05040c02070e040c0306050703020d050c0f040e04020a1a07060c0e01140703090308040b0d140702120a03090231050103050d180902040f0303081305030703140903 77
    0x2c0d04540314004c0c0700443c3d80700406400181d00c00d140c01c03c8003084000016030814000c204410f00e044d20394a8540684e1025600400041e5001504801002030351003050b800084c01c0d1281480c00580703803d180001d028074000d00da140003600d0003241c00c40d510180d10000400309026042c801552101c2c1c00d00e2140c021020a4a6040c14003030202d2890744900510300310498161211150307100c1d42d8410040540100400b101441403040001c170204031550068001031001595041c0e54501c1c1c4403406050717031208405480308403c21f02c01d0241c121340200320104010503c5188036110000484110042c1103072030000b9410140721040c0034500800402803039080c444d450107110b8454102107a29040321303424071000d000c40d000308044040710384c03144014000c0441d4043d40c01e0b41030743e1101404002c82e0b101d548400c980c641220b20030003c0540108100e6485a146003210b07a02c0c65058540507123910407940002c0420500e2950507500c103c184054490380800902210f1b5000c0e4880f800d0302c0019020203142 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 135832616 1250 135831366 135831379
    0x31a0d0507030b0f0f0106050d140a020901110601030209060405130609030507060b1e01050a1215030203010b0109060512101e05091003151d0d0206100e090309091906060c02 76
    0x3404c83c9001c0840031300031405074403120000c1e86040400c44060b0421504039031220b49441c1c804006a60410183e40a400041001a40c0e58046c0c0c0c005051034011040081454001c2c100400c00759448040d102e074007950940e4041030310380c1d4280f4941040d805140b002031005103880600c0050550142c050030350300c3d01ca0041000b00702285030030440880c04000c0c0820604541e054034554a52040e00901002d440d907080c610103d802001d18007050f2005c000c403445210070350f40c1c0200203620782401f81c0cac41c0b01503080c20f0403070001c0c0c14000014010700c54405040841d41550340459050004100d901c00240145541c0352000088400703000142052846407030b1180003050082039208000c0e000d40c20880ba840701c1c3c1351110441c80c100450180c020031060022a543e203046103a50740d2000e1100707494240d80355014088618003000c51403480911900000c0758282d44004001604c10008102d81c072020080340c3c046035694800c49844014112880000c00e00790030001c00048075900305d40c00c8241c480c0300702c520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 135833866 1250 135832616 135832621
    0xf060305070e040b18030313110414040b100b0a030b030a02090a0911010207120605090a0c06110d020c180a1512060608030702030307030804030c0605010e0a0e0f070501031a0d0507030b 81
    0x1c10405d909000d500011a007040010901d14071000089521152080c991000c0c2d100a1070001001c9940108114144202c0c0c41e0030001081301d0b40d40c21035401b0203450100c0241e00c0c2403c1c020205801a508014281982c60220380710f1503404110b10207615600410031070070341c90142001c00190030302001c22952009807072400000c6600204030700341076544101c003c0e09224950703180c0b100549006003106c0b40c18021002a60040f03038800798150301a0181d625200002c0052503010707071030000c6c040011801c40d000f090480c82995a020907120300c0c00700e210000405602d95080c410003c080c0c00c0024400b451880701d0004403680844450680b00780070310002c004090303030f03841c1c5a905c0384110304000707516400420008001034003031500c0c540c100d0702138541080d201106580d410100e0780207821584042c030401b000c10909140780e024800d01c00b141b0102424000c0b2a02c85a070340d840d4014051207041c562607014a006441151200540c8004000c0c0407c021004a0800e9600c40d2072500042c1c42d0b06003038100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 135835116 1250 135833866 135833881
    0x1e0f0f030b010806130e03030702030705160608060d03110a0c093b0a06050c0711010203130b03060f15030601020115180c05090306090f0d020a0809040f060305070e040b 74
    0x240c1d0140640c10707150b4400303a07540d4204110082d40e481e8003000710305548003a181d007425010005507101d081c0a4000356030341c400c141002c62900c02d1098010b0484c002d120403d0000603401240743d40c0204040c4d544a08041c032600d0107440c8445140d842c0c4d00b99101d803041e08000e1040d000e04040c22140707a1903003081031640101d0004182c04601d40780c040b00d40d0311003a6032040c0300d52400714052042c4e909401d59040424596612083d030300c040e104640311003030124440050045a0001c1000c0d4102400110710381000e6604210524045125035402203a01000180c525142e0101ca0b1855120040290714011148001c1c00101c4d0800d0f40d04038015884c000000d0742d07902460054000743c1d420002c201074080b079074442c48030203001d4001c050b40c00c1007070a0001141ca81c0b0100001c03070213a0002d60180101a10b1621000c1c50510724400e40401c41d4030031030403000403d0880c0c0c1161300c900820b60f000f0881c2e600c0340c0c14441c0541213035413000b06944210f03980040c0464040b482240550720944070005203855030300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 135836366 1250 135835116 135835121
    0x6060201060501050f0903160b0d0606050c0d0c17040801140a05010b040b0904061701050618070c0f020a030c0b04140307050f061602041a01030b1801060f1e0f0f03 72
    0x600b07804104100070745036051018002601141c0c0c402011500f0421000c4018502c0c0c40040e800f082ca010302c00310750401002c01c90300407170006d04881d1400b641001c0c071000900f40d982504080c1c81d001e001450038184c0501c01c0c0354000a0440e1500c014083e600d81d070740e121240c000d0801c44030001c022445100801e1280610b1b000e811b0480e22401a40380c107046c24114411100d50220302c0c0180e0240c0c0c0c80000003925140490b07081540401c510000446d440c10005009000883d074004403450300c070b10070410810a41081403041620340024010400703402030700c01700d0000303061508003070314001d0016030010f4881403080c02032003501c00e050b145009400c2020185a0390703084a008095100d283c110152400381002400361200c1d100301c0e400d0ba5802c0d605600811b040310001c0900b903020306880342c0c1e40b010a50301800745400119090380e650000003200c4040c8465040c1c1030095504111004d004403000c00d10404271426141c0207008078100d0034800c41e00141540448000c50008903000c2407888164902a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 135837616 1250 135836366 135836369
    0x80f010b100806010818010603060227130b0105040801022808040b0403031107120e010905090405070302040c02030d0f06051005031603020d02070804030507140316090c0302040302091303030606020106 88
    0x5803685002c0703455500065941c44401001c10320501d52020405060b40001d006a1000b580903100059650b1003148081c00c00c080b9821440e05004181004008103454604810802d1040e4800004044e004507004851a1240f68000100f940c00494032000003c8191684102998195000c400d014404541900c211800f143d020781030401440001b00800d00079000201f041400e246007920707000c4182e542c06032206040303c0350303000100c0011a60015580120300100944012035902c400c500d01551146d681d00301502009020301e403502400740f086030081042d121004000c0206000d44d4001c0300c82440104034600c2103e00c03650b12007185818040c05841100e0051400c008100c5c5501040c05043d4082d6104220b03030310a00340c2c00c01c0010086070342d202c0500040c51060740070344040ca00d083c0c070b0009900c0019443c184203400c10b60b0815684206000703040c08032007034a00003007184c1d80040402d0340280515800a50440310307000c1084031800f030000ca05191144203031002c2200940b9040c00728200d41d00f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 135838866 1250 135837616 135837649
    0x60105030f030f0a0908030d0507110a051009030207050d0b0604050601030203040201050a11030c010903030e101401121109041406150f0f0a03140601150302070b011e0f080f010b 78
    0x20882400303814183c0008280c1d4826909004803a156524625403655200070940c0307940607690024040c4440d44800d03540b442c0c68090f4000c058000268444e540c50701c05c01c08101c05404e0741c455109040500921840c0d008120040c440b464101c02070401e046401422101d0f00d10691900000800725030080c8240d038003894040e0740c0d890504000d45010750348505e40c24138004651205000500300070101740640c0c401248030f40c2e0007240d00701080e0401442c0034200300e01c41010905180060311000d110340076482c11503181d580d1070501c4160a0a001020b880041c07d201d8101001034100418000b441d510145100e215404070340c0c091b0b46800c006012a402703074403031580c0140c5900c104403440c5042500c0e0780d5078400003092882c0983c2d0f0b981d508004a03190b104680c6042e084100100078580c942200d0000c1c2d4001801c056141409545e03c46040035014003607142e00b071020320032a04074000044c4541014007141c400001c5219150200e260f6100104a2031050b95801c142c0710b000c1c141091900c80e11040c40d07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 135840116 1250 135838866 135838873
    0x7020a1a0901110a0c02030c0901060c240603030f080609040210030b040b09010f030c0b0a12020d0e2505030f0606010503060d06110d1406010e040b03030d05041103060105030f 77
    0x30000a241920800030708034012940d01c441d0036000c3d030750400f0700500307101000e03481d808440202c40c4141424520302004043c07048000c00e00400c2419000500c201469030301110340c0e01c0391443e40603403105010301c0052001b240b5181c5240030040640043c60500000100d131680296540d075107082000004044500a404ca400c42c0351100d5030f20b0280e0000c0c00b0310b1000820126660300980d0100e1403800c02648406c0c042e200d070050410500c02c20f000c4810150540010716441d1019002000c0c000040754228005a15400252490f00c54805e9100e200d00c0a4202c0c292078000c0300b828045145609000211080c00841c064001224600056904603050b003001c0504250742da040e00654841e00010300054014603200c0300350000a150344110300c4403a0b4170a021648034602802d1100844500a5002c40d482c10101e043c4502a0380000d0011100442200c000c03030806d9203400424114003c840f50010700c01e05050500c01040300c495407940d080b240c2642101c920741c0e622010103035031b4030380020210001d80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 135841366 1250 135840116 135840143
    0x3050a0c1514030912070f0b010602060903220509091501060306270b0303040e150105120f04030201020418020414030a08120a1118010914060f1e0301120b07020a 71
    0x140c221001d0f543c000859030560f17110111541c001043e6900100c402c50b40345026000480402a40d4001c4601400035403000b00200d02e030803107400e81e4a1062440d01906d004207030078141611103d042c13801c405000d010707010100e54284402415a03d480c0c0710341000c5c00e01d10500000c03039030320b10a1245100700c0b045003103000c031900b00c070503204020294102c3c50029002d4451038080d19a0300c007000244000c1042c80445840d51070003041803010050b80391340c6141080010892040c22003517140c4c030b2640010b1071a11100e5152103900d0305a00a20aa0380441034865402c000000e07888002d078090400c940801c032404c2010080710b030405480b1030f20404000c00844041c894041c1400d440d9806540c04206250b0000760070207030810350321041e00481c00c58494458591200400f65902451a42c000c10307401040c0204007035803100007441409449141603c946000c10b142d10f00b4011140c0d882810000c501c0495540d584513a03a106240c884a101030f61444065000300340e040b4400268a60800e421500c09a40007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 135842616 1250 135841366 135841397
    0x11a01230c01020708120403030b0d0b0a0c0c12031d0607090b1c110306130e070504020a03060e0103050d02061608010320130506151213140703050a0c15 67
    0x1e030484540c51200b90760038059040000c0d0824010b0054509141c1d118480745840c3c03400030103456076080900d02410a1040420014000ea009030b80c01a20052001c80c210b8040b01c022510411741141c0904030010300030305000415015404274040c11440305032070541025500311150355943c140e8288001a000000030001030b450030000c2d205a0102011003001c0c0e1007000c0b0510f05849862207014000c0c0c000005000c07141c0b03070880280114850300c07807060020442200c20303903803503003a1840b0b49130040f03400060101c0031358403a50005015000401140c012035031a4140f484d07507803402c0d4140a01500c14840440c002d0040d0700e54030328003269242d880340e00aa00759a81ca11604004511006442c4080740c2c000d1000e681b68008004050512140011540713088010441c945010b8050b0080540b81000110003180d1a07420b8142d110500c1008c5809200d11440d0903031401c040340034494240c2c0100d500c04400c00038041400501d55000e1130800910396120243c1c603844900b014140e00100b40d00041d44000d0707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 135843866 1250 135842616 135842687
    0xf03191112030702060612010b130c030908031306051311010e0a08031902010b0a060c060b030a0b13020f09010b03040204110c01230115080f0c090d05011a01 69
    0x91154000303079200d001c410303070180300503400c150f40780707405a0454000c000890804031512819084011700901035103c442e40031800300042e000d070420304240c448403640d103214000d801840c8080d500102455581c6050088032182403091007044465034106004140303545e87d406203c50300d4a421541c0402c41015010042d65884041d02d00c998111030030210008543c081440986140420b43e4912590310b011541700a00710381511901911500750320005004d510f40c040304002c034842e401071001403e86520800289005841c0d64010076440f642070411900c04c0d46103040340e01c100d109884c0900031400324810000055024011201d01d40014800036015182c582c00c40320310b00f51014002e610349100032010030300391410b2248030070070f5400382d85034010b21610032002d80d40104200740d525860010b01020044c0a020042c1000382070b07208000106003002440c40454030b02c80d60041c00400e06010510f42280641581010500f400c1a400c0381c0804a5005940700f408a4a0354101aa585640780510822 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 135845116 1250 135843866 135843887
    0xf0a0b090f12010b0a090c1b0611040807030c090606050304291609091a100201020c030d0e010f05060907230304060e0d0315030b0411040f0e0f0319 65
    0xa009091a42548490b20780205142d000100e02d00003140544983c010310100b0b05031948124111071030501844025540b240111900e0f07244d50360120480321040c104170020b061804107070340c150180000c0000c1c40c0e102c009030803012284034a01020400e5554441c081c100c03001c134442c050104d0310810000b00000c40355024003150220f140000d4004a4081c2c0003a0078111049590310060306102c0c100f550340a4000f0803142c01850402d006200c000e00240c24a00c0c0c0040b030141d4140a0100010300c0e06445000703405a07850a4411070403a81c80d2001e03030309540090301e40c050884c0802c0d440c22040e03800d5254940913952141401419980d441e40354070008a4200c444482e100d550580020001244e8200b518002d5005034007c5170045000c0c503420000d1401e103a014404401807500e00000454410110b1a40790200c81d00440c003050659500d0034042c0340c20300c1c5544516841f80c0390508641e56050713a9440025000c00c0002114035000d07080380174a5503441403035080c5400e101002c2c14030548901c1404001c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 135846366 1250 135845116 135845119
    0x308070312140601020f010501030c0b09150d05070306060509031510080604050109020102070f080c04020304060212090115090204180504020301021209150f040b04030f0311040602010207050c0f0a0b09 88
    0x104001e807580116030440301002c03010203075501c42c10280821580e0422000281452150080000b945599952150301505216215070244003240c0b0079680d54030020b2007600b03580780210003030341c958a0342c03140300040130216680c801017481e1a10102d080b031710407416241c40301d001500400c0d0b41c1e011444e000c90705040c000c1c4030b01620002c1500c08100d440c02400900c7c00ac911800c008030310740d400d82c400039042c01380075000200c00c04181c2504002c0383e040051070103c48181960010780d682c999081910192180b0f03490f103050302200d034060220f060f40c154400e10a250044651340c4503552a69003082c20707071046108d52a402841d00c2d0341f000b4401c60356480705030000d1004000503d40f1003030f09045180c50f039013110000b0098000e042c0c81c810704610b4042c00e59001c0c55145a040d400e10b05660303000017038070700544041c2c100081c101c00d446045001e580110458120b406500e500c50b50b4030700c002070203980441e108503450300030080b540e040c50500f00003030240759030020022440a820419481000d4100003040c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 135847616 1250 135846366 135846377
    0x90a020711040915110d060b030c0f09030a0b070807030e120a030209030712030504030b060901060f08071701180b100207050907020a0c14090916120c0302040f050f010603020a0903080703 82
    0x1860522032078400c0e07100c015010240c842e125520f40e003661003191f54990090a10602c00c1003045540f0083e582200c4d01c0e000746030306094480c420304000c80e10704071031804010090300c150411711107006d421010080c8109800e42d0148a4040e203000c510307855109104040d0b0755407105104028045000383c01803c0d01e030300301030100c900c02c80e61440400c29681c1a004260042680050180b01788110720001907480034044d0792403049075144c418010080700200846504112400700401c4284d40b1600b1050701000389810250300ca0358503a408250204900f09024111134601074007402c0a00b010031030004104015005846654030340f500380151040d0040000c41140130b8002c48000081d0400b80e0320300501296011380003081d801e0005d00010303200140c000340d41548203800d8404114584070b944010b41798140350b02041001e0a280c0003402840e207810095000d03061500b1242c040b4181d6012500c03540000051a8145c0d0303a03070320254220b1080b84078000000301c1d00d000c2440490340c00c1001b0326110b8401c0c50308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 135848866 1250 135847616 135847643
    0x3030a060e160e10120c05210105010903080d02070b040302030315030105010f0905041703090705090106032009030a080c03030a0c170135060a0b0111100b0607021002070302090a0207110409 83
    0x2c480848025825075004034202185c00c000c1c250100ca00390013074000108c981d20155041000180c080300c2c0742d00c0b00074074448001805400186694050321b0382e045d44200d02811038103162402079101d801c1220504045c1c205d034041d02d003640c901401554102c850702e11581c1201414030304140080c01000300182c0700401c1300e074100212a143d1200441c031494045004e808124141020458105810303030140382050b0818032040f008059149c00750040621103882d442d80d981070000402d052802c0808081c04088000c40d120009400102c000d51042032240c0b41000301040c00749041d10f404209506064a8001319001031003000050101c110343d40800050084c005010014048921103c0c0c070020400341d0401000d00c03640e49490f000301d01902c5000d00703110541d2a587d08044da03403038420000e4000d01c2520b07040102001c0e01d410040302d0601d900900032100d1612000b201070b40d80c0e40688012802a802c803030002d03102c49624400d88034811392110100000001001c10000039100d006001d8a50005940c4c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 135850116 1250 135848866 135848897
    0xf0a05090a03121205090c0d030908011401050909030a021e0c1201020a030615020c01030b1c0506040506070212070209090705090a062c04150e03030a060e160e10 71
    0x3107540086205010000714070201100040c001e41100480e02c4501d4100f2052004800b401b048010702c0c24402d440c901d0040c102c42c1800c4070513900300e5201c2201c40d4a01950400d200000030300a90580b6426148521644c0307811150350b6036446604c00c1040160444085003d903e041c080824889069901c112008030b810301d000070b0688003500803d011282c0d4001006100150103018600080c14a0f5174080d0000c400388802a4440c03444030121810150346402c0c01e203150703407040c02803e011006031384072440b06407003880c28980c4c800302a50103580f41d104110000341d24506c000744955840031903c0100d400c01d0070b10350902020181c007900c4000e5600844001007640d032105443c00c0d101e583d0140010031418945070200c05000f0752003803880d002000300e0156620a403d40e680040e0403543c004c0340c00782820031405208005080b10704c0960308502001081c4444400180c0021060740c01403081003aa607264611540358111b440001040424080d0540c6030061628021184030f820040c02e015045540100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 135851366 1250 135850116 135850129
    0x80408090907050712080f061207081c1e05040317160c0501030b15040b0306062709010504052a09030a0f14030a02060c03061302070303050604200f0a0509 68
    0x5880b5030000e000822a14103100300c509200d6414074007810429078a080072030102405410003052035002d049804504200c040080041d0350003480500180c032010000040104003041c204100c44001840f1602855030360040029030a0f100320045c0c44691515240d5503a00e2520500310768150f141c0001030101496144082100e944080d20802409460131f0412001404441e255540f01340526480f0480050802d1200100e60030303076145185440e2282e40d000c0008883d03201c0d08603418440c485481e1b000e0180012030300c1d000c0701c1c15411503154039182e8880051104440e0201c0714500c00b81901811500c01400840106080076207d5105514040d0b01501081c0341c0490300000301d40900d8840241000d1088049040500099410280d4600320400b0070007595094098150780301d1401c0080840d446903200c1120503003503c0d07800015900d9000364100035004080c00c8170400e0207a41845107601105100f10038034280800401045420551014649011600100030006c10f008007044184010b0741d522 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 135852616 1250 135851366 135851371
    0xf0504030203060a0605120304050603040807020a05031c0f030c0e1504170f10020a0527040c0e0a08030f0708090f30010207030905010c031709030c0c030307050d0804080909 76
    0x40010650790300d03006c14404011899600524a0380007444248100e940740c1e0103c030342168000000d5501c501060001404c01e805950000f03603d84184200340d101140301076400c007072503c429100c0d0f00d0700d800c101209400740c2d0068042e24001900080d1400c0d41841c003081c0100c240104c45441301d0030262200e00351012400e030801982142e0f48120490701101c0030401c4448121261074506506012038180054510300440040314114159092454071064442d4a40c0742d2105000b4030074070141c80c02c002c02400c801c503446555801800055008115a88008125103001003404506447d0080540301c0400c00e404c6001e4042d4014811040c82c805075544e980c1c0007001c20072404003d40b065142803402d0f0700602280d461200c440c1d0051007040c01294202e61020210f03142800c1c00f00105c54a440e00302c0380c2d01d0b829540d41c02100b446c40c0622018010010250543e10303618400c07281c200c00f01c4000c00d9641d0003540c1006010358008107203040b44520843c40301d078102c2d02c214401400c00c0c0c1c0071000618001e004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 135853866 1250 135852616 135852631
    0x1005011d04051003050118020a05060304050a0614060103051305061b07051e060a0b0607081c050702060115020a080a050c07080303072d08160e0301110301052b02010f050403020306 79
    0x200f1051090203001c0c401c2207140c045401510340c2102003503001c505d00500c00c0c4103d0344107a4011000500703020051056400103584404104840500a8129140d200d0300341c40d49070000b4642800601240000030000d900c054003c0c000380000d554a6081c1054228011a0b00d200c080d41030100f070340001c03010803450441c401034200c001c04001003407000d50314002e4010000b602d550700b00480d0b421251100012246019084440c80341d580c0d844034035103185404c0360b41004001624120400003004d90100c3c0c4241668003050764070b0b0203200855000c0b03a83d583c06000180c0124410094104598090801041402d6500c01a180c00319601c01d082c0342141c1040b03462001044007200220250102d011040c08602d010f0140380364003617a00c0c4001030008400074090000041034203104581c10340109030361511560300030020711601c29078400e001c8107a0000c0c42010300030105040c443c5480050610052014a0080c0c041c00019804e60011180c0c08128010f4105118040002101684080c001c080c030441e00e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 135855116 1250 135853866 135853891
    0xa0c170a020a0314070c02100507081201030302121804050612100606020c33090604030317070e03061f1a03090c030f070909020a12030c03171005011d0405 68
    0x34500b0041c050300c001c54414a0a002d12600f0000a56001249540101d4055814001e0340c4802c10302038030144240100070301003c4010480b007440c92082c0c01034505981c800e40c2502c602101c00001c0c00002d0041401d07407108103444080001c2a8106940180c0d44420000c0118602d403155400c03290a02c400d624a50300304980751602446100d404000c40c81a0007000d030703010904030044100080f5100702d40e60300c03074030701c00d5030034120b80e080c0d0729040181c03076141200403c420341c1da40c0c0d81d00d0081c00b03103a4a45032002c5c0e8144454000340810307001d03030b14140501da0042d01500d01503582602e600740c5044080e104001e5100014800305250030b0b0100203000740c0500b0340306640d0340e0800201d0740d482c1c125910310f6640b0130380c0f0450003c40c81850104880d42240d09a10f4003144584c5644001000350704250481844100c0c19010300c02410790104045861a0181d241c100c00382c028034603078400030f240441d0740031080f0002da10200029442883c14072200400038044074030119010340024140d6005885580704503c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 135856366 1250 135855116 135855127
    0x40606030206211b1206040902060d0b03010f02040803041502280213060303020c0f0f090702010504031103070309050105030a14070206011536090603061a01020d080a0c170a02 77
    0x4a500d0907207074100d0301364070004c140514068a280304a129840f1603840c58078221010529a03265900b1a000c40360b070007040349803203643c01070304130f00203081440440d4425820540c2c40201a00f035442210191409100514601070810007100052010042008210300c90142e0035651071055407041d0218030355001ca1040301283c11f00412010760807204950751030f240750030b008000003a00003d002c810303041c0c2a140710100d108104005046007202141d403a8002c0303158001c2280140e41035000511851003034031303041c003480064110981e5134060008000d010860104c024011036008001869000c106010081a1100000444811441c0c10b40314071015a1140c0018003054640c0010b081007a00c03107140045040d035151403038034403021408000210140c0c500a0b95810034004400341e40181c41084424011a940c9150902c000c00c090008140302c0b010550700d0070031961003c06c1000300e002d200e6942c80710b640c0780c3c0c4444000401c000415801406182c0d0143d480c10040c980c5414440c0512000c01612075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 135857616 1250 135856366 135856417
    0x30109090c0b0c07060e030f0f030d150303080a020306060405040e07051018031e050d020d02010b060f0d0b03010f0e010b24040b0d1d03090a0603060b12040606030206 73
    0x105250001400c41105018008403c000020528200c03505498102400652007012a050150b04000403e1a002d20510002c1c2c0080c008004e0500e28081a002c2000c0c17002c954000c0001081da01005000481c808003058411201d07401075500400018941841e16544800160803580c0307000405c1040d4006200400261901c50756800185c0054203003950101d8547c4140012800c050000030000c5d0324000102c1044558541b08440055002c800c445103001d03042e0010750b0790440010000019030a055110b0240c0c20700000b95280b40f108151003038201424201084c0c090310409411a406641e0b4800c204003029490084080680d84803000040c60084c000601031200b60740d6000c0140c0c0b135290701e02d98807440011012501114070b58940c2544032110840a60f01400e07100e8039070407201c0c074100000400712102000600c15904200c81040d0459980c0310705a00f601d42a1040e1500d0f00000e0040e0031070a000142c400e5401807040c507001410545036400194a80c000c40010b0164042c10000450b60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 135858866 1250 135857616 135857633
    0xc0b0a0f1802190b040b0c01090614180d09060c061b091409060307030f03020a050106150215010b0f0904060b030a0b09090606031b0f0306010e091504050705060309100203010909 78
    0x2041003c82c0300392035506040301103800d403169105400303030750000040b1080e85441c03e41c4032444150344914184140c01c03140300c48210292040e64103000e20210500040c401c1c003030004800c40f040d0000d8640ca00023600c3c044080d20040c81c44501076035200d48075511b20740c02d56800104e0380c115207801d86415040e181410803494001d04440885030241806909002e00c5907000141001101e611101c4d0f88140006071404034105100c0c0703400185690f0034000c01048c0c0350303111120242d40c0c2145900305d682800601303620b1605d0800030301c900044841c0c1040f10304420f1120000501c1c400a02a00c0403611642d0f8501c5c0743d006920458008000940d02c20071000303540780501c81c80e0f401203c2079004261506001c80081c2e21800c15401d0584518100317500308101c2d0b1503682001e0180000241502c0480d07075110383c603240d845000c949000341c40c05901c407016070300d002c2e4085144c042c07504007008189403424901800081e91025020310540d00c00e50141074240e003040d0006501800c031702400804c202403507142c00c004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 135860116 1250 135858866 135858889
    0x2c0f0d0311030103020609011709060a05070509011e0504080714180103030206010e040c12140d210507050f0406050406020c3106050618100f0c0b0a0f1802 68
    0x41504003090000401d51290035681074075012a80030755188518001621040c11160b90411a40890010031038122000b0541c00e2050100c42000c0c00b941c0d841180880d000d01ca49184180441e049540721102004034000c03140903031445003015464551103e40b803501d01130441d407098048101d10504a1041c5c00c05004003a00607016004e031400303550440d03030065120030050050303004106501e0000384c1400030a0888400900c0d40061404408903142000c0e1303910240e2426510704c52080c050200c1220380b04010701605004502c803004a1100581042005000094010005c02c0024000c0c1e140003171007200140020005030301e84940d154503000c400780c01c060748403c01034030545281003001c110890fa020900b101d0074040034031a1a04900da04661300400f601c0c0c020b103400030b90208002c0c0802d607046a00340c11840701100c0100400f001007404941c3c07420301148440000350550040c4001801d941000b0350481969100030602d04a10407066040781c041c4220042d0009180705036000f5410b15400702d05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 135861366 1250 135860116 135860143
    0x902030103080d050403181409160e010509042d2405010f02010e0d03020d14011401110c03060f040308070c11010e030a1a04030807021b042c0f 63
    0x1819585980c80d2092036006042e1024110760300e980000d010107208000c10841c4072030042e21020950b880b40d65000d402c411441c102070043e07643c800031405041603980c400000c90a1a9030794007640040c10011505074020b84c454680040d04e46507509510001901d4102c00c0c21003911902441c083c038102880c00b5100c1c000c44032a540c0700c1c2c0c110108000100301011070140c1e8028240220880c40c1420120f00500d40461800d00500480300c80c0344034140d02d500103203c0034014240512180030680303041d042807442845114002018084a1480b55021302007110100520701d00795000c00502c0c00120b418034a0481d600d2201107800801c1204043e0480750b00b58010740c051421485070650359070b481d9203030206204002d062100501d007400490794200700105a03e0350040360020492070300c0c041d880b1441e5064804901080c0100001050548009148a18025105c0035503c0131a080300c10311008100700315070600d0b8801d0b2916405101424041d9588490502400815000c1003000516003030200407000003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 135862616 1250 135861366 135861371
    0x8061005030403020a02010e060705011b1101050c041202030703080a21050405071a0c10091103160b09040608010c022506020304090203060607050f07060306061e0c050c18090709 78
    0x2c0425400514020714130390a0130b080c86c2c085507400002c2c0240c041d004d4002d0540d03080c09902c909441056808801c2c081150f11000341600c0514134103400e9840c11580c016800e10240700410a0030703000345400880ba0f0002d0b09491059840e03460f00c4840390b121b01104000b05240250b407880e100c1c90600c409905868266081100c0d040660328180c56400703d100e00d454018480d045034496048010031208259076200440e90003009020805025000500d41594030842114800809050200c2d0b400010b0060104800a860902e01546100d07000303101d030260815500c1c0d0703000c00d00c0f007001d21815030202c000340c00402903d000880c104010161842010301c440f2804041040a980c0001c2034400740c680d08400940c9999074540410018007075007001620522407281e696900450102d0b040d01540c10554050100c1c548500c400d480408980e2641da0040b0b1856940d511102d01c0780405801d010b100700309643d40c049451000800c2d12415054440084018009000d0030003000c01808005110241c4203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 135863866 1250 135862616 135862621
    0x270a0f181b1101020c07240305060108040609060b0918010b01090803070807020d17130602010513021c061b020c040b0904120507060614031e120f190806100503 70
    0x10101d450070555440303000d102c40c40c5800420b40303000307406684c10700079078904981006548801100022000010940704031103600082c1e11140c0c840e02030f06201e05810307180c00c402512141d550800a0010040030f13140c8580e40c8420007200c2d582c010b5080d00611003d5072013a51189600c4910342110131910b5040e05010540d903040020303490110640d1030300c54100c403029440d4034407400410309450303030000000c0a02c10356076401c030003a0310088064920310256600080d072140d102c15050742290425609a240d01080700c00c14001840d01041c0741c141154031412100d000e4245941d800295002c1d190000c0c90605003001468542d9810800e640d200c0500f00ca00344203460086012400310391002d000034051000704940b80e03406a01510440d0001076014900304101641c1c1c02140e040d0001d21085903110f07004035211000100e2100d0950b5041900780c03c0501004000c024850303001c1e901c106821040340c02c2c144840a078007888200c0180080c1c01c1922105868544581000090022004400d050110500a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 135865116 1250 135863866 135863891
    0x3030f06030c03010e0d18030c150912020f04051807090606031503020a03060c17040b07091e18061701020409060501081b031504090f021c030203270a0f18 68
    0x1103d60005e01942000c0d401d01f640c2502012695200390070103841524500c1c00001c07407008480e4105803d40721652082001c0c0e80320480034101000447c00a94000030f030604188651810f9807181340c200382d80240f08003040707140c5080607042142c1c1d507104c00e50300e40c0d0b03881040011507003501592080703060001642280d2801c0d43d00241c100c0304640009001c0b641d80740e1140320203070301a07440c8840400d2080343c01525450649003016100b50308440504c0001c0882c5000034410303480f80c003610041c4001d40c41c4141624140b5a0701c0c01211007400140440c241c40d11000a0b580b0101940c0304c81070500c030b10002d0b81c1c030350801d44201c1c02d4410a52155042044d2402008041d080705a903240300702d25001e26160740ca440751007404005108030b000711a0b00500d4149014104aa4005030100c3c0e03d03c00c1d2002a00d8200000803191046122540076000da0420400384062028889a2030680c40080d02c1400c204000840031070881c0040340c020304021b200080b402d0040000c0f418020302c83d41000282485005492407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 135866366 1250 135865116 135865123
    0x102010c03111b030403020303040f0906140306040311070b0f03010f0519031106301b09040b06040b0309030307030f020414040213150c0201080c1612030e03030f06030c03010e 77
    0xc0040d16000008201c2443e040d402d1044074003c54004045a403903944a03412001421140c3c030420078018030f4107900081e500d25994052202000c002d0281610396616203050f501e4440322501c60109001c0c0700000310780300d080c001c042c0140310862541c1c01d40b29070602880c82034102c903c1c0c20036407150f50401c4040e0200700c04a210441600c1e8400e000d4040b00d80c1d60b6012070124001c1c21011409442404441c100b65600418006a580b6080200726840e0302d401d040880c8180710882d81503444075041004034100d0506030030140480710080c0103e880c15135034603640c0105400545140306c00360000000d00404d6503240c002e40118034144042146800e01c0c20071102d10f01c1200d43c1c0000d00643c4c001c0342c800b08205a5031010380c02000c04c401040d4030411100d800900340c501041d002c0340401c0007407020850001e08002922a0741001001c500014070260700d4070b01c2050041948981050344942d2180c4440c171040c00614068601e00e4442d0143c2c1c1000c10405003000410510580603a14052807841040c4002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 135867616 1250 135866366 135866377
    0x102010f050402091305030f030130200102100213080d020706051206030118140d030908161e030e0108070c110f0d170306190303021b06160b060102010c0311 69
    0x150008807001d180e501e0494158083c401d00d103803855001100000c0e000f03100f590040108141d0bd91842d46282c0c111240140c00040f01c030018285103942081050031101000f0325004602050048801c902e005100000c240d030301000841400002c4c000013000360000c1048914500e00080c000740c1b00c000c2c200b850041c654017501450300c44501045000c0b07202c0b80c0702036000740f105042e80c0d64810f00c280c8603420b0042415944140c9407140740f00d81d108402c10a44244140d040c590340c041420307403070300b00300c1d941c1d60050741c420000135200d022001000c440071540882405180301d20a880b0401c06240080000d000060014400400c1c010980d0014000925241c3c4928503031808403804d005035214800456000042000001d014103082d081199000304910041e510034182211504004603584030758141401a600c0000d0160b402132208a0a4002d1070000d0303410001c000d44000c0c20902c0e481204d80e0000d802c410300755801c0c2d8511050000c2940d0a005510b041030442c14140183d000e400780c40050362207103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 135868866 1250 135867616 135867631
    0x26040819020d020910060e0103020f0403060509070f09050a0515030d360e071b080f0910030c02011103010f031b0306020f030a0e010606090303050c0a02120109020102010f05040209 79
    0x685250104654035280b64520060f005000a5258540601c2d4404800114041c820100c3c02002441c0f04941c80307802119800e648440b032030780c1041e203965204000307044054038000035405850004160485c060309004000c2413618008941404c0500c00751081ba0006841080322800c004000a080d840001e07407a10780480c2e0340f411200e040c013805071150004034104080004003980c401d1804001049005038001c0d20701c6c050340401641c480306006d80e1741052807401d002c1a048000c40740300105004102030108071880d80c04071450142000001101e00c82542501c01c0860380ea100e044688903424400c003842105200d80c954a1541007002540b519406440020550500140b140c91485141c0300d85038000c5600000c19034031518020040f0515400440c1d00e01c1d2554a410344002075a001401071804a40d203c0d141e40c6c0c0d54501b1038404503190744c80301036414020300c2a4401e200058a80518070404192030400000d40c0b4080e5100080c00d58105074141d540c1a4107040034003016030b440c00040d94100c6031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 135870116 1250 135868866 135868903
    0x308090d050304020d0c05040c1808030c0d0f090f0e1f140409020f1c0213020a1b03020307120302180d08040e070c1704050a090203092805060103260408 67
    0x440c0d20b481b441c13480c070b0354004a0308a424501411040c5404c1008951103103003601c120300680380c40d01d50190341c900414202a1940d4804480800c0460050403280e4401845142c0460080c0d1601c0c40145840050b6001003040b5000c03900b00301c1c2c0c0000348015640c048034900011030403185030120001c0b1401d941c0e060750340309658404900e400c540d80e0703a5101c0b58002000d030203048004078491a01020b802442c4050b40102d82c545150f0141f084ca43c421a240e11031b181d1100c0c0040241e0754503400900e9102507044003036200c1041080301184400000481c440310656015940e0201e04010030702808484003100d000f42320b101c000c60001075001d02a501a15441c0300701924a688904080316241030b0340f00b000e00140c3c50421125800301040004000f03850090310300360115980c40c5d03540d404074171007112030722225040000c12100050340402c40300101c00746039440399a40b200c5a250726003801c030281d200b120012804051781d0b00a441d040c147c0c0b01c1170300f002480241810700d02110103881c0c3c0c2c0e024000b1a0000c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 135871366 1250 135870116 135870139
    0xa030c03030b0a0f08010504050d0513060320070605090c01090b040e0601090e010803190801030506040f0501060906060302040f050108060d0305030603030d0f0f050f0105061b0705060f070308090d05030402 90
    0x443d00c0c000e4a0051030b030041900641680c800c503d034024034082e9403c0d9294010324112a64043c062000c07903040312a242d4819940a2424600b10002c00d84002c02101e00c45840740070804929000300904005802600700117541d082070b00e00c05140c520410200b506003c01d54900b001848101e0051390101d4040074805491a95031400484110420b41c03c01c00400345c0d03c2001082c000800405011240d49600040c0302001307807140140d41c0c00b00d00344001001d0341c0c403807000207000032186140402124400e4002149040c1ca0349010000d031020740d0422400641d003c0303400c01c04005000081c00042c4000c0c2001070b65818040f0108804042821000c0c041c030400001291942d101042290601025107070300308024824003403444090b00d00396150003009818103020400d00c040751100c5d10f0403940d0042c020781c03410b20034000e001c07070200022250602501079400c00044075150072004005440d01c0d51840350360ba900614002c0c4c0041800b80188090381d00c140701805503e901f100c1200d401680442c0c40d0401c00f03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 135872616 1250 135871366 135871369
    0x1031505030d081312020307060605040227030a05030d0e0c04050403021207030c08030c0702131b0c02030309150309060115090311041b0306081902060703030b01020a080f1206030a030c03030b 84
    0x50040000c01014510111084045e241d400310191103840d1003050b043c008583c1c1c2e242048280e0080100007001a10340c064940481420600540c9021001800b520708a86031078448608542143c8195212603071101c611048c120001d01451b940550120f07001c2295003080c0c0c40013542c0c1c07454295400036550002408400780b501515815210075440710300c06d6564a0540d070503161030f41020740201d000e0703041d490070319080e02c0c4580150841c10309a005901c0182200310380c11105004141000d80c1c05000420041d00c240d140c0044001150103e0321800f03949050801d030140c5010b0050703200711045001688001e40b00382d44103c2c90340442e504030142044034844240024003c007581c2c149450701c82c43c80000042d100e505500902c00316444030041d650807070415108007150f4400d50100a5002e0000c1001800090107648060700001041c8110348105180740d8480489a00c9284c000801c210041183c25581d1040c0510a5102c0d03c10303070280010042a40c0c000c0c210104070710005050545510f24a402e0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 135873866 1250 135872616 135872641
    0x30e031206100c08040303120507030905120f0c0115140102070e06221a03070506040b03040b040807020d1a07030905030d0e0c030106120b01080d0504140102010b06030c0901031505030d08 82
    0x43c541c0060555503070b41d40e41d00d400360007581140540310600b8285000981003600030300c22203401d42c1e00040900a4000d8a0300c0100313031340c2c0c001d00102003c00001e201c6a002c0c0e002c2481100e0300780300040c1a4001c45824440607078401241d010f0860304651200505001d428550b40307800303401190030341d0b046c0c41802c800701c074041c40c40c1190001090306910300710298892003a880c0b400e9001540540035213034150b44032030034400148118010a04c243e5010004240064034801015900c940147c0322a030610070240d000810300d25802d0010b07118211107107001c040c0c4040d0248040d0700070303220381000c00c50f200c05995003d0b01d030700591459054669541c05005406507080c404c0d0121101c000340200304a0392950f0031440030000035207058418000e05400400d601000140065140f0140d03140caa0070b0500d000d640c8802c9405003000d441c11552268010b5009480b4940510701a100d140491510345025100050032500c0313405888140c40110841044951008605520690443c0c80c20400580c2c50a00c030851 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 135875116 1250 135873866 135873887
    0x1e120b04150c02011505010908120903071703210609010e0a1b020d080a0b090c0a020a0c0b07020306092107050c030607111203010302011209020310050a0b01030e03120610 75
    0x2034060400d1020498550f0661110350400034000c010390245440b0001101c210b07100d406224441e900c6110f901003002c3c8944041d000d00702000303086540e030f40c0d00d5441c80e1042020306031101c505540f02081c555038041c1d0303006451100c1a054100440301e89495400964503040c18030840031700c040b44101047c1038103601c0e0000b02c615105400304c404e041c0040c0900035994943e0994840004903c54041201e000c00c80c012010882c0c401000c02041d46c5844071044d0490340004071700c800794800d0341d145000050392818840000d0240c20006511801c01d80140f5040010007844911545c02c1140c1a504000c0d000c03d011039a007046100b45d60315002107261a5107080c0410246590501c24a010891219401122603207400010070580d00002c8004549684d10b00003800000d01007070302050780e100b250fa010341c4401c2c040fa0000703007292480c2d844119854103d600a6901c5142030b9283c1d9246601540c25024000034a81d465009614118882c10851050440038100d5403007140c8442020100f075204502008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 135876366 1250 135875116 135875153
    0xb0a090605070801080c0306010312050f130f090b0102060f150402040302031b10080705040b0a1407060c020615130c03060503060a06080106060906021c030e03040303020102041e120b04 81
    0x119074100b041c00038007040c07401d01c507200c124030844907030001c10304011540f641200e5100101d88507880380c0c40404c2c0c2c0c06420007044c0c0c41c000d580901050301900564030b11071006001401d0050710403802d2484000c1603680d50b80780305040d03512010910100035201d0440c981e001d03000c8004422100c000000090280c0f01d40e034000380d07045c4210f40c000d840c0c4650801d20080c80c001c08a40b146000c0082c0c840541d00b5603030864280c030116109010800403101d0754001407070741d240f10b840d100c903104005110300b441a800108080c1c1d02c0a94407580458015010030446401039080c0c8100d0344115092000500004d800056074131035103803503d510105241c003d411940241c80f000f4261402442d004100e44002c190b90710820400e9800c240c00020305600074455017050300d00b00d5000d80f2075a10280d0415407459900b40042d01015514602d40d100e200702070010b080030b1403281d400503a0303403441d00708107800000c078080c020125250309010400541401040d0301070380da544000701e042c1580e04c0b41800c0410610041e81300703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 135877616 1250 135876366 135876371
    0x301020d0207050717071a03090c09010e0708010602030f0d0902040603080a1d0409020f010503040f02030708071d0702030703080c0d0203041a1609050103090f020a060203130603180b0a0906 83
    0x81c410044007042e01801e9070000e00005c0d040e1003180e40f00e00c4c6d0f10b005d14801c5030781c1c08818842102c0d2003800d010007540d1061440f030880d1580002d6502280c0c801e48240d1002803180c0044041c40900381c0d1083c0480d005200030300c01581001400e006220452160510001c18556107619020454460350040d200942c0c00589043e01d541d05501c000c2d0124015143e00e62000c058118058050300c1c040c8900c004854015055400c2040c009005640c19400540152500e030000f502840042c0c2c5e080200ca8003400c59400170345602842c088480c6208a05103103456241c0b41d0032000c01c0a030550000c180c520540c1c25140c010400c1d2102c14503007000b4032600c07124041c0107000204010900c001081c110315a416100740200282d521090404034030180c0c81032900003d48500020000c5601c130707030801000a80540c0380300080e802c1c1ea03070000742c4410b0395604c03820160300045400c19044034035414010007000541020b00440003480201d000403030746a80d00404010b0900c001c600740f202140d112003801907100808 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 135878866 1250 135877616 135877627
    0x20f12120c061009050f0112080c070b0a0f09031505040c0e01030807200d0809150705010b0306130b0a1e090c0e1503070902091207030609051908180301020d02 70
    0x91512590101c40c01900f0300c00303042d000191510244035142c41803049458002c0241d003400407180c42070300122030903141c404c801e002c4410f2841e02848000010a0150500c0d5070310380d02418090011244418800c0030322030000303410004152115003003002603030040800141582c85180908089000350014804480b80c00000300410100c10020444503000b0f2a0084508501d8209040181d01000515811400181501c0005040d510140141820081810700500305031200d81d640e40e0030001c000d64481c1e45075002d0a640d41401c0c40010781024041d600021000c0700f685030228149005404000000c1e680e124910b02040c4141c0d90a011001a2000b0b01c00b07807115041c20000644a402107212820283d408540620101082c40b0032800004d006441503600d000482d000a4025001554008004a1050000714030510441c00607502ca07043c00212640e0360300708149130009158001d0282c0042c2c1241d400451801c50076191701d400c5414012680d00c00e02400300380a4080da01100100764000f149 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 135880116 1250 135878866 135878887
    0x604140c090105121603050c0c0d0c020310090602041a03040503190c120c03080718090b0303040e09060711060618090c060406050a02100b06070b070e03060a0212070804020f1212 78
    0x481d0603030804c1a907411310462310fa80c4030404047c8160701c451402c41d0300c0060b01500c80c9000701800480c40e8001401c0c2c0e100300d000082080c0035108003503800ca0f11640d0000e4103000110f0000f0740d0642d0710200806680c15880c1503943c180c0e0328030881d800071400114521100c40201d06c14058001c085500074401c05091036100d901a1021068001c100d000c1104100000c1c605807184d822900184070700d0080382d2265180500400003045205442070701070104020114800c3c2122940b50700400002c00185054034040d03500815481011003081440e41224060005542c0c4006002c04000440c0300c001449484201845242c013a403401f24542003e00030400003521500203014116464560f02559121424400100d0494a8a5890715801a004e001da0400325202065641d80069a0300302004c0d20202040080d00d0f0403021944400044e4001410008410355410465040321550800003d43e0034554001030740320000540c851b0064042004000400c0782c1009014a400100d5418035902e040c28034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 135881366 1250 135880116 135880141
    0x807030f060b040504080a0c05070b0a0f020706030c05040e180a060c020d050c030403062705010507090e09060606032e0305190b06010f0c0b0901060501080604140c09010512 76
    0xc8191880303858449802e5031810540102c62040d64000301e4245042c850001c00d030780310080724209076400e201e2a40041f60202d0903c3c0100405807054880400300c681035071009190090b550030040c101070030814040c154540080c20340d011341e1031205800700c8940d40d40000114104170301c11012003074410340401600f404034070343c40009014500e609660004164a0b0151501d11500c110580164030420042000c500680e0003503040d0348034405082404031150204202303860342218181e4440e5991024440110b4224450400801202040240703c0c5000c0300e0081d29580c00038490b6000e20b60020000d01400b00b4404900d40a0050f0f400034007024a41c8440c07203204500320700040f113061080102600100201c00c8410035016031000c081ca000303586d48401102c0c070a0380030038844140030001100301c0014489103001031103541e1a0000058181c908800105181700143c0701070300440c0f0302800842004103084003151301080952003140d4403444c1c04012101c6104241c4103841820a08085c08140380889 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 135882616 1250 135881366 135881393
    0x906071a0601110a02040903020a02101d09010501051902030906070b0114030327130c02010b280302060f1306021e031306081306061401110a020609010513080703 71
    0x418a01440c0e890a0064480d086010008481913000c501c0240043ca02078118866171403007031054a60801d07032540421201d50350701d04058041103400c44490006800001120543e00d030848504025501d804000b800c1445a545c03010307040c0404041048145000308112a62544081c1c8015520b12807400c041d4041c61083c02003100e510508002020320386000021741303000003110b840005416100c6a1000f9031008086086074101c0c203001c145104142040c0b00314000015180c0011415600f18401c11a110b15009000040c56154141442d003c108a12842702560b030f043c0e50780d6558102d80b05150744940602d1002800305d1560301000300b00faa03808a248a0425014621581105050200d070ba07142e0060a0110130810f0004400b080258030403000d03140c01125111300d2417160841c0e0749071442501c0d550381200f2100c04c0500410012035074400c040c081203504860140c03005c03120a6000907620300c50204003c1c10000007040c0084c2e070401250040c1d000304000d0040754291580c80c0b900b5008203911 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 135883866 1250 135882616 135882653
    0x803030c040f0b042d080d030504050c010c0803240d080403120903050a1101050d06031b0b120f040302070803070c09060e0906060405100e150306010803130306020f090607 75
    0x4848000448488807420313101921034140700d400d280c4800050b40705003140c03240b0b0074804500c02c0800000703440d541806000c041c182c050743e001c1000c0c41c1c1810b00501e00348044011904025900900002080207402a02c4d0018200ea8003260a0b40c0030703400d8024006000010680c2c010a9404002c0c02c22480034000d10459100c2d080307080c074014801105544404081c070010740035400244560740041e00b01d5410080703901e01414514103154119600400b190408c0c1c0086800c5199070800c83d208000c101c42c004020510048803d240c4018214080007018000d014690301382c10710f4001c582018001e2002e900541401c070101c80c2c44081c0c9040c0401000f40c0d9100b00b0004a16048000c520402c8031850640301d0704c2c043c402480a900c40d038051000030071009041d00c0d0114060726000c5090080010140c0c0122040b5036a200460042c000f0036050480683c8501055841084030200c0c2c2030308804110101d903001480183c4443d12240340c40c2d658400d403007080e980300703100180d04002c0245510b08001281e18 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 135885116 1250 135883866 135883889
    0x30a020c0c01090b090d0816240e03270603070e0418020f130b120604110409050a110a0e01120c0603050702190f06020c0a06050a05011d0703060803030c04 68
    0x2880c40040d40e95140c01e0103880081d05040046002d54185100e0071001c041c4110203061030642040c800b90f08e00c0003140307401c0780c2003c1c1914130300c0280780082c51145400d00c20ba40040203140c04480d40716070f5030b12860170f03412000400c5103071101d4240042080740000341d00c003410190380c0340f5000d4070080010100d841028071982c6080d0440d01507440030400d1006a65010304042000705006042001c0d5012401807428001d88403200c514503510307030b0f81624480b08040b030b00403c80c82c00c1503d4030404031415015840d016501d40408080070075800640100b00036042982e8115000140020a40c252240c0e005900d03c250803600008440806881d0b010710b25005078842140f5a0f180c01c801c500366501911030200591000c442d40e1071407442d1500030400c1d01d100d00415060b024540e91101c0a1381c201c648442d12603040382000e90240941402050b50090b10048100419130501d20a010118482140780b0601540c040c00140e10074020b41c850009000c403007080307230b45a191009018110364000c1c014000d0524 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 135886366 1250 135885116 135885133
    0x2306042307050112020c1f020a030b060c0c10050c06010e091c0e010e060405040c0c0213020f04030f03120e0309030d05040f050d150609050a1b0f0305060301060b030a020c 75
    0x400c01c54180d9405075103030310004001d440004080e41050812030755501807400c20008044240721144150540c0310703001b580b41c00c44d491000e0102ea83d41103040780100c4042090b141c0b440c40c0441c0c0700ca40c02e10201ea005080c0080301d5003c81c1c4a005150b11107544d40710f139400204210100301c071894070030544441110443d15112600900b00700d400c070381200c0072030150040040c1c20360050311211952280540054102079540780054184c0c2c003000c4040002c20084130060007541401103035501c00c0c1100e4030007985082000302c40262640715605c4094803141d551304800040500c00c2d0103102c414640e0700c200703011441503142d00301e81329403005207460310901c102c540c02401760b4003510603070301103481d040c0c4005240340c0345c8000d0104034a03120000300e41900c402026003407007415910406000c0c15400000152a2600500c04400c03901000b01c091050300d1002d00e0203408030703032003072044280c0001e900e0042550307100d82000c6805050315030080e20044030b001c020030a50003615030140c40710902e03040803182c0e0300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 135887616 1250 135886366 135886433
    0x50114100e010f0f12020d050106030b03120304110109030206031014040e070e1317070203010b0f030d030b2d030105060405013c033903230604 63
    0x1186040003030302051050340d0424006010f8030312842c11445078117188a0302030b4051042e034101e07882911f5500c0107580d510b0041c060359625210300118070305c041e0000c0000341810f41c52080d0038080100000c02800c0c0b540404c1c40143d02c10800e040c01164050030b900d440b400c09907091103c00340c00380100149242000d40f1124589054041d100004c0d0881d4094002d0b2400c02d4124140400300511108403e041505d0f007000241000107014400340070803043c1c0c0d8a4050a00c101340c25100100310721440ba803501e920b2030889560102c0c101080800500707000072070302500c0d004180540401170400392100300c20520354114044403c08081c40003002c900800195840104100c2128070030302445520f080000580c200404c5000b01c1010000c440004403184087c480d004074402d4811500100c0d42040c0e101c50700810760342e880c2081264081001c004418229800740440c25000207440302400d0f445c40006003400c980c107040807100c1015203040c00c1c0c85d6903203018280800b8200c41d284560b00315292110345076411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 135888866 1250 135887616 135887627
    0x1a090312311101210b060f070f0c0617060105030702010905030c01021201120807080a0c060c0509120105160e19090b090f0c0f071407080106080d030608070e0c0d05011410 75
    0x10041380c803c0c44019284008510002442a681c8040e004042008290900e40050010f002c825208118000a600d10303864001103d9229910243c20300c00134800b0b001c420514003801a50124081ca030041e200c0e0784408049015010220002d0210f01000031780c901300361410b40042c4234141c043c03041048280d03641c01c82c100f6103c1602c40c0141404005014110000310260000c1164050b070b450242c080d0850ba8a404089540c0000500c0100c0c5d0700162120903070400194243c43c90503400000c22861034034203813020210311142c21403070401c8420400034000c1d0785c0d542c212240c540d40c2c4420001030a9150780074840180a08080ea1348603440a2000900362210300c40014882c0e40703070500d202d04102c07001c00040041d1704440300442d8480300e03160783d0100301c0d401088590018100c15001007074561170300f0a880e0429840400800406060003001d200329140012004100c0c0c1d12400100002d075180c0702c40d29003038011481b00080c43e81c2400b000003010040000e00501500007190b072664540a140310942d02c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 135890116 1250 135888866 135888887
    0x10f3003140c100606030b06090f090621030408010e19080d02070f060914010b0609120106120503190807080402041e0e0a1a090312311101 61
    0x5056569981800003485003116203010846950114200740b01090500d00381800d20b0100c03035031603540c0d820400c207640d4940150004150103071005850210445e0100704800c40085006000b41252000308403242c442c40e4030302443d2014549010914074000c401d1580720740c854030403c400ba60030030250044207034020504014807800b0070786c040d00141c0d003980c81c40c4070342c1c1000307122034540c0c0d40c280310311804900301074602804244075880004070405140791904110002d42041039481e0b00d004001c00142e159102101c00c144401c82c0c00c0e8060010b26200320f03026000581246450311612078184041040c00409010702850942d90f52016004208080303540c3c84048401e074000810100114000d81031a5014020a2080140e055425040001c17001d040c0c1c0d400c560380d104c8582c00040302c1404c1c000c0103a80c050f00404580c0044940341040301c4140d549001b00d6901000f425451008159035508500c1c950091641132466521412182644000c0e07120700e6044c07d9030403140e940c030741c9421907104040c0260b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 135891366 1250 135890116 135890189
    0x2040507260103051c1704110907050901170712020702210604031707090b16080f040806060603090c120f120307030e161503060f030c050a090e06011a070209010f 71
    0x6c1d9411b01e0480c044540c0c6d0f6000d0000c0e51280f10301441004140ca50101440c0f140f03c01e43c481e08e0392540c0c0d0400051142c485640b44014443c044001c0c4182160b102d10701c2d42602c140c0300005a22000035000042c0410b220146e405400602c80e40c102102e441e0200380c0610650094980c4001c1c1115550300d415800d00c104d03903603000244040383c05d2008001c2000980f0207a940b03102002c8502d049980c408c0300d5070b8010160003c21200c00b00e0300304440303001007003007170ba1200301914030314103600742011829500c400c5034038218451511117510311a107400c10042c511501c0f079a20111036030030321485100f0016600507614140041c0c20070010171422840000e041000454107600f18801c145402c100d40d00340e0803140b200c2402c060301c0ea400003401101040503040594000c88420751341c14a00810032514440030703804140d01600704008002103040c089010380c1141e0301d46450b180d0f510354074480300c22a446800c00003036210541c0740012030307408000d075040026030301340a1030102600d0440501007001c012003030850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 135892616 1250 135891366 135891377
    0x80a0204030b06011b0c0b03090c0a0305030307031812030510050409050d050d0b0a170105010509130f08070f030908010606021603121803030807030b180402040507260103051c 77
    0x2604a5100d5603c1e030004042044220005d0206699496101301d83d941c070000c404800401840751110091080722540101114100300b035510315a5840c2c0c403800300605035400d0550300d00e48000b05800041c4031800681d8420210f00c2c03500140c140145c01003d040d9581c000d44049013502040d0342c00c042c8914105260814024128a43e011034200e0300780d4403200c00c1d0350070151154092034084d00c424020b00054409036003110440d6042401740c074211034050340000d10580341103041c8080ca82c0c3c00000410216004890724280600c1c40c1000c08140c0300e400c500800030b036240000c400605500c03030800f80942d9071040c02842840e0707480030103c0c0e59195148900900b14190f01d0200001030315800205116941410020070b00881c900a40c040403090394000d80100e0f118408004006130b05200b07220000e102240c002c1401c0d003407045040080d1200500090144c0d07561000301e2102802503485070f190351081c070303610001a4454182e900300d0140a1000700d0b05441164051000142c507454500e030030400c0707035858 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 135893866 1250 135892616 135892621
    0x9060f050919020402040f08060103050f151506040b070b060a170d0e0f0306072601031101030207020d1707030908010b06070b0c0403020a150e0307060206150105090a03050d080a0204030b 82
    0x341030b442c00580402ca0b0704c26820000025400f4404506c0c00c000c21070b0001510389503242d401c00703905100345054030411642200c00d10103a029031041043d40c00040c0e440340102c030b1392005008540288a03035081000c040e040400c01c40c0400271203013942032103400207450f05501c9a540303d894030744484030801c030705060b904a82002481c840c8a20182031448000a044081d0b444111001c48d040c00d00c15103440c00001e0f1110f00340040a811043d030740340c004a00c1d0711082e0441d8916110f60a2900d00781d14040e04042c1c0001d000000c0d5962011045e441981145031001e840d00070200310f00b91030744003d20803808500000750024070180306101d444001c903c040e00c01403515019590342d41d4074640040404010400c00d1001001585079111208042c004107030340550003058241000c1c1134180c440354072910990201509208155002c40e55030b030440030385071344102c210070b081006072201d008443c0c645030000c02c50b41c3e001050150000724103500000e16124650207880c1c054811080c2d12440c0805000701619001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 135895116 1250 135893866 135893893
    0x305010e150f04020d02071209050604181d10060605070f020609010c050f010b010815010c110a0302220b1c23060f0906010f08211c09060f0509 63
    0x12101d0480d8010034001515646600080c01c98102946180c20f10380c0c003140c104100801003190780040e03c02401c001001920b01000500c65120b24040c002e1003000141c0d400ea54413a503034000480d414034505411441c0c2403800c010035601da11201905581c203081280c000b034000d0040d07003115802c41c0c00c810500618411034003801030b668420f0000170304100310f0400100c04181e0a1069130050900e2000102303561000380c000400d0804040c3c0041c410031414902458145e8200c0200070155a220310000c40c14001e4000060309005e00340d00c060b412850000410080000c010354100e2060740494042140da8559400e2001c550444a40400040b200200c0b5001241c0311041c4c0d40f00305030605c807044c15051041c41d880c40c206542035450303440d1040303403900b4410217038028007005000d07195070310710707010014a060340540d590008000011814240821070078040c03480f5a085075803500f02d41395a081c100c10842000740c02410303c2c1c2c1c0181c0c0c40624200c1c95003259903590194a000300c0000e07005194503d820403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 135896366 1250 135895116 135895141
    0xc0a020409020105090306130b0a051302130b060a080906090a050325061a03070503010b0f012708071a09010e191e061e141b06010b07030f0305010e 65
    0x301c060f41401800e000a100956041000d1440b900700e017407204841048a00d00141c440d500640710741000b506000c20041c4000002891032001501142c841c08801002840300c002811181140340e040100041d10841840e0804109805140c0310000c455055650382c10181d11010506001001a04208035074410001d100d6124402d55031000c1d091074494240d0f41e92a02160205110000300c5140d00781d542c0220701d4180b0050340140320660007488140f501c1c10008100c445c0130b0701070b40e06002c2021a690b01c0c1c800c080e408540b5011044414101d078646900340141e1f104007900c203003541741c003800c0c00405e0040390381c20039103400340720607100c004513844a034040140c01d508403d07031080000000c0000050360340400f5a029456100b20100718a5182040c0b001807455004048810700d250003500120346003503024048420904000444c10789504000030a00090901070004510520880d0008200e00708488020204280b0944410380103100884080d07041da00b091086055110401d800583c64240d0381 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 135897616 1250 135896366 135896381
    0x1080a0b04090f030206070e1302070c0509090a02031b0d060c0302190503070e0f031009080c01020304050106260c0f19030501050105010e2b030c021008060a0603020c0a0204 76
    0x1a14003040490031440858200c40b0400c0c1c00791072514490140360141501881042e070003100c94034203501c40b40c0700030020480c0c0ca8100440e50414550029010091040158041c03001d45401041030405080c05100f495807503501e41c2090744213005489044001c0209003112810000c005050303085580d2461701c07080c004003000d0400d5400e15800304a140c0000d02d2483c0103820000c441c3e1074080d00da003003c190040034449020300c4540591420030242d400c1d6a0001058081d60001c0080400d0341c207030350b203048003042c01a140913140b558000b1062008008064214006031840000362502e2694201d01c6003c000c0e00c006c00100343d9802102035401c0900300400218075881d8080c154440d0b01107130603401944d40c22268419285a503444e00180180e40e400350516080300ea04076169a010240403482082545000142e607034618050304000e8101402403040c0c1d41c000750001c1440e0745501c180c40307028005c0c4600316945889050100c0c0e01240a500a05c05e9861000880740181040906076007400014200d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 135898866 1250 135897616 135897631
    0x5100e0721091e0302010b04020f040905040609080f0301060e0d0308070305040309150e09070905060a031e0e061503190212070b030c07030e0103020a08060409150c0507051612020108 80
    0x1152000c0300031070a1106000d0030f8601e0844480b849420606000742124400d0746110300c507038010012803480c50901c006039000e44800e1a030004160700d40303241c104020420460020b01c10328000c6040310150110740c0281d070485006441d0000d00e504214100004032042200090100e4105404901024400d81c00154024071a0900049280e22011500210030b0260505c0340007a000c1d06801c800c5041080000d9045400c60030100c03c03440c00c1c04002807650040702864000c040e0780300100d80c2c0500201d0404000b100d400398040107460509503019840381d03c1100c2c0035440144a0f8071407111800c0002d400260400d04100c500e0704c0c20307403640c20001680c640b00d1134220144240740c0c0205418540310001c500030440800015950f5086140140103200c00920703a605140c410701400c1d02d80c50300b1080d06540000100c0d00092040051f103004d1410800c2500440c0181d46060004c2803034603080001400404e000300110340d00c500c08140c080c00c48820038001d0800140004e12500015401400f02c0c0350005034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 135900116 1250 135898866 135898871
    0x30c0f031202130609050d0f031d040c030506040c1107180906020c0a0b0a021201060e0303190306060e0a080709020306030a050f03040f090506030a02010f02010b031005100e0721 78
    0x181e0300007900340c1c0c10800b81225100c110f040300708a91038001e8038140050000340c41300703007651103192500c44945042c05005024032507100810f012401030300d03810010f400b50003030040280d100b80c944020000c003411603c05000f2803404408030340142c000e000c07100100c180302004007403540c2072082c04412080c40c0c0310600011500c50303080600058040c00070300014000e0000400e41d0b1007481c00c051194000140040800390300c104500d2015800c0320340000d0556816050483c107850550340441d00c0c51050b42e01905030f504804801000b03196064019208070345441d6034041d110120a800c11003a4002c91058104aa0041004100700f00564000d503a100d2401026100c0c4076626480b0fa500340192485110000c2d000010306001e14440d004903c07000e410403950800c40392504002180e59236541d100080c4c14029861400300856100750020b0360b101801805032030700c3d4080d04811501070f18040d078006a07542000f903008111002d80050b087d1060226540301c40380403462000c0e5040030012811a884542d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 135901366 1250 135900116 135900137
    0xf010c05192a1e031502030703110f07030c15050a060509010501031e0f06080709140c07030c0b1b0a0504050f10050f072303070b0906090703320d0e0904030c0f03 71
    0x400f001e510b5101711a90440241c2c0d41d180950000303088980c881400c060b03001003808000301051501c410395003a41c0c2c0c1410040d8000342181402280011a5002441c00600b4441041688100798004004880c0242d503040c60341c1e62200d00660030344100100a40c1100d0041069142d8000541c0001c6110840d00f4070009455881e0180030b82030801540003800d41a450741508540c031a031860340c06502c0030a003401d141c240074440d500140780c14503080000d021075070b041011600010500001059100300b119071203648000061015084e50004d10440d03100300c0d520340740740585040c8110444007800355940c9040c544000d00c00206a1504840004d5840e100001c11036601c030140f42c2d440c100b69401420080d5103804103850941d25910000704207482e03c1e0801c0052204503c0d001030b107070003540c0c0e100c03400442c0c2c94190304200000715002d92540480c0c101c03c0d83c0c200401d00300400d5164070000c259958a0001c00c5d070000b401200c0c0d400b81c0300200040e440c0d08588011488030440d60012911900d0f1803030500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 135902616 1250 135901366 135901373
    0x150f07060908040807061d01050307120203070c150905060c030c120f0411030a02060a0f1701120302070e0c0a0f050909040605060a0602060f04020f010c05192a1e03 72
    0x107a0741c0c0d05044400b0140090300780040301e401c1118800508507481d181c60110f035100035186252101d10758803410300c90080080790303181c2e000d0540c20416540074a401c42d00da00d05003030004c0102c0b001c070341c1c140d900c9042d9040395191598213006071002c4c00d07003010003403415494003035511000340d00043c0043e50525040c0901840310a03001842401204091100304050420303061800035400c9504180d0310030f912003548440180c4840080d0b40c011000d070b046c00444c64081000542d02000c8030741040301c82244840002ca5001500c2c1e01c00c8025600076400c480005860304100c0c40b20010503913101c27810820900089000521940c2d09050344440342c9003403130429404038085501400299803c6400c01d44071010401a4100b4492107001402148010011420203001e6080f0090000d0000380c02002d0480b100a82640602148900c03d036201c411182141107540c03c4003045880341c94101d4801b405115209485413040c0e45000721181c0c1112022812880c08201d01800c03035400346000720160b0f0300000040407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 135903866 1250 135902616 135902621
    0xf150d08030901020301050405010b0a0905040b060408100606020d0504030309030803041a0f011401090f03020d0501150603050411150a231303050c0a06091707030b07050c0105060609150f0706 84
    0x10800c2c1c1001685a505050400050300e505804c0b01c1022a010f01110a0b000c0d4045101c0003140c1c030658002480703a00f000301203440391203240c01043c0c0d0f62044d46030140c0d6405d102c0d4494000c51b50141c0c02d484a05485100c11989482036200240000300304840034404140403030700440d0040d11941000e40060407a00d8840e00071942141e05000300d2a1000c010008400003c802d65a40c02091a00c4190725040c00014071148a840c000680124a408000000c00100750f00c1603d41c4041d1866600740f0359924640140034090841c0c00300c070704480c2c40c05c64103c28108488181140c400d222046401c004000c442120003600c11601d0381c406421414824640c0c0721004001d220484421130112402815401c10790314005440200c90300132520240100080e41d404005007080c3c1d140800110b8101c0005141940703080640c2e0005807800400c00188001260014010020215040021b11081c2c0c2e9500801c00140561786241e9080450b940c90102303e00c110708020b11095060301e800314201181038035075404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 135905116 1250 135903866 135903871
    0x504050603010611010b09181606050a0e060409181506050a031401090209070203041e06050307050a0203040506030106030e0c030c06090616150213090b0d0204050403360503060f150d0803 82
    0x2c21a203144a000c4802d02403083e1000c4202202c1c3c1940b0540c03810100600c07071700c3340050450800408800d510a696100001c45000b03154100c0c0500500148820400b501303400104201e13500031501d130701c0a02505060103001d003251300c01800302c0c088600d035440d030400d00b49c1404281c55041d581c80385c2d10309c0169182e01c205401001e4650085850f03500b00384247ea81c503070100134074188052180e0780803c80b069000c811030303070b100a0b649401510f58280c4601a032440c0516048640d00090220011904c00d9060340102d204080003411580e50544a07402d043c0c0782e1480855080d0000e404012050040c281200200940d5000c7d0444908005107510b41c0c07014400c2c0181e840c13207041c1d0006a404c058101c40d4149402400c00400c04100c001705041c0001c20f0b03512000002401240c880d40006c060502130442c600180b14403941c816264484500c1c01c011020305003003990b01c107000e4030101181604001403003030300c210344c219490040d41d11613006400142c507a2010180e4069444081500040c2c4c0c0c4102550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 135906366 1250 135905116 135905131
    0x90c0b030c13180b01080105150c0f06011e0e0f060f120105040b0702060105030607020c0405040816030327081605070512030c06011a12192a0504050603010611010b09 73
    0x501000c851460f0594003002c040c1c03410860120014080c43d07894404540328002c118084c141d0303540d0603000003400e091802c595189180a8039000090203402440003540540340d02c40a410002d8882100141c103200c00da031620492000e083c00580f0030304040d405c2d0380c07003900000d0400c140e4000d407030059400d4a00468045a013040d20340280b0a91903010802d031405840114054441894601e10096842d00c44010b060300c6580c40740c0118003800340c044100d4540c0329000307080c40c00300c20580c10040d000d070480784070003c803411103140039003e20001e070307a91507c40541c45200e603072410048071001d5440c4603403180d041d24140a5080005055680d90300c07030152104040010350345610007101700f103041a074164004014801e41c00b40b407000900302417080350046c3c01074401c101c0668035603c01c0302d0a403180307801040e2005d602d4040700c00c8102c0c410307200b02d40000402185c208a480703c8000c00711114011440340720b400090a01c01170140d1070140031480017114104000140c550f40901c00500e51800070303034004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 135907616 1250 135906366 135906389
    0x5030307050705150403120c02010309020d0b0906090715210204060801090b06180907020a0221100b1c052a041b0e040e0f0a14070603090c0b030c13 65
    0x411640c14580e421003403142c038561500382030921b5912840721b400310700c5071458204070102e014901168000d80c0980e0019030041d2240b80f11603e60b1a005010002c242d1301c0382113070311403480001c0103540c0006810042d55104145074600450404080e5018055010f2620a00076a0f8081304411213861015000504140d1354400403945869100811070f40c00c080e00601440d010018006100d01108a41c0764000c03054910f40d6040e41d0700780c4100c2c1442002c1400a6105028580c2c0012050011255402442c080c3d81500c4444003030800f11011220105505500f00041500100c1e2080e20040c86100301405907040d1160005000ca140949850b919640d5a072843e00c0c2405213110304191140c40d8101e2080c051216105002d01c00c09004c800454441074810380e1034030521981030310103000003601c1011103070488400c00c910f490300c0704603102407007070204191040000026940d071181c050180920b4020410030206410720300203a0f01e136480240756803076515003000b14401c4000344220f00380050181d109003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 135908866 1250 135907616 135907619
    0x1b070302100201050906150d210909060f030303200310031101030b0a05060313080f040806060a150509010e100305040302010507032306120303010915060309081b07050303070507 78
    0x10806000c0d0790755405801c580c503140800c80c45050001d0125000b6484040101c4003100070400112014010f45008150400c0c1d448090009640000800342c07401c1a501c41490490f15561084111444c80c0b0400d00310070750101040010a0195100030107082c900c0c04825242e680d81207008442e580181e92401c0080601d61040003407202c003003d81b256580091a0502181c03820b240000d8019030b41d0b02540d44100d40002c04280c070041d000b0a00d42c000755000305900d0315070f25500c24045058005208201250094000080301c0b45410300e1000107070b650b400c01400c04510951422a0340b03801003000d09042c004262440c1196a0300c1502d8200015010b58000c2040c0c0340c5441c0084c00e603900a410030062500705194840441c024001030f60580988601c180010750f610400600100120304950141d0300000002240c0c81c405500910305000a800d40c40b5030159907050114220f1300c041202030314602051110f003032014180300000380d101125408444205841e0300000381582c0c04038ad012191a400500c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 135910116 1250 135908866 135908869
    0x110604120f051006060206180102041d010302040c03020a0807050d1107140d0801080c09090709090506150315011e050a06020d0905030309060f031b070309050f0f010f050d021b070302 80
    0x414001003c659414004c0c645030107800307991150041c0c1450360344110249018078030343c2d0940c159001402c146003100c0e03500d0314654900121540c2800141d0003a820800c0c040c1159000b03000312140001c20b0760700d050190307660f01070803140d9411095040d812140c9442102c1c04d100c0f0424060031119002e603d40340001210200c001d8035020700b10078600c0078003851030010407070100d0202d1564280402554840407654400780b450382000000c1c0c0200c60190f240010703050a000c2d0002c0c485100c0c0300d000b450b4204105049040540d5281d6050780fa0111081302d50050000401992010501d0b505412913016180d8461001910580b0aa003110300103900280e80340e02115441510000149801c1d40690300d01807425000c22114410943c100025000000100d40300b00d5502c0e0300c1c00051181c9012454072403c65240c02050b0074030510820788141404210a00d90b03251003444140145030503110030400022591065440750001d0403c0c1e49030f40e82c24000030010000c520040d2503450b1302e000c09043d29500303510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 135911366 1250 135910116 135910123
    0x3020a031406060f2104060603030908030313080d0f0509010c020106050604150807020307060606020726060105120309042a05070b220f0b040209010902090d110604120f05 75
    0x4a40540c4180c040d007445010788400084900c034800c6800b04542c1d5020241d480181400410071117041300341c6400400090105560102c41500d2007542c552802070740c0c61000907601c2c0000c0c0d0764007044807070191540001420079801001e00030810000481e10b440041d042074101c503021a180c1e50717541d44449603200c0305642845003802410040301c50780d0615003018141e150b407413100c545100c140800c48000c540d94500030020390b401683d020905103e0310740c81c0c40f0029142c030f8080c82003941d03503085400d0800301041c4004040d1148121a4002c00302a0719100030032180200310300e8040100d01042006100039181c5004030107103a5460141511907a491102c010162210000140708001c02402900c00003a45070140640241c080c100a01c0c106031318218058141560010080203ca0040e6941c810440300a190600c5140200d074040e003d030ba03031111010140d1140085060703006030300e1071aa90020b08200e807400d550100c09000d41d8109030700c1c2c9001e00308181c2d0300c603000e89480c504048044200322040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 135912616 1250 135911366 135911381
    0x6040b011404090b04020603072a0b010506071e02062214010c050303180309040c02010c03150803070f0807060e0708010b0f0d1101021f06080c03010b060708030c0409050703020a03 79
    0x10b45007045072240300d07292206010300c0904001d10480002010030802c5100d90140c3c40c0d0410404c010310303004842c0400c90880112041070480d100661440006064684141074507080c0b030b00180c600d400020b03940b41840c0c204400c158101c0c1e0001050203500c00c03a01c190600219110380807029901014244920010742e02002c07102c0031b0421440805c103c0c00a0000310903650040103a030750200761132030f05805080c2540a50040306412a150510070741d840c1e0340c1500001d43d804180d1310200010b40c403a0b02103680030392840c0a00c2140758400c00c420400a24140750b4403401307034050302c01903007401050349c1d50b4410703a000b0701d0030313441298440001440004803e1040d050540403c83d0ba50810390b064501107400c809001001170030079400c6000302401c0d42d0081c004030142c0d00700600804889000c0da907a440042c03980c3d0045441d03620450480d24064141441111085100182058105000c59035980c0c943e6100a0200c450040705020002d141c0c5264050140988030320303240540c40b132850040040468005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 135913866 1250 135912616 135912619
    0xb040906080c03010207020609100c1a01061b080316020703060f0504022d0103050402040e0a05010507020f0703110607020a03140102091203090f04020315211c020c0409030c020306040b0114 83
    0x1003160368012381d1b401c000c0f02d101c924240c3c0e018045460508040d60340d664212006003564241704034000380b41c0c030b440a0b9141642e600d030719404681c60104070402d01802c3d81100042c070810081000c55080e50390ac0d24846401101c1d44101ea002e83d84030361342e0708140d40c400c15404541176118405c1c00f086140c19000c1d13690040c0b80c0005100341a010004410b600000c40300e855041c10742c0c4d03e003c1401d54990f0303048400c1e111440004c03a843d02c10701c2d1400a0003030100303c4011006010302001c1d1207000b200469403d00700c07600320101c848810700c070101f00210f0b0f80c0f2018080741e20080300403001001550460b00050048940800144c80c2c0104205200c1845005c6101c1400383e00300f007101d0740085e5203440700100c80074025038005031a5590300007611141741c400c906290348098042c000c8101071009000b403072014400c09046d102101c0000c20340c4807500400c90080e0015801c4007412840c1c604141d84881003c1d0b0007450a0801d01c051070300424100603040e1001c2e9a8110444012b10201c0707019007100288010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 135915116 1250 135913866 135913871
    0x1a0702071e06030c12050f0403090902182e020c010e0d020117060f030a050609100204210303061805040c050105190311040312020615090103020603040204150b040906080c0301 77
    0x144015540144207650180c2000c1c190b5490071485458441c007070032501243d98030380c100312505210052072102a401c440490001d4010b01011841004600a0750313581d1081d460300c80b48003a80c0070b0400040440c40c480c103a0240a9030050070001e5001c410352461410403a070050302005c0c008400051031a4038030840c0768050f00025860f540140d0707010314110030a52164415100c50b03240d0707400090b2001360400750180e15104080314002400008a03000d402001d410741121680d42a284841040c0d000f140701d12103242d03c285a801595036100314203010b41912a16000891030707104c005003c8081e2000d81c01040c520740d02c1d01007000300a80c02d6041d102412090801d0360903c224041c4c60400d401d66000060308140d140c81072000119003c50503203001c0d503032043d14070303000c680c403ca0002d656590464805284d07038255003004e01c481c14484003050503aa0094a007602e581d4076a02480301034812020714140c2da04501500182d00103000000d000034003d00800802d1061030025003928008540b6a00d0307100781d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 135916366 1250 135915116 135915149
    0x2060103151a03071508150f0909011503060518070e01060e0102030906030106020a1509020a15020a02040903020c041505030309010c08040b0703200d1205131a070207 73
    0x2182a040c1618640040d400418101c0050044104602004070300903003510070401d022846241110360000805a1546c410009955850070386c03601c0c224100d2416086000b950450b4250300305002000d6200800c0300000c0f07200407061603090101c25007940107880302a80c403003e02403a030080440e9040442c2200005000e06030505402c403100d03110600c2030340c040c0711b4540e40c400341c5a4020b00c10381d03483e028000c18641d1a980d54000103500e44400c1c150440745030700d5817010100d0001c02c501c525600c441d0050030081e13100d41080c1c00b1480f40f00e0080e174610250301c180b100c9440180c1c0c0e0b0f070142d021018882e038003400541e0a503006000c1640c1031188100100d080c141c4003805640c500006030b071003034036003481e0260541c2e4141c02c05c5002c42c490340c0c1040907084400a00700d401e040e005a140d981d0080361880c40220001c1400c041c548a9802d07501c0640001c0d0818000d04c1c180c02e2179003005811400281c3c00c0f50681c0c00564850030340300c2003100840c2da051050010402d0258042c020400103040ea42150706218 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 135917616 1250 135916366 135916373
    0x9100503041a190905030306010e03030f0d1d1b010810121b03080307021605060f032404020a031415031c030b0d03050d060b090d02090a0b030a080307020c0102060103 73
    0x1107800d142c0280e011048040042c2c40d075914061030b900700c004070403000c20498945080c0242c0305c0d13008a8802d808569050036011903410b000003180c00010916034003e04222881302041c000d00601688400d00c0c0c3c1403115500300003030b4140050020010005002080a1012800504006401004500d1074016003000304103402648203803042c1c0b1980080c110381d000c1ea0b1040704070010041d54102424843c004010803641076000103031500e941128143c043c084036a01c03c20485188070714144c00d0348048051003c1a1810101e9024241d15412100b043e28100076880100d4200d8001818500c0040c3d00d0740c4a1030491001c81040d1794007c5018010850f56030300c2000481da6032a650186503507011503020080702d80c1c0b0711036400900260310050011180190a081c001c0664110030414900640791060004503640800c044542c08070307001e2b0000c2000d500d65004c101c40d88600800c04a085a20381c2c2120400d070307130f0a0000c3e2000720700c9440c5c03142d200e04242c41c001340f81a425440d5035055510020060010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 135918866 1250 135917616 135917633
    0xe06012f0d05032701090506090609060108010903120e01110a030b040b030c030705130e06100501030c02070503100207050c040513050f010903122403142104090902010c0f080910050304 81
    0x103413940c0b10040c8104108040c2801030900b21006844c2e4042d55013804444480407074994040c07a8180b08481860340c03200e41e814200c0d0403c1c82d009006c5582ca00d02c000022a460300114080640d06000007000032040c0d80220740c0e5803107c00301c040045c0e598214030030035141610510104100540040c0402094680442e40c4c4821a004252052100804112010055801080b98441094140c1d001401d0041c01080e041c5030710b010311400300e8100b050301141035100007024400c0380c0005004140f88543c0080820081d44000c0702039460380144c0079200f03071507151385c0509401a580c980500c00e00074018145541800e9800d034540c0e9080e410504120b0100f5031096020509800181001403051480840c01c1f4420b00d85051021407517a1640000062116030545440c0c00c0701c02400391400d510302403003c021030310080481007110040512090060340500da005a0050b441810044100801c1c0d031146414107205000403546250006004a541d0820981244107481103080040c00c40c10030365142448d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 135920116 1250 135918866 135918901
    0x70302091212070624090603030e06070b010513020408030f0304020307060504030f0602030a2a08090c09042909010606030b060403020906040c021c02340e06012f0d0503 74
    0x1c1c2e8072485c584103840200400041106820300d12900090380d110146001f502c043e2105034046541e818403070701c180c1460301c1103888280e403000d510381d4142c0c240170820a50360503405d1000c8a940e401d10002c60803031b000b00300911120801e0308049403245040d104240c40c184164200b80b0410506000030800603140c02c800660701c03a840040540c6960f55600d0540c014240700b45110a00c001c8036a100b048040504601d0346441c03440d540d00d42c403075130b52174001503914403026040a1b00300031040002008101c06003020141c1402500e04410311882c16290000114000d0320b5009540c1d6480000b0001c15800d88070f03021b041d036001d440707039030420345560002075054100805031400340da243d421600c0b44500c00e000365103400710021781c1a190181c3d4480025030703c034201c03003c01c2030721000080740340010440300c00156003120161851349a40c1d41404001119204003030a02d9044c03200b090040340314105110591001c1f2880d0340c00c0200c184606054051400c03450040c1e0170300b480810428040d039840342c42270f00e94 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 135921366 1250 135920116 135920123
    0x31205031513050403080610050d0f0f060617011a03010b0d200405090105090f070c050a120c1101090b0a0c08040b04090e061f0510021507030209121207 67
    0x240c5980da20918080030504039018107500a4422040024608060744098080c074041d9883c80207558903035081c071003550070220100001c507200b80301c00000301c2e42030b800034001c11044007008100c00400e414041d003990010f4108101140540200d01300221686910703500400c9103110803426080c504400000e148018081d041e801000081c0425041007140c000c4590792600b003082c004409683c3e540346c1c1c080e8015000c0c040c81440c17200b00000e007500c2c1184d01c00d801505486091207094031001011744414203400d008a4650003081182c402041e003090800b4561a03150320340d85e030711700050b02e85082c1220342618054140a45002c05000341c0c2160825145030600d1400c00000041c05401d181c1142c1c02540c2c401c2040b0300340005c0c00325082d049a089104056051001c8882d10388543d90761654000045040801c103590707502d020070032480c2080c03084162a5890040d80d5100100e0480442c51100407110140441e40000f040a11401c08040c409480420400601b0040d40c405450405900c220580035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 135922616 1250 135921366 135921377
    0x70201020d03140114040e100e0f010b030d08040203150a0c1e08042306010b040f0f060e060a09090509010504050c030c010903120e060406090501081b09090403020f03070f0212070312 80
    0x640c0c6c442d6401691441451411610303c0d40921000348058004002440c03668010020a88142d81050041803444c6c40000c0c00fa180e45510031000300c0315501d00030300aa0b411700c07034a40b0803d00c1458034016140110001200841c44148100003d4100d000c03010301001080c80d244841405541e0000344e141e00709a01140da032903108588081150b24141a0b425102c450098100000b4400a500c004104a0322070090b002e24031030351032204071400400c40c03081d00e002c1001903a03560900e18045c0004c180c2c01c1d08904001060507220b103010400c03950100c40c160243e0399075005000a10004100009030a94124010f003419004840000c04001591000908001c401c10107428000d0080600c042c45074406002c141d261750741c5240c0100b8210551107a60b01184020000c1081000d0b115640c3c0d0400305081940340c134014015051041d032140040090302107001d00d0845d00b403120000c1c4002d14000e805a01c1da14030719031250040040044452003444120762089030104000303009600801000001814103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 135923866 1250 135922616 135922649
    0x406091d18010e010606050c16050a14060706090311121806030405010b0607050d0306150c0201050c0c09190b1206060d030e0603100806060d03021b04020408010207030203070201020d031401 83
    0xaa015003004103480c3c4a40d42821004140b0552184c0a4280548110100c60b940c003d0f019006074184a240550b60b00100b21950900c0320980c211000f5090000250041c0d00e06450f9403640000c4a040c45030890000303144080b205024001042801c6110f04450000b81ca09020000319040030840c00809600a800220000302408420f500140d0119000b800d40d40d030f5400d2610303050f5260420703006001d01007498810085000208180101c1151026498039000d22005030010350701500b0111140016215498001002d03823030b1070707502a0048000e01c03c04000c0c1c100384e030302000c00c1c0c414000b040ca02130035245410705500c03200003070b48580202040c1d40c841c2c1161f015040881da5a46294800b13038005500109002800b0030041d00c0c1400c8034080001da840d40c2c0c841108110090742051009001644229900e100000b042181c000305610300400c0145016502c0d055103081e80c1085000b500560004a0601c040d9601032005c60400c1c0300e0f40c134041084400c2000c140c19220010f01074241d507020680351 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 135925116 1250 135923866 135923911
    0x6061b0c04060303020d0f08090a0206030c0c10021e070c0e04170a0801050a05030a0b311208100b0327011d0c010f080610050913020406091d 62
    0x1a4034800c030141c0706014450700ea04000c1c4d5541031000c031190000b002050340701c440511a1140b40d0143d20341c4000780030540526000c200c015000030341083c0f040305007004120010300e000c1050803082c48603020056183c801461100d004004113070038510540408020644c00910b107642248150f444071070300c41d0a0342e201c6007400d1701014900d40070502d26003000284c4c1c200068101031114100d031400c0742c07c40e200603210010325440781d031802401030203805098003042160160310400b4000e21070400f02c00d22741c0d85811480c03410f10fa09014094403c034081169440301c607a03120303412641c0812990b9080c40000d1910140c1c64083c8001000d5118070b01d011079010140c0c5043d4001084170a008c00c00a0068544035007108000a41301000100a0f00c074000817104036501071110b45030160200c2e1118071040d42c4100c207100d95200e030303c015281000780c100260581c1d951510406500f200900c0c80041e01d940c1840c0018180e54615000300d0b04000a000002c0d207a10000350400707074401c0100000012000b96241d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135926366 1250 135925116 135925123
    0x204080a1704030b04061a01090312030506010212040b04030b010f080d030e010204050904050d0806040507051813091401050106020c22150b2203030206061c200f030606061b 76
    0x4000400030420304c010f000c244080f9411071020342008400b40f5411070329003c0155821002c51200030301c41110700080480090082e4005948500c0c10300596528141e80f880c1400307958003a4101c0a0034800105040c000e00010200b43c2d40904641c600c0102d1840c140416190b03190381c8040344404150715401c01c0c000c002801c5d0141d400a003c00307080100d080c2090302d00662643c25078184200050545000111076207024000c041c0980d0054440c3d5141c00301030440440c9455004513440e400c000d52070303a09902d8001c00c1c45005002405021210080300100c04c90301d080d40c41c10b80c232400455010b250301c8110303562010845003c844e100c02c0310324002c4142c414840098103058408452044034040d0000da4065010001d10441c0c07041c0c580d164040f4858018040340b03244a00010b40140d0160002031180e00b8034814244078605104007900b2701007000e40d00c480148920301e661054424003c403100c59075007040564241c480b4030480c007402140c508800400c8860003100001168a0445148440c81549c20b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 135927616 1250 135926366 135926369
    0x50f0d06080307150c030c200703081909080c031c110a0605070e120303060607030c050307110f2d0112060312140301030503070204021b160f08010204080a1704 70
    0x1d2007035940b210401e080a00f0001c903c0304c0c209000ca824100001c40003446442265007180e400e80310b000300925070050b01a03c06203050101d0340148035608006c4040351440b0f02400e8900d00c030840c03880e134000324000c0c02840000700e6840540741f076001c80c43c28041540d02160340c80001e04010150b10300880a610200daa1410300d100d0000b25005003051275003485400d402c06032141301c494881c00140c0d02d060081c04441000c41c01d0115840d003081c4003151300361400c0c0c0010545203000345800222102d075510354a0865005900440c2c1032810300309401028100000c0310005c442c0101c800b410a510a501507117010000c040208502011706c81c2e02c0e14061780645000c6591141c030503070400034152a07242204003100c1c42041c1e0000f0030510194101d41c0380c607807021a070689910030080c42c241076075a070070301010f03404c00580700000d081d81c0c802d40c00203400104000b003440481075902c0d03500c240c0307040c600501100c455009a01e669004100a1240c900001510f001507580b00d000c503408011045221501806075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 135928866 1250 135927616 135927629
    0x61a0a02060606033105010b030a031d062206031103040b0f0c040f090b030f010209030709150e0c09041512140313060804032d0804060e030a050c0c090601050f0d06 72
    0x2010030214203000c00c070303070812440c0311b840204101905601099600c10420310000d0028200000c01400102080060740500201405440c00c14085030070102243c00204400d180355403420070200304607903040c011303080d40e48804a1883d00c1c608082c2c948000409005100101192410b0042361310055001c1c22a40103181c0b800e880d04e0320a883e00c1806014007000d0280e18883d1046459040321400306108a5800c00401401007118030701c0c101000e03020700412031103061004d50f02440000c140d144100250320988003104501d07501c040b15800c10049510301401350000700941d420910803e40b000340025a5590407131703090380d150480030004500e10b1140703505030507421700d01c56400265aa08161141d02443c8282c80c0c0401e2194012407040b1102441807252410044402c00900058024140315030440c2c000c210200f05608007620300d81c42c55010303002d6030000410002e188181400c050002c2e40c1407140480302c1c4035190a103507000130614003c0c41906002520001070600203c4c800d43c0c0000001c021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 135930116 1250 135928866 135928921
    0x501120b0a09051e01080c0121061802030108060a0b06030a02071e0c0f0b0f0d0f0b031606110a0503090f03030706060605031006030b0a1502011509061a0a0206060603 73
    0xa0030b0200c000346850b201114480301320341500118000c8000301d1580c03000c510687d10440300c04148207240c111441c0078541c62248560700d00000c105e4821780c0c103038040604100d00c009603503545460131407440d061004001003051840c120703c121003607941c10308590b0030040c203c801507110020350410460040400580c9900140750230000402c001c2d281c8001e50441c0c03194207441c40700c1a55203c01c4046840352041d44516040d0810181000103240e83c407a43d16140c2d0710200103507901400020a1401c1000700d262500000c045070104021580403200624034404000580f44888881e5645030f601c0c0100b40c1c1d200c1c030036a60b2960a03041c5032070030406d03100043e811410910200742c0c2d540c0042d056a001f901c2440c0004100e03580400c1446c0a4010056030300005012240c0661408805c6c0c10b860000804003401c554071030310311106200944034083e01502ca42e4400107111440c110986d10030940201f024402c154050180d40d50700d90300419400e9101c6819600241d80790380700c021030106080099098400c104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 135931366 1250 135930116 135930121
    0x309240b06221a0729040303060801061409130f0b0a0203060906010305041e02040204270e010506011704050309100e01030c0305090a02010507050705031c090b03010501120b0a0905 79
    0x40082d40c0d01d141108211031101d0503074030b8901c441c801040c40805094410070400c03c040c0010007070070b40203c082070300781207590a04000120640d4002820755081c1e001175103440040c4441c0e60288a600020140c40f840040c0003d800e2020601d15031004001d0407448540f640880240050f082d034208138164017035058103551520000301c0000350000e0390100d0045400780f0008405500900c0364074012500000c0c40c51601c1d00e2030394207541d030502c1c16070101d030810f03000d2000040c6071007401174010464003c0110140c1c0c2201c0700c40343d42c0c120b80c1d1b01030361034400741c0c1000284101e03179070010141280d10100c01082c006c103503600c0c10803d01c1c502c1820006074025801156842c0d8050707001420302a41d51003640e0500c00041d045a04070240c8030b0603205440306410410181c00150b01400041c07078060b1080060b200000da5600009090840024000307041c844131004202c00540d10600140240c11139509845c119410100000e042d0f007210070b0007090307240da9101d01100da541c0d50301a00c00244800b54043c0030320b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 135932616 1250 135931366 135931387
    0xb03010e16090501051c0b0702010e03030114010809150705070f02030d170a0e101503060501030308090d0f080415180819020102191808030403030c030e010309240b06 73
    0x4032442c8180c1a2007454040041580c2c0350030784c682c1e4200e008900c1c2d0400c0801a9890b8100305100150000d01907658500e00030720b00340c8060014600070280c4400b070102c104c44050024045e01c0c0000d1040c12281c00044e01e000c003950460a40c1d541040b0300d458296100c0b0710f540f805d05540380202d40040c0d414400e81d05504c3c141c0b54407511904070300c4c0b4500c0c003198003502c030a401442510984c070902d030040e400801c2c041e140c1d44001d81c03080801e111288030b451035403179481e100e94048840070303042070380018000d1080025842080110505602851030060383c0d2000c030010041c51900d028000800c0080000d125803807226041d041205000c020032052f0202498070b1030001000c2d4070498004516000030300045407054018400d441030207440065000f0741c140002d80803904091068801030340c541d04c3e204c001c0740c0d1403020030103003002c1d43c0300b0b4541c22040707912810058846030081e0b038461304041c02c1c81540e00000d1454a2080b1200324600348061103004010138140241040c850301c503800900c0030802c0c2216 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 135933866 1250 135932616 135932653
    0x30c01150501030605010f0c02060904020f030f0708090601120320031602041a060d020c01091205090307051c14010e16170d1b051911030607110d030b03010e 69
    0x3140c4090703d08100e1386a40b0001543c040d20506940400300e1203408602c409070034884010400d03030b800180014500341001503107402c01e801c29142c2c0000400504102b01900b0781103084290001c0b0618000c000a43c03510f00301014110141c5130003001c2210740a0303905084030452034200e0141401070152511030580c12408005668020001c0e48100e0030080c0400401d40b02c5c04110344003000250000740b400d0ba218154501075440b40303030488503a640e00d00b0080d001c94091508807400a625030340351661450408101440d000700c503040300340b20707030322400083d02c083d1440e100460280341c3c4000f0080a82d200320780b80390300420340b60351010500c1c0039900c41e01c0081b041800001068440700040d09142c8001900c0903513941c030941e41c00f5000300d40d10f000d004030002041c60040000380d2040d02218014460321a909140190801084840380d000104150292034140030203544a030721840c181c85000a1144c009644034000e0020313000781a510030b600d00f030a480a40003405682c50302000c542c0d0355040c0710050b401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 135935116 1250 135933866 135933869
    0x50d0e0a15060602070504051305030703180b0f04270507050405010305100e13050a020307060302030609060103050403120f090804060c1202030c030a03020a0c020405010e1b0327030c0115 82
    0x4035040400100d0720500c01c58841d050a6614544c01170402c981008103001c02464080d0035010075000c021640c0300090400c1008010f07203480303651641d08050121138042c0300d40101e908000c414410520070184e00b42102001d0f20221081c407030482c011000d1020302c981d0100b502410910985044c002000340b841e0308240200111002070383e081041da6580c18911004103c6070091519046403400869860407a00c01a5801b16000d101a00c104090f194002442c3c100301c0e5201c040400d40100c00c100003413810040c3c85a02600c2801c090103a89000d0f80c0040071200f103d00561401640d03010b07036000307090155000b6041e0707030f0f0f00c0482c05035565181e04002e40f500601c0b0404850120000c507825800d9803000c4103903031b06604494029410140780c1d034000e8001c0d4000b41d690400304041c000040c40984d950b80600c9008155400b04800d950400d0101c4010000061172402540d90040041c03144012111892048800c0841c800c42c5900c01144903103800c0d803281c100f04610a608050f00e022005440310000d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 135936366 1250 135935116 135935123
    0x51e10050f0103090507050607020a090212070e030c100302030a1806020c07050a1d041401090c050a0b071115070b04060e1b010c0b06031009030c05010c0516030f050d0e0a 75
    0x6440c1d00e910401107054400b80700000b4141c0d00903540400107810030f0b0025004291008101c84440c5480c4c4594030101c0e080048000313200c0e0011028010503d8001d020101d14010a401400c0d0342c0840030046240641d40030400c404065001000401010044c0d00241c2c5852202138010100e400500700400a9007140d803442056004a00d00020303d0319002c0003140c11500c1e03010f0b4042d0724140240c09100c5410004200780c8211100f98130884c4d90060a2081a1010344180d4404000e03d04050500000c4581608002076a00c401c00ac0c7c0c801180440041c13011008040300c0e030801c10710443c0d5111038039004400005002034034103070a110411409410940050350380380c0403900403118000914000c03100811410f80401d108401080101d448600020b600c444042c040310208081c0c810340800302d4507100e406070300081c11a2000d41c02c1200a00403604618014980741e401c0c101961044140384c0000b04009080c000e00c504001c40f6580903505403070107034103100010003505203030020054071140b07800c3c4102c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 135937616 1250 135936366 135936379
    0x1e060204230a0f12120507060608060f090c01020705040902030a0b0f0a1a010c02210f03070b010504110406080405010605040f020c0114101203140408070608011203050904051e1005 79
    0x1c6400030300042c9800c11981805002440b505454550814010b14228003d040100810081f40881c4060149d8002881c2c040f0080410f85000540c024401c04040d103415800c0d0010b02c1185a244c0c0d000840030140c7c1e0040318002078054031440041c0c03070403034a403100800070b50010701085001d10f054000c5a01c900c0308100180181a80e0071a80c4030001003840c50640071462503148480541400c01120305020001100d0441200701d039000640340101c0e140200a042d88001580b008101d020141c61b401040280e0f000c1c440d28403060203069050082e0f0060104012401e4005801d004094010000404010b002002401402c400141c040d40c01010404902d60070304280d42d00084a00c1c90651040003405400654a41000040491084030500076020400745010801c403040d04000140000c1c0200401482e5907450088007904804050740191440d608a81c6940301080d00681140c100e10b03003c03a400511235032900c03a040461b045181c0405120841d007030401c68001c84c03059200b01501c0003195030707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 135938866 1250 135937616 135937619
    0x90708071205030426011b09080a0b1605040f0b130509040b040b06121203010801063c031a04110d020607080d0b03030c0703030f03091e060204230a 65
    0x18164109060700a0490340108030810100c03607007003d10820140440181019600044406400e452800701c0d01800d4100c20000c0010441c1c02641c2e1400801c9080c0252a02d6002e07515105c5251a0052850307089001042000c443d092142007100c8c003030032102400282d07254464607000415048905c03080005441044041030b68078250720113a1041e43d003c80300000560743c07695440210301700035000c2600500010b0509010400902c9054941030f801c8007401c0d101e44c903007440c0383d09580896100a6040d0301c0140d0340012900e0004030400c0b801898501503d030744560000310301c04070026030b00141447c6017243c003122034004028031190040f030044100d039051198000070031025030840207009520080c10440c2340006008a0041c1036080058000014080101000302e4150380c0070b040602016040280c0a00030181c10200c801400c10340c0c1d2904101c025402d94483c03107481380700a05102030b10b90102c410010480b1640480d07014005852480b200d100c1440d00d418000300381e0040880c8500d210140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 135940116 1250 135938866 135938879
    0x12030703151205010c1407030c050c06070809240f090307050d06050a0c111e12070f03031b0503070e150a0f0806030a03140703050c011401140a14010e0406090509070807 74
    0x411b0507804000c0c40b030301031038841d903650150707880c00010f00200d84034050600400816692203018080c420b0180c4001940e841070801005041e080c0e030160aa01503c81c00130800009240c1410381c2c8140c508111265074801104000a19240403036001c070b60701c140304c01c00d80c00401259801c0035001307030b94500b0180503c100d00d00054030982001540b80550f1350010034101001c00010402c00d1580c3d0580c8140d40102d411801034440c181d2201e5000d0b5529000e07034403103204050b45446160348898807441d160b20082c0100d200145940f00c054083e10030441c03604000981c599444e0b15403035100b03e442480d569180e100b840040c0c0584641d080400205032480300103000c030709010400d24001d661690301c6078002c030505511343c80d6a401c0400142e08002c828803041642c44800d1080c602c48490641d0340c50700300c1d854003062824031551592540c1c002c0f451030324100001987c00580c050308c0403003400c3ca201e415103a40e011500420f0558440304041c0d040c281070010794100401ca880c00e5810b40c805a030312450300d03680b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 135941366 1250 135940116 135940127
    0x10b01030e0303070f030e011802010f030207021804020102010209031005060a080304050d03140c01060605070605150901030201030b0102030702191d1b0703030e06090c010305010503070812030703151205010c 91
    0x314002082c0c1080000032030091058891005a240328100040c3c1c825400c100142161285692642c424001c07010050940d03030801840304241d806031070154a0420942d010403200000140307000c9504031141c0200d02168000e405644001201404583d6030584d01c5c41410050403081d2155400750304421030100c2d2a1102008a41c02da0b10080c2c003a4400700413a540407a0303031510107858020300b250140700c0804003010a0007890010110740d900c20352a1546801c00350f0886070003400202400030300e0703900c07209143c0740d5a071102e045940900f0b00007284146040180e00354442c03490000e42c0901c0c10040824082030f0506141c01b507901c01c1340c40c1034600560b11030741c9440d168150382c46020500551894400f500c03c100080404600c02d24011036910a102c4907180303800019a041c015940002d1160401c07075034107100b039a006100480040901c18074041c507164035414807204002e910000080001c6019000307402221200c044404108116907a402c0c1d1101d000c1204501103ca40d4204403820210301d1041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 135942616 1250 135941366 135941381
    0x3070203190c05130c0e010c11040f020d0f060e010e0408041a0403080c1f0204050a140a0e07020708010e010209220905030c010b0103110304080304021c0b1305010b0103 74
    0x280c014980031035441e08240151003004021907060031402c001003041d441e0a81c21280b0503d611001107185000d8000c0a4003045210007107a041107664244007010800f000510300f60f01e0b2007603a0001e0405c130b43c07024001c064030499010710f01d640c1c02c0c03c3c103c4142d803150342d100000b2142c140000d8010381e601d80303c0004c00c0c02d60035140030b000510b050005003e1202c42288081b80203509240072807902d40e880c0d4810740b06030000c048003e0290002d000c204240c00c46a1104004450f500d501146054142130000710340c1819401103003a05054400f01c1d040c03e4861381c2014010b001c2440c00f100c0e1501d04410700954444050040f0031465082064208112105000f42c2d8041d8074004c3c4a400e448018540314590b04414041840344151541c401c0360108405000030300e0440e81c10b82c004121755080304005001d40b82ca5041c5101c04410410400002c10000001c1e00e030865070446840c50200340028200070705811201010f000c124038201030000c0c0088054410704800e21441c024091030072840019000c07100d14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 135943866 1250 135942616 135942619
    0x5010e01051b030703180303091a07021b191203200a0609020f0a0e0702070b03010f050d02030a17072a0b030a0e160e0f1b0913091a0603030702 63
    0xb481e03122881800303120083c40d403151907441d00062400d00d00381e02d0a004805010300741c01080d0f941702d1400c140704800180320004104c5410f1280d0034104010029600d0a084580d00e0b004404070f05078024943c0e50803042c40c0310140032a80040c07002e0b100c12190b030000403003030700842c00309100c9007152891010111424031549804809090726039407585542020788042102240d0144020300301800990f1114a214090b12001804009030300e0010006403a14203070b6003018211050a1004004a80c008000f40d41903600a8905440b1800244082460b1166800f001010707400e0001d482200d1603203040141c120380c0c0c02010317950507020005c400020508107848900b4526011503005210040d000341c020764129000100008807404584880c60500c040024600c248203140b24042128542d03001d002134002c1060540c1ca0172030700b003c0201c028140e4400a60001c030708e0010a00e03500d41d44c0c0e02e030480b11100308060005c1c03282609528102d0101d0403802403d451030b00386c04010450a0500000b51000b80c0e1b030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 135945116 1250 135943866 135943891
    0x7060804240f05040c061b082502030a05030a020c010c030507060b19030b06090a0b09070c05071502030a021b03030a120b1c050d0c0807030c050c0a0f0305010e0105 72
    0x58025581840003005107100308259107a0080310800425440742901c84e9002d40c1c0c8200307200e820140e00a085012416014910010440c40100420405001c690b115070340301c1c400d09030246105840d06210004000003079814020031807190709100000c00180408501903094407080d2a800b0010765190205400250020310140312580020f4140e9011a81928004021034640180804007414034070032908201d610042807001c0c03108a080c00f01681e030b041110860203018191529000c2082040024400c404111070002400103100c400c1c011400901a002d002c0d4607080401880a03641e540303d48520001441a002440600e45031440042004513000300a10b2618081c0f02d021640f100100c8400341c500780c0e4840c90040030380d503160180c102452024044c08481449410424102045040b00307405004520348207000160300ca500322a800c5500d0f0074404000d008600701103140001c040045a001220f0030b00114901001e03101910489209038000c1c0441903a1850031030a8580640e0f06003814107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 135946366 1250 135945116 135945143
    0x503031e010e01092d0b040f200f09060304110306130510020a02010212041211190201030203150d0321020c07090e19080301050a0b070209160e130e07060804 69
    0x10f69030088140c1000078040060503a044e52005000150700c0e0b0280130b60340340c1d100d181e06c160f0b0a1034020001c1803103507903608010f0008084082d104078250040410181180000c10344842d01541064402ca0341c00034000315181c1c50301b4542065000581284a48a4070072140040c0200d103074100d56044c5242c1c070034080c0c000300c0800b0142030041d402101064040d55001c0c80340e02036041c1c08424a510030340c01041980c041d040400740152245d41071420840342600929036070750b211520200b06201142c2d080c0b80050703595841741102070225240c0580f46d94013003407400444040c185d101c41070345881420345032a12044480c402c20f1404900c11045088a42c1c2c100c00380410402400f58421061810303d1400d80d0030140302c6042c05003d00451100407940b018010006201c9414454083c002a100c4403050318a003400940004a620b88004c10341d0400e1207a01d190201c034640b00e600c0081200c1d80c050500408214860f18520151486502d604880d200d024800030b11603102d541100d00941e0010301b14035402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 135947616 1250 135946366 135946379
    0x2030a030813020607150b03120f03040f050303100305330717010605070507150c0b04140d05070b0708040c030602070317070e0f030102090a1403190503031e010e01 72
    0x459008180111004015008001584900c001491500e22032201e00c0c0340307004800030703a4007207d1a40c12514020750280f082c0e0800014460125442c01d101e110f003041c2c0380da8651404ac03603c2000b403100248a40800300501c21a81e500c8001301c01960b100b602510744511520040c2520f0505064102e400907080703000003038030a10701492071a0810a1464615082507002c082c8008208080e400040001c1e030001c1c2c4141071080a201034030141a41d0081118050214000140408803500340580a0801c10021070100207502403c1552210381c5001c0d500750003580c12018042c1d422044099446500c018000742ca500d12071003196104560180c02e41c02564155140c010081d080030070308a003444214006070020a25516900e0701c10920340ea10091395070078050a0250b0142500440360103a170040c0001c0708960780755080503041d550039019591794a02c0b480000783c0340c1211041d0000110702561001011b0040c01310040d8070401140381e0004a00d020281c6d2000030403000d1040d0480d4544030710060200703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 135948866 1250 135947616 135947627
    0x10c02060106230306130c02150f01030309051017130212061608150306040c06122a0302040e0f061801030b04060207050a0b0a150e0405030702010c030504120c03020f090402030a03 79
    0x11014003942c070000c81b601c800900b205c904580510250740080120004040c180303000c55880050400c40259039450369074007500121442c06076a126404528080e000540305810400280030081c03122841428150b03030302c040d6601000b030180d000f020a50340d0304c1c20080c0700244842c084c0642c4120141e0700704c0707001d00442d41c40002401810b034281000d5022600d03590100405402140101000036070140f8040380640000390400e540d40d400d07070600c54541002c4920001c0d0705000038640980e0b00104042c1d8034200c0080c8150380000b12035000300001d00186000601900e442850140c480b10302845045004203624a07007448010403d2510030700180000b203994000d00300940c40307542140c03810f1215940780c00102208544140ca0b49544402c0324203948000c0420100500210706d9000c441c0c1425100d1540364402d2035406030601070080030031420184134100f140c00401810180d010040340c0d61034405c0c410011440141d1045044074901561450170b154641c2c0650750040050114100c0e03554183c46 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 135950116 1250 135948866 135948871
    0x11190f0201050705030c0106330513080601080c1c0f11060702061809070e031e07080304090606090f0e1501031803050706110406120b13020408010c020601062303 71
    0x4200b42072000303000007203003080039000084030381002003902c90030034107039011080500c50403180358042244a1445000a11040c04050449290641d91400480725480156000741d100c8071a6108003000010102000b1601080c1c881e8211076908030010408400e000c00f603140c41c0d010b00840340c019600c0001a082510700207036030341c005c3d0140741416402e400003080342d009611045001040c40070740c50b41070710f400c0b43c5003a80300b155400c103802100700c80c201280c2d440c65007003941c0e01c0d20741420b01182c041c1c40081080300001c15050781100d5549072111018406822540b05520100d1b204040c04108410300c904248241c6200d5901034582c0c0d07451a506445800f40724500a051540d00c0491202c80744400041c441c00320f0082d1251a0744074118500343c002c44840b07584600304000244800d00c100c1d40d01666400858070b800102103099154800003030881542c00052400845c800500020401c006420003030303c503202a0207407807050382e0f540c00035034061000501217260441c40394140e141c800b048901a64 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 135951366 1250 135950116 135950119
    0x5160c0506150324040b06030318010e060c011e0c080705030c070606030503030709030c090207030203030c22030f031d0f0415050402040306150617070f02030909010b0301050111190f02 81
    0x2540311516001c0c00c402d0440e651440d001d081300140410052010070b0522603040801940110310f002c0c1e01d40840c080d07d000440d0b0f2103040146e1140700e010165100380a4540301c1d0a1500200407200204034180c0015125400c0c040049050010032401940504001482807910ba20b0baa451907907106684101a8024602201c070b0540d01c000c04800306804001840c81942a0340740c1c0603010b4154200035032921285c0c0d0049080d24010411180080e601206807500b00308400d140e562030382c10304402d0304541c8030381d554901c00301c09000e900042400740000d4400007490080c1c030741582e4503103014002006450300d100e9558116103c00034084c03442c201075000c1a041c86c4482c0340405100d0300ca0000809a0b07200f60720a41c2c840b510340d003034860700e6066411110000c20140c240251080034003000d040490700f00400a0083c429180000f0118600900460380d142d0707401031002000d0342e11040181c400e90030038000c00d030004030540006110103100181e0f42c1c03005246204020003581c2c41d41c1c1c0310081c860b80c0f080300b01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 135952616 1250 135951366 135951373
    0x2010905100501051206090c01081023010e03010e070506030a0608010f0603050c030a03120f09021018060f080c0d02040807030b0a0b0405010b1902030f0d05160c05061503 75
    0x1580421400e2210045074062800c001c0342039450a410414104110a601c00c2c0c030350800d00a028202c400001c1c0180c40d02001c0c00d000074556514241d000012406a10007094410314800014041816010041d86030301c09888903480e003084002414201d4044122102c4030b0352104400f030141e0b01d000009140c0c0140010b001084c0140c881c412142500c41504100540540712441401000014800c104001109500402107542661401002107030b041c5491104260740d04102459020b80307030415165035030003410004501c602100c0003080c1d941842d407409151656a6408a1403600c41e41c546040b000242e618407085c0c3e22103111130f00265102a068950850b820031002904a5003407001c10021402464409001e00d03007004441e0983e11009992881249400014014085400207880000c5108403003550068000724040e85907100359407025114600101e80140b51190320342200d40314000408000c40c18903010340003503e60440c400c000403c5500410001303400002c0f80213a031748146500030101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 135953866 1250 135952616 135952631
    0xf03122106030b060405010b1615180b0405010f020f0d0203090703020d0507030b06030a021318020405090c0f06070b18070b0d0c1b0b011e030203030a030e0d03050108060f04030201 79
    0x259080718001c0d88100e4400d0030000c10041c10740b500388a101d005140b81c0030500c0c6801c07004404141500b415000c002c00c03e1040198140e21540d86900c2502c2d030299020f03a90308917191500b001041104212412a419030030b1441030080b45007c1e00175151104030300c51b001820681a109800041d410040c21601684901c40d4000050707034403c9050b02d040c9004102501c940d60071410b04100b4610f00600f07550003603110000c4e8500507214041412501090301d4800103500722020900c130204110343c603019602604180a01045000c00706540205100807908a9003050602c3c0901c9103034040c3c65405070100031020001840340d14522041c120040c5000c0a5034400d81e2500000505500104030b500c0c0c01c550b54858410419400515110610100b41c40100d6096025503507802c043c541401580c1c055042048a520302ca85c0507407025000c0c5900038180c1c0e44075803d40c48028010b181c003c0048405114200700c10010a00920441e81600d445002420043d6640700811402c02e1015008401315966442d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 135955116 1250 135953866 135953927
    0x92102120f070804060503090f0d020c0108090c2101060519051005070f0503070b0f06150a0504080703110a1e0b1e120105010807020106061205060105120c090103060f0312 75
    0x304003030705c01030b00c0d11900d034144544041c0c0741c040440010300a135030004074000101c540000d40100c040c3e03000d00e401910f076602c1800d500d040140040c182604603481c0d4207410900707039184074040d4480241d00020420282d84200700901c001e2401400741c0604468030060040b42004107400700007403580c5c2000d501d40401c40c2e8900c0d03c00c2690181c2554075400108401d0204200300c40050f030829502e40e0b03011901e00700807002581301e04100089401e0300400040348001c1c80e004030207850017010384405039456141e680c10b00c20305002005800d680b007408866808200040c90703200e40d1460780301e00c2e49446c6d443d500701031942c5040e90019a00d51075036200a401c9103030403411000102400d802035103800d8400d51408002420150f005411242903905081051001c130b0f9000c01142c80403155004082400d0701c415005990612503000d500741c0028088080142c1c070402d460041640a40aa07001c2182075990032100383c4125140c003008106a040d41c1050419078840e0111b02c200529a43c584c4450000f4003c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 135956366 1250 135955116 135955133
    0x3021228050715031a0d0213050402010e130e0d0201061d090c040207141c0219020a081204082a061c0e07030201030e0703050c090a020715092102120f07 67
    0x203880740041d85500c5c50001500710040b010041c080300fa40c401000028540c00205c10740100304150385440c4e81c030302c002015a88181c658442210000e801f50084a60140b1900050101c5542030f0400e8400d0044c040b142c0c80c0f0500c126021182c10545c518074158242100001b410f030040c0c012560b030300c01c0105252296540d8802854800e00c2070b02c0307002d110307280a00c1c514100322603005044807040d10b0902040d40e180e00810318015058440c0403025145030a4400101e00da00f10b50030441c060b101d190112405e00c001c42000b0800d44600500b200c6101d1403c0401c01112a8501c0710700761340c0031010000101ca414000064000e94200300d01313400321240842c0341c110403119503003410f000300c3d03000350300c10400e40d6094851925414900c4019003005411619010307030707a0320708200050140b0b101e10300190b01501e407681501c000c1030b8080d07104086d02d0407070340402002d4180c06034261520000d0441c100502419136240c542881c4407038000d040503146c8200a100c1607005211424a8101c00b040380600186904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 135957616 1250 135956366 135956399
    0xc06071401020d0b091609120201031112010608091c11030c010c050901030b06030c03070c021c0c0e090a03081515030901020711060c0a060b010c050610030212280507 73
    0x10800941a0484c07010801c1c3c490020744010481144400d40205566200030505c041d0f469030016111380c07070000c0c80101c00401c40002c008088000128403c21a144100f0000d8101d901c103941d0030340c05071280d80e503035500c1c4c0740005262009215543c00043c81d860003410542190300c100e009490809000a040c1c501791003881266a0004200242203101c0391380511071140307101c8003070750030504500e001c6079070b51614030000c3c01881c140007800c442001150303602c02441c00f901c0078516040642d44910300c2d121241c2006400340b1081d40c516900040d911040000f030f1880c4403070b01a9140b89052f01ea000c1d091520041d040852600b14204500c5941051704c2d050095001b0700c3e030180011b81d40c20f00750411a4600615400892040e4400c0101c02c0c0559030000b462003440d60030140008240709420010788000c651020018090301a0038100828480c000041004a0780240d482078002c1400044c550b403984044a080d50341c540b104a03103500c40141c03188042c1c01251042c0119034003140ca0744071003904415003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 135958866 1250 135957616 135957637
    0x7050a1d1f1407200301062d06032309071509051905031b0607020a03080c010c180e0c040b0301180b09040305030106030207150c0e090f07020c0607140102 68
    0xd10020101940c400b03502c04140301881245401c10205a50390045220b91001d500307a00580003181948541e000e43c81003004003040d140506001c00c0d01000340c140500901a1100c034602844000500725020380a83c4030202c0c0904030030711081880200f4522000c6001d0503824092054181c046404c81000440c10b0b8210407544940314000e19180410102c5004d00c1040c95500081003002c000580b000503d440ca0b161205030001131040709503010841360b0180310006940085400d00c00001d10840400070401c44008000a2098010b00c01e800d6400c80c0c403554042240b800c0b4510104891b88501c40081d800854407c1003d18042c0c0c2e441d04144290801e8100d070b50b082280d00701c0c00742421150701c00c0e1041c3d010306450740b040914107911f0107449030005100d0b4406050700083c1da07404001c0c0d420605507000409030000c118003a40e694008010076a07002c07501c6c1c010480c2c1d1012030200199010600e1268019a0040040b000e90400344101a00049011035540e162040c107805013540a0010b000b003140c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 135960116 1250 135958866 135958909
    0xa05040326030c0c0109241526010906060608010e0f090c01050c0c040f0506010e060306060304020609010c0506040510240b130302030a0b06040e0607050a1d 69
    0x640c00d1005201c4804062400104403450031248008840001e4a0f8008115071000307441d90f40d0301c6400e50240c01490700080006c41e042c0251078086281201141c0706042c1c81104010f811075540458181083c01e00600400000001d1001c0c48403c080c00b00742010013401001240e4000c03650b844500340c520355001103001c2070a090051120007051440294001c00710b204061141c01e2250b420364803100310005170750400c00b0005040510700804c010000c004000a0002c00210900f542c0c0f85005010039121070380007542d40c03920ba0000c0d15082c42680d000750030091413245140c590b44d0800c8200d9000d0714400341400b516080080104109211542c0f0031402030b000741c41c48400414150b400c65102c400d407607560190980754030802c80100e50b0f254080c1c40c2003640d01035a640c0b82c0c503009040f00e0340350752009615200c1d04be034007000c0000181070780380561415202800075888025a042d103070070040b500100010410b2205001c01482010b45416858035511801014170810011491141480d04107912468 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 135961366 1250 135960116 135960119
    0x5090a02040308041805160e012d0201050a060f050f06090d0503130509060604030f030c1b08030c0106050a03030203030406050411090c12090f070b2206110607020c0d02130609020a0504 81
    0x317101d0241c207921200100c050002d90780b40d050040c00c03d8000100381030402c41c540c1d04440f0740f542d500c1b08609001141c00c02005000010b2032000f806014201c50740440304c1d040c140000b072281c03071540101003551801842036408510034814812076411204e5115401000200700303102090041c0b0041ca0035040c3c111082d00b01038105018800701c900040e100d513029410402040001c200b01d200f01780d183c1a49441c2c41600003c640c01c0224906040c1c0446000c540c5402da000180444004010010490b510f0028410f05958400b0841c80809501c0090056042080068009803280e813050b5031003072098014000000312000031503550007044804500b00071000072000c010120340200241c0c801244401480103151805980d61140128030451030340e814085980880e0040c401000c3e203001429110b03070301c2280d03a6410018126481940c1580d8280123080124050310300c0460041f64040c1c001c0d00000950700b0950a01100301840304100c0030340b0b5911000402e42100340c0c0000d02d020700495072025140e9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 135962616 1250 135961366 135961409
    0x103030e0a05061b0a14010605010e061201050105070302073c060207121a0408070201091703040b1c0c0302130617040b0403090803030a05071b0c05090a0204030804 72
    0x1101426295204401d901d804110680d100411901d2034a8180b6a800384183e014003058500841c0b040b0007030030380441e1b002e00c6804602c1544550100d800c00d80e00c1e5401c202d1740c0ca0900c0303994819054000703411054140181319550041c0024078007a446441228640c07545c5220050303400c4003180b250511800c00d50207000c9030076505c030b140e141551042c542c2042114504140a03664042d20320403400801c00c0b5005e160280408030030110703c0820900002c5040d440c051614441541c0030b201d040307020035025900030480c410030224800c42e03054158001d61030b0604000400140e500a200ca0b00511941c040700a11000e50f00c1c040d0100c40c01454030b0168132142d40750170004840c25150052401c01036400070451a4081e842c00468005400c02c0d4903514544560408481048190300b0021140c8400014080b681440d40d0029100c7c51180d0b03684001c0100e004103a020038000820041d0905c904508280401e242c81020150000c411000c01480c25980380d0303542085410952000601a100c0b01039103688 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 135963866 1250 135962616 135962627
    0x6080f06101e180b04080d020a0c0501051318290102100e030903030a1e0c0f021e10110f03030c19090b1c110f0a14040b070b010303 58
    0x400c0c100c410306a50410448010310340035074140e40a034011201840c406505010f446201c4405405080c100d800e142c4907003030840c807503001d441303520f69510844c014038201a1012443c020851382c0f10794822120362901c0011101500f12036241c20114100280001d0455114034030341705210200364000c605c8003600e1810454444443c11203440140300c61407500100d81e40403c2c09101d480a8480c0003900702042420940341d40100d081041c0c2510000610002e420b4003e113902410304c10600c842c0250364908603044500d003000c0392008000b000a0044900140307080304100703200640e40c0040891500311040060b441015900012020518080701d100140c1b00074080503c4901c0c0c041d00852660030417200308101845940c1e0085503400c9184164201d041c40381041d01c2c01480344103401c54446080d1407030300c252460072140303030740900e03141100704031202400c0015901100c01c52a0400d060041203203040d5103c8004d02c9004483e901e041001040d0402004060003005000e160000415810b61401400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 135965116 1250 135963866 135963871
    0x2010213120c091e18050123130206040b070614070906020105010e100302010f050d060b0904051003021f020f070303090e01060306030c0603020a022406010f0e090a05100f06080f 78
    0x1040d00b0240c1500c408004a840205104c64440340082c040d4014103508181c9002c18400804650030140d0445400400305a41d061180c1081b1002d101500d0308915001000d80100d00250003090038841005034108540240102c2802200c01007007007094070080c0c81240e002100c1d22400310b10100418000540e0910810380501081ca6500e0407505001512442006c00307071200a0410010300414641648148203072581215214820300c601070304e90044940e140c10013030685000310f04e883c0000d10482140702162084a4014000e007401846042180e500102941441015489040380c0022600c4041001000460184d503452000c03e013040c1c00f0741d0603081d06074049030426041100a00105022405030300c219852030500582d070f0b40c04c4606c242d081044070f004007903c3c0032040340100c000040e2084c0051281134241d0358014540040d980c180d41c03103048920842d03004810f02c0002000c0403010ba00c691307004005290a5003030980e46e10b5403500010442c2d0032181c001114401400b50301080c481d8001d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 135966366 1250 135965116 135965129
    0xc050418050907120c03060515010e030a02010c0b0c0403020604081b0306010b030105061e03090114370207050a060905062d060105041206020903060c120705030702010213120c 77
    0x4100c0c00c1c02c02e01ca540e680564012442c240c2107500b040001c000b0a1900c850045501090a10441c54410080200143e04072401800318030446a1306c685e914010503560360b403a0b816100d56583c10740985900175102c9004112032010300c42004080003581d44d00c0003800051a40760001d20881c5e10f56698005010503000340c050099028070014080b030031840c0e080d83d05444099600b00d850b81c0601940140d1110600300c218068034000007840702d001410b401c201159111107140d00300303588031440d910242c094161900620307514811031014150700e9a8420743c0048400080c0982404081c0c0c40366402c1c140e15003811078009075075490000411000f444203961104070f13010116034068001c4290070781c04070130b041900d001c0c40c0100001241d030f0780602c00b44e40245c410007000c18061041c52400000a40c00f21000c14824405d030b400041da090551400c8600030664000c2d41283c989490400f079440740c0029000009554080c0040a60880c039100000c004100402500c1400c40c0c0300c2c2050080b203c3c1d65003005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 135967616 1250 135966366 135966371
    0x80304050f0a06120506031608100c092702040b03070c12090b030415090b090703050c040e070e092103070807030b0108160c05010204080d1404030b0f0c0c010c050418 73
    0x8000583e0003601c45071046103040303004611743d91014002420044100116410b50640700030228451200060568084942440812007801c03010001e81380b00402e446a4000c0c09411103112040141c0d803814036420184030040075084c29220007800d1019001195204002010340c00104140060340b00c6500300d480340340c1011a07807a810315206001c6c81c840200090b00c43d9001c41d4150b5590500c507030040e820980c02540c21041824019a81522404a4842591107103d011a0030300985401e110325403200141301c0062a11518181034103c140d030000f4945503042c02040030544910803400385c206010445050400d40c0c9180040000c0e103250720217480c0d4002c0620308028459181d800804180e0024024140c0410a21100800311841e0119410040165002040010b610301700007a92245031103468450006194600c1d455501e580903605c40074180140040104440360521241150089004c00081d4030700b15000708102e007507070042e01d000800600c0001c0c0400084a040d803403100381900d002800d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 135968866 1250 135967616 135967619
    0x2130902041203110a020d05011a04110301151103030a062d0504020c0f0307080c01050f10030b06040209040c090305060a09110907031e090201020d05030405030a08060a050406080304050f0a 83
    0x241c101402d001d01c00242070040224100c1d950039001c104500d091713940242042035019240c907020b40a0030800d42035100520100130006241c0c035140c040c00006000002a090460b880d01c10b40c0b041007100c00c000c0c1d4050060143c1220302c13030b40c030900c0110300c1000115070110b000e80c0303041c00c604000340104496440b800c1908800d060b030b080d0750703a0b000000c40d1012100527031120300c1444500d00745901c2000300001031000042ca142004060f0020700b148500a4008100d5959030b06500c618144c030868100c1d06005500d4402d1000a841055854114002074001800d0802c20301c0403a0490b44105146000f1500443d000c008000c0e0820070f07103a22103c051020b020a014681d2020b01124230485040d100d80b803054005a2542e109a203c0c40300701c108021090381c811a0b041c1d4040003000d4a440590060188003400a0424040d40859000f50b03072050043d40b800c006032030308680324000a80219440494144002225559030151074082c1003005c0c095603a0340c0c501010400c801c20a124401d000c1e2405400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 135970116 1250 135968866 135968879
    0xf02130b010c06091103031303050708010915230c032502030a051e0304080a080c09010801060c11031c020106050a03050c010804030e090c0a0e03060103170903070803030702010213090204 82
    0x80410202e40d1011020400103628074001e0380c8001700703a1030340d84c041c40007007064100300016410410440e070007a01130383c40701c2e44c0314500e807800d03200001400742518600d008410710381d04a550004500702400e070034144034880310305c0044145c003a00745c1d407007580c00a01109022400031811407085054a915186503544014090040c4d241e009001c1c00500380701021465241201c40031504001080d01d9404982e07a83c40c0a24103074601d60044600c0900040125000600c568510f404544d4240c6050b11448503030303841c04504540089200c3d0781140c11009102c19408251000c2042c2c982d40381a011003440f51280c140d07402400c440203507029600c9212140010030200d40f0129848a540e2000c0c03030052182e545600701500d031103001705803041d00100a5004c10900d01c15400103031508241a6a40011014804ac101365a5650a01010300b45030703d5142c1d103401c42c0300160010301c00100701409443c0383c039658282507410354004680900c0541d40010b1813000c1c0c01070300d1142c1805803825603000c40c1007504000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 135971223 1107 135970116 135970127
    0x901090606140306060f0c0c0405160f0e090c13080d0914190b090d050102030f150a0609050405060103020c010c090509010906050d0b040c030c030f02130b01 69
    0x14254010b41041e811030b8010003004221908240540d00f10705101d80c44180c0b0035083e8495040158041c2c1ca80c1d0081e5807145501421107107090000c400040c05200583c0c0c2c2c12000c1111034604140700f941d4903c0b50507045000c215505455818400b1240d4002d141c1360440700491003011203055005d9800048007003a41c1e60890103003640d074064002d000b20354480c06011940000e25a0082c848034040341d018060329600100600750380c10301521418226030041d00d2024041c4180c1041205d074004040c210b56481c9401d0701c0e030036130603458100300502040d81c0b8001c02d846152508007207220b40c0e102e501907980002c0c840c0020024005180002f8102e00340510404c0e00800c0380e00000158880703a4030030350b402c85c0c3d03002e0840840e036942d0384d80e0b0400d10000240104c610720240700c00400400c840404c5400030718410081840503110301e004009105888001841d002303070030420080016680315 = true := by decide +kernel

theorem cover : BRFrame.Cov 135791366 135971223 := by
  have h0 := BRFrame.cov_init 135791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 135791366 ≤ n) (h2 : n < 135971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
