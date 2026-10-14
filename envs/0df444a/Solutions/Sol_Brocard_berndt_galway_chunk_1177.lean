-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1177
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:37:10.816317+00:00
-- url     : https://prove2.me/submissions/309dc9c0-3dd6-4222-b43b-39ac0efd02c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 211510791 ≤ n < 211690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 211512041 1250 211510791 211510807
    0x70c0b090606090106020f030f070212060403110715050a0c020109051201021207031820091509090303091917040e071e17070c0212031e09100c03020f03 67
    0x5955104050a548680d1140d0f45c80801341e94580200c0348000e5180c009105641e0100034010150002c90b00041620044082d21000103040000c107071010380c0004d2412100721501e600400c107540040950340f505207850040c1a030000c043e4000c640c0c8410810180041140c15680300e03402d4034000d000f00a2189410480c0541f117203000394444810510042004000210098080c1c403034980b0b0403003004e4501d0300041c0c942d56404180601d4480d40c2c100c0c001e0100891150b5262a141c591040c1a07400c980300081c0a002c04119048000030b20020701d56104204001030a00003207259070740c4024000b00101c401303040f81307000004040d000550010307902001c41d00059400480305218060015600e80d024040141e5198071448001f01071143c000c80d860580d203d201c000340420407036100103945480010901a58006201c240700c24004603c0381d84086a210035021021a07400c950040c0c120b6914942459100440c040c80e888140c1d0b1018007a900c4660000e2600038007100d40444411019039503a0140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 211513291 1250 211512041 211512043
    0x60d090614190b0405041707030315090e060906040c090902010c0609060b011112030103031b020411090a090905071401052101030b0604020a2703020d051011180405070c0b09 76
    0x104a44034012403c00143d0f0300c060401c0e125a5015075000003071021402444460b050b034550010b24100c04055994158041c582c0d0310003011405030000d1100410041c0f440b0070400d20304403014200480781d8002c03500f404005440003141d42d01311a00d402020034901110300040e9010100820058109810a0281f104111181c0e0050450030300989510205004002060303507501d11010416242c11002c20051001c0317030040c100305815000129548a4414071680170409841c801041207090036000309090b40306242c168007010240204850800c4903400e50b44030f01e80c1e07485040c803440d00c0070000811900c02903445074040f502104903004005a0050340521031101a0100340b109035a0f075000312011402600e080e000700d8414902603950070308040c03416046c1d5240c0a2117500303501ba0032540f400f00040140c9400303186c84030303c81c02400a04109040841c018082d144028003407101c0001c1048010700020b010006010070040a070b40000e4a647c0da420709440e16440c00902403c0d1310301042c02c10048441c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 211514541 1250 211513291 211513321
    0x80c22150e1e01150e04061707090b0f060409020d110c0a1a061018050d050102031819080a030b09090c040e070501020a08090d080333060d090614 64
    0x5200c41d80c82c88000c48080040303050042070240e455514008680000541e101c0d1200241c0c10000400018a880d0b0343c1f03034051240422030262904a400c269820400c2c908240701d490b00584090700c000000807040380009200f0303ca58010151400da002c60700100300c40645d4003441240b03c80307581c5a9541c0c48400b032544d94070b03040100121810f40f04a01480100160803131898041d070070252074401113503070882c029680d004050a00410071000031a00242c1907803049880d2050300e004100050766801c180107009925084400109916806084a5056441c0014200307a50f907401c00c000c0e03500c84010380303412005406403664032940002c07808107000d901100420403109a0a0850b401c01084085140300c945405051040c0b6001d600881000800b01b400700000b081c0d864801403c02c403116040d9610306900d60001c0d601e034415132804074940545098002e1210042c2d90a0121503a003410035440054490303c90300045501183e1102102410400590858881d5175403008401086283c00c03131401d14416 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 211515791 1250 211514541 211514551
    0xe0a090504061d0f071a030103060f0908031303080f09030a1d0604090609050f0115030f020d05100f06030207110d14060702010c1404182301080a020a080c22150e 71
    0x5c010b0b8140080d81c180004080c040408410b000d00e421a86552203141c000d100c00e40070b0b59807031501d9038241c1002034a500011442007124603d149401c0400e8107000f80902030041048403038034040c1d018450003400020640c1c900b04200d1904002d60f00400c140c0c1c9629520260840e5003001c07021401294040040d0410003d07100c44401c1003140307540300a14100c803910203104502e60950700c408558865880303604150680b860b00200580780c000030f0a2401c0890b4011541c0c190082500ca4042c800800707616107081c002d192903c0d003507040030744980f10301c28800744401c0014820f40d8490031a070204141828842c00715088002601d07004d10749200064041e02c4400811000100384050300c1c890040302000f40c6041e600340c00d080c03600b00b203560380c4014014040319072000400d02c171203510400f40d814400f58031406092002c000e00f000e402d861052000c0da080715040040d450300914248135458498900c56403103004152524009074482c804014020164000c58055035850041c0200c0d41103020001d40c1c1c041c1e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 211517041 1250 211515791 211515793
    0x190608011a1305120106030c030b070305060108040c060f090b12010915080c150c120901080f0f0714041806080d0f02030703051c0501080c100e0a090504061d0f 70
    0x601040710840301e07118600d00308120000b802402d005070b00340ba4111207610040900005080c584941303800c00b1000040c5d00c1194143c00e140c0403c0032255140c0a042c1d040402820480d5071402d103a035071100383d000180a61b504001c2040d0180c0c180500c900590b400030072140d00703c10f03075500060070a200301141c02d0003054001070030300a40805650b004144030086441c8407018195010300007040151402c0020280d401001e802d00045c2c2000c0014008060181c46401c03040e561820b411002500f002c0005120802c0c059102c02080340c407028601c0d1080d1300c02e000d80352403002008100300081d811f0241d038105d950080700002d41818600c4081e0301060647d8501c00c12104541e600303007c00c5500840b01030b0103c1c0140c000384858000a4004c0b8080c09000220303840780382c2c103003200b40c01c00340c00c0710000d034042c0070765030300094104846040001c044820310006140c00c40800c9080004555040894404d03000111f5492001034140011644411040d400c6070303010344801c8a000350b8940c1d640f00c448903803046c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 211518291 1250 211517041 211517069
    0x1b070f030803130609060c0e040b010816050309010204050a0e0a0b010503010b0f070f0b16140c03090d080405040f05010303120c02071707050d0809090a1802040902030307050a03050c0111250219060801 88
    0x80bc0d80140d07601480785c2c105002c95407000342e00311011a501c0d00023810f030100381d40d020300c8080751540d0340c0301080014112105a9414500d014492003041c0ca0400c5c12090602030208018050f0206010868800c48601035806075103c00c1403410605810000c00d002d000c0740c02031414400420001000744281140660f100d07840b0b11182c1000018910a08005c1012a030041140004c2c9050002c60341c88004d014126207410140c2c2c43e00800e00b620301c80c03a4581d0a0559800060040580040c25040104080a010044c510846101a50700c03031040c080ca21200918424080054404000340806004040c255025042c00d81c03500542c3c83e045110141d00c911581c20008240c0080c40c1b107000390b280328003074060710290b4040e020701c8000c0100e4003050740c06010400c482130125800f08880e2005502c282c1d9056a15031b429005a401c44c1c010880300d80381000100401d500607881c46825880ca00c2101481e81a820054800200c80c0c0030303040c103e5038101e26020000280c16801042040c100d89080841c005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 211519541 1250 211518291 211518311
    0x1201170d0e0604050f0a03060c05041703161112010e030901082d040f35070209040b09030c1b011205040807030f0e061b070f030803130609060c0e04 65
    0x1001c031442020540c0145007030000f00081d01d080f40c4480d0030010050803101d00705032681c032050143c0c0d041e00d5518001c10800039080140b020840e819500c0482840055414150862600c607064a01c8038000303000c00c840440b42002a40d5102d0300e030078515101500030081d0303160740c42c0040d0b160b40000e901c99011440076800a0191111826207040c0c0740c001d021003248402140f040c803402c00001420650351504181c00410026a0344094000040e00203031400010341000554a0030340500a1100f251100d0140039040041e201c2c200015080390388100741d107202c2d90310b194a403461401802c1d4024002d2182403003000c400e0500042c00201c0050a1341c440070021802c0050740e050f6001554000c24100c4100010404680300c0c40d05400d6200140c50610045400840081c60f81d4000301003114500d1400000750980401c01c00c288002056107014064000d451030700c62041501000300a0044080000b610380c0401003503521414000350700c4a0200119401c140c0d00800c90500042558040c070714003c1d03440c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 211520791 1250 211519541 211519547
    0x6091b0509060406050a0509090405010518030a1209060b0a061206090213030303020723030423090118090b04080705010b04060b0a0f0c05070611060a02180d02061201170d 75
    0x41d580358000b4011614052605070201c4e21a4490501d0f0003c11070306000304e610f51355400001d039010b640a0703000460a1b00705880c80148002e000c41c032015580c1d0080040010650b0040301000c1801c0c0e141e41c0000354865541000c030003501345d1a001543c0012003c4010a541d0b400054428031041080000c2120a868583d44022481401e9482e242181c10010400000e0720a80017058064400c0c03507400d035034150b10840b00d000402c0c1d11020500b2500007080521400c0010b503208a1802d05060b0725107a5051104045080c0c0d0106004100000c2d0800d118900440099008944a80d50040302c1b0031079450181440d012540255904031143d500301001c24600f840c0038060030b000d80300790082952420a103910140c40c6442204521000e2003481000d481c0482c01c2400f030031004001944820300710641c00d01445003881c000400302d616207031040c442202c1c1541041050b070201c04056030078251803412400025913a0085e400492030401c610000403e05420b5031000307041005010b0111102d00c806842c045d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 211522041 1250 211520791 211520797
    0x50403020f12040609090b040e0f070812070c06050c07031202060103120f12020c0703020306040506060901060c030c0f03091e030b0105150d0b271e0423010e0106091b05 74
    0x2c44009a1707814001d0122845c1940050085c401c014000242d14500c0d840c000e09180c03407a113901090341c1010720b08002460090000c88842a13202d60010703c1d10b10181ea035002c401347c0e103010346800c02070041480213041c0c5080102c1c80c01340d5001400310385607a100307440007175079854240030480796803038a03004202003280190302c03001d00f04000780c5032000c2c03c2050740c0a002c025000884081c04a114280000005d40c03003c0c4503c90080c0d002e81c000d000146442024006081e0060344400208004100400007099000c1c08003546954801c040c160568141e040840c1c1c81c2d221500400900c680d039140d00001d85030008070103003c8a229030f526444680e40e403010000041000d64202c10384200811650040c0c0b10035900c83c0510f610010081164401c0200b02689014218501061482e00300303400d001c452555207400e84603194445114a000c0d243c60340d100c00300b034011100c0490401e282c83c2400240e6240c01e412000c2010074140003080601e0341d4500700c41c0034011610700006203150040140311800d1140c800c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 211523291 1250 211522041 211522049
    0xa0c0326040803030f0402011b03080414060121050c1c03080108010b0f13061e03110901060f0302030a0618060f0902030903040e0c040306061d0a050403020c101101050403020f1204 79
    0xb5600f10340c0c404100624100c40181b04070b0400400020440c4034224951070145500e000c0e544100c000d18051822178403001c000030703215259074032480040205000e82d2240d607400c525550301c40c100c0d1000700d144c243c0c0740c58a90403c87d64006840115002032400fa00756001d09980a44e5034040300b40da8031080300b030881b10211a442e4203d0300c0481909403d08042c0d981c40311080807060000f07580c982d140403c80c182140104402c0c03034005481b0042084c80140001e1400d469401c540d1400154548400901007a00d48803062060680100004610458a0740020020900b103947e9500d41a046005074000b40f500b8001c100b800154034130b01281c14011b81c400d07240b040b1b01040003180b4090415101070350f049401050800034000411010000440900960000705504074104902e40c0360070781001c10b02a4010405000c4034a414100b02c0400e43c0016010800c3c0f80981d0368441108507403400326404550711401c803c1960030a401d1001701540003918081c2d105a85c816541081d0011444c00303413500c190702c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 211524541 1250 211523291 211523293
    0x5060a0506090f160f140c0a05120c030418021201030b090f0606030c0402031906090c0f020a020f06090102010608010e0f010b0102030a0f030c0509040c0e0307120f060506030a0c03260408 82
    0x10070b0702d00942c010380c82054000c0c0030b402d240c4846845406c0c3c880e00c81c3c1c420508441103401c41d401842c1048020010001c0100801004a00b09000d100c0d146590380128840c1c0016088012980052580b490b0304543c040aa090600d00b460740e12070814450000042e2265a21071041101002d1107140c0801c00c68001c2c20010040d040b808034002c01c200103500003500ca1074001c0d2500b1b542e030003075020900c10a0014070300d803400464642756052028268200260500b000d640000c02d00d50b00503650940709035000704046071403030b85610a00004074010405504454800d61a0181c890b000b181c0004120407a284180c0c02444022080d4004a8032030241c110a1030101c2c40900030245c0d0a8001c1d004001480e0703552503e039040220300740000d0151030050321240c0100c0c40c41510390303000e82824805407010300340042074032030105070580e03079200b03207120700c01010300345999800100b046540d0034043c92003c2ca4008801d005010344030308042041c1e03003244030011524142600403000c5141584103690448440034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 211525791 1250 211524541 211524571
    0x302030702210f0a030201110306090a0c0909180c0504060e0c0304061104030803041a010b0d020304020d060608100b1c030309030207081204080106081504030c03090305060a0506090f 80
    0x1609009882e4400e41034a5611080e881407802c20000c100048480400e03a0401401c03940c40350b0401a0858500460a10050703004004101a0352204c81c0c071a6008000d0900010301c50107440310494801c480c0c0c0e0010034000b401c0100090000020f054214480d90141041c444056503d90810044903018469000b5104440b0f0004001641020107190b10501030703140480c0100700b05201c0000355119420445544030003206000901105120b4607850250841e448011740d4104104090b0901494907441c0405400000250454543c0701001000750352028041c00000c2c0c4586145454480641c2d0440c2400d04c1c1c800c074030034503143c0b41030a600744000e0b0090100d04d0f5015a10102e0280c1440581075080d4481c01d03c0000d0102020406100c0d08441034104589450406201500703552076a807040700c060b0701002c60000d0b80d06c02d001c0300641150341820b1a826440c5c841c80c0c01d4601080550020704035000790310410621f804030740c01243c0304500407039116045030f88440901c1d101c1482507440e2a08001a1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 211527041 1250 211525791 211525793
    0x601050f01050c03070510020d0c0809071e08070b04030b091203040f0602070212010204060908071a161202010203010e24010f050708070c320d06020903010c17010803040303020307 79
    0x1100108050500300044d82c0c0703407034010b49810b4603001d50103062240017907000513030056039241c46c82020650001494481310341d040c4055029a121854010500211103096030201541080b0440714000c00208041e41c3c0800c2c0e8078000c01d50340e604184000e41d1034480c004000b40401c0c4000c12540f601d00052060781d81140c40fa502c41490b0701d888094211802682041b50402603a035200820364065020720025903241c1c00e0810041c208000c07940010210385c070142080c032480d00c2000c14456801013228a071a201c80024080c20100c581e011409000440700c2e015940d901541074008506a440d02400002562241c001d4003400410030060941c0d00c0300d90504011042d072140601c50a48444d61510340c1c01e00400c2d440c2e020700d44c0d0001004aa142c80408020020b1401c44100420380c0070b00802e2425558181e01d12401c7c18514900758648030b610a04001c604100240d810380c0e04050700034000304200d0001800280280881d0190380b01313034174195000010200c200004450650b0740c107501550620303400d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 211528291 1250 211527041 211527047
    0x110d02100c030603051f11090306040602030907030b01030f06110901021f06051c0c0504020909070311040b12180d020c0f210319020610060c050a0c080a0201110601050f01 75
    0x1c10100a0101600c0d901c002010440801c481c451100d01001c2030200d45034401a11011201c20b0030304d201415105202407112541e0110304070382e000350000000b50f41d0b070b900d4544035070a00480d41c20060161011174008810f0081c0f40c0c561a1445109000070800000310551425050040000360350050340910005c41002c000764581c40c041542c1d420002c22115115000a404031103400e90344001d0101c290011005c1c0a0100130b2000106801c3c3c9046190058031000305183c550010200c01c00d1640302c4001810b18000b0404a41c01055214001c41e00c920160355000c042c103c0036038000c00c43c628011425019031001040024500e2900d40041c01e001d01440c1c14000100c00c100c00442e4002d042c40100c544d80102c1926108581200402540e95aa40099051f4203c2e51808840f8110740c001c03010400b251490306201e4003610307500c2c104200c1c0e0784c0c40d900d000c51400c20028401403960403102e00024446d440001e0a2001302c1c401d03207a0a1210030107101295441a00b441480c0c0c0c01002a6401d20305540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 211529541 1250 211528291 211528301
    0x30305030412170a1d0f030c060a0c090b130b1c050709050102030d0b21070807090603020f040f02090a060e0f030109051b0a0f0b04030201030e0d0f0f110708070303110d0210 76
    0x110325280004159117040445080ca540040003209580000687c9059100d003448a04c1d40203010080410040c0c042c9140106000150b01491101e00701c0014000745920484801c08001c0a0350701c6020b90b03404607800d43d200d90864900d2032801d003070304010201e000c1d80d014421b85000e40c0e106034015402c1a410401e40c43c003070300700649555003040721050200400e2041902800300040020010b00c071040c90b0158052410140c0e50156001519060085c001a62502c10440321000211008501c51041d00c859030700034800c80220310750084144000144040d00070300079007030f020f204496900c1280c03020300a01d0b00742c50305480024555008403003580c030b020100e150003044081025001e50105621a44e4020044000e0780050140c3c03131000c2420002c41d81d15004070b840c2403100301c01401c40c1154865001d40031b5102101c4001c01d00504010740d0000034445e81c03d03051246440002c894142c0c0d039480e51140c549446c2e00054000480101005eaa05d49001410302c9410b4840d40c01407040c03030000c500040c0101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 211530791 1250 211529541 211529561
    0x3020a231b0a1a060f06040f060e030712080a030b04140703051b190c02190e0c0a0203070b0606090d0f1205120403080604200a1e090506180604030305030412170a 71
    0x321704544551840d02ea001c040d1014065012141030000e040500c060288900005e0891080c1c3c480d403030500181e20401c4e001d40010f6071101030240c4410b020f00041e0080e241d0481c2c1e49400500e0408000704880c41e0602c0b1074003500140e1000c01c443d1b155200403a070001405030f02c0c03201e801420400300340b00d0301c40c2010146805010340f4200c1100390301030b8000303012032808003141010300c402c102c0103003c08074030f8a18107904580c018506c0781c6413113089a030181d200c1c041c810025203102052000204075444581c1150743d01310b0300815038030680c112481c0c908a081c2c4903e005640032491030f15003910781d0780100304607a0141444280084942e8850383d08507405c00001388003c1c1c11a4440c05a00c280c41440b43c219108400d1f00240d690315031a103118010160f00007659140c6007203001c03010300a0015041910381e801d5580640e059540e904c8240980c546042008442c0c0d600302e400020300005159005001d14003d9109070b00704815551941e80854914055500c0d03170101f034000d88080340080d03080f503120964003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 211532041 1250 211530791 211530799
    0x3020f22030615080106052707030f0c030207170f0301272306030105010b16060209060d0c1706060d0507030f06060905040c030e0c0103020a231b0a1a06 67
    0x19140d9664105999400152003080f4103030000c2445015420301075280508826a40c200040c0d032610f03034000c0021201106204400380384408100c040744650080594183d207240305001e80c02200c10018001c2d444050199000d10344043d15114080860003141c800702c98507a030680c11a405c01c0c040c05056051410402c03520304200660300880d002c0c0d80544200c10b200d00340c3c5600c404854110603c00c0140081045200b0b924080060160448030350542d000c1c3d10703402c0c00743d0818040900d002c20082c0729070b0350066848917021540c654100000c1d005219900300a640e648601a03028002d1000385c041965100d52250052040001c050f0807a1702c01c6034800081d190110310200000b66900032602c840d00310754000790140310140514181801060903049040c03070104130030584d074a501c03502c03101c070504051704054000403490345161295400c4468000c04120f002c21003001100c6410990317010307c40e40606489040c13008035407510049040400e086d005400d04500c443c40143d052807040c40203094070340c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 211533291 1250 211532041 211532107
    0x203070c080304030c05060702090f060f060c030405030708070324110a0f020d0e090f0408040f0b070c0b0702060a0c060e07080610140112110f0705031903020f 70
    0x82030601540000804524000d1035466007075041c030000c4140d00c0e80109000e001c1c200080b40041e1100044198030441001c030010130b0b41c0700c090024507007500404900e070340944080f40100240b00044001c01c02c07180d0840868240da5030f1541b807a81c8800c0030340301c0a00924400741c40302e80c03c6a07504000041446003102c1c000350148208140020540280b00b8010000c0c00c400200d11041790100401880e8071982d0902c3d1030000b14400c001001d280c0005c0c4203c081c0c0903001e0200c0c00308001e15003074401410100b6590040c0a031980c011246c65040724409544002440400040c402e50a80480320891b0300940382510f06040650141c0b02201e442004680842d9109400a0b131014188002000342c908107000d403aa82c00c0c181071302c60928080340c00c1ba0700d503401d0b0300300502d000d6071300b1950306a4120101203020441990704d61203a403403401035004043d0036600c000781510800030040001c100400046078401808008203a084040340100c440d2200700500822205540708003900c03109100c40c0740241e090107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 211534541 1250 211533291 211533293
    0x100506070602070605010509092d010c020f06010504021801030203060a080316061b17071101050c03010e071e110a06020d020c100209010807080601020109170301140f030d0f020307 79
    0x55440400180c85007540030445208001050150346d004000481d40300010b400c040d1111919070351205080500780784407104503569507412400015491070703000020080402050700203515140c200580100d240a9500003003000d107070903c00e40c1c3c00380d03150030000e01440381640019002580054011070340041041d400060101041004044e020300040440100002c3c928000b07050b81c0d21050450b04802c0428200d175825a4005c8001300142800c0d5648040c9450306201a02d040401d5074070320b01c04c0e500348ac0802c1001c208400046040711107045601d501641c40304002c41d603442144555511130b00719051350500c0130b485001c0c911000002c0505031030203010705681c0c003001c90340603080080710310f038010981c80b8450303200380f140403084043c1100552401c0d009400080c20300c1c000034904414048104042a580c0c6d1007503201c0d00305564400c0c9110900880704840031400d030000d110f00260300220004041d02420b003840326003690320b070150003000c5513034040c0c1d000d460035103420007104210b10061150340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 211535791 1250 211534541 211534549
    0x307320d0609150b0105040509130c080d05031501020c0901030b0604020408010e070911040f0e0406020c0307050a1b0f03060905010e0604030c0308011409041b090f05090106080703030212031005 85
    0x8500e5520803c0300d070020000580045095071480303803055051100c24402004070780c030f074000507551041b080c07510a980c601092810a01070000d940002c60907101e403002c81e030400d5400c03034002c5024022145113a82c8080403080126904e0b050792400c1c0e60020b0f440d900401c0004c02c940326940d04480020005400c0075200c034034041c21640403901140560307011142c200103c03038207489900d29454900384481e141c54144521005944c50b2441380141081c0d64000060a00c140c582c1610403408040342aa55a011076040407a035031003100005a400c0305840c444103c07412140c05c05881141e055800f000d078810328548800340104801317102a00c0c955240c0403039280c6400706205a510852007621140014102410010301890058200c03507080174266007254595541c403c00c565110b503021b404004900e894052066080d8544d5001c01d40d19401c0140c01c00e0000c489800051140e605840200100e903078903d94241c0d80c40d03503440b020b409a044913019448103e444c400070342e88074000004007103103180e50744049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 211537041 1250 211535791 211535801
    0x204050a0f0207060501170d080115020304030206030f040b0105062502061e0d060902030c040302120106050402031302040f0c080c0a140301030f150605010207060309031202040b090307320d06 84
    0x111100d40e9a4401070107c0103401ca42e0000c2d0302c00c904010003501c0c8030b6603030140c10a44107000b00c188231707110031000b10b149610070002c81d03001d181c1c05007003075442c0e00b04844048018003050320121400081c802c00444c80e414182c090320600e01c088011020203072141d5403c4d50018501240076070b08074030100104d082c9511030320b6401d2610280209501e5643d00341910601c00c030b6800350800854980100144401611144140e400784c0350110303250500c1000409009004000b50350007550003d0012041014400079021400d021038000c0d10180224a0000207000450311020058000b2444030000310384c4092403c0003400c40b402c0c090900030004007210f041c2840a400c244e000315038a003144c412103001c100c0c0d03800c2014a0184022401d108441c10500041c0d21200503005031002c041c2c1c1e40c882c0e4030906100340c0703c190140075004421941d407600c45440034001e602c8159028040c1c4183c1c2070020320301c05110700c4c00c03102c210918920110050b140c903c1003100d01e82003e00c181c0c0f250102c0d1130040422058454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 211538291 1250 211537041 211537043
    0x80939040c0c15021e030603100501060822120c020d0c182306013609062304090f0516030323030a3201050306060f0d0204050a0f0207 59
    0x20024102d0192a00e65000b003040c000a59041e40184504529141c86800080c2d40741c0751812840d44940c1e031040402d2900050400440b03005007408000212300f42c1103001d00d4000c5440c4c01402050300b401c0300032002d903000301000060800b01003c080c2000d0f14814483e891025100510b840c449404a40b40d6401d00440c07504070a040b00404044141d400c1401c1c800d01ca0015103c1da100480c00e0185407800000801c002c210070305000e07203850f81c80c0400010949103411480d4800481d100b40c44c007001e2010403003101c1d000b16031045141c10740105e04055500c00e04600094001d040c004100c00c4003081c000500340c0e003103084030940e040e24040d0002420500403104032140c82034448811901c0e50800a000350703900c1c01c0962101421808000c800044c1000b100e50205000901140a6481100012282c1d102c0f103210510402c03113402c0d03080f1484052030b500f4121941203007282c445481d14001c0100640941c149103030300100c403031140301c010704094001c240e010841d4040040d02c001615404400d03688440f030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 211539541 1250 211538291 211538297
    0x3051c060305030f090a09050702030313020a122102070506030106030902010c0611070b160c030c0c050d03020d0f08060a03150603080c0d23030f04051c0f080939040c 73
    0x17551500e2800d00000340310041c02d00304003e1100741445000a9201e20010b1302c0d841070450b41d50781803401c1d0b44510100000070b1043c02a13181c0140f0607410800e00111601680c0c451002824425142140c400142c0c4070995400401c05465070346403200c168018110f8060880c1400680c00305140420983d102d002c0889a00b04d000d0ba0f601c10081c50038881c5540014400c91117401000784412440b5070000c044500b0940c141070000c8850031a00704035000240036449294002a203ca405081550208400410400b03c2d194001d45500c40d44003610b41400442d60641c0000401030200086182082c0401c14140c00b038100084203a1281c0701c00c0b1084e808041801d54551001c4404410310768230185209400300203910a401e4140c1c2c0382c108901e10310000d084114907071503603c0402d00340502442100c2d40c50441007065251404005405000481c5021081010400980004861003400b141c0e502e00f03a01101d42c1e4108000540340000c0d10b0800100241e40156103030400700c1e645869a2003400c0c0c400a10340c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 211540791 1250 211539541 211539547
    0x90f0a0f0203010f140a060203030106050c030708070602071a0f040303020a050c0601060e0f0105093303091501060c0203070e072f01150e150103020903100c020d03060303051c060305030f 82
    0x5c021041001d03a42607068001c541100d0200311803580030040da41503580601c2c16a5848403034507003091541c0150710001d8039000002401c0c504004183e402004001e1040358112031901c07072400d04102e4000101d46014a1391403030030004000034429801410300b0105818410306156015040514110342608a132000c25a6407420700d10310f00c2c001407881282035091074030f14035002c0501e003c910750041d906006129000501108166400284040002c0c81502c0c1001c984a1400b4040d0315660b03030155945070324080c0d0740d2001040c2d841c8035101091506030042e00811815150075001200360304e00400705820803012040300000c8800580c589040322140c103000c101d8054505103c0ca0854080c0307a02490314400036441040300807c817503152030f400b0380490641081031983ca00142c002e445601c1006a0500400f80c06a20420319503026200c060042c0e4212001c0348503100c07040d0308582c01400040c02242d028485203c01d69110420710112103400c00000c2040740c4c3e00d030340d010f00c0c542240600d48a010004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211542041 1250 211540791 211540799
    0xd020307030f0c292802090a05030d0c0605010e0606090d0204150b0705010e03031009052703030708160504031e0807080a03050a060f12111905010305060f090f0a0f0203010f 76
    0x4e03550b540d80100d85000e1020350302d108540c1041c2020741c0c3d00c14000c031990f0080388071011130b40d41903030b00030007450081c2c01d03070f019090b010710001c16154098004440480c035000000c03c0c4d00c10f8080341c0781d04c0707901c002e480589000c8580c401c0041e590002003040740c0c010303169950720b81d004940b041860000c02a4030b01c030541b51405e915091303003552a42c0102c90000da001b40b01308014200098903803011503203103010004858640798030106110071800d003403420400ca854591340e20020000002d5120f100d07241e0720070540ba1108044100340104610490300045c80900081c008107152035a100c10b503600c2c007460085a81d10039560050030b40c0021000303440250001c13402c0c2c6603003500740c0181c1d680f0045c40c2408000040c10701d40d84901c2c0e242680100b601c29a1490804010272640c1c1c80c0e103186008006040c0c20285030320820312280b0f25001e006150000f4200000309901e030611141603820a5402002d1944035680d080d114804120020700304010f140e1600214281d40310180b0085001e400000b9204070350900b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 211543291 1250 211542041 211542113
    0x1020a030b0f030d110c0312041e030305030a0e03070f0b070906080405070b0a180b03090d0e0607020d150f0c0e0102030c06071d0402030a021b0d020307030f0c 70
    0x380c103a01d00e000d840c556600c0342082e0350100d0031441030780c424141420030fa81d01c0c8145a15000e001c456058152043c40c5c2c110104181d000007420481d0b103030b030703e0004403c8070b5141d800304001090720004010980500210711101520342000d404102000100c1e030619140e6102d624080b602e0080c00e551800444003800690780d4859008000340005050150f001d041580d14295039811500c10300340700d507502180001c003ca01c5105502014040185d10300105a11031148600540c0b00740c840102a109241013001001c3c040e030380908184000806450400c8265000d02c600c901c00140d08a0340c4c02c90010180e46a140d8030b100c0c0c0b6211000072000000c10060400025041031119000385056500c14003040d000d54000091840d8800d50614003820101e131807000403a11030103d40c1c80e8076800390010080101e107914640c060f0140c910311101110445100d0520740303440c0c40302e0300a0b01d40140c10800072040030902400514a4204003442d0100d60000240c44100700b4844c40781141c10308030400c3d4104021440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 211544541 1250 211543291 211543301
    0x28020a02090c09190e040602090f18090c011b02040f140906010509010e06090423070311150405100804020105040905160f081003030e0d050f0a0515010513090f1401020a03 75
    0xc03c110fa075043c0c09040480c3da9110b01c5c40100010115500010700b18260384805d08042c4030003078098000d01041c905540ca580c015202100d17842d500d4490707050305801d00d40c89000c0360441040c0b00e40d0703d1000d40480c2d400303000c0079100e0044500d0300b56894101c4071880c40c42004e0a240315803007a00140c4555410b0204000100c401a0300c2203d603040d2050510525035114400541c0050b8003034a203541507510701c24100d0143d130143d040410f59003d250000000d004500500307005401c41155400b0014905c41611f6456010703502460342c011403007600c14600c0e00d005813680e80c1c010740141450340c10a9501c1003020b007590304c22100c41061500c40209881c6264000024146480035420140b0013031420301755417120000d0034400641084200c180b60285902d42c443e80700c210319007040c15184504940c002e89691503203200800c0b544c0340704441111035503050721000300c0d0580d4001827420881c00403800135100500362001081d01d0f0340a0f4010715400040c01810503403281c60001c4009a01d845c074400740070341111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 211545791 1250 211544541 211544569
    0x70b0d0e0106081207050705091b0304020406030803150f0315041202010e0a03030e1006051e01110304080a051207030e09041b1e050405100303050a02070807060e130228020a02090c09 80
    0x52741d00420b11001e880c0c07001d1846c0d0301d5100070301c3c0e05849594a00015010740455030016081690001c1030040506a5025881c40580c0039262044103080c1e440038156120100d901c0000d41d0354111000c80c2c0021880c1c204200c0300c1440d4030001c00c0d500600104c4500b06404000110040ba40d40e81502c400380d4070a2000041010000304200102480d11002c40e840803007040e07641854071443d04070341041d6070046440c4c103074804000b02100d4a50307450305101035688240d2901a1214030810841d807500c0300303034502181d0095515943d20070701c105a01e002d1002072103002c1c00072280c80f80c821008600283c466460700c0014080503504603595810b594810b010b1011941129000710304000400c8115614500d0200459501d07140c200d41d01c482d443c004901b0400030350002506402290800503d80383d114002078913404046600325142c0c0092400203080384903c01c0103000885a0480c01480802c984440d15400502c60068894150076135000a000e0b0900316020403010201080254040c18964902903c01d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 211547041 1250 211545791 211545799
    0x8040602010f1a030c190b0f030114060f120c04031407050909010b010c0f020d201305070206072d09030c0f120b0c0d1d010b0102070b0d0e0106081207050705 69
    0x106251030007003500d075003025040300c0c0190009601807a41c62217800a40c002045441d56148d02d0b0303004242e11704140e034001e10411182c4440100e115850f40b6042040300e03001c0c80002501880c04001c11100030541c5002081e942d0206810701001000c92010a103401604086501a00b001030a01c0700f04200c40304080c3c901401c2d80e14000200b260741e40c01c031044440c0aa0080b911844c1010284002001080b11910080c01e180a080e50010002c1901c404801040400c487c5d003a07000700c94119100c104d440032150580140c3c04200401d401c1d40c0554010207003140d412008095840d00d503064621102008490a40040c034204010030502c50940c1600c4003400700e00b20060b00d01071812070000140b40c1c0c04d8030090000d41584001c2085400d098007100c0517004881c10030b00808a101800107040508001c2c00a0b00d0b5003020520740c055880402e030a8207844101d41600c0c00c100b004c1d01100c006006600d9984115941c49001082c2c1c05420048160005294040190740300c04915005003040c0c11603110f1401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 211548291 1250 211547041 211547081
    0x6040509032119060602070305120906090105030402030c0a12020a1d16020106030f080918010605030a09020102071e18020a140c0a0c0314010e0604050c090402030a08040602010f 78
    0x400c41488903428002d0040c0344421409445003c0400314003803403031902c18801460400006406600401e00d00e0441e0f0042e0295035006070300e006c94044d28072418039160740c800c4c0100240ca4056004038083d6400078000380840c3d00f1803e26001149004519400140080c20310103050780461820500e240302420014003164580c85200c0504801b02c075000d800d02417003a0800e44400d42880c401d600c000001d64106803200712060b680c2c02c00000300e03070040700040d026101c04d80f80840014401d5100c0c3d4129080365586506d1640d948214000034001032000300c1c11405070100010b403614054a1104590b10350203070200b081c0f403a00f490520980142c103650410742c1d00610115101c40c0d0801800c124a484907a4000daa0340e0b404003215040004c143c2d03004001400008001c010700051000620080c1c0c0040020400499400c81207940c50608071001801903000d0a81e001003410640d4620350003920160403100c1055550350365500b10740098000f040140e654018242c0305201c01c2c090b20888115548001d01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 211549541 1250 211548291 211548307
    0x605040e0a1410151401050c070605030c0403081207020f06040308060d020112020d0b010f1803080d02130303050c01060f15080417070503040302031606051c0f140604050903 76
    0x1403214840d40300580880421511414a0801442400750004844200b0840313071480120310003000c0c20501030341041c1d1040040c290b00a500410840324034a103140c00030602545810011103032a4001001c04d80c0e01103003440000b00081d030050141200d1880d0764656003c91418410092400080d1407101650707603c5402800007294100180c0d03600010103445030b644001050005940043c4800004240140f0005050350a6040c2e41e112221040c02607a4621035188501800c68408035084224040c880001204000107a0320314001e0840c0c50710940c000d030030400c0c1c5000080c003040301e81c2d1065011920000d0107480c0f458080c410328028190a541180d003181c1041ca4100ba20100c4650520a00030301001280074030012540b05030b0f03100c5240302d01542c0d4440d1864142d84030b400501c07040b4003c1c810340307084002013400011908159001c0e035443d281000007600c1030303a14444154030360310741d01c03070b035074203034103026813900d0080f96580301e400c104040403414410103000131541c000786508403035041800008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 211550791 1250 211549541 211549543
    0x100302030f040305031312020105060102060105150d09020d020a0e0a0e030430020405010f1d1b0a0c061a0906010201090b0703020a020c0907020a0525030201030903120f050a0605040e 80
    0x10b900030b0b03014500242c41e6612a03540880410700b224000d400342d480c106003040519415080306100328002e07400d0703c0e0a0399130340c42882011a18500e41d548840030602211034922902c0d805000050700052888884039140c4e00451100b10041d00104603004a0034100300e405074a43c010110340004180045140515190501b406681c01d046009202101908103a0030703000b07809051485aa0010020403155940d9003590320195614031840400406a00d0020b081e10444451144101e804175441c5681030342121114851b07501c10030746002801544051500454450701c602400264903008128a18001c1400c00903070600007440581160b04020b042c034005248498450703049800c81c100583c44108140081c1d0801400050094001100d04100319034903500180450200380a1001e44280c00c00c056035004880e413200b0700901148000036410001544684e0000060300e010345041704140c9010003030481079960505000c13403140d484074203028440c1150701c154801090700701c130208407900a110000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 211552041 1250 211550791 211550821
    0x2010c0201120209040f020406140424020a0c0b07020f09060f040b031e0618070608011a0409051305070807050a030b04080c06040303020d1835070302060610030203 72
    0x81c10070505100001c0d04154070703010f4440581008000380f260044000d0380384001d402078400d0200040d84840d001000792042421142a0745840104400000c6109190b0030040b0100d059a41144601c50040010540c04e401c014058000c035408030790340380f0070343c010408450064521284101c0512090101c150740e01c00005628040c16280401c400010500090400800c60541d00706400341f0404d08082040c041007441c8501c4210000c841540b5803000c0083c0e645603079004100210380364000502003007801030f010010102a0b000006c1c50143c8a241d04800c1e160142c1c2c0803844004044099010003c1c1405180c0140c4110401484040c0ca080000381d004043d0f0311001d040d042d219000309040c00745d00c10840360124440700032120b507410140ba00030007e41c448403072440340d680380998200811000640b1100840d410100d80d5500510000c4008660000342c0501c0700480e840400140e10754408c900942460f40c00ba8010b001c062800000707001c8130f104401d108508051040080088403d1100c1c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 211553291 1250 211552041 211552043
    0xe010f0f081b0c06041406010308030411030307021f080c09031207020d0507030b0115020a1205091f1107080607020d050f090414160810120809040207060203071b02010c 74
    0x304000d440d0802e055031180e6140d441d100040720002014418141c00040c0740340543c3c490040445001c00124920351102c0e0207000c010b00c0d140f03040000c81d000c590380c641100001d10005041d01e1420989900044400b034030708401900030307400f04401e0307000c0300d801100b52948060f24192803440c00f601c1000082d120340240c80202c00f1050045008000d540302d007400045400e0f8400100c030b07070b4180c607030619105403c3c0900c220039982c101d40c400f0700c50441c40451b4030040710354044130b0b004004052170307000e0f6800d030840321119820080d998008401303d41141c042c0c01d00b007006038403030024859400301c085050903d10b40186609500c605d0900c10a680c0c001890032210ba420300d030040e00c802903003170f50f41e12502c904052b095000d403c003082200150810034803a80905806060480c00072a1100b0a4030409002c80c0c641c54885c2a4450800c510303110542e80608045c41408040c2c035007078004002800f01d809c84941554003590103c20407a8040c3c001c0302c000e804441e103940078a091034141d03000901c003100000d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 211554541 1250 211553291 211553297
    0x50106020c0d1b08030306100201020c070e0a091a060a0e0613051e0103030905040c081009150902070506010303080c03010b071707051c0311180409111008070e010f0f 73
    0x2d945414455101590000d600303c0c0c4211841d466a6103c985aa9800555043c0e11442168013144902401442204e103081103100c041d06d0031b10314243c000c41034600024600d0f034140341c407002e2500014003180c0300652403085035468000381c1e007010707010b10010f1141c0d6000f03944c0070100352003405032966a0000000403009040008141c5a803900561445507500b50010920003481200105c10150400140002e4030300a59080144000c054021240c82070103440d49252140c0b40002401410303440d8000a032550b117005049606e807982d0300313000e030101e84c408003064906420400042c0b00300341d40710f000950401090003000e81994104582c11100e8811484000d1103024030254418010300804207841d14150042c041e02e201d0f81c1007e100242c400246542c46000038070300030101d110311342c00005072184210b0403086024120031b40e000380001000c0380c4809561403090070302c03611116500c44011218404640d82c4842c25810a400e018100c41e12220320b0b02ccc1030112503540d451541e075000c0c41440b08102185 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 211555791 1250 211554541 211554559
    0x1a0c0a020c0d03030e0d210b100c020a080a0c08060906093c0a05010b030d0507060906180f0b130308040b1b03010605090a0801180f1103030a0908060a050106020c 71
    0xc0303800e6000b04500000c0001c5c2e0f0194561039464036030000982101c40924811041c0002002000300d000c50f45c2034445150b02c00c0d101c8500700100c4d485031900355842c6101602c56070075140c42da180c1e6803521111107411940708825800c00c2c2705075201480110780000140004080344e013045000395486440c4050f40243d0001c043c0ca4901406540c240680713620b0641680c28401d60484c1c18a030ba4561700350f1030060f06c075503081c80f000340118200003d00b5252001e1a9462500385030f20b07a6551405800218020b88000c7e440305e0f0385d00c2003146074076040300b5201e100303061a0302c0c0d100492800220743d504c010300d00032114040d441100b0100b90461400c80d0301a80c404045c1003956180b40b8209003401c0e5624880b121448007000106a00d074004004000302e502c121003220006540e0081c03a03080e01c00640c00e41c0c6403500e490303000500103003200920104040c420328100304e05038114008249550005103200e0009045d4540070011840180700c903c2d044180102c00784519030500e0000b941c1c486400c0038050185072a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 211557041 1250 211555791 211555793
    0x303060913050102090a061205060a060915020709110c0d0c150209011101050711120f180312190e040219080c16110a08070609060c1a041a0c0a020c0d 66
    0x390304445c8aa44018000d00d2016211103004000110440d403d800c03440c0f400001c00c0d80b900e400403480d000ca50040d543e00040d00c0c1485651000740600b04040001e5120701000400c12440500621190461070010301c2c0d148c450040102d85004038107030381a4240300b010640702c0042229a8404003240500301c40150f036512024004030391003d100c1651410952070b02c01401081c550005034804420080f000b02c5405030701c0c0074131000e114403130b507000498080f808124410b10907211801100044500030180c42c507860444500211a51000503e0f42088003541c500c81e40f11504074a88480552050794110f00b040b2481004807018003000b00c201c400d101072500001c002c660440c0c01c9850b0160361100c802304586542c40d2078030580303200440c028411030303098001041e20007000680d40c0c1120039039501c0c0d1030010b16004081da03400c00c1c500f009899080b120303556450301d043e407400c061f400303240301e0007480e40469000d01103076001050151000c403045004101740500c160f03000134005000342c82120b07074607803050381 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 211558291 1250 211557041 211557043
    0x30215040305150906010b040b0d33060f05030c0a080613020f0304060605100c0609080702040608030a1101360f0f050d080103030f051c15060908030306091305 70
    0x10320351004280788191200c20300510341401040340102c08640840f111030340c0f5055030364540d00441c020042c8a410034050f19040034029040103846081054402495030340750001d00b040c11864428a61008100201c00c20145911135200c40c8009210301d411415802d0400c1c8203113142c42441c04020810000307001240c65565036600c0c1c101c2d0080301c10303821565000c69102200c0160812642a60641e2504900260508043d00d080d1071481c51680e800c1d0a4116640c0e90700001c2400c064240e500240034010100140c440d481040c000d410400000c58448000c10170061600c0c503000028010382c0d05050003001c90b440c851000c8404000701381540d113110805100b4904a507502640c0103410000303109185410f22408204040d01c0d070b40942c0554180d0a204001994030500030b100040000b40c1a04c0b25140aa01c00e0b000740042ca221240c99445040d0071140c070000780c9800001c4001c140d50100402c10000f42c11140013002821160080d50961400c18001480c9500080c130b003454041d0004002410000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 211559541 1250 211558291 211558297
    0x901060903200a06020c010206090a02010e0d06090803190b100906030b0609040c0801030c2304050c0c07030302061806040c060309051501090b090114030606040b060d05010b03041208010f030215 85
    0x103040c4400f01c0383c0c0c81d000256500e078014102c2d8058003070340011800c60310001c18110b1000d501a141c080c00d48050320103010320001c0326881580c189580fa4101c0000800c1040154010369500c11266603d5038404041ea0445070341c0c115161289803403da0026800380c001c1440c80440394a4100099140b4851001c220184104c5c07002a510619114094403980c1e00031402034182c900480c0b00c05030301c5450f502c007650311078140100e07400ca40c003840b00c1c0b0324404d14068102a9000c06000c215038144151110391a1034811507030000c84c0560449010050070709821402c0d400207007031407002041e141c107043e01e03414500c0000340904020541c884440740144841049144400c1001590301b800b43c1d0781d07a2103c1e0300100304643e12540710300d4011000040d480c6102c00f410310b01c1da0f0000d02800d4661038001c1044020b14800c40081d0f00a0424800310b10060581e00c54507000b005280000b0f036882c64580b800802e1911403140a0061201c01070042c445103c1214411083c1c83d07054428441404040310228400c1c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 211560791 1250 211559541 211559603
    0x1507020c030a2114160c09050a0507111605040e0312070e010e04110a180f170105072a0203030f220503010209030c270c03090c0901060903 61
    0x1102e54208201000100300d14030240b030654900b40200d1141080c012210006001d40700f40070010140220701583c0000d24150050f24440d58600004070b6940c80b40c0825030b0f00c00c40f2161141c0759a1000c120748281c200311258002c3c0418005440c1c218010390000300d40c0c20050180234001c0e40d8500394070031000c0e8200b00b00d4100c8100e668144007940381c8094010001440c901e049400030b50350452920b100d04081c05040d03a80d0001c030349120b05110b5062000c0b1141303000c1040071035021030b40101c00180741e00390200e0000603107081c0c1401c04039842203000d454203540f40901000c0800c00382c032601090109031001c41403d0694100c1400d418030405000003441c42c0603141b000350755000005064801100800c0c1d180c0c1d4041400010007481590302c0d4205400c03401030791180d940540100e11060301d549020f00080c00c65070490744103001109101b0780040301c0502c003210720510441c030001c14864250001c00442c104480f045500045035030410000905218142c40010b00d1a02c2404d506010200303104200b4406d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 211562041 1250 211560791 211560793
    0x40306110d360c0915030c0f0f0506070206071202030f030106030b10020f0309010e12030708030613050402030a110d0f05160906081e0a0f110a080109051507020c03 72
    0x1d0042c6505845020200c40010070340e195240100441d2030b4a0100070050150b0406500546140390111080107443c2c500c00140906050701000710020b00101060350142041d1600050107504001010301c0c9610f45070465403041074144002c000684d6100e040f22070b10303039011011240e601d540c280107901d540604080a4520342d404800030460360b0741680954850030b402ca8184400704030a0201303a0f2952500b031490903550300f04000c640e1040d4003c1d61507504558001d0701c1c4031212590104500d00b1500a10700440c1c0f10700d40001440842c1c640486480c000302d07500c0c10104002c2c1400d60000e80e90715200d50b4014844401d03c8024021942c41034420329006030031000e5500c114620f0301c0e040b900c80f07a4014204440000103034020401040510580301aa04000700502c0c0c402090007950351011800c08580c0b03603922038943d501000400388000074054510468584545005107820413070a10410b0300640240d80c541055580441c1001424100303158010100714003d49881c0d42c124100004c100115801d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 211563291 1250 211562041 211562051
    0xe12090f0114040b0f090f0405060f011d030a050105010f081507120902060a020d14040e150a080f0715170402040b030309040e0a050c1203030c0c1e031903060605040306110d 76
    0x1482c0b0b1030000305521b030421a240e61610f107030b0904000c1103c909980f601e070041c4000030b407002254059403101c1031455140c180011b1980644000034600491480c0c200d0341079458800400069030030341013440290070688040e103e0301c680d4001d521046400140079000f000307640d29210300000050b902000740c0d140c02405207940e55a1a03440039540d0741d18090404e00145002d14240481002502500d0660307003544921005500c80c0111980c000700c1c07024510b07503c4901000c0014800c1800c020304170603a180c140c041c200072072401200c80d00c8803e680803c40103100600b0b030401c1007809444a6140d10a43c1118000385040382c0c480071a29501880c400c3c260050315042c044a802c51001036405c909510803130460b80e101c0e104100b0301c00c0070b0050030070300c1045078418400b26a00c545010050500d18001070110b650313256412055442500c00c00c804099150000511340f920b01411058100843c032060074103025461401e50010400c0c4500c2c0300107068642d4a204042000541c801160586d180d914010301c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 211564541 1250 211563291 211563307
    0xd0f230d0606052a1207021504080601060e0301090305030109021b102f2a0109080306100201140718050306041103060a050106210e0f010e12090f0114040b 68
    0x20742d42c08005203055050302c0d0820002ca8610030a14070002c0c0301000054040101003505c1540ca80d00613000803a070101010103901c3d01d140c4800050030007402d1280041100d5490058041c002150a41c3c0e44d500a0341025261008640c001c011a811140c0f4400b00507500d884410b0913035504501e0b50341c00340741c0340281048440c41241d80e1300800d100c481004190b2401030050100062100c062035200b444c6250240712141d800c081f101001d5141c640c000308070110090b90061254210350048104440c000d401005002e85401d00d0400c3c072103050310302e0008110040c061014100380c1400103219030304200105842c092010400040e460040ca40a400c4802c00d091a1411506103040b07a809a4064420350b00002d8003403c55000c3c0d58101d86041e11110341c6e4076105c800a0b490010595098040035499001da0080104100a8521040829000000d00501c61442c1c00d040150200c4d2070302195074140010200b40e56408843d0700815030900740000c0240403400100d1041c091544480c0c0e811a0100d4994 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 211565791 1250 211564541 211564547
    0x901030b130f0b1506070f0206130e070804110102010b031b12161a03010b031306060e04300816030e070810060504090b1308090d06020702030d0f230d0606 68
    0x14064140c56404c0c846494a41d400d00205014002c405040789200071030f01009420180e004021440718024400e03111030301d07000c6801302004241ca41d0400154020308010500c0340d4940d1203040c60307000748000c2c0035181030440000d658400c00c0c07003030460525450111460907580c040e0a5200b000208054643c01c0c0c58032218118100780612848404540188100780980b15807400c44c3d058404128215081d602d400c1002c14034582810360031140c40c3e64507600841c40f51105c1007a01c1c07050b8402e40740b0320b0b032450340d906000c41c00913181c010600402d400000c00240454106101540c01440071240b1160a090300801b100601034078604440140146c4402189801011643d0307400304515030b0091020039a69820b0000b02c5207041c0e40909400448804507080c1c2d80d000d65003880c044d00407184a800c109038074000411500041e00b0859500342d00164090840c02c061203101c0d1880240d06091848404100001d060128001036840c0c0c50310070b0791800c0da40154172a05580100c200f6050801030240c940e0406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 211567041 1250 211565791 211565813
    0x2030603030315271801020708030711070b03011202010e0415090b0f0406060206090d09050904030318080f0d1b08182401030b06030f030415020304030b0a0603150b0901030b130f 78
    0x4504442c1c000700e05c00b0030050085075a00350348a05524959a14920304481d100c2c0e035084510079a005034900050801c081c8005913020340802c01603c2c60350480b038400074100f0300302d02d610740d1701031403e01c0511040c0e0300341d801340d8104513000500003207080749440f400925668880204a0b45c010710b8100086417160f4009405403083e0b00040c2110006502880c003a5100c64451298950010f20340002800081c46030304249482035410390050018000c075a103a0302c2c2e030b41000403444540b440104181c0501d1a690140714041c6481c0203851141003d1107100404040f0000c03d205079141380c2249400c00d0305e508000058800003c024001194500200040c203141030178402580c07041c6c01c58010840324600481c04c00b00d5441c0910080d413609107440103480103028800c0c5090258002844000003142501240e03900c104901000001c002c0d04602d0804503402c1ca0300d03401400d091501c0d44c01038007511606000b41c19250056002d10243d40c0307000501e10034100c6030100600908401c8442c1c0f040100001030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 211568291 1250 211567041 211567051
    0x309050d0e030d0f0519051e04080c0d0c0e011d06042a0e0301050a0e19030509090402040209030109030206041e0b0c1b0304060207180203060303031527 67
    0x654011001004003190600034901e00745a060300044011800203001e040050312000f00b504107981840c1031000c0480980070680c4014020440c00038682e12090095000d8601c1d040125001c3c50a042c1408956507940b1440e0181034068509281540d042c402c001680000604010710340108968441002c4c0b0b0402031071f5503840345412440c8011503800e1030240640e014101c0c45401c202c0321138514031880000041c1c00c04160341403001e060a410b00303a0b00d080c0241440741030700c0140440c0603403142c5029843c01524510700c40d03036100c440c504000007030313401000c9900c040c47c1210000c1994940b800042c0c002d226008940c4d9066103001200c204054011034140e10803401903401c03080c8460345403048000c0340c02032a002004401c0300c0c00002c011082090107000000c2d40069814942d0344691096032841d40f0540000c005030f031000700b0810a003014900301d81041020701c0ba05604606012001c83d54900000d040104c1160002c0419083c030344075032050019403441500107913040703140c440b10480854406d0b9a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 211569541 1250 211568291 211568293
    0x100503060c0405011d01020327040c11100608030706020f0d061706010f060c080c0109020303122410050702010e040614181e281415030705060a05090907030905 70
    0x401e05d80c864040103001c0f054010b1f00910321f0403040d401444a1001c4403c1d601355025403c00d082a0251524482c2003240030150300c5030344021800c1e1030413034034014001d1400c00c100340c1048002d0203c6d0801000f520122544500f01588602044030bc801203406603074801c0391032500d00f400001e60304601141e800d40040840342074442d281d80b070300d0740014211924010321001c00c242205150000703030100010080040d07501c00000d0442c1180c4d0010b030455024004030b203050074030314081c480c41e03c1140c10001003d480d4018402e000300900030214600502110b642818000042135140170f59025a90314039840d0401801004110b80344c1c4201c2140743c281500070740c0161340d00d8465000e0441e6004040d40100c000b01700c41c149540ca00705a220044c0c20052407007200c040308064007408910010200140b081000d10b000c2000c0f4240d01c200390600c41d000b8071402580e618140c0221082d100801d1540590314240c402d20385c0c1d003c1c40102a6010721030301c6920b640100d512820400c4541c0d01d0b50020020504c284 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 211570791 1250 211569541 211569557
    0x4050a12140f0a030b010822050c03061f12170d0b0405040c060e1c0206130806090616020613060b03010207080c0105070806062503141908010b0f0306040203100503060c040501 77
    0x10b4011a1f002e102182c8000c800440340660798602170f0841e00b5610702e81e2080c000c5070045585100481e04281c001e45103111600b540003032400c1d02402401c2c0314009802d070303c40c644441d43e0094440c403800c3c04441814004034440050711f0185401c4540111581d50380c040d20601c010b0520b454803d103140b2141c41010002038449405006500e401010000c1502082c40030f04016880c540800c6129440402040501811840d00050492050000070b10880c0118043c010501c1d0003500140303840c000000c1002150031107420006074100075164403428642005000918a00380c0022a009104d074800c00382a641020800800342d40d0305400461007074585581c0c0c10950f031150701c1886800e005401125018480f881402801140c040304803400309806890042d401d15040f201504270303540a24641c0039032074100c50809030110342040740d480c01000d0541d00c161500000c00100207180c04090324441c401c03500000402e91002002c102c071000340600800f60388007420301300a440354035070207071141501250080d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 211572041 1250 211570791 211570811
    0x3041e0b0a2301140409020d06020d15081009030201200d0b010206131106040f091b02030a02190206070b010b0d060803090f010318080a0203120f04050a12140f0a03 72
    0xc0c0e800d01010090803200d030701e0b060b401e1002c000b251000e01184550000e641e0036034500076030b546c030750b0104103140941d00c0140d840310b203080c410040c1c03407448552007000604039404004100c00010180c400c03d281d0000040c0e041c13080d1500b280074100000b8280d01d03400622034980d6070790520400806202d5500c82080200b2000356005a8503600c0c100d030703042013560300e0b483c1080201d0340120f038090450724010240781c903180e150800c4070b0340c1c420290002c500ca244c1d9219010080300c00008210303588050350004500303284814070b00030341c2d560b404400e01440ca294002c0300c10440d1605015a0302c01ca504c03144403030166131115640c3c0c940b90032548102030407038100a000a8094004402c41d03020050144c50b0385483c801c14001075004d080c51030032a44ae02d100244034440410001805000d03100040d5000d1a41c0303400d1580005030038480540ac003000c81c00c9040500001443c0080c02c1442d255110300851140d01e019541030380c4603610b060314080755880000c0e00c034840d00491401081000c103d07071410050844c1c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 211573291 1250 211572041 211572071
    0xb0d1401051020030d091a0714030606070501110d0c0206071815050c0a06151d0a0506121501032102061f0b0d050f010b070b0103020603041e0b0a 64
    0xc85450702d03021a1100010074004210755103400314241e0f404080700d280403405040c11046901032170054a22180404007000301e68081c0c02e540e80c1061a41c0340c00903640c0d1716003501c290035200107007686200e6580054403000304842908004c00c0a40b028803980d0316600c070003040380054000e4a0142e00140640e038001891940650701d80c40a41c0c0d01e6608240d10a03040076011402e0b118049041d41c203004092125a00c030107000c029005406102d240085903420040543d00c02209003500310300000881028040806001005c0c103561141c42907a02080c540c40300030205180d401c09944e0280e0b1070094034146244081c640c0c294504030f0b4410b201c1140d565004421080701a014039480d00d005811070350201d9224100003107000507101122096400d0690303a5407071081e0950021031800c155039110300810054100c083c3c03445005220040003180b5000007907460350080041400024400c84011010400380300c09640e290101c0d0350b02c0d80400ca9422034609005514034011560103072860301f031600040c50948 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 211574541 1250 211573291 211573309
    0x6100e010f0b0306240304150608010c051204030309020a0e0f0115021507110a030e030c0a06140a09050d320712080c01020a0518060f070308100b0d140105 68
    0x1c030242002d401d41e100d440c10001c503200107070401e08403026254aa1019064020000c41c0940d01c03400c0780a8440c44000c4640c002e561103a8080c154907494041e070525107581000464246034840303800100b00d5a5545401e030020251404080d40012040e880030850003540310402c2e001c0d0000701404944d50ba41c03540d440b03d2030000300c8103010060300a89541c0040769002e0014070307004115814000c0040010800081c68400c00f99400e03000100c22228109803410b043c0026110ba50080e21000c2c0050308010011340602c0305002501c40d41880081c2c14800144169207413409004020a4007614055505010000c850345800c0c40102400d01c403444040340c1760900b915905024003a0244c01d1031071410705004201031811400751044c070310400040e442440d0a100500320081c0b2a03c810340c80c0d00e0791140c40d85840d4165404140603000801c090307427508020380c0a55003495810b14040441c1c0e0b60304028400044113507400201281c901180c8012410301c140c0100d2210148202d202d8070303a0b0b0340c80d010002141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 211575791 1250 211574541 211574549
    0xb04030c050607051519050c03010e010b180a0e01081b0a2907030c0312020705030d0903110f030405010311120103020d0309170312011e141206100e010f 67
    0x4640c01000708420b00381140039044480c06081070b500100700d020151102040d045544800c181c201005c061015031482c0b00b4250801c00100d142c0c0d007198144031102c207840e9018045e606000901149070450321031410301c14080000c0140ca40c50b9500d50300c01c4c204001c0da50038028006240185001034440d17111901c40a0f000b280010b00003800b1502d0b280c11a584070b20002d5240c1882283c1c180e80c90340f40840d10004001851117944c071030602c000c2d0740c24014a40441d00750120240d6004101510100c0c0e000020346040c2003c041002aa0416514083d0b0b1001036081401d032140c05000042c16107214003002501c210380c0c0a072804d000060728a06c450066218005c07051200201c04001400942088400e00341c40300d100e400d05074546921020b481c04070500070b40489406074000194407200c9138680c1000750051003418001c801c80742e01c42d204100302008901500f0700d4980241e505826955a08003040c600d51800d40965006092000c03100390421458020007500041e21000040d51040d1060300304112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 211577041 1250 211575791 211575803
    0xb0a05040f0603020a030c060905090708060108070e0306040c060810080a08031509010b0304110609011d0102121803071a0d05100312080405070f0602030d0f0e03031f0b0403 76
    0x64205000c010060016018448407180c1e9100e0100068952090210145008424202500e4074120009009100c0361b0861409801950184501a5003042d0381540003502400d119000e070391511b00441d0f40304040d11901d0340c144684424402480603d81800084ea81266124411a901e4030150f90442d1418400c0c0b941c550b00110310800401c0d00c50020f10f40062802d24503a14482c0d40d0000501c207010700307800625400000005100412009800745a09040d00b51019800d00c80350360000f0300040c48100e01c5e501c54040f5184081440e030310030311160038001030704c01c20325488038201a2217040d42c00318400d078175010380f007413084c04280b90708603144100030141c200303039010b10b4065140140e001410780980707442c0307212860001c04000104039000b80c288110700c1e079407115454500f40c200b9030f141204a60010300440e11461041c022076a0210407110712165401e0041189002e0105000c028503000c02c848441d404040306001c14007100f03200c84507800740c4a0102c2e6007210313155105020184200d2000401d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 211578291 1250 211577041 211577059
    0x1505070503040c0b040f0e0603070305010207211d09090a21172707031a15090903040909050a1a10140a03111305182413050f0304030308070908010b 65
    0x40080a517020390348c00390019080c1c07036050307030b50703030307100c500b03a030000e15007122030201c00c4c99403070005600c3c03459000c403544903032515800d600e10400c04990301d0040f09001b00c0c06402c6510004044903410400d55051a40c0f01d40d61040d000409440c50641c26620320580c00060070001602c2c542d29000b40c212405030715400781000b03440d41c01c40c0c007071110850448820003c0b406404400000314101904120101300304141c22aa1454401300c1d441010382800c180c02d01c1902030006102581c0000010741e010340d03506040008a01d00c80341041d071b2400801d11001003000050000c0000310800740b80907913021b4002c0d001d500c0d41d91529201d48040300c098510701c1d1600102d15000800c040b0700402070036282400054042c84c80c1403840c9080d0000d40318121042183d030503d0f4180c09940301810003011110a01d091190b501d01400040326000c0020f002d4041d0f0106e2000220460a0141c244010445520400d00b00e079601c940e28a0003030001c030421103a54022902003640052404410b002d5250000c40c000d0507022 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 211579541 1250 211578291 211578299
    0xc0603040b1303020f0709060f060c0f03210501091b1106060904030c0506091b010c020102060c0c12070b0609060a030f02010f030b06040b07020a05040b01050f071505070503040c0b040f 81
    0x2680705140d02c0207034110300c9102004003c015081c421040981051600410903030b08092840f041d02645030b0200c800c214464800c03001048070011880112607144c5400140417260b403507440c1c0c07543c01e0003c0e01506545403100005104003550f02c101d4000c80400d8681100244010064604140c5044c4810941d0000e0000400724036103c080140c1c4184030b0700308604100c0c0d030354551901d0490300300c0d480d038038a6200d6901c2d28000001d20301880c80480092130b10410520003680000d40b1800b01900d10a60301002050341c0ca840070044c80780601c000c20041c00e032900d0341000d041c200c001d020700303980c454018028500420640c0c02c10490310816203402a942203900d0030658011503030031000084920415594094064942da90075004000800710800c2590f00d50100f070040081e103a4035984058400d07481c01100781c149036088002c2da83c44c7c42c0a01f0781c40e0345030744460800c025142440311401142c3d0345410104011190032102540c011070048403d0150300c1c0d2070300b101602c04d00c19401410046090030000b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 211580791 1250 211579541 211579561
    0xf0f0504181e0302100609090b09010c050d0b211b0a0e060f1305010f0914060f13020702060a0c150905031804090b01030605160201060b0a030225140c0603040b 70
    0xa03185031203031040302c3ea480c20000c5c80c207048943c15006440030544401c650028802c003940d98030380082910000300541c115803075014089115401200f082e00b0303200c009101c2e031075440c0917401d60760b100d511880403000d1046150950701c0e10500005052200d0044914040c10f0400c0c18200c425180303180741d2804962145010450155403003192507502c01a40d180307144e40d04016014250082500201ca1020381c0c0c00c212001c2c0c26100d6070070880c018600c403801040416524004036a10a03001512202c940511055910001e4816440081d4019330006448550f6561010b502002c550180340d04036101d44407081650182d03852a40d01903c15441803114001051001060220f100801400001e115015641c1e081c0400d10990080da10281c0c4c0d45e082003424802e0314401d02c03100c88248000c0200c14103200d0765810a00070342091000300760340458100e0024100c800c0108031403002101750364200504e454182600748a902e1014a10700070b290302d001c01c0d41001e00030b40307004035406090400395598060640c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 211582041 1250 211580791 211580843
    0x3040501031a031515040504020a0515070501050f01060906020a020f010305090c130b01020c0121050403110f070302040c0e0d06050a0615050301080607050a120b0105040f0f050418 79
    0x155162002c4100000c807995802c20655080c1c10b1690040c881a00d0458218200301400c0782d00680114104410800140d56805c0700100752a400c81e0300c2d00c01500414100541e500071040010501d41c40e01041c0620b885980341110304a819035500e0240c079988820089880e010780345070003500081114040c2c0702d958000c0c1c004507800310750b030001c8800080d07261002641580c100000041e45694072500300001d564180607400c0c00001c2800c1845007100d8107909040380350406484050056130f9003000c20304252180c41c209000c03034122000c5a104242d00c002c030540b140b80f5444100d124503d44010200141e000302c0e0b03004120040244184091401d5072159006407030010085098180e039054045181300700c0c60400140710600340e0b110b50700c035030401c44010b18104001d0020700134803009005101450340c0c060920401190418804125240e4100041e10180102d81000d03485151203180400c4c0200700041d401e0450320212024003d800c0340300d00c05403d1a440040c007805030507880c40180c0916011850b6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 211583291 1250 211582041 211582061
    0xc120b07110c0d08070c050f010507030f030207020a08060711010605030a08220308030f06040515040c3f06030302120a0203040e100503010e010515010e0604080a051501170304050103 80
    0x10340d40340d68600400940084000e103c1100d901e140410b4160a200440b8844400f50a0a6641005041c54200060103902071680018100160700c030800e42014807a070150b035085503000c0e02105400343c075007041c6034441300111850f00000d0b90812003148800c00500030382c41154405000780180e042c550319200c1459000811400801c00c842801d209120b2103405024000c600441440d074903801d01000c1e26044640113041c091086040a081c8000304143e8403000401c2201100c0001e210601c2e102d0a4607082c2503690700940c8104115071907102d4400054400c40030381d86001c004880c40881c020b80c2d100b222003d003c040c0c0181c1c0441c60040701c1a2407280144450301d40350044134113003642d55049490803076003110a500c4002c0651720400c103a007024041e01c40b038400110020f11152404c11006c4003a0101491182d0410030904443d110b19207841045801400044050352000602c03810003554800c405124941411000000050060f00401c45400002c525801861030035103441c00460180601440d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 211584541 1250 211583291 211583293
    0x140106090b0f130609050a0f050312070510050703020c0c22151502150901051b0f0408100b0f0315070315051206041118042901030308040c120b0711 65
    0x1010f00c02911801c003481c8018860740d9508074285003060280702060882d07500c041011040008288110364000c0750314162202e5181c81c9a807502d0f0382e81480b0307150801541c8017114031403401061102040e03160b0001d050300e0402c14115072a01880001b8816025150072011902182502441d0882c0c152900a642020f0f0840401c0303581c0e0fa145c0c500181902074001c00315000d030f40411940035420800707040f520791044405000300300740c1c40c151781c0010500303440d000e200c112844001740004065140b28203440c00b81209200300c41000c40c032410f01800402e0603e000500c50700600c15003600525001a4943c40c1181440c030051080d143d104090300645640e80710f0019a81045501141e5074440d50360f030141d098458001030080b8205420030203c8410044141030180001e1a00000b503146041c0c0419045039004510710900a034040d81510196041e0012091550a91000006040d8400c0301240a14000c8035110401a07540e50700c004440c1150300000c040403400700000354081d025034028280e80110b20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 211585791 1250 211584541 211584547
    0x9090e0c0d02090403020f19031e080417040f0603060311060a021f1b020a0b10050d0b041a1602060109020901081501020a020310290a151206030602030703140106090b0f 74
    0x880505021080240c40d02e23058050844100345032780a05421120700350703140c1c0f02000d0081d140000b40070150040026100308400b020154003049898221401019500d0640c0c0d0255103491009000e4107030f0f840700765a00d82d007056901c501458060210b8480d003020380c00415001c6000707060099841005070241e020740d95582440414210030b801106030720200341e03002d40790360748203460603024640c0050212a4050f1030b2200c280120348800c00907003d1290401410103039541c80e450010301c0841c26111035080c5180c50350600c1004214110002e450341c02d203409948880c0e07240d207801c60482c01405400c41c00649010040b8400124144194803405010b1041c0c07030180320282c010038580710030394506540c6144c4d554190b40810042104412107000188282181c020a99000132a5000c5078010040200044218074071894084d441d44496140f4041e0148071241d5a414224000c0d00115821004641040180090080901d001505980150f29101c44280c20804028010342101c001803411182c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 211587041 1250 211585791 211585813
    0x14010f020a03020322080a030e0718020712031404020402070201030b030f0304090e060402030307140a15050703050711070e0c09030733170a0609020a09090e0c0d0209040302 76
    0x90009040d11030280c0c03000769507814844405c9186240000301004810802c0540000040a44e400c0b81c880720080c0c5004144d21201020080c01c00d14684d2004860151002c0c400c2c007225a1500500201405100201c5801005140c00d80603900c080140030f00c5008100006070040c6003d6019091590040c500002d00d1100c2d400880d1400c40480c1120780b180d840802c0400540c07113540141522021098041c11803030800d5404650340f40990310700100b103071820041c07000710b44504100060301c964200030289520a2024103410040c00705071008000641410f0005a01e14000c1e000e42a07444205001022003518100402500500182c0a81d031258804c01100500360340820418001e0114101201480a07402d441d01845c1c4480408802c0116103917036584107495008008121b07000c2702d01c2c000401c9580c81021400c0109040d03005040300300c1c404070b40441c500382d0000902d03098440a0704100172081080248944c1d075004490310303941c41404070224100609000d21540d4005109004850540c1e00c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 211588291 1250 211587041 211587071
    0x10c1505042303071104091707030908070b090d030804110d061e090201170601021006080c0907020102040b0d0b0d050f0a110d1112070f09020a180609031401 69
    0x4140c90030340d01d00050b04490350540064051081c082841c002c000c500d8820540e60341c803101d498150036944140d940300d06801c24822001506240c00b440319604596170313112868090310443c0b07a801b030030b00c16211700b450202c3c10070304c51411510034007401841d2440750302442d501150b1411009004845030303a500030f6508800d07220720b003040c554140b1400000c00c603030318980c880902100c01c04259800a03030908041002503608020081214406900300e00306956031600103034a006080361b0340d400e006181400c0010032050200e03050a4100e001c503502104c540b66003c0407400e038012401f54024100f0100300381c01040b80741d40c0c001c0c0c11080015007864040c000170345a0504000c1d00e8500b060040c1c000f401c0c940c0c10007170807424801c001c400440700c144c007882c4240c54409c07070a0700000005000e4080a50803030b1000c0400c00420380103042c01c004604070a9169401400a908010100004240d02d2061206040301d0f40010b441075070501d5581c3c5521074516210515002007051030071341c440d542d5041e12506001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 211589541 1250 211588291 211588301
    0x2107060e0f03090102100203010e0c0d090b040602040510080f16030908040e0417070c0302130e0d11070e0f06010c020a080106030c030b010503010e07030602090609191d0c09010c15 79
    0x80701440e1038090540000e803c2c40c420020a1400e103104000520614500c2d40c00540c0003030f49a508951280c50341051140200071520020f17100068450801c4100300c11a0002e2043c0c85060720f014803103000c1600243c03050b02e03042d61255025515200010b030803400d02034001542d1107a80c58081071285050720f54120660080e004521103070b40c0141040203204818a00b80d8604235000c200034030342034160f243c4a20b40c03900da00000707208855426190120703106a4100004401642003a11442401c0d00c0c8040d040d0700c18104411914050340c00c0c00a285580700c075816218110030244040c0c41c2c1d849900441e0814106141280c1c05000b03404003041c1d1900034401c45c40518441c0c101c0300080d44c2182007614140005a100c01d10981c1018000c482008000c15540202c03a8042c00260b100c0b00b02c0030004650703006907071003a40c010070326030230f006456812500c5543c211504053b032030803410641001454861401c03200417001010411201c4280d5106000c41560503000b44100000501440c02e00f41c1519 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 211590791 1250 211589541 211589563
    0xf04051f150e1207030809061c050403020f010c02060f09160902040513020f07021e12070905090705030727020a0e03010c02010614090604020405180a06082107060e 72
    0x140090345590840e00a152070110341c200711000e108044030744070125030344e1084d40001011060081000200e60f20747c0760a80300354860007540016061201d0340b1642c005c040c01c4034107600502c5a20790913468201c041c46446801d503042c0d805898a07580b0403903078038100c08025201003d1440390503281c01d42d03a00f40d10741e41d8001c3c10000001598452402e000c02070340e01d0b5041c00009485104206100310f10303e080007200d0049506031407480019501e448000803d00703012143e44d401200242200ca0b0080000c5010015520481c2e03007040b6503210a20090340e03c58460007501d816a0202130300b44030031580450080740c040400e102c86408440300c948031030213030380001e5802c2001c291207040d803110740d2501707014400400115100821403a454015921840e040052000d40254415030100780d290f162501210302a0a018106802028000000740503004040b0340c0d01030300343c1ca044030100741c881e0702251826020003440f540720082d01c95018140c44a90010604507469039a500724500009010300160081c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 211592041 1250 211590791 211590809
    0x18110f0d030206010609080c130b01090b0f0d1808040b1804090303050402010e010c030f0f030f060b0301030311010603020d0303052a0a0215011206090f0b0a0207110d020f04051f 78
    0x4c0d4509000502003041a4100c080660840e61090751710303440710b03400f00d190881c0c140300100d803950002005a072403a410b0780214031100b000062008014103010010400c0f0f12413030804002c21940c940c024121740b1810703140104102020030007000740c8115140a0118594400380318000007400e00009000c6420102d1b0880c04252514100401c0d0341e0003080d240c50010082c20903e01d50307271007503900400381c104110251042c40840030344c02c0c3c0349510a030311118400203000400c1090039142c803d9030358103801c24401140001d900300030b035050483d010300603c411664080c2c01a180d40e0025a820b601403d4010326a4222150030712490f46040411a01580b080e001d00701c070740d9620001440001d0400454054001790450300c5d8004000b0003100343c80c0c071030f5174070380080700003402030701d146403509600008040141c0300d003840340180070b0085841d0b030040c003003a071084001f000d46101120901480101044010b075001200010104003401c007504203990007888040c1c501820791600203c0382c1000200d0300f102c580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 211593291 1250 211592041 211592053
    0x50d241505100804020f190308070503031008030a0e0f06070818040c030608061303051909140a080615030708010e061f080a031d0901140108010918110f0d0302 70
    0x1282484070380a001d100451400f18503c0c40d0580104070b40c0c145441099001c0d104594000c9061385404d00080003460303001881c0359880090b4248165030b90015910301c69400009000068032030302c000200d911f5440140c885881800c5407400300464000c10005283d0800d20800156000031654001405950035140400b11129403003801e020848110015503000c2c1072074400144081640051980e40c84204400c10407409101c0d032030121820b006840a403010b424029004d500078035007108060040d00c8089000c0483c800c000c2c0c0030021812020b225007655034000302c0100300c5c0307084054181c00d4810030240807100d0041d503c01d03c603400c6501d0030b050320009802013420310541c0c448240d00094072400d0001480c00803401d04140b580c03903540e0010020f050140d0101064021001d8418881c00b150340240700c41d24540c1d6401c6244441d48092103107500242d1581d002094400f00fa1141c2c600508a800000712003541c50780d9140c0c0801c50b40226994402007105032102e00744c0e42c070050203601e9032095020f810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 211594541 1250 211593291 211593299
    0xa0903020a09020a0314060f06030408160309140301141920040e0907150503191d01051008100902010909050a0212100311010c0201030e07030308100609050d2415 71
    0x8101d4071b0341d6100c0044042d08034140581542c804c107052000d075030100c402c10fa80343c40c1d074034200c0910701c5260a4541903540f43c004240516810810203021904900b2212241c0c2491070109400c0722400c403094844003c61801081c5420010360a0009141c909880000c480f01c810982c0f02030204200301c0e4000308000010b0500141e00c55101c025000401640200b141c1c504140068103824007451140c2c082000210000300020f00071148100001024201001358001155400c01e4102109000c65515801c01000c148802a50f003078680c1240d1020014040f5001249500c03005428040801c0e810025401404506a1154400d241c0641b01c0840010303900ca40c804001016041c0092622508205040c01000400c0303a0340c02e641304012091030702240100003840103031b00402e6442c030035045074410b80000cc820150840807031400341c070091000064141e0755400c03c448006450182940140600c200440042c5256440d000e032061100810211001c06043c01000c0f169001c00c8a00c2080d90504100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 211595791 1250 211594541 211594547
    0x207121e02030c15130b0909072a060506010e01170c090103060803130f1203020304121403030403020a0302010e071d0c12070e0f1e100201020405030a0501050108070b03040b0103080a0903020a09020a 87
    0x3c2c00e060440314202410351f800502203d10041c80041030010240071403041d41e04070324424906041c943c0b4038844400103410700314002d00701100c089011a682441d840391a40c013440205d04103000d51001c110300c07552200180700d000d420882249050580b15440482c0303908007840030700140c0b118a502d80d00460300c2c1c4020001c03180c020b03074402a40c0c407001c600b490000c2a40801260207070303810900f1154142e4a64a0b0080c0a801e00841c8402c50380008000c2c0010036074081460014640a0f0340203110311a03081132520746514071403003903a001e000080042503e6120341d0800d142c0c004140810070f420840404180100403400302c45513000070b4441580c0d48801d02d00710301c103c3d01411041d604080180b40c0d0162680324600307211070780352141100e0300c1000c44192003501150060807001d02640c907590450301e0268080c040a002e031203d140107000000c98041c11032001e5900c600c0e00204480e8007646192142d0020f540a50100c0e0200305c0089008805611600d00f20710040040c2000140d85511007a070003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 211597041 1250 211595791 211595827
    0x3162108040b07031401090207020109030f061d0304050f0409080903010c0f0201061514131a07060e0606100507110306010b0705010c0e01120c17090c010207121e02030c15 75
    0x3c00241490055501c03401d101c1e02c5440c505442e0b040e9401a6509140d000580d03030081d4a41c00146070003030304100c04007000500d422039168409080441c81800d582400c01075281d00a0f030007201d4108801c2240c0800d030785003a1700a074525600446545152107901c0c0c2c0442c1c00e48102440407070105040364030510035554244281002800c82c3d60f4a10701002c006d00c401090140c4141a0300c20145002c2a000e0300024040d881c0e60040c042d240e020350400c150224900e503603810405040d282a0326100300b40d403580c10301103509881030a00500030304010382044800c0c0c8054000910580c0c03181890203038414991020000f4034043d1051801340c544581c000d10b425825a9280d0000c04200140c0326400200d40e60000c00b5200b200128803000704000402e580e007100c4855011003540050107200c0c05208410102080e441030031030003a0300f5222041c1d242d0031000300c1c1c0d4140d558010703c0e5041c0c1c04031060801d88000ca1640d4010b1000f400d4842c2034802000241007003801d0411103145110005140d0241c0c2c010b2140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 211598291 1250 211597041 211597051
    0x140a20070320191106190e100203070510050c12040f1203091a0a0e1c020c030d1b0201090509040b0108071406040306020309010e030a0e09010b0403020303162108040b 73
    0x780714800481c64042d210301d5030301c43c0003040aa0403000c4588140e03038003020741c0c0c43c8071009168407400b00f101c0714005203e1041003122034010460115500b050030b02c08802ca414807038001c001800000d5162544500408001308080c070160014080340c0003212a480c00680202e000703400002a22401b4281102545080c076240e0041c1858580d42c44005005008103900c00003410550f07180b555907000c0b050000d0110300d04d04c010036006050080c03c001c0c2c00c0f03225200b0006295030031524030055000c1496070760b2880c035804c7c9011400700d200038000840303840c040f51103035071040c9044440b09940d000481c05058054808650410007080140404141004030400a002c0d00840540b180c0a240104496101b1400040c000d90b400100040e6510001d40026205181d500c007101e5881c030102da4010304282907050840e225159070000010a81007401c280e030107982e0000e000c1c610748010044090b0403001da1400c00c03940b103012084031a134a800352600c403d484682d1071700e0f05000d9240a14000d1800140204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 211599541 1250 211598291 211598293
    0xe0d03150f05090f10080a052409030706020f2a0c01050a050a0c0f080406120c030902060904020307022e0b12071a13090c0e0301140a20070320 63
    0x1200300304658821801581080c01c001541e441500c655076441c1c80700e11705806c400071520030001d0503000c11000045c25030130450858180c04202c1800c0001c0600b00a040e140c50b1032a03401070102e040403540e641c0c0104850203a12002610b00102c4034000301061601850301100c00e08403044410f8000011b10150100d1002460302628240800e18041d00b03600450032a001000890713600702041000c03104861000c2070b0081020342c4c583d551003400501d42200220002680b03810710b81c0302c0180a020780203000001382d00802c1541030082107002e2100a401c01000c410131481014103040785902d032203003180d04140784091040c03010150b1140312016100603041250180003c0c115000c14000040707940000c0d25181c2c0f001003400c00b03001c2124001c3d40244c8980b41d019502001002426a24541c0008000032640c0c0302c420410b000d0074101070880718108050101c1c055003000080c08640968407041f08440d0101c07492503100780083d4400fa694105007811000f00b00e00720000414500c61112002d60030003484 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 211600791 1250 211599541 211599569
    0x9060b03010602011b08150a091a0a06030501030203120a0509120c0102070803251403120f070e10032706020d050c03010b090f0609030f0a1209030305031602010e0d0315 74
    0x5c07500030300400e0300074a9407002c17505080380f1400a685010705100289042e103001e2203080351101c0380605240d01c01ca1454401c07012182c0000e4407030f009003e040e040f03d4004000d01402041103d40c2d5150364410b141050420000300304800c410340e5650072120400150134003c11001d51043c00291800170141c2002c8034591003840455040f0314080602002e61044030b0300f000c1094600e203400700488201c0101d80e0518080072546144044007000300c10b2140140d07815100e0140c40348203090311720f01040d02903aa084010102245207090003038101c1d07502d52030741c5180c4c204d80e103a0310100001000f074951070442d5116000030b52440c1d6050940290380d000401d1344912843c41d4074007641201c0300c0c4509a990360150120b0009503c095443e803060301c0000b0400750a48446407110102180c0b520310451045410350340484c400c00b0010322602030b080582e03916859462458441d031410300721192460034000c00710364071210825030303400040c84450344081050b01c0218400b604054004094509900b0070302824507e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 211602041 1250 211600791 211600841
    0x906050a0b0d0209030307060f0b060f07200d051c0906020712240516050901020a1103100c1701120c030204090614090a02030c090601020a080f0409060b0301060201 72
    0x9816401101c0c00440307140d5480d016001c0c00000380c0109104642d040c00041104418030130355070011401c0c07201e12403080100050750790410503140a44d00002950b2407042c00900700007103803000c03000a44070700b4001c08201d2681000c0080c600a0100c0001c44098002048124800c0c0c0c4040040000035101d0800c07034440f60a0030b000039070341c0b0503500c1101496181c03a000c160a0080081c01c01ca01d440140c80b201408030100c2403a500030b4001954184500f14940e001142c82500c14801e80d02140c2c4142c1c003030240c1c04501d848001250420307104183c0e05009034020501c0e07500d05441442c1d900d54a075260300b5100c90411840e1141140305074010002088884480400100102c41c1d400070b50b40e049800145000c50341c1030031002400200c10500c4695403000074480428030005120050078402c40848131101d118030107120241800b61034103805607000c1820480080c02ca58080e10f0f081c4184442641003540c3d412400c42502e41a0b44180d1000c40c0000c01480300307560a00480048d024402030300010140030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 211603291 1250 211602041 211602049
    0x150911070308100902071202060915060f04020f0c010b12190b090a12031a011713150f0504020a0e150103020901020102120108070e13030c0f030e0301050702060108010501090605 78
    0x2038080001c0c2003008400c0012505582c501200c00540b000903401c40d1100003a15003400100036005030b00016100300c0c000a01d5841c80003d02420000c001c03000c40040780c41e21002d1000d441050f03c143d07071340540c084c080310385107260100181032290000da0012951881743e0082c0040c0481083d10340080e60032410b001c0341c0d04041c9070640710002d94807181e8107070681d5039a0905801c0003140a401030940c40c11203005561a545030b0000c0000c8900b10700b03080d8a5100c003c0c019600020545030f842d03103407181d540c0040c10200040000902403801a001ea460940008503150100c0c0c000a81d00c00302c00d83d540f42484190304200c0601800390240c90512130642c01d03c0c40050301310074080007150b4101a0005400c90241e4401e4041c1c0314036150211001b03000f540c540715040d0b15000c1034002e80712140071080c002100c0b90500c03104440d0040c0c054666014144041c4c41d94420222280170a4092040704075174800340b030304c09120300c078030441c401da0107082c40f035050503202400c2da903040c3d1021080f541845018451691 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 211604541 1250 211603291 211603297
    0x5040906021e120c131509080601090917130509180706050f070204112b0c03091707030c080309060610020d0f080415060e1b1303080d0902090109150911 67
    0x300500d10301da211700d5046268030004c00c50350002d00024603604a403c60b121713080303c8078105450950303080c0d910766070326072050608441c5c0040c07001d850116604140c1d2a40e003800390043c01d020040d10024989e00e51160080b5203c144182c0d0340c03040e40800c54126500c035003014014200075100703d240035807030301c120400422920f0048001c003034403541d560721401480840080c100d410541888800c080101079640041c18411500c480c81c8031100e0622403003607c5140f09201c0e09800c1640503042c0d0140ba460010300310f0302a00040c804034180105c1419210224011300003540c4034504c030100400852400e407003442888a402e4556609652000141c60070840e004a050f1920158901c0d0001e560355803800c060b036502c1443c0010705581441c1c8a004114244008506c40c03040c154a821401c080004d81e03071108603489103201718081480e03840b0090002812034801046001c2403072002107201c00c181d8000a0318610280d000380034440d80c60740c0040f078003008070800c00c00a00c0304190420458810108441c0c0d10704c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 211605791 1250 211604541 211604551
    0x6030c01090302061804110c010b0303040506030408130b0409050a0b011409011b0605090c031c090911070b1501030e0f060c090105070f030e011218060c02030405040906021e12 77
    0x1001040b02c017180719000503143e0340b08600030014444c0d08400d00d8603100651181000030419428000d0942c00c0b420f00101301d8003242c01c003800e000e141d5921500c65002e5500320030642401c0e0170354034800007000154003014101600285100090720300b40700d03140d00708a07822002014144216407104201010081d000e6a507164400e082c1403030680d11401b0f1110604c440f03550f0040c0a00d18280034800808800241815414030550841e00750440700906c4231f0000385904008800910100801d10a18100c0c2d0071100040841e180c801d810641165500349058a0840b40406801050b11030045150f80c103000e416009003591024100081140b4502c079100c0740001c0c46c24100c154001800c0f40f180e4460341c2180d0501d500540c60080c040302510303008008402c002030300342c0010000e1022002c081140e1145488120342e99000075113118681e03803181c2c080c02a0750044015030000303000003e5a501d5601039041e046125500050381c0f200c3c51504501c6420400c0c0003004850814021280282c216030500354200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 211607041 1250 211605791 211605799
    0x909070303320403170304081e0c0609010b030601060c0206190509120106030516050d0b100b0a020105160c03080112020402070204020d0b040e0c060d050907050a060f0806030c01090302 81
    0x2910500e0082200c016184503030600403030340740c1003940ca51502c40014106036807103a952031500e0000c080180c10140400d65000d45111020001918905101c0150310070184d06040030a05044104c0c650038240002142c00d0f20721039440350700d20700031460180003040c0500424144010104800d0700421494012000c0f29108108260181090703640150b09454400e000102131003072245414400307034007801075407108440610643c042d00c0000d0501604150940d42c01920007981920315490b0343e465110041c0221603100000b88011540d081c44d880202000c04c070f19000800c2908040e11035404441403034142000b000108600c000002e98000b4095044030079000307010582c4611400003034003c0c410300f28002e500030307c00211402e4400244d04a1080d0000895081110100c0320550a8507152050760143c0c1c000010440f60b8010700d0558085500250075104031074a041c3c80b04042a507416141c0c01c407502003408600701110b203540c8070f1012980650154003401c40041e85070b00182103240940402442 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 211608291 1250 211607041 211607057
    0x703050c010b0d03090801050601080c0304020d060b190612090503310e071803030203030a090312050103050c0a091a10030b030a03081902030108100504050a0c031505060909070303 79
    0x3480000b50080c030003049000703001402d440060318000e4112840c40c4111221542000300180c01513000303204483c0719180945415140da901c6600700a46c0022501040307800395665194000e0940301c14591020306d080d000709232001d00707041500103030001c00c8c41c0d54546022820030002600080000c001e4030f1400411000d10745281308100440880070a401e0750400d107001d454000006c40006054140c0e00584585c1c4a60034085403203650003a030310391280809000b45c1c5c0200049001c220190740200c0e805400780c5400d10310443c06404040941d5070070703030041c0d40547c03100e1011480ca00c0d103000c185000b000307130000c10400600110b0314954200718030300d0050720480d010016450814020741004c2d210540003026900d20360b4843c035014205c28000d80d80c170a46034043d42911070551007070f0301c03c90341681c030554004c01041c22180081400b420000b0003c448074011000200300007281140280c0113180725902011001c08401c1d2050111000180803d220303035202c5090024504011a40e002960340500d00801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 211609541 1250 211608291 211608307
    0x606170a2102150f0106030b06120c03060f0301021b160608010e040201050c0d0c050c1804020409020d0f0303050f0604050103020f042a030b1e13020901091a070b10060203070305 78
    0x10500420340881020031036954100104104100e031a0f50584106c0e440801480c48200280041406070903040ca01d20300c1080e0128507a9130028001d582d00a500500498605103149c0109003a0307040500c62103c00100c2540081c1845018050f004a4a912182c012221443c002000301814018480d202c285250b00e03020034207591044084845a0300404121051314010a80042c490100c0000c20b45960240494014852811044200045d2008103248080b52200d400f080010403040e101242d000e40503140140009001c1d06075942958004d0702c00240b10303d00b42847c0010700f440201464032030340c40c0100620060740c1354a1030b03060814007994002000600c555405a000c90214044003103584d1a0448444032076044e0040304000d80d041e11503501c0410f010880c08000c81c1c0270b03140198442042c07410504000c1c1c4d603034080d02c01000d05241808050750703601000701c2c030000c010143c0e0401480014821040c059401c0440e0703084560710116103002450b11100940300d00603031400408220000914003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 211610791 1250 211609541 211609543
    0xa230607053f0106020601080c010e0d020306091b1f080702010f05090c030f0102040e04030507050109021011160510110109080307020d080901050402060406050c1006030606170a2102 80
    0x10102c00706409040861001540400d8402c40d600c000040c501080000080b81480c40402e205048030300d50401055280d101c4001510f402d600102e4458100d800c40c4440d40159a04011081c00340340d060340a8081c1200c4c4154080d0310090b4144aa401034950148280420a1800b9070240045452521480988401c43c08a0141002c8003040d00c0842c180800e110010001080200c0c1042c070441c00c41d000108070910749403d070700036440b60a110190140c00200400d000b04000c0003194424400020695255400511140c102c2c081180c00680c40c0030404141001c200a031441c1e2100d200010305000d464100040c002500f681501010800c2214200134090002d40004070283da00c01c103815228507020070020b60380d642a00e0690b00242d4141d000c60604031041c03203103600550b0003030900f500c0c141c1030003000d41361507004c02d0880c82103100380681e24050110600c03070320015520441011030300300d18001e4003504521210160b0b1451340c0100c07180da800204a010352a2804a000000040b1a20114011303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 211612041 1250 211610791 211610827
    0x41503021303050f150402030a03050f0409021620030c190f03060b0a0f0311011d0306070c0b01050621040611030a020a02070608010501170c0c030c0a23060705 70
    0x50010340301c220404000c12001080901c1c0710300c00e07802159600380d00803000300b40501007940c019415400840100011a102d04010103201d400400003500e07040d56064884200da210302e0b2004403400c15a204902000301804140c981000345440f040342c14a40407001a4451641c20031451103460000403440c01c410005411078000c2440b18894050b1950740d0030140007410202c80c58610850200c00b0102d5603443c00304100b410b40390000e2030001d001c0200e000650305000000c1e100c10017840241c004108aa9080003040e01c035103443d41c1e94544042c00c5103807540001d081030b008a8031800f41844019131030000001074880c20300101100c0480343d2118200312000380f01291070302e81d92081c008100844c1c4880c0d6002403070425403507822940c40d6941c808049a840000380540c0d4001450480e5005020102115850300312041c00b902c589041140c07503156185500c10044c0d10031503001590031806014045c10903580c20300c00d1240320544504182000c6859001c01426079043c0f040c04510411841e055860b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 211613291 1250 211612041 211612057
    0xd0f050307021b04200702091008070905041b03051e030315130f060b0309060a020301061d0a0f120b060a120f0f0209040f1e0c05040b1302120702061303020304150302 73
    0x200411700b58403a40b50401652110106038022150380c804182d280c0400c2000340d08071542030001d0b142d8541401c144501800300a003058034032490314048505008804c0d5624001103110ba001480c4103034284024003000c1034007803000d01d0240c1040c000c208841a808504d03403880ea0044038081c3d400035080b0700ea24014500302d200c03140343c14a84a070200301c1828200095004e0702100c2c0890b401c030b5813070615030000da202c01d000703c000199040c914000e0141603680300211100d4000c0404200070303141c500000b000c041a074054001480c42c4a51230090098240303000c2d4116000f942c000c19540c2c01c104155400d0210103400401d01405003425209001c5503801c150b1388954001e01c41e25090130326082c100d100c220b600c3d10960f003030800e001503c1c42c510001080f6440c8a40d201d0590307005c2a19110420005100c102d0f0080d400c07491140151002c00201c0c402032a03201260300030603800d400c0c038540c002d181000040000342c4d01403003032000c0c80100b500001901d0496461a140110345080013500310003a01900312 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 211614541 1250 211613291 211613321
    0x1207030503030f011d01030f08070807020916110601030c0501140f0f13060804020a031103010b04020d1a060309100b0409060f090627150b030303090d0f050307021b04 73
    0x10a00c011403d0824100741250700011301404000c880181d2551000b00a21001382043c4e151040d04000030040e901515525006444290908842c0d4010680c1598115144041940403000c4945001c2c0c20400a00c000501c04000740220760543d0740780c0551200c140100390602a828010559414118040310709007010619201d84554060007004403e40081d42e549050700341e0b203c0045076407485103049610450300100700300401860760701ca80303454034440d1440c560155210703210f41c2070039142e900081c83c1e40036145000203828599081844080160003590b284644020004c1c41100180003d18a428003803030300000880c061158001402000d15610082409003000011404e182c09580106a01402804180004ca16665941a20348a24440160b81241e4a9062030119038550150808a160783d440080c8148003c000640703103400480d41060142e11943c500065164407014041c184c40090504605504141101a40f20313100401140c00212400040900c20703a6650444004410400d0f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 211615791 1250 211614541 211614547
    0x80403140a02010801170309040f15030308190b090c161703041209060923060304050706110604020922081819080c15040f06030b030114151207030503 66
    0x5255859401d00141a40894069400000d90a00c0c8081e0402000d0980003d1841d1001110400000f401780b02c492000306503840c060b80e0342410710128034101860207900c45a456290009815002d20703103400300f00d1103103410595040b00070785034142600d400c007040f01d0106880741c040c0c0300c44a00300c94512101520441007803220094003500b0360003d6000e00c1c000c43c0940c4d403169105000f40c546140d9482128009200c010302001007054141415904403000a03154080342c103483c00203044c50300262410b070384030342011004224986e00003100411410f07880d005058140341a40001d421050010710301202c0b01b80310b0309030b04c0c0031214404001c0700e01c941c041561500d41603020445050b18011181c1940210903400125814480143e0500c040342c2030900106044d1171800203201419130991000034045a0603c40820f44070354010034240a4091681e001940e104500b08060039902d060f1014445907030a24280050070201002540d032108040d10600340c0205001d25162030035400340c1c4040d090340004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 211617041 1250 211615791 211615823
    0x7140f0d0f020606040902010801120c180c12060f0302040f0b090c030105030f07150f050705010608030a2c01030e250503070503060c160c0e19150b0f07080403 70
    0x890716080d034010a80e4200c030b081c2d80d2540180011a2807414010740482e0900300100503421440d402e03103559a110340d00341a1016515488092800080d4090f80c1c205501c0310212030344c6a501c00000d8800001d07244051000a15061402d0f8544030b0070300000c0e01543e03c40ea52406085800c0d0040f440d00f0102a2900c0702c2c52a000405901d59042809628072a0265080380c85183c01c000074801c1c04e84032450080c0950040b1a0010354501c807141040074140401404031902040d820302c51580204001d0024558581c92020001c02c80030f0040790740c80381500c01c0c5e54800030266241041e0a0704000a08000a04c882900b401c10b1170b1427282010f510561070b036690054010a20a941c0b041101c0059080700c00081e15401010303250141150703020358054061020a81308030510300c400c40407501511402600648840c41c8450b9228211601501c1d10f44502d80f140c8041b0302c038441c1d404568948000c0d20003190821699541c80c0c882c5541d203034510203022400c1024401750208030350007076600500d0b0700075803061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 211618291 1250 211617041 211617047
    0xf0405090a0b030f071a070314040308030108060105011d040507052224050a03091112010509070501050a1b1406090604120504140910030506070306050a1a07140f0d 72
    0xb026040d4024000e1400151030120000f40d940e00361044001e6210000951480c80021504405026000c11400120700300d22403001000910245000e102c04540d29810140010324000e0113a1000e81042203607440303192005480b0500305040501100e02044a07254218121424040c2003148441d8000d106807a2050701c00050240046a400b03a078403100c485e00044840200c440b007044100041074040005400300b5129034072000603a0711444900da44590000086420703203040810841c400ea55542c00d000d0981c2003046404000c0c0403d2a1945c60103800d11001000480c030300c40d082108044003003210301004402418140841030450440d0f00520b0a01c3d00e550741e03850709407000c5c0c032151421204da01405d48104119410358804550300e1603505004414044030110042c00140c0d500b4a00c500400060360034858140181801d40e40400c82c00d080c0742c200443c0d107100b07500103092414480a40708000002c00705030351519802520174100704550880030b43c100060b080b408101401032040202c01160 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 211619541 1250 211618291 211618301
    0x60108030c0c061303150609091a151e0310020703050712080603030a08090c04051014040516050f19030c120212012706080f210702060f0405090a 64
    0x5506001c45003940c2c088418081c1c03501c100c660b42403e529003074a00b4404500841400d070424105080002113079903440701d9005c03c803a00800c5c01c48038004034030340c0070b1050300c0b4080c065030304040c00d004243e1500d00120001901100b540c2c521010790031130f6400c01e08560390f05024010b100c0b0b4a0304030a40d55140c03c1d1a000b0701c0c0d58000101190409065480c036400188101e5038144a410040c0042d40790403e44801030315401c000500c118110710440329600040c2c0c546010301c43c0584141d100d500c5400d42401408000d0b080105100c0b40150318020400c04a00c9114040c0d00481050741081c070754031900044403410502c1a211580c540c41c41e8200309006041e8554414001050a0741c3d40c0c0c0000075416002c04213900c251034105202d22504d01c018000c1089083c41c102558001a00110200c8414005901519840c0e8028292504030346c900e808a424140942d003881d058040407060364611803110310075103006040010f80118000702d0b1107000342e8001c508440140c2401400d03402d080c0361803071080015007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 211620791 1250 211619541 211619557
    0xa0608120408011103090a031b0f0c0e16120b0a031a2505090f1909051b0909070c021314100e0c0d0509030904060b070302010501060c082a06010803 65
    0xf41c80c0082e1500c19100b4901924090582180505884c0030b85880c1200c4420714484e4590004d5400c0c01003200007500011006180341c424900c40384510f1038008030350004030b07008001800d00341c000c0c101464410fa019410845081c400742001074000b0201012402011198000070325651808040c540c080c0c01d02c08485101e2410f9003002c08840e2000c0d100b2200c40c141d00e02c2100003054090204c04860b05c3c1000071808100c0b000740c08010090921200c070000c001d5260b0220348869954000e03c551501010079861080c00603460702c0d440d2550740e801160070303c2d600825860802c41849010011507a507065500c106600484007030000700e1544619420303140007600c440101c0c0c2e4a031100054202d0040c42490b1082c001c0d00842802c00b480001464060310300188090760a0201b000f484c0302e141d8541c85040042c02d807500c5038603200c8217246006030071108103800c03140a002e00d00407c400000c8400048900250440450045084051883d0402440b1050303050072540103440001c034452200001030301000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 211622041 1250 211620791 211620793
    0x240512011413050115062a0c120312090b070804170304031d01020f06060f0301060801020309011e020906030105010c050c0411360120010504080d0f0b03150a0608120408 74
    0x8500d02c0100300c1180921b485400d001c6441d40301910021301011554141000c030411121005005690700c0c4c9003140d001e500401808540e10403258107050707215900031074004a240b8204002d88198a8908400c00001d02c1c0e14100b088070790000b420080300003000c1ca9603d14150740700740c4901701842c0250845840c5452100c41c0c0d0300180c204c0501d0341c0300154001e001c042210180c0000d4030b03100c050105050303d01401507010364a075100080c24007004d2004512500451000041183d075200c41510507103c9100084e130440e0040c40186e095a652504807411901c0900b000828407038646001c0c1d081442056109901a250410000200b010040101200240c0380c1440c07140c05030420b882d0280c50a005c55240002203500e42c0e0491030750240d902340b030040c502c400c4964500f07003804030f6007800d4400071607040310241004030300a1700701c0c0440d000f0301601c1c018490f824010f0319a81307030110756a5003000440240441d40100483c883c1d80d184c3d03000b08081c0541308259105a81e07454450f8405900c0740c49520f080d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 211623291 1250 211622041 211622051
    0x51b01090b0f07080402010e030c1e101403150d0609050c090a0c080631061d010509070810090e0105150f011b0819030f2405120114130501 61
    0x2582d0901101d9204801039140c0c20003035215038004558081c241401241c0600c2144c60704009569020380c0c1d04005480092000b4510709000700b44881c1c0d2655040e80f0080c00740e01d016181070070300300400762030b405000c1c04c41804080c0c035000c00082e18808041000350200340b030000d64000f402004035060050388804d88001c0100d03110305c48000c0c11508103000c00d4001070100404540d41e4a0442c284060142000a55090403404d8a85035054410040503800c5d40a6450604001c0156010700842d44901c1c0d0407009092580751202190a90200402400400c4007000020740107020083c802d0380070702519401040800d9070001d85030700030401655600c00c0b4038501c0c10840503d150000340701c00c03c5201a500c09031070301c3da0510b481d1464041044e080f6522001403200500042c1c01020407e10045a55000302c0c400740c44401141c00c0f1131980240300912210741f03180c404403a00780110703d0200c620594900030055201100c0314014181403610b0b04c1c441c920719050214418100c01d0514200d40164002c02c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 211624541 1250 211623291 211623301
    0xb010311030a02060712171e0402030c060c0703050f120d020c01061809020112090c050d060b1504060f090f14040b04051003050d020d1209030201090213020d0b0306040f02090601051b01090b 83
    0x152400301255448000c0720542c1010144240c1d04094a4009e4400b80c102c0f0700c61240200003d000340c0020280c0c0505c0d6104c80401c00902000b0030011103411600400f44c00001482255404640300d8400000c0b105600002c03400b81e00345c000d501c41c42c0140341c031280b03105003071411407121805030070210700036030009503100c1032004014402e2041c03041c0c10340c0c003480c134083d114030701000e04c03140d02102d55081c0c0d55a541c4201c0c0d82c00715143c03081c0d940b010000c03109003180e58506045001c0c041685229191041041c00081413100942030000070381500c40390744004058110382c4000a024001300c04005070010704110500250700c83c0d000c002001d8900c80c1040e0741179182081000ca9a403d1045660301c0080c520b48590510300a0543c050321940c0d00a100100c0c11070002e0b00414040c0c0903100c0310100541c0c0c005802070300800b0038811070007030800450150000d4140b079200c4007440f503a4500d020340305a0040d00442c3c0c0c20380c055400c941c0e10000b280d03c001c0503100200740300c500030a50f4030b40c1a1800401d010001d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 211625791 1250 211624541 211624577
    0x7110d09060f031a21030409090605090c0d0215070501150303090e0f01060c0f0503070b07030c09120b0a18110901060302030105010c14010f020d0f0c05070b010311030a02060712 78
    0x4000080d44d000940200e44078030200441c0395841801d00303401c01e01034070032008555001c3c0300030805890325078004204d0b95554034113141200c400078401e0040d90040325002c0d00694440c400c1080054048031420303010b0340c0c022940744c800e10500400525640c80e02202c00d0106011a40800c2103900949070f180c6925035804510070760365000c683c907410300f89026006006440c000e0b030110800b540200c52952040c18555245482e69020505c241d170740000c9801000303419549402a4480c17a110361900410552400003864031111003681e0017800c0c46520300000700c5200d4644e02c54a51030445402c20400e04003242000c1c140d4034000200e55018000341130001c91158060f002b100d04030341c01a0343e0143e500714075458800741072081c2420405995220b405696990a460000d4801c0d0070000b40c0005100700740d20b54034030031140098403d00c1808001e10558001c2588070702080e04507a0042210280b00c89041e000a0402c1c004a100950100000c103240040c001d00e807240c0303044c0303070425124692881c152340038503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 211627041 1250 211625791 211625801
    0x70303090512031318020d0606020a150e03040501200712060f0b0a050d0c03080a05040512010c050307180b13061b050d05070f0f060b0a060c03020c01030507110d09060f03 75
    0x1041d00207404c1001044142c00d488800c943c48008103c0041c100f02c02d072000d82054486507480040164041065001801100140c4400c100440c030002c110351184489141e88a01491007230a05001032484040100400c0d2031400c0600418541902c00c03480c0c803900445441d00103d607058810303500d004440d090400322071050450303038440202180503075442c1604100103c0c40003030f0211192040042c0020000d81420043c1c00911003d445181d1100c0c1000c0a2013198801e220115105a0505803d9600260070404a80d0000214a0702a401c10075005295003440d160f0b0744003190b024000100b1000b5500509a803d00342c80d007030b545441d8100d6030f2a4107029a00c001c00d80240070740d0407da144864090183c0e006109861052829040250782e070707110300302c07a03442480d41034481c02e1325480d08a2640c9071484098014101a01b00b0700c56500d02030310004c0da01c0081c1d9084c18185503a403800315909034090521491400034032011980126405000100004214851400440c80c100450051103000b4003031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 211628291 1250 211627041 211627057
    0xf0103210e0d03030e010c09050f0102031204032d0201020d06080c090c0c0c0603010f05040507171b090405070c0308150d11040b0d06020a08010509040210030504050f07030309051203 80
    0x10714050703255000104071807035000b804120241607685000c0c0100c00400e001c1c1b680c07424003d0315121a41460708042c88071990340303503403018110740040150b00031841501416503089501850600310705030280204d00d050350750a0360341110b1034214041d442603141e030540040855001e0708005105080d540c507090b40d03484031074000303980e8059079240010348a200140041c0201c40c0001085a80b0101c02c0f002007441c0c1c0c0c3c401c0c1c1150261103a03110f428082404c0c0b40c050990801182d140080481411038032460f4050b101500c1c1411007000c094000400d00d0000c004d0b110001030042c03042125040c8070001401000d0100c204401080321940010000701803642043c01d101006815114100442d80c0d0742c0c072030009540c1c0c48951080e511030140c46540c1350050ba03410128401d0400694a017440040905642d105130702607489098240304000040e0cc1c0d41154600d0f01400d82804030b003945891900a0410070041a2680541f080300000014958021021412554207031030303000342c2c4100b44a04030303224420010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 211629541 1250 211628291 211628297
    0xb12060703050403030b040c0503011a1306260703020c0601090509030708030618071110050403140703200c0a080c011b05030f0304060212060409021005210f010321 72
    0x1000031202030080d0031059005129240c006210943c140011701101d00c124803041c0010008070050280c0710681003848030702842d45032034a04001d107802c241c01c0e0b0781c3c26034010842004075042814a42e0b030794503c1021140e50300d511440c210f600d05050004c00940009500d00300501c0740b0000003503146851320031070f130149000c10051850300b921070321202c1c0d6683c005031039aa0840b5400c511280f051080484050041c0481e0b980c0407112083e81017424030300000c205901e18280e01d080c0a000c0000c0c3c1083d01c1540e50b6007040c2e0390f81e844201d80d0909403088040d2104d40f66944544c080803000b280300c00f18503087c400008070b0b101a038094507020710703540c1c40d140e007a2402d01250380c403001c039415003100b9481d000f81b1070712460440b41740600204610005401c10340d02160740640204041905541060b07140c0c0d030050b401d07201003010070401d40010780c110801e0510f4006020b40010030241c4145c4d00c1000d02c1c030031112000040740900f466485082001802d00c000ea4414034a480c201b50310b140c0000a245105030b045c0e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 211630791 1250 211629541 211629553
    0x411011809090f0f050a0201021501050901090c020115171618020309031e0301030b0f070f110c0d050a0203062206020a03090605070206060f0a0305070b030601050f030f0a0b12 77
    0x80e8120020b008880042d203003007426540e4480015135841c0010034840c491000342c00c51a0062002925040c141410b11144440003401407003103807a45011541104c5144074041040c04410100760700500f51100d500728040122840801d6102600500843c0340410300c049640c4149000d4681c08545210702803500e4002401681804800098010b5600807080c001504d00e850f445a40c40c10301030310040d002010801000c40100180080b415400391b000290814049180c6041c0b0001054050203884078000e0111034509100c5044082010310503041e000740c44d81c0c10701c0729070b81020fa030707110803500701284244030722000a9001212140354884201608a00c040c1c1d180581d90746001a40044126078109aa40c0c01041c000c94440d020b510300425031a00504802c1c103010060005000201c80c2250043e8117540342040014400100704046a40c495155902c80d22109d004035030a10030000881b203007203400f0060221352441040801c0c019404000b0400c40c0300641c1d030912011201c040c03035040c440d400031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 211632041 1250 211630791 211630799
    0x1d01060f0201020a0e040b01090b2214010203030403180503120403050610050315130b010314070501050913050c0c070807060e0d0c09022101060306030605151c050f1504110118 77
    0x40c0c011f000000c0b0b05040c192903e5032600260f04030f0342c00c009080149071440258241480c0c245d115044040c1500502c0c00031060840030010f5030703d100207003000b420805503003c11111114001081c00151100405556804a14201c2020250020f0006480f035025100203d10451451480740302180c1014003d03040000248503d1110207030010078030680320341c441c0407807400503040f1240c250180d4484d21900c040083c82d0003001d4584080c03034101a0500404100c102c015561b006005640c60110b0500418255520041a001c5001e4160b00d13100314800d541010424140100d10b040c1030351516520718405010940410182110141000c3d001c3c2e180010240190a49900106942002c822080d50f00c0c0f50f0a00c003003003051100341c2c0a980080e42d11003046c420041980100380d0400c01c80b4014840c03100301c02c400107410f100c00001d2801428043c03021328082000a000c0c05c010001203009850107005084008001100110750072145161704d5107a5803040e40c02940014152612526403181c09820 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 211633291 1250 211632041 211632049
    0x8070b07141c050c070e041a06090f0606090a03140c010f02030301050109032a06020c10030515041d1b0109080604030807030507021203040c03170a05030a02090402041d01060f0201020a0e 82
    0x44a4421500b50117001404100541848a40c5025520819069051903012084080e0840e000782001d449000790206000100080c1d4012a401c501d0880310280d840e0115400030388444555032008000600411981801d043c001c268025017072070a03200d0080002140b1402c076241d03c02406040d010480ca03903030900c045045402c1c3c140d41000d144090009403440c125500108051940c03001c00164410701c0c0894003070422010000c201003d9040520850500f6800c40c001c1240522070f45009030303500c16080c640c4905238500350b4001c540c04419580c05104a41141c02d9110100740c420340031403196034002540744800a071461055030940d03641401e40e1035040c000c402801c000380c145801c41c07041b1180705105011220045000d00c0c4140c02580b8998030f145018940c450320002e404036503100c180080d00080d5040401c40740e00801540300107a031014a000007600070701468100510707103c000003051400d1852682024161282920790911515003040c04a09031b124464240f800640c41c000c210001f418 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 211634541 1250 211633291 211633297
    0x10506030601031e03211a010903030c060507030212090706020606100503040b06150a03020306030106050607120f05070605090f06100609140301020d021612050702060403110a08070b07141c05 84
    0x2110749051401500d0f4080310861b44000008071103540f5688164884c01484481000c18200358217003090521705207543c8025080c82ca691030050241c5889a000901107842503045407002d4036054100c0358503007461001ca981e03034001402603001522645001c5515441c00c0f290801c4045a0740d130b2a1407941d521580c9000c049000580b031a90040354440c5a044060207040c082d12010b4201d540045c0c882c40c0001c2014250790181d440305001d40810451007020541301c850880e260340d542d0034440880c2c4e100f590122840d208024001d82454038000a1241002d00481c120b800044580300b15089074035001d0204a9800941c403901d00858100d040030054030000a0051200a000400041c10711071001141016a400b0b03405d00e203152403110740b4003802c002c0042c107c00c1c0308074100d00d0003c0c10201c1c2070340410b00511581c000130b84648100c1a0491855407000700754806052054291101a81e80321220402600039200c201c0714050050381c40b403c2040e00148070865101a1000468280e01c4001c0a880641c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 211635791 1250 211634541 211634543
    0x902030c040203130b060d0b163f110313060209030604110a0602060f0703020304110a03120e06090604121a04030819020a12020a2c03010506030601031e 67
    0x40140302103510a41e44500c0550712030320070441c00c80412039080c036040100e100e0003405584180c044682400106000900090748a421005051500f2800031010745401800003000b140c0644a112600c0f180c002183c040000b1040d40c40d690501e805421400105440c0070035140d03040e03000148002032038030201e007404c10381d0305001e40001880c0051080100382019802c03903043e5000300749402c0a41190904128040081209202032300041c101070003e2000c01102800c040209034001c4041000d00c012180b1905181d48001d00c0303c5d010641da4a002100001c11031005000b14005c03840c0b00b86c0038104081100c1940b20b008080d546060b0400c0d1503011900030b084420350300b5491030403c001c00708151590060045000380c40d046501c0c54010360310b00107a50100320300144940180030380c1c2107040d005801034000b502071180268031100e4441007101e141d0145031719500074405002e2900c41075144d08000c240c1d0f600041c0c00078082555524141562201c00b07200c02800100e2200024100da140c00500c45921 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 211637041 1250 211635791 211635793
    0x105060c1b150c07080705030604111009090c08160c0b0a090602040e0c0903010c0906320d0207061506090b070602040f0902030a062c220305040305070f0308030a090203 74
    0x44207040040c2c1560440003060740c07180d01482c000c0c08006000c02c000c20091000310001c000d940303041e903178000004061081c51800f034034254815508041c010340c00d80c401740c841218200b00c8001082c5c2d00800400d02a90841d0143c0010410075144502c0780358543c2440c1e0b0494180d010341e071140344244c4003c0420000c10b03182c140e420301c40443c070208142a154010000860807036203c1407030100f0142100c010129180c240044514104449500030302001c05104a98000c850080500f58003a05000401e400840844400107128850514194050100e95008400030071082c80c03456124000320741d06000ba00081505074104121038142c1d0360042412610400002d81050740da00d06802070000b050308a14a444d401008204481106109400c01002901084414105914042030f10801d0750056518400704002c00149445020305107980440041c4020b00918030240c01c1c02402c40d001070004803018001c0c8080000c0c0415000201c800762504462030030310b9515a003d80c0340003010001301c12030305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 211638291 1250 211637041 211637059
    0x1a070b09010207022205070306140f03010e061008060108160b180303040e072d030207060e0d050c070b03070e0409031209060e0f0304080a06050622020d050105060c1b 73
    0x5844020840b44000c0c840c4039110010040d0314017100c1034400c02000c18040501d007000401842c503420008072003000d81034898150101c20440030074094035400841e40001e215090511001c040d1420312501190030400c140c501d00c0e41c0741d2090680b501002c9030b40b5604110542002c2c020381038a00001d002c0c0c00f02c1030543c401d01021031004282103400c203070301015084d0443c44c01c01000c1a00510806440c0320704c00080020000150201c00110418490350b208141d40400c0300301c100300441d0322511030110340104441000c5000074009205178040c110166a81c01500c0f0001041c0c0214000d590003980306450340464642d40c01d040c070004061041c015001c001a00310040405e0403c1d2040d0b1020074004c220104564460004091510500e4592a11258020801040b0810022607200a141d52080c004181516140f00181c0101c541071113800c070051980d0300e6640c1480042d401840d810040c0c41c0d048c0407aa076520304002903402000100c810303640105035a8402c44140d9140d010113481d00402007a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 211639541 1250 211638291 211638293
    0x110d0b0d0503042114060604060803090d12090902040905041713030206160b0702010609241a09030303090303071205060d0b070504080d020307060b040510231c020a1a070b09010207 79
    0x4403245c2100358203031407608000144540c07800d05000340009000c1d500015440c18000c82c01040c501e400810010f0f03c2001e422245001d2984507118400040c5034260055407207a466040e0074004140549041b40c0c108000b80c1e000c0360100c0f07000c06840060000c816180603051454090203800c4d4821060070010f408420040710000b601d04000d1405441e0710380c00000c0240c107004040301100c094240b41d948002187c69828180c2c0f07520180744080d03503c03c4c400c00710321100181c480c00640c060b4000c400d42c580408000c00102c21000070156228840c0c640c0c41810352070102c404a030841d041941c0d082e420404640c11000031421038820290061184d140c40c2c0d182035a2118428113180c0001d11030801a080050601c003844402c0c001c1c2e02001204880070009030528400c440f4499500d80329500c1071002d00c11b4908841604802c00304098030018055103402410302a008181c42c800941c228801d4106200104684020790340142c0030060174074080f0f1414540340c80c2c507a00500f00800d01c5013950f4080003044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 211640791 1250 211639541 211639553
    0x17061b0d330506040b090f120c030c0111071a0c010c05210606030c07020109030c060207091d060412090b030124021513110a0305010c080903090604050d03050706110d0b0d05030421 79
    0x11030348034031010150804607180300405045c424001c2c1242ccc1000402c80e1040070404010a900c000c880868460802c40d1b50289a044058012082d600300903520b0100741812003a0003100400c0581800310503440c00c925007400c405000d42c420b0383d15a4000d901400000c5140480c0c0c00204011401410090b2020303a8a68550440d800c00313410000040c3c0052904104594070350194500c1040c03040314078200200305408903551100002c0014042699410325141081c0c040c0355500060318071003001030303965a185c84504400050144100c1d1010910304091030b0980c0c804244c4a0382d044800c14003003100d45940c400030081401c0058190344030400600c80b0900c607541c80341420004c500c100004210a4492070015016442c020500700c00ca0b04100700d000100c3d9540c00407101078550031106600c00d0440c505040b18980038000d002454186404804d90f401c00d40c04000d030090360034051051000280c403001303215550200c0300000b491a48180010700502d140f0051840390b80020104001365480252184 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 211642041 1250 211640791 211640809
    0xc090117040c080c01020a0f020108060d05010f091101180605180303160501140f0601080c09060c010603140d080a021612030902010201050117061b0d330506040b090f 73
    0x71229102c44100c10807400c036040c8070998131400e00340080c00ca540900d03103c841e0300f04101000207040140000000790180d448007a507070ba956411800801c0340b100600c030458018a1550411350304000c03030302683d845541c40f60040d60896040785000c40c0d400d500d4410280c55039001040403d840070800c0904006648040011705401c0c2036050502002880b0b40c102142140c141c911032065a01100c000c05c44444554041141c1081080c81c14804540c0d1764810507056010b42130100740d21040c00070380c01e40700d000c1c15041b10090b64015824040300341014140e881d41d4059004560010680e0780002810341e03050750740a0050711020021000b00d0b81281d0395001b1f070844005510b0804669510709403002d6503070902c10940500300c03011409412084081d0703410755076040200015006000d007000f1414803101c030000c1d501c0b424092202803000603440e501d990a5a80c02d0228464225180c095040001c000040c000084400141440d80340c20700344044091a50302100200d070300310b2074810b11400c0b5a1502c04c06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 211643291 1250 211642041 211642043
    0x12070e030102160c05060f030c03090312150118080c1309050105010b130f0e0402060d090804120510020304080a08040501022203151b0f09031b0501080709060203030c09011704 77
    0x4030304000f40c0540380900c06038120780c1001d4052141402662040740e03802e803c490f0451054101d1a4507039464075600d91441c400c180120111034421424441d108001005170304101c01c003602c49050b80fa1003050340391040e119034481c011099001c441900d01c2e5007000b4400e0b10324121040c00204240103141c9480f42500c20a920046d0030b00c4000445060070241d2210721405000c0d60b14101203014074111010103e00070142c8041c2c882c1d1000500b29116110035405080c0003a03106007499152aa0303610721604076040d520054a107405003180705100744049108891050354068886801c00c00d0500b000c695031600100221070565003044007200401080c28403006441c01b07907080307140035801c3d840d00240c400300300481164028202613941044403034910190700014004d1400d1a1240c5001404580801c031a9101805115010703005244500e200c0c2c241505843c403e0701c4020850b2150701e400c403401e05140c030840006800502c0803800c0b94a201c4000e0400c02e00c1454805103602500d20618481076080d20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 211644541 1250 211643291 211643317
    0x1103130b03160203040308030106081905270109082212050c1804020a05040f060317030a0501150c0b070306050414010f0605070206160317011d0f0c12070e030102 71
    0xc02c403007240c0c5910309803941182ca02c040c50516140d0b40e0340c4501d0b03000600410040c46071308400501e000248502c10100354603842d000b400039052101c03000b0107144040c030661810410155081201e0340c0140605000194041001443c2c05000400c00703092060f450b90320385013a800300c407000402c6a102006101e00038000c0003d0100002000100520b02036408070382e5400046441c10000541c0d29010364104592003900c010504c8030401010100800107504005c1c40c01640c0c9150b45403215200e070213103114903450b0800f004a0b03601e070b03060041c4ca6075181c4444000100c0840321040010f2181c01042e07000021820040b0314103882e10001000d41d449000240c1503440c0c0c0c1d200412a40b0070310303074828001304901d042c010715140d00350300440c032584030704001c0c0d9080c01301840d092070400d03200b1000c8a500a400c180e003040903584420005816200744400d00954009410101d015401c903420f4144c021104602410f2501e408000d107040d036114001c1c46c201c05d00c841c04030102c549841c207000810a50400b10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 211645791 1250 211644541 211644547
    0x60f0a050f03030c2e1e090203030c19050f0a02090a0c1e1e090b04030b04051005100f050910090914010203010f060212210408040b0d0f0c0305070206071103130b 71
    0x304d5100d65010030300080e510690410f00c00a00c2d08840c414501508880b0440118500c4c0e1f1034000309141d4403c2044450140c400c0e0100300100d58400c80081908922a80c191002c0d1081805000d540b20b0154401961003007800d0301088400841d64004102d42e100d03410507408030350407030302e6101c2210090036910300460b64602c081020326404001003a505222400d10303c0303603281444c3c100c0e00350340101d0000a0446020101040a000c003c1000a0348141c000354207200c245032020a07900c040060388180c04201410481c081745525140300510f11071014640d040301c001d880c0c022900f01030240c401095640c0005800c801e106044280000e6010b801b401101e10105450311100a00e440d084a00c403600082090003103c111a003400600a010800300d020307800141c41d14280000c01d482554048400c80800151254042c406908000309000800d01c040110100c0341d0420350660740201d80140040e04010005082d403400303440c1410350615200100ea003801c80348074000c208042d55070440710103000e000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 211647041 1250 211645791 211645843
    0x30106030b040f0501061b060b0301020703020705010908010606140d0207050a0507140603041a0712061e090509060402060d020f1210060203040e07140d02070b0609060f0a050f03030c 80
    0x14020401ca21020300f000300610762401100400344030340025100034000034502140f00f80b02041c3c1001c00707145d000500071556040e5034030780a59501841c3c4111804030350309600000b42d8a03418030482080318003588600b2001044150400803036442072054051140c3c3c02e00124010400800c14490824811401052401e08044540721200149082c09100b00400c104000c001001c41c522105c401c5d903440c40004a540344c0c00c02c1514401012420100b400c0d19120000030118002c07500340c4082d10102c5810589542c8805250381550412102071078580c2c05278000c640182040d0b40204002000c8203401400c0c4014800c822132a648000c036030070b000364a00e0003480410200c0652420060486000540c9002d00d081001003440500a105105002c030700d40310441d04450f004100c407016080d8140840d99000980360082850100f42c5070a40500d41c1d44c00017038803c0c00c012100392080c2d03400074482a0307030b10324060810032b0014032841ca40d601404103005c020b2543c0001c0088201001e20308000d5648d200da4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 211648291 1250 211647041 211647049
    0x903030b04061a0f0c0718050f06100c0201080c040b040b03040c090212070e010c06020f18030c0a0b07081e070b0f071b02010201060e15010908070303021906060b030106030b 76
    0x255400c004200d070f007110714000d44042c0b8903080311800c0c0d82d0400c3d1142c41d00c50b55221030781000303060b901c0440415220b201c42001801d2a901c082e01c44e00108466a039262110014002400740e5904400c0c0802c0042e03500f2005907000386200d586c072000900981e40b070552244008010750f08a40e004181d01440071041c40100581016610090010848114100101d50206045000303002d4500030900403c00180110f9034400c0506440c0d1a41090003550780f050401d50101140c2c4c04002c400e192204c0b00e0742c1c55005032078007113807150301d426000300644901418030300860708a5002402c116030040b4100541401050084880c1c3c580d903c24400c010f07258401030a00304040000100780e8500c14180200300460340b50000202c0c008843c62049002c4443ca05100503030040581c2c1d0800c050340c01604003008840f52030144500301c0141c0a80c3c41116469442d05d059941e614a07000050151300811281c8800b203480d0085a45405c0c0100004070300142d071004c0d042c9450340207030040c0000075100c81a001040c02c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 211649541 1250 211648291 211648301
    0xd03020703090503060c03010b160807080d0c090602100b0a081501051e1c05030c1605030f01050408120c0d02120601110c091506210103050708300d0903030b04 70
    0x100942c045c01162038440e03081000c52005000350000c0b40f50205003d1041590b509107816000d27400240195998400d0500b4a16a0803049207500594140010340d10320754410700079507003107410310b4005020790003070320781c810001e4030084101c42d030424941e64000400a504104220a6107030801d0820a00c1d410a801e02140003520030511100ca225220b06c0c100f25111903179884144841c511000590710014039250f0f06500c074a4001425078400c8091504080e0341d0038001004070303103084044468a48144c1075a13801e031074007143d01500308031080c485070445440701e94030705074460b00d9040310364986450001c0190490300f2183d01c01c1544070110003002540d58001c4095922190000300600007080c0100000d001c000d402024031600c01c1c7c86a034103031120f4540c10b00f41c55a00c45842c072000c0101c58003240310048104244010b882c5803040e08000100e0041c0841c1c42a15050000030f0003903105100084509400121507605007141b40800684203866900d1082400039840703642d000c908030740c0140c200800d0350307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 211650791 1250 211649541 211649549
    0x130c03061517030703181205060a0b010c0c0e060d05060c03070207050117060103091e030206040b07030504050d05090315010909120305090705040e03090a0617071704020405040c080d0302070309 85
    0x1096a4030552041c482c00000d5500c099458900b046104902440e10242544184d0120210740c4e40440050304000010035520302c20000c0711002c12880c00c030003004440c040c03444880a0071001036404107000d40341341490155448180580840080000c0e5a16a031a02a013210325444011001c41840902c0ba0305021440007007009181100e50780700807174034108134494080d1801d03041c181c1c1d50380c0c2c04080180350202400a6401c07840144030542642c1000380d15004c040724111640d620400000300540d0191289501a50708940105210401c10a00f940c0c07580c080a2a980e051084240c040c071100101c0080234080c4c80c5610001c501000c0518100c5101e01c910003800f810b0504207020001c40740b00c00601002150303002c4601040c0180d01100c030608500c6000041c5070000000341c408038219812035201c42c8000440c2002c454030795154101102c0076600822503d498581d28030101e809898182c01060300103000350301130070003195130700d01d010310300b0201e00d000c03001080d00468002d05142d04106501c000b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 211652041 1250 211650791 211650809
    0x307020c0904020112021c0c02030c070f0e06060a120f061e06121a270903070309050f030f0d0e010f2a1a10050907050a020a0b130c030615 61
    0x2074201030340060101c504508072035a0b100e071b0120380b007180b2906078004480c1206d85202c080081e0764480c2002904c2c0c9d40001c2d5080018404c0d1100001c03031808110101049a4543e034002d0065156030b02000055844014603c0820403d0002c0c0e501c101d0700361091649200402c0c40000d0300606c1e00007014110954910310842504081408219071600700b0049001c00140c0c1100044003141c070340340c0100fa500402c01e03054002d2031140c00040040e0503d030038a6040b0081e81600c0069607a841c11041d6a807180c008010005952040d003040a4207007501c03210303030b2301d90000c0aa490004101c11403901d0081c002a00c034000550700c0613886907a50f0000c01695031000c0c0d91401a01106500103103005130600c481031041c540e0782000b920400e00402564511802d01d1440300c890071410309a4a06520f158180680d038070404c22000410202405001200e880103001e4020740341f00c00268481131300c90040100700c2c01c80c8080042d0134200240050003183c0c0950301c1841c000412a0240402684010480d04103404c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 211653291 1250 211652041 211652059
    0x605010509010921060f020a030b0607050d030b0a0803030403020706030b060903070b1323030c040c0e0405060f04022208060103020109030b040302071208120f06151e030c0307020c 79
    0x481c1da028039850150341040b6610f1040a480760300302d0700f1380c0201d00b601a2099141c441000922016078005203000c4c0d1150354140060060141041400c1c424848014416401307642c41a1259000e90090b12203030300010008031501c1c0d82c5013100d605692040710100d005800c210300c1880b80c10303010f20074025029000e031200c504002d00e29011075610062400303018005e07c001700c0c3c004201551484070308040e0064100070310081c00c0380f0000070404c0c45400745482c803031702807426019164205485816903c9546a48845407036120b281804000c200240455402c00c3c002086c0384250744807400185904201c1610803010388803000c562259281d699000910903030068001003000d80e900942802c140c0b070300041c2c0d0860350f40302e0f482c091b490441c031584650341d074522608400f000e205414001c0d2041400310380d40420541c1d110340070030840c5807040390440d41c0142017140e440300304400c0b1b0b030241041400e10b0824422940d0594651207580d001150145510403000080240a0b94180482e15866104cd111119 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 211654541 1250 211653291 211653307
    0xb0a05090c06030a0921090602011b0f0c0602031f0e090601030213020904050705190306060207061202040803040f08101a060904090b010312030c080103081603180801020d06050105 79
    0x1d11040800a214824240031000c11384440195102d010001d602861801020f83d031540a0313140c0c01111440c003c003050050b4000200eaa0060281c410001e00050114809004400080e03844840e105410020000d184007100e0001e5074510045010b95603000107180d485440c03843c95511440d90381c0103401d06401400030700c07426903000100181500d6040300d0980030748103400d4a03d8001d01504041641c800c1c14481404442500203000301400310150030082c1601c00403034000c0e0184e074030612030080180d00c02001044480e04c19028101d010000000141c81e00341c0e619005440c41c0c00c0f5070040c401400d41820100035401081002c414074036410035042c000c0940d0a42080003140e0114034440c004d80000a050307040b03595590100740c0702c0b9403068180c081961642000c00c0e1601c5c0514121012a1402e078150250602070492241200d61022956280441a144012044040d140c04030188030861070300354900740403c0801d1000d408007000050f140c03d02c0c0c0d09030400ba620240e11860600c00100710101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 211655791 1250 211654541 211654543
    0x504030b06010e0d2108060d0b0106080703020403061a1206010308180d12020d0206131e0503040f14130902010509090712020c0105010510090602060109052a070b0a0509 74
    0x19070121003400d040062908860202d038940300d21040040c50100001700c8418000c13400640800c40c1e000070754a4070300329503940051000010002102600543ca04001001428800d0318102c0d44140c40b49009420a82d89595450984106142101e01e90054108541c0c160601e42ca84c804c210104030300402c0d6551654545100d54460480d01e1009021804075a441c4c50311540701121405520440c0f2941400d200c12000b91140d00c80e040d10001400317a8404070349500800c002070340350f203034101c1d1026410014260b50030011041c0240700301d81c907010900001500900641003200103000e81208542c8642a00701000b26503062001c0b030184c49403920000d5005030b40e111056404040c03081c0e841c0d43c8980c94403101a954160203d041c504124000207024500c3d91b41034000c24103e540c00d0b500d2542036080090207585044241c001c007801a40520010407100c1e195400294120310000304d82d45038074071111141260702282c4018850030130b400040c40c50422444001c4c03030780d2103000000d04001074103065140b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 211657041 1250 211655791 211655813
    0xb06090403093525081005150d05101410060e1210020d0b0609060a0c030903020310061d0c1603020118110306160f0f0e030d0e030706050403 62
    0x8100f2501d520389070180100c0040c03020f0800074100d28002d80341c03041c4091401d0390301c101c00c400e203030320481101d005410307510440c0b1202010b95101c0f6001d0710451031943c601ca0001c2a0041c840a424102e036007042c09039407200645400c0180c0108050000b0100b00005d08054411045003145012042c504110b00c40e100c165038041074031f001b441c007520001d00790000038604130000c03000421680140b940b521486009940180800c0405840a0002c0d403200803c01c0464010307486816003020042140340d09240c0b1030010900c1c124440d0070721111054480c0c02103071410303440c80398225090381d842d1410712541c80198440650b00c4050780c82d10f500c6203090b0000000c0e0b401031071104000809240300c1081010300030740201c403002200c0103607060001c1d106d0404509105031184a64028001c4001050b04540c103c030801c0b4410005071140310031916502421500300c40e074400b2100c200404450441100d0b901449002400c0380320b070faa21410080440700305400c0420f59403180040c803108010070800982d412000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 211658291 1250 211657041 211657049
    0xa1407140d0f0b0727030b060108040c09090b0609090a030c12021f0b100f090b03040807080d0f0c0207060801090e01020408120316080c030a0c110a0b01030b0609040309 74
    0x4141c90300c600c01d18020140c0001c00030b0041c00182401c040181d41c66000c0715511000100300c29811070074682103a17680d2054160b00028040c0c50301203000800325405004071a070028450460000303c9640c03428600e040322000141121400e81107410b014252614500c405c1e0040c0044000d004000090ba9001e4541c00c81c440c801010034004080840700d1a00901c0300c402c941d154181c4c403000701a40320f0207400080264006440c03040505403210074100340300e844072800601c2d1648606c1c511609241c401c9025030801001141c28450401848001840c0c18000e4517a4000c0302002245070071040c800070080d01c49101d4500115400b4410410000703902000950469441c40700016000740c9a8030101c1c0a44116000702c81c29115034030b0f00c1d13644039451200442c800d800a88000c1842450002e0480c0c560a0942d140714058000303002080d11054a030f400912000f24606007184501c2d001510607040c40e4181005640c41004031004109010b180c5103d285d021800721541ca4003803034a607802501841c0a402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 211659541 1250 211658291 211658299
    0x4020c0d1202190203090a0b1c090213060b07020a050405280e030c030a030b0a0617090c220b030606030a0f05120304061a01020a0203030915070b07020a140714 70
    0x190050304035259a04a800f10040440c041880421a01c00030359aa0710204c0218040c4044030030000d035000480068915002079404021001c2c0c040ea02044064080000c09a03446925100013410320555403207035038001c0c40200d449903150354182c010840c4031000c2d540b00314040c9003803108000000c0c1c01c00320400308003e1204140309030106189075400c0281800c9041a48903c4000360451920340000048d0441003002d51341881560340c41c00520011111a218000120300e805450800c00d10f011140315920100c5001101c2c2c0254802000906240c500094000b0000740400020404505409240082c0009500034401403d241c0d000ca5682c1000c144007501c0503182c0480001001818070a038050540501101c5849042c942803a400502200f5100c0c04400c2040560440650002c81e2240000d50014040c606140c00b04041c4110000c0000c00070400d40c6082140a0026290700d2455010304040d900401d003c031598941542e2900055059501c1c1c0c2d81704030b07070821a1110702464200c07480b609071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 211660791 1250 211659541 211659557
    0x16050105310305060f1e07052818050a0308120601170f01090501211b17070e011703030103081803030c0a030807030213050607030e0307030807020f04020c0d 69
    0x2070005984800c14142080d0103a600010000a00a0020740c00c2e020310340030003c0034419202d10054202070500000a00313034542081c40010800342c06440a44000d9030403222100007a40c3d4442c90120302803482100901040780a0400d02c0820902511000608400d890403054642142c40d100e120b03002d000c4140030414000800104240d102d0b00940002c4811085d101155060207a15000e060409011712041649040000200c0004001540b60800480395140c0b403100500d8548010002c02480700e002c209030040d40000300203100030034007095504401d0160444d11300700b1041d500083c030182d000040c2d4000340740c01c9031003582004c400c4904695010700207941e40d402003c451802c486042458035407502002c129411880c201081c0c2e02c40c410700c6a903e244940d500d04100b0703002c9002d000020540c500031048244210b041c0b003401460207074000d08010242844100000c1e1401115030011140030034040341c081d045007080a064080d4540032a420350400200c80c502070303640c0d6102c10070581003051030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 211662041 1250 211660791 211660837
    0xe0d0c12090b03070e100c020d06150b04091407030603080a0503090a080c012a17340e03031204020405040f05030d0207051b0108160215010f0816050105 67
    0x112940c1c0024250910b0350340e2a4540141c0190009001010030b070301680010884012280c420041c0c19029640104180d09041030360311558014090708150035805807082c400841c4035400c2c90302070030003400c1d628400700e160002408030104090010b090f110500d406c2003418400a20081d00b61400450a0320b04035031660b841440d198604030f0b90302c001034008140080c030441480e0041d00003030b1a41502003038000c034001c00c002c052005290b0105d00070000482049034004c0c2d0354441d0060f540c010303030b140411060000c8204111018414107015a5a01000341c076605106d298003c2c0c1103418603074040f4060341c1000d4031950302444003000203200a20803961000001d00f0000c1c000e02da90241c130342140072252240e481941043c000d610140c000d5820b0700c01c910a0400100c1c102c0b90b0040c8009060355505419200c00341c3e00c0d10a40d04c0c0104e020207501510301ca076103161381074405081c001c108885051441518010007a414422002c194a02d80841080c0612141e604481155480880b0241d02c014003441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 211663291 1250 211662041 211662047
    0xc010e01050309070e0106050a0807020604021309060e120a02060f01080604030e060c0a0b010f0506090f0405180d08010314031e031e01081506030607081323100e0d0c12 74
    0x3a45d0080010240444004140e255100021b0035160b4120f80798076445484604080e0b0751114110b0380298400d042e0034000c80709591940003407580e5880385001150040d0440c05150034046848401c446111002c200f11426584c10003540790230803850b4a841020f941022020342e00c1d0303000204090b061280061106209403031b51001c442100d955041590304c0465646024100c440080c07040d104040d03048400480e8034076141c42250740c4040000c00140ca12019142440054000141088200c10031002300e54007603401444142d646650658a00d203040d0b05510348905114603030100c05e02c866000303100d00305030451003124600e1f0260312804455180c0c0d460768501003040318800c004070203800b003000c000150305200080c0c4286074045140c3d00c10407507449000307250707440f00200d4446001600100204031035040d0700f00001b0045000c1c01454114400d070f030283c1c02e100c10842c1341240a940c44002043d5070070340d452188400050f0301a010301848600b004c4000c00500803a103000e000800654041d443c0680 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 211664541 1250 211663291 211663303
    0x50408060606031015080f0108010e0a0b0403051b0c090a0203060913020307081e07080c09010303080709261002040f170a05250914010b13080601090b030c030c010e01050309 76
    0x446519172148000c1e420002059400103035103c010141d200030000c02c0031203060090325403803200c6d10010011821540c0303d1100800d000740081d004d0003001c0010b05441070780b804003690300240d0840206074903541042485841c2400901050a19105005001003030f41c1d0850065042504550301182e00340c05400001d052007800c0d408203200d446200f5104030019443c44800300c0714441c4500741d62010744e5600d031423031719940140e552a5000500400600c00a8055000075401c9000d03490480b01241d00e6858064140c05804540684000303800701d80c0030003100030441208095800c800a50905240c95440c2c80303c8c071844e009840c41500f50790070b1407042d14000c2101c05a115089411901880c3d0b0082e8544800c1c0d80c0395040c10500c920341d5001140000d1a4000da00c05518000e00525040e03281044000207500415085500c00032000300c0040d0109013003204502130102c0c24030000d0280054401c040c5002024801c80307010b0380150900100c1c3d0f03a00045813010303103e000e0810340c1d66599004281c6040c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 211665791 1250 211664541 211664549
    0x303050f2107030f15060f05030c070515090606010c050601140d05060403032004060f08041401090b0a140f151324060815130b03030720010504080606060310 69
    0x307240008220915505030031000d1030444144040000a94401e801d150b11002e0b8002c40700441c0e082052100014450300044d948111805610b9013094100c2c3d589600f04800d080c44a040c00018100b4050f00301c60a00242e0741280303090030000800c80d025903c490b241d0301c05205540041c000d454052446854003800c886c90203502c2020341f40c2901d07107490301900400780c0b602141c0302d0901000b148440064a1030032182601c00301e032a500c103090903078034080718a800001d2007100e401040047d17001c00c01c0360034041d54110502c01c00c0030740c8451604140c2e034411100100100540703040d11500b40801c60030105221500100703440c0c524802c1c5486134000c150710a0300b0004034030f0014642040c1da0015031060603a070490410307444541020550790f003c103c4024000750360414034500d004045080c2803409a620340841c59440301e000c140d1180000c00a4159002038000341c43c18060020070115240010a01284071102401d00504180c1030401d070969550700144000c0c051240040400c00103610344041c02d0045c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 211667041 1250 211665791 211665847
    0x703020d050f071203020a02090612160e1003031407080c0703031715100e01031b05040306230711010204050607080711040507020c151201060507050c0105040303050f 73
    0x40e4541155520101074020b1080d0040c6030f00450003002c1a01103c4000b0340541c0142182c0c1500e4081020034070f000b80400c0d0307222a8240d1881d16049046c81032141019030302081d04070440c40c145a01c7ca45c20801041801d031200d200f030301440001c0d041900c00486001f2164619107030481c80c50080e000380718001007e145803150b41000000c06501070304207442c1c10021082d096071510340005c052004005507400592014450584a6a03a4400c510f049005030341458045220810345440980e0030038200c2b202c900203a000074091061000c14000d00d0b03103145024011412080070100f8520029001070503110400042e4841b14110230302c00d4054801415000703103c075a49005601c0d003601a07074000c0c202203902e40c1036040030740d90920302481050701c02c2e03a0540140c100d0054000820030710100e403c02e40c80300b001d0144044040c11004d518079601921064903410340d21070b52801c0c114a030000701606141000810841400003035440829103048a400080c00c40d02e464802c0d0140031807281d40c184190320 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 211668291 1250 211667041 211667059
    0x3060209120a08070309092a022d1203090c010f0504080105010b031806060307060e010c05010e06100807081b03010b10031a030c0d230d02031b0118060e070302 70
    0x14442c83e1801841c0c0f440c03190729403020a0ba9210004800d9410300b04104800d02d0400d40c0a4034000c42040116603821803c1c81555240102120204000780302c0525680c8201d510a035020080701c0100b1440d842c000402c44030b1411860400801d035646da15816003076041051019150081c2e80c01542654068400000248040e68407141d03410600d03002200c406a19600078016411000c4001c100d0324024900900940009420145d09642c11510b410a560401010460f4440499406c0c0b04112182e880e000c098492802e051240241c0b124480c1c120b070340c454000050802034100009201c60454032041000c44960701502d000038010700c05040482d400080c6400c0b411041a419849000c4005040c2480d86460700403009165440c0c00c101015904408240407603000300d03001c18081410400e64101a4200141d4590014101a4035403441c20150380046500100c6550440c2200000c8030210000c002072403403040440c1001d006140041c1420380c2c0c3d511381c030880900c20f200e41c80145402a00d1618 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 211669541 1250 211668291 211668293
    0x70b09030a0f051e03130206070605010501020d09080d080604060e151c08030f18070e0a0605041a12030f0a120e010504021f020a0b0403030903021b0a03060209120a 72
    0x1032654442124000003401e2074100c141454020002d844002c6110200014011607003160110107a2020300001440f010103401200165952002420343c1ca100b01c0020030a5403500c0006803400e105c1c09903450034841420024070080c1000905550503404a14240304a505c0c1d05000c5001000240c0055280014050400505480010104400e103c00b07540950082d500c00391100f00b03c1030220703002000c102d010000718140c07844080c20a17401c03800070280c031440c650001d0541442c2401580c030940c8002003980812403200c0151050400910301540c4c01d11411030051858402c425680b40308a100b04401e81c410301c5107102c10030907038589400c0003042681d80c25082030080e041031a081002c03c0042d08042402d1a4103c040c050380d0b005a501414003640e000c402004102508a070881c1c4134118440d0703008450100703541a040c0744c041c5000f9240007c0d80300107410002d0070040d108840e030303108940d40e150800464545403a0300f411a13803c0b910040c3c44007071080015000c051024904550761003018030b000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 211670791 1250 211669541 211669543
    0x1030f02070302150f09030a050c012a1101050c0301030308041109010f05040509010b10050703030212070e0f010f1b1704030501061701060311090c071a0a0c030e03041208070b09 78
    0x3d01300d404001c8150b80b4565030f005000140c034030102c5400350640c00502c410162980104007420580c0c1c51200042015066002c100b001c0382c20b901c40030b0600002c0c038801d1003211030300f040304403004046586c000e000310324116072440d1041c88184401001c0004c0382c40010140441c0d41c00100920100074000c0c0c0d41565510440ea00305030701800f42d00c0c41140b6020210707a440f20144189091312401070074002d81e050703a401e02030310942c00905007234003410703000c2141c8280600d0401040d80709041940b5286000b6440f042031188a004220305107040c001c0c864501248143c000c00d1120200f0b2001106444810681c50090b403684000c0d60400500500400d01100300311064200e801628004d82c164200040192105801c0e01e2051001030201e4104500d14003850402e00300b201e52028590b1072442ca8115690345140d5528490290008801d000906121308640240a40e150410305803030140115440c1141181d1a485503125102c2c048011180c01002c00c0041d100380ca0401e90014905811803070251042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 211672041 1250 211670791 211670803
    0x1406040b010206060a050d020111060109020403060c0201200d090f0b06040b18061e030631020a0b1605030a050a09210303050a06270b18040b0601030f02070302 70
    0x1510540c108038280d8515403002803114410800245003214162a00782440701d02013001c1010380c1045400381032040e00e907200300080350080545490060b61640344d41003900843e0380f80310820003164101404400c4407ca00e2051312100c0c1105a00655125a00740c6040c00802400b40024503c0d81000c20203000e0001648a2511520007940d0030f0140b44031900c1000340351900a09080401844400031500354100690380c00009140d5501e460308180e0442c0002c1d00d44502101c1410280c0712261101450303003101000300701c030b00d165150004100711040e0700248a1301c06e9070280b154040804076402c0b0360a0040d5038480b14050b000300c107881d0b807002e046000410b680d200313040c4900030031140d48000800d4201b4419081140390000b601500c00d0700c070340e0703011005404041c00c940111500d0325004039045055403418100548240b40c40c900c100c0a0f14000c00aa504148000e03101d48a4910403104451003000ac0399402540482c2c21a03003551940010b0b00144501180301101e90f101164a400f055000142 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 211673291 1250 211672041 211672051
    0x4090602090f0907050703052a0319030b0307030206070215030106090e06010906050d0b0406080d02030c0c0d02010e01080405010f0204090209031e030a03090309080d030605120102040308070201050702010e030114 93
    0x2c0030766040324140500484007402d8070741c1c2c07001810400400010902c550058242d201202242d500042c0d0744a100c0d980d000f1a42c80d0100752900005103c200104c15a1050001c40800b42400c0c81003041c1000041d4032251a8071000c0e00504000450030119503c5001120f0500c252491700c0c0d0300ca50f107a440003801e46505000d50718941a07014042440340d80030b080c05104071012544d81d030340b401042101030009040520700c00c0750031a407a000d020440c141e0500c40c0c41d1010025a0086495004680d03200b071a049807024154050b00d040c2403400c0c00750342e00082441c8250703401e01b008400c64440b442c005005001c4550080300e1107201042c0441d501240740c004240c3c000d0700714110f4081da04d000f04c4400740c0015041a03441a607104201c60022140240c000071066806410074094190340d40502e2030401c0081003074103002076a40d65082c40145804010107102e1061880214141421542c601540d80f003000c602078180722002c02c031041107a204888009001c50003500902085444040d007008403c400e940e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 211674541 1250 211673291 211673299
    0x60e220b070e010912110d080d050115030f0509062a1804050105090f010510050904090b0906010807030507090b04060504020d05010509070518060706020f070c0e100b09100302090409060209 83
    0x1800281000c0c0c0400c951217a2a00142842c201079400800c100010100d400102d0b0b00440501c078082d003105040c81841d00900748182584400340152400078112283c821a100c0407a180c0402d0244600000034541d601c10700a2402060741055900c103030148559060744528050400a8030012240318103080c480307540800c0d5414042a6203400400038801030480b01e0242014440004201614202901c0c5070348c0042070528034a0119010045004d44801071800c0e545da5000206025200c1d5007082400d0041c24010040c100d032034110341d20182c6440c8584030322128952035119401903981d485c2e00550050000510865a4450301c680303c8000d00401d01c101485140d1380c0c2c0000700c0301800b8000315482a40583e03001107195840b001041204d4200c5203050398460307420b002c008049514803008250180c040c0030482d0115190000c611904000100308402481ca050010000506078005984462000325460342d00031a0440f0304038002c2c0241540d50782d1050a02950741d007400150340c002c1c09080c005031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 211675791 1250 211674541 211674557
    0x92a05030715080f060303032e0e040b09010c020615011806360b0d0f0203010e010315091e14031801090b04050108040f1103010606081603060e220b070e01 68
    0x840e03100c0c1010b005c85200d40c068100f000014024451111800504000c01c40400000b1384c001d14180c00b40102034004c3c189600010040c030040c442d4035907002d907214418000908c446004440001d40710800540782c4130101c00b025002c00b02e103a0050641ca890203580c2449404059030300c050007422201140403c0c015400e1944241030100c4004641c4100d06501003a0b907500c031890540c002103164007529000600a594070100031160b0340d240012341c000e10103081d14100a5040d401c0200d51306c04d1601034203030880c1c0b030080f020001483c407116104d0480310525071300441803410300300091545a0001240340b46d001c0041d602c800c4ea02c1082c651402d02c4c80a03a0380c0c11406484441c100d00d144154040d950120307481000040c00904002581c007500b900c2150006000b1002c0070100b400c1d102681c101d8404a000c14040000c0084140003190f6030620f41c2c0f4090000c41d10305100103203100005001c1e442101d400008818105041010b0b040d034030b5502440013410b62400400003021010b0314601a40041e4100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 211677041 1250 211675791 211675801
    0x90c0907210908031906091803080108060f0f0601051605010608120319020c0a08160201031a0d03200304080d08060a030503040902090a0503030d1a04092a0503071508 73
    0x1d449903002c5a58400071003890f5442c0c8000340846290140d04007125180c980c0000310b0711040c28000d444d9204c000c0040c00f00801c98030328001e402800140c10a00665100c04100440c1001040705a5000601c0281d00d0110741c031400e00488152040501024104002c05050303010080154010011217039214292801411002c809882c2c0d4842a10180300000300da481e1000c0814240d8010902d00150f24100da21400f104d549104c502d4000e41703503001c99808920305040555030140124000b41104c0200380c03100003c00d4000480404440c1c01c0502000092208948200c1c4001c140c0448a031060382182d031260340e21120329644c2d60910100000003140761004c0b80c3c003414404944000e503a4040701440c01c180c2400e10500080d044100f0607980031010b20b00000d040c1d00d080c8001c1801d1a80f1480c08105051040c2900f00f01c07a001c0641c9500480c501444100800d06144462034007076805035841070000e24042c40202c545a05802890703050040410014110b40f1006400b840d8003542d0f1118451507440b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 211678291 1250 211677041 211677107
    0x1401080c041a0906032b14041508060102030f07060608010c051309050c0909010303020105061e06090105070f050106060f141e0904060b040602012310030308090c0907 73
    0x41c081480d0800600410301c01c0c40b61030802d072669409a00602250f0b001010f10000d40d40c021010404000030b5030b1800c0e00d0100c1e0716400b0039040f22108818540034a09850721104044882c2d0100217401003041520100c0c880e03a10a008844006500c620850380b14002810200001d0206210705041e0703600c0d0140140d035241c01001035800607001c0c80240103410b40380c81626000780800a0402442e100100701000e000d649030031030340d4007940c040d0f80005400d15200013803110980d04407a080d805540840d00300c01465a540040303a4011100b880c181e038035001180350101c10840c4ea46d400800702d50a080000c41c0d003a52004483c0c90191590f5182030300d1000035010503140d48a6400e10341e002c2202500c107032141284442c001e100c4108060710000d1083e0740d548001885030070580010005035120401e26400e04541a11017031080c04c3c0814411460810216069052803940720090038001c02e00c000684d00f220034001940b40c0300c8040e100c401c1c01d00d010b40303000780103c41d201551a0306d00741c2810313840d40b8618 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 211679541 1250 211678291 211678301
    0x60604060b031605090301090b060108100e010b1303050102180a0605030c040b0315040501080f070501091809030c08131a0703080f0a0b18062b060c0e041401080c04 72
    0x480901e03800e10b0354036115462507a00c07400d050110309001040103905c405403024070880700441d00a681e0608a41840c000041c00030001a15a0f50702e1101644244100c0362450003a50441d0144000b190741c800080f07181e0303000d2005c00e0b4005841035102040c04480b15142e2403001c05501800c80b042d480345a1110030599441c0015101d00c004000107006c140b00c807911020007150822544003002d941c0c03488100009003a11f1098011107143d800500c03070a0740b61142000f403170003d01001d003481c0075068103004802c0b00e005114074103810307110785901c1c48609141c090300d802c43d039181d0020b009a80c0d498050140d203c140c01c1c1c52044181c661603004180300c5014108007074645e480e515a4424109407078071110451a114060a00c029403540d41240306499502c205442c00c248003070f14002460742c608401000400d0082c1000446a4102c190392a494085402d104119042d4031810001d201501c402d000c131084122080620381180c503103601002000040ca091504a13064002150341c0041003000340001d440c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 211680791 1250 211679541 211679549
    0x50708031c0b060708130501030501050409111519051e0403050627160302030105060a0501021e12030f100602010e07052e0f080901060b030402041d0105010f0806060406 74
    0x844052802440c4807019000007040400041449040229a80b00c0c8442030740702c004a41203440c0710707000c200080c1d6050f004850050030100c40801040c08980c450391040301d002000e03113100318420302451202d20488000e0303070105403110880e14031407500110080c10a81c440403004103039210150715900141c01c060203c500f62070780700b4080c010030b0310f804585622103034001000d841704030358802414440c038404001320109410343c004074094940c40c500606003150307000b03080c3c5c2d402052100d400b030200c0d98000419902e48075101e4109200940d841d01064241280401c1a81841d0000001c5c00f44900104151130b0241d00e40d0006d0000341665000c0507401c0310012959130070140c1018004024500e03103510b000c514001207180c111030941d2401849802c65090340c03036138008940301000c21100d4951000e112507104c0000b4000b0400035040c00311400c01800b0041009105986440d07035440f4009103403a022200d17000c00301c028030482d40c54103404c1c40c0300800c0303019491413403080000007201d507d49405040304403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 211682041 1250 211680791 211680817
    0xb0408040e011208041502070b0d0207110415150309050d090303080601030e0714061902010c14090a1703070210210b09040813030b04030e10050702011d04060e090a05070803 76
    0x241b9040300250403804259019042d4018181c1c0040c45181e501c00405c5540c0c400c080050344c1d9011807600340004065900014005c52802558410241003040350300169440104120191302440004402800c880701b4020403d0007109816154190054480002e13a40b00742c0b0340c500305540341c0c1d004404455205116403410fa01031102003004000d074800c600d070700c0e0001822262504c0d4003510481c5882c1c100c0004000140e54030040c526105d070f4404030b21503014a10407100e601d080c3c0000d00050300f0050500419075101d501c0300780304043c11001c10489802c1540074102540b0032707604140207803842801d00c000c081106c550705104031600d40b5038840d84003034240061180800b910b0703d444811060b0449000204108070114011001c1850070320180d10891003548c2d08000003602c1c0742445043c07180701d500b12041c840305000040060782c12440500340060740d078071075801e005401d00000f400b6002540c003418080d118042440742c055030200e6440c40080c010b0f23084400c040e640f0a0000e07070700c3c800d074024032071a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 211683291 1250 211682041 211682047
    0x318140d080609070905090c070f0803060a050a08070504050c09040c0306080607030c022817030403030b01170f1005180916050a0b03041104020f0d0b030c060d1104030b0408040e011208 81
    0x1f40f4140c42c20980045040c0041c0b030515115079500480140300e5082a034a015004c8100b00f100c1c540000307584083c03c1c040c4c4038111841d10f0704080315503440c0c541c024507118a4032540014070100c0414203131031000c10001c106000c02500780f0f02c050700421490090308506d0040c0350006038168000d0040c0083d200c0e180d402801c918a1006101031088000046205403000d030300042e1001c14040b1045000d20b2401a11b030030780d241000c2c81c01400321000150300b103050012004122010b200340d600d190380d000c07210410100d616660019035140c130f107210f50040760307205034207000c1e281580c000c1082883c0b0507043c1404844040340051401540c00890380703d002c2d07200c0c0600c1011300c205c000c0100915000b6115035101c4500943c0900003c003640c00444800350103420204118404060034040c0ca14a900280c2c0070704480200c6e003020984520481c0f48010300700762101a0b0105400386881258011900104040c0b154282880e041d00140c1c8544680841c0d4904007002080b91010380c0702c100300075684003010a103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 211684541 1250 211683291 211683299
    0x1b031f050f1f050420041d070207030c090b031608030706050a05010f03080c1618200f0f04050a0303030e100e0c0f04200301080709020c0d0318140d0806090709 70
    0x1025107005a0b140d507903654804007042c3e41d400703c580031b800030b0f00c8a503020031044041400310851480c4020814011540000d10801c04603840c45c030044141c5000c0302c00031a13090825004a407508803050510f084121090400240c2484084090301800344106014419070b19401d084105960342030050f1800040308040800004e441100100f1258000e04151482c0081c0011945140347e02913001100020034036501e200c0310381c1584115010f00d500c0d0f21503000108004101002ca501485c118060400c03400580e441130a141041a1001443c0c01482c5201040c0c41c3d14008000e840f84450076507485c0301d02d02c3c2d07804a020403401400b05819565000b40f96000178401000191020810702507001592244030b01c1908500000c02041800c2c00340c100da40d20b51404c2d1401e071400c2e00d46c0e88422025071052101076583d08012484007000304d030a02e4003180c8841c0315071701e0009000c802030009126940e110b540841c0020041440341c0c1d20310340c54039140d40554400003400140c1c43d007100c03182e00082c0e4500c4144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 211685791 1250 211684541 211684549
    0x1e1204151a030309060912070306140c070302061605040306020426030415080c2a0d031103061009050603090c0103050f0f04060f110703110606010c051b031f050f1f05 73
    0x200706c07000001c101034260803503200e40908001e441e03042501c00e141c6401d010000c00700c2048040fa00248018000342c6400a2a100252216030280400d0204540f414101800b1072098040d103014540245045544607034440644c42c10349001150342603040304038510b8000012012040d103086030714000d43c807408100552811607a0720002805a10158001d01c0a410312124414040d11039540850520854041c1205154501407000410720209030a0000402038800e950080c1ca40100058035014040b150a40c02924162074a812040c1c0003000841000501e0b1000140182120700a880401950301c5007842906141c00850b81031407030005840c046000250213a1010440140d05800014030600c040f82c2d4005a602044040e400034021614909032042d0601015800c0f02003401c0444a000c07559544584034541c020704c1d100e1a05400e42c4200c0d198030148100a241ca480340c204261000d00001210700808099408030416111480050044201c0100c402010030305180a1510989005c00300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 211687041 1250 211685791 211685797
    0x103150606050a030e1504080a081b04090f1808070c06080c0301150207031203140a020301050d02060703030b03031204050c0a030302030906090d02090109021903111e1204151a03030906 81
    0x30080d8406c0c88540145800c010520364003452142ea10556101c03116203009009107005000c09000003442c4800105650b80c1ca01150200c40c154800400c5404000d04804010f040b06c200c41004400781d03981010422002600030321440d841000c42c503c00301c2d214139040315090011201c00040d8542003005000c03400301a03046c4048111340d441140c9505840c2d644e01400d03603003004040004240c443c510603441000145406501c01c502d03480031419903161000241c5143d81488003c1e02408001584c28181842504102c8041e54094101e035a00c202d500c1002220040c00c9034142e4076030050012070304480c038000c01107508880c0c0540c020747c200381c00d1208200c440d604c488a9a648920010340240050311065030007030084c10840070040e100c1c442525a03450401050800c5001c00d89001c006100700d400143c143c580f00d203514010282e021401c850066200c1c07240c80c0300005852500340420081086140391200c801401031014800c03005000368407038100344050075040d8160001e21441d0080d041140c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 211688291 1250 211687041 211687061
    0x1201060e1005070519150609020405030f06060319020316031109010e060904170c0f0304030201260a050613090501050103050c0307180e031c0516080c1b010b1201050103150606050a03 80
    0x1641c1d102c6c3d001641d0074000ca6911750f000307500721074001c1400c120310b240a00410490340040c401904007441d111001907283d80c0c040000405801c042002c003805e540701040b40c81800141100c042680070348a061151700c15503c44030951250f00b5240022442031038071312416029127400781085600d40c8880ea240401328040c5020500c203c8018080c0c260082010000c1c0c007070f0807a006d0099656a0305500005040d00d441d5002420800c070141c411040c42140c1c0c000e0154007010310b00d0000740949a860008282c4018072003041c88240c202071141d006c0c820103500a0b81228820812150300200c00c0b024540c443c4c03014424002c0300019444010420403158000308440306c0e2150980f850320101483e08068060890508107030555180201306550ba0011018296214541403002c02440c2c010318034100c510480011500344294500342800c214001d401030303a54150014008540401c45a00c2c0c0d038003c1009201c2500d07810030b440300402c4003013154400c1000b41d8107159101c902d04500c2c024154060060456 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 211689541 1250 211688291 211688303
    0xd1401031136071806090f1a18030712150605040c020c01030f060b22090203150d05010f290d1110020319053112081201060e1005070519 60
    0x400c01c030030300c12580c060341c00b80c0010b8035201c140504007442481204150741001d0302303c0051288840700e002c10b4a040d651a03000503100c2d1511080440080307420840300d607221910400d582040801041581c0d0301d881c0d046020340070100720319986c41c1e04000580d288102e002d40943c00c0860701c0d01d030b07651298001c050461448140400c040f5526080d441039640306105aa4002d454160200f42040ea80019080100741480d400d50442c180411100c503400c0c03080340e07810b10410a140725001000005e400c1400c410406000400a402c4840ca1701c100c11034045185209034015189102d11901d00000740f03401c0070750072160030000220f00310184084510303100d103100107501c024802c442d041002e100d41c20110030325940c1d91680b202e003c0c0480c1002c0d18551103551002c1940c5054101e520300144108008441c02c8603c04010507800c0c0c00e0040461081e0200024008800300021030b0590300500001c11180d029a03922160302c403400001c450340e005070304008105030010403008111643d4800105882c81c0940307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 211690647 1106 211689541 211689557
    0x90a080a050d0e060108070f0f030f080304020a082b0804020d08160609050d080709030809010507111e030601150e060d140103113607 59
    0x9680242000380110302e400000c8441d42221038a444041c040d90610b5840324100f80d1640700707138003950448442500000a03240c082030000002c9a401c50b02e00c5288440c2c958030402141d001070401d0b40d00c40c0c50524082110b05c1c00b0702c41c0c02c0540148072522080b20710502c00c09010403500f40384000600030b176401080003586500c0714940d9a264010240c80d45ea03401315000e030204036200d207400b0307001503e0240716004201c800244400c1e41c90703007a141d010180d0707115281101ca038903160200510304c030300078400c18400e540204050700c0c1c100d1147e08102143c00703240000c17510305c1d8001c000300c030a1500480e0402126080511682e40540030b00340c1361400780164110f01410b2901200c116501520000680d1220030031a54401c144110003800e2200c0c80d965a0f00b0915805200e041c0c90501c210219940104a015004211040e840e10401c2e4501108240d03c8070b0342c2000d100030b0995040c49440 = true := by decide +kernel

theorem cover : BRFrame.Cov 211510791 211690647 := by
  have h0 := BRFrame.cov_init 211510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 211510791 ≤ n) (h2 : n < 211690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
