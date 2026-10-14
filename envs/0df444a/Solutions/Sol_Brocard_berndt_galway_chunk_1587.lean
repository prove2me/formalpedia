-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1587
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:43:32.760011+00:00
-- url     : https://prove2.me/submissions/cdb3ad38-d1b1-43c7-8901-f44cb1557dba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 285251798 ≤ n < 285431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 285253048 1250 285251798 285251821
    0x80a1806050c1203071b03030f050c04080c01020d05030a0f06080a0c0f0902090f0402070201050c1507180807050906030708010e060f06180c030a02070c121202160909020109080d03060e 81
    0xf21100000a1b41c000d0f8211203031040004100140b6200e0f080100720f1010f040002e9054420441d03000803100d4010030200403401041103820500c0500780090300d400c02c41c814005050f0311006003007640c8983c46035640c007c4071649900c12001015030800341c0e003408007546000820001140710750201208882e40101e020040c6100b15a070140c0c0c0140040c001706650300521020b9002140182e0600c032080c040464610810f101142902810303c0c040700451600580107449903030f42c54800a10910f115006014550300010810141e40e011103000341c1d15610f03500020314000d4241c201c54040e500308403102903000c00005105000f040a501a990b140d034440381401500103041551003071803507010300840c058502240c021900184000302c058034106450300c6001c103000310356200c030341e1140310300840c88103105482c104211022910b1019103402e4108940700317200da05050080d218010743c1d44400004580c05040758000608201c4142c8110100c5500050300404003480f0f245121001d0700009040003102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 285254298 1250 285253048 285253051
    0x7030b0121020d1d07120609080309010c091a3a020a081506070f15020f040509061008010b0a02030409050906060301060f120311101e180f080a1806050c1203 69
    0xc0000406070113160028501d06c04241035402e4911596404803000401e0b84000114400c80b00503001164480d0100e20040c9900b24a910034030b001d00303003c035951000d800824221400e180340481410401c81e40200c01c0118150002c440100305c1010b804201d44114881d000b03080c440280307840d4540d480c0e5407440d610b40303030b0f421071103400341e01c41402c0255070000341d001e1040d0b6000300c1c0110540b0542ea2a2116104c00300d03442a5044d403070041010404000a00c1c0014031154840d600b40c4110500e00000d4102801d24101800307440d101c00b170007185d80910103100b002038400a100c210428030150610340206622210190750107030281d401d01401041040c4a00c10f00e6080f19034040a900340761405071001c03901c00c0c0700b0000c0d180c101d009406603503203090840c4c068194101c204d40c5034526503200440c001c030210703182d44154000c0e20000c1c0c107020000c519040340b00d02070703290444482e55444011050883d1003c4a100144004400340f41022a110364420080c19001800328104d95840030b403611005103a000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 285255548 1250 285254298 285254351
    0xc0605011401080f1f06020f0712020a05120312011403100c090b0c0741010c020603180f0f150c0412021f1d0904050607030b0121020d 59
    0x3520b5003c50302c0384403c00039a039480000e01820251710680c03416528135102d910f40c80300c03005900c05035104031500c8051041c00c0007400c604402079000b220351340c00310b054200c1e00d00c11f081c4100d44110f40001e401c4001c0c0120f488011109032100025a1152084010030021301c003118000c3c40b0301034814160300c100f403007009004805900c40c91103440c03904007a0007141d44080081c81e0140100f00000a140700380c40207000d00d8140d0080c2e242c0703041941d081400302c808101d84641c08881401c441c11402a41c1000301c80180540548603659284d64414200c031036444040c0b4401500d204404c9500c3c07a052000c40c11000b000030701030584842600d040103014850b582545c8460080100b000100f058040840c110f290359403010700309100060406822400d010445610300b0301258000701c0801c404491800f400117401e0086680f214070f81803070303211150b590800821a1007850365801c04a1507580c02100f00e00400c0c0d4584800031180c40790110007070081d400c0003201d04100e50402141e10700c808855902c0303504021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 285256798 1250 285255548 285255557
    0x30b0f01022505030a0501020c190c05060f0403080310031101050a0813240501050112090b04020112112107090b030f04080405060703051c0513020d0204020c0d0c0605011401 76
    0x8800408003200c0c0100e419201c0c4000010080001c1e00e0344041c0a400317a8180940001600d0f08840c000c0c04c0d04100500144540d08029200c3c40741c0050800c40c2c02105507a000d07502c0d5503d80c1c4107206005000e11498002800c00d4201204101c4034001c46002d42060700d00c0b03001464501c1440800541ea14040ea070000d1012861035000a203241c1c0d103800842400d1405070440100c8040310004682050710361800e05065603444000506c0300c0d5820803186061312070780d1a0f0400891101e915611110070000e00000e0400c08102500c0480c90110b800c03081c00f80440380e0036169607009030050009000030381c1d8004102c4d500c0c0040001d0b440c5014459100c121746031921500d145554020004480110041007110781403028800414244ca45002903d1510b120352034842d0341c2c034004080000310428030500c0540c041d04000800034451916042901c0555040c2d5440c0015041c92000030081e0103410802540361080a241d4101c2560044141a03814010981000f0701c0c0d0720381d9443c041c08070100e034a003400304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 285258048 1250 285256798 285256813
    0x100603110a0c05100507080f1605030f040c0b04061d04020705150a140c04051e010e210607030b1c0b07120b0a0611070b031605031003060e030a030b0f0102 68
    0x140c0500d00e9240020f2159003924600c80122940f0022140191034410020f006541040081d2400b104076540024100001060780c00c1081c00040072480700034103550502c1344440c0403408021609650802403c181000c003500c468455170b006200082d2130307200d66200b9070008280015400d182c030803070b040c00b41c000e03014020160f2484000e4000d80c0000e000010840e580b20461175035a0158409280602ca40003d0345035a00d10f01000c02890040781a49007400c08140040303039030b2076a0447c000c0400817605031510400030903142400f00e0316040d0352003100b20f640030b10400c20590b10382c9076011b06454142124101802c1403c851881000010400018600c8081e007000c204030601402d1800140045c412005c2522489400172440c0c0e00f000380d1108002c10100e01c0c150002d03900500000300903241c3c12400904501c0c06103480b408982e04136100c00144807002020442c0452900c0d8414003840d0046c0080c800a0300c561400b5640e40c4c0585a0340c00002c0c54111039040302e02c0d080101002c1e5040503401800700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 285259298 1250 285258048 285258067
    0x30f0e0601140a0e01031208091c0e0103021308010b01091505070204110904020711010207081f0515030604050f060f0421050c0111180a03030c0311010603021810060311 74
    0x310394180380b581d502010070780000910f02d5a21800501940c8220160105d01150490141013070202600d0001e098001c0070803400c20828290a4101c002c109103402c94000000fa80141c00a200710325070500f12051203c0e001c00c0348170054104280e1034800780c0e61040595607400f022880600c50f404210300041e01004040054503050704840700ca1500d9900c009d1a10500500040c101e9000d030300d0403613080c4111800410700c1d43c0c0500c244001005002d010780760307a429a81125500c152246a4942d20303698400102e90b450301d4140d8081c3c4003000142c2161268141410310075680d6030300d4442c240307040c030443d000920006612480d403030089601100c01212014103046102001c2d001d10070440c1080b009100b04007540304c0074000e041c0000010360582e40d6684500c4165510100c412171018081d1010020030800607911010f000f450a1b014502501403600714141a0b002d8400d0740e0010354030180300040440354000035421180220014019482100eaa540b41075054400c100050003d0440900503e01c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 285260548 1250 285259298 285259319
    0x3006070c1703060316030f170408031608090a03051c0302040f0501030c030f06140301050901020903120c070f0f06030b0f0a120302150c1306080c09010309030e030a12030f0e0601 78
    0x20040b80050503a070b0000141e008408030b42d10302d0382c01520100d0076a00e80c6014454060440c03000038080c2042315141900b00301c5040d69034400e41c0c0381015180c03041803007030083c0542d1005480c041e0100070b0007408290307a00e0424513503d10304983d0880d407190b004101c89210707600030320856044688040b12070f03400300d00d020015001441403a101c1d40c03d25855002d072505c03100d2144258400b4020b5072900c1001442290300345030031030714000d0244080b623104110b00300969800044111840702104009942c07a100c401d251800d000d003a0384004001c3c020160b0118103909030000030015900c05540402260144504000c410460706090b03640244488206000b4140c3c00c900d8240c0031801b0340102e07020341d01201d0040c20344800032548115260b1010502c0a80402c00c0349a0200034401443c4c0401142408200600144580c0001c181410742d6600100109402a2007141105200509488001c0800d0501402014034240304800082c80c040b041e00d03002d2528800e88201c51102c41c020032282c0e080c00c00012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 285261798 1250 285260548 285260551
    0x915100e01020a14010e24011e080f06041203052a120a1406030a1a0a141006020601050a08031804060308040603091506050d020f3006070c1703 63
    0x74118020300c0581c1d008920100140c6403010f20420002541983c000c60143c1414001d00c0749001d080c03d0b010000c1200a007040c011410344540e030403900c0110081b90a010700ca10143e07030042c11280601e00301d046580c8004100c19100340e0041e02c520503410240c1e8022402c4440858010000c480c42095510030b0644102d00503030041803108510340760a54100a90080c454101c0c0c0c3c226610707440e0759000c004c4d041c1082026400c018141c0041102d9000c1e80d84550742410780d088561007056882000520f150a03035008504903420740305900c5c0340d80c145459411456039243c02180058480e8034000141070510b40b020800300c40c0d8020166080c181200340ca03040d0381ca844400d00758060748400b00800807030390b580300801c000d000c19240001c00558618000e1262484130540b400382ca40f80550801c00c2d91a0315856101140c0e044983e490151408800500551980d409622141540f4000080101d4080405840c002c1c6481e084540f142c1e1544070032602ca01130603000400002c80c00725640c499240703102c05103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 285263048 1250 285261798 285261827
    0xf2304090506130804090e0606131404080706090c03081305060412060f06080624100f0e011205190e0f150c041503021213020a060f030209060c030306091510 69
    0x5803400d6940c034000c03801c0e40e6007d120015282c20020520119240034a5850460314104030f0900010801d88980184e000d40108050918940003421500304400c4c0d40c4407402082c7e0084560031450b85a007454941504024400c00100f800900c2c0801e462401e68203031001c0b11902d80e40c503255410703e90b603a003029242403900610b00e5512200c01103103071241442154414004082140244240142c0c0850803a00c4641203a01a088581c121200540e204202d0408d4601a00381640812120b000484503000c1244c10082c10515160602000d00301100c00751002c0450803030203100128941e035040e500e071490086e031050590b01103001c230102c45443c51556580f1821501100e41090342c0d41500c40181280c16003543c0c0060383c00102c1400e05401c542d0165041148040103214251499021500e6940340d4010141800720329492590610304c0303501100c402a01c09004642c0f545050201e0300c1d6290020f81e03900c2e00c1603502500052400e03015120b8801507090091581e03182194030081a0380640c00e540e0344 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 285264298 1250 285263048 285263063
    0xa03080d1a0406060201140112121d0907050a0e01051201030b0417030901020d0617061f08030408030307020717060c0f0c01180308010b04060504051201060f230409050613 75
    0xa0301001d503a40d12a00001382090b030008038104084540000490030140c10005120301341060102c0440d0241501540003840d1782024103226000641c000d428452990b0701541c4a1041d000300040c5680c46005403c102040781c8803050850f076207100650340c60003401954403c40c1c80500041000c41c101e07082c2e160304a8040c03401903043d950200801d29240d03104541403181a90006241502c0745440d10460700204000744008241c4a030741e158154407204003802d1481150038003840b442040b441c0340c030340e100200341c0e2200301c9a40c1c4d43d40f401e4250710f2344c000b205c40c9000741c000e040c0c0000d04039005000608040c4051800f409980c6c1d00c4200055898100003d0040840418030400300d030000c00744035040062810341a41c6c1c280c1861440c2c000e00c0008143c00540a82d0b4041c041080368a4000080c0e0342596011140c400c04101100780041c01000349a0046828001005001400e0181140c02c01c29400074586101c40d245d0322034003071100350303040e00c44018016803080d0001101d0105442d0b2440e0014400c008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 285265548 1250 285264298 285264341
    0x20a110409050d090320011d01020118030207030b250305190612110319020d050307020604061d06040b070b060a0306051503100b0d0f061407110c0a03080d 68
    0x40d901d00d00b041c05140080843c0084e0300910602c0102070304046c1c044510142109903005200000b804104458000c09041e043c2c000031503c0360b8000e401c415025018441354480340302036400c00954603001480142c4003641e4100210300310400000803a54840c10b0a0481449800b4140e4114002c14005041d42081000341c0c00348203244116000c2c00000300381c034200a05d054207047c28000300340e1603e617806903c264030104100701443c2124203810000c5030110389000043c5a6402d110307085104400000351312030300000b0301003809038020b0304a5403142841c0d40210704c83da14000902007076202d00d0103400c410010074040c40b40003903503400c03c950740100042c0c41c02490903602d517149400d50310203450882d00c0c0503401001110350704040108003c01d000c2c0c820103014003000c99011408140800d10b014205d64680c0152106100d826001440804424243c07883c59160030700c4001c1c04006030128002c098014144100621300c0c19101060031380c1c1d0000f800c1071401c0c01398000c0400030301011f8021120030b4004c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 285266798 1250 285265548 285265553
    0x1005191e0303080609040b01090b030a0f030c17031014030c040f0b040f060f12050307080d1a030f100c030618020909160f0827070602010507050a020a110409 69
    0x1100e01034154036003403080202900310700d0080c0041c01c008200d540510010420000810b50b49040c20303045408030f40d00001c00d440c0741c00200741084210314002e0111034500001c50101984080343c1000c0718000c00c40012055040d92400c0a184420741d0301c0c0c09210f900300780c02c1c010200101194403c00310300404541c2100b0390072001c50140c60140030034280403980c5240a00050615001e40345641980c030104100c802d05010301d030f1000300864024695002428407000d0304011080085401c0f80303801100c12034450403a01445400341c9807445010002e228280d43da0b001e42e040010300c0032064110710002d005440035180380c01c03008262a1248600701902d450f4005003a541aa0030450a15401c40d000360340e5080309000d0000020700030b0142902e90006495800c0703120b501007809043c42c034480c6030804036a1142140c007400440c01a041c03103240d40d00e000d5481c0c43c0c040002558011030b40d668000f072003290ba40c100140e48500440d030200c0050b030013002445000030403450071203c1c2604001e10000d44400c054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 285268048 1250 285266798 285266819
    0x204020a0e21011104180e0304120506060a140d030c15020c030306120a0b0109050411060a030903030c02060912030a020705160611011a041806050a020d050f100519 72
    0x4044070140c0c2c460320a201d44454080c00307150750403400c40102910f030500e46502075142d0382001810481440d69104540c92840c014001c0303070000d0a03d1391a03618030168a043c0291030304000c2e60b40c0345c850b0703209c07120001d41d5550b0080b0708c0d000440000c150651008854806032521014400e040b188003d0094028a06000c107101038805031200b980115100c0c54620107102102034901001c000d0795000c11500e400113100c040e1a641582c0b5020740c042807503111850304000c2a0401410705500c508003040300000940e02d5400044250300a5505000483c1080c1c000e0340c550748141c81c42c40c40340c0c0103810107040030b43d00c0d8001183c215991200051415440303855560503c00030700308402e40c01c91440c0d01008801c3d1701a6040310001c6450b4000c101440741c8200d085009022101810f005503111b0780328407410034008141c581c11300c2d0040d005008234a171064045009621001440d149945414041f40b5440c4e07a00d5401845454400340c1e03403442506240810003078030340b00e41501d8500002080c01240301d10381c0e07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 285269298 1250 285268048 285268069
    0x5211b010612060b0a0504150504110c0d200307060207030e0910090c0e0409030905100807020714031c02060118050112030509061303030206040212160308090301110403080c07170a0204020a0e 84
    0x8230382081c1007680c100b80c1008107984119134001c880010503c02e0812842d80411300e84101511420220503c103a507001c614028551640309911600001c60705100f4044140c00404103039100c6d0395469080c0900c04100f00410300d05440891400e00031003001c0c00400b0382648106c0c2a9600390604083e41400000018190b800b007070b4040307001900c005010005414010502644502141480e010074541081e000b96078942d10300c642208242c3d00b03030714007401d82c40900191100604010080c000c14408060103941c0366001e200c1d0382c070700d80c4e0007045240c0055411f1003220b040e118400440400904c90352000c8601d5003011442030b50014041220342e251244484442006502c41d4000d0300e170500d0180100034241542d501110101d412a014400d2041c220303420b000252a80b0904464440718090007107401840658083ea0035054001400310604c1001c001402c0706441d00400c90f21466107034241c1c0801001e040100c2a05030744450f04010042c90f15402038480c01c030991500c501c65000100009000c08e01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 285270548 1250 285269298 285269321
    0x30a021b0c09090d0f030b0d0204150e060a03080306130615031a0d0515180102040f05030d02010e0d030e120a0f0306050907020c060705211b010612060b0a0504 70
    0x240c503044181050208664440f1420f806406500c82004029240140c2400d1990402d5654156070714140e07214403e440d9100c0d0064020041c2034841c441e243c1703010f0014002e00215503030100c0044c10a1403c4908442a0380c2c0c0455200e05680f41e0005000e0410000c4400c02c10107a203a03440841e00906441d4601c412850982e0007203100c10b80c80022168088101c4200c60140708141040c201083c00011882d158502d1128030000f655500307014a030820b120303918543c0c0e00e540000740010f0705124011955090320021802ea80c05c54025060607422960866442c40d905d400807000001400c0c02070384005c1d1002e01c00c0741500d08030006080002c15aa002100c0c0c82e02150040750740c102d00c240e2500c120b01c0501800c1e601031190b41080000a95240c40b24500306124400002e0801e04100e024424030800b0100a8003800940c441c0000306600707608858040c0811400004000c00e0050050003040200d03141c80040102004890311008041e15600340e00701d4111002c0ae000141c1600c036882502800386c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 285271798 1250 285270548 285270553
    0x12307050d1d0d0b0601050d0e03030109140f0906010b0f09030601030605010e090d020c060706090501060e071101060b031303030902091f1a160311070f0f0b1608030a021b 75
    0x592080700000d8101c20b80965500032a4144203040001d81c1c40004150440400d090442d218400d20f4810000b4003485032050100d40400300c000910751a2a4000c0d03050110f04036040729a076510342c80341018400c42104c0300380b0164005801040304940c40002480c0001c00340780c0c19403a00c0309084c00700e486c0020030b901c100c1c0e11940d100c00400c85940c110240c01e4020b0180000b8058442803006c00031340c0d96400e404a580700b03040002d40181003091b95406014083e074400c009019007642c8081015100b0411104000450b000040209038440d0611038071043c1c41c40805410708684403400082d00410080c10110180342e640d5880304056500c007085188540d405828020b15066034500001440c203860307100040d05604c0850074180d1440742d00945414108400c2901d50000c4182030484034800340031000e0a15029421010801801d5882c490381a03840c04c4160f800c0980e034034504480b0501c00c901c03445410346490710101001404010040d50010002e060160074141d04003039a44006016143e440c00300e6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 285273048 1250 285271798 285271817
    0x70608010e0601020c0117070e030109050a110306070903030e010c08030f19060605040e130804140f0a1d040c08120d0b060702130b03030f070305030a0b0f012307050d 73
    0x404200d59082d8010000e10241100001250000c0d02c0100301810000c0c4c00c3c2e04400004464901c20b051640c03d03240000c00902100e80d25003800354403460300d40c0050700d0083d001a02c0380036508002607403a014441c581d03100922103285480845c2d218013807101c11810003031004500000f0490040207140124030042480c110b41c00c01c1c080707401300c1c20b00d007541d00d480141c1410000c100c40394006040d5000c4900171031900c5410303039030088100400030100740003e00d0120f01090105501c4056803800c00c0d0402c013524208100c00541003000146a400e21607450344c490780e0707e80c40d02c140c1c054060080e005441004d12010351611040e8960409002500041c1d40280208506020480318092512441c40036030340140b60071915000b00b4007960070844140000703900d58200c15601e03203080003143c00440d404000c4079160b501c0780c80c0003441640b040c0c1d4080c0d206801c00079250700318984600f5452840c03605031119641c08201c10701c1c00003800f52500c1c40381000c1c0da051107000080360050140407151442035a405410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 285274298 1250 285273048 285273059
    0x319020c0a06021b0103180c0e1005030303040c0909301d060703110a08030c07060e070b1812030301090204030b0c0c101821031a0d06150807060801 65
    0x281c0e00350780a8001c56100603101c883d40c0304280c5200d020010700b8a0003107a13100b000703111651043e8080c00010700c034060b0074000068007803e621020b4081c8820b0134500981e034ad0341d07104042e80d034007003902c01034100d05900c04200b04c1420540e1001060910401850b02c01e00c5000d07805010030044d14040386c7e800b642018403403c940754005528034042884d1403240ca003c04084010814070f00807000c008050002050300781d0700130760b02013010012141d440300c000b80d42d07441e200c030001070541c20148040341c08505100c401c41e600500030541000383c0b0107503041130b803c040440070031101e100d034000200d0350041e41c07240000c80071078001c2c001513010301610000540d07201c0c9140351032210580d004100040b504820b220362100b940c40071a810351583c15841c3c0114561250428034024820304000050451038040c850321204e0b041002e4600d40b842044d1030412000f88169001007070310211005203036101184040040c001001035020103290014020802006900c5000103031600c98139402200c003041d14100100700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 285275548 1250 285274298 285274309
    0x41a0111011401030209061219030f030c08040305130506030103052506050313030509090403031508160b03040302070317190e1815041503060c11060f07020319020c 72
    0x1440490381008000802d044103105a000606000c028070400d000c1001c1840c40ea1140c1c0749201c41c2d09003a09541003000c079010601d05424100200b2404072b01407071a0300e016203000e4445e80500c808581c440706140d54655a048a059201130075040e1983c1c44600c01040c242c0303a41c0b02440c040c0d4800c0e030007803088240c3c42808403040000e0041e40000c1050758442031054681c842c0603240c01030800c018500c00894140b800365240d009180301da64004130000e08100038994150050140004515140000c003a04d0b0122503803506001c2d41c1c14941082e03240020080701d001800110703440340c0203105071491036480b0381e12800c5d8585c1c9400c90200f406c40104000e42c14415040340a01e10701ca03182000d040d241e40c5100407602c080c680c1414030500f1044a0000344440100c01d221024640c8014800c02c80c004000300c08081d45000c0d0b0005545c000d01d4819108100f0740502100b03601c00c1104c50007003940356600c0d10300203072146005001404502041c003469000303411a1000d1095460140c018001036002c08040c402e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 285276798 1250 285275548 285275567
    0x50f07030b01051e010c0b0405010605090f060117070c02010c050f0102040b0c0706080f0a0207030e12011410050f150f0d05040b06102a0b0f090f030702030309040b040b041a01 77
    0x1140a0320711900f13201c13660f8015181d8042240e002d40700d4441a5a641041c40c01001e81c0e5000c00c0d0441845802c002603034204c1d1003541d2140b60240ca46030200002403041e00399029080300d071807000c6407041c00c2c0140590300441948103c10303c43d80442d4403040303081600600b640c12991001810781008212412403407001c0c84030401408162030079071500e2502000040e68080040d1a40111a80c00180003062510440d0300804400c0301503c0840c003240120245070080c840b8055541d4508924000300d441d20390769014010444d1070041031010b002c02c0050402003408020001c8541240080000403041e51000c000340c000c041480074000703603d00e06403c0210025000401c241c0c4202c0103940010300c0c094105420251360004148188440d540b48104601714580e030403c00f40c919400d9104100070011115001d0380f1a24130360050b100c505a0362000c01c0e9a90143c001c00039855001841010a85c1c140f661041e05420030040002ca82d5400070004030382103540228070b012940c1003611219030303113580014180703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 285278048 1250 285276798 285276829
    0x10203160c0b060d0503130b0d0c0e0312030915091c0203031017031c05040c153e060718180c020309120a0506060a150309050f07030b0105 61
    0x200e009855a0b81c8002801c00c0050030719103c2c0142c85910400c0c06801c01c02d030390080d1696403000003e240c4a040126803900300c890403d462504000034006a94803501a070359051070080c0080180306030925500c2183e4000925943c0184620285020310450300c0c50458000c40c0c06401030039150a00218003207803c41d00f5040d42c415580100180030181410100003c101d400940302c040c0452496001141144540140c401110081e540903440350031a90b40103d00847c81460382c070314001c0e035900c01d440c058800c001200002c00c083c0c689a130030100500041011005084490320540400c450034480142e4807641c0081c403aa01071410400f103036400c010030b002c003080c50030301700704070149040360b00c4507014840005c900e071241d124070708130100078001c0080d10751001c3c005000b101d50b00098034038141d0320707080c0324804e450f60720a5502081445c01c0c01000a0156205c055003940c100300e13054026800742c22120000ca42a1082941c280200c003400d0100001861042e081d421465160200308001080d010815 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 285279298 1250 285278048 285278057
    0x5070507180f18140106122a0510080a14010801020304031d0604060e0402040f03050a1e0f0308040213060603020a12060608061309020604030303143108040807060201020316 76
    0x400c0d07420312400b480c601d40c10368821500604c1d01c09400c11319001d040580e000102c000c0c641d071617810800030a000e682620001842c101c120090240056040b041224492560400d41c08800318030030341d2080005c5a071052108a003c1050101e5a80d20303d04400241d10100d10f6035404000e100c1056441140800c4015001f0f034800c4500000200184c1c21788510304c035003c00c0c080301e1802c18603207407100c1d01501c1c01080e03030f1411103540c2540c0c7d00380141c40310044a022a40044204040d60008200145256110743c0044c9103401e011440e41e0300761152035026009981c00306201014440b01d280d18002d40c40a4840d5550150b110082d2410140100303940c00c01a00016003000801d101040d4070820711507205504440a0040340b4080e034007403005041159000c0c0d00000e000a001c0f041c0754168020809140b14240d1030403c3d5507031071b01e40103254500310202e0307140014000752410a0000004038909594000d0346154500341d51418110318110995100301e0141c0d401000b00031124840e0703800455611080d040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 285280548 1250 285279298 285279311
    0x10120b0a06021e191a0c030c0403020d0f05010f0c030b0d1703060109081504020a06050909010308031b03130b01080a080405060a090b12040b0105031504021005070507180f 75
    0x4040d45400c10600080f0740c80d0039807200c08480e400d081004061a80003100d29100406850400820081411501410184442010401c081342c0d920031640f180e45800c5c805428036095500300302e42c00d030211b1010750710480d0000d424000f00c2c400303105d030a42e003000003800055043c4541c00084e061302c000f8000a80304100c03502d18803000c42c5c0543e464140c5c182c82000c00d1685e07699010016034a14a1070340002d1036501c542440b00110907458980f01d0b000e03500884003a0b0103031b03a645604a074036104194009801ca0010f500400010344d85001441e0003081015030416440c401703144440702500111200510700b8210540c1e40148210641024003600c40c00015040e051250b85641d4094841d40c41081e015102c00142c00c51200e20400059000d07050030041da55031040908914808100c05642c1911a02415000080c2e20b182c0013a0010f1848201c01e025030240c0c2d40c580030404d0040c1d00008e60014450200410b80015105000140160182003081d981d0003d40f0a07405c1e04560841c1401d520752442c020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 285281798 1250 285280548 285280559
    0x1205010f0e19140403050c0c0a03051504050304120f11331326030a0f030902040e150f0606030618070903050f0309040f0218010c0c0510120b0a 63
    0x400c240c0d0140075200c164181c0c0c0303507502c088001000b42981c075144190701e52040c041010b50142c0104154a0404222070b1a01011010040001e81511001740346034403440700c250180000d101007681c0103000b1425a07007031980d01c24142c2a03200c0c04541c200c41070512004400c0070443c40389826054407205540740301200700a00c6220341500003203101c000c201080d13910304c990504ea0400442d00b210f43c0c1c800d02d08008075074a501403840d00c00780c502c00d52101c61081c1000c5015450000c10b54454003c1595807200715201c1450980003040521420f03a0025101d14246103105410400c22000c03140801d0b01d85120301e812540001d030050301518452142d0000c1003800525510b98802040520440f031a444c1e01d03031a01001a5604402607000038928000c00c90070308502d80010018000086007640c00303002076240510500c00700d1255040540390011000c4001046510540c41c0790042c6106900094909440d5000a0b0448001c241810300140314080e003070000070b1403030040004607503095610808080c00d05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 285283048 1250 285281798 285281819
    0x3070b0f090d110411070b0f0c1819030503040f092313150c021005041505070c050f01020d060e0f0403030e0102120f010e330a050405071205010f 64
    0x14895101d41600031603038041c001c601c880b1440f2840000d104100c040c0071049503481a40000798240d81d030700507a5000450741c8000105040c4141e0100200074078114841d000386504540c0a90125040b0701c91a2600f410300781d14003503800c05140a2002107455a1403c00760b42800491a048111007900309900c0e0020505200700b124002c9882c03c43e0005244c0d2212180c0c001c02040500c06011024018410488482290f00c203030300c1c0500c42e600380c60f414480340c1814000c0d58000d8400629006850402c10361200b0340764071440d004030f500c0c90104426041629540d00d0400f611031040041e941c00590800d11480034410f0078010f00211104001324030b09040381180e0a1801440641415143c1d01601d540100a504a4413032a41c041c1d0028040d040c0701c0310b00460b09409014070110701c0d8501012a2071780501c4070060818031a030751039820a41c812040c64964200d043d201d159001188101c0100d11691240074803807040c01f4994030150040415030701c00e01500e1043e2703c44001d075030b10900244040b1030179 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 285284298 1250 285283048 285283057
    0x106050c070b161b0e090309210c09040312180209040b04080405060a09080f03040f0627121208130206070206070203070e0f0a0c05090103090501110409020903070b0f 73
    0x21400b50b1920b07000c0c050140702e100700c52450010000101e2181d0760700040c09858052060310440f42c8211019507402c10750540d82e10a01c00000e0740059640d10601400e1f0752400008442c80c0404150741c0d9402c00200030411020301036408070045000105403003100c060380c0c4162a40300c107088080301030450050300410a4803102910182c03408a030240001d0600c9140d0084400515010301703d103940716a0704100508003403560060281d02d0240c2403062404041c0001a5018bc540c4511070303d5000d8640038041d1400c0c2d41c44494000311507003045800e906014401c46000080820b9420030f9400451498000d40c840c040400c1901809940800d0101c00c2046210396402254141e03003490345c1c0c0c800b500001700d2a00905000030f40c0340c4540c01000c03500100ca0a06940a104140d941d20440d40701c9540c1c00c41520508603c4100140e0140300c449403e41c821b812690704a03010310000210902d098031800c00c9035015820844040c4e030000f90003803050404020380001080300444050401d1003890411106114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 285285548 1250 285284298 285284309
    0x160b0a0e061b0a020f03160c0504061d0a0b03102301030c06050703050403060c2a03020604060c0c0218010501110705060301060302070c0e07030516050c06073f050106050c07 76
    0x40c086a1088400d0007002640482030205d02200d0311600c0c0000c40c400300202d51007044501c3c0202d100c0c0098241041c0c044d001c2901d81403079002820810741602079840540090420344130a0321044100c80d2034400b400718020b0000740310300102d017070072401840d13801c00c02012021a5503a46000010408600d90845030f0040c0c44040c40c1a0740e491400307007000c03141ca0041d50000ba18151601005090799a00700a070360b03080c00d251807884510760b81d078140c5c403102541502c280500942c2000c00003400044582c0e0045105c0d500c18242098614205c2d000301d280c180003040c0381480e65000b51f0041c407696070040f407840110443e14000f0032040d810f14011400c60701040c400c1000b45134020909030100094540200c0c060459044015141d19007114018064441a548640080e01103100140d642d0b200710f0480e450b511180c402001191030342c2c0380c02c641d03180c8810f03850001d145000e0392805100000362400064150765241a001d2814045103610440c5c4041e4020b80500008020958100c403000c5039607002ca62 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 285286798 1250 285285548 285285601
    0x1905010813020301020c0c0a0b04030308070e0612040302071809050a1511120a06050a0302030d14161b05030a0506070507052107050606240f160b0a0e06 67
    0x80340c03035610345201c1c0d1210307000035410f500200c1c0c904148440054218001030084a010010300e41c0d40e0310628940c4a1400301400084400e4005000300380244006091100082c2016241c9200301201d162070100680701100140c114034070800200042c000040e0590b08131200030071855a450b0f4a0382d64850040c04001d240e110380110003050780105e03520a1503094070a2032510758580324101180d031402000c07501000b4580c6040c001043c41d003003040076030003038a42c040e009100405090000741da4040c480f045120460008002002c11a000c880d41070103c144181c071501c500e0480749410700410745c2d10b900414003d91202c245000440c03000038060780c020f282828419035694040c1445810103617141d850300e03101d484442280302c40c1c00780040201605805142503400c140c40d00801c12611060700c3c140c0b4907048150071180001c01000c1c0009184001d132204841e49000750716400f01c1c00303005000030700740c0e100340d80c0f00c041084100c41402010181501080078203418588201c0d280d01c0c205422807020200e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 285288048 1250 285286798 285286801
    0x1b100612021324060909110a0302031305010c09090608030f0403030c060b0a0f06030c0809030405040b01030e010c0c0b0a0509030d230c0c010606050c0c0919090b04060b19050108 78
    0x10b4080e80c0580c42540300340300c0c1c2005100700032820880703600c510300ca40000250742460005207400f451160030f042c252000e00c00b034a400714441040300650405000342400388140e460300c00000300c0921038060500416102c055419241261a0381158103070390000380da581040003880d00d80308541d811102920361500703004800512034242400100741040c5082e40264464401241c0c246000c6104001c0326401e40e0207012833061603004480100c800e071030b00e141d40d5000b84020301142c540b6410010724a101032500080c0c100303800e0001c0d030a41b2498101c017400b1442003040c0e18184031240581c4d41e4045418182440141040c071011a5248200d02c80046680d5507102c40365005886e9915101c0f0900e0103140500c11403c0000142d821603000110810141d8079080b000121180200242c4020000500c0940100c059440610404c40001407448030b210303408504005100c981841039040190144078072100c240b405203440001c0380c2150311903d1144606c04030240074540c1c083c0c8940203440007031030311100c1c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 285289298 1250 285288048 285288079
    0x50a0b0a1d07120606210c1e021002030a021b16090b130e010c0f09050a05120c150d0c0e0f2101090f061404050703060b030a081b10061202 61
    0x50241e103c5018901030030071070002000381c1e00c0502c41904100e002d004584115090016000b00c4140c40404004a0340d0b59030452a403100e00da000c035401c8041e40c01600c00082c14541804202c0c0d000701e44100c84668041050600b40598014a880d090403642c020101d01e44030f03414113030300040710f4440c685d01c00d80c40b02c41848490b21820f00701411840001d40500c420032007401080d01911101414500094514041c468618400c0d00f400301190400342400c0300c000c0c24001441001a40b0303050031015440f402c0c001402ca900e5520001110f03161045036961a4140008604169083c00c1600001c200c20350400881e81c0d80c80d040082548001210010403a0203040343d4090706100c00c1031941c929518045120040c807010b850307001c00703562007402d00700801e0001920359903081106507406032445d80180b1003440060420351288003c514010304a600c040c0165503000744640c040c0d80d903095141c07541c1001603142a4100501041c1c403500f400c0600480342400ca6022030000031002c00b034481c64006284100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 285290548 1250 285289298 285289307
    0x31e151107020604030323030601050702040905030c0d02060103031202040e0a02130503120403050c0a0e071d060301091b030603030f050906070b0112032613030512010603050a0b0a1d07 81
    0x41c0c1e8090100390b1107903a00d044c0500802c811060002c040085aa00040c0071001403080384e00c03c18050f16481d091524a40030701008003d8144212540c0c4010004040341c90f034200200d0070410302d10703801450030390305600d0010943ca000301040c406041c0103100a025441d140621160b020140308401a100e49000321580d5100e41140d02440d0903000740f0010b890b0f01d0101500070419a070140084441f01c480650078040b01c8001d03481b40c1811071241d00c0224080700d204061010325000c07080c24905800d0480c01c0080c19680c801e078801f00ca002d03038a10505203551180303c51819240d0813401c1c10402103181d80c03030103400c000d950441d0000b0824005031b1041b1664a4505844039960054400c0d0f9056854000104024989403000d4002c81c00648032807044044044040104d054075098240d1591500e1000d581c23a002c82c010202d09200c800d00c6850350028008034600d000b007259503000305660420520440444101003503541c09404100c0707040c020300f00f403a90070004240f06941c0605041d680c6500c02c49 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 285291798 1250 285290548 285290557
    0xf05130626010b04140915240c161410031509050c0405010201140c1e07082817010e06040b030d05090108010b0403240b0a03050601031e1511 62
    0x400351014002040ca2116032011380140c81c00ca42c810614606000c00304120302400b11854070040070100103c0307070300d0304000d1056104411420100712801441c8046408250442110544107a10250325603000c0c200c0314003030000800d61441551100200000411000c0003400b00280038903844070304803801800c00560900040c04600340c20000c0d808c2c15203540e1526031040c4103c174015801c0000c2901c0d00600c2c2c4610394060080442000c0c0780c078031030448402c8681d200e104a42a40502401803d002c6880640100001143c03070020444005824180b20380c0441081015000c1195000b4802896480040440d046d50185e9011040079600e035800100600002070916400d4080c2c925920a156000300c040c2c4071200090700c130f0318501d0382c07616514003150240788405090101141401185c9842c0701c0c1c0402d44141410801144c003d0b80c90780403981907100341d03000716000c1c1e00c2640100305010b031514403200e640c40000f503c495000703680d0b115144800c01c1e0b45801043c05555507a81d84544003800200d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 285293048 1250 285291798 285291857
    0x7020f0a0302030c1228090302040c1e02010203090a151d0d09140f090a060b040f0602010b0603040b0115020a0203120901020f010618181a04030f051306 67
    0x300d6085200c0d00d4000e440c1e4004002610080c440c603500140091081c00c01e0365200420303036801d9034841c205010610413010b0303104000700600200c440701001580351070161640b07090a50319003844810900fa01c007000740a140000302c08591040c814850200008100b004100d81c010308402404451684408014041c00c081d0910b0f1244407029208180d0000c21889034034411511250f080741d60f11900300c020071441411036544002c0c54070160440b840c1812005030000001c07440018115140d0740c0d0038215500c2600104e6841000740401c2050075424007691688400695226040d41815580c5045401040c00364489071494402c446550510801820001344d8008084400c11211002440000c0d80085100f60050183c0076550341a02814040e450031120080000c5040e42c0c44404014010101c5121400380c410401c180000810703104032184141000440840d012410903207005019181d05280b540705104c814015421034030800c0d14000c08681c120308003003400c0714016000d240d084400d052030703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 285294298 1250 285293048 285293053
    0x203010e030424020a051f0b030f07051e18040510020f0403060605030a0b0c0906070c0e0105190b07030c0f0209090c0310200a030e030301090c1206140907020f 70
    0x14003203081c1403250700540040311a411062200314000c17a258409030300b0150555022010b412040c00640c641c00800340b050329400690b180c81100000c0c1068041c3c4550301c042d074014441481a440c1500305058003955109a580010f0801d44c0440c00500c4c06202540c20100144001400d08c4014003140d403141c19900380856480380c215201c002550800d01094a56500d8801c01194509000903880b00f8150000780100b1240c0d01c0519130092540124a5107410810170b10010000404d80e284902c06010669854802907042000f407002100d5071020050f079290502e08104480c0c01400c0450f61035540610f0309070030100172030170000c0500c00c1c038010017900000ca2404204c2d11110201310171000f44400c600741c1d0012a003152801040d607880e030106841b0f15100485080000c41c4182c001c00340451a0309002c2448480e0140780d80c02c5070802d13407014410075103844500c03e01540c041c1400c54000311000d41040550306210820861040801e0080d008121003804601d00c240200300052180300c01108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 285295548 1250 285294298 285294307
    0x5010b09040623070219020a0506040b0c0610050a09090303090213020702090c09100c15110d0608120703030f060819110405040f0b040f060c050a021b011b0203010e03 73
    0x81c024000c0079424540414046410880449000d090290500800d020f41c010646c801e03001c6444c0c40b0b42021000304a9104a550600160302c2d00c4401c054401004010700c40e50311754140402081c20258000c000800d4400d4500040c0280d940d564042c1c405daa0f00c192000801c000689802d030018100c100002e0750107244200e45075041052900203181e1030307209503103134803803a00c1d60052801e1902448080d02d0741b00000c0d903030791684170348075446504049009064010a83c080044414200c541c0c0030400440043c0000c0c0d0700c0603108640c01050001d02c1200000c14000708441200e200c14015582e00404041d2140c901c1071100c019034001c00081c04502c0180c4140e42a02170688180302d030018011210711480800031020b074585131081a03c01c5801001070205491260355021101c0401030003100c818156001041c007051070342c0328046400d40030352501070342d0f5688400d0103858500b005100034500c200104044da02070760b11800b5030f640d03480740d0429a901c8064038400070f0b0140c121400c003c0e80034440480d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 285296798 1250 285295548 285295553
    0xf0d1824020c010201151503091202030415180b22080c2106060d020d0804060f1e120b0a0e0a0501090b0312040e0c040305060f0702100c0210020705010b0904 69
    0x10303510103600380d022680d910031810300590907103c54450f4241c1031100c84c0c608000031a444c0ca01c0b214050007034a00040d0070a00c40c2e4030342d1801000f0b04440c2d00160310101e0184001c80341e51550094000701400e20081081c43ca41c038049140714180190300700d1050104401c0d185595551007001421103040c2055480c0c2e403256941a80c0e48032001102d03108044030081c1104120001222120078440746010703000f941d9904080c4078060440c003900b26001411225600c0114008038040c00c0a00001e640d4449a12480380c001050001c5984481c0350811003c80c4030504103400c402901c066004040000c60380b494007100040d1421510f41c0401c40481d505010001c000b00260b0000d81070700d8048204001000c0c03040c0505503038008010030390300d600400700010712038600040d000541c004011070350249000d4aa503981403c00b2015201c0d00880c4c00000c040c007410719014469020202c0c1d10b02c0e0204900c251801c0029079954564501c0040c950340015100140903087d00a074100c1d1802510f443d0450500d40b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 285298048 1250 285296798 285296849
    0x908070f060501090603150203040809060d05010303031a031c0203162319080310050409150c020d0e0114070c080f100504030504030605100f060302070c080f0d18 71
    0x4240c2250403030720342400800c0189240c82040103a030340122480e030b00111079142c2c2070000d50000d0003d4951240501c10381c9015500c2d400148050083c03840c02107070311351652501500b503400004800c02c1c2200c0718074510005481c0054441d401040306141c08444003410a01a0308512410b5510240004056298000d0003040c010786800c01000c1d105e6001c80144240034507460700c10400281a2145200b900702c1c0c0800c1501e07000e940c0203405881850261a40e460004007141e410800c00c681020410342c1050302c4003020310074108900c80c9400a880c4480c07015000424204042054506010903000d42219000498040e14039a43d4028441c850a5480b582c141c0c0c1da500066901680c1c0303200f929110b1084a030b080c05400c0c000c907495150b040c00d1506560b00c0c1400b0b41001000380600585001e0700007061040d240c0642d008004a071801a0b4521031814804240d10054005910552100d031300da0031055000250303400d188442d1f01d0000c80d061400450202d108980341d1141c0ca103000071100c40c00707202990 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 285299298 1250 285298048 285298073
    0xc02060a020d1b02010203030f0a0209041404020f01140405130902130e060702070f0e04050a0204090605061206090316081225020c031b01020f0304030615120b0c0d090807 75
    0x1a0346905030503140f80b100c0b00404403038081000740140c10510100e01540c4006c10400d400c690018405818640c80304040781c203c0741c4c10740706220740d5104c1a0030321003982008442c4041000d001e107002d42e104807100230001803511131442203d000b440a1000d1080c0c0704100d41c4030400c200d900902550f1149404040b100c00303803055544054440c001d0038042a0f01c14000034294089482a458000302c040c03034180c921035130030740041003902c49000d0216a48016030352840380c140c407144981d10004039400c0c1201400914442a138440249038400006e01c044100f001094a8003d02590070300710b034040b000d180181140c01140900503031812341e07409203c0c00398000c0240360690048410000e019100588040344e0300e40400c0345080e0150028101c0d030101c1e0252103000e5490844c1030040340c100800c80c1820501c4e5601036802603404640c0d41e001d524040707400c100300d540100075012a41c0c0780705005454036140040054408209640001507180c58245160011b000f02900452000d032034144904203000c11300726 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 285300548 1250 285299298 285299323
    0x2190801050c07030e041e05040b0108060a1a0402030a0912020303061905090f0405120a030e0114041703060f0a0303050705060f010602030405060d02091504082413030c02060a02 78
    0x703110000e003100d00d42400340c2d040c158059440d00809002c12040c0170040440654075540c0c0b0f80178000108100c809400b4003801944501c910b48030540c5803003886810450040c019621319070070038512801100000c1281309600c0e200303c2e401652500c50b804000020305032000010101d1004420700c0000030740220180d88100c0041d81e4a45000a240c80003900e52115402451317804516540401c01e2483b0b00c00c105035000d48039000b26030411108103540c944540006400d27800290b00c0300300400b4098000c0c09100713403101400311000c46074241542c81204d131540d5841e422000c00000700c0021459030345c1606103030140201070305880342c00c0d8603030500500070b0b44001d5042d14113110380c0c404a42c5070301d820304a4904031245640a1410f240c2031004005a0341c0c400c0095005003034090100060317540d210000464a0b00d03806d0341035a6141d150001480c10500b048100ca0701406510a1446a021301040ca060340300c400007500c002c1d05a07071468241d1b0b80d480921000f80d08500b012905400b45500010403120390b08 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 285301798 1250 285300548 285300551
    0xe0a050601140304031b06051003030905030703052a0901060e090609010f26010608060103021305070e150c01090b01080c030a12320712020f0a03080a0902190801 71
    0x80e9018010b4642161240111003103060401c009804a445080600d0443c6120031519402424a450b04819180c013622044410b00c2203400c20030405400c11520380c02420140c003e02500c5242d034843e180c54920b041d56210811101c60f0281d00485400b44c40303500e00b0350005006a01658507800700508450701201414001c02c0c00d64040b40d06460710040050486540722151082c0c58102400560201c001881950105070350410a198248082c0260009018040003e02e02d561442c010003603400c3c00d483d150201185800203010a0f0f603031104800b8881c200503180c8a0507403008254850041c0300e026105001940f0307180d610000c0100d0600d007103049038900780c01c40d031212015a00f05910741c036140c507000300b041c1c1150680d000c17a90b0142801d151a20a491904030b0000902a88000150710103000300004403000034080c400c002d00d005600741c5880a610003490200c82c48060144c0d40c080a08020381405010000195a0074250304043c3c1095409001d1440c9110505030b00d4012907068040c580455 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 285303048 1250 285301798 285301801
    0xb040f0803120106050f07051c02010b090f280213050f0f030c0d02041401080d18080d030f0e0a0503120a02030402060d05091e030c070b04050a140a0305070e0a05 71
    0x6400c00400d441402c1c02c0b4080600072039291100a40c0c0c2c980c00300d1089500070b1030500000000c500144030103c040302c80800300700000740540c80002e0071141042086031150030300c1d800784040e10f860308200b603a01c80c00d00444095001021280780d60504140410101c4242c000948580310551074103507101124802d0303d03901f0b41c07030703400508004180b06101d100d507825502680c059a81c0c0d140907005064014000b910000340c510389140c000c00c3c0c15200341c03c900c5280d804100b2404404d907021166015074100c10782170000060404031881c0d112410b0f41c10900405440e0a545020040a41d2181c0c00d400c542408845040100f0315109451350044500c01055119480001d0000300303181c021248607a070300400080c03502026035000c4005100160150341b203841451a424006c18061420444414103a0700860b00c5118040480b442c0c0040c5400c0724116440030700c003c00568462044400c1542c035141024409078450703c020541000b000d90010f429889441c100140007100e4a8070903001d200c4c6404280140d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 285304298 1250 285303048 285303059
    0xc15020c04020a02030f030604021303050706090b090d02010e122401080d020307080a02031204030e030c0a060f0e01140d0c02120a0906050a0e120102090a0602010902030304030b060105040b040b040f 87
    0x4900400f002034016800030004400712004040c003c42d484803000b4401402c000a402c102c03640340c03005800845442d841048180825030f08051560b004000040d0001c1c0392840a00200e0b03200b190560000381489040940081c0030390710201d401c1240380071003045904000c00c1840101c2010a14580010421900000460450320108560030900944d4004610b4085c0655810440b6442118040c045000900c0303a00e0304000e04015190149009550700c03030034003410b54105400e00003425402403203001007840801810307070000241600700c1c03003e00b006501c2180c464010317102c0e014107000c140c29115000550b8060242264401b51124206608540d4072414403443e0141d58800c0c8000d000104105800070000309100b100248405101c510741041e000da00030001c81d4444000308050155650045800c061904041c2c0c1590000c21a070700c02841001c0298011a881c1d104500001d08805c0610000900310b0340a00100c40050190481d42d99036590f4843c10400f880d005800344504000011100198 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 285305548 1250 285304298 285304301
    0xe180411010e0414041e050d03050a0b03010c09140307050306190b03060705040905150405040c06020c0a1d06040902180a060f0e0a05090106080109050105060a050d081b03070c15020c04 81
    0x41071001102c1c0d00820b505c0b00c0d02c400c00c030450010214640c0040c030110000008106100700d84078010b4944011519042100388081900c0c08180c1450190385441d00d8180055488400c40c41200c2074001c40d100701c0520b5802280c181411600610f402d441181c040c08828104013100d40707109404071404101000c091000c042d00d48000340e802000280080c03105007e907c1565000d00d8108142c071a10514654104001c101615821242901c0e014101d00c01000843d40500060315402400c58240c84500d00301500c81114822030500c80c40350031f02600000b50640c0300e40e030104c180141c0040515284504000c3d825110ba1812a001004c490404500044014000050105850f2400d4011a0b26650304100000030300c2e00030000b0301a503490f410000384200081c0304007006203024000206462030480140801802e0310361149020f042c0c0c5404040100b0309a90903101900304401018180754030418050341745010700342e4042c021001001c40081c9055400c5081d510511058080d00c81c0800070604010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 285306798 1250 285305548 285305561
    0xf02041103040b0a0218180402100e0112090c0306050c1801050a0e01121104093810022104080d03090206091026070801090603050c010e180411010e04 66
    0x1404003242c1000325a48016070b03006001b10041c3c6484040a21071810001501610444907480035804943c00b40425414106041070070b4600b02c2c1000b10500b0300e0400000c1400303021340380d594010b555400d1028104525940d61000171074102000344414140024454059848141340c100713520091152410b0383d5004000b40c42740d082c01900d0300c804810543c00103603507890006080c2c4c0e203400d0b83c42060080701510030b40648003401c455440000c05554aa6032080d004058640c5000440c00e0156841410159950b88200e140c02c2034031200d0300c0c0f2029140c240d252240c001060a11030300c002c1c0410032015008809042210400b0013180c5200c11031110580854061590194000508000c3c0b0700c003c0c2000305c58000e603842c0318078000100384c0034803098510050b502c0e900490402d180005101b040b59000243d623015001e090f008008a40c69a0fa425541e40108240c1718144941d80d0881c244943d03880310159060900f45049203038070b14152802d4100007a8202c03805001ca12104001b401905042c442d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 285308048 1250 285306798 285306803
    0x714010509070816170f012c06010e070c15020c010c0306151e09080a0506010303080106181e050409060603050d1701050d020609060705060108060c0a050a2106030f0204110304 77
    0xc0ca00d25041801c0c030b40c0001205190801c03175120f012000d0301451000d00c100740f014140b0154100311a039841c0c200038a14210701240d81560750204d001404500200e6030900d40102c464104043d0300e080d585404d0f41c1c1294a01301d82c3c0d44e1244041400d50103048190000c80c4109403543d0104540780d150001e0401148000055000103010749000c81c0784000c00034020304d05d001c224200404d1030307644c03164118075254a290301201c4a41149004004042e04455070501600342c50400c0e0b801c1c040c82482042001071248a5604e1048140f4000c8031542c0d079100012000d86400f62050041e03000300d0134600302601c0e0612007141c4d24032400e540180710500c02c5100540800ca940024455a4600020480012264070742a0f0307005504010300302d59980d900c801007940910840151115616202d541d41c180b0600500c0b0321511320042240c0b030200382d480401c6542103144e50400101d10400c4050034240c410b000e0850b032101901c0c0803000b01c14400c002090070205413089506020911a000180201d4001039400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 285309298 1250 285308048 285308083
    0x3010501091a01030b190f15030516080604060509070804050d0e18190207240506010504060c05071802090306060609030a030c140a0b01031e02150702040207140105090708 75
    0x20349907644c40303070700300c50740341d43c1c00900a5015a9140c1500c54600c407150b4441044101e5454042004a205045040e203c03503140c00c08111030724110140220a1500014035010406600005805e59880b0390001029200c05024921540380c201c402400200b002e580a540034030403401252241407080c824445011070140c100d12070b00156180043d00743c80e025140a060316900b0840c02d4154080e440900a124050410b12903210078148940c0c0c2940915010000e40c0c134242020002907036042411242150310ba460b02103840711141c28058100700c8650485a4421020f5016407441e414a801411502e01e0407820f5540c680c8513082003250902c6080c5030240c05401c040d08400c082802414030002d2603000304001c144500b0a10103450030310a40e81011500c4801c020014418800c038000c1c0c006a586140e4610042d60f03040390009051801040d030420f00d44800003e0190442d00c880c1c0581e060f4582c040e80782640c0c2c1d203108040c18080c000465518040344a0000c0000c0e40480000341e14404070320760b405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 285310548 1250 285309298 285309341
    0x5010606050324060f0d0e190c0605090607300201061406131505040308160c0506030402130209060706050108070501111203070f030b061912060f0e040302070305060907050301050109 80
    0x545810171b1b04000c0032112810f5441d1098a18090240700c605112152641d00880b0500545050380e81e00140c1d40021080041c18040501e160310303640700304c03a0016000509072903100d0012a24880007400f11000c02c000e42c203031020400401d81c054200340255800031040300c0955686c0400d02180340103442180d40c161050769001c1054007107409d45003141c0ca15a1030014078007034a0b625218000c3d409400c0c0e1075441d4600784403d4090100c4042c0700c00160904550041c51400c044d00004c800c804442040580241c0c0000e0903591913441c07a00f1540d07555030019050103250b9407450302c030361100c03403d12406001c00c626903407901040401090307802e03000700e0740f6107820b003542c64100040360440c00f405011400e040e41c4009880080c0d8400d0040c0c0000b1341d07020846024001c000000030b100c1e00090030040ea07106e042c58018010f8040304468142603440584d21203d8680e1941070891070000507500c0035045000701c20520204510102e500419188260001d00059988200070307070071584140c00340c0170b08000100c1d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 285311798 1250 285310548 285310567
    0x7080a0236151e03040c0510170c0309030703030e0304090e070e090303060306011202061b030a020d0306050102070303050310031a01081c080114030a0c141c0804210501060605032406 80
    0x145400c0381c06a0405404187c4890126015140d44400705000c00e80b012000d41481800950a40e400b02008403d02e0541c1080741c81190360307002c0d010009081c151200c01210040408200765401441c234128140486030713240e45401e403034007403034020607541c800c620000801c1048000304403401240080d00a00301a80b0b48102c0d0290030101400490703100c00c0c104030040e0100c0a0ba001801044ac00300c020b940e684107505006460002c44026040c2454107043e8200481e07a0080307040c02c05c40b50141001c1e541c0f541c0c0c1c00302c12010002c540c0c00040001c54804204e825010180441a0580f10f600c0704139107405540100e9019100d41009000000490400041c80000104240d00001900190840d00111302c1607850050030503103034116003602c0d1820070b601c292910389481e61882200c44001951351030b82103515480c1e4284540e001d841185440b400c0c028030700556100040e4400c64021008120040d00c1c1d00f03000308282d0045d110340285a02c02000d046002e8120310003500c0b105d02c001d15841c6010000c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 285313048 1250 285311798 285311857
    0x71d0a030c170a1505070305100b0d020c10020a03022106030706031802090f1009091502031e27010e0705300c040c0807080a023615 58
    0x442c40c1040e00e0141070340b0300001580460400c1038801c5083c00c00300d403501c1d29400c010225203000300700740c0110b640c2c60420848640004112110401e0b8100050303501c25180f17580034039240010300b0004150344002100020b056165000c0d0040c106080100348242d0041100d4031103010050328065850b802109040020a000342d10402040c5141d005400e80c005a980000c2c0300a4021580003e03a1042ea4007000191460a800c01c1d000d85074501041025600303603101d1070034140358104003480207540000032070b07027140d007110004201000790b0104610750300d082612640811120310f00341c203032a002121528401c8a060083c0281c030841d00004102042c0f41c48204480c030358602d41900c410f400348000c0d00024851014005c110400c000009007058180407040c0b000f00d502c5550840d08101c0804140400c260348040d110344c1284400402580300d0490300c4e84100342042d00e1b20440401c0344200c550f407800038008920f150071500219030440c40b030429144104c8261040747c2c1104405075a000d90b03101141a078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 285314298 1250 285313048 285313079
    0x9010804060b040f060f06030e0703120903051014060103090503090f060c030f041701050721020f03090a1506060c020112020c0303130b07180504020d0f05071d0a030c 73
    0x19000101da4402502c01003011960504807414807503031241414800c2c0740c074962000f402406580741c104043d504015172952190100d001c020b180c558070080e21501903200d00c60400281d40c002086c0c40b8440341408019000380360744001348040c00301d9030300040c1e81340d070081c4152243d00350803502651805000300100209030098401d06030b4828030501641c8490352041001c1c014150750604520740c1d550a0072042c6103540040b9001014a0b0305000400000e5644490744403142e011213401c103000c03041d20741d0500c8080c0c041c400c032540c10103002008020070504002044010207001c0d6a0407a6202001e0314201d054802d107004d0000407602c922403100041d4401c041c54001c60b032501400506011043c019036041d0b0740300b42d402c14408810032225000b4003024031449a0040c0c880e00344140c1c1c12010039041d01e240125171280d24810356012403850340302d400e250081340043c074801c5410011440c2148001d815101c001c00b0390004401c06094003501420419072060599411600108041340f9044000804400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 285315548 1250 285314298 285314303
    0x30c03110f030d020d140c040b0703030e03181807020d0507020d0f08030414030903071701330902090d02120f0102030f01210f0803181e06010506040b09010804 70
    0x103400a00c2880d48090014150070324014030013581e10001c40040340250703540f80c40b07888100881c25085c800d0385020030007110100c4900c40304058480032a41400d800920590186610301c0c000051800b03503854032984400c0051004491031503440c90a0200c107158081e00700d4505001d030f4003080d030210109010b48050315802d44000c2988080741c1071036660210035581c0780c0d0304a0f00d00e035011041c04100598401320b490f04024400081d030614103d8800259200114421000310700c00340442140140001e42000351080c80d055183c10b074071003584211003900580f18141142c00f00a02d0301c042112079480c0211030814070010070070b8500244c9902080700c440702105c01c84a80e44030380805d00092807405e00146104107003400440782c070381d07140c0307070301d00010f50342d0031811080984541d800d400004444001605049800c004920344940c1e40340d070656119010603005112500c1400804580d2110404440020682d04c0080d94416642c4005204140c01135010b01d41c01d0075000e1055070465480f601c10568040d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 285316798 1250 285315548 285315553
    0x302120708070b03070e01170f100518040210050c0703110301060807080a0302011103010602060f0903040b22060320070309090203150307141305150913060b03030304030c0311 77
    0x19a29800c00b4a003580300c0e404050440004000c01804603008511109201400c5c00c200c14081800c00c40d56000c840e00820000809030f094010600014840e00c503c030140030054080c1d0140241c01c4038031042c01404440c2244120700e11400e00302d05c0341c4510261459000064002d05849046507110032200003034500ba19015980d03070750300060f040c0303040009000810046002d04400040ea040003401e490016400c680340940c2000100021030740056020791000b0004006403060319072035403640c218891644803074030301080410b41c0d0908941d0103040424842c0ac000d025280140d07500029020741d032081405001c4003030300c001d0440221444500030103441d40b00b850541c02682e11143d07030030f040742c0096400850700016041c150105040400244e4041c060640d0031300040ea442e030000a00c03090004207440250343d00c50002c01d855042071451401b803032034001c109002e94900800010b01110780c12505440c61810580011514103001c070490b40126096a680c0000c6000c03900e0903103e110006003031600c9413 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 285318048 1250 285316798 285316813
    0x11e03170c0a0c0f0e0114060a03060509090705271603061d0a050a140c07060e030703081603090215180a030b09010e0c0607020d020a0b0d020301150216030212 70
    0x9001c2840120040c5205031482c41d5000c1c100045000c0404594120403002ca10b00001400703004410301c8250f001d0755040312040d60324100500200c029000b140d010742e80000301e00f0244001450b010070a00103844ac00d45101d480b400701d2000804108403012000c610500301000803a0040c4000c0a1543d003076140381c10085040ca070f0310017603000c0c24800200d10040a58102c001d214000e8080d00507580c202a03c0c81c0d06220345a0b041c2d80715480c01d00041d09500700070400080010802c2a940c0064944904050a0360785030941030034060200c9608450f14201300c1703a80d0521500042c0244160040380d03401410f003d800c4210300c50b039140154071104082d80c148a40805aa5241da200004007029522a500100990821030f12883c2564200d00c401104c07904280070a00041e20342c4010f5547c0c183c1c0441c2c04201704407440c000724107070717103d0f80c0c0200c1d11358900040d041034510450f0f0011812107150480400ca5401004412a10b54921111007403402001020070009403404140e03070048a2008030a03a25207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 285319298 1250 285318048 285318067
    0xc070303020604020411030f070e01030f060e01030311030a1205040212010905011a0a0b3103030201140f0103080d0b04020f0a0c020306070e0d06052715011e0317 71
    0x1001426481200140d11890400c401c504140c015480e044841d545070b0b908509040000e0924010010111000c105210704001c0540c0c1c440d030002c0c02d00e420714003c1003080617141c143c0341403001c5007400180c000c41c00010580e003140900208449164030213a4454070400f0038048981c001c0c2038090700c2a03a12684141440301c0e041000c0c8101440644984000940340460f1092011480446042648201850107003000b104000a080301c11b100d0558066120490000d030f12954840707049041c0c40c0010841c0e200102c101501507221042c2032028901c2000c42d40c2d2401000c1800e50000d01008021450600c1200780540e05604480f9101d00010000340c10403042200c004a02c1e081015060001151000c1b400c080d81814041c2c42d400c40b5040c41e0a60f0400d402c03c0114018200c549130080000c0e903500e00040e010b9404116408040d40410b0134510386844400903141d4802011840790390700d50f40c4000001e01c02e8824280b8200b20409024100400c42c616244c1411455920070982000201000504503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 285320548 1250 285319298 285319303
    0xf22061e1d12030d0506060309190614090706020f0303360d0e0405060f0319140d09090c0305101505040302180f010e0709090b010509030628090210140c 67
    0x280c4800b0b100045440310800d01550051342d402500540c0200410420300400340750225241100b82c50481c580700d5510710350310b4004000c0440c0448502c404803079105202c400340780414914121001a0700b00c800c0e0401030000c2d40e440b8802038808001c0040410030070000c602130088405018401c6441d540c4850302601d82050800d24540c1185c07002418103024007600307141602c03440303030004410f89516020701035007400710380d03142844010010b484540d464810200724125403000301c010f280c07a095960381404840c0282140c0c4903401540010303070038422a00b58403480791040350300c20038030384c880c203003400b803910344400e810101d0b8210820411908100c0440540c0307030013007000070341b2000308200c4d03055140008030ba0500d440d0682062070003400d04000d10071702c650b00007088025030782400000a5004503003801038079903114036480c4580500411042013203040038008005031510081da80c546003002504503ea04840c1d1000000350701c400032011400c50345200d000c1507c1c1481406130390030301d000c104101692 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 285321798 1250 285320548 285320569
    0x7050607020c01120612020108040203101404020a060809060103080a030b0603010b190c030e0f040b04050f07030e0703020117070e060d060306060501050c030a03110f22061e1d 77
    0x50b900c460721524441d6801039200e0180d04100004000f03444c140031202d4010a18600d019041000c3c0c00041015940e090010401c50f030182d6100b000854590844030b80002001c5505a10904c050400001e8040c02000140d22440040b4042c00c00d030303800d596608049400c1045108200360b543c1205802c41c0c1c46000045028001c8030141c551120004503480c02d0302070b40202c10500300213019440b640041e07040340c90414000c00031104200d4076050307000428001d04801018961141c144002d12101031000404c80c0c0c007607104c5503014009803612110041d40d80c0601e00c0024000350700c070410b2241840c0140d0146800280b0351921142c0500d1a00000f103c82c1c20070240c1c403042d16900d01c800c0040000c9840303030600405003801e00a0916420450090b207034003c00743d00c40103250b22030003104100e00c1302508423091003118100d89030321102c2d001940e80001c01c444d640490000300d03038030713020030280e0003208012000f80f2510b01850030101e5440c000c40d0040c4054600205600c06d25440c4952661303240d0041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 285323048 1250 285321798 285321811
    0x306050a14090c09241e030402040c0f120914030a0f020705220b0a090609020405010207050306090d0c030e0a060e01030b04060b030c070f0f060c02060a060509040209060105070506 79
    0x48200305000400c008800c0006043d00c103424008200c815815140e19100f0040c2c583e8a2401c085004200740039140984586d209180140703110480c00d84050580101540c040c40c000d0b03074104464505040305481c0e8800d1004001c010503045c551808000c2030540250300c4003481400d000c1e21880d4030703514103444e41c1c110001010100e0140710f01707401d10b5a0304001c2e090003010101c2d0955400390420091441101c6080a101c80550f02d8600705845610b690707481c14014441c0d200200501580d40c1e907ea8025009401640e0050044800000d0b551800160450158a0b41c0c005083d8041c04110f06403000004000102e0501c9840d100c07070880c0755243c8142c54010300054807414800030303200d8001011142e00c8042c1c1d84c072440ca041400e01480b000b190aa950044064035040c0c0d84040e40e040c80511048070304d800900c2c0000d22807085041140742d400c00d00d003000f9260201c400e26199010a80c0642d103640c010503070440d010a0002d0050319000c442c50f0340203441818064a091180e46600d4203210703049030315 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 285324298 1250 285323048 285323069
    0x70512041511060f06040203090c0307030501061e0e0c0a090803030a0c03060b03040507060e03033c07050c0d150f06080717031804060e0108010506270f070306050a 72
    0x8445000e030007a008240b4032140002924071450032a0306100c42c0e21014040382c0c003031580403001800480c2c01704903010400708018115095566240341c214080d0455000c4c1c2d0580d40c2e00b401c8000139503501f515003001a20f92032848510f03580e8400c00d01ca070407900866080010000456400110540244000d502488400401051500480e1006000c4e02c11541c88240d25200420400c4003007040412030030292452494040c5001c80082d00207403442c01050b8a02c007402d030800c00d84171080e000d5400220b8480c0c1404444034181d4400c107083c2490fa0107074070320203030058001c01220445864801d41300d1403000e2050204440b40e02050450b001100e031420001c40400340d540d1410b100c59441000800002c11000300317503091402c10404003a440b40200e01d810a08550ba454041040d40d4990f00040e0180c0700c0c01240712015a0740c0d0001a0203030005841030350051400b05d9056901d00c64011422801c03072140713600f581c0143c0764003041707000c6004003d00a0042507a40e10300440c0541e94100043c0042540c1c109 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 285325548 1250 285324298 285324329
    0x1090510061103030609070324030c0e0103020a060e030a0f0609051c020d0c020a03060c050d1a010503150406082a06280c050102130612060501120207051204 69
    0x1031080444035900640280501c0200018600800004036580b1480030386041550361109481a4050090110340340191401e425580b002084a12100d408480c003400703025100541e95102d00d03015179000c0c0000394000e104101c05004003405030220220007180030702203620324ac44980b0350515419900300c08840d2952501388030700c00e0250400c040f041c2d030000d0100201e8168007903a006940c602901d040d0a06006508407210f0555440142c3c100042d6080b80d020300c201e401815000b0656444218010109840c21002d10884500343c000c40c0c10251040e1500c62940d21007c41c1822241c0800030302c954040d440e0301c0c0210744081e090242e0001e4002010083c030781e04900e00c0c03621941d0307074103107980c1405003038144403c10941c07880c01800302d0441d2602c26041c010440e003241c101d60a400700e00020300a5800040c20f4008844801e8080e01250b9065640d108500c148201d20301c01d0340c01d0352260034001207000030540c1d000c501682c001c0200310311900c1200e8644240401030450341d042a4042d245e0243c1040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 285326798 1250 285325548 285325561
    0x313140a111f091a0c060408030103050610050310020c03161425062006070f0909020304110405090106030507030507060306080708030403110d1a0403180b030c09030312010905 77
    0x5024010342c0b04446103400052800e90014400207052060840003a840d1000c80d41e4100c803401201e003242d0300d02003542e800349028101815580e04c2032108550fa8440c110010f20100304040380c03107040d56001070247c1603c58030303081004007942201c0d024261074003003003014010658800c0c00c66070059114003540341d44a4924030000d4103100783c91080c00d4080c08040b40503854036110246030802e941c101d050240c2141c074215034032221110601078041c414407481052009168008090a0340248941e480388503082d19042e50718180e00003641c0080c46a004440d50b4440780c074058001c650321110751000010780c541c0d00e031070301490140c2c0d40d881075070583c108a605101c83c590500404010b0503c0038000c050141c6004c07580c035a0ba00c910720001c0d1200c0e420f02c4162200d40c0c0c54614180c106a003004c03c1101e41d100428480710303108025941100810500410300d0208480f80d0040401c58403640b94030ba00316601c62101c20125404081c245605000410101d050701d00c0d003000060181603450000641c514221 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 285328048 1250 285326798 285326809
    0x601080f030a0207090203071701030c031101030902010c030e010e190905060f0102100b0105041a181c030e06040305011b170103080324060d1517030313140a11 70
    0xc039140c4050341c20800440c402d850300022244120307101d1031401030356565041011114040c501108180e6005042c0001007400380f036100110a0724080e010080c041111000103600b1a002020000c1c0482c10389001000840d01405005010401c10b04004555052150010700740441941078040005441e49040c05520050722072154000d400b614945103804125002035031b244650f411120139a92203000106507a4812420354000300200c1d4540244803000070b40f03694164010b079040c2c0400c0614030490014500d40849042a500c00c01c0a80c4091000b003500c003200d003c040000482d030002c03020080000000c000740f2911503200c0a8003002481e117250310314000c1048420915082d03100c4113510051020030000c3c81140e070400070b21032103400500ea0b00b54400e035102880b00f640d150f2122000c210035005646680062001c01003101007101d5290302e656180000d40e8034125940100d51050000622a005240160003c18001c6060300141850700081d580f4108080c03034100c0d00301d4510760350b01c0c0b681c1c1000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 285329298 1250 285328048 285328063
    0x7020a0210200303011a03090115150305100b040501270603061508010e0109180501060e1b040e0a0507021005040c18051b160b0c03040b0c040b070f03031d060108 71
    0x100e0000c3e6203154501014441006400340c1201c07803d0388000f000c2441c41009522400d04000b00c0032488500710354039088121004007642c6441d001c40d08000c0003030030b2107600040c100c080c0e984143c01039040504020046615560300e00b504c1c6503180c81090111424105003580000901c6a0b5030301046440c10a80c1c0c9192070541030054906101300d010040c0006446450003d066640941c40060704003803d410700b941c42040c0840150480d441c045010800a407507200943c4200489107201c495404095126204e92096100b020600350400010481750b015a40106401114030310444074400301e11858075045030720941c0e080311011110754042108403070154140503e5194840100001e00d8403200d9401031540d12600340090b101c001035910b0b6020307440148074a171242c002040b48518941a019105654415201661100070400004034600e45035000c03102900c0c0e5604401d03081101c90350f592040f0444000c0d049040c075848020f84924100394800c072003010070800b4001e041030f501d81404541403840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 285330548 1250 285329298 285329357
    0xc0a02030d020d09030b04170a02010c0e030309010801050f01030902090a0203070f08063d11011d0d05090303071202060a060503070b0703110c060c0307060b01050313080307020a0210 80
    0x201e10f007103600c0d07143c0100481c02181d40190402c64156580e1a000c0344210840601c10300702100440c5c1600456030550103054041070684900e44281041d2042680d070380030304041c42d03000841d0480140a103040520709c600d2200818100803940c000c0c26800038003400800c80d01d00600e107a01204102c143d80e403040d010400300380b890030a101e2a061280c0030441c40003500382c3c4031072318002540b180c0c40704840380450a451030b8161403004401210007400104a00040030040280d50701313120840c20f00c150003030b0811002184100c024105411108801d86a641009088070340c14001400000c1c0400c07154194410050300c41e03800f815451a00b001c040d0119000e941006000358043c120510003180c03000d0131140301c46d07014102103068201c104906440c1c07905400d110b03900f1100101c0e085c0c40181c1d00001510031184900c03c1480300000038801110140401c031294001c82054041640100d001c007030003180c2001d403920548585810507000300311400c0010032410002568004031042c492007260190b200c015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 285331798 1250 285330548 285330553
    0x100504090803010e070e060d060f09052502010e16030b160e130204050d05150a0c080604020703020c0a2909030d08070c0b0a02031504090c0e090703080c0a02030d02 72
    0x6149072038450789400140030302001a442d100201d40c0031402001c60030031260300200f0320b035500ca40d60103c0d00050403051080450480100c5000b003110005401120304c1201c8101561190880d60001070310f80000201e400015550b8480140520410900840ca103101e448003a03082308501c2e6203403201584000030301402414900c4500300740b10540c4040707018100d460403600b610005508000e140000c1c07090340d11481d401359143c00c1c1030303042140c0030070042e01650201e009513080b40d07101d8030000203441400c8440800141c01c1c0001071102d20b0305501400d032860081c81100d12482a0101080d0401080d800004070500c40400719079a80340500703031591a0081c05900c560400c050a00443e40d600c0320042c42c1c00502034940009402107200b03c00891260f0381045d0032000754240242800e009600a030f03000480d0881c1d244866010341071900070f155003264025002c401c894589418401e10b814042d10800c500c0c0503d090003c00f203200e500c040c1541c1c2c00541c0181460001c584105031410b0144a030901c10f64 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 285333048 1250 285331798 285331811
    0x2070c0501051c06030f050105060910050d0c0e090616050a05030114041b0305090c120a12140c0312010e071e03021c0507020f06090a14010b0315100504 67
    0x80120008004698080c02c0880d2901000750499025012000c10340b451180760000020610450403400888180100d0080200383c480300d007400442d000071104080c4403500803108104609058910b8003445000f9095180e510b61076403502000c12405444c20b5079280d218109111036404441d1000230181080d080c41440e003048820003400f61f000520504844002e4001d54802549654000b080540340394050304035101c89240018005200a80300c5490601c541c051044007810700032800100c100032180203100403165a650301c080c13100300450316400c0040710b16410f00700455250241c4024802d901c042d50b19503108502c14901c8a01c1640002609103242c018400500e810110b010070320311001d00035100086800740107a000e031103181c40d01501300c401120545124001684007038040c0600d0713420388032000c000105082d50b81c40d0940d030710342c078030b420036000c80c0c00080302d81080321940b074600300011504018034400642030080032903170001812000d004014225500c00160030261000701d40c00c002c070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 285334298 1250 285333048 285333053
    0x20904140c2e0315120812072007060503010909061407090303020609160b1602090a1b0c0816063207020316020607050c040e0106181e110f0a0206010501080a0207 71
    0x15203144500c217446501918420140543c1800301c42c46e40341074140d00305143c1807000d002040003802c9101e180207401d021100c002c410801145034001c03900540d075440d00750390801c025030700200100c41c0d04550f00e640d600a150750600e12070a045100704525252580f4441c69410080d040120003403000300c46403c411491482030514814a800362201904955241c1d0000380402c444035083ca031000e9800000d070020005000e200f41c225500c1c0700390100c0308030031b818400700094400840d0080000c1102c202404a54011110b14040000050181201003100c1c19008001300340c00c29001030f40d1450009840f500b01d4205a0614503a40010103880110324001064202c0985807a003170a000784a01000580501405020000b420341810700603c1001500c0d4010000d134020700380c511072820070405080e02c80d00e40b44090300ca64030415000b0031034400160001000d11004009088410030340e50300900203080512210300150804404540080802d075042a0024000e8600102088083e500400c5070900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 285335548 1250 285334298 285334331
    0x2030f06071412071110020c06061809060402090a110313120c08030c0315030105190e030f030c070201200c0a15051b03191e050403020904140c2e03 65
    0x40c041205d1a01c2e0f1060f406840312641064110041110440c0c00454003141822004c580140121012038107000000300b0101d0b0b40308801002c542c204225000741340060094105000801c1d885452500c3c0040c0040c07044400c0140707030b001603490112800c110035480013000000082a40d03001c0741810160300c13021640d074800304240710040440c41c0c0c284e804070109150350081e000d8902d0f0520010f00902007072502142c500b10b040d50051000c00d869081034040c030814400801100c4038400c0446680e85540d80e139554005c180c1d4410b95080f0b041101c031403501d14204001c031001d168a00c09100141480390640b0703040110b181c15a401c0f45510740001116464401c0c2c100c01181d40300042041036110318604e60030018294002c071040030603610800d40342d0300307180d81e800044407454048044c2c14601400c142c40c81240c1c0d03800743e404025040748412000c900810114131826045040c0842283c609030340f0400410071078128a0702058240d5400d1a141103000308521149008201c24034042280405140b0303900c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 285336798 1250 285335548 285335551
    0x50c030f010b07020402371806260709080c010504060507030315031202030a02070902090123161a0609160f020f010510210c0b1602030f06071412 64
    0x52141c000081100854036542c054070f00c0d91000d000850a4075030302011f00141540f404039141c1c481d690355031880b840030307000d07141c1c0e100c06001103414450f200b41400015150b86d64070032490208181c80b04d946e18045c15060303e0303041c030601d01c80c4d40d0b56824030302d0a0800e514211036024054103218061206200c0c41d84c4c010190f640d19605807501243e40c202d020003211409030a50009070401022801800d410b540000062250480c15400c132040c4641e202640003c90051031407903400505010380c0e01d42007404501d03030700f40065282c0c0b5010b4909040030781e00b039210320300e900030031600c1c001303150a28106d45580454859002500340c4071000340e0314058031030604803100c001c0366406116803180c2d0b00d000140300704940da0820101070300811071400e155840c0c60030501c0c1403056409032a14103442800c420744608070380040c6079108010441580c01c14449a4080d00400300d51100e16542d1185440075079003c0180c050207806240c080e15440c107101a00800c440000703517007803100313640030403a000c02c80c47c0b03070348426 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 285338048 1250 285336798 285336809
    0x201200c0a0f0f0f050309030c0307051003020705150a06090c032a0302040e0a0e070b13031203020f07030e090109020405030a02090601030e0304060806030d09080613060f090501060306050c030f01 86
    0x50150703440d0b24021003021035aa101914580c016011503040160000080419140803030449e218111880c08042d56507009008a0341c12003000d40d503070b00100b4065000741c02e13414400d01c10f8071004100f01c1c10403800800101c40700849291100c4040161110600c244440813a0511701030015400140300c125102c054540045035500301a450000b656203e030313040e1806001e0040c08605070f410581040e070054840b400580925000301d020000b00d44031410216400c941c1d120f030795072099900e5034440c0030380d0003100030206c0c0030b06800704140e203100c5038113500810407103201c1d8072110807a01030030007031281c0e6050580083c103074113104002c1440141c2d000100e401190f541211008295540c1000480207007814035102e081910001c140494481e8001c1d509a00c0750f4000d038125800f8904941040701d00044601c603d40d000d810020100d0020200c602c55521b94034028007000c030704140b5401103881100c0310090180c809954400c81030040003060b020315500003040540c000d041d4286181c1d611112501807069 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 285339298 1250 285338048 285338063
    0x170a0203090f0105040807140301050c09011b030309290a020c190204090b0103080a030b01080c0301091a0306010602071a070b220c091e0905190f05010204060201200c0a 74
    0x419a131040d0104d0b40605120310650b01e2860b6030b00e84c0311101c001c4d045075a0b4401c0d42403d0000343c41031424030136250784140c140c0d1000d0000011545c0200d40214154080d42015102e1031007a01298141c280b550018901d11850340501d412551114884030780504484000d50040000c3c008001c3d00040740426042c0054100d40c03070880610003e001403138484030080c08072104100000900c411403028080106d400d440a003c0903488100450384907004642d500c04842e020300c0180092690765000c1002032030b4943d08002e0062032440000c1c41c0407426440400103a02200c1d051103c040500007004082c0100308009051580d20380d600084540700408800070b2100da450b0046400640003044851690451a41c113481c80d21042140c0180100c0c0820010880d0b101d42c9158407400385100d40e4403054ac01c400076181c080b6008070a9014101d1040050fa042d4074804400000b0a00070302c0284014a980d07000000c117103d035044100b20000c500c1c00b640721142c40074440200349403000f0440340c4040754440f82 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 285340548 1250 285339298 285339319
    0x1e030d030e0c040507090501080c0a0903080306060d1407030b0603010f031103070312080703111c0209040b040f060302030f0f0d05030606120405070e1005131d0f0a170a020309 77
    0x2041d525050301c440e0b0503a405820300303090081560300001c02c03005448003a0b0710a041640c40003070101e0700d4800c4003900400210381c000c0030004a0442d101840c0c005030020600e0707150035990541c58080d80c0460708050310a281041c1403020316078140c45800c0a820701610601d041d589003031502c40014180307200141161290412070700d500d6801380007034405168000641d00b258891200020201d0300200c4800020a14002e200f4410104c240c0c150782010300c03203919105d00d5610710034a40000c3d40045000e40e4001c1e03100c24101d03115035254001e41d45a9036030143c0000c0e00c0c07440c60040610300311001d823102071290444640490000350208440089040030300706541c4c0d90b04c0e40d4011800c07038441c43c410451070203c02c000b40010090042115411210080f0101e2041e441e80034421005080034407138036134880300b106603c0d0400c0a4940103140840648101c05e107503507514010303081c10180d00303140c0042c80350410404c1104010540c12541c268041c0708005505001c81d007a006592441010809031145407060f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 285341798 1250 285340548 285340571
    0x303090f0a051903110d0839010e06010501080f040308060a030204060303020102120105060c0d030f09020603040b04030f020303040308010b0d0609020415031d0a02010c17070b04021e030d03 83
    0x7441c000146005401c40c0d29200440003101e800e2070160108031040d841258900101d490101c0c9a000ca8903040f402240c54403540f41e1403015000a0100000103100e060110b00d002694100169890664401c0011844d6501c0301105410140140c1000341403181c400f040c00020400c008840d580140d00d82000e0007103464210006260000319400298001d051823404000c2581c1034000c4c2103040e110003c40940d60340c803103041100340c0c060904051403c1e40140404041c0c4ca02c65000904c003406c0701100043c0341c840d80d8010441640c400c1390144ca105034074109000030142c2c400316040c42148188003031415410140c0c1d0040c0440070622580076081008106c030b0842c1000303940b203c001044030b031004559807942e0754200c005003211020b244000c83d1a08100c0707940c003441180b581842400001c041c04602c6055401583d61040f01d09050f030b5010b100440f507400540f45400180340c0d25000c5c880e0260070740b078544100700c0e0016551a9102c00245005d0b40482e4035100060520f1803140a030901186c0d40301801c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 285343048 1250 285341798 285341809
    0x80306210a0807020f0a0303051c0b1509011805090f180609011b020102030c090904080c1609110c070905070e03151b0f0307030c0c020d1a010609050303090f 69
    0xd82000418003030081000200001c1e0401808814070030307a64803601d21132100400c04608010300c0040e010510030450180032401c581d0401c070000714550030007d016510a000710300240444808a49810000a510111580c1040f03501145001015403140315030b0030500400c03480c65010300140c14003090ba00226800e005503e80c01e1411080c00402c481443c9440110540a40403166100c99140f00c4021074903292403045c022280301d8003c01401e00e10749004030003805010440208140d41005040c4804c2c40920002c0c0b00300c0381c2040050307401c16081400d05c0800c0c4101da44200d050010050308102c400c1a501021803101c04a40d00301500090700d66401c04251504245a40ca0540c103019801641c0c0707000c8440c2810a0250380040b02c4401102e0b9507002116141c496203943c0224017509000082d41c0c5842504150034590181c03078080f40c2d4500030341c00706072301042252084894007188090356000100f82c030407260050001d0304d40041464a03200c04030f0386074403c4904d0180944500d184401840c1c441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 285344298 1250 285343048 285343099
    0x9070302120907090c05070209182401050a0b07030e01030c051606090b0906040c030807031707030c140a14090a21030207060c03080106081803041d0112080306 70
    0x40503032910300c0c0b0b0105000c5071100300710f00442802c0c42c03418603d403101c0383c41202503401c0140c1c0508040360503100d1750344051051500789250b4805200e142207420302c00600c1c0308050b03004605000c04c00e030380c1e504047c03c01801c521550003000c4003400921940010942c41083c11001c244e0a00740081c11450400c070445080c441c4261845070362007032600102c100090750344060b000340e000d058a07011948034586000c3c1c43e078200ba0f40c05080032030031400074400700d82100b0080c04010700c281410801155400125604407104440072404255500203000c40207822690500c4505070045645180a0904101500040e40ea0081841d28003011a11154948075a4114000342100544018090b0168244000809080e1038110014000c1c40e40000300300c2d00601c410030055a042d2074542c0c0584c200003046031114801011a0641f5884020031007400400f400103001130000e010b00010f030360b4030600e03540c1c00402040e4014000b039a841310071030010500c108207880d0000390032150500520420003004003204607 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 285345548 1250 285344298 285344317
    0xd0c060b0f120c01090b0c030901050d020c0d030e060711071a0c0303040c17010b18151f23030a0209011106010905180c1807031806020c010b0a030f0209070302 70
    0x307121400385820b0300010280028030090340c45078031795501c90000c1313a6240200200300345e09600603c038030700b081e41c01341d0050058172054040050038221101e5416103080300c0f00b803550340880e69071030200e080d0810900543d90f00c46001d091040f403071001e00d2003e40d81d03086c803481181d6a40c0209030806413a801441d080307545500501040382c0c0c81c1d0900c2e007071071414140a8461030040103591342e10600b049206001318400c04a000304940156400c41400701924140280207901008a0121805003940e44a082001c00c884011002410102e00c0300301078107544005000508001440955942c8524070400301c0383e0101d9110805600e80c111030380103a40303520890280d0044c60042d4000441c030701c0c069902052003110310100000860b450f0840311a158a0714605842d08011034248100c00c441706080c09a400401030b207000a2a110080e840560131011801c00b1190584c000030701b003641c180700b4010000340c0d000868030a041a49541d50306840a420028000c0c01407015500044c4814084ea0550b0000407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 285346798 1250 285345548 285345559
    0x30801061809050405010b091014190504050703060e070507111314280506010c030e0f040c050304020405100501020a0b0c040f030f02040f0510050402030a060510050712020d0c060b0f 80
    0xc0c1850b10078040c040410502d401500c49500140046820242c1601102c901801d20f8010411220621540c0541c10748401d201c4034100300e0018ce281c40764481c00303125000aa40001c0c403113040480520300d0b150b0140406041140c103000d58000305101e412201c4025000320785907070b2203155003074004d0003a094250380e1481c030550341020090303d0300080442c815003542158507078142020140203036017282d000b0365030b10307001665005400700068043c51010711240030050076040d0300410302c1e000506480380d500700300000600100500c011070070640a141d4108130340f00c1a050407682003000013580c0d5410014068424222500170804051481007214040e044100200c10596100d081907450140c10080c2240a10b1921b4044070082c1c046208441c05072000b82040e100461510b800c01c8040e410151200ea00d40382d580c000042c05545011506051003034640700c5940f20320190510100c0d0b1408004120295000303841c03070080307040e4080480070b4041d5010b10009248101c91002c0354114042d454141d4002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 285348048 1250 285346798 285346801
    0x30c0f15070f05030a0914030318090910050c04060e09091504030512070e12011407050a092105070803030c07030c29090d03020c070302010507080d020d0507120903080106180905 78
    0x30b03038000b80074021f4943e03008804010000c05000d06959104034048010182e110554150181c9004010244c1140d031a07400c4494a00d401c1802c4811a001a506040c5110f4000b03000c2000541140d400d44c5a0102100c200c80c2070b1424010060303e40d64410a8480344a800d9000107007018001d000340d13800f021310350040b8070840c40c100a02400e90724641441500c1074034002038400100d2014000d0403070744050203403e03140301e468280007a00c25401003540401400060b91011030440b080e50000000355803000340c518010710040c10941e0038410320750040341068104008000c02ca91420781103418455040c82c20059112060a0408400c07241805840003400c450500c44000b41e004804d083c055100841641c165840f0481d09408034480c20548820130741100c1000c202640c0980003511072240248402c0340382a1140c4681022a40502510300c401c903651818000f0300b42d4026030880340c000c0b9101c0200144031103034030040e0049005208101c05c104084982c6400301c15090960b078020b00d11b00b48140701a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 285349298 1250 285348048 285348067
    0x30c070309170703021519050a030e010203240a060c08070f02090703050a05060d02091311060307030903090b031e07091502030c01270602090103090c080606030c0f15070f0503 77
    0x112201413000f60300c100100d00b0140480c002550031600b0f03884100c840b00034034101b1600203840e10303008030102000380355a072007036519004001c0c002903105001c1d01c40c401c0104004903140d10444141c89000c50301480c0c400d442800002e421028600701c00d50040d01c015140c2d071032841d12801b4489244402034014003c01e0030312004a40641060f4000e8681d410107001507503803241407010700b80440d00c1c0079500c440e80c0310204803058003403600c4502c000e0107500c0550b035021241d0080b40aa03030007640e24100007030356903640600f41680701c00700e1006003141400c294a542040c00d440c00390005070300b1405080b0142d01020920031400707400c1300d100400744800581d0300d0f10134401000e03480b1b4215841c3c40d4001c0d4201a800c541541e503100d007109070500448002d10002034681c440c5d000a402160504e070505540e551a9408601402ca0f03440017410004001d04036803510001307140c100004201194001c401c86058051a6520340c1d208081c40c40b040c640d9a81c58032001d04040300610360005003c1c08074000000c28103030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 285350548 1250 285349298 285349303
    0xf09050c0f10020307080f04170a050d0e010c060b0d0c0f18060501050a051308073008090d0227040507061704110607150204051c0503030c07030917 65
    0x69550884102484800c440705100340075418006400c01a001000a036001814000144c82161405042c0703a00b0103132120b032507038410711000714240c0555000341443c0f4100001040300031010101d500d080c00c00b0403854000a4901100d180004041c0740d140c0d200380001d81c85450044201b5504240d0350903106681d04d02d00351644c1c00310300074008100800c101840f504c83c01c2d4002c010031101d041e52ba403403501d28204402c44a07030304a06811010303158191000075034200d0811141010300f13034080c0400041c40e4108840018460f0782400d17140c80050b480f800c1c00100700c0039815642441809e0715625002e03001c5100203480e41c0032501000740312071300c1c04840d501c0701e0707001003c2c152045204004403004551104e07019034650700c203c030020f50318803c42000900012803040c03050095440c003408160a203980c55581c41e51200310309501c11082035002c901048113150009141c1c045a1500f50006410041522410703100c3c440102010802c2e0700016400e42014416200c920007000c81502246043c0b01e44116180c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 285351798 1250 285350548 285350563
    0x304050907030608150c2101090c051207031d032b05070e040c02010204050a09060f0e0f0112060f050f040c0f030c090c0e03120d0c0306140d0302032a0f060106080c030a0f0905 77
    0x1001528000d0818ac03258058801c452140d00308480131a072594402d0001c5001d44101c0340e511094080d00d60951801c00810400717400c600b25406100d1100480141c0c5d0071040003c200704550b0700034100f00c18071020a40000815031446401d440100c0e840b11107010503130191080d6403015811501074580014441015407004e001d440105038040e007050783c1c82c400904241d2054410452000740c035401000303060007011446064511510020495441c00a41242140e100721030250014125104000801c80c04181420203884001d80441074141152206091002107007c1e0080c0c65940310b005002c828005e0381080e22070b920041c1101c2c803100f440d810348000c0c0d4000405580d890b07804c11103107042050180c00340400b0380b42d1001c07159071041c503e00200301c1000c0b51482c2c150194041080751028650445501c03141d2081248a03481c11100300128061070900080c044503003580041c2e006028241e40100b1035034020100482d02512600c0c0d02010340d005042c2c41c9485003d480c07500342404200080402c90f007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 285353048 1250 285351798 285351809
    0xb0a0305101a060301062601031b0608070e06090a051504060f05030c16020d060f022d0301150504091514030a2a0803040303020304050907030608150c2101 68
    0x34400c200e060b0b200054503960140d94035034030500a1005001040c49820030789094103000804036100f2081003004080c1031320030b070003c0d140001d000708421012106210000020809440c0040081ca01080c000305080100c01405200e854001100a82030ba038880c92000030b050010665459462510f4a100ca141d01c640301d50001300e4454031429204a0040c1c00b80c0b48103036104054149000f40c1e040f07034105c140c007a081c0100e070f00440b01c84200e80420b0542c40740300c248540710200140d845500048891180380140d00d01c0294075400d0314805620308264050b030381141c090201241825404200540c1c6500680d00a04042441e003e0301c460a100c00c202554211071084e00b5111405c1091400d05496544071400a00945540104400c08482d0361031801d401c44080d0b105161b07a29121440b50b41194042d80c4150016071010030f06001381d140038640d03240c00c1181820104440c44c9460410307038a8110307071a10040701352030460001c2e41586569045a079488401100001005c181d841d202c0082442070240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 285354298 1250 285353048 285353051
    0x3010c050c15010b04030311100504050115090b0d06180b04030c120206060a06050a020109060e060603061e07080a18120908240901140a0906050c09010c150b0a030510 73
    0x401c4402d0205622203050b00c016101d014903103429500c050700c000d003aa200b9030100e8403540c0750384890071500348686c6024510601c004036a146030105500d42035240c03604900a00ca00d080b00601d50b503510391840740f0300c1d10f601038000705860302c1c8244500e02190403810007408052102c410041050b5200b401d406009200e85545810030b82224001c9079203540407100290800070f00c1d0014440390780200c1c0901610046d80c4004180300810b0b69807070094803100d28031441961700160a1041c540f80600c005640001080b00d018040d4840e0380403d8020360000c2c00f0700c010302003182c001c221a0304a0b034001d150407540410314a0030300051407034902c017104a81c60b00000003581840f03000c116041c010880c5000a41d000f032400c036007985d0400c0d410600030405810030559660301d00759501d4a090704580980308040c014030004080403c1d0418509480c2d0041402100e02d0003004001c820303a800800000348644c101074025401c0d202a0704085c000d00480816039031042c583c03600041084000103a0fa210000c6c43c420 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 285355548 1250 285354298 285354313
    0x213090506160206070e220603051b01091203031415032a040509030c0609030406030629070f0204110705011401120f030203130f05010e090c040504150503010c050c 72
    0xc102c015007034808202c00044c2c12400100f9001442210300e05440c081c01015102d0f0b8043e0841010540c1b061088681c00003900d03040104280541481000e4245030f140600561001a11000920312540da01175280340260b44074514041c54401d610244203400011038254441c10034212502c106040c0c082c14601c24410070b090303040500120079001d0b010810179000592190502402c00c070140c80010554051488148655803445034100034460055035a00d000d90b80c0c9030b040c000018156002500f00303004c00300e4036006403400d0780d06000e017003d5104c06003140c2c2d6486003110700e0036010484115502a6016050840c030556410b2644020308030184070310020010049690b5000700c00c0d075424440c0151456105a250000c24004980000c03654482d2054928100605110801e1100030b0382201000764000d0314144204e5070001c20884840e40304640d00d540c40e2900103c070180c40c0c03040e409031a0169440341a4444074050f4030503554050036004000744040140c801d4002c1440c0c10010400c8124841d181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 285356798 1250 285355548 285355561
    0xe030a110c031b060f09030a030309140309010f0807032316030603081204080d090b072c150702060409020a140406080403030519091a010614070615030213090506 71
    0x18850f400141281d1000b81d40a88860804c210350700701d180300c00c8207004100076443c926a000e0001d04200c91180c1c9000401e04903d050080104549048440c1d090703004200090f800c0c0e030800d49005140d00c5503c1d1070400795a030084201d0180c4851803601c1c0d4800600d8408030300f41c100c9a14100d225100001246000c904807010840030707200c0910000d4080340c1d00300051750484105034640d650040c050b1141a00d003610300c44200f8116030304004c00f0764007901240d0900542941c408440d140c0c404d000600701c080c500811300d40024402e000011380c1c3c4101e00201c00756440000b6035055031b240c940c004000580b290741d6007642d00c011f980507048841c00903c500030f201620000603825107054401566815000b9511036409a000f00000b40940c2c50302c560728a203645e0026a00d009659049102d000c00131913001001d1201e070704021068002000344403200015822203c0514240c4403920380040c00031a4044031400500c0c821000d43d08042e400c02404120150341c0c8900b07802114a0030b100310300325452503a808 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 285358048 1250 285356798 285356803
    0x210518070614070302070e0405010c08060d0209062206060e091e0c0a0c0606080102092d0f040f05010e010f12021810080318010201050f010302030304180e030a110c03 73
    0x14007030340021544000840c24840180c078040c0180381e100340102d600054840c1300502d03000c801160115140d80d102d18956042c1c1d503120042035000442501c17025080c2d01564000b48403104003c1401d0300a0440001202100070511074068110443d03020030440280c80b8035000302100d811569203801406045d01140c8080c601c2e071a002c030080c507184010002501d4043e84119a9844600075904003c1516100004581c261049400a100800005959920700030500c004410452010701c82040700e0f031418125289100035a0201d520115000d0040500170b5000030010502c030300d00900300c0fa19000021407000c15007031020307040c0e0301c0d0b04000707000c0185d581441c92aa80403c0070000d42140c1030404248070444000f00f402d81100100d01080314076529003031200d2441d0000070300c1e040351000c40809880656028844c45400400d003103943c156660440d008241c0c0d0348218442c0b05c0881d2480004415052440c0d40070328880c0c00b005059030365401c0c103404000c1c1910380d442030009150090202140c2e203445c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 285359298 1250 285358048 285358063
    0x3030603120a050d02040603020d1a0916050c07030b0603101a01030b0f0301111312021e03030409140403080705031513090b040f140a030c12210518 65
    0x2002000d0041c0e440e00c1c2651203420091821050140c02d00c10b00004110314000380002c2c0c9155a0016264910341000b2000d8642c00e24500c0d000d00b051961012480d00c52000d51a88010306204040129114040451f1207106001c0c014403240140e8401104006a540e455401407400f1000c0315022005948198110f4546181602481c030f610120700d4015402174002000b1558020314a103440c40b4140086401e4418160045140c1000010030301c0081113509100d03c050005485010018541a800305185005c1002c0c80c400300b803d02d048401280da400c00458010b02150402070100c6400500e1500700380206031011004078101c41c001070078087c4200145d03845040b5003546480d040010900b808807420106491481c101e8030390100001207509071709420b000e14880e280c07500d80c50390a801c120030460315030307042c001c0c072500305125000119a0050030025420f030440b9880011030003540b000d50f940441e9100d2460b90041500d900313544a8026800340703204103500005185c0001902c1807607a00d80b00f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 285360548 1250 285359298 285359311
    0x306010f110c09070c05011407030f090803010b1e1209013b030c120405120a030212030c040302090a230601050a0c0c090509030c0f1b0d210201020702010905030303 72
    0x844503074042c2c0382c544021895001183c60400e0080d00030710f13403940d5003901c070481c0c120076042c0c2014060102103603041c0300b1401c0c10320101c1000c0281e94400e0b03584009070b02c4103110b030380c00c3d844020a82e0f4003400500c400703004040c0000d98a41b50313900c101080140000c0c00440d03000302103501e4000306c0c02d125552143c1e0400b0501c40c6000d02d401c40342d0315030468542001e54588040c0f01c0e02c400c3c000101c04550401c0104506500503000a841e80d00c0c24040150090100c1c0c2c8417002e542010a81c400065000200201c608001414564480e41c0712502009940159071010b503016000b28144070310510300d41d01401e603041e000360003c144404520022810610180c0766680001c0e802c100581c0958854a40309410300d10410f107008490f070760741c04114140e81c02030300d60048a4100040141c480d40303081280485a404807000b604501c3e08120404554444076034500b8040c50316459074508010380c0c0131101a000b4041c4444150402001c0341c000d000390000c3c0c1741280400e44d4690085840d03d400000d90f0301c140d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 285361798 1250 285360548 285360553
    0x30f0d0e04020f071e021314060a030b071110090606030b060a0f0506070204060510200d051b01020d0609051501170703020a0221070c170d0e0307030204110306010f11 73
    0x4107940d1401c0c3d16500125005d40c1d014030b90410040181d03203810b0496607004851002242214039880496082000500254800ea007922420000554400e1074a544506281002000d95070313000c03040380c104000301024445482c642004c900c10405103510040950b40205001152551584103000204111303020340040295118400c100e1031412200800c481880600045203190b59140410380c4440f00d0002d1002084c405188070904806c411560280f040c02480240000c10080d0f001400301c0c40f17407241d008407508443c4960300c1c08642c00d404407030605090040811106540345c00e14401404142e508080204681640c80e076151310038500080c0c00f0001c0100b62560352540b213000d400941c0003120000c107601444001035500d02c4014420f0318119180981079646050728034213a202c4580079002442c1d0034555503880b11071900d00151134180510141000d089900541c8002882c00006620095015081c401448507030950800a5030103140c00b1f0b2204246140280401e84105d600000c0f10321856 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 285363048 1250 285361798 285361807
    0x109020c100b0f0d140c06071208070309150c0306050301020f16020307081b01020c011106040303052802040e0a020406210b060f1207020601060c080d0b030f0d0e04020f 74
    0xc0820340c000b254140b0010001404803010b4404a002828900e10540c0c0b401034044151000c44428800b4400d0301c2c200301c80003460b010705980c45100000703542c0900800c1003800310000315002d00079404000d2068100403640c00030a481800500a0891a01040300007814850002201e003414001c0c1d401e907600c071138049070a10403201451950580c003034000366807510074010001403e40c403d01c2070008854003403042061301001d040000e894600d010780d0080c10003102d5803007849020004115290040d41c140380201c0e9545996201c2141e00545484002d0b2074540202003080f0202c031a03005108440c912510344421355107046a10b403c900440c072800c0c01040a05810104409104c0500c2500d000701602c001111030600f004160729801001055444140015015100000c2041c107280c2c8458503200400301581407500060810494220040c411b413008684000700d07040682080400d4080230b002c803900307040c42080060b60f1700100c45401c40411405140050035003072030b000f115010000c02c01042e151 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 285364298 1250 285363048 285363073
    0x2030a1a041a0f04020403080319060f03020a03020f030715170a0b030a0f061b030f0e0c2b050f061b0f0a0c051515100c0c0302010f050408030c150109020c 68
    0x20000301506070702c00e17400c010101c001505980a903000351004120020310142d040d090004490158222990010242400b0070044c1e4410744d10100b900c0d0b040d01d4018090140b100400c0c6003c84680012128030040c1c450410300c194001c0e20008920007000340c1c803150303444910340502207a2504010755015000400072001044607060700080540c40b808002034061768280f01100003411040c00e01c0000380d21580718020428050040300c102e58404000362118030802400908010a09440d900404a0020140c90102c4424103042181908101910401c201c11084107860f60300441d120941c4c0c00196206850f6400f8034400d0b1040c0c1503000110910b030009800090700c0304c5964210481e850f1081c000c1900051000d00c42c91030055000c8803c40500c0f0b011030040050240700b921100c000c008000200e0800301e02100d103000110b94080c2404d200310502c1c204110380510894100c003609200009180c0446180010312285111204001002c02d0343ca8466000036442080f11181c546c0d80300581d204030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 285365548 1250 285364298 285364309
    0x1b0c0b040821010b0310051903150e07031a1014010305100801180302060703020711040e15040c060813020904061104180626071202030a0602030a1a041a 67
    0x8403810914148415100c24045140b5040b0090f00108a1010b0100600c02d00010320660070000d4401243e684424201c0b0000100a84510f844080d101c03601010200c7c00340c2d1250744c000c0d0102a00ea80940341c09580324181204040ca107121a440080840c00000d215000c1c00a03518095030564400307032406d060540011405810094001203041e405042d001800100c01d01c41c0c2848019207080850403022581406401c00000070003850501d40100504c2c00090300240d41b00e0a40e6808440009004620310882841e0607050180c09004020940501c418001e2400b204c0d0115002d0b960360034065621142e850822182d1404001d40050381310011400081d4550012983d032800c00013001d06165848000d00210790b55014080c11603591200d051202c4802440102c0610b260081e01d4898840a00340440d0b680d0003500c1003606102520700c044045540a11044005030740061042d5201d061900c0c2c3e01004044100000040302001078000c94203040901a0044041940b001100d044502d1303428010b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 285366798 1250 285365548 285365557
    0x227030d0c0c1d0702010c03060b1606020409051003051204031502030901090b01150212030702030403170f0d1b080f1314060109062d050d08120a1b0c0b0408 69
    0x110402c0c0c41c1180480d15166102c01003081041c04400c0840c02e0416240203807c513184100c0304020107040603410701500c91600e080350256010310041c0303500400d0740d003002402806190007000300300d8200814006041c080100c2481500e0050041e03039a038081c28810ba500d070340305512004044541c00d180342030f510f03413460780950b502514100001c40c0802283e50754104102d0260000300b41680442200700c0035560404c0f80d14050724811940510f50305100c503010307603a40102d100080a042c45004101003600c0da0340c0607294030b07402c1607003969160488100c0f01c4014003540320002c40e1160480d03400a42c454420340d03003540070303100c04041480c42d038030b031114004100b8a608105440c41034103011103000d040341c10080b45009004000c0001045410002c0c038200c6445007401141d01c00c0c2c0b50070103a48003255000c0b03842e01160004c43c0c40d0390a5148604c0c00c8459030058444044c040705102c001c006510240d90800b0104214003904000c032440082d80655002080c0c0001400a01c0c1d1000014001aa90002007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 285368048 1250 285366798 285366803
    0x10b09060915040903030509010f050f0c1b0106090c031b080c09030a0b09010209010e06120a1a04090f060b1801050904030e10021606050c2d010f0227030d0c 69
    0x72a4142c056001040c141c03052560120b00280d625400c021440800784220500b00c52102c005100d54146482e295019940c0036040c50802000080e01c84440c684218407030701d601c0395400081c4295552088080010503080d00081c0100b03060554684c0140b101140e83d902d68982c9031102403403600c44039404580c50b08041990f0340c2504c1050755000104040c9415140b02d441c043c1c0c00903076a58a2a800144007207205103680d80240d00900c0102c3c4042d00400c4001d0b4007800b4280b0021303c0100c41742101822001e105019030b001442c003652203041c044003009054140340207600910640c0b000c0801e0211000c07540c90b0411105c400400140101d280101c19a038120b4041d04e403003100080744d500003a40075500d610044002d0380c00405170061b1760941c0c00845006216034205079040a021810715600d40c3d40180050752440c14100c20001e00c80781c0705055400284592000700203e142e1110814000c1d40491000c13102d9104002c0c0d40714180902c20108030004034040e02901c000f62111800340c6000c14a507204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 285369298 1250 285368048 285368071
    0xf02090f090d0f030e3304021e031606270b07060f02210906060303160209040201090e070509210304030308190f06030210030c08070509010207080601080c1002010b090609 75
    0xb02c0340c2c44d40003001150b4961b0049500d10105400d1700720480700c01e1030711842c1d681c0c00c80022010040036a41d204440003030324103031880300c41d11202040c0c006428070b207044030007110150202c60003090803079100000d04030f080320000005580d800c607465011006c20607807240c0c003c1124104500000a0043e030400b8000f000000000360404818901d01c0e00441d01c01003d15090b031582d0b10400480c0c1e03000700403032600032100780c01841ca82094030306102404039171070601a01a0786060702080440e48183d82403801003401103544134503810284070050469101c40300710b40c0300300300c9168a01c01c00d1410b40c01e031000038642d50380210705c0c00d481c564040e500b12600034465100c0d5070000080906c1080c0328080d9281610171a000000c0c0e2604605c100801841d04003640701c109890318101c15412034200c0c09041c1c00000c103040c030366150428500100d1600b48503410091850007074030b0002030701e6100001d80301881c1d00b00700d070b01c0c250300500010100c0c221814030301251340c480401008600c403803c00c00c5403190065649240d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 285370548 1250 285369298 285369311
    0x6150f01030908040812070b0f0114120f0609011505220e0a1401050a050f040203071701090804030c15111002030a02070203190308090c0607060213030f0f02090f090d0f03 75
    0x2d5400c6c02ca00328004d0004030720002c1d200003000701c1e09110982c00070000308201031650414045c560104104e540c41e50042041003114241030750100145025644040102c0d020791804510450103006620100c14041074406004902450300c07a01292044203041d8240b1880740c3e0101451300a024007038803481a0713000f0020004040b6064001c41c08440001c90000300d0720741001c04070030080710801000311510462000601005940200f214402c4178102907421114502082c0d06a005000c1e01030000d141035400a4008100300c10640020202c0346952410b418107450400140c40301c1100e6904683c0382d401c8015000c0040c1c606602540d0409600100103043c98950b60109140504200000802030840c40302c84081680c0a0322a56110400c1000342c03072043e4919021420301d008003040140401d40110b0201c1c00451202044402950856411551070b2000d0901e01104811402c0c10f078014801e03480000c801030100034610f4011341040c0c00900c0c0c80810018201c4000209030800c0d0b04054541c0c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 285371798 1250 285370548 285370559
    0x10609120b060d080a0c030e01111507020c1206090106051002030d1a09010306050f090d1418030102070b04031103040302090c0304030909110a03180302030f0d02070c1706150f0103090804 82
    0x1809000c2c003d0b485d4a46c0b44c5444828100a0041d400c004600ea04000d0350360101d1075885004588000501c5060307000960326283c403402a400c1502d0842c4040d00011050f1040c070300312400044031401044e0b06002046100c1c1ca607010b000402c04d1104c00440941d0041000f0f0503110030300d0b80001c0b4013040c20701d01e01c44880403007400520302000a0b80195441604d8209201c00d550070815540d4006218000524070302c80c0d44c03200a4862054101004007120740420b0350085040d036074502e0410380b6401402103684190343d2a0814407400d00fa00c050300043c51800e14104a0403002040310b0503260020a07800407035490134218181644020011400c00c601e010300040c1180f03160181d12040702101d0a00c1e5103601001d0303001421600300e03018280d54041c0c0420070300c0100740c01000b01d0b04449030307609000c1e0341c40c015a08030f580a0b11424030001d101a0304c0a00c005401e840e8680740510103c210000e480681c3c13a0f031a0310100c0b10a121049592001101c02c0c0f4265643c069030004051510842d141401c1c26030340c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 285373048 1250 285371798 285371813
    0xa08010c0e0603180607030608010e0a03020717010b1921050a0b0a091b05180c0d0203060a08120d0b120606010305100801150305010e0304060504090209041b17010609120b060d 77
    0x191b4405010a80b601c1d0b090001074402e004125840252000401100500351002507a99001e40700e01e80710b01504040b400301c210303000c3d0840b00b011000a018540784092000e00918982502c2c801d405618918000f403860b29141400c0c031503009a00000102960780141d121000c400754054a058025682d43c41e0031000a1091404145000d5003822340d920550720701400d0084e0701d003803c0c82d41c1c03404a070322000b00700c00000018142e0742552500b50300140c9a581d0b0030302281008409801c184138600c40c80700c22000c254141c1008004948050000f0711543c0503450074004500e03c541a40070080d0803030340002d00954440d0340800d41c06000501d40c148040d0380c41c2c83d407908444107610b2007005084602d00c24020f0200034002c200120a114000b9450186040001800f5000da03028822045400140f0b5008554494102c82241050000b66600c160b204d610b026004280b003181682e6189840c10000071880c1c00b4032501c500f213849030003100f510703444242c0d141905c01030020240340e0b003d180180141c0225094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 285374298 1250 285373048 285373051
    0x80a080a0920030d02190609080918070306060f0225171e0c09040b280506100905060906070f140f0c0312070f0302150709050a08010c0e06031806 64
    0xb03007841c03520303505001070034941041003080d40c035000c4d54060f03042034610520009007042041d40203240020f0300d601518040145200d5000341c1980304d056007502c0c0e465054074040702c0c4c2c0a000a61000c0012030790310901911240d0010f40307000d01507040403684003a0903410245e81c40b00040c08030f04080e00d840e12029444440b10011700d80c084154402d80c001d00c0d10095807102c414140c24998002d104100d40300e00002c05083c4020030050000b03030b0180100c0d84e00100365035010304080c51102940c100861150701400101800c0303605601c14448865500a0316028801c03010940d20082d22841c0303404156004c0c010582c0c000e1104880b03ea044c1c00015001c28020210840e80c0040c1e0b40c0606070300003121920340e00c0d00c0340c0c01c00414881e4110052000350148140211580241d002c01040840348060130140e0801c00c007100c400c0300f01c0d01402c0c1003186166022890f8402c1c1c0718200c50301c404498503000c0d40c1c2d02325101c81005c50f001ca5248a003060203841c2074806076034040c102e070f012243e50b480e066500d5818440b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 285375548 1250 285374298 285374333
    0x4110a03021c02030c120a14011401140916020709110f1219050c1801020c031506190515130f0605071203290d08030103080304031704080a080a09 64
    0x40d81a00c82c0218501805441c0b12250200d500006003605010282d881d00d105200c018001401080311740f00030b000070f400040094070841a03510f0300e503a4614000a40158059141d8414000d0000064031031025200a84000c5810381c003c1602e83c1c18521004001d00c21460541030500f014010b4a04455899000b8495241c0241000b070701070404410035030000c1d1400c0c00c01c81c2c81900703201c1082441c079088000c4daa0079041010b840c60110000c0c05c0181d090a00280322943c25014081207084040690348400303004000680c2c2c0040c1160b0701e841041c0344040c0074010154042111000741151880b894040e25024502100c0d551240381d88040305240014aa80143c001c0344d004641a024441c000f1341201148880d4101400266148030340100c0010495410429002103c41c0d110178a0f11003000011034194440e0390a962941c41b03090214250b0001c460440c001403095114502e0410008890390049500c2480e5504106080138265983d00005140340819543c0307040d07a00106da600c25020783c4940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 285376798 1250 285375548 285375589
    0x1512030316080603190f170d0902011103040815040201140309010501030203070e01050d0b091e06060a1202092a0409020a02101a040e0f0a0c0e070c080304110a0302 72
    0x280c0210702410055009051901c6500100100412034440300c801c51102d40e4080485103a85c182440c1200908080800c50740e40c2c0318000c2098014000d140c2d00c000009030007600c0b10b11840b6581c10f1155601c0c4541e00038174400d43c2101e42c40c541000c1c41c409406400a01c1410081c1038034891070300c0907003d604101c4c2d04101da6134580e801003041d414180100d1000d41480c0d81503a11030360402010441c841618400240000000000520900001d020300321003174004500c08021300b100090001c0e40d441c0c095a005105400d00080003d1450600d05d01c581e00950207003e4410540e1a19042000d40c09480d06501030500b10720030180b40711644a00410181003045001a12030a42d804000d240c18030016485220600d8000008403010b42c1c42880d0740c0300c0e4400c0740c01042400c142c890719820140e00051414044c8100401c0e4404c11030710144080c2500d0b1141b020245075078a80c00210b03081d9001c00009050847c0c20030104004c65041c220240d44004c003d070480c3c1049507240d005c501c08030f0004000310b82aa = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 285378048 1250 285376798 285376831
    0x907030c05030303040c120f020604080706030b030f06160c020a0e010e0702070602030306040f0b13050f0915041101020c090403091d0405120a0210060f05090604020a0815120303 78
    0x16a00500d805044103030020750840c0b4143e43c1b40910300708540103020602c2001225142000842032501d00110f0740944102d40300c65964000a0342c8006900a8501281c10a86080b41e1810006148602030b030550f4014440c07a00c450700e0751600701711038441420407c4a400305150258540032150720043c000303440184d505626013401940c0080001e0040360854100c0d6a0801070b00ba4000142d0740c2155003150000347c0384400c0d19648008214188406400829095068075201d4155003c030b449140303001080c201ca0b85d55244143c0e1542d2074134031542502100030b00840d020800101c400419018180103c5a0f40140180004c0d1141c0c0e04076800c41c0081c0c0307030b410140034041003039541c4c11205000d5528400d20303060569400d82c45117000c07030032a2414100801d1070b10280f40b0070001040381401d024401c21000b61241306100c200240c50040600421040313000c10752500740b131b10840340c652000c0c0e5911803464440f414a00d000c090040e480c981d001b8180e00b0043d034644002d0000354040c03203203040b0a0141d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 285379298 1250 285378048 285378053
    0x6060e010f050a0c08031f0b0706060609030c0e100e090a05070501020c0f04050c090a0303020307050c0604060c0b0c1b0601051809030708130b1c140606040302041a0405090703 77
    0x200410746950004205080c000c802d9800d130000c40c1284442d5101842c00d4132170344e5042d1941d00c1c41c024016405030400070305500090703600325a40206409030042c0d60a104440d104d6100b0b65002d003003488001c00b0f42031074100400110030031050290308084518911100d03150f952011041c1e0103800c0d50603801c180c11180d000b078204031040009000400c001c2c0082d2100c0090140020107001e485210755000d035488000150f054644281147c00703643d0018940c0c010207407a8203000350f9a401c8504100c42c3c5119070b00d420f1600b03140090565089070320300c0d5a551501b20141e6960b000040018004000c00311007440b48603918400c10901070039805c3c0d201e000b000760b98901010081c07840001c400a0307a5540700320041c0151844084100c5001e02c0d04040305a68442c8c4400140e92a5030042d848000d8404000c100b07409040200300b4202103e0200017002e00c080f11a2485400310307510705031500380c3e2140b800c02082006040a030031422506980301c141e442940080c0010400384c8408440d40030132a08421818000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 285380548 1250 285379298 285379307
    0x110d0e060906070321150902160b1306060902130303030b03070b04230609030a02060c120706020309060708010f12020d020405041a01080606090f061c030518060715021c06060e01 78
    0x100d074403201500380076903862400c403480004a030f4007850100a400107003451082c4690421084c0f160340c0071082b01e1103490700c1750342c40c540c94160040031200d95062070710014000c00b43c1d000f581c0300d5929803010088401d195507412b030001c1850548840d05809103840004050718680003038401410080112000744e00c1004004550028020110788110801d1042a0b0583c03400104089055815100650307210b94642885290114080689409a0002a100701000240d4002e5409010568100c0c1c502e038450280580b4699400d004500d080e050744041041111881151240307420f001400078140c0c030081f50046010b4031812a0b00b43c2d80c80c4400123803010361400c641141401031203424003130301050508800003051142d02400d5000348001070800700b0840d030340d0001e200f030b42490540710b02859007045250203005031304800c5800708210140620190310f82403420403144442d0340b103113007002400d07000b01d440320080d04030b030034036084041e101c0454030006016441040c018001a0716852200140b1200051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 285381798 1250 285380548 285380597
    0xd1a011806050603040b13020d05010606030b13050601020c060f041a19090b030f0c040801020c07090612030507120e0a080f0c0d02060306040e010b04020703110d110d0e0609060703 79
    0x50083c00c0400400004ca02d20f4240720390000c01c05043d2048000503800050039000c06a0320160041d440e1400020342e25426500440b01c070f07441528440e00250b0041c11202c101e5104803030550258100003c640c0c40c0d031502030010000c3c1154041203030700b8241c80e009010300f00940704051030091140040c90000c42c200c8240340403100182c1d85040707410350b400d00c2d80c54080c2d030201611101c0b5481e400c002260501d0fa00c481610003030306200c8000c41d2a44680d1030a56038035045031085825180c82c10b10041038070002100d00c0f100c00740d0951900351400c0c00b580e4403c0ca80c1403046a4072401c0155900d445461a6100b003030180040001100401030902e15007459410883d140002920580c051020715005841d001d042d41d074080700488000078855180302c080703809001c241200740c4e800b510000303060040641040c840e01940d1006c004841c100d032101c100c195100c0c44920720a0b4035a03803054040280c620b03c504007510400d40302601c11800c6c84203041c00300d00540c114003000c0340401c00d03052801111005104949 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 285383048 1250 285381798 285381809
    0x3040b0c2506140910090503070f060207120f0e0f0414070f02060c090f0402031b03090a050f060601050301210c0320040b091504110409020a1107030b060d1a011806 72
    0x64150a260340c01541d10300e000031040051541b030703d10000a2002c180150307000c2c01d4203c0345442904003180342400096000302011640e004a5110700001140300d0317910890884601c0c0c41c1d805407004c800041108007804a050326501036104c01c0720610209500744028024200d85d102c13030300300c41d02c1c1100181c241440245030805c1c0c241d0070b0101c012203564900001c20111401e40c0d00503a01e4913901c0e47e43d07114800e60300480101c4180041400b503800c0000407900100c2d4094030640e00c02c004842107041d1240c1d402d860880c0010020300061124121441c2c40c07500080302c00c800b81000300d90740e640303582d0400669802911091007100d54549034100510022000c2c0d20b00f00c45c2004826400c100040c07654601a103401c08082c1d06440018807070302d41d5840800c400d04405003154481360b68000c0340003c0d5100c1c00007080003400318819000350002c00078108065961041141c01650386030300a20a0300c146141d81503c00540008600b101e4045041d80103020304005400e804180d142a1070440a40342c559100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 285384298 1250 285383048 285383081
    0x5040203100e071503022a1005010f15020a210305060f0d030f030603061410050a08070902090f0d03020a02330a0e06030106030204090b041103040b0c2506 68
    0x186089942c0115400e000c3d500c03408048418582c09080841c024021f0f00700d0147c05126280c404207005651480d80c0703488400403801c490105000201c0d0800b070350300a105100c042d00f82484d042c400013900c5501c51004c1d211900c115040030030141c591040c4240003c84219509040100c000001d40d49070094680c0541d0580b407541d0002d942d4008036102111100300542000540203022000740d1194018400454010806000240040b0080300d050b020954075502d000003d0100044d03039007071210305241100c0c0144094110759181c00c00f048069408001c01a0344000303418001c07074691342c581140106103402980200b031301c810f442c4144400042408545800d040305074070345a0513840001640982d5503440541c40307880c3c07118200107036690300a041e131155000d10040b002047d038540c07641c0640100c8071412801c0c4000c00c01c000900048452101d81d40036422810000680802c140300c14080e0000000c5411514051140690b540e462a854080c450701a03800300020080c040b107401201c1084e040502c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 285385548 1250 285384298 285384311
    0x906050a060c11011206051327050a15091e020a0504020c030901030e0304030b040312150b090d0201090b040b071106030907031217010f1e0501020d0e040f0c02010504020310 76
    0xf90030050704000310f0203504000a115448501d090207410580061030b02030700d107480100220303440c0805001071005101500361411001c1030700042442843c411645c0020260038901c219442d06c41c1920030300c518110030180c0395411800066031650450b41c401c251108180b00448007881046507251031076002d50b00c40d42c0180040f148881d801320459040c2c0c5d0007420005035980e84c08044d5419401694030203001c209c040d604200505400860512110707402e9034080040c1130a4606103800c2e041c80740aa84240c6a0500000c40b0a0908072a40d035102401410590302d2990348a00304140b0742c2c0030342c121a000100114002040015030150070f1005841124060b056103015030314070340d4031005031001030105d005032014101c455020303030480c00017030034200c624440a686800c14000c8840071407040d85801b80c104003d0f08000380d000e1303090b10285c44059020b000f45000d285021182c80c5481107040e035006540b444654400c007090710030460003180e50380012483c2c0c0742500405040004c0d400c0b84510b018180b48 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 285386798 1250 285385548 285385553
    0x60303080a09031b03020a0210020a0b0a020a18090605130203042021010b090903070b01060e030f01020c0106030219060206040f1a040b0f180a0f06090203070906050a060c 75
    0x205580076403400c41c0040d00310020308040f81c4102c6014041c0c0ca84008000c0014107155000c9207850104d402580c2406108101c0f110881c2e1720840d1b9540602107a0780540881e409500f030350028088803105203000406009e030000b0700140807002d5480890f46580e41d8408020701d0910780d140310700c0310060450860640c0b4064903006822040540020340310351000684010907a1399803040c002202c2203c0460321080d10706002c0e14024080c80007058401c52039040011291540041141c6a4690000c2010a80c2e481d011090300c984c01c100078441c0e4580144051058400c00134400b910350308071070500100c0e10394554018070241e00c0760400c299003c0701380240c06011982c2c0005000f0f402c181c1c01114061a0692420801e0f4010704001c0c00d440690540ba007804180243e044003d40160400001201c640d10740070504881c03004c003415510102e4003d060401301007001030f6220105a07009040100b640c41982c0e001070705000c1e440c1c02c102c0e15155100741c01d1066081024102c8041c281c2414524450b03240354 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 285388048 1250 285386798 285386807
    0x6090303090405070c1a1005060702030d030b0f0301090c140315070503060a0e0103030c020102060f0709030f050708060f0a1103040201050f3708160c030804110a09020403060b0301060303 82
    0x40001e01d01540c2c90b00c1c0482c0315148070b20440c10710030750009621103541e0804400011141d41c280c0b016400c03130306c05400210701441c4c401c08807038056900400030000c1c0d2501240980241040f040c2195001c42d050007807822030b407003c0c055040964418030000120a0a000041c09260071000b0114002d90040264800441c0004a40380c1c2021131030604680700d80d19000024003030a03540d00b0110791888134400010415420403596100240300b6000c1d80d030540e80b107284100c02c180e003c40e010741c005400e501040000caa0191103c5c6181c0740940c003034900c05031300c907109a0301d043c100f0b44410003400d091908010411045210300d214145040d1003d03840c609181d00001c0c114040d6900c1c0d070022440004000100b809210052030900e503c980400020f2181840344c050804420300000000c0b80034500025120039840445500081c0c40b9194807a50f00d04903202110f44190090081f644503450103286410303540c519000c44020441070380050b03a25400d625000040e9241103541c1b80c0213030306049090001a400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 285389298 1250 285388048 285388057
    0x30b180423070b07060506030607141c1d2d0309100e04050906010911040503030a0507030203070b13060e06090c040b0a030f06090b01060516060902370506090303 71
    0x103000d0011a5681c1c40c00d0a9040404603072003070201d1038000504030208070300ca801c603501c200021010384505a88948003641c0c0c120440d0742c00240032108100c0442c21400c001c1500c80e560300c800703100180701c00305006444a041c900300c0c3c0b0b02d0010340c00f4000f49480030005601200030580c080703032804242103c20070300c26940d00540c00f5440c86550103401c6800503600c561a02c2d81c104400034814000ca0070030700da000352521402c1c094801010300340003810050b00c00030000c44080700c0d800703001541b43c1141c402049515070880e007001c070114001004207402088080304403d000c0c0c02031400842c0f80c481ca92078400120341e142c480b03000c49604008104400c0b0400421006421a401e8901140c41c445040000b103030518550001080c5815048802c0140b2020b58414024a071050001d5421790f602e4907000d48403800b80188103c0e800030075a4680001603015040511b1540c4040d01610b01d0200713510840140310004440f000404511042c00c0b0743c030f0901685414000e10007030341c1480ca0f0059040201e40c89204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 285390548 1250 285389298 285389333
    0x106120b0f15060706240302010504090908091e0301050a090f031110110403110102030c060a0e070302060a08060f150702151213030905011d09071e030b1804 69
    0x300d200020b803903003040034070120030a100103040360b507103040d28540030004150700b46142c4020002c0c00c41940104007000805801c2c0c2381c050b112942030620b004a0240540f02c1130b08116a000d0040c001e410f590348400c80680c00c9000d603401840c1c100e02d02d0200789421980014280000d650410b0b4540003c1842c0e40d0400810580501e00748108400254800e8988002002c5640d2018901000300e41c41d4440c200280054a106000f0050302c074800c000126540e000f01d0341d0211395501b20030040760702000c199001d441e00405040039a0307040350360f0381c002441c19001030a518012588400030403159180c52000010800c1d07089a201054581300c0ba5440024019000002e015009107050f03454042090000e80d212030f62100310000503031078282040c20101c0214041100401d400781e1000c1100e40c026000d10584240c210001001c0b103405008110710074101401007400e1108bd0301c8929510298400c1007600405981c0f40030850302e07969428000142c40a5000d24104821101804000340410044124140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 285391798 1250 285390548 285390571
    0x3040b01031e080a031d03031620030a0507110301060e0105130e0a0305090108010602010506130c03090c0e06030f0a0206191403010906060801050402070309060f05120108010e0106120b 81
    0x10b400e1082c040d41d02ca555900640b40c0c0b60086084c0803400d81c160410035001c13094070508442c00041200680c1c1e03d01040e941c178040304ca000001001d5192181c400c5000c0592072482c4409103003140d010040c02d503402041040000f0310f0004020050140c0006c0c3e2948503030050300204001071a009602e4a50601805198422410700c00c0700c0285009540140281da041d0b90300f03940d42842d041c40c0140c21a03028056080c081480702000040380d50042c40385905c038840160001d808c1c1034080120400a0205c10210800d1580d40d000c1e26003c1851000c81e8406864150414611401c1a8040500d001014240c02002d640a210300300d005031900c400381c035400f10740d1984c0d80d0f1080d00c40d11003d9884040b192145a0001e902000002d19008160005001c89415440e03003000d43c2d8855003400140d01c40d07008082e000c43c001c0d44c0d0070800c080c4200c504081f102c1c4d5514120b4103141d84841041e800040a03801050b40c3c2c2e458408681800100f8850a002440d80018010b811861580ca2941c54400100942c0350b08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 285393048 1250 285391798 285391823
    0x112120e010309020301050a0902090c0301080d0e150307111209180a1d030706060f2d0b070302070f09020301030c17010204030f050a1101050307050f0c010b060c0d030b0603040b0103 80
    0x69001e40c00003c0040d60040c0240b04500d03100110b0401440c0021b4142c0c030a81680002c1820440108200da050301d14050240c0f10700400340d0025250b407850764007800e4016452a5802d4001f001c540b01a500075001c03a030300c0b09030030700010701014a00080c0d0034681e14994400c22201041c1d0780c038450305160300b407102c4042014035038072401070746c00030144116400841900344a0344051150f0200041c401035120310010066a074542d0075516000800b4000c1ca6031241d03c0901180d81e0440c1c003500c0319403100340c001d0000c00564440515400750b0b0802101140540d07c00a401d12401904954400107003092140071070966141d5240c41c022a8454842d01050051890341c10b8a100020340444c0e0145030803558902155080d450b0055940c41c044400380c50b13540c0c0fa0200e0034621340c422004c0b00d004120a80c0d5290a08001010a074085c1d0312403403002043d51758400102c000d0391a0f07207002c1c0850001c031b003010342444551818054140c0391b21b04169840745004004000010762a0101141900c1d0040d0403040903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 285394298 1250 285393048 285393077
    0x20d0c08040b0c030409110702101b0507060f110606011b0c0b07210305010e0a0c021e03030f160210020f130305030c0f01090804031b0b03040c0e011212 67
    0x5901c00c1d9007080d0100307a4002404500c80d800080140704903090002d007001a0012203d0031101405001c2000f54420511111100058400c803001c149025000414030841c038001d6a509242605c40c2c0c2c0684041a25082841880c039040ba10324201840a070700548014a09100000e03ea500d0100b900e81c0c04002849002090020591242000d4980760030080d42c1c80303401e4200081081484005a50301c2040d5809044a40c1d100e0702035181260500b814985194079903c541c06c01500340068180114441c4440c1c010700100d01c114451180c0011001869480c20910010658820001c0a02c10b0b0000101c8600d02e400303500041d4580101906240181c54003142d01c1203200d144661658452441036240c808002c5c00707004401015074100000890740c0841d50095407a081e100c520070003074032880c0300b84410804516528030036202500c0e5034400c480c041da2900c0c0f43c1e851039002901e007a284501c04d243e040c44680081c6002c0360140900c1241c0c40c4c0320079841d64898040090b0040354204119941c54452803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 285395548 1250 285394298 285394313
    0x50420011b170c010e0a0c090e0c041a03030318010c1106040f0317041202061b0405040e0309030f030c010b060405060d0b0303090d03020604020405011d07030209030a0b0112020901090507020d0c 85
    0x403c0c2c00c1210080c0300c10701504010300d0f540c40d50746800b40c511006807000060000082d2081121003c2c100018001080c0b10800300b00007445100c40034108601c6a61441d00d25980034801140304410001c4028140030ba4140c1d1603086420301d4400c1d105100030b01607441001c01c000103045500a81c040c0b580c4000440914040340d0201000a0340350309403030418180310410015181d5400001007950884109958062404241c03119100008203407d40400c020f2103603007055002640c1e0726910030200e80c54503080102080c9024400c0341250419040859034526001083c041c08000c0c5400303e80160400d0700b0b000011f05240b19a50800011590f1820002c200d520240140c80c0d01d160f000f420307005010b00c01d0030081d458000032201207105525040011821490060702540d112200d4813090901d55a030f001c0540003940308180c02c903810302c101460741002484041d0114040c2c000304001e5400d01245105100141c101070b008002d01504240c104581c031540026000400c15403483e00040c14041400d0406 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 285396798 1250 285395548 285395557
    0x6050301170a0b071e1e120605030d0804060c090b0307080a0902210105010b0a020a1b1a07031b080d15120302030c07060c02030606010f050d050420011b17 68
    0x1000d210205080141c05031700480160481c1d0300b0b046810042118048080729400c10b8000880074242403001000d41c00b40c4588513010710190608000502070351168006450040020fa4641c000343c09907003000204680c1b03000d030b219040440e081120546003000045681c0d4000106907400308050710300041c1c41d150840e0000c81c01d840e005410b24418000740301c0c000481041207540d10000d982801d00029900480300100c80c0b459145a02074205180a0380d5841c0000072811314501d40380c2d080000109405483c2009411805194400140d42d01c08914011f40a0b020a0310103180c0102c0d004000780c041803694080301c030882590000001c105071035110480b03c00040d0340010074841107144003401059000401416200c039001c046400407903455900302e80d48090300700c00075010f07081440800c00070350103207114419070034250038401d04118100d5202403c83d201214180d880c3d100c8440c011611854a01910620550a1805510320380e02425403042d03141c0300b1070004240b4102a01c550f554004840309a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 285398048 1250 285396798 285396803
    0x190f0609080310050a080a0f0812070e0f01020a2105120f070908060c0d02091f09030c1a040b0f0c0601090516030e100506040b3706050301170a 63
    0x100800802814111080d4200f25036102503000ca2440200d100d14200c21524100c0307000000612040f9442d68840341025007950f8101d0b000c0034240000035001c0441381c800d80c420b110960b5460412600d041c1001860120400300b181550003811800e00030413801500800075005000105207010402407003210307a8400c2c1110b140c030b4032800c14240700505983c1c94405010303140640d514601d4540342d400302501c408041d03c006280500c100041203c80308142c004d8400794000a001c440301001103801c0d100f03a1420360484000042c812181071080141d0000f00b040a01210340c00e2120b01d0342c411000410512a41c090003007040d2011803002c0c8000911070407200c20050b0303030043d603860356980d50200b8050402911940e8540903104a034284030743c42846068a200c82c140c006100c00000c49517000000c2501610182c0c00ca07482d48080344a603180d9058240044000030070f0184148500720300c00b00425a404840303150841d11040c100002ca501c0f03401e607810755840070142c420750408510203601e40b10544100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 285399298 1250 285398048 285398051
    0x71a0f060123070c030c060e13090204060b072109080304030201111204080601030b0a0c0f180522060f050901030b0c04050409061409010528110c0703020a080609190f06 74
    0xb1608203c420046541180d00c540840707640d140c0c03103c1007506d66251581d2456000300b004101c204600b009504000d42c510300133800090407175120b00c4116040d42c0100c50540b14070b00e01506800800030100030312041c490b1941fa01c0c20703020b8104128561603108500c80a810044003035801c51401c041882000c1c00141c051884c166555134880c0a6502c0c3c1000348400d460b8a00b14034002401c0d0445400f812040601559450300402107580e402c5c1d5801000340002c0118504905000c02d00d601c07400e0f410f0b0650440e210141c80c90410004e0180292003003501300072503540c243c02042010391640c0c04000d06403503105c0210401907842090000d0a0b0050340d00580e8440c0c104030f0301106000d0340b41d014003900f800216404809503240c1034800c1c00d81d0403e458186120412030300601860020200384500d0341070009020504450724206a009074015440d8208990401401007003189130460800c0014140c82001e4442c0745000f881140c0c403048903a400c03004103840c08c04041c0800052840d83d44059512500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 285400548 1250 285399298 285399307
    0xc0c1603050c1f09090e01090501110301140d05030a03020307020a1b05040c0e030a02040b01030f020c011431030903060507080403090f0509010b180d0305071a0f060123 74
    0x51a550b1000082ea80c18040d9407030700441d0181081d2100c46842d0301006840d96030300d85240c06041c00051200e404068095580c0341d0a50001940070301074034030082000e0350029125414a0f2000004601c4548254840c801c402c0d203140015402005850f101c003043c0c180140c482d9215001a424041c040340010042654034500041880c01c0c181848242da00030b07070b810400b8041034441a22003d10350800701c1d0745540301080840040c5446e80003004100e1043c0340100703c1801010113441681c104040324503282c0d45901700b8483c00144540e55562120341201020300c010020320350742d01169109401e1030607000d00c451510040c540180c00d038000459000004001520b0b0030303c00241144802e81e411000034030003442c001403c54903030480e0300681d90018801c803010b034603101110a03181d1145070003099110f43c043c1d50078416901c40301440c07821400f903141d581d519100c0e4504000280400d0040d00840c9207503100b84104940741c041202c1d800642820011111841c0140070343c900411651201d20803c000138 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 285401798 1250 285400548 285400553
    0xa02340603090c090e0a020d05030f2701080415150509010b0c070b0a022806021c0f020a09060509040f0e010b040b0303041a0f0705010f020711010807080c0c1603 71
    0xa01402d012401400c0070b00c0026100c1505000380d81e48003e980300181d010007010340140c903140c1c5441710340f9031003002107904d01760030001084000c0e01b01b203030601000a450603004414041a1100003191002440e04410a20f0183c0c0e5155004c0c43c00001102f00640d41e101d06840c000100301450042c003030040062620790303036506542900e548804074900c55405802c41c00544014410181ea0135480c0540192500c1e048041c1340c41203a8080402c402c40c00841d0094242c00f05860384010103404141d0002c10724100d008a00d0b00742956900742641e83e0071807040046480550380803410368140e400d2403503d6a039030407001700060003402001903030b010001d1810345004c6030806c0540c810140c0a2040e142031000d903201d441016180e0140c0c2c49200c40c0c400c01e96141281c0bd800481c028603800440003503641c02c00a135078440d513084030040a00c0e081c52a5001a0781e00a20200c02d1104142a600f441c000013a032400c0b40004221a201404400b420400445c43d050654418464001d04441c214021040d81d075690 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 285403048 1250 285401798 285401801
    0x7030605180420010203030106110703060207050606032407050a030207050f0d1202040e13051204060903031710050906040f150e180a200d06090c09020a02340603 71
    0x98804403070581e81101c10440e5100c298565180c03070f9405030090750842e0300e0711030280d40a032684548501c1c0344c010300a010001a209201038030000d0f0003007004008502d4600145032078180ac407440c156500d110000826000b0703040d64195a8090b4161070202e84602115406401034052014024914080c44020744810a4002036020900e1100d94803400425031450340302e012441540105614407140100050034400c460700e140941d940310f1401c0350704407501c0301031981194100d40c10120008070147d00c1041403613441101515526001d19204450342005c1c41c5110b41c0e0305103413154500560807080001c506544a50003c20b0f10380f528007090000051035841c0342c84418103400781c0e0070744c1d80e503680c0800d2829182c00c0800d20600c1d03070b00c0020210b141c05911000d00c20b2042c00c488500918a05024088039256a001201c115100e9a00454030005038030f0300d40310300091500401c140c0c41c410301080000750350018120400380e06074400701d416010309002d111103202c0b1350752049003500403030b6500040c045d905 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 285404298 1250 285403048 285403051
    0x61703030c04120c33030c090509101a09010806010f020c040c120204030b06030d0206040b0114040618090203010c030509030d271a1608060118080706020109020108010b0a05120703060518 82
    0x400c0480c044d40d0218507091b4201e44110071610b0004110030014080ea0520504580e0403818410309a60020303540e54007903442d4040c0c1011043d100c440490007010b1940c0089485810450074248116a51080f20001b580c40d00400b40391803103a516540506900d5028500c86c17030342010903103419035035540c4a003805a1030a500b40c0d031060180c4180a02060f20350303c0414a0340c086c0e0380c041d000c3c0b03403280d10f4070b080c5841c19a82078603e030394444d030746440024202040c800d01d0348075858601c0001c10b04030303803d00415007140c46520442e401d05040c0f908100071030002108580c5803903ca80400201301d02c1c51440711943c00424a40e804250503007034000301c28803802e903600c030178045c01ca404000301b1941c8003407841c80444c03562040d8101185850010941640c050318200034801d140707541c140c00c807654400341c041c0b5000d031540c01440940d40d10030401c42956400520103024042c020082481c200c2213034030040c003520800100c0b201d086180c101103035250303210342c00403001854010024441819502050308103c00d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 285405548 1250 285404298 285404369
    0x106091a040e0a0b0c09090112031205040503030c0d0b0402070b0105090a020a120c111b2b170c030403080d050f06100302030615040801061703030c04120c 68
    0x5048030403446518090040854445004000d041d8001241d501c40d04070880140000c1e04988042c085c17200d1035100d40c0c02d00303030003405405001210f41d5814140a400e51410f207100007682070800040001043c40081202d4004d580f4030405983d501e001a000d500802078050780d2703076200340009050402e01840d001141c0c1130791012540b95129881742420002207100c0d40d100c410200c1c82d140002054203030386601c540811000703400c02500311080406581d050051061100345056440c02d1142c0550614807003034405034012500348020001122000d103a4107075203120040840c40120803080d0b03400742d0380c4291707503440000f0011a40c40342d407285450102608941110300200d031900c4002401d0400d101e941d030b800742402501080d0000c4564200701d010b0f500040109800c00c40c242d203c4102e45039240000c1c0010320220380000380c21804d24420804010800c9844080e6500c18402d00200b1054141110122010015072003081c00071072a28056002c156071110310301c50301c4514000c000075140c07080d03034944e140d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 285406798 1250 285405548 285405581
    0x6030c120f0d0207180525120e0d090515040b030709142704050c0604080a0b060301090b01090e1006080d121505152203030807140706150503010609 65
    0x202c195400700d0b903030805481003454003c1c80704100300c022a00c65120b180c20019602100c1d0b040314003915045900b019403109400082c01d07074071018000c100f0314443c19504141c0007024010398004000024031555041c02424850b0341c0c544004d070945008201103074010200d400559890b032400c1c1e90090720000091143e2101d000c40c91900403494074041400301214401d160180400710003401b505841c2d03140c01402111b4a11840014550a42d0385d0009003006080240044c04050242c1c600070110060160400d0b000768107001c20a030000304e1000d2014151040d2401c0080c100541203402031074041e181031120501460f007040441c12440100d00c07401c40780c0c4540c55050808c4210049182220354154140c40198030004052144c1e250010010200340d80b1201f58900b00003481001c400c0030190b1410139203504910480400800d904102d02e07a80c07183e8181000c1c60401d40329500c00030144500c0e00000c0003107903240303c110030f0b02c0280890b440203048050001c124440d00d80d550400100310f540852126107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 285408048 1250 285406798 285406813
    0x40b030910090f11030a0c0902070f0c08010b15040e06010c080d060612150e0c0901050d11030f0a050103150905010e060901020d0f0219030908070b190c02011a0906030c120f 76
    0x1800c1c005055840c0981c09100e03401d87c145450300c2c1c1002500070314011100c6444428a450100d60700030001009030005500009010144004100555007031164801003480144070801401e01c1c50011036a1181c1d003820094180769080c0391024161280c502c2c08100715192400103d940d540c40881c8286101400408114601818070700224040042c030a1100d4604290000740103156101c001d06145d90f01030600764105070023568010b050750100c500b90000e40402004204001401924298102c9a2420100415410b40d22001d5642206215280c400e41e1a1002802004000d600a5080174007800c103486c058102504a03034041c2d0b10074450a80458100440e003145000d95200300c4541c2000c42c2030031910369400440940150000e048151642c1c4810b0148102244522001601c1201c800e4031200f103c04120300c0f03400c00c403000c11041804580c5402e0442c0205101441301080c190021038a2050300c0da6003034000780c17814190000d92038000d900940c01003500c410000c0e40b07105080303400d001e0f224003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 285409298 1250 285408048 285408083
    0x709090e0a050604120c060e010e071710051012061e0b01080406090501061e06031a0d17092d01020c010207060e030109020d030206041502040506040b030910090f 71
    0x907501216805000c036003004000c9000a07aa903c1441e807041003508040d03100d1401c54513a1001c8825110b0f51fa211651640344003000d400050080c08003070480c59032984854400c0e00031290b0b8402410820484d42561100410114410000d8401c01404c65281580e00c1c004a4500f20300942088800c0d48000d11140c26075036078401c51030050132090390042e03640030244e54558030b030070010b03060b00b510540e03aa5503640000319647d00320301d188020f840030103107001120600d4018010121265a83c4400c1005001d01c00c07030040e907031410202030b601c90f0414000408a001c0e00750900242c450b42e02429444524007145000318201c81d042f00a07a85880c0b01070003540c1070a10010390311505082c0465005030011002400350364002e8401c00c46002000d000061780c048554045100c08050510a50259100408010400c4417001c107202d0041008401942018a4600419240c0c0158003c5140c40d80d00032002031200360040207038841c00c1100840c10f010803401c0c1d090045ca4180c01a0f4103071460310401e10ba400300c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 285410548 1250 285409298 285409303
    0x1501080a060605070b150406080607080109020a0c02040b040f0c030624050316020f06240109060e06180910031e1e02061b010204060e0a05030606010c02060706050709090e 75
    0x111112900e40744d14010785543c032124143c41c02041c0000903c140d50796840281c84902c5260301130202400103020b142001600a070200038160b2001250038010081581450740c400034400c081c5505840124101d45a05c001802410f070346000302900524102d108003109a154012030200d480d042070442000c0755102c804807014114552590106908101260307108210003209460350f00140705039030342c00ca0052180c03410028107076422520685801d00100041e8448501052410002d003031002c06145800400361804683c089507030310070200420095020001c80c440c1000000000307181034084d1400c02494040d00c18a408103403410300c0c0306480803a040c2034070056210115080441c110344100358158261003c0c2d0342100072600442d0600c0743c20419000380c004040705406030f0001580742c80c18460b000302888040204603204641c0d9240410171500c0204105404c18001e1800006800301c1e400403413030610500c94000d00c9245840104215180c2c80348044040d10001c0c0020300a04130901d40301503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 285411798 1250 285410548 285410561
    0x60f0705120406090b040e0112260703030c0f09030b15090901020d11030c1606060b03190b0316150c080706090506010608150d1103010e0a0203190308190209091501080a 74
    0x114400c107200140200c5080382014007010388642800c0207003034445206000445079985840b4030ac4000811040b0070160540512400c40f640352420350b881c4600540001c00d0800144009010120000c0101c0c0d441100502e078070100d0f80303000d0501c056600345020968002d5014120b15490346280c06141410342a944003260300540c03242111a09100201a400c2103045584a045504039900d0000154050845003e035114500d011064250316081c1c0c0c80f10740560701e1518241d4820b0b004941d8000d04e01e80d4506105041e9031190140c485141980c034000c1c0c41e07648a195005e02114800314485e0208062034001c02d024030b2241e002d0396440d0366100d900351503500b42074406c46164a00b81c03061401c1c0e810072400a9803400c0c0141900340030603005101103400c40e60702d4032f0408070a42091010b902941001c00101c0368511101c011500500c00f0b90310007c0401e040a400b0010010300d440055049902c1e036010b40307402c254010600104c50800d0100398482c0701600140f035012030342a00008000b05a18801d90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 285413048 1250 285411798 285411809
    0xa050a0507091505041d0f0a05160507021504230102070f060c05121b01110a020606010c290702011b140901091205060915040c05060f0705120406090b04 67
    0x100110741420703e03801d4098065682141005014400005d44041c00c2d12003440003085014900c69500301001e100c1e80c3c103440181440340709410f103424401e1802c3c8081e184400250305140030754680440d0710000b00303038a5013002c800d504c00e6408a008600c04000400100512406441c9800c001c00318000690700d0300d840e0312031b0585010b00d00d601085440d004200c99041c40d8071601c1524101e43e290380d002005a000010316504125880c441d5078126242481244007030418001414145040c001009544050040c8001d041140c0711441108001e0380d188020380144045180b546030749020300e604080720302d0440f442d000641c01d11500740300794240a150244110019660061211044450710b9107503407180d218030341000080000011619403c51012000d2845030f801b4240b0b41c20060182480c00800813451045844100305010000c3d202104034404c550b400da4943d601c840d10710b080f005450007100e002410703034000c0c610010841455040180242c90403515000981030300e81c620502a80150700a2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 285414298 1250 285413048 285413057
    0x609140615030d0525140712021c23030304061a0a03120507020a080106030c0e1e0c09030114010f060c0503030a02030c1303081c0e06060d020301021902060a050a0507 73
    0x10248061050b401041700501000500b44856080c40b00784804443c142c0041d20740d4000c082855800740c10510200e0300401070801e8904100103281c0015690046540303440780706004507001c240400c0a401d06054640b4141c4050a00e102001c0303080a44961084408807011880e20311003041c400b03940c031807902c11544003410503d0007905641e81c03007050b884049103800510106004c140300686c0d96410040140070040300104000e880d41c50003100d08901c0c1c1e0402d80a40c15458208240c000070300b0150f1405ca82c0201c0c080c10b803034a541410440314400d102c40300d5015400c049101c00d00c0e080080d10310703049503048000f40302c9041c0d9542048070a040c3d807620042c4240c1080020500b4130120380c0140d0382101d00345c0c00c2c445c0344c4181d0945850a2041c1544115801480410f0030050080c0e0140f007400c440e1180c2d070040c049041c4130010b203a1980002809030340704030f81200040e8155102507041d030b0020842c125020b0b88103010101c0107581c520041707071400c6401d4100340000f00341d0907241c080c00740a20031580740d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 285415548 1250 285414298 285414313
    0xb090a02071a0f0f150a08010614101e090b04030b06030609030f04060c08090a0f0612091e15181403120105220c2006060f010c060207060914061503 65
    0x1609a90700090300c61000821707010009401a034840609000030030b0144000540c2030702e0560b10041c00c80d12a0409880b40f0b0b201841025520f40002c0030818016440070645051140c0040556201000d900000519800402e0100402050f80d005078080c050440031500603039a00305525560344074070a0183c3e04000140020002c1ca400b4200c04001c261143c0040341c14148410302050034003010341d10580001c01941010082c19420011004400c0c0d03890a05002d0320001d5150007621005100c3c030041940d03980441310050140359030a284c912003c1c490b0070b1120b4030036281042030141c14a40103455481c8100c2d4105c008503400001c403171410000c0100020303168a402c1c00c000541a01d01c404444080384c07101c828440c64441d11424040c051035880700b03100b40000c062515a084000c0400c41029403020081c055142e960030b518581c07800c1e00346041400d812040c0b50890190041c886c000303018038106030a000420806035180d9403050400700c11034680769520384d2500ea05e0340080b807400e44c25812498 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 285416798 1250 285415548 285415561
    0x305100621020d140711030403020105071104090609030503010906060302031312021504061a191701180b15030a0309090902040e0d0e0307150915030b090a02071a0f 72
    0x8034081140700d2912001410700054030005001c1d00d9003400d01030030240d105010001255040303500340302d0044070100214141400c643c0080c0042c072a229000e0304030841c50078139140d030707075250340190031100c0e4041d0061000303070034038500130f08660020300030314406608014000c00c2c0684680b0a40388a0107814503540f65484560301d0709a0680080e000315021030040c00304400c054601c1d0490b03a4003e0b44601000103881c443d803140d481c0d510910f0325000d40b0031648840c1c80358441d00314081c08010b03102e2450003158519115111306004201c40c90480704101d07600031a203000e0085801c12944581c0c80e101100412409540c10551141401ca03c000d011406813001403000040340c3d844030050741d2010f000010a440780080f00740c507040200b1a0b11b00040c912a451600d01e007010300807c4001d2841c8101c0b078540010811002e01010654059a0307907440203910030400b81d5102e500140c6010002400480e42070618038060700103036200342020380b001c10800c165801810390b134914403445460040805a042d03115030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 285418048 1250 285416798 285416837
    0x90509010209150909010509090c280602010f05070504080a0809040f02042303010614060306150a051815031305152701060302150c01020c010f0c03051006 68
    0x50442445507609100ca94110307292070802e21620345030445540c0c1c88804240400003030300b205800690042e0301c0b01043c0200c0080000d600880404200c5898008000c908486000344040b5021012603503480c4000141141c1c040d4000c00094950000912050340c0c1c101050310103208030f22424842c0ea200309a542e022410420180031401b40040c80458602e151001c07000680e0001d41141d00011903c521405401e040700b01d07000308820041e8006d010451400107803070b004107070384070140f40100800170002d022a40d980e204640720703c00095a03180c4400f6103100080a03030304503054070414484048941e451a1030210b100305480341244600d00e02d103681d06000580d1000c221b440c00c80d02485002c41c0c03503041000d40e0203414802e04860500c6280c81c0485400b000c0140241c0d03025001c280d141c01814009030b2910583c1c0e1886044a400320b0f9951500c2c0007100380240705108421842c0c2d40707007c500036032000468003c0000f20b4001d64080c810340d00e504906c000140e410307114120101c0e8150000c02e040c080c58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 285419298 1250 285418048 285418051
    0x303090304171903030c1b020f04090213020408060708090106030816020303072103060504020c0c010c02031009030509091609061b06020f0705060112080a05131205010c080105030a0203070905 84
    0x2401500d581100c441080b19250380503282c120046500c1c1d01c54603128940c418905028204000300b000c0401107c0c1d004101a02500d0021302e0055071551603413030540d03c0e568142480708202c00c1c001c6644580d070f090718070f0701c030f01060703c4c01030000307680ea800300e908180c05008510030749402c00885858518100a021903013006414126010701060040c000854030118500c0d0701821640380402c40201080e000400703d425580005210341d105022682050000164400d040780007800d1040d14000c260000a280001e003001171841e0030b00f4911072608059003c0013509107100107441d0081c40340ca9240500c0302103014180c003079002881c0c0c200c08010542c443c820020b07000c1c510342c0c540140030307040d40c540c4010703a8404030b03122111900c00200c0c81d0411030b080003018010300c412580070208401e10703a5600f02611030700e0404000c102001c03880c1c1d0321111400002000412540c2ca14103440b16062910070302800f90781c0182808501178000000e842e0a0110307102d0a4642d0013030240c00c1039070402c810320005010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 285420548 1250 285419298 285419339
    0x708090108040c180515030114190902091911040320011e08041101020c061209030d33060c0b090c100c060c050a050f1c0507030204080705030303090304 67
    0x120800001c80000e031501e1580900c0a07008007050386d280c0300b0900410442611040340c0282c3c5800c408484045210f09800e41119010702c0c2c043d0680e0031031000340040c05444030040e520403200c906201c8601140944501e03500110780d014018146148007280150084d0b2101600038514800350300120fa2942d1030307015000b0014100100200c20180d41c4813405e6103031050381c102284400c4280010301041030300c54080c03858244000c013041e11601010074181d0141c0c59a4108980b000303400b00c0c10b84201032095804d030840c6d5401c01c000318010320402d41c2b001c0601da048540040b2000e07101d018100c1d040c20900c0103440c40c984410700fa420107544c600e43c0050006240307000034007030380780103111551341c6812a029100c5203544409425540b82004804c80e0500050f6030240141000b403007c01035042416510414607149000340c031110012034803a41048058a0745c00315a00d4082005111034160b4080c0c010780c0d034603d0031120450f44070000e155803880143c0310504194002e120400c14040c1619003900d40d2030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 285421798 1250 285420548 285420563
    0x150a0512150f01051e03010f030c050d0c060c0302010207120801031b0303020c06070201172a16030c11090705030a0605151801091d0103031b0c06050a03020403080c0a031103070809010804 82
    0x801d003c0607442545c03c280c1103042d48c011083c1040007440648107411000d850116030000300001e05903100c010b07100132031080300c00703120030300c20104103060007941030700c11058000010720406524078070000e044000900080380e44a4001482007224459412080d0940e03134150000e0032402a00d4040050581042400703d040028059103800d00500c4900400c3c003c420f20082c1208a401460140311500c103c201220203510081c010a204040150b80800d405600343c03c242e51400b95030300b015600c2e4140091803640044403803050186080e4031100440c812810524104146d0b5255810003101038490a038018001314280000d08010454039019100c0003030505202d54a01d07a02e611f151558907204040002d1503503940e00401c00d05400210a15100d04110761000804083c0c1c1e85010402100340601c004201c404202c8180c2d250280c0e045401858104030400e4540040d21034090b500d680c038400480000b214007100594058002040e90001603110700c01500b0045868011200c8010041c020348034039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 285423048 1250 285421798 285421837
    0x200d0e04110c030706020307031b090b0a050408011503020a08030703170903070c15030f05040f0f0303060503012a080c070f08040e131b1203030506150a0512150f0105 73
    0xd4070803c01051407501c078480142e201d14000300050203e0f02e40030b00350390030510700d0358480c24426480702031802038844820340c8540301c1e00b241c0000c0305c0e43e0090340c119030641d40c0781c489c0e44007a03044800010002c581c07003201c010044a4450f801c0d2034407801912402004583c4094000c0c40f000c1d0103051310782c8d0011018048078245156a218824243c03d181e0100111a10041800f5a059894090000b02d04804417090000b418107a407000c9245071460400f5101144441240c02054803a03005000180401002880205401c9403045004902d41c8040a40480300e85991a03c1c240201b4038144194409190b880c104460b5444516a4100900048694410810020034410000156a03000790091900d032580c0380c5141c5004442c50305030001a81464500c25006c200d1080c0580c1301034880d40c0c0c581b0300460152103020206400c0408a00302004104000c00c0018405070300030054941c482c1e0042000005403510000c07141c9a544814a00c0d8100d9007213440411035500840091285164401190740306 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 285424298 1250 285423048 285423067
    0xf05160503030c030f06060301060804020907030608070f1e06020606060d0f060e09010c03050f0604201224031b030c040501031101090e061320040303200d0e0411 71
    0x840e407080381e90f90384031031001c001c2c0610300c030b480d500c410307803144041e65032034503650525001074040980284001c5c4541507590019281c98444d400030001440c0354411111400d461b540c84110442990080100c4c81380c096140c1401261601c1d9002c0440b401c0b90003908039900e5550038071031282d00140d4561041c40c0c4071000c0726501e072582e02ca40002083c44480540450805603003150030350301d071402020308060500007401040a40081e002350031240482c0c0000303041c4205401c071300800c84010902ea1000b030700481d02c42681e913503e41d602c0380714a00340390307000e4080c00400f101403240101003090f03690940d014980d40e4941490500c812900d40c0002001c889181070b9140000702902c100340c00c201c030000c0643d911103a50396006108000507100010501d0640d180040124441c3c141c0f840d03a400009844100c040c004814550044003400480c4020a070f03a181c40c0e0902070806203150703021519040d51607040d41040070000c07480c641140310039560250301c12515000c2001070415860f60903100c00040144480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 285425548 1250 285424298 285424303
    0xc081203131b0315090c0503010b09060103150b070501050f071e0f030e1f0c1d1c0203370206030403120e010905060a0501060503060307090c0309020909010902130c0f051605 76
    0x45544c84002c00d4080151402c1d07417102c110399100600980c14026450b00c256203c0d10f15543c090b0702883c002440b6443c00140480b03c801d80d80c00610030181c0000c0910034410103420044c45101060700d040443d0310780000440e10f80034060500c03240d05408010550050340300c2e03641443d01d06040d150214842c451b40422a040c1000d10340c0c5408060007003044414008124043d034681c0d8221030400c20100321092440f0800044051880c9214000640c2c2088005401c11003c40200d43c01804844840042e03000b4045544921503402c06200340c052240829103000303c0c1651062a4040c1c04507042d0b407101e5905079032104503d8205040e290700c0d4039591018100074403031440114040e00082c500c5050215840b000c881042e0401340c100103007041040820788000408000703d4840003c00030320f088a52608900070803045200079032080d00d10042c842071100541046528078000c6032152606503526009174111407440c103114000c1040f441c01345030740a0140001d40120300b44003818000240013030f038401e070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 285426798 1250 285425548 285425573
    0x110903030f09010201060f081006060e0609060c0a061805060901050c09060a020c10051e032205010f0603060b09060f010e010e01020a081306082d150d0c081203131b03 73
    0x4d01584011403274000c00509024840080031300c3c0c20415a6000410702017030f00c40c821018024012480000e820a500788100700601406810080c10000c00503295501200144c2180d01079a2a10601c00840d45c22a4103210f00d80c0101c0900c0c41403868186000f00b44030182d08211440415070240e0b920b00000c58481500c1c03e4880c1c80c8503a14142d40700d05401501d524020038914845541c04103008001c0c07481c645d200e0600e45d10305200030042d020409460042d01406244c1440503805080040000422805802100d481c40040341e210300030341d235203405010f0341d205882c0015000581a01038085103500a0006800e00c000620543e500c0207059200c0d0450b03036100700125002503418910401030a90b2261103141c010462840c0740800500141d211690035014440f820011080000418a0407000020100542c0300c0500003481000041c10070f04542d01a03813051103914094a000d90f070449040d002100d1003425111401e01002815482e400004143e40303018807080310b407007000400400c2c1c041d080c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 285428048 1250 285426798 285426809
    0x9060b0702271f06020c181902040f06090e040b150d022d0102151605040503011b0207050d080301120501020c100b0f09041505072001090204110903030f09010201060f 73
    0xb8a403120f03054880383e90300902a4801011504556030308100b642d01c05c03a0841c089442e20038031045985a404590501d44074840c80c1c010720030701c0040c0c00900c030031200c40d0303c800b03c0384203072a94140c00b682c56000840e8140215001855520740000041c1c401317028240060301c1e640050019036160606a0208840d050a000352075810220b004e071301070303505a00b1408040c803a082031010301008041b0b560503da103680c0152000c0300a16000c0d212038200f6101c1c109480003000300800030310000400c1051400901059801c140060090500202c1e09007460300008600d40c3d4051411403031340e0310b081c4446c1c0950401c054122101c2d5004c000045800720104109410402c2c03074000029a0300c013103410804542074554480780240360680801c00455610b20507860b1224501801241541d50f50380c4c1103412940da4a07411000710101d83e00f4400c800015804200401d1007a542003050201c4507140191b2406080c4139a5459402081341001d00c5100f007001e0700e12000c041c000480d4003500c3e41c0b500d0107109800d8010303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 285429298 1250 285428048 285428071
    0x1603110d0f0b151626210901020c0d0302032d012d0504150b1b28080a0c05030a080702150105030c010f0c060e01090c09060b070227 58
    0x340126440c1600900342d0030108605880e03c1e142d03012601d04011000404041e00041440c280c00f0010315005e4580ca2a00308481403403540c1d000c2401c40d4102e00c0e94450301c044c0a0000350f0001803120310051080f40c0002c1081d00081c0301017040c0d03110441c041c2d48001c1009100350503900c0c100146607850300d039402e042034504001d8038003036040500c025040610b502c0d003486545031080f620000440c1c01c4074a8000e50718241e5020072101e0031f0162201076400540e0020304201000a581c075820355074240c00002c1e030704040c420b0794908601300354100d102400b1450801c0122442644d404001980a802031007500c245040c250b8100a181d164642150020900200401c030281c0810500d0365050003d554180390111aa0000d5410000403940e982007050721141031011b05a0440020340c02000d48690540e406030007400260320202d4140e0281c00207240c101c071308280100e408900740c051070241c6010b55598010b0b076400c100e2250204004848080d1210284010307140e40c61003410702c08aa000d01c0341503540e05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 285430548 1250 285429298 285429311
    0xf150d09050309090c030f0408070317040c0f0b070203100510030503040605090a0915140303091224040b0a0515030313050111030909041101091d0118051603110d0f 72
    0x203111303012400401d0f80b5a410300400421864009442d0f080350001c0e040b101f069203a06261800742c4036150b4044905c05021150070800c81001040311040040e2022550642c1516607207004051980c098070500a503d0b4110040740d28a207015540300952000d800e00091160700e41d0f039200c16055a00c2604102d00213507000801c520617040295004004081141081004882e400a44001c0300711500500400c00c04400040003260740810035980050f80c000c00751449044555a0713159a000500e4041000f120410030016001480c0046280301d00c2d0010300c80059503842c251100014040100072005138401401c0039961a102000500602d0201543c01803141e800e000000d0a400120074408030304d07500401401c00300740c5408403666042a4040b0ba000c040c40040300040c0e41c039903c80c1c1c00034940034613001c00c131444404015454904071810440402c00001402e4103a006903136044510f6402112111020700da141e200354406a498040c91000314240140513400c1d4040d40c1c130340d012084120b81c44d41c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 285431654 1106 285430548 285430567
    0x9090a2604090204080c0108100603051009140f0604060b0a0e060903060c030403080609070f180e01090609112d0403051504030e010207050f150d090503 67
    0x4400e40c0c940e51a031414900a401605c50741800c0c5c8612000c2107003d500940b4894041c8072000001e5402a00b410004d8010f0f042c0903003a42c000b0307030061100151403c1e0512440c04081215004c5088a0034842d460364408076002c0d0400f8459890302c42c080108180202c100c0f80384640b28200050102c000c0f90004815008690645825026107420405043c0d01c0302c004622451103602c03045034585950062201c00c00040b1001d40114020108182007540035080b083e000d00c500310f104440198541c2d0145c042000213034440d90059403100018030145030306000b028940400d0401c05401d00c4209000000c80205080503800004024900c0c00450612041100e01a540090485525143c0c01c1d40107a210071003181d050300046c101c01405c40d01c0b0b610100b1350408603100244114841420601000401c801e0740c116054940300400064100c507425010b007031600b50141c009140c8403101075 = true := by decide +kernel

theorem cover : BRFrame.Cov 285251798 285431654 := by
  have h0 := BRFrame.cov_init 285251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 285251798 ≤ n) (h2 : n < 285431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
