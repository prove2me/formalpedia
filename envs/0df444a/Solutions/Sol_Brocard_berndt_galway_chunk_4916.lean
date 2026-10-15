-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4916
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:09:06.249683+00:00
-- url     : https://prove2.me/submissions/b894b3fb-2e2d-44f5-95ae-2764f984f2d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 883992805 ≤ n < 884172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 883994055 1250 883992805 883992817
    0x3060905070f0303021b0613050f0d14070311060703171f06030209010314041e05030c10051f23030c06070506010302011101150506030601020a0f21031a010302 70
    0x100448004980d90b400c001d800305070a800031401a00801c6400341d444034501407100400b00c0403690075140100a046a0004001d0740c401e02d80030340e02c0061162030355a905110a503400740c005140d52600191039201070f03110715030f034041126543c9801c0071528450400d9801d483c095039040c0c4441e00c0581e142840320100c1d120050000034240014900309408544014115008080940300586c540640718009001e0b180810810440c04110750104000700b80c416905902100e1200c0364103410182c6410014110700c90503840d80c4040c421100620040c080b164030292081c2d21100b10b200090031700c1d500c500720140c0d052151a1180340c1c00302984200701e909001c03c0b00129001400c546280e2421804a544c0343c0001d18142c43d29003241d4010030030f65070008191510040d00308000c000d8040c05090190030320f00701d8025140140800300015096900801005421640100e42c10800758000d01d08824a1052000800445c0014040b114005c501900607680220305c00301840c2c0035042c900004500a403c08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 883995305 1250 883994055 883994063
    0x9030f120414070f090b030102090a120c09060803120702160519030f060203182410090906060501030b01030c021b0d1a04020315041524120506090f07030609 69
    0x1402c1c002c0502c182c1009944001e0014076038000d0101d1601c81d0500803241070600f1940264010040c0e00515038170400107506407210b80242041401c480d080c05100180c0c03e030002c03080303249010004142d0300800409802c0c100c119141c40341140d528240c04a0f200c2510021401b0000503440741400a860551081056203900c64000d21040b6aa62200790040b05501da00b83c581907800800c4c000007544030403480786c140038404010007540e0700a8481180410401e003100d50b1851842c408110500916520f0070020245003005101041003802d15074000c003a140f2a00d80070916240c0034600c1540640140c60404c900e035005407082c10621040701100445819005900c07014588088000402c000355070350b2902c44900d412a11440c1a1041c103240c100340a0744100c0101100d403c100000300b00741d116050688a5400100c2e42005d2846829641440c0f040502d89410031a800410741c02014001485120700883c00c0b214540c85a0803c1031302e034210350740d411106802112003440422215080000c1251203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 883996555 1250 883995305 883995323
    0x12112e031b03050115080601021002162a051509040506030f0303040b1f0f0b0a0917160e060109030f080c07140424060311040302090c0304020909030f1204 68
    0x460302000d0040c008120074140802c0e520001400a00c034042500b0800703d2803400d1404113802e0020002c0d580311580d1030507c0c3ca440d00000e5111650041c510041020340d4092501c040c450249002001d62440520843c40c0c003690719180040c280c0b410510740da90301562400c4281c81c0c0131035041400040d001c020b1a09030184030b102c2ca01e0813045410030056115902404d510001410215052200454084001c41a40040100c00d001591012221000702da2a082c2400da84c0d0001050668070056940c2c00340d600078075840325269001c0310115007401c4140358201500b114a49820042d40754041c00e40d03e1a0014005a105000040200c95203600c214010b1445074107009004000728070b402120782140403203003200110421981407a0107580800d1015164591b003460660060b507054900c01e2242004040e2201e034621083d03581001224090360b0042c00350303111442d1254814000d6030050311304030b000c1c0421000280c04c424001c81568015000c42d00240c2c94541408070f0203101e09800f42c015110380b10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 883997805 1250 883996555 883996571
    0x20306190c08061f02161d010801090206040501110f0d030605211902120f0304051c0f02010807030f0f02030907210308040c051c060c020c0a2d12112e03 67
    0x10007041c00320010840c1f00200d001e14065105031400000381070b802a0156030502c0000e8005949010075a41690001c4c0303071003210b012403440c0e42c9250605100402800d0300810f5041645c075645030b0440d0b001e4031000e4a054260781074600c500c0074000d200046456840e0040c03201c0d251000180c04440a070705000801b10001c01c070302c40d84c05508000f00c0300314140a58ac000101002702d428180b551a848200311404490000726a031110961744262100c001d041190400005d0303a198000d51000390301c00784409040046240c45c50010000390300958881626108203a400107807503518003415580c510741e20398031200111044ea801d0700c0c07580010b030084401840120000c01d15071030f1600544c0ba8082c0c120222820600c040c1048000c41e02088501000c42d007040c2c085009580790580d80074121840b40e1801c200e03100e10f6036250341480d01e2070000d20030914042c0c440054128640b020081c0389601803440c0b08400c803401010483c20309070f41030b104900b07039114403080700401000500b50300610b400ca00700410001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 883999055 1250 883997805 883997833
    0xf0a0b0d081b01110a05030402030c090408070303050a021b0c0a0f0b0a140405270105042d02121303080c090a031104110a1107090e190f020306190c08061f02 69
    0x14005c900090005807005c4200b00a40c030b820441d2600031082500e121030b69007007075200c000d05d5118100000c0d0071305440328045101380155904072000c107041c241c10000c1012801a015440d0810521114401e194514001c507000d00c011160308110b40d9040d0700c2c6c0340b42ca0709841c02a24034500300d402582c41200c0a100000709a103a6110f00c4040e00090041803060010b420121100f600c03047e004540a03c0c0380aa0091004020702d50a18464525050075503001c050018403d01034420f044404807840a40c0b414401020008009841c1c00f51080d2190307107243d0b0303501012400c1030060240d003981c0840942020030100f50030040c200b01c0c000c009400850345264000e10120716601c040d0081002401c40750131405815002c1c07007a1805084111801d00803442411201a0b440281009400e040c24101e0030740010031001c00304581c4c1269003e01034964501c0d00040a100c090090320213440c0c920305141e20814041d200b81c06492183c60014003501c1c0c041501825044010041d41001003548a0441400740d11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 884000305 1250 883999055 883999057
    0x306010512120f0405040c020705010806040f0e0d021f0e06060f03030d06141503090a02061c1a0909010902030a1401061a07050c0312070f030c0b0f0a0b0d081b0111 72
    0x1008083c0d5016074071803a0506210480d039a4082040c01c54005401c103000581e400319aa98100c40c00701c8021030a920801f400c500100301005094445101c0c2c502c41540198010660140c840e820461405519903c00b40d907000b5180c0d49013826039203420000000300c4510b0007103069030111038090110790420310381007103401c03c5440e15040038072413920a01d2100303058500784000300313001c0c404000300e28110304151115a5482c85039000c028450900850495003026024203c0c0044159526040c4515110603010428a4161008040c0115119000584448814042c5880017a40500204403c14003a2a0f50614403d40e082c9400b065403103031400a404111280b854901c030b0003550100c0da80d0f8045241040c81d00000c407414600a80040d45000c8250465000b52002c494020350542000c4406180464000b01c0448004180c07007821402d0015491104050701d1280400c2c10041102c506180300f00140d4801c0c2c894001d240358410810f903040d04043c0c040004511034484008903110b01e01241c80300711 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 884001555 1250 884000305 884000317
    0xa062303150d0c051c05100f090803070509180606071410110c070f080604110607060212090c09060d060b0f0619120510171509030a020c060306030601051212 69
    0x1000c02241e002c1c8440d00d0601440f01c1040c2e201031050802040d1641c0306c170f4650780c51040101d02c0507680c4102400a1059422140c280ca50200752140e991a04610103025a081141018001e00340b800307400c13000c0c000740e412160081600034416801c203800c03a9204014444022112400c500840b080070015600502800000c40c0341c01c41000c1d210110703000040d2406d02c1075130200e00b403c85882c408000408000c40c101c3c1e040754002c610200702c140c288001c80d0482c03040143c01810288001603070040c40c2620080c10b8041e2044406a03080e00c03291404210001c0000d96032203600404802069000076865032040c0e4103043d0103801c0301560080b40001440a0b00b000e40002151031010303481c0083c00d6842909101c2c03c51700110200880d040082c413400088802e4080c1e840721109900341c9245030101000343c04a800b8210112108510b44411203030f407283c000d292640d0140c03044844807845840d010060302d1240313134064002e01041c0c2c80d1804005214001c000100101d01a0385c07510541d0351040b034024a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 884002805 1250 884001555 884001563
    0x60803071106090f0a182301061101020c070f090e0a080d09060609050903030f0115080408071b08030c0708010204030b0402190b0a030b270a050603100e0c0a062303150d 74
    0x500b890200c1e0300c00380c955114040268003010480d400901440047d180e0540c1c0d09864000c00c1071407a0600d1600a11a0b5006000b131441045000191100034000e81400d89014000c248901d04c03400324bd10340c0e04c01500c0300041c4802d0b4140100c042402d06a44a40f21081c014840460001c1c0d40f400070300c00b2608207036684201030300000f003008200f214400207030b80101101000c0d0303801c02051010060a0171000780c80207101e200f0009500091204450540751585850142010101da5883c18a0b075645d0141401701b400780192400042d8410042c404d84088075001807903400103682d00da0030046401c10185a01080d405c40c840003003203048450300600f100b00450307200040c0e80920001008580e0300c40c1030481000040007046403030100c000031007043d003010030f080001ca0f00781c8560002a0401c0b503081c0382c1107041e929043d40c0d075510600003e0301901d400415203400d20752a03202ea070120789806035018241d00c04245030200d1109128484021944991007181052101c0d08004c002990340d08440d100792 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 884004055 1250 884002805 884002829
    0x815040e030a0311030c0901030506041418060c04050303091002010612060605031605030c010c020114070819030902031b060706050108060f0a020a0f0c021302031801060803071106090f0a 82
    0x2c5919826100e404181003c4042d46070940c505600c0003a81d5103c1c5004040c1003589031008501c40e91100d80210714480c0c0c0041509820303103040b01c3c1010003802640a07000051148201050081d011f43c0116005d0b2034000d0301640c507101c2c031341b01400184100c580050301199610b050004116011804080c040e500c103050220b04240740c04201484c10312080354000300042800c0c81040305035800914581c041c40d0a0030002e0102c100c6d800161280d03140a212282d007003000050000422860800500d105c2e88008440f104c020034044048048668112009405520180384482046441c207021100100020000b501d450100e41c0e42c1c0098543c01e0780201d155074041c01c10300c42e9800e030001c0ca0507401020761004501381804400000c069600310a03004081c050075054481c25900d41502c2d42410f051160b00640d600e06004100030461402e00e5038403261035203080404501c9030800310480b4012034028401e0406030350741c0c00c200045540705034021940044450500c601d44c0e00c4640e40c4c2c070010180c01c0300311 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 884005305 1250 884004055 884004067
    0x80c030a0e01020c01050d2a020115080a03050702010507050c0a030305071101020d09090b060909040c030506091f020f0706060906091103040c0306180804030b1e07020c010815040e03 80
    0x60441188500d001d4155000040741346440d907131040540341e0078000d0b00008503091000d03010862030b106c2e40452400d402c07400902c1010540d80c0541005102c0382e0003124250b612a1b403500320076181c50900c130005000400801c2250050f62281001d0183c050081003621040d00b0014001a090311459100f01c2c00f04a02065441c103010800d000c000e004802030014082d210740d142401021003c260140c44c5403a95a400c0c2100c8036184c050949010b06c00161580d01113003058240f00a01d01403500c0221580e224070000215100340100300c51194007456600e40c22811207064040002c0d401420100d00111014070601010034002c0c000d00c0014401035000140450422650205580b000c1e07880e940072040400074031000030400e080007400c580e048030001a0640441c5924809546c4203030300070b0301c1464017040c0070040c8031101071320324020351840c41080d440d081132014540364080111890030250304451f0364040154010035005600001d82420745490f2001400003404a983d460849000d940c804141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 884006555 1250 884005305 884005307
    0x19080604060c0203130b0f070f110a0f0e13060e1e06090109080f09281508040f02010f050f040e0a0b06042904120303050603010b060918040c03080c030a 67
    0x610b1070b8106491000e940b80a005041100c80c080c4c1c1c510030341c2c41005c03001a491003074a20704016540295030100d10400090910300703060b0819054091001d100d541111000a845d80354a64220207c411005252266a89031000c40081e140c0c003540645a05844040740006442d050041040900032201441006102402c0b098a8050010114481c9a161641c080b011074400000d8420861a90030038550f0b803d8070002140c0007030800d419014005104c290100814802401800e00350750140c0e103040c0c00703903030a101d04072144036060740d010b070400c040200c0700c0c005948107030282c02d800038507420014506030302d01c007180ca102d9001d40d01c1302600c00d0303840e810300c50707421418000c0c1903040b101201e4250425042c101460280104500900700100640d10f0b81c001c1c00c00200300784c40041c0804043e54500c1d1085040c003502901044910380c0c400d500e40030510310b035840c2510613108041405030404114511300001303c0400322000d07009440040c1e280d0b400000081d0150010920018824040c5413110380c1400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 884007805 1250 884006555 884006561
    0xc030f0501060807080c060714010606091e050a031b0302090c07020120070608130609030f0e1206071d1c0c0e04030f120e0a0506100e0c181908060406 66
    0x40f6410603004954100000c45000800c0220200200e40881c3e41d1303403040c07030b14280c2c80319201024040d6509108000a030540c0001c060300c11a03c5418004582003d6001040f204200c1400b070107030b04c044003038000d002107551064900c010b0407598070440b1b081c5031a41c0000f203400c0011217498214a0340040c5407411968000104014903802c4010030003600c04400ca001d840b14518008c4d00c00b000b418000061107206036500138001c42d89c000c2e40030858080355090081480b90844031000c04034091040390505401c210413401007540c80e01c000390002c0d0300e0340d2030200c5405018510500c41c43c01e0500559203240d90b048031040c0d0b2048070740f04030382a030117440c42e110b00800320541c88031036210211010480400d400000d641d56014452501d055180c9018101e900248401d09a400041c4030f5000010304008002600324010f8071400c03010141140c1c0c0380d03a00f46400004640e041000d40f414407910841c41e1803120041401c3c10300803c0000ca1041a80c0d00ac01141401c0d070021920f0303031299007070105101280c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 884009055 1250 884007805 884007809
    0x702130b120a050c01050c1c051206030c01090306020f071e120c0f02092e08010e031c02030703020c0d020102030a0b060325200303060a09050615070f0c030f050106 72
    0x1c06410060019240d054071001c04030003190601c040000c81020080c01071101240170a541c009581c15074481c480c004140b9000003015403035060003900880c8151174000340300300b8004016980c0016442c155510f0b04081d400408241004090a010310000141e204200422030115084a204000b0301c600380750415003d0f0f40d41d4581401040a000008201e00c00100d500c80764060b10310000703a48900d00150540c080b00e1920303450074481d81c0a005031690b0707880414400c80e0b814100038004c1c01c0d1030980c581d45030b105031280c18070140100740c0000c0c11003e05802840d4002c0b0203060060400b10b0b03a0700582d0400041c0c00003000140d600108101d201c000c0b1344030b044032a04080d55007034254980000030700d01c222600e8400501c00f0b0b107038451011070b444c4100b030b071500300c04103110800c1301444503520425525002030f105c00d482a030500030046008049445118410000140f0040c415040c00400a40b10342c41141c0507103503c10445c2004000c0741030901980019403040014002036100b604255003100c400d0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 884010305 1250 884009055 884009089
    0x7051302130603091a07020c04051e07050301060c060f0b06161a19050a0e0d0f11010911210304030804090506180a0b030c0a0609060914060d09030201020702130b 71
    0x3003416540400c1014000c240d0170741d410a048107860f01c501d00c0603450040580c600c07503801400d0a04100f072440941c4079031000e61514001e0302d403594841c603400b5505800b0900442c4001510003089802280da5a080300d8180102544009004480720700840c0c541c0d40a0030120080d4215550ba03902080030721040310310360480210140c000f5003443e450341d030441036910101d2a55941c823403000c9040340256500c13452030b030b112100481d80c8500d80c001c400340c140000141e207100880d030010503041c0031507418014401d10690114461800c0c010220802c042000c001c6141e00240c91300d0107400a03550340820041c13018601408946807a246080340030025150018001d502901121282680c0000460340440d00b214507014040395101203034020030f19100c03510200d141c1c071466000d80021095001943c0703409480d444d07640c03c0985a1100c40f9510703a0741058403a660081410010301c41c00004643c003002200c0e11034800507103401c41540015482d1401c001a2034505503889030020400e00e07101c41e4806101c400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 884011555 1250 884010305 884010311
    0x1150f050a0302132306030d05190f050d0905010f0f0e0c130b0915012606131d010b1e01021203091e030910030e19030207051302130603 60
    0xe050104401807054403000340200b003150860b041010103034004c3c00c0302003140c8160398000340b040761200b4500b050a481c0c43e8028010443c10320410351241040394940d183c00200c03030542051000084400000c820808002c000061103001030100c481e00581411034080c10000c902d42c1e02041e00801190f6081124441c520710305840980300c902c002c150141180340407910701c0c4104503c1c1c2ca41401502c20850801da1040d07030803007045240c080c504804c03500e200e400c2e03a42d1000c2d8401034046451700040d01800c0401500100b0024009150070a07010005800400c00407c80d0006204901e4946000c1c1e0340400c0f43d40d455011072881810a1480e04e5481407902d0540c201480d142c20000c2d4607580b440c0c00c0180c1d00c840010006000c202c080040e809034810b64002c0703d08401030080d03a251660440100c0a02c1414101d810301e001074442e014104041a00744098590211100c01066006c03480318001c905600640c080042c0c5952601d80c404014204480c01507035030f0440c21418803c0a2131504140e0500d89 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 884012805 1250 884011555 884011559
    0x207080111030103051c0509131a180a02070f0606091a01080c04180b06160c050303090901050108090a122601060504030f0c1a0405041415040917040801150f 69
    0x900018400711500701d140c0000d1185c1e51b0700008075a40c2c402c0b249120780010740c1048501200c040b036441460b040b00741591481c8550045000c002c04c0e10700d056448007605450781d01140c00111164018007a00344503400d9010000f070290f6661081c0c070310175030000b45200c1d95040f0120701013103070716000c8208080c01d19000030140b0300641606081d0149000b400c050216515882c1e620000396805100300120003003105e911010899149050800c100000319019003051400061034100001901c2141304000c00c4141c56a0902c40115524600145840c01d20310421100c10007040001480d0f1107058010366550790490700d40120500003008001c624440340b100c0000421445034440300341d078282c81e88120440c8025405003451240c81800d40c00800e004a01d00e250072034444407050041040342c0007920107008500f000905000e682d1000c82e07001e60b07503020400c20305a41e49095808800914407500ea42c2004421130401c0305140d0f00f054004040b00c4e0364171026000480c0c80c640c503810007400103020079004e40e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 884014055 1250 884012805 884012813
    0xa170a05040b1f2c0a0222030305031603150b09010f050903070302280e0402040b0d0506011806031406061206090a0326090c241b07030209070207080111030103 70
    0x89030500c90f85a0700580c2c0480d14045500380300866211340c1c0c42408045540c1408407812000b03500201030200310000c01c0300c1110400c0044001d100880341c0544940e03046a5540005190b207030581442d41c002c1507030300c00140d00750300da2010024015043d05503174135407585c1740e010000d071216580d442094103201e0140541c5002d5030b8002150415a0340c1034401c103420484004000102041000d0424101e61600c5400b08142e00c103808420f2045000f00d40c107121412040c41844003840000b031018129421880041c0300300541380d403080c0710816055100140c282c1c2d880c2c44401c0314000c00c290320045a04040c0038010300e85054179005070901c00110103002c2e41d04007108107681d40d04011000600b80034103001c0c8104501003a5038449414507030700050300102e10703155004a1706c0b0402000081e1051441d290144000b0040390708624404100c8022a403a0056141c04c525032140005012600c9108a403c00300c01a00c40c1d61805000d4241074004200da036080100050a40b402c10404500900050004001003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 884015305 1250 884014055 884014111
    0x40b04450609030c14010903080f15040b03100e03071a2a04090903020d0f05030c1602131410150f0e010201060812070c050301050c0f0a170a05040b 65
    0x110392004002540b190301d4a419078440003401000340192050b08030045800c0e0064000d800400e2081c0d8030110302d561910b80a420744141618947c42c1c050034204052060b0825500000c0000070080032500e000704803e00d2141500e840030f000301c2c05a040418044104a004150f140c43d1101e12110b0030381610340b181001350403051700a0316104041c6034151070151040e01c54100e0f005482840381c14805c5120509000c2d544400d0307045604002000c081c0500e84c3d4074401c0e01600d015070114622140f1349800c030100c84985281480c01680d01c054a4042d00c07621203180d00c81e003405a080c10301c22a40d2441c0a200740070752040301e60300c003560141504180140440d071214014031451528100401c105000000403801402c503034010441034420b14600c154051032130000b51080300e100e4641c0702c5ea490740300c40515023a0f41c0161403103400d96106000c43ca40e0750f483c2d42c02a00c0543d107a450541003003807000c0c00c03440704000282d81d280c90541d6100c06000a2080d40e640070341d8020400290020520080304461300c5e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 884016555 1250 884015305 884015441
    0x5070807080903070f03030e0a03120c05010e0303090a150e070e0411030a0503222402280b01060804021302030702121909080d0903060506040b04 64
    0x10584001a8003000c0150300da0940d0080d500150480713403019110140e150880b04c090000b039000c14210070b5a81a10303d042403d0360146d9030300003102e0058071040102034aa564403404211015501c480400d0192502003001d14842d540b030324002c09900d80c0e18100000c1440130220351501c0581405066038490b100085c4110440b4124165a5090342d9142090144202e42c4180302d9810300840005405001000014003070041d8082210054461041896089192540301788089034a01385910034442070420842901816180107440800601e07000c1004199400c03000c002d142d9400d5040003007400441c06250340940441d0410007010300f000d0300040c02205021624001c00344e000800a18044c1c800e00c00d100941c0401c01d4503d84800c0c0366060718040c10610350a040005081850001d23407421300180a4008039590340300d00c0c60780340c15a20307044007428005200036007241c0c50313510b4032041d42c48a101e591040d41b010345407403090441800108101c01c1e0484200c02d0300b13050b61010807d0b1000e1400501c1c070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 884017805 1250 884016555 884016563
    0x30f0711011b2607080c0c19080a0206131e0e1008030712140d050603010c020d051c06030206040e0714030903041e0902040e15041b08070905040e07180209010507 71
    0x7542c0f49042c4800743c0c074810b205000f0102140400c0c091140040020b200c00883c1c0100c0b07583c040c0540c3d0100703c1581310354500c074502c5240d002200800c05420054004e0104071000c0018030b00d115110540d421700301100d000e01000300e2503007210030841c910400e000c40d41c000700410101e085c041d11b003555407030f40e901800001900005d00140c150a9041c01040040c0650041d020710a07100ea031014503141c01040c044030242c0c0039500b0001b1800c5a10f00c04260003d50b00d002d42ca481c0c0c149412107801c0b4030951040c0c4060100c3c0340c1e80305804000b5a413200c1c0540700820b058a003a10491030051402429001800078036031a40f070041c424441d801c4004402d48007942d0200400d0140c2e4001444034002c10007040d805611001e10000b00807940e0441461a82d100d03511110402414908000a20041b10000c001840c0030003a00301612140e10700c0b07000ca09401407198503012003d03e41354800a01201c81d20f02809140b83d104900402c1400444100103036240107000c011030800814000180062048100083c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 884019055 1250 884017805 884017853
    0xe01050c0106081e0f0a0c030305070807020a03150f0504080d090501060b0c0f07080a0c0b1b1b0418021018030f0309180e10020309030f0711011b 64
    0x50340c1980250701410090248400300c8102c614502100c000007900042120303ea07019030786a0840306a800588030060716070280c5041030305031035070b00c044030f8a070025101140c0d071403020400c134030169654910a0014501403806500f01c03c0800441d141146c00c06d0544888090070402000080b07050070055482d0b5400907400818103038024074120b401028260130481c1a030f5408189002e502800040d600c541c000800c04490000e41c0740c4400f566200d46000b00182480c7c0500010f0129203001c0c0042c286a82d418400700b60b800c0d81034007504d03007084d040f0090120080a00190b01c41d503890240a05184860503403c1751090b4440c03500415802c0e00d4001c520410700032400000c0f01f20760645801034000756008071700c2030b030400300d1840e005000440a10461010450031001440c540e40d8900c80e00c43d46e014142d004182080c80c2c1e41c07840f0040c0d04002c00340000e81c0424040361002d000d4142c018002a84609035030b106001410001521072446000d161034015000c000c3c0c1c4c00000e0843c00c2c01511414021505 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 884020305 1250 884019055 884019067
    0x90f06060906070204051303090e1605390706030905030706180b0c0406030606030608190c050d0501020d110307020d08060604150807030b0f010504030b0408090301050f04060f09030e0105 82
    0xb00703100344280400250028a4002000309101c000b050701c0741428400c1d604c41c40038940d9440b20341d9040c0c40544030b4162004403a80318820541c0504000c080b0a00c402595915080d0a50700300300c104500314080c48414083c42c08000f030800d0080c0304000c00780000341000c0002d450b031510303000d0340e0b801482c800801c1ca030781d154800408444944424440e1a0740f090320800249000340d1059402c3e0480d21400b4046400d00c840810110300a0203101c007a18a034a000300400f030002c1c07442107041951114143e4001c8101030700800c040d29441e5000c10000e0040b0009030742c80c02100301410490302c0c075001c000030380300042c020302c41c1041d800300349038844c440ba030310b8095480d48400b000100c00e845943e100581d034600d0783d85008102038100c0c00207031082c0c05648080010a502e0801e000046141e0b520040c00100c1c100002d10016403120003081d00b0601031003650b0704082d01580420b0840e0425200307004d41c0340124080104000e402d0059482d0040300c20317001e000034603655174050400b0100c11080d82c1808404204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 884021555 1250 884020305 884020309
    0xf0901180e071e0207051305041103031803060f0705030f1b032d090322080304060804050709021c0c170403080106141e07050a050307080301090605090f060609 70
    0xa0040030300800d00c4803075924144044050320740050f4502c050403011100500c442140d001041c00b000b00d8030702501c07e8150700b00c00c04210340107140080c0102d658000c58004800c90303031000c0014004110718200c0d03400c1d242100c1000c051501d040100040d409140c440c04000c0074950201c00d1320340200401c2444401c54031000b800c802c0c1c02c4c6a1140080001b00d000c0f08200342511502c0c01d01142519000340005030001060313410502c5101107071200d520782d00400030b460001c40c4c661404040c0480503116401001c2d10740040c0b90840e8080d6110100042c1d024040c4024484188107520041c024400304500c1d000920304010030319075607050091682561184130450a50003800e006003e680ba0759020001880c281c034028040304c9080c01b40000103100740180061004645048555100075581c030554070180b42002404154484030b41290a03005103008880025020009025624400c040582d10303503040030341c0c0008855003540700600ca14402d00600107503441c050445900000f007a95050b81c1d6801100c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 884022805 1250 884021555 884021597
    0x901050705150a0c020c010c020609181008060705070c0e040f020d050d08150a0909020a031a010806100e040b06060c0a0f0b13120e2e0f050f0901 64
    0x40603205000700040444180000464644260f036200b0f8100a00003a49104998540311000703840e01003154044240090324100c0080c0940400040c5031038241407100c1c100c0d20485030151560445007102003c1400360300c0f0103020403580100c2c03d1610604042041c0c80d01d862004441c815004800c01e600082418400c6003112031003c650080c180165016080c03500c80c0d45c0e864124007940000d050040403c501c45001404050345100040c148051181441c030081c0080c0020b18080b603000c1c03c02e43d40000001c0c100010744401d195034a400c1c44107580b5020005042040040466921040070719080c400e540f50b00c107076950081d4003d80c01c0c00702c650300e801c0400c5991181c0c540c200717610710030082d0b040100852000c002508611480100515842d220b040c0e40c215240f501c00186803030400507224030424490414072804841c000d1542d00010400380c505c8528602020f003820001e8500c860070700c5c03001d802441018013004189001c031710b0304484990300082801034050160402542d030392801c401c0e5030066 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 884024055 1250 884022805 884022817
    0x4141f020304380610050f030a02040e1e22060e0c1207090b090411010f02100212090c01110616020304050316050123161b0806060132090105 62
    0x40d5209061500356510401900c2c44030f280308551000fa0000b25071342020b8160081c2103505482c1c0c2820180309441c40000c6400052010103440d509020000d00c103221124918002c0720b1566000200c03040a24030824a003400a010640c00d80c243c1402091200100900c46004c0d9007114000416000307003420182012284480301c0d0380304031014070320005031501003010030031030b04500130400c2401409810f10018083c100e6029180500030310031003440354060307140c001201c0034070b1055540420a003014032080340c120316000d00c0c9082c6518100242800e0410150360000c0003401c0c011600194500310b596900801800d99003040546d0310502d08280c001c100742c41c080d10004094170004071600d0380c8a4a04103e92040e00d00050803010003507400c6241c000800d801d03c40e0042e20074580001540242e107060300c110000c40d104841c0c500e841c00c0c4000040d200c00080c040742c80280100c0e0030280d0006103c200000164021213240ca51500744642c041c40c2e000c50b807500c02039841e0361900013440050303076a40664 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 884025305 1250 884024055 884024093
    0xc0304051c05030702010605040b030a0605070219060b0906010215071805040203091b1f03050705040306230702030a1b0201020a1203020717040b070624030b04141f020304 75
    0xc0c000d8540a40140145200304030071742c000c102550369501008161040c603040140c15030484900c08003c2211a0032165202d59540100c07481d4084a02900540d0740d58a0000c0d94402d40d00c600681692034135410960700013200f4070042c01110501d680d9602e0b80e8102801080c00d03c140d030700311905a501c1031201e01c8000c0c44000d1046441e480d007002c00319240c103c21043d000c00034554a00000700ca1500d802d00361810034048880d40c2542030746840a60040c41d0240c1074001f4031001f4840007001405a01451040101c441e4090712049207103c4e9560342202c01402a50541d0018010383ca041588914001e0b5011800c038141741c80752059000613400c058001d540501030001880a01407410703015001440b00c00e01c1001c008402c0c1d139640b00907142c140260f020303103400200100700d01c8022851907080031361b0071104240100a564181400c1c10803560503580222031080608041100b4011043c80b070000110803100602004002d40400066125104910803110399010001c14140482c040000c2818481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 884026555 1250 884025305 884025343
    0x108010b04063213080d021204090f090215070201030501052211090603071106131a0603011506020114011d040210353418030c080d080f0c030405 64
    0x3800410134004000d4043d4902e14030809242c2c03078110303100044013031540ca58140a11304140c1002021409883d16400e200c9280780ca500811001da070718590010141c01502c00d801c0c1d5a54540d10016007aa50b050f0700952251003124800d05e00d122048070480d8404041c10070000e54000400d0441445004080117a500850040304011944d40c002e1041c450459400c01242c0310345d40d40006944072078100b044010304840d51840801010404030720402c0d0003a00050010a0a450442c21001900420360188006070344801d03181a483e40d03a1a081c5003d415850710300c0e0514581603864080c0c0504c0130748000d0044035107224208440d885050802c0301802c040c20380d42c0d850034100e03411009800042400c90784104403480882d00d409012131001882002c1640c074607034183c41d01001c0c005031a0010f50503205210442d1a8102ca084e84032440e00f0145208032587c001481c1403040d024a0b1421184215061100749070900c540d044d50101032542c4081030050032a1b4a0344d40703140850418503c00d506d0120041c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 884027805 1250 884026555 884026567
    0x6160201030f0516110115050913050d0f0e030c0d08090613030c150c03140c070905090706090e01060206040f02060903010e010c23040302270c04050108010b040632 72
    0x800d409095136007000740d8803101e250500c0410036003202d0031907460b14411140e048003004075003800b280311355010b415007040c101c5051341600c8140c04d184510704408001403024144101c101c0d00482c0b05844500180e0003000c3d05040340011072034000405030090191800814126a156501c1e0100c44c00c3c80e003020652a092941ca103071040c901034142c060403215108100741e0501c03ca118801c002c0744190140d450160341000100100b607160300c40d882c90350a80c01044c0020804a0860040901900b0740c2070051400c180341110080000340301c0c0c1c0120a0b11414003004004060740028030365086500310034040d4250704540300040e858032458044940650804000c01c100c000c040d407061009034010749518010989410680070742000780c0c001d100c03020600b48018000750034019103042d80010750720a11080c5050f115000e4821800071110070748840720005081c0301701c0d43e0050310140148100703e94141000c0c20040b000e01075004460360b01c80c0e450305515003084c50525405d1800700c0e0b5180b00710016a901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 884029055 1250 884027805 884027821
    0x1806070f031d1509011409060408150a091218150f1713030324080604050115050d03050c0a06061707080309060a181d07030f050606160201030f05 64
    0x9070074080c05103410b0540c4074403200142004103e84191000007010f20307180500d03200c015503081c402030003400d082c00400e11500f40c0d1503c4010050014098520041151041e07100120304030201c01002c5001048c107020f200300004a800ca03e00403a2542801d00350100300c401400904034036800d034809040001f007440021a0742d074011702050f459402c540c1d070301c070f00c042c100c012080b00100d4192140c00030010200841400300b4442e40c0040240480c1c100709482c0e40040c5520601d021300a0740100c9050b4100200303000c2081000d1055915288210304426212403520000600c0c03036050100150038000c000440c000244810b000c80c074038003588081d041050980364000c2418040c4841c01d1841030784100d10000c81e400c80f00000381c8105401c0241918901211524200c0d010548620b01500011010b0310214a41c2c804a80d41d1b000c0c0c0745810a40300701490310f00f10003026a2034440c6078408207483c1105100a54450408607035800c0900030709080c408001c0e2004030b0051100c0040c4003d60761410301480400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 884030305 1250 884029055 884029067
    0x1050103030e010206071e05070206070c030614150f210607090f060201020c030403170f040e070e010806010903120215130218010f09051015090608010f0b1806070f03 73
    0x2c04001e038210b4081e961611800d0340c00100d558404503204800308008020075120b240280890ba10183c90b0b94104a990758a48000161075081140d0503504e230180614600100c0c0c0a241c0d10040303191803082080050300c0860b006107429070019006d5a02c524001c0c0c0403204054083c034880580034111801d0b490b110350010035410542c0101544080f0b05000041d02c18414000d481144400f60050b610381440c5940c1d010000112694800c40110203010a0080c0142a000b82c0300911703c1c048008128a00000002d040380344030b01889042c01803590500c02640da00c9000300054a9216011199500183c02e080c0d242959140c10791402509410401098101305400c00502e184203a800f0545242110008600443d09005000c8440c4245008000c2020300d80c100c190410802c0300b1000e800b9445840c844000c44000e031a00010400024040010a5000c01030341d0040c00c0e50992180c80301d08100c1000021302c10094081031150f5602c1d1b88501c10764a003022108003940c00512030350307400654075029000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 884031555 1250 884030305 884030327
    0x50411041d06122b05070302060604050402120610030204142707050d03021f0204050105180105160803060909030c0c06130503031b011401181802130b040501090213170309030105010303 81
    0x400013000c03c2a01c0240c0c010001c0d00c40032541070300548501c1e90b44800780720080034010000d90380301c04d000c6180866018280f05040c0241a034000c0d03103c040d811401400191610500c1c03100c50203006908021802e030003140700c8040805034030040d0301c2451034100000c0c5041c07419081140d001550012035000c043c0c00103500000f01c1072102c02e002041b1403881e05081240214891300b40455000c2081d0760091000c0041e403681030205040c4a4140380e40102e0b80c40a0b4140804219142003001051000f10318080503541e0740150144011480c140f0b07071490581e11039072030842880c06824046007144150300074140203005084080c0860f516404880c22005c00e410f000d5500300c4242d440c0c60090000b040b010a241816620781a008180c3d180c01c008102c40240380c401c680140c0070490300802001a07484c1401c441d00d03018000c00208401e20740c0f0042008548040e44001c182d244108450340c1e00c000d8029204044078200342d210041d132002c0843e05402c40c41004001ca61652a000021040540101130014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 884032805 1250 884031555 884031613
    0x10e011d03030714030c0d051819081e040e0702151005010806011202130b0a11010605210a06050a09200102070b09010306030804030b01050411041d0612 67
    0x10446101900c0203440384816504080040d0340805046040f0380c10308010740d04213001c03202c10b03440c0c01c801c008003504071002610f2106280c6081800c0403ca20020005030351596020901061464400e0740e4901c114441c54030b042110301410303903400d008480302d03905507401042c50030b000c140c280c0b8010100035210307500030245002600d02c1c08046605400c070a540d1506503041a140c2c00040c9c1c466400544003018010300c01604240c08002071107200c945d0411140040108129040d00c0c0d0040c0400a81310b85408401060380c1da14290b401c208641e03a903250005e003001c4030800710002010307020100c0c1c01c041d036660300902100e050100740018840306500c0030708001d006010307807403001c03071201900e02c141c4195181c1c80d80140d002a60a0256001310b800401c01800d0504000070a00d6407940c071554560850b5000340d4540b40e900004020a0500c1d000703c03003003914040c000e03d02d040d05100b0068902c00301006200d0120040c400003034002c2e203610800443d403040e42e40c115044a1031410006108030802c05500c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 884034055 1250 884032805 884032841
    0x30f010f1401050711100f020f010b09040f051507080f06010503060d1b18090c08030403050706050901050d0e0f2a0d0f0212030a09240c020a0305010e01 67
    0x910200e144041105541c141403888640300511070044903141c02c0110f09540d10742d6450070740d08150791440c94540c08000c050b12245040d082001e03001c0d0400c88014000c0c00240d041100c0900d503507450100c015401980807070135007404e10040c20400d141214003420313801010ba40406000c0901e4000410301e1042c5403403201621190f440600440300d40c081510856004480f00001d84002144141b48804c0c1502540041d107025035a900400e0341d081d003241d444a0003d60b501095010b004007e102080079000c444000c47c0b03414a1a61182e9840e01a40301e004200300012a90290581c0704000f02d440507001c10780c05111241002122607200c448100124903244203c001c07010008940b1269101352003580100f80305502600e509112280c0400c00c1700302d030b040412094810041c2d03615003500007210044001507403200000303e0081c040001c25004500701f4800f154094000d6480b4a080c000a5605450000f113400000d1003c90030310010364100814650074901898100601588a007400f658810201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 884035305 1250 884034055 884034059
    0x90c0b0415090f06080402030a0605070c03030b0306070e2806030b13050c0423040203070c02150403050d0516051b1302071203110712020a030e18010512030f0c03030f01 74
    0x3950345a260348a40c4464100100013042510b004024045c1d1090020302603030303080020703540e40b072048072f0040702d006000c10b1102504409044c0e2611801a0a402c03d80c010141c50908032000b40c80d80c901c03220340501c202c810f0303a10030200e8400030440c0d048000e42140500801e81d11010094042c0000d521030381e018201c1d0700384400c500c034580c0c01818041d468070208985400d09109881c0c10a4002030402c03e44500e40348105102e5413194401588a81d80550b607000103404548108541c902510808603c403640a0200b0300203d000850401c2c04000c80e800c10668808075406031640007031078598042d00340d000300310701c0c0002c00510030010012210125800d0710b41c2c08100404a02303e02645070054016011010800480340c060791040e201d50802e07585490901105a48540b0f00d540ca040b18000160441d02201082542240900350071040c12118101b451460070207007151050140308003846090b14680707079002482e00303008039482c600500c2c0c00d46580f4407007007190660720b5105441500c6000806000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 884036555 1250 884035305 884035307
    0x70f030209091915050c2a030705030d0f0c0507030503060d0f02030a2a12020d2619050a0c0b100f0e0f090a02030a060c0311040603140a0b030705090406090c0b0415 72
    0x11640c081c51f040c2c8504e40c040c543e40410340242004030303120035403c6c8400c01c1b816000c51001c2015200d508254034010654954400a03807054503000783d10b00040c46018050140000d41040c25240c0c0414151260f0740c2c1490503040c030071030351092158040c1d00740c060b403030032a0240074048003001c4c601d10302c1828044107904150304e1034410b160701307210b015281c00c401440c2100500d0000c518541150094480c09006d28807489401c40c80030181e440c20310bd813500010110b032211550512a401e0b40c2072410b01a0821000180103403603001c0240004265501580025020070000202c03400074200030807002c25400c0e151a22582018420f40c2c000c0d41150070240003e00d4220000f0380307801a1359000d03020300b103140002d5403860003805c1c80324610014541c4034111003121942440140005200558020a00700342c410540d5103007440c060002100c450802c1040802d41e240000d4a40c01c480302075901600a0780c450038900000c00601c6401400021135501c001010540d250240055543c081d132008a000d4050300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 884037805 1250 884036555 884036557
    0x7032003130b0603120a0804140105070f080f190507140f071a01120b09251d06030606060702041b08040b010609080c1e0904060f0e070f030209091915050c 68
    0x43c8001c0e00041008004602d0780f10b100c440c0c0c1c0080c442c26540c815880700e4278003603003920412252580091109441044901c0d804483e0641151080c03400020071305180c8864054504401403041d24142c440c40802d01851051000030610f006032603071a900c1e4081c268040f0f55640c009041514210131200030080350300c802c0d6804504071092954541c030032401c19a2550072000340244020b505008907041c2c80800d02000e818030715030420000b000091107080c81a0100c0006500c3e1644001801d000104841900c00242007a0051800c0303c1103602e072442d41c0b0018003d0649011640f088181240741d01000a40107070515014030f2098945010517a06d07181c0c100c4540c401c42c4512845035100803074070446810092103583d41182d489910182100103107000c00e41d60002590100c464968a101201e540c100910444203407881d4400500b980e20f24050301c0030410700171307400041c0c403075032001001c07541c00d01d801c011b0901b40b03101c107400c00e20901400d0f040a0b2120b1a86800105030365080c28001101604400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 884039055 1250 884037805 884037823
    0xf16060f0f060e131a0a0501060f0503100b03061302070f05061303230919090b100203091e090103080a020105131a04082110060507030807032003130b0603 68
    0xf400e61126580c0d104a400030106000d400b9109002c910a000c446448a016860321a0007416004181545050380c01851205486900c000b0003100b03200303201032088c00c2e41100046507220304c0101d4480e16003038000784a2289402d01c4030b584910024480c03040080b040c0b27080b14040c0c041c1003907071030a9a0340d0ba8081c2e04418106030080008110403d818410591010b100b214041000c6415003071088070b60224400c1000714840810103408a181080300d1041c6008440345ca100c03d8803041d840d40725051001c1e60b28041c4440c0c15100f00c403c0c1d4034840410b0448400b03024540f00007001c1d83c07c2540e5904003140c10ba0b111340301c660015402d080c00201040102512000c44940c030200d4036400f0010150008200d22010b0700885103210108031140b08a000302007500c0030a04c03601281c4c0128107000407800d05501d5958403080c00d2240500003000800e42141c0ba00307501041d24200420780c00c0203903040104020044a2526605001005000f00c1c540b00341061920b2901c00c101031485600c6000c105076a0780044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 884040305 1250 884039055 884039069
    0x70816060f080a2c010518070605070312091b08010f020f0a080403121a030606030607050913060f090501180b0a06050f0d090305091011030a03020f16060f0f06 70
    0x103000401c0c0e1103c03c90744181c240702d0b0304000c1926103256982040d000303584000100c10b00703a0746a5050050102c0744a42c45404a000039005080303940c0b41150180c13142c001c6c141c01900307024424002c008111801d030881c1201e030b03600641446951236040c501320003001c0c203401180260341c80e00001c0301c1c5c03201035031003181c40e00c40b000d0032003500b441e0304080308488611000307004504010a00091201441300c0f80500c1c50803c0b01070f224003003903a45510500d49001c000610305440b990249045c030103c2030304601103842102042c1c0e107550740517000f8a02c55001e8070140d030200d02201c282001c00541802036500042c1a9030301e0100c90040d040c1038028070b0003507030240d034000e50384031180e08001c00c05107014000030031040180e1086a030900030030614041c1140c0c0c00072015408603100141c41d0045280040b4001d41c1130b145030401c080c2c8040c9a4858542c1d034050540248241540007615001e10304e81001a035903000b088046e40851188140707400c0020703140c1c0541985150342800c4412042c0601070280505440007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 884041555 1250 884040305 884040317
    0x1a011205100c0e0a0807170109020907080c0c030d02030a0c0e03060c1c11070203120309070612140921160615030b04031d01080c09040e030c070816060f 67
    0x3031000714801481000c0810302801401032520540b034940902142c0248507100280070301501e030400c4940040c1403032060400d04d92500c840640140e485803405074020b40140b6008846a032011900c0c10144030b4040b101701a03204c003041e2448a0003580e002903115001c419414030528244000c10b03540f4840101200f58140c00000020f50710000c480b02a081041c07100704000e0748060640322007021070b50005803c87c10b0010008200742541420400d0595844114140c1031031860b0000700cac03940f030758004d0003800d04200c03c42c1d003103020401031034206c803035050103440d034198260400c0c1d09035036550030351180003112000c492504008151008015204078072041108094582c2040d5148401851181a2100b1041e0401c20210220345407030801c40c416071080e192881d13031041000d100003070903030050209030401002900b0400d021894405507840f1410541700400c416030817112035820f40c058041964454402d01000290303c3d00c000800d8541d01d0012104400800d85908048a0308504460740c6408210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 884042805 1250 884041555 884041573
    0x5011d1014040506040e0f010f0b0f03040807140f0706030c0f05090307030609030c06060807050d02090a0e0105150111010c080117010906020f071101110c010e120a1a011205 76
    0x2008051054841107546102072a280e141c900150294100d030b00181c40c00140c2208200140c10003003220ba014000c81c980560b409864091191028400c003001c0000d0408048041403c01880ea021340c2e01c506c3c1e0200c644807800079182443c40d546c509130224200203200e00f0b000026880d0107840b8801c40d00790745d9a117640c2c80320481c110a4aa60740074855807178152003805000004a0114460b0362120340c4a95a0402141c40c903040038170507030754141c110181716007199204000581d160200c0046296050b68420200c3d590f1024030300040c64034241a050039400c1c001009104100c01401402509098891811103061110154202d80706400141c02042c0c0d200014025141c4003020105080300c448008102e40c0119a102c0782a80c021020342c05407000007244281c104100f209041e6240300080c80c00c60942c40c61141590703503a480400049041c402d407410f4032005915100ea102c01884a160100e682c800c125103002c50f40d40d003852405007551451100040780d01d00010194000d1140c2007001008200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 884044055 1250 884042805 884042807
    0x6030f12030f0c0f0c1a070206010509010b0405030a060506120d09051e0d08070f060c1805090f04031803021c11010c05030a081909050106080f01060e04060c02010e0a0b0105011d10 79
    0x1407100c80060310002044c6141c06006d070301c0e555921784507082076400341c5080d5140c001880580710060b0003c1a05034800e11090000f17450002c0c2000c40140c01c41c2010580340c03252804240d103941c0010ba41c0d00c1b1409000c82d21401c407900800381500319078041e41c0c101550ba221040d403a0485501c001410341c0079010b5480300011906580203006124086c40c0b10386a90541540e031007045034803d440c01c80108805095444003016070b20b020750020a001d0366070004510302540021070074140100000c0c02c2c030030402d00b0703050490001050303d0091179000e4106410070b101b5102c1c5a0f031000c648841150080c41403004000da9502c80c0e0302c1c4082c4642c2c040c0c01903082c0100d109041c1d83c115001883c15071410340b00d086011408555000380500d040c043c07400081d40e2030034195600d080c0300c1c581d4069200d03603041001c108459400c1c0103c255102d41c11040000303611f81500340490250070b900003000f486200303620291090000008020741240c00980301c0b10720702290f880c644400d40302c21180d52a480107803540113507889 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 884045305 1250 884044055 884044067
    0xd18030807020706050708030f07051b0c01081006082a0f130519030b090a12080414210d020408240a051e0604110a12051f03140106030f12030f0c0f 65
    0x3115083c241141013100c44025445100c42d1803114410360b9200b000078841cdc558224050340d070480300021095080500b00800944503140103031400380300302550312280026040019608426001452031a44e0395a00c2032501c11345a000740214001d06180c12800080c60300d400b410316910325007802140445a4550303100c2c1c900c444801454508580150300d800c10000b00c0140d0804051216501d4400d054201410506409910040501d010394800550300c1405031000126203039a00c101e81d07485544140c01030134803010340155400441644910341d035604096440c681613007d00751010303075020101da0322001e10702e0035650142d919a45003120a20707000c10b04110311045551108008d00003240c4104000442d101c41c3d405a0b41c40000100d02120119000600e8000d041c0c008907001d00c000d0710710b210340305482800105880010201c0c480e0504180c501c032001e4000000440d00000c890700c949045050042108180c54105000280342003140c400d801501d00c51103141008555404020b4020f001050f11031b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 884046555 1250 884045305 884045311
    0x6040f06090f0806041b0f09020301060210200f040e0f091b180a2306030d031517070902070609020f06030f0a0f0b060f190c05120d18030807020706050708030f 70
    0x3800d0034000d80881c0038052801c041f0010700c0420801a41c0e903242500c02414001008010a65203040011a0300741441c001c48605403004849040c0742e4803103075030f007421080e403142d5402801e0800e024020080d003c001c0d080d442e4424400f500940340d00c032200b001080e80d62440a00305550003da9911441240030140601c0b66020306451000284d0741d41c504088200c915005220702180c2c030540080041034101840082c1111809003818000c070701c0d065940908804c83c40c01910110076012590340c507040d41c108991801089092011540c1d4503035800d0a5025041e5010180c0c0194044c14010499040c448120391043c02002d4200001d0740b07034a2107120150907692042400c20b515102c5d2011155203007001070000703885030450560b8601d2002c080c1114400c2c1405050b0900415201c45008101c1c04100700e08894001a101d9660350001c0e680b400051169020118003885044000c3c2c1c101604090b1240c00361a00d902100e07501c1c0d9507607104903218880d45d10000d00c00d207003c2c0082050b4001034111550 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 884047805 1250 884046555 884046593
    0x50d0c120f03230604150b0403060b010320030601090e070c061109060412020909011b03050621010903020715020a1b090e030a031b2c06040f06090f080604 68
    0x1400840450054940c50b2103c440c500b454684505000c990300c4d2910402180752450034001c070241d882e0800c030794641e006501c80a041d858544410603540e0f84260300c1454074012455a2881088001c03c140c4000c2c0c104480305030104010003004a01900d40c5003882e4810801540c800600302d0065a444003e8010b40310003901c1d050040c0411401540c0d40000b5002600d40e41c01c1d400c41c44499401040304400024000d564240d140c0140007141c46240dd0030b0120194450170042400c0d290f03c0046121040c54032030300d0610050b4000d01480103030064006044445c040d90803111019142c1c0c4207264010304404040002d6805005d0001c00a4032101400c030000d00d814450a805070713075030318401d020380c1c1c00b0a5454045410016480c1c510a03054400ca509510070400c49500544032403c000d80042c564111003134650718580f070400d84c00200040c140714214409001c1d1600d1f1580d40c4034040351090580181c101048511001060441002e6122800c864082000f000242c9032500e600009139007908001c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 884049055 1250 884047805 884047811
    0x3190305160f1e0203071b03030e190b07062c2d0102040f03120c080d05040f05010c050c010b01080606030c0307050f13051008100303080a180b04050d0c120f03 70
    0x18180c80a81c010f0783c01c0c51154002d141e968641d0b240c2840342c44824030000000003600329040c00800c6d840f2821408800080d501940c404080d41c40324514850a80d01c402901e002c0000c144040090030340110502070f88004490020325100c0c1000c04007140c00498a1a05910061803881081c40c001041101603005805015460003045002c80c03e81c2c0c0290422690110034400c10401c00444a031102203684242c540144025499601e0070344c140b045104403c1902e0f01c4030702140a0104245841a140d0341c4807000708204000904040e00c1500800c20151580d442d24042d03d56950040b10001e2107080001c241c0c41c616510b009410a250304040c000e041089001e00c83d0000201c4800b008000c1c101d0b1800c21203241c1441d000400c0882d0200f82030400030400b500050003d401080384200d41030341e1b0301d0300701040c452f40c4031442403008140141c82e82da15680409507400c148030343c003411107009070f00400940341d85004d5010282c4983d10020b40040141d111001508400c500c5080c1c07640d00100c00c2d103004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 884050305 1250 884049055 884049077
    0xa03170a090209040807121b060b0105040b070b1906052d03030c070e18030d0b0102100921050c06071107050a03031706030f03161703010803190305160f 67
    0x1c1002928101e408490170031001600e201800708180144114100038a03064191204a03a4645003401d407482d0001e15040d16410359540d240c3c01001902e004c4d040e04042a500e402c441d0800a400803001d4503092016410f2843c03440c01c0c00c0c5d140c00b844045c1c0b02d01403d9641c000000a000700d405020f2603840140c0003260181c07801060350180000d200200000f8010301d500c5051441001d88020094001821702900260318074170ba5401105503010803030311442c002620140000140d0610030800c01c5170f13040030b1a116040e03042040e44c03541c00ea041d1120a9203036a440a2104c0141c0c3d0070f200d41c48484480d07038014800105030134070502110202c4075000301078400c490b030380d84081102101d840e0000c9010560244035109140c001920259020808038000d0031032201c4803510307940324440c407014042c0c01040d4400d1082408195042803102c0492003001075075031740c2c0d5108915201d4000c08451600001880c0b1480c840c035100c3d01400340500240a4021a2000c0c1d000c401e9403842060745007202031000d04191 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 884051555 1250 884050305 884050309
    0xe1302120601062106052805010e090a0504140118060509010209010903080c10020703030e06090601180b011416051002030c2b06080c0114030c0a0c080d090606170a03170a0902 77
    0x11103034000c3d4405c9840d01d40d28914840940d41d051f0740d03401c0f642c100306440e02c480300c1c82d603036280b4035076040160030340d0024051f00d603030904c9620300f40c0b5000f1a00880d820aa917800062035640c00380b1a040340103035000c1100ea15041103d600f80d203c0c02d002e113800121444c0c1c041c0007142e4120000c00c01c88014074100d5818400c003100b05010b80e000705c10103401207a943c1446541030442808856403140101024000b1581803008880300c030700040391b0b040c040c1381c3c0e1001c11900c6640030b04070880568401182c16904d0320414864200521011501120b01d4054070007120f05c44d002500a50b4017800d090401c042c100400c14041d903180810b111000304450b20600b1802c0d0384020a80b20700c1d005414a040a012403c034008c002524440030925900440c0d0303010000c1102072108107055a0141e103480c40e01040003851340c14080914092000d09403052464907401c10f0030006994060011180c0031001d0300a403c40028503161174108608000e004a45001d603131400b9010b41c11405903100b014030900103814410781e00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 884052805 1250 884051555 884051569
    0x80c2e050405130c1e0311040e09010b060f1c06030b0f040b010b090d0f02010519020124082d030d020315041812090e130212060106210605 61
    0x60501140c0d0019040c09903050118041d1541120b040c4103010580070404001c111081007811180401006000d40905a10035000590f2070040f4489540c0c9440d100c040e02c144500d4103a4261046610b410501e101c1781c100841505c864440321032040b42020840404800000640048280025654000400012003e141550041c00c074010340705000d141a01c0c001c22091011780100419070740900c100741c0d80b50313900701c0c0c1c018070540c0c86030008806403010702c01031368207006590154203003850454100151590552014130420345281700000f0401ca0818001c0c0315500c5402168141c0c1c01226984440d50071103c00c001e0342000362005010340c030b0b03048880681503411a4458100c0d65800100f0b0060f00b62410407030707a0015004403030402c48a188130408a825018247e4000d1884041c00001e205041c0070f07008540c010404604044510320304804442c2c018400078504070304c01e1003c20500071116000140f81030683d881e64849881e101c42c8a00e110030400c140110111149481f502c020940b500ca0340303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 884054055 1250 884052805 884052889
    0x403061e180b0a050129160503130f030209180a08040602070501180b0702211b13050c0d09060207050d0801050922120c060603080d060f080c 62
    0x600e4100807242a00c0c0c003002c0200094000012182010014050560704501c8078484440c181ca4080c2c000742c42c20b20301c90b424014a03d80000c040038282d020401d100d000710080c20480150505059801d0720f0700c1c48590051064000a5081a6003c000400c01c42c40880400034103c4124101d8452a91550342c062442d48540c200e140180c102c200d08100c1560807401d8848a0501803030001401790500324409068091908041d02c80e0041071042c1940b24030401d104150315081d007081d5003950420400c0c225516082e8250f4038007409000d181081c1342003480c401da902410810300183d1a001000c9100c5014100301501550641e41c2008000c00054003000141c00c103100d2a101c0e03003c2036240c002005a4a0b2004181d0401c9400000220b1050042c035241d141d4001e51104014036011b890410446280081220051250780b80c058040248079005c1d010340380007201e441c0c0034081d45440c0c02041c035101400d8803807040254801c00011949203092910780f9a08001d1014120b0511240001c0d000d10705100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 884055305 1250 884054055 884054081
    0xc0a0b04090b03010b060a0f35060306090d030c050d02041d060d0804060c1403120610050403020315060d05120a091a0d0e010e0d03050a050702120403061e 68
    0x6081040c034040d070142c5060004110001c200d0684c0c1c11021402e20f03c58881600104940401c54800080c01a141914031401180c61000c400d0440c0d02d031441108076140e4450054412000050014600006c885105003400c4010f8a20404128025009410804213030802d1003070030711003031010040ca8800f4000420a24240100e426030803c181c1144200141c41c40f801100781d1801c10b400704920000310f80884007246081154001d86083c42c40002c49582544075881c0000a186010b282402402e40e000320b0044039484912004c0400545480c451403200a4050300100000701881514030465070340080050400b1100c000940d5449081c2101d83c00243c007024000718038403000c5a4000c003070740040c3c50781d80d8600481842030003003c101d600a00002031521620342d14042c1d44410290804017031240c4246c02c403400748010341000f50182004a8440c00700f113142c20000b07003603280300003003421003500380d40101c42c03405095480d003402515440da4601f601440aa0740c1c0c80089039144038201000c046 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 884056555 1250 884055305 884055307
    0x507111302070f17070f080d06030222061403070504050a09050f071e18020306040b12030913052a071e051b01090915051018080109050a02060901020c0a0b 68
    0x70500d0442028883c2c14001e496455040c060000024003466031030340010f8104020f980c50302405011023000c0e08072600000d4100549400750b164182510705d045444030000c901c10b100054440b4030741d141001d001424268154407011082000b41407582c4065004103072900040b5001100c3e461b10b1b0314040ca241001242541b150b1070800c89903000d038403492819940c514860800310b2510061600c410381402111030104d6000002c60010b9032954001c0318030702c6001c0c00d031514500000208984a40200411034002c0320444c8140c41440c0340f80c451148128103c40d4054407064250442000c03d01100301c0d000c9110404029071808603062200d03002e01a5440f00b400400e0310b8040c80c0c00e50500080008031008461042010b564681c0c010401c0c0042d200300401c0040c0c010030091406100220961001c1d8010714280c0d021080e443d8007980303600c41c90220720a01040a0f64924400c1c3c01c07101200d070041c106411140046d401807034590300134501e5403814812114607440e610001198003000d03501402003020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 884057805 1250 884056555 884056583
    0x50904020919080d030e0a0209220b0105150f0403060207081e030711010212011413020f0405030c01020a03020a030503060f1201272402040b0a03061e06050711130207 73
    0xc2c08000130b0280c1c151038941840502004541e4130703920906018000c2c400e0200400084074400214080d141c060b09600041c440d1010505045a01440a01074540220143e142d41d101000d50103049450b6051103103951841c040ca5074948500941000c0021614a10204040801c242850100310003d1810b80c008650f00c0c00c0c421409000e4801074000b4118a9005102d0746a056182804040c110b4200910b00041c02c1a074000081c0491805040341035442d03c0420407100141c0f80d50003401c01c5d51401d40c1250b180220100041e0781e640038241c3c0040042c1e109800e00f900013403041d0040c50700034502401a41303c8141e0100003c3c030117551021211041c3c3c1d0740e800c2d111841c22002c182e0300c030441000c0c43e400302204815112420b000300a2003548610300c000040c0c41b4089081c41c0d04032001060b9450010313440341e090000c01000740001d40719441940600c0c03500c101c8444031030720900044031181e4031541d01d00081541d07403c01d652564200303242e00c881811071201210130240004c00006105969000c0000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 884059055 1250 884057805 884057819
    0x30a0809030105060904120c020102010e01020c1b0103140a0c0512040b0f0a0c05120c211609061d12010c0e040e06130b090c061902060f070f050904020919 68
    0x100f00404003032046010a017444040390b0880345500809030701e4580720041600600050b800340043c400c4180303982d840064009018240031410b2a0010b4800c6960b40d046890480110190b450048201d038844c2100030215100910039400006a4141801c0050602060700340c02c040820040310290340f105180e008010304014000d00e820b83c07090301000208001d41e589000103080c1e014140910941c00c1032100460781b1400d400003540c1301145201c2404d5198580d48000e00081107050f5001110401203564611485018070235420559034242d0740c1088031441c0b04c01d802c40003505e01d25120b4100742c110380c0c10700c0070a1081c000e0100d5815030b230704e544205100c1201400b081719065400c0c0c0706543c10490900c06028542c820405249030400041074998541811a500340401d0140480c2c0c002c10014408546c05c040320040702d119607068090300c00b26510040704014101d0201d86404c0001c50111002a42c140198064881c008002d0401030600700076401107040b004051800060b4082c4da0002041b00e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 884060305 1250 884059055 884059061
    0x605030f0907150f14040803090316080a020918010507080603070905271504031805010f02100510080703050114010506130b0702221512080423030a08090301 69
    0xc070150004107032092400c514030f100004040408004c01800c103214450341c0b84908220116101240d200c2695156100344480d640d9001c950290b009000f054254040c55104081c1281110710043c040d0020003541c1c2c0c04c10209210007403071041429000c401030710780780c0000d104240c0b11300d1551b1696111418540100340c07070120140d010081403800c0c10100040d0140001c03809242c03650b401c4a0449404e0014102030500c0b45880b4131400188926040009144c4d00541c604001001124031480181c2c81e03a004466413000c490721100035a004918611641c0f0166200c168440441d000c018020f0b81c4403908103081c0041c2d9441501c2e140c1d1540c0200600644100007140100300072a0620718020106016010000031482810044400801c62070203546500b0000d00c03040c900d010240d080c80d800303903091500070580e90b488101000020007000c1a40d41549460031225900213840f54105841c101c840051002c980e40e0700d203c1c1c0c03003800c0d9136111f10341c4081042c004070600c12000d480d04c8202d070a090600b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 884061555 1250 884060305 884060311
    0x20d05040327031a0c07020d0b1e1303140c010c090305010515030d050c07050927071223070b071101021603020f010215012304020a0512040f0501060605030f 69
    0x490b800304100b040094049000000c1d2050200e00c920003990750f500b043c480078002c4540c003a4010712000540020040980d0b2507900c140040107498110010301c01c18a0078502c01201d2170140815180f4950780841e000c4c41c0b080b0940540600030354a000703500c0c00c00d1400d6500800d401d0b00420f0352030b841881000000c0c05091b500130710b0b1000510081f601400083d555140c0f8030880e1b024403c000484060b0320303005000702c03006004090056030301c40c10050515410315000442d40181c0c90340180c01403045030b1021071341c04101c852240c4005200401038541905804010b901500801c0d1004144000c0420901504e0003d000c0708080d11703112050750400446450169071000d0440d04420750300c0501002e440a070400b584c0e015280207000b102c0a0f00180d1500d41048240e075145100e03c00001940c082c0342d00e080f116400c0a8680300c1001a4540902080e8082c0601620200b1406c1c0004d00b94640c40014166000f8081e4880f80342c10805510741500715061900444d001550000c01c000d0b204403110b0b145a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 884062805 1250 884061555 884061617
    0x605071104060f091112011a2503020d0212030c0c010b131e0b03030a0f051b0d090503030702130203060303040e070906080f0402030709020f2205010201060609080d12020d050403 78
    0x21800a031b11160454a03c0d05001c0d00080d4420055807038142c4c007122060343d00c0d0664000c0450104102d00e512818140d2408800710f0040c803680032660605480401c003080703020401d40b0480d00719180d10990b0844c0e5040040728200e55940c8409051082e62400d4820340411090b90f4001243e0400c4600480c00b202183e0541d0701e19418401100344684000040b54101a0103192504600a51790002c5901d4810010a22011105941c11650304e00010400103c4010141c442d16070881d916020302d0b442e07019180d0041d43c000010304880681030801d800955008600a013a6403400703481c1c0240c0c80c1051310a07560500020211401842102e40010119820200f10f20942c6c22038030b41507001035a1003005009105000742c02040c04a8503900d9002941d1860400ca184560402c061040787c2c1c404031001d02c9010700540c2040c10010f4030314000c040940980c2e6001010340050801d44c041601c003030102d104880c003080e600704401641d280f01403086c203024502c41c1e0303034071b45c104040d100d00c1001d0641049001d032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 884064055 1250 884062805 884062807
    0x2070c0e010f0e130206070201030f1a0102060115020712050f0316050c0409150c180308270310020309160308120c090d0609020f03370c0605071104060f0911 69
    0x1089503a4a03142040c0d081c1c0c110782c103039030310110388c801213003d0829012045001070030444030b131980354041d003024000e4903001c1c0c1c00c0314880d0f82e03510b807110540d407210021880582c20221090003100c0074901a00403080c0120126206540c030044c00e00c1c0755502a0507901405021038503041c007085810302c420404000300702c40500038010140c4030007080740100b007905c0b000349a07118142d0401d640550385014000c1d60070001b900140c1c0c0e9a04214005034827501c10b08804400126441d14603074604211004031003006002400f864201090340802580080c01c0034202d44106084c20714544010905c82c1c01441c81240302540303401446a44414000001e808001c40503410311100000f6260038070440d8082e9003080c0049a018000c0c008501c01100f10181180c26004500e804424a03600088080421004031407105540302c60310104441c0040c0708030020702d00414044104030040c0300700090b2138210b01504000d1070004170300340002c04660035940406009542c5200410544602d846075090b41c080340700c00c003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 884065305 1250 884064055 884064061
    0x1b1107050306190f0f0c02030a030501210f1e1203141506160b0c0403171306030506061c0c12022a120d060e0601020f0d110102070c0e010f0e 62
    0x114103a640410b020014059075000440501403131a004901101c941c0141040004050003000b5265440006100301003402c14000140c2d038440c0c0c00d04011224048804801100b115940312525030a24150a6607104148100e20040c005240d80580d000d9114442000400e0304c5d40034080d060b00c101d506000e030310702640c004001030080e40c2c0e0b07544241c00c0402c0328480e99950041c000c01d4603003504818090f0400002d5010001c1c4400300744000c0003540d004000300040312a0005030019a07120300c01d080880c0314001300d0100907440c040c0d0841600100028041e40c00e0011035403460504500e102c1041c0c1403182c450ba8258800e03600030340000c080b1406014158a44106101e4000c0f0005050202c01140e402c5000d2840c2d1003101031042c0f105940c150369007159198281220b00020308941d004002c4042e03c204003098456000260503442d44c4010001b808a08003440b1040d55010402d460004465408208020000d4004400c000150003100d5030303900d880d410803891410449407038000045001e510424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 884066555 1250 884065305 884065321
    0x409060608240a03080d060801060b0c1504031704032123040303020708030c090109090c2304050a1d060d020105030103060f200909060a15121b1107050306 68
    0x19030044249500754001d914080e21001c5452220360f03600103032115401280015813241c25420510499140200a00004c0d460320184c40c0bc0d4400c00381c0040f4103a002d018840926101090344940c040e00030b04200c042555025145c5560710300860f07040300001c0c0025524030b1102080b4940f42c80b0850440300c20811420302c1d1f40b11400207180705900115054058000801305031194048950080d07106582c982c0720b0800782c1c100202c0c0d400c0504141c3c086107407401e01040411840c840c0c650702d08015a01c0300ea00450380940c0d41c02e161640320b81801113900810002ca050344407101c00340002c0ca01540b4100c41c1a03c1c1340180b540701e04002e008107115050705030380f650242c0ea01c9020380b41581d40002e4001000d0701540c582c4802448055480b2640d2203102d40c08030f002c169124003418050000740c0703c696032540c8080c1042810401401281e102120f05107104400e1031180c01c03a00441038040c0000590a40210000650701e0045001840010300c0062152040c001c2808200000c000035001001c080c1032100c0307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 884067805 1250 884066555 884066581
    0x605160306080a0b0a0e0102162009060607020a03060c020c011b0506010b0c0a020307030b040201021603150c050d020c010b01090f08100c020c0927190201051309060b0409060608 78
    0xf40c0902942008004030b0000881580018802c103a043c0086540f07865241c5013002d581c260b0002503540800400190b0541c0b08450261003607d60020b08244144d81c5d4001040130607081031030241d0304020b5078140403000403568401e10f0f210308001e4004007081401c0500041c28894000441c83c002030002d20440c0005100060890540b0b01d0f90454941710008152103030f151201d04d000203507040c030480c0c50010911081c944c00602550003a820b07909004688860740b80546102d1200420099882007070300a06401d941c0111180701d5145061490082070241d180d0030f9070000b00340104565500c3c1403802003580c21040200c01440d182c14482d000030319201034662640685180c3d546074a4030350b01d089140c0d6209000729894020010100c81ca1820011101c08031107224560004940c1624503107c031b13800c0d500040158012948018031030480e005680111183c1d0000c0c0ca801d241c40a40002c0820014103600405e00603010310025191601e01d8444c400302594055840320040c01625428004500c0303801c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 884069055 1250 884067805 884067823
    0x301080115120f02031c0519050c0706120906050901020c0f06132d0b0106020c01020102131211090705030421021b0303210901060501020309100327060516030608 71
    0x3a65201095035400840e04086c20812000c050000001e2560b0031280c024020340701020748001c1000f10b0300741e8000300356120702c55080d0403001588070070700c10042e062203504602010030424a02040c1c41041d42c0c0c0700e400b598401c0c2ca0041850f5000715061191040030080132101c00b8105004043d98101841c450f0032401600e10301800d541a00241c004224502c1c000300240042c4200103007018100d41d081c018003608082c010200180a98601c0d040c0540c414005e0310640040d0810f20000720349422040c40152005440407146050800f402403800e64400c00114424885038440d0340d03480c5001c2c50625890f03608542c483d40c02ca84038220000fa9130b54001101860180c00030444a50401c1034400039255010f404a541c200880d600801d140240842200c1d0b4012141d0385d001f8420507071181c0040e42c80f401820595030701b000305000d48a0b0032074420341003042d40205840c5106d490081c2c256460141c07052221302691019101c00030b10070350400100c100103001001d0319081103010f0038103280ca034039441c0c1c1c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 884070305 1250 884069055 884069063
    0x2040302130e190b0618010b0f09030f0f030415050f1206120610080708060903030613021e04060e0a06120c0e030d020601050a060203120402280b030108011512 70
    0x41c180b40e40300c03507204002e542c2c5507030360342d25401c03a652026142040810404a55650180b00701c00740340004800c2e00d07082141038403d40001281007029140d210141c0381c2100c00b60030341c0340c03107240b5002940385010700c00c94050b41f003050061550389040460401188850a1400b0704004007041104860039401013a030b034680c2150310508801b511a0000589036000d81c110860103801a6400d1100c0c1c00000c00e0b61800326460101606d019603942c841c2075403103040031155174415420410001d6220b14116034204420905040c6c0181400381c4480340e1002c4a10070b01e008101054001028003055400103086c04910384111049808039041040c0240781c1c4c007005910800b0903071205108081c40c0c0c007a04158070b078450054126102c105101c10001c1d512034080c854a8021680014081891440401100c4900620701401943c5032204ea00b80008820454500c1460842a445904074014040002401880308030140c0c0d40f40d504202c0b00c1400c4480c050300fa00c500d40417400c010011012103405800f100c0341c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 884071555 1250 884070305 884070311
    0xf140915031f170738190c0506040201111002070804230a06080c07050a1101080f040b07051b0628020c1b0607080a0201091b05010512041104021803010509010204030213 74
    0x29110854003125a9074024001d50301580c0c1c4603081c6010145c0504400e80c0400c4150305d110b8400002680c4071030281c0c1000e030450304060001001365000750302c06442c25401d1412180311030000c601341d02c120780082c5000c80700c00100007001c008140c440105207500e2280e1442c240000c590440000c1c42c01c40c000d200d08401d0140c904006011401312009036001d458001003607681e09410340c0340210240110b664030a0229201c3d40101d2214941d40050034031480d880b0920450235140c103038007601c0c180c2000424410310103042e49071407952103040c0803550142038800c1caaa40007a00f001404258504081c2c0d02c01315036032040c0b14100400c034001480319080e580e2072003030084408050000c203292b44110000980740510024281241d91380c154030860145000702031a1649600d156143c4c2c105504501c40c290020b042403001902404040d419150024455903a0502110303c544c0400d059800240403c00d01c251145070742841ca00b030a0107815408003603000210700d00790860b0300080c0f07007407030380c02c4003c03c560f03a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 884072805 1250 884071555 884071589
    0x6040b120a3009050a090216141204080606030c06190302070809190e090c0d060c0c0c08070801200f071103060c090f010f140915031f1707 61
    0x42100c03214000031042550003140d1031210000341c04030003e4400e00c1d004d090b0601001403041141c0c401e0302c004c2e0a224141035010465900d50802e02e40304151000c00074001d054a03140c094040d800188001c008000c0903100c141b0b07010b0f0030503041c20401c204460080c0c000b0014a00341610704e890030315803005a07040041c7c4640c81410075059601420804c1030b00042196854080e00000c818030320100c074041c250200c0143ea03030904242d2036410f5038241d5a0091031840d206400980c081c1c100c013001c0010b03031402c40280011a292a05041d11a41c4607184640054200b404502d5080c010038443c500d0754205401403410400d44079600c3d101e20400b03024906804a24081040b1280b120b0b40d00c1800c00801b00d03002810240701490280d48140c0c4c00034866007103c1c0b0a01d01c154007a260010b01405503407920301840d2030f5800c50009a034003620100d03500060a19002d90b0402480000d580110340c0000442c08050100c07007021700300751664001c181c08a015100a110351440010b4103000c0c4c8280c0001000324507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 884074055 1250 884072805 884072843
    0xf0c020906010318050a21030e150402061620040506030604030e010c08040e010609091e0e0a0203100504020a050109030b0402060f280201320702030702090f06040b120a 74
    0x5201314004140b4001d980d43c40083c0003280c25007109101c9814101c00c015411894180e041307074600700703106a40303422220040201042c40060203503c10f00107002c1500d17014100043d140840a181e0b41264510318000b064280fa1100380d0041c0c030014000c0d2002c001d18280000000c0c1e0307502c002880241001038010710035884c0d07403081240701d45030342d4081034507515581c03208603aa40303900d402d0003041c000a0300e4000004000c01175001c3e4880010300d4400d48200d402c440314110010302031540781e40c01e080c8500041280161020400900b140d107a80344009141c3c00c1520410a6006007603020a0411100c200c0920100f880c501c200d0b5007169044902a90310b82c2140c804121f0350180343c111400c0c01401c030703014451412030310f050001404081d034001c000d2160500d0f4114070902d130303078030f5113011481c0040c0c002c409a02300c0e0314005400034842d004990500749503a000407007a150446004c58000008014010706040501070a180020200c92240141d54120045503590004000141120140042c0e1049030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 884075305 1250 884074055 884074091
    0x708061305211204060b09060a1508100810060e09011506120b0405090c040501170d0302090f10180801050f0c030703151d1b1c0b0406150f0c0209060103 67
    0x404551030b0500160f24017420000010000f442e0841c4c002c52003500002e07010301c2c18840503015295960410100e04d1142c40d022100500d00030002c8a2600305c0d07203c08940c4410401c2805081c410900c1b01050741420100103201d900c60142030701d071080c3c1c101140044111005417080c0c0c1034a4040c0342c11103240102c041c0003006080b00604c16500309144c4020300c40402800300b00d0040d0703018155014005643e07610911030a070308131501465038941064442c0001d07031f48070f50010445103400030914500f9000c400c0c00100200c0c1070000c54004912482d0711403001591001d0380e00003d100340740007004149406543d1411140c00101503800310600040081c940c1402a0f026070052001c1c035240010040d241c82003030260701503102c40c000c01e140301240040c0030000c038600d120902042e00600e2a0601030f0485861108001c1000250400307a22030180c001203440301e10900009081c1601080c2e0aa04450009880c203904000040b003080b070420f883d8401750305c803e400303603400000a02c5c0026008807040302c4402d030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 884076555 1250 884075305 884075317
    0x903030a05221401030e0a0b07121e0903020d0206010b07230105090105060a0e0108070e041e03090e01050402120c030720061501170f27070806130521 66
    0xc1005520041079a5110040a880643c1c081c1c0f400c0100850f9400501d5840398100801810313811601e0006000e507200300b405841e07800600102144102900c8040e01d64418030401005100765251403003c1030680c104241102000a800501030310350400a104405105400c00688045402d104050014200c05005003901080340e008115606103848642d0280034147c134194403c2c020000041003d504907001c2e28101d484041c002c0500e140b0300034100704003150042081c0caa0a0200800c0502140180317607422142e442a60359071451400d01c0d603803848040c0180c000f14042c1d4414448a105481540102500020b1908100e5101d9071044030444150301c51301e40300c65901d210900c400701c00b00000680325004503d150200e0ba240c8a0801c0111050420300c40c00c2110010780038041440c1e00f6110705080c1d04440d009242003243c4c0e8032001e50400312941d0580e10002c0e540414420003040c1c50500516802c250145010a003100240d21281d179125014094840344099007480c0c00302000d8103004480c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 884077805 1250 884076555 884076607
    0x304050610060f230d1505150405032d0604050703060f02030702030a030f0605130207021e031e1204060c051b060a03050c04030204140403090603050f160e04052a0903030a05 76
    0x29039081b810300030f4500307442054003c0c60300014541e02403840c0c00c1038405031030700600100225400d03081c0c0184413105846000c8003103c4000c901c0207001c0d01c10f202107031085d1302410003003880e54518501802241c0040c02c41440c00c0f4410320500004c030707034044225607001d080c0b4034010529109807500706009115542c4220b80c0043d920755034802070302062700a815028001c81e04014044c0500380c2040c40440220400d55058008003042e8903500c10307103402c440c41e0604210480701b8024000303403001c8050b8059044000454400440e013800c110040040c15640d198107501905802c1410001c00c81303074050b0800d410181500c2c3c20014034803582d900c00307507001103400400034080c1e41e40c60f0703030f030104500710548081e000035090410124950303000307004443c0900724458910766140c7e1140e14450b0503041281d102000c0100c40c481189440d0b0365806424000c20001e10161040710121841100c03a4044020702150420203000b132258940e030100a07107070191054103120341e945004260160704a120844142 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 884079055 1250 884077805 884077811
    0x403021e0c030c0d0f240f020c0616082a0304030903020a1413090302010e060411030c0f06040911040812090406120b0117010905030304050610060f230d 67
    0x2408603a000554005091094054860389007602c8140000d01460703103406055226020310030300000301401040001c0010320041100107080d895920704c2039800d140c54440350320350042203040c030040c8140503240d0442c91808420703820f96a00c0001070289407005002020000c113000c5550400a0403401180510a118070b100343e507450300345006402c0d44080e00042c0c1c09041e1180000c600f2031007451750402007000003003542110708100f0100001612003018100d08554a90108044404007008400c2c0603500c07d15a81e50980700100c03d041c80c00c203401c0c503041d1082070034100c003a2140d20750030125002c0e00d11800004c50302e46003401c403003030b1580319552000e605031040142e2002610360f2030b80502442081102c041c424035654040c5040d24800c2c010b0054150401080100041515091600d82a030140000407455500d2034031010b045800464082d181038100400300001c101d4884480c0380038020b00c0c1410140072242e0740006042610061303480e140e0401440c8000c1d1240000400d1354141c0d03201103418 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 884080305 1250 884079055 884079103
    0x909041203050c0f0d091406101401020c130c02070305031b06060609061902071a0c0c01080919111005091f0e0405040f120503040302060717040803040302 68
    0x150316084540140c00040d02e004085401c1044400880c0e08190310206a241081d0b1500604801000719140488001c0d409007403480c1d4000301402680d10503004055410070f19490019041c049030340c0820314038110f4200c410140380680d101a6171541601e20210300081944002c0416407410115810140892001003008244001071038049108003410100383d44140d20796030244600d5000302c2d1035803940f2000601c5491724500851300c00140304101da1044400e0607544000305161042d080150302c117124000200340c0700e00c00040100700b00d46507080c82c05035403c3c50409107076a2038440110f81510600001a043c0c030601101e101c0304042e00400624010445005010280c825070110030400d004030204110341050801c4002800040c0121782c80c2d14002c0342e90307941008004c01000b041254400d0540300640c020402c800c078002c00a0000391246941c900f01420041c2c03504400401e0340c420088003a0200407d11701051100d42c116a202e43d5858803603c840c5801c0e03080c80242d00700d00c04800550401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 884081555 1250 884080305 884080313
    0x7051809010b0303070f060e06010608012c10050307050d08030c03040503040902160201030b0a03020306181e0115170a020f12062a1305010f051204030309020f0303070209041106090904 81
    0x6650003179102e031f10104002080c7c81800341e02d4150910600c00800d400000410101c142d100d1614000100d08800440080754441e0b5034002c41015690f40600c40402e010a0025040c04c100c0c0c00043c050855110f43c2600c0c1a603107030941c40c03000400d2400e21210100201e0100f0000304140d0740a41011341d4203544400154940000c603c0030110164002800c00401c0e04180c01c1100f910700517a600680a0901d0780d4034840a07451010341c214180020344244844078210000030104071074008040c10021843c030750046410b0074444881d0708003011580a40050701407001c000950040b40300e0b41502d0340000c50303081100260907540d07091001c5200740904c02c20896609040c0c2d10715030700c070000c5005c3c038802c485103141c001e0078601515840d050041d00410052040c0e6001d001d0401d07950903545001803510000d1035840c0103c4405480490200707458802c90002c520300040502c0705140150004c6080070410340014207041c00c00b81002e0704141e044c1c030320041d050b2580310458804100c050100b81c0c80f410b003490 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 884082805 1250 884081555 884081573
    0x1110306041508070308120a090b0a0c0e151209030a05071b050603040c030c0b090604140d050a0602300403030507050c031b0c090f040b0c040f240207051809010b030307 74
    0x3d80d4039281f50b554001000e8807058480c5480c0c40380c101083c3c4102d80c1d6a14100801004d000e2000024002c00c0d000301d010300c0d0784d0640000c247c20648824192103184079452a0341c202000b51110702c1c03582061217644042c540c00800d441c3e4940e040075886030440350242c0030b00c50803201c60304881d801450001c10031080c010903644c0442160700c626020703d05590b4034403090a89020f2140c1c41e940c1329200300400c00141034001c2280040d50310041120600082c9a83c4d482d01d003400381981140c0141c1c0201d03420501c8007941c008119860381c4240d8480243d24043d00000e201c003c0180010280343e80c80c400b08046e075101e230b400d6480b034003100c800f12643c0e0140100394000e6404419040705451181c0407880f5404e0919180690240200c80c44240302034a83e40c1e00e40c800700600610251318030209010001d06100e03552a50710040c100301c854041601c50305614103842019002d024019580109002c0009880e01c0743c40c1098606551140c0500e91240603929014003100c00f0403543c14030011035640c0034480d03110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 884084055 1250 884082805 884082817
    0x1502031801030213030b09010b060c070303030606050a090603020d1d0a0203120906030c07030c200325051e09040b0619080d0c02060705010518070801110306041508070308 75
    0x500540c25200c9014011800c3e0701c80d80440c10900200d22030304100040f074000038541c0210341c150005c1107644a103400309a05030000205098035500012080003415003601c41c2001400552906624022241001500003146032143c001059030004101c0d1a000441e4050b80107902484903403402124139008443c0c1d01c94544409910134010612440041e100c40c0080b590140c00141c402815a032b140d4000d00c201e60014082038092014038402c10000441d00718001010400303ca640544103603691052508c0c0060b403c14801c2d80800590004507040003018440084850031a04081140300c1c085986240d009401c20403034000504a09000400c240c520b000e502c18041500c0721700b4004c5042000114040551240304605d0304201c000a20302d911800d03141422600287c0550302d0010703a0780c0ca890840701e00f00c41740007803040c00d02c1005000360001d002d90b00081001c00c4c024401c00203c0002141240f20140140344a1940d4542d00016824030150724402040c004068511b4155682010b0007194402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 884085305 1250 884084055 884084077
    0x11b08090712020a030209062205240f0f130504230a0b13031103070f1704061706120303010906030201030c030e1f11040909050f0609060718150203 65
    0x1040d0115a0320458950302c0c11643e0001c01c4458450325507000c0c40294040680240d4009001c2500c03900700c0883d8820b000341000c8141310014007840c100a41e000d01100c001e07045111402002081509a41c641042000c200d0003182d4001c2520300c07580018111040900c80c08410030b00307120420003071140e00300c00c2d41900074030581d0322044060502d50712501c8960300748004008521107800708003444441080944094464281702c8415080101450f1039034006a0f82150345912100c00d620411912052100f50780510b802c00500341410b08401501c0b030180c89058010400601d4006801a59102d0440a4401c000c4080d170b540c95840b8050fa201401860200742d000ca81000182500f10303102c4c0c0304404414210310042e00c00036500c00c1c603045801140001d400314050700c0d54012040c0900c1740000348000c0040f510001600d40d014074046040060785200e8004581145080010914001c1100390748418945000352030040086030a465400c242d400080841c04111003081125400100a248068103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 884086555 1250 884085305 884085313
    0x9100302041e060801170328020120090121050f15010f0806010305040c17070f0f0501050708030c070b01060f080a1109040e0111030406051012021c05011b0809 70
    0x90304541c40c0003018644180c00005400304c0c010081c0d50070800d0101e404505c8001564a482d000d000803400d400c0c86088801c01201c03c0c0110451210340912400c80109a0341015801940d4407942e00a218014100b034241031003203408268002c0001740714520f813280c041090800060030f10221100c0c505408680400f6400c0512024140e550300a2088410548140c4e655441503900e4030b0046003e000043c00071030b5442078600020461528500080003542002070007000c0185c6401e511244800044c0d1007001d4200d00b0243c28480d40e40e00108541103240c01c00c01155803030f10343ca002d400c5648110440905601c200500119030142e1118884000c0315096032800103584030700400c03d044032508001000c0407201081003407854145600428003210745c00c00000383d650541d512000e0b03260310031101100c080d542e42003001b90345046000002d000c0c015099245180003803950108107055029050000003400c21170f10341c03003001000d402c61a00051002c2c004400d2800c2003034040c003220400e6840c184079000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 884087805 1250 884086555 884086589
    0x1060321020d1d010309031715011b081213080c100b0303031014032a04140403020304090b121c020618071503060e0118050705030403080604110910030204 68
    0x40b00d0705044400c2d49614840f400000008801500100151001207062091305240300e49040898502d10b445424420014006032513a00c2c001041c0c581071501001c0080c0f001040302010900c034030107403039009a1540e611007442c3c8031482d458071841c01d0364200a160b16000207241c1c6000b9008514107034014042d8509022044091301095101d000c121b40404030365110307510400440e00842190715603204080c080c1c0e80d08000c1503020b041c107031400d9048202ea28000107050041400c182c401c040d14072103e200d141e2a14141079a00a40301e210703038442d02454580700d040201c41070340d5146662070601e40900886030110105070800d00c1405880a110002d4021540000c091400e07010200c04a549180094051141454242c2407414a8443c90f102015542c060104441d0591850345010b00300d03406a0b00703842903416500748141c50b0001d0110301048000d0051000113500719803415082082260042100340c80248484414020117030241c1d4403810040000f0100f54056006009031040d00c8103001081c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 884089055 1250 884087805 884087807
    0x7080a060b120c1003150f0f0f0b0a050702130207060906050a05191503141c0e1f020111130e1b070209042915040c020c100201060321020d 61
    0x440a48404000d5030001c0d00340080c145010644d0b080c4012050a0000b640318082e05c9a00b0840500c2c1c02c00a054100f2840a0003001070f00d424120080800a8048000505108202115001d680821000c1c0306010450742d01710b5030381d5010900401c00c0364400319101c003540e003000009031100d0442541c0c0c41d460b0601041c0140902c2c0580b07446043c090543c0302680102a0000c401080c1d50b04090407138800b803000110001e07500b43c5040d003c40816000502e080034010000316440c5400c8161750003840702a100140c1d01740c90b050008194143c80c0081540751a0742c82c40e090307000d8030004c07407801511440050701a9001c44569040402c0d58503410318035803640d03201800c481c007051088980c0500c1882c10b01c54180140303010101140d02c01c0c801d6011000c00b0200f0058185501e0904c1d1440206a014508000c0b18a00541c03c03010a12030885090008102c280b0300613488400c1c980300c0600030040c440c03010440c94001d4204000440e800300314005100044051000010b2200b45001c0c010b0007a0760000004d9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 884090305 1250 884089055 884089069
    0x50f0d0b010807110d0c030c0507060c0b09011b08060d170414030a0812090f07030f03031413140c061c05010b04031110030e06090a050712170c03070507080a060b 71
    0x4481303540010700000ca80e0103410b44640408070002c504205c515456000007900a10040c0c0007000b458441011401040c40e00000c84c0d07500400708006030b89003001070940f0564410f001d018040741400c0c6501c3c0c549074100424003040100300702900007004402010207251000004004441c510004007000340d1403181016119500058090f040500070303c07100460142c074075152900908144100d0b894441940040390030070080740d0054550250408600052641500a1054005032002c040760f0b145880010809a28a02140904407a019402071226040104074400c02c0e510000c1030261a14900451701d10405400945914181d0402000281c03001c040400c4d54140c99108071400000e40f00c10307083c40000700300c807000201010b44400d181010110306000700e43c001c50f45000541450000da0038110302e400b803194070485904540307451a6003c1840c6001e00c0344030f030510301a01d03a84c0d13224141d1118554081d05c003001c1c0090150610001c1c1c1c04600141c03900301d261140c40c2c14450403441c07000b00618 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 884091555 1250 884090305 884090327
    0x509070509130b15031c080708250305041e080c160e150303090a090e01060506041214240f0c031603051f090605091b0702010f050f0d0b010807 63
    0x50044500404c4900b0080100801c0c0024043c0c112840a03176811a4080000541d898110220b100f08003800662584100c0b0b25134080d02ea000207500c1085120f010060240151003404101640c071000310b000c10a0103a05043c00c4007628030800d00091740b90074a9900c940c0040000b42c9075200c2c101803502c50044120b400002c54803182c0380c04405507547c450441d09010410103a0f07030300d40020030124040b959540200c00c0075281150b00010380546001101d4210380d0203401242c8200c1042c0403c00008030410600c1d40e000e54019200c0d4503020341d058509292400d4130b0014440712611005403039100c6084000544100400d2070741140c2d5490b50960f5258501c0292610081d2003440c100c80c0c08201d0207a0403d40e004070401c664480e010500d040c102c0ca4034205908580b09080d20b0300020019071034403d0440c1d40066000705228000141044a24072504c600c0c20020306005030000000603950058094501503040580c80700e65885514025500605095106a01003540a008071313040306c0c45049040a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 884092805 1250 884091555 884091563
    0x31b03020c0616080424060603020403060f050103020a0b2821050105060306120f010e1605010819050c1603080703470402160b01050111030d05040312050907050913 72
    0x800c0d074840d46c55607140c020304070301610710300e000b25071040040159900c10000207204a81c0d00584890640c5840c6d41583c01580203241901d00703000040c03000d642c504c010070048581c00385410350380310b480c2d509014045002102c07400c02915080d410003401c54110b1480d1102e8800340381f56003c00072a0584e0a01111400c0c0035a0341c0100d1f062001540905010319182004080d15084a0103c02c0c0c0e8035000b825510b0040040f68584c0050340e0031140c51011064900c0a4002420710802c0c42c84c0c130844c0314100980111100c04460345a50100382071300191800c440d1202d802c28400c030403244ca50308025042000c00e0f0386003c0000c0c9820f20041c901200614176007844030903d00a00b000d040d540394603040405010780d058140d0225103003886100d0391184010600c034070b00c40c1180055a1b01c541484128100c059101c141400200c40200c40e40020100c01c44038180d5000000180b103803100d0804480e074241080301900030503c0c1400740f100e000d000003406800c0f01c0701240c544d5907030359510340804606402148014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 884094055 1250 884092805 884092817
    0x1401060f030b0a080a05330c0915030406090203151501080403030e0a060515060a020d0305090304031406041101020102091c080904050709060210060e0a0c031b03020c0616 75
    0x160520a412480c0d030030100034900450140c030b458200d410030070356202c12625980401e1440711140003004608140c0729807081110082e00f0030b40c64071f01c132445008140161500c0009a020250b5a903190004074241c1c1c0d488200361245490310380300e00100b10411099229202e104204d821426107800b0a070701c1503040b00c001e10280c05d031190064603000400762007107040c1611504050b0b80540304215203c1082c0c001d220120381800e203202c21600c0b440c1207090650080d0001c0000b4074100d900001e18030200d032040c0c9000100c03503980c01e03255403c40c010f94000428440c5802040d03100308400007001801240541e00c440400000e007401a400c034403c1d00042034004110105554405045204203d0300d40c1c0185d4a50f440c00b030072000002c1c200c1d0411505800801d020079400c0c0240303941003001280058036200200806410520454140781d0000e000d896556101c8005500c418407940007000101d4a02004407510381350f00c6005400303904885142580c40c07140d80001086103202000f0030341e081940740c80302 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 884095305 1250 884094055 884094077
    0x2010507050f190308060f0a0b130504110408010e010603030824040906051b03060307030b070315060f141207051e07050601060909020a08070e0307050a120303140106 73
    0x191095080104103440900036541c40e00340803582403000301c50040c04921882c40c410900d141c00b415a20014108034068500c0d465040c42e6a11341040320002e983e0032554068541000009940381a4429000700b5000350501c1d1040c20020244005001550313001c5009010819219214070b00300c54030f0780300140c0021118004140002842000101d02040e0000301070584890306008c542521415007007280c0d0320740e03108100070b0344401d60a011a83c0c40c03c1070b602030349541882c1c00001d6030b5a01c140000343c07005440c60301054040307021360322204540c1c103680d5510a4440c0e540078040c1000421a03441e40104100000340d89210040804880e41400e03440c0b003501598a80301000c03142138103c61608140c500c1c5070320040046541c00d00280c1007030b502c100b0007030042d581042c0c1d0003401090350f50300001c0b006006200300a841d94002000a50200940c07503c074010340b4a99001070718000d0144d21840e0045140b01d004540c03154030442d01445540251824040400c000d062003c28403005d11a80307002a600d040740c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 884096555 1250 884095305 884095307
    0x606100201020c0c040b0d061802090f0106050d0507030902180a05161709010b0d11031c020303060108151e04060b09012307140a030e0406060e06070503071b08010609090f0201 77
    0x20401b00c4940107403110310340340540d0b03071010111412124034a003040c030307540c161200314504011082e80c000c140c039880380c55a51400d04003074143e010307144a0056068440b00003903252442070784068142d68006040b00e4a000309504440c000b4030042d54403d00319409c1c24009850340d0401e0795084100c01880ea00c444450031040765401d101700001d09541090f5480345c2d40904146c1da11941d244404d409400780007901c100070420185452107082c2c0c40e10006c04c001000074000c54000c01680d03030240c001c1c00c0c150495510030107400d008216451066611030317080b4030f11529400703140b1115a0b80000650b01081095110a10000a4014804120300080e552004108800300704031240244441c0b4503065400c00c2c1ca9681c4141c01203601d04850f00032944103240c0d000526500540c4007010000940d8108107003801c04000802e5081e254804900130b120009002040060400440f044550420301088641c0d6100c410350708140fa03a40b090b00c5066007042070100784580315100f0351039056403100403100c0108031940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 884097805 1250 884096555 884096561
    0x50904050111040b0a03050f01031e170a020a1707020d172b1a0a170c1c020a060f0e1203070f050105012c040f020d140606100201020c0c04 61
    0x2110555290490540c102c0c0903480a4406810600300c09612501d48540060486000070400c000d05c0c02c1c0c840040001ca034151860310043c03a003407210000003880d581810010101c0d084105800d0410000e000c0c84035a501240c83c110b200d216003002c82079a00c050f00ca4604038041e000001e5840021807042d000000c51201d29120601e800c02611400d107000c000041500200c4402d28030020000c10400f048004198407500d40d40100074030059280c07403d40404103000d4810b83c000c901d4803150240b194440c0c2e001c10041d140c000c40c0b00505640031030611001d1140c1d101e80114080b4007945d00300001090f880e000f601c030902101c81941e6040c02100f410020485d80d200901440081c601082040314040750210304461400c078011800400c0a51504050300c0c040035040340340041c5944010306403100d0070890901982c1150308400c0101005e00e60f030000a42000006200a100300d845104141d4003e401146961040004544852201101d44000e030300b070784940080000c2c07503003203a1410a418070f0594 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 884099055 1250 884097805 884097811
    0xf04110f0304140f061504020304110f01030617010603060506090c180d0605090114090f071505090913050c1215043f0e0607080702030a0807030e030601060e06040509 73
    0xc1c9500400d600f0fa6124904005401c680401c040d0006410040401c640b00c1d0075090815041d1811032840c074160302e560100f20421044030f0311070054540c6454807a8030031b070080c1024280c5074068a51100c0141c0040b07008156510088841500b4203000889030b181001c0401d2249031141d600174508203024010700c0ca402d40d0b2081460344001c00d01e0014001c50558030865100b1107000000142016010a04172003840000349011300a40c0070182c1074001c1c00b00802c0740002c80b10080c0706601c03080e142c484203981501901d0340c00780d0001a50b400b040110304030f1040a900d11405042694002e1400c3c0c0d09101c031441d0401600d07001a032051045110741040141500d502038080e5042007030010401e0b11903404030180e001400c446c500595007840c0050054100d00300090045c1c04c3c20725403601d554000c211140100314018010030404191075095440603c01104500d0348040e500380d03503c146140182c00c0040316446507009115000010400034002c662441b076654000f050709003810b00c2d2104010440d8001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 884100305 1250 884099055 884099063
    0x1f0b0d0803041707080309060108120d0b0d0f030206011401090b09010e010c02061b120703210204030503131d270a0c1710020909010311120a0309050f04110f0304 71
    0x4243e21030a510300d01c400362204500c03c1201507528146121141c0c60300c10103800400300c503003116404c84040300c503480480708800e04030400032903950410f40003c2c1d0310041d000406441142c0d2101032104040d80428268141e0741030003c5001d50140e80790046807411b00302e004240c20311008002121456005005488001805141117048400c00d0b50100b0402d0700f1402c2800c1030300700414075003103c105e003d210303100034081c40014060900780641c5005124107200100da50404440070303100c0c00300b0b62541d01120050f5170844c5c200c0c0d6449040700c04929030416988580081e00c1c1c49407080a101415200c5502d014042c4030801700040082145408441000c4048030b414a02c03a810031100055541c1c0080001000d0001c00c0c810b18000a4046500f011107a203022062540704000c0e01005598035281181580d03040705407042d103880018003180244074014a404814800c0c615010700300340e440888442540c00541320000c80d00d503407800340019100712201034052000d05000150158022001840e807040c0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 884101555 1250 884100305 884100323
    0x6060e0916090504060b0a030507090605040207020603071b051c1209020d020907050c06090a060c02071d07052104150926040506040605070b010501080118050702030c010e1f0b0d080304 81
    0x5c6d0002d11488581d81c0700b216690402039040103149040e00c103150042c00255003d610300b0440c0c1c3d000500300d1000070018010310582404820980051524010100c0d0f880000c03584901400603000c103020703201c1010840020050110b05841400e64091200c2c0594060403032842c0310001d0b400c00820000007444030040090900649881e82010804c80340a1b40740e001c003903d250062424040107684281b0541d4055600c00001040384003605100308094aa0042a143c1a6142c42104481506c2604032501c0d44804a500003103100125902150056106e203141c800240f444100d04070a0302c04441002e07124280c10703800086c0d03040001c45042e00c00714400702c03214034003038907000040c086401c20b8000f800001c0010680804121941c40040e01406090801d041e06600d00b88003840d920501200322007405480c1c01c007152005008205541c00006624001d00440c3d035862607156481e403401402e05009445d0513000041c120040c481c4001c102000703009a0031118598403401041e9001400846680305 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 884102805 1250 884101555 884101571
    0x909060f011e03150b09030c0d080a051809070f020d0201111b0312010f06110307020a050607020f030f0d14030c030115051c0b12010506090a09020a030f06060e091609050406 76
    0x4d8010003020180c15500980c9803284c180740d0525140c582d900c00c2c4036000709014140740b808501c00100f40c81100b0031514000d5603c020300c4c14010b810ba00106e00c80d5810440c5031007840790b0f05401c1032940741482915400c803121051003800c224240c407010581400c1c00b10341000000f040650100c501c0500410040403246001079421541ca031010003640622b030506020350050001c40c0d44100c0ba444000d119800031400c2040c81d80008140d0030680c030410b031245500082040454860a9102941030402001d8580e0070030300c000c00300d44501d0049061b8001038010001402c0d20780051081e60b0141c10000b40640c2507071308222031005928040150300c2c0c00d1210500c02d4024a10600c001040035107030070100070402c040242d00f0f10000528840d181e00480e4108010403016440d1108000c0e4041c000c80808582c221950010924140643d00302801800e4060925014440d403900b0582c101c0308150401c2106070780d03c860a075116589252686074503503210b6010002000c4a0300722075003081c00380c000007450f44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 884104055 1250 884102805 884102831
    0x50d0206070f0605060118140607110d080301210b01030201050307050c0d1d1c06050a1808090316080d180b030a0b030f070308040b0307110a080909060f011e03 70
    0x14811000440b6035684410401201c0d587c4080c0c0c038526a500c00300846a604d003092481d420080c1d5280c5c001e40140030200301c0405000301e01854244211000c4d10f000d010b036076a030a15202e1a4000d01440a407101c26040d803443c403622400789001d000381c000c01083c040e64216401100d00e40e10140c034000400c44144040f0b0244c4106101e0901210019102d82d0b60064049595841d00c2d2840c411092103911403c03c00642e081c1001c006c00d140941c0b1078400182ca41d20030800d10000d2080400f1104d010800541c03500402201400030310556070210100c0b222808004004d001c00780c594080e50000d41c0040b0803401c0664040c0c0108100d680307048011840c6151a21004007464000300d6060a0b980c0e25182012a542801d20100403440541000751003200e04644a801380b510440c81000100a030002c005003007517100c0c0111000e01c8899209480781036000f4101022150441c25010307200b110030300c0100b00ba03490300c0c0045013100001a142c1c051111405031001c1413131070240302e05805040d01d42100807001c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 884105305 1250 884104055 884104073
    0x204020318070906030c06051c0504051e15090a030f050304031b0326010f23030a031812111314090d020115060c080c10021201080c010f0504050d020607 67
    0x5414010f00001e0032902c1c6040c901c0808801c0c3d40b00308180242000266092060b000c0c20201c0034408080100365520389103082450702041c121010100c1d06d060001c41c0c44030102051481da540c181040002154440d4038020341c80c1c03800002c004021403500b50804036105c3c026030155600c20300a04020a100170180c0c103254038040102003c400140c00800340d0300c0e44514420000b9800444a02442c070190306081180344084010302840113400204120448100c011641c20780440d5009020b8941e107140ba0f103406421000030b014524640000542e01198000e140508801641e41040040b601c00341d05d9414010040004c1419120441d220030140d400c807511542424001c0300c025000344081003203a030000382140c121340101120001014803c108031a44103260130082078100c0d018a0b42c4054108481d803a03c0b5980104115030740c0013043d048030ba10b4401d11810304030384845042d2070b5110b00850045818130055440000400c5d0b083c4024065410a54150484507202900b160b203400d819489900c1c803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 884106555 1250 884105305 884105309
    0xa09050603060703050f0c0f1e0a0909090b060d051006170d1e051c0f0c1d0d1b05090a1a01020604050607080c07020415140604030807020402031807 65
    0x1519001800210708040094030350200d02c501e01000181441c0c840d1400c620300140004209000110b07054039000554002c48411000c80010450f040b403541124070410380140310540045105580009081076031401090845580102c1100442c4c1e111406c0181d00c4980d501d007a141c0784a045044100b443e01c0744200c0d03024090000d900c135680e010604416241030b6110003000e041140b1902e000c150310359140d100034401c4481c0d0419a403142d5a51150307181d0103d188411b80b08150800390059420340e10b5034041030180031a5510041250600590911a6041080040d810272101100304000c20394090024107400341c080004468039030b03110300080440d0f805403130100d90181e9800301b0000d0003590b0800400e0213802800906944e1419407103042d00c51100800b25030038040b803000016903c2c41d2003011145016401402081018000250304150740558050120190703c5038005800d980b8141e81600c0460350310003541482c12185900380b00107508041c0c003107070b80c02906c03149110085c0020720690700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 884107805 1250 884106555 884106569
    0x17030f0306370f09020403031d06070506010f08060703050f13080d062402070509180109080301230a0b0f090604090207050f120313030f11071e1e1e050a 67
    0x20b5070800f41071641d5400d0130750044c0c210a104100400000350419a5041004840d00b002d10900c00303000b011402511901c08003e025000c0c0c0340001c15000203a080030810b07502008203c815a07a194130041d0211282614580301c0300180700001003c601c07403030840d41d12851141c8a814100410f207000d13a41500c007c0e4011081803501c1488181520394000c14000b004001c2d44014001d0305e1401c0042081606c0252848140b1174200b03240e282c0f00482500140d801365407040307a0b03da80e0341e540c40081c25440c00007581490780b501054841051868002c040c4400d6560035041140b40c040550000e83c2294020450346400c08018400040c05850920241507414080c07000b41c035902c0b000c44015400c0a00098030400f21200500c00d0041040940e4646078400c0d034141400c6021200060042d90703d1351901e110781110344200b400106000c50f0a90b4010000303a8400f00c40800951288042525801c4854589444a07841d00f0200700c0800c04008624603140d800107149540c3d034442000c19200021900608 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 884109055 1250 884107805 884107909
    0x9140d02030a060f022d03071d060304030f1106100b0c0c0607050c0907030c120c0e190501030e060c120c040801020c070312050717210a0617030f0306 66
    0x400c0d451b85580340c4462203050400000448039002d056000365002c044d05c0035040042140c9000000d6542401401c0b8240b00186000e840b840c1900d801411048001c020728006041e000035032001000c0029110300501d20041544501424405410746d5500909031030743d0303240f02e00f12500c0201c2d10751200502d5202c0c050009810030300a030340203015030351101505080803d40b03442845009284c7c480048214800491408520810258011120041c55000c1c29038084810151403481030140c01d424021a2000c0c0ca0612111828290f019110b0004844281c94030604206012a60302c2d85426507500420b8000040d0903d07840e19103c2c0e003203810085600d407850b40005810703c00e006d110a010588444280341c01c03484c00c01141d0704d10181850348501d15442c440c001c1080c030961700c1c80581c044904043c0c0b10318250903141843c0407401070883e512070080c10240303103008610041c1000c000c0b158170801c1d10319181d25503100ca03420b01203403494074190700d800c0d54084065155091000a0103941c82c0b04d041c0812 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 884110305 1250 884109055 884109067
    0x160507060207060908060718090c20010902130c0c0c090501030510020316080a020d0e031c0c020312060112051501080c0408070909080405220c09140d02030a060f02 72
    0x6881c0c042d05801c868103001841008128a150010b000d6a1001107031034112181d4610001d00c1c0c1c018916071704000051414151403240f041c3e4490190102c0c0c2c18a0111901a0340800d1102400c0355511750340a90080c0500c04031401b0001c042d0410101e0000d1440d240106100380d454040c142c04298002c5492103445000400510904016906072945608421841d50400e0f000c0390b0416000d1400b10b000340075650f030002e2401e000ee507041e1503040c440d5a1060200300d030003c0d10285c0360f034428108d0287c0d04543d01089801c4c0d440d00c2c03081070381c00207030f0350001c529112100000d01c681c403400501881c1000241181120369007402c0c05014040c5680c100c94421100010b800507080c004001c0030040c050405010400810380d0025070f90f03040310b0004000241d2130105040404031413042d40c11080c0c224010100401c00d0181d607281803280791301e24610070080c406040301c00301d452034003d100c0ca440200e90711503c0506407a01c4580060070710301c010700305c1781600e102c1c2d0303507601c141d035101082000c0c207503804503803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 884111555 1250 884110305 884110307
    0x503040b011517041121060a060e04080c1f06031e0b01091a0613051e0619020f0a0b0601091a22090908040f0e0417030a0216050706 58
    0x21405400700c8401080c1180e48682c0081032a8101c41402000340c02c03001c08103080c007851100c002407011001d044030304042400170070740000c00451060800301d40311340d60010302414054400c0c0e0059400310b40144056403980e1700c410089404c18407034280316000e03448040072001103151180d001051025804034100703141d030a0450f10844d424181009000c8054031410000300c0c3c81c0340284c151041c1e01000101c00e1750581d40392001c108007140d525000310b00082d44061210840801e20211038084642c1220500c404030081030b020540503100350801010300500340e11001403203040c131801d01244111210039501e04c0805240103621901500c500c52100248109943c1c000d4058000c0c0a0300c01e84804d00d0702d1601c19000300740c4201c1c1c2c5421100845080484c030b1000540c84520b0042c2080c500a01042c1c03413504088035150f00030301c2544c2d4800b40c04ca00c00124590f8400a507031044c5d40140040040031115080800d03180d1005018118082e801c000c044c443d4103004820f40c1c6120b00940040c8215070a01d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 884112805 1250 884111555 884111573
    0x3110f030a05160203121609080312180712030806060f16020301050c1c0513081b0606010c03050a08061201020a0305011a16111f020f070f06021905030c01020a050304 73
    0x1003c0c01190000c1012091840031104855041040e074451000c00407007003401110b44034050342000d202d900000545c0602c0401c00107100780940040c000080210450982c169500c180f688190109015010345100229018451344d65100c00c01400d2686040d400720000b445c150300401b0402c0100c2e00b00c05106d0150b00b02446055800451216228540f0b8591111401000030303800b00001519111000581840039040885200c0b40e846820240c40700780c0041508010140b20103140458031404001850540c85158040031064041d160a46465078824044544210090110750028a01c80c0364144140e000d1006080c3c6014075a80013403294100610403100207040642d0401560043c0180a80303800400c0e04c41d1051984540e680e03c5a914400104007151440305e00b116400c50040c0003082c00580110302987e030040030340d0548078103035182d9000c2840c8146500410006030320000403c04801294100080203d004004683c10201781458003401da80c002145c0e00300090001c418007080000c200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 884114055 1250 884112805 884112841
    0x70f0e0a1d03121f03141908040e070c0c18110a17060a03020901050d060b10030c0e190504020c0102070203060705120f060303180120070f0e130303110f030a05 70
    0x2185100301c0c02e12030740d41051040443e00029180c1c0d40c0344840d00041d50401c100290207c1600f240707520385d1001070300f0149020b801500c02d03c1c80b011841c0c8001071a861042d0451124a03502c10003240e602804c141c1c40800c146d040240759010a552104107801454103080a000810f04995400d132282c507008141d224070b14005000c4c070340a00d0303c1c081d0070300059071003543d107a0544030156143c0c030400c089410150b000c1e06250414941112480441900f0240d0607001203200b03400d246c82b14542400389605200140202c0200010450036100381030001c0e242c0380e0010050550640c00150900506070002800c045c030664111011420000303440b4604140901d590354081d0b0a503e0021192070a41d001c240c0340c0c0300d42c02c108a00c0f135416004072125603002c0c1043d40071541031407100a200c0300300b070800035503a1100c50180d8103601c01848000500341002030000c1d4890100451340491851450b54241c0180c4040d000411600c28244210000c04451801440c41010352070710105060a01d9103035541884007038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 884115305 1250 884114055 884114071
    0x903190b07020712050a06020a021207060902180618060111010204090c080c040f05060f04150c0201020c040b01020705062b051009090218180304080618070f0e0a1d0312 74
    0x11001d51320124102050700c401d240c3e0002c0c00541e4490041d1012810b019001c1d0b0011540c1d500862543c007804050b501c184141d62003510294601441c0c150708982c0c0c240700300c030883c1c0c0c02f501071458582408840e61120390808410705144410298510886003680c005422142c1051380d28440e4051050740000610f40081607411003914040c00c1100c00301c0c00c07a006009885c0180d000180b01d454000ca642c040700d000700416109007410044480000b002500320b202d00740d0052203500d6810940f0310b40b500c14034542d160160010040725241c6024000d0035002180035014a501a801303491088001400c810141d2400703002c0054903207084040c0c02c7c1403142c660895001c56180003a005c0c01038036040800c0c40960302996804030309a403440048000059014001d68031800085800a0b0017600002c1e8140528045560115511400380e03086942d2082e604c03c800507250811004c0000064284400f0380000d0710a00104111881512149080440520b030211a0b48001100308400b441042103071380041e88 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 884116555 1250 884115305 884115329
    0x1020f191e03022e06061101050709050a0e060315040c0e0709030c0e100f0b0901121404030c0c0509070c26040b1c05040b0103140601080a06020903190b070207 70
    0x16880084d40d0b00c00300c400d40804001213203010108600c4910410922a00324007084c49880d0311b4100091108416140320550741d820b00380030505690180388a6010368030050f042c4040300749040c504010300070f000703001190580104a04071508400000107948030b03c0c06905014916480c00d441400701c810000c1200c0c00708400c6940500c006000c8030412000c498901b2900045a2100900b0010520303075a40008407643c0342c10800646040c40b24041d2503ca107090301e07031351000c888121a140a440214402426441d0440300160019000d43c84c0a13400754080c82c8141c2a244e15503010608501066445101007800010700e44200b100c11a00000001001c0080c05075658207060380340c05034062401452203070240070032045101a80364481e000c04006880381800241000c4c00e003050411804c1c00140c4201c50f20007010700c0c100b0350010b4914101d82c0b600000f80b8000605443e418000d40111a02e25454000c0b22140761450040007a1280700340c0c01480c2c0741400b0304080340c010f0719060b20b543c045900045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 884117805 1250 884116555 884116613
    0x50907110604031d10020708010b06090d0204200a09050405090a020d03350601020c06120105060f0415080a0b040b01081f12210512130201020f19 64
    0x31001c149940c0065050500c2e88402d610742050040c0249525400c03508102207840e1040d0490f070010b0100304440503640200211006001400034a1140303540068110060b805060018205640000070080e022121002640d00590410510b6800303210070310700040d01c185042c042440c0034072460b904080500010100440140d010440f001c060303000290034400300480480c030524102d2913031010a0181c074030142c1101440382048182c100280c41c3d140c0144221019a4138600b0507004a808410f076002d1041c0507a80ba00040198a42c000302c1c8074010040144400290040415545152005503445082e010300d00254a2000c1b1010310314214412402e101900800340d8002c080682c0005031019504010a4004c4843e206400c0f503503c0100f00258200e2880c0c140700c1190501c02000304814040c02c1915004181100c2501031100c030380100704141e40200c1d1400804440401c202803040c015100c07101102c40095007002c400c145222500d07003000301c00f5400c0116007600c0200442181d40f101a281c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 884119055 1250 884117805 884117837
    0x126011e03120f20070305070b0a0909020f0f160b090105070c0204050a06150207030312050712020a020a150605091b0f07050a121d0a0303051c02160c050907 69
    0x412044800d800c3c0310620300c00c4040b051058516101c4030807110501000303920300010003039861490384020f50f91b40c0542800800e1042080301103034807410b031594400101071300304500072000750302c030000790741e44103108100194010740c0b402e0250000c050724805900d6401c92031704104041d24401408801395034500b13810845001d8000c9070101d07002d0303015a0001290344d2221155401050182c015400d0502051080e4000550008007901500d100307944021a003040c1c24148429a03105542103408200b8410216038481c1169020b402d080546104540c0341014644501e2100714941d1040c0350825250300d42030040d400c1070540c2a40110003204120b4034280000301c030100d81d00031950340703281c0e20320002001e00c1440401c000d500306454114840840040c0e640e40042c045040802c9232000803071f040300d501812444d28403002e04c00c80360952506441c010300e100c030403a04c03215030255408100b5402c7c000711641c01031104120013458401e10520515500700010005140c1d80149400304001e40d45000e920f2032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 884120305 1250 884119055 884119073
    0xe070602030a0c030e040513170703080601050a0314090105150303040e040f0c030618020f01110a02090a0212040813080303070c17042706051008040b060126011e03 72
    0xb01c103862070b24602c410841d2138200c441c0c4001500f580e034000c0c01c0a0920006d40c1040300110601407094a4044449004400c21705941c080d80c0000340110304084002682e55004400414060500b441d00084c02e801c50302040c540c2d60b1060342c01c0040d9030f640f4010040ea1041ca000200d00d002c508400840c201403901e11400c00c072500040008158196410030b480070000c800490030042c5030712031030a118800809524859140e440345043e4071502d0103403d58009540220002d413900030060010301000c038000e40a200c0d00003000f0342100380c240c2e420412084003c0d80040c0144c000c612030101c05642d81503d5414607541245c517008030410750020010b1008681c0c10480c440005580a0120f80c101c20034035600a143d402641d0145060302203900007203003550030f500c1c808590810382c2c2d0400c1059980720000d10081c0004407203000041040c6d68089004502e108100d56800241450a05440100e203c0a2043c0400d0350401d10312416a150040c0011880307048070741c40703420030b000c024680a49141c0302c03039180c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 884121555 1250 884120305 884120317
    0x2060d180c0e010f0e01210f0b040317011202280308030108011d0d0e040f05070e0907260406110c0303090712080f0a0e190302150306180c0403020d150e07060203 71
    0x190b421f8201542441e00b1940d034006141c03c481c02205202c40341c10714250380101110128001880d0f5111901ca0903182d4000906039101d1b000800e11034030050b42800609581130710054006215889215007152002203c00040c500c0794000a890b03502d040304950944070144094004040c1c0405001ca02c0070340014100f030642c3c000d00d040e401222080c00810002c1025020f10251241407004211030320b038105203c4142c40300e0988902c01580d03105c1c1411500354117a100c0e6075074512b100702c6809003400300e000440c40d0414001c240000301c004001d12040030960203146403202540004c03040004040040c45588003c0541241c0a880c0c400340d59541070341840340500d29841500040380c50004076200c0d003238244541d070000d410f0b64055400341182101101e55840100c1c0719050380e011140759030004005490207400040c011000b2418400e248801c0358200504092802409010020140c0d4401c408101001c0c02020402e011303030b1408a03410161400000007005560250030100712080c0e0020403290 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 884122805 1250 884121555 884121569
    0x7080a2c030f15040318090f0e10090203070612020409050403080709061701030b0403030b040509030d0b0301090206090402070807061103060f100f030507090f15180b0702060d180c0e010f0e01 84
    0x1b20703d07400700010203d0102c294200400b564a00300780411034620070ba004402001c00501200d00380881082250183c0f01d0041000750550400c0074204112409000d5038241d108000d503000d8107258503404041c046400c2201c0c29030000e0440b01c14010309a0300130202e98050411443c00c1000c41e22000b2082c1c06004040c031000301b40342070100000b4241440f17075101d503848a00050081c884e0b070416552041e52608001d60b5007805900e0404c2400b02d07450140f261019040c0d0107000603003054161000c100003900001410344a60b04c0400100c400602c0d10310940204100d002c11310354490800409200700d201d2042c84540c0a006070440c0b100c0300a82011601184c1c50503443c0109807075a0383c81040303940101c02d46c0420710004400c40041001c200000030314246c2c040d95600c083c200800040801808089845424928101080550b025040c42401012400070f49030001c501c440e2221000d041c480c1180100350b588919840d000d00116000b05030941c01480501a5007000350f00700f40d04448108410300c5050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 884124055 1250 884122805 884122817
    0x210301060e060a17270d0e1009081005043e15040605120a020a2c180a360f0605011502070b0f07080a2c030f150403 51
    0xc1c811032180140d680c1204441c10802094140308522440405a005c00100412a8651807101640001441c101140916038840c01385080c2c81702480040520307801014100a9a440040303410141080155001500707242d00150701d260504001e8403203501740c0c0c074186500305150a102c250110202c0c1481c00302031884420f03085400c00e0f10000341c5400040d140c03100d01c800c020800042654000c00604a82001e1140f903901c181d4840581c0310480c40399083c03074008a03540300ca1140c4100e4107130200121396009642043c4400080344005010310600c01c0404840d041000308002d0b840095004403008600c805003141442710098284060801c10010444c09069a03050a1418040502e44c02c0ca2040d40087c030400841d6190425130610701241140d40015202c0d1074400284580d007102229421760b001203616042011a45c3c0d01007041d4404ae02d0041001a1034030b5001c860009402101d00c880e20301445055088141c6041c5800c008818149003117540003049840c3c1645054014142c3c0950305107400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 884125305 1250 884124055 884124067
    0x40201030203100315090201030e01060f171614011d06032a18031501230f03100f11030c1207020a080c010515040213050f0a0302030a05210301060e06 66
    0x483c403804201c0d88042c1035046100b002288001c015445440300314002ea030300340806000640707860f081e0b8040d4403a4011901c22940104071031600c90304840821004c200a651010014408845c220b8a05402000e4001d070201c152103959038104440e04800ea8240c4c0c0048400852040050401e0000502c0c1c5012a410f81d0200c0700c00c0780e81d181180c2c50255040421640340c0140300b400b100b000c105420120300921a80240c00c900851480e555412102940e450003840d855403070210b1080764240c3c01c032a400030703002203040b20345540c18803006030106030380400090b0103a20902810161180003034a0101c0c10301c1001804034030610700d4111580c8040b140c0035141c56458102c012454002101409003c01c0700102e1105600101900818000c0c02c2d00c034000351035564407500300000c034031803082d0820356840310f030303d0810075410300c58900e041c2d014006103920445581c035008203050030031000003129150003607046007241154100090790140902001c4071306641c144000a0f041410460f0903910824003c168 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 884126555 1250 884125305 884125321
    0x16080906072111120a1103040b0a0903090302031e06130305160203070e0108030a0e0f090402090601020c0402120919150f200a02120324030a05013e03040201030203 72
    0xf180f0a042c1c000d4144950701d15070005650032612041e140650600e0500300c0c0b40003000442d109a901942d0025450026911209601001800080000c40c107005113081e000000d40d0381880200b101c1c505d8003082c0010100003101003418000001d2545d10b0006d40845a840802c0d80001998141d50700c0300c3d240c07242c42003103000291801016901100031000c00100226400b2000b20192507400425225443c1025500c1c0400c280410f189401c0c0c4c1d0490900300003c2c0151400c081c000b0f80014060043d41c800e0066000824142c0e846191580400c811580600c1b001101c1000f1440000caa040c803400c1034400a552003d042e082c8030194011455216640b0200f43c40c80c40d4441e4118081c0c280f4101c02d085101c0482100c0c40d0058000d000142c000c8245039040a5180800c503485003081084004a1402c0c0d6030114400416864440c0d401d88615080e01c0d000170380034800d60544100003034030b00301c100b10300901610542d9000c000226180c800d0f0711514403050321100981e0b41080c1d09003805a1650ba41b4a6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 884127805 1250 884126555 884126561
    0x210020721050a180e0a180501020a1112040803030412090807090c0806090105090c0d0225170a1e110604200f091303090e160809060721 60
    0x2200c02003006038a40440710458200c00101045031403502c514940032060202640b01e0790309481021740145030783d00010120015580a200711160458200040c030355503464050890308410f81980c00300d43d40d842082403401c020003000081071001c401e805d20701030819034980c2d224080500024605407001c0c100820b080d000741140006030600908035200c0c02da580742000003038401c04004c070010902c0e04002c0f50441c01d06509244c1600c0014100d04040c0e103070300410703102582c44069010b000d15424132040045102e0441074480c2c90300d10703510300050130a0340d082036041c0d0751a80b80740b9a1618001c014040f052500840403184900709101c0c2d02500c0e01c0f0140c4142e8104541c0c8900300c1c1c19015903010001003002401c1d000b02102e402c141040c039040c5040d01440000344c00040c0c0540d0107255180003a42850466005840f0301d4800c0ca000755030503649212000300c80750b0a8500f01c422480e00190384204c00da1151506600142000c000c0c040c86c24241c101404001c4441a0b0a000c100c103040401c5c1001d80c103030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 884129055 1250 884127805 884127833
    0x309070e0115261608061c17070b040501020a110a0521070602030708010f0510020a15060302060a03090615031a09030408120301091401050105030705031012050f0c01030c02100207 79
    0x1888100700b91a00d1443d00c4d00d44e01d541840c0d074000c01d05802c04a0740e50b0814508206d66801080d095200c20a4507864580b54004003035000c40e04540c081218038002201601e5081c02030f442000050f0726450f81c4507024200a003007078950081548000022404101c00042403c0d41003c0501000254038a0000411040c41001c5000c0e094034000401d0280896110b0f0086048508101100004c591907804025015070203025542c01a84801000ca000c43c0303c21182003407400031140b000035203a560780d011926903000740000002080d664004041401201d010f401040c0c41003240c4c0c10306560031503940d00e1890300480410040340f410000000d48400f41082100c000c0c104401c00c030350041038022401689a4001d000c1c1051590400c0010881c098003035521a043e0341050311041d00795541c43d142181c003900002c000d4020800c004200107040004c1290600b50180140080c0c040c1e214800c0c1ca40f031801924080541c105850003000b40b884075404a500d00c101040f079080982c0c0d4481906144020300300038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 884130305 1250 884129055 884129117
    0xc090301060b190206090d0518040e07080f010507050f04031511130807120507060c0501020d050a020706290d0f020307060e0a1a0a120e0703080309070e0115 69
    0x900d54100300041c00502108220350780c00c60780c0031358604040d5500c1f1804107250a003c2241032080c01103868155140804a1002610005819000f0010350303140c001c8030360000c00d19420070815070542000c02c1c055181c3c004001d0170102c0c42c04c07040c54954042071145100107000540144030941c000d84003600841c1155008080c441d0711a0a000e400d65030b014601e1080d04102d1154417000644d00400a0035030f1201604500070f41880e5141207401d4800e40d5040c8000c036410355080080070b0700c0386881e2144a01460324804010f032034048501c0c100c0210317464580f04044008030750b00e000740d04083d00c04068040032000e5801c40c0001405242519095404003802941b42c000d2801c0400d40c240e12006646150a045601c0a00641c2c0d80030744030800b4403a80c45104d032a40741004000c0485016600758040805950000107620003285002d909141440e001140c440a0000030b02242040c02c0000340080d000d00f18800c1c055524003a640c80d0202d01e070400c4c010611995031103022400c41081d0b0307c50f0aa442c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 884131555 1250 884130305 884130307
    0xf06091804110f01020a0b0f040215121602150105040c030f11030402150a0c08161a240306040f050705090a140a090201020d03110915090306010b0306090c090301060b 73
    0x3a24004003039140c0442864003c501842c0220003561002030000c403032540207440c542d0562a41120b01100400040c000e0703030006030300f0700301c81d009107202c0ac0204413850143c481041c0a0a1071800042d022106810050466000020f407045000d06809440d0445008480000d9480b0341c0c00c0e01034020f024141d4480305610300e01a4031b003c0c01071001c0f0007544958401c40301c2030289034124045070040d0080e1420180001d03503401031800059040130083c5000d01480c54156030f0010f0b2a40e40f07240046448031100c5020040c0c0e4103002c1485c40410051154003851b0704130000402004011035951301340140042c0203040700d00d0494080c0039050017600090000900b424131140b500a000d00003a200c1c2a454603007141c61b403c001441c0710303e28070500100b16030582c05000c1e4074100590032070143c8040d08007411584003c0207038803841d5940c11341103910300d4401c411150315402100101414180140e0042c26510002c00c02c100f803d07503500040369413141c0040e82068440400102080c01003103580c01010758144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 884132805 1250 884131555 884131561
    0x2d01020124050f01090b0403110f090117060a0c0e1309120c0308160e040b0307080f160f05090c0706020405150301032618030c100323060f060918 64
    0x5818001c000e42c0c1e0143c800d4441e080040004403040e00892041e100260424030091001400c54641201443c070010a91060001c1e03e00c00a48034000a03400360040d009003169604031007400740a0680c1c0498070700d504008030568510f01038809190300002a104403900c82c0c4c048079620403540504020341d0810000e00c002440240050401c100001c070a0700445e0042c400103684000405038803a42454590364080002a904e00303000c00782c803172104016403600642e00081000d0b0000c100341002e00142c0030040803100080340f1880468031041e0880c0e41040c0510340c00b880981c6992003880d4001105012013039907600542800402030060b03400039580314240c2e03404030180e000850040e606881c090380c410301040001c50008058505252021442d090717042c0070403900501c0c4441c1e2468040c00c0641500c0407102010001995410b6010040010a40e0b0b0100c2181700d1202c40002c80c21150310700303241c401d981880d00000d240b21385500f040c90300c98000010400c3d4507840e2020014880f40d171110031020141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 884134055 1250 884132805 884132861
    0x501200f0f07080a020a09051810020405012006010b0912070f0f050609010e0427080304060e0f15041716030e031f05090f100203070207052d010201 65
    0xa59000c1c09034850b102c0c1c600080b480900220703607140f15a034002d01c903066032032901c2c2103007006d040c000301400900c1c080d0f9681a0394580091249480d20710085d200181d4640c100000503000b0041118403a1354900401d0040811a60004000341540d0911107116100d04101c00081c00f07014140312403800c0f500803064001142c440031000d030300541c0c0c8108400031001d612142480498011065900e00007040701c101c21100d418203902c140c2c0407401040304003032510078880f1403801e6421003100c1120030100c00810003003071202c644100f015140b0107402800c0c030741c040800f541c0c3d03076024030303030481003850480102040c10442a1540d200c4260003c401c0e060719015000103400b05012510402d5001c501c0d501c40501a0f442c004c07820400503440b90011000442040002e10002c0800404002c01403045080555401904000450408001c9000035907649000300b0000c4c1464250350006018100c019491044481c5410081034556454414584880f0300b10004070301410700108003652030a10040401450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 884135305 1250 884134055 884134063
    0x41e03030e100905190201030e030f2113080901050d0905030d14270c1c060f1a0d03032a080907030c0501050a1206090c030c020a03090501200f 63
    0x900e80800a03106146200381803182076500003c0010440d42207582c4100c2c1a4035500581d8004134018900040c03c4070161381180c1c9554016a241d403020130020448041e500d00310780d40c0f072103001c0380807064903070904250b00882110341d00c0b50401030241e8408a032440581c0d1144050b103840900c074810601c4400300b903040007526070f80900420709100381801c00c018119290020058061074a660740e44103250400010030751000c25000d01c0720a91300800d020502c203640c2e080d18035000c5c078545400220203c8800d00d0304c5012103600305100742440c0c0c03d004203c017001d150394808240d84401512039801891161600700e0092414503640015056001102c0d0406040c04002c04500c41c0b154440c90143c0d164204103654440341444003c142c2140c054042c000e55101b00e014141d904800d0408000d0702c0340f403071541001c0d10300c183c203c0c0d01c0503a524141c01079850b1303050045800540c541d0014000300e600541f0010894507003400394038107000240924544c00185480b000c041b80c402c500941e10506813040300c145d11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 884136555 1250 884135305 884135321
    0x50607050c091b1b060f1501050a12060f06020f0a08040b09060702041e0b030a0503040621111e090108220b09030c07060906080a0518010c02100501170a0209041e0303 73
    0x207103125007000a40d01075010081c043c002e541c0b07403541c03801f4081100d00449143c0c0c842010314003002405101100a0180c900424020307224601d482c002203401d0110003446d1019081c13000c062680301d56400c50105d1403680498081e03e07a00101143e4884070640425281d12504000941282c42c0458961402000c0ba0700604003514030fa03c180401c42c20081011390300c0051340c0d400303046504100700401040e4003030307085201000c0321481c000c40c10381080d841681c216a0003508554201c900028a0b401c140d040f0904820302903e1031412900340300c03035a03000a0005200404049805510b400c80d4500b480080400400042d0b00c441c00d2042e6281c03070f900c082c0c0c0b039420040000c2c0c801e00c2141408180d66001d40c0c0315005030791060740e864140e56900035200019150142501180070100d12101c0300d6440c0030300035a1784080740d0740c004020328803140401c1001c0712070590121041c041c00302a08811044041200070b03d1540403914030742907499504010b07901030b10025504020203010440d0303c0030590142c1003081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 884137805 1250 884136555 884136607
    0xd02090f030303130c05040623030c1c061508061612020d090b070e0603070827010509060703150302010c080d360f0308040507050402040f0f050607050c091b 69
    0x6911b44d883d030610040da41c542c0a0400e10341590781c172200c48200b003405001d5940794014203d0300480310700808607451111800003148004c0c000382c10300d030900c0060700071820600030107141d51440754908400723a40c6400000d40070071010881440001140d0b40f02d0841500c408249140841d9038624020018006021546003211100351240000352068050b2020848c3d003c405002d15103542d0b0707040c20407505080010300c01d08030100380f803070380f011b00c4080c01400044072035001d80001940d0820b4080c0d2032411000500c00c07c20142082c2c10400c100c22454403404c05c82c2d50a09202c038200030a403800e04c0841c021841c0050006280c08080202503d80c18030040300280340200c0c0d420b40704403e4100b500f40200c584406007144194800110020384036a000701c2d0301500540c15603000c19102c50016003aa84603601c107091010106905000c6001004d4014004207422540103140040e940d607000d8590031003030700311441030340c40c94000303a034112a107840804c421003d01c40325545c4070f050078150320020101c000826 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 884139055 1250 884137805 884137823
    0xf0906090b0a030314070804030308183d05090a0309063f0507050c0706320f0c06070f0c050c10050c010e0606011803080d02090f03030313 61
    0x952000c14420320545080281c03003040c01c02c1c1151401c3c1c40c0c00f00400c0005800060401c21180814980390140000d98402c3d82c03445646c1c20105040c0c2482084030101e4170040d00120301041c1140c81e602030170202d008800c49003404402080c070703c04d0340040760006c0001026080c5410001b840030041140c20781940300e502c44c00d0120342c5609089884c001c030a00c03c40f030521060084003280c0e001141c00480603081c0200950741d51080300305600241c41c0c5c15200d11011800c08105c5c0c0c00c201600f4000701000c0d280510340b01441c0c8041000707904900d009520710180108005c00a0131a540c50350f4101c500c0c8a6085610320350b1030320403000d4150380c1e0700201c6810740080c400411802c80c0c0c40c4603945100216070404000e02e03070160500200844148503003003080c00e001080101d001090402e005005c0c49004880140206107007500014054100040074040c82800c480c006000051040b0b00383e55845581100050712039003203e000c28446d501c40300c1050781c1071101104104a80d003d001c040803035035115400d11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 884140305 1250 884139055 884139059
    0xf0f0f010f0203091c06140907030312322a0304260403050d05042607092d0c02070e042303030702010c0207081005060a03061407020d0206130f0c030506010f0906 71
    0x12840030302d05540b01d005d0750704240020004248201001c840b000c194020001d03400c42034010310412651000c0da45580c01c81c021142c124100d4a544000342d01603440400000111093b400348a00b50a0700c0304640c40101c0b011001c142404200251910b0f140e00c041c2117840f1110380401203c2d6150454803086606214080000c040a4492015207013140d000c5d8254030131030751800c0c020050000d0007484040441c03051000009030518dc602505a1440051004240251801001ea68100c55608410703c1d05400d0803608000c49500003110801ca4031103101030882c03a2900e10300b40349040e1403200c0f02c1c100c00f80b101070040740c2224040000e600840300da8008010701c03030707902c0426611108079126000076600500700c3c418000c01c554101580c4404002e0040406070b807a503980c141191003d905401c04c201e1003400b0480100d404000c0020568010b00007003401d4a0710b8103102c42c000c2c0517058000d000814850888c8208214165104061a8001c00342c6a903503849500342201c43c00c1c54130400309000c2c249900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 884141555 1250 884140305 884140331
    0x4050405100b0a0b030402100e030111130b04030b01030b090703120302032205070b0a050d0c020a1a0c071203090f063207140706050a06050f0f0f010f0203091c06 71
    0x280300700c0e06941c04c2c4a0a580c1d4a8082104040b4130981c80001c0c440c103654120400d6900384900201c059103000156251058404621000110f680210741a010704120074000314402c5050581102c0e48121014200d640c1c8103a0030703060500507480141101c40d030814013240580c054028511800086104d0120100302504409100192080282c29500f1075041071004c1c4600344014114007450342059441c20b100803540f40200e6803000c042ca8010780044111204000d01c0045990000bd003114020b801810080302c100304901c0b0f85000140482c0501d040c1c030442a0182e0000b04000350001803c0c155004103082c0b22018103120030354400030820101852100c240140c1d01289101880f00015403a43c1c0d500e03a01355108039040c022800070107401c2c001d41c0000b82950158078455540680042206451309081c0502c0305001c04842d88510320b400c0740c0d404651142c501800401c02d0901c1c0c0250098901c181c1a811807280548a40d0401c030f40f00c4040c83c03032301d1074020080c2c8907a1041c00200403900c0c0d000c070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 884142805 1250 884141555 884141569
    0xf091a070e040b0a0f0305031812030a03020304020d140d110a0c030209040c121421221a03160806090106080405010f0e2103010b0a08090c04050405100b 67
    0x4050001c140c9061000940741000d6000d00d0f18550003404500007181c0721440c0d00c140c07030200c0d40104c941e91300000c1d100e550380c8008040d040032804140e407040b43c07005140b1400d0b51030f401000f40150406a002c000a025035079503015004009030060900c01441c05000c5840d80c4588a1903409000304107004043d040100d40090100b2003143c010003050441401e5a00b00105070700c020b40140c6403409401c2d004241c1060041500a00c1480b420030714100305500520b190412801089146400b542c030703414178070307401960310445042130740080035031034880d4498050f8400c0701540c3c4c102c480e040254044004200503070800550080c5154040d400407034100b0441218070710001c860b02c503048070801c0010003800d4001c000042d042031085c400460b0441c1d002108800300c03016038a484020350f1145007a124802e40c4003000c10a1800d414400c0c0d45150b042a01d80e24007482264012000c1001d41700001d044c0550501c10308034a440014014001410b081c2406035481c0d0404410719040792608481100a1174052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 884144055 1250 884142805 884142811
    0x504050403260c07150212071d01080f07030f09120c03020127030c0510090c03021801030809150409141801021306080402040f09080a03150b19120f091a 67
    0x103050f42d407405032150b8801854800c00344c060156281c080c0710000703078180c2036021144a00002d60b14a401d40c1c40d054140d0714203170711000c0054140441c100500800011031310269038405801c0c01c020400704086641640200f5542a010f0b1501f01d035a000c0700480740c0e00404c2c8040040c000d40c003e02c0724000d903000c50741801900c4401000c00740066814140002d0046c03200204581c004c034140c6484030f5009c1c10340c6056801c000d0007290590b08002080c400c51070602e00160804080c142007040d65030465490300203512407620740c0d0b0721851840c80d04c19000c003a40006c40f00501440f00003800f41d0003c1e1090000010010358409070111b0030300c03200241c1204148251250307080c2400304d070300042c0e00d051002c1d40c3e8903402030416a009034036060b5625100c0c3c0d49029062090b441100c0352070381c85e410350000404440e03a103d45142441606c100411615040809540e9403540380ac407119018805c103030090350242e911500038248a418408174080540301035019000d4a4003c031501d648c0300d8400c3c41c0b0400d02c0b4201b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 884145305 1250 884144055 884144071
    0x1b110307180b0a0b1909030804080102030708070c050d0e0f181510080708040206071b0503010b19050910030c0611070e07021b2b02040b010206060a031704050405040326 74
    0x10303c0580515060a42405c84c00b0881e400d06524558a030384640740790ba031090b08050b00c10381d000030900032900d511a10365540300c42503151400351070800d41e072156161088402d11301d040040c01107200101d07075550404241c010b0001071230f62300006000344030141050001c4407900e42c0c0800c1058022501d04242101030a4103005607a04020b9645907003041d552040060805c1c0e0700024140070003070002d080c0d00900040300c224044d880303220030328110800d425560100c400300c0c0a0752081c001e8100245c4000d0801069420840d07080e20550b481d00c4005c3c548400b41c2d480a00074007031800340042d01e20b810440a80c402e00f40102542e20180e268074074400d80600544502005074450a107840c0e9180c09038080140100e0020580350b141d42000c0c20000e0084440510440c500da5842c80d69011880c1900c130320540614280081c00c003500d041400912000f02d40d102c09400f85421905403042c944270081103402400c40100104114141814020050b820b030184034242c9070300e4580030301c03000d109a0320080c0c450307070303c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 884146555 1250 884145305 884145307
    0x130302120f0a0b0c161a011403030d09050109020303120f0115050d0903090504110a0305010e0402100c110a0b0c0f16120c18150906061b110307180b0a0b 67
    0x10658404a84400007040301440050a10550780c01845e5008031090550184496114010703051404186180040e44154201030359251860b4403902d002c010340314a9035503074100161030082401e0107409000302c480c00941c54040000d00c204d18462902206018400788080710510780e0720b0394035000c3e4441d420940301000c07503414081c2912224142e000205210b1081c80c0c00205150703658040340c1543d008607012181e081340800c1a40d416a1305100312801806d04c0b0281002c2401c0c0794021802402010441c0b41c01c02440310864404d10800c000e010321014800342a1240b100d940303030201149600884041c030b81340d00900700e80140d0106c0000e8201151a44410110410703440d0103081d81d0110603040d0101c0b00c41c0151500060180510300d00c15080d400440008a10400d05203111800700c1590307000b001c00649401c5c4280480c0d9800b0f41d201e018070003040b40e03059000c07042d410901c40c0b200304103104540c10b10580801142400a5039140c94035400e1100d018089004800c04002100740940105040c0c164 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 884147805 1250 884146555 884146573
    0x1c05030702030d0b18160e190b0f041203090302120307170a020f0f0c01031b0806130b060a110d031806023103150b0603041401020906130302120f 64
    0x2c0f440c0d001040c0d04000a014500e000e690542c0d01060440490350104800c00140391507504542080340c05503044811200c400c0052840c0e04a1003018900c0c0c050001c1002c40802c0500280c00d80404442c0a00b10040701088048414900140103061a000c22800340c0d0701c0a010107002c1c9800030550350320541c0a024140c00301c910031a48583da8104c101c0380030461091019402001c0e20900820081e00d4544001d080f144a0030000502962001c0d600f400e42d58190141126180d0740c081207041d0003400441c4c090180100c3c540484c400ba01c0e014161590000780000c11207840303074201525411582007081510b003043c58030202501142c880e10700c45101a006040e031a03001031140c3e40200000009010b2001103014400350f01c3c030b4414281c020a50610511110070300504c102000301030141182c43c0b1050005e00480c8000c2005400b01a100a09041641d89500740d10742080d01034410008010307005940750390b0340e40c00303d88039000d184c4001c0c5e000380c0a010300002d800c0317004204c0780000f05845008080b0302d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 884149055 1250 884147805 884147827
    0x90203060604110910090302190b0f0702150d05040204060b0a0e06130306060b070b090c0f0f0a0b03070c02040b030316020904140616030b0a05130b0f0a081c0503070203 74
    0x740c0d0020f50b4401040802084101d40d5074140b1140040b281c03540c0d0941d4060441c0305214820742550400b102030080c28100300504584607007191b074809541c40880340c4412051011440800740040b08040e82440804d03022542407040c3d001c11700c12402110b0078010b050359142d40704040d00c00c3c2818000080d84045d0445007a042020041c84815452414208015541c1c0c4030001115895041000d2403280003c901061050b000d40040c0c101c00810050680880c0c464000b40001081008840c0155801c155114280d42d136003100300001d0003400c000300c0e40ca240501005100d1004203104910661404c40d007030889080010030b4844015220613210952151502040100308000300100e40258003810010300354501407201c20b01581341141d6003160000000c001030240c643c2e2041242c001e0000301410803499032012034403c1036604115000400811190114606903007040015030082d84840c030010711441c000030800b6078001744d41c04458881c00e441800711418030055441800590013400f040340c2c45 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 884150305 1250 884149055 884149061
    0x1c020c0d02150705060603060a06241e031b021606030b030f014704020309011503080c060709060504140111060a050f15011e050c0a0507050a09090203060604 69
    0x16600042c03400082905644019915611850007194035802c07200501180741000c111301034100007200c2d800d001d620305006c02004407281c16a41803030b001c144000c20320b000c50300916128094441030b0b080f640c046102214050041d1580c0e08400c181460102d01d9000c0180c40494442c28800c0000d02c1100d603c0d1070140114050302c0081416a0316000d000690014890240b081e03005211060301032482695100305100303030300985080b00001c41d000032030b008036540603075070940170700603c3c1210010389948410748454010124108004483c800d0068080706101103907019100b0075045104070341659a840c041142d03410380a10441e40426003d120501112242607488212100185803201980d990034008615080c401d0b1a070040580d40c8105000c071030505110030b10b900248502c44c400c0d000360303400c000030b114410440c040c280c801110400780040c10320810450307482c0d140b92012a900c030f1030203007442c5032117000f580309203445a011440006280c0540f40070b2604110740050140c9425500c8106201c09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 884151555 1250 884150305 884150329
    0x608060a0e06010e090106120b040317060d1b05040603080301050a0f05030709112b06060504080a080c0a0506010f060e0301061401030e010b06270612040314091008091c020c 76
    0x1b03549845012036204a0b07100201c1d1a6070080402e4186410603040242003e8281c3e512b10324003007441400c018283e1114002014503640c40381e4450030502c1040b016409a112a41241e54400d09020001080c000054065416100100c80310707019165950600740d80f0440e10311403645c158004002c00c00c155140c55001d5a41144005492880d1a03a00b00780300103501d00400845900c4826180000751415440c89030102030b10349810418581400c20081698803d182c0c80010800e03580040c03130621029060103401074141d0301600b180c0c5070307503104c01c4c407001907a001d0b000e81c000103003810300203540a16050103503100326403400d44d05400d201310500045001d400010b600f0081036403280c0c40c81603035888040042c0b010031032200107046c3c0001107117100e038034084032008802d104541c00c0c0209200b414174894032940050703050501390208051044a400b241c09a0780b40c4541c0f0005428414443ca5040442207125a401600351030000c0e03a00d5101540e400321a101040044c1d009203000650b0341400055500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 884152805 1250 884151555 884151571
    0x3300e240703020d1d101a19090c02060f0f060f01051b0703380c1c0c022103040c0620100218010819050a09150608060a0e06010e 57
    0x104d07105001d0032040a45202983c3c916400520025100600006101c001540841e0a1044c000034446030390b41001001401201c034400c1c1000c0416414000d28041003c004101b400f206000702001040040d440e050115011150120792000046400642100461150b44018501c81c1580415001128107400081e2105000e0038007010074582c0110800148000390311514030a0209031404841c441c1d4418601ca100d81d16290580180090800185c011944908200741d10b40d00d42078085000c1c084014013003c0820705034601842488000c2e40414005500301100b448400d0f00351508034940c45c1c034401102d014004490f50a07040c4102d5120740340402c15071902040e6200c038050900307145800c06400c6017099203816800210f1000900c41035805420802090030210140c0c90000c1c801807080190a000e0754030146e4a00004060703000c154000c02405401809811402c50181c003490300500603401100014030402c0e0005030f007001d0a025850030f000071440500402e9280150701c0c0c0805c4001b401c0340c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 884154055 1250 884152805 884152807
    0x1b091220010528030e0106050d0f050c0a0f15090501022d0f15010e0402060a080703021b0615062514030f040f0602150c0703300e24070302 61
    0x1500c1900d1107512040c1001e90038060791038402d25010f030817601c410306000c200c1d9040110820881e0764504030b80951540003000c040034995545446410881d40c4840c46501c01c040c41d10214144e68403906110640d180881c62a41402260030141d9040903940b00e13041c0103901c120b55203000d0403d01020440004034080002c0c2d000d82804aa80d42130415a80002540d90302032142104240080c0e0201c5004001c0600204207a08046d004124a4481e582c0c0517014446640081400184650b040b034101460400c0c800903003840720015030352a840300707a90700c0c0d15a00102d08030188500c3c240d021280d901904c2d0029941074a01c2800300740002c0b5076400140c40440d6a00c82e010040441030000b89803001031560402c2d503460a2981140349080107400100440d40700000e208049180d1101c00c940122030500d45a496070f51078076044501d0401d0005070203007070507914160b0f8000314144583c2d0f495011008020300c82407020481c0c6c00c1e44c444042450003c44140c50052503040342e0707000800c40d0410141e00d405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 884155305 1250 884154055 884154067
    0x16060902030f1002280212030411060a0c0209060102012912150105120c010f1119060501060f0512060609011202031f0803130e0702010e011b0912200105 67
    0x10b030400241402c0c2e5000341340c0001d1410107003a800c03910a458200140300d44102400e1514000303645880442403080e54000002c0864280310410b4010103000c00010039013552200c4901c0300500d00074064000300e00807004240071030650346c0107001f0400040410000880f8142046a500c1806031902481e503030402600c2003070034441c84061000c0640b04d15801c584000c2949420107100300300c004103c204131250401c83c1c4002c1c0e540e900154030383c0d0106080c90003605482d141108176013412410781d4408a6803503510b10742810450300d0380107203040b240503444a4420091800003a181882003c004038661080300c400070381d00d4500640a045070031010700d8020200d90501040f48100d130f10503220200b10100f0308041600c001c00000180014144032006581000303050206422800114052824030b01034010000e42101c0c803d62040c43c03000344130302c0244241c2c1c05070040d0901c45076820003140c0011749010404510321101000800459501c5000d14404160040174140074900840301c3c981004810402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 884156555 1250 884155305 884155333
    0x409050102070605090f03031b131508011a071502031b040e091209012f01020d050105040b04020c0303040609060609050a0f0b0f030c12030706050f150102031606090203 74
    0xc0c1404901c1035a0001300343c00d111603218034145460741d43c40803903402041044400d4005005c04a4001c440e104e40a44604100a00c1c1401844a070845a038024402074452560f5600030260760488000d4400c008140561201d00b40c000d210300034002e0984007002620083d42d4019074010b41d4085641082e424418001120214003071b446684181c1c41400c81000303100e81c0031000d0100144600090926a02e480003240010340400464003d102400c9008152021611141c003424803031882d102000b19660160000404d005000a000e2107015034076009020814ac140380c0708540030b8202c43c50045045940d9030740c0d460040c02d01124210b0300e0326201c041c00146071005001d40d030302401d04d90401088020302d00d000d0004542c0318883c41403003102d00d5520154580c6020565031000c5100b9124801a41c4803140407500c0c40c42200c80c01400c241c54501044103220f003003c3ea1500030821a030180036444099001240d40340500d00c12142c400b41d080206800083d00e90303000084040c4087c055600380050011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 884157805 1250 884156555 884156557
    0x20f09221532070909020702030703061508010e030708120a02070204060b04050108100b0406050c0111030403020106061107031109041b081f2003040c03060e0309041b0804110409050102 81
    0xc40e00109014442d442c10701080041c2d24000c0c0282a074801618044000908800c414401c001c2619400503040c02507460a02040015541151050014101c2065051403203060307842203440301c0d46000403140500c40080215184550000b2034207041c8440540b103122820009810340305c1c0f041c2e00300240001038455019039001064080e02c02e03030700d441c5017030300140049000400c044001c1c060b8035400d1081e014400240e9050b070360246041500c4501d2415050300501d0762140c0c0d04900440801007004240d415000a001d847c1150798000024803003e020907640c602c0ca0000404070050015002100e09040d8486544a0f0244840c1c28420300012101d0200c0c1456421800c1c550300001c903540c0d070b2841114640300482e6840d002c20041d101a00f0440c0e60202d03810504601d01b2100017011806100300040142d01a68111102301b005541c001800d03a604d901050495000c0d5080c15030f010040c03840c880790341c00401d0864803030340d8099031680c0d40e4540c2460f00601155105075075100040206000344 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 884159055 1250 884157805 884157821
    0x190303050103030306051f050c07030b040f03200601121e030e01020f1207060c090f0603050a1d0c100504090608010608120a020d030207020f1507020f092215 69
    0x52000151941503050040c15100140c00090255a1011900c19000d0000c1140441000a032404588644070303603490304e007440c02960010309440eaa0700c0500040c440c2043c1d164641a22a888440303082650051402424158140c00c910b15003064004008050350f01c0508100b80e441180c0002410341411101c0c514024101c101341e0028400d243c034103880e542c0411000b0241c02c0900020820010001c04a81c00c500c1220002010b4503141c030017404800d40514200000703002d220480010759030310380030010020b080843d102e504075420120341c074641b40144500400ca0758a500058800c11002a0a00005000303080300300040100800c00010000300750300c1400003a0089400210303490389841d80b035a1030b0102503941c8135148241048148101500001c01000b961110b050150301c0d81c515000191200111464403a0041c2822541c0d500c940c01040041c440d0700d100301c0395814103130002024480d2901c0100c5208000209440826684290003807030101c0c8648200705104c4518080f04500081d201c0c49 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 884160305 1250 884159055 884159057
    0x90506010e1003140c0c121605030403030512010e0c162a050f190e07091a0d0516140903010f06030803070f0f050301050f060d110c0f15070806031903 66
    0xb440c2018110480401c05034101c4400361205040c00e84082c0c0603511004003200c442c080c0c10002900400c2a070230549280583e5800c90152070700d070303039036070030083c0040c0d00052104071054240703000800d10f08101c00206020343c0144a8035030405c40034118205000681d01030036651984007018910742c21110410290701071402a840c19082c17450402030154059100600718820607d0b40c101c1008622450410001c886594a44285a40390f9040985104102d44c0042d809801c440b00016003100c2e000005001007103040c10700304103d40d19040105940c003041500b000000e440c02c2002510b84101101424410600400001e4002c0510700d42c0740480c2c0c0c60740c2c8115412000070041041854000c2541466651355040401c0c0203c8901c10081c0644414040e5900c180340403940890aa00c5a070305580c411006013900300304c4894104420003084d004092a04000e21901300c009002800100700d5000340300d592554980903458120013038405503002000d1581600c19512180d003403000e11a031008030f00d402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 884161555 1250 884160305 884160311
    0x150c020d02091005030f0c06030a0b0d08040807050111030703020c01050a111e0d0503040c0614040b1b070f06050306060c1515010801060f02060403080411030109060e060a1104090506010e1003 84
    0x244c81c0a16042080500d160915608400c02108503074450307004a90b1b00a1201034000303011000c1d2000102074591021014107188008100468034060020300d0506076202601c43d00a0300311031409140e070303e02c00c410740140160400e042c00d168070350051000d801e400440303041c0101410307150442245841501c00d038402c000d6404008000c840c170380601080c40b03521001c0c9084d62441c9890303100d040c008003051044008102c440d0840402810b0404140c4010b01444190965544002602060901440540140a4003420500081042010240e40304503400386c2c54403403c41c0c1d5085c08114590b042002a098680a19800344d400b40045400d20342c46080414100080ca103c00e100040110805070489d80500201c040000030b01a0001416544194103180840c943d555034034220f00000310001c4032580541c2000802400c0102980102c800c0e40b038084200c5450380c0d00c4051560540b04240364644030b110301080140085c00c0d040e00040e9001c40306042800c3e2140b10203000c151556100100d82001941e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 884162805 1250 884161555 884161559
    0x140f01230f1c0c051f11010f090308070f26060d0602070c06080f010b070803090c1c1709210106030c030b04050c01080403051602190e01080d050301150c020d020910 72
    0x1807000203e0003526041e0307941300c801c107542d4211000030341d0100015001c0c400c002c2044036518809400c040001910303844144200261481d029043e09400c3d80ea9001141c0202c800d0140144150320002d03ca400c14490b0841d10008200c4041071808c000c0c0c8890340000312500403501082e010700050203035511841000800700e01d8004000c115030400341404402074030420040185d911700106480b1801d4008800f907a50340c640049003803501c03542c0e01c1440d40141540e0f00d2207807200b444004003000d40d8014001400700c00402101c1880c01e104c0c0b10381c4140d00c0700309852510201c00c0c06640c51406407142d00700006410340c4903211aa0320200580c0100c50000a43c810482041003d102e081c14040f07080c20040311500f002d03603000d01140030366100c0500c1d0003007281440d001e554541035110080011074081085140c1c0b20110390082400c24043e10300a4809c0903d1040400d20607801c0700d040314119454a5028a6120340881c1c129442d44030690740001548a501c026a07202d9129601640302c840740d80310458 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 884164055 1250 884162805 884162813
    0x3030503011a0403031e0302120a0f0f0216080703090801141b0c0703061e02030103210809060c0706060b0c0c100512041e15140f01230f1c 61
    0xb0078080320200300050240020000281c201e24100d0750034900244074240f165032058200d0080c01005040070040350742000740220505258400034030100301d124240b04d80c0c2c2030840840305a11a0398002100c40f901e42d182d06010912400203414603a210303140903010305a8820455082d030785900054a14030244000703100c0d8035468100449402c071440155542084900816581c0301c1500344005014aa151140c0e8000b40c1c000754144c0800e4046268110344950310303820700906580707940708103421181b1461500c00d041c60081035464461080c04000782210381c1ea00213207054030b8120361022191103481da04040f03103046111002d410600400d170b000300b5106030b0050070006100351401014051040810400c00302ea550340854aa00c2900130503403941440c510305c01501c11407409070002d0720480c601c00b00c40d020010141c100c0300400131040610201911180b00d0310389800400e00c2240500010721a4041a510042c406c81c1c81c0d081005180ba6239140314540400c000c3e0030700c1d802c40600f040c201c01c0160200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 884165305 1250 884164055 884164079
    0x2061e0903033009060f0403020309030a030e0f0d170c0c0a06020f070f080a031404050a12050609010212070c051501080a060e030a0e060322060902030c030105070e0f01021005010303050301 83
    0xa80740c3e004074811241440130b4003907110380000e0606402c4d06081c070f00080a06000f0400c440e0600c2001c0d08a4010310007070706009101c030b08200011071180c85520440440b500c8e001901c40e4030303550440d220022195288030845156400040003003001d00810840c60311664650020000500843e0041c2034040001070195040502c9500039a80069004030284840d803000188071340e1a580c9030400c2901003030000d44e0845240100e9101c03a034031656000020a0420032121400c2c0300610500441d00c1c2510b803225030341d09038051288200301942084e400181650312604060f0102400388003560b640c03407210100c3e2020820241c100a143d680034000902c1040b00070f2080c2e10300c6e00030a501460034600300b0070006090003981410742e40700c0e00011001c41c901110460400341c10024604454607440e44600d010340c0a08135118050b44a03002e40c4410725a242010b000f00b6102e01c81e80e40d90480d540c401d850402030440c071510006070445c410150602160301203442903074040c50007070f2107054481d03242220710401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 884166555 1250 884165305 884165377
    0x50a1b03090c0b13080601090e0d09270b0d080a020d0c0b070f050c0a050c12191203060b03090114130503030a050612010228090302061e090303 63
    0x20507181045941c08200e00e41400c400b07882d008010103648200a00311182c9284040c2c0110038140510800080c50b030b0b0507940001d03840030840701a82c00c064021b91341540c0d4106180b2890110081c055001813040300800c40320090940d602d00001040c1c1d000c200400c81c11034100303204440c02031000030300c0240b0755010004010311100b10700d00064071a05943c2c4820055401034081300500000780d000000c02409035040c1d410044001084400c4070340242090f036078801007518014011080e02c00b44607448000802c11029040c2000c585a40c503001556445280000c45000341c4105562900302092000c1f03890300660140300d040002065901402c19400e104503409000c01c07030701c290b1242040707002075000b00079207501599480000485030b0702e0001040701c5080706130784103c1d035500c0010710f400c020200d080c01c00c050a04201040710310030350440060b40c0700941400040d52200040c401080c0c00400b0080c150f00f80d16040385d0b6a42054610008249907030031500301c10084548150f0550181c4100151440e9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 884167805 1250 884166555 884166557
    0x4090b0f04031101660e060910090b040f0806010b040e0c0d0b060d0c0f05030613020f0403020a0f030302120f16110303041401031514130b0301050a1b 66
    0x10030460303542c03040300020b009440d001384940c0700e151290704114041e008540d078004120301d0400c038010300b6039003502c605e5103500002141c241044040c1c40045100300242d4200560240c00d032803a0400400c04c011106c2c0c91041c0d0041080a6840c0c04103a02d00441c01610050445800d80004142440300c01c03800d00b10160401d88100b50f09100401006440b80b6180e0f400c07003842c080d002e540702c1100340814041d103070f9004100d40140c00003840c00010f0307000e51b0042c00f8a003c1d90341d0351081c1c500801001c541c00d11091321401e5100c500c2e0440a072030540c4a5005000d00c0390401401450103941e54040759115440f0781c460032490a00301000c00034160148001115018039188080c5032041c04040103d850281e135002d4484103450905071020000e05620070804180020101c1e500e0726542d000c5000703600343c0a0511130000b800d01c10b4080c1c103014504c0b03031742d01654840e2011513220b4110b00d040c0304440281d80054003040d9110040e0503220b450070321840d03004440305000440c50341c0064000249100c84192000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 884169055 1250 884167805 884167811
    0x4060513091b0503040c09061520060703020a051306090503072c060d140309030c0603040c031b0f0306091e0506070e061b0706020f0a0803060f04090b0f04031101 71
    0x35860700c80c4110b205100742400d05019449803501e042c05859410785170440c0090901e40003010910380e16410000841e48019030b21030000e00385622111035441e0b02c40e0765840041d880300010500703090003500902181c0c0e09910f455802d0002851700844212007070351290010641c0044244040c2c02d00340b1038140a4140c5803210304540028100384078624402105495585100c50f02282070303030351410340c0da01d089074000005d1401c00d2000c1040795106c0c1c0c07041284510a1083d280b2440707880c10f1050a0303a12036500005151045071a540710b40284003480030504141e8103e5010100f901010a04614040d50090342d0029520103140781038040342101d0788070320030a040158405000100700181030b542c0f00501d0314208680280801c003045150181e045c0f44603071030319170810901e903030032001656404071b961f642d0850321340000b100c2203580c40d4440041c015260141c104005110350508840c00500d1041c0034100207040c0d680e42c1c90b00b1041c031109560386564400b2220500040c954030401580100305100020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 884170305 1250 884169055 884169071
    0xa05060a020307260a150b09011d13060905060406050f040209010314091b06180d0213020705010219110316110603090c1002010c02070e1509010e0103030f031404140f030406051309 79
    0x5001140900d08e042070400c000341400c003201054412241444520203481a407a800c44821144050b101500800c00981c1c54600019990300d042d0180c7c07000c80304040c0419128001c42400e02010b035200c00701060515850b0840401520312482007103100b50040d03405030034400611040c00070f00d12002e1104a104035014002d4149950990850341e2200108590350050120244042018201600c2a542142c0e20204009c4103002d419001440300e9500f5600c2407955411001080d164035100e01840c6100e0b038001d0110b00b1210750306d03194003480c0741d0190f01c09903000c1c2d030140d00044203540b0440c1e50710101e03081158003240d07506084005e80320500c0680020701c041e002c54000255505420301c035041d40341c1c480b1800b040300c40c070300d54481c02c3d001d0201914420305907864200f0743c0c03955042840100d00065020800b00390062003031088400c8052080303081622500d558541e010305c542031811400440c007402d8a11400803070100000e1004150315201c0540340c2466000c42d080001c05540100c00a904113110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 884171555 1250 884170305 884170319
    0xa060f0b04060807031d0a020310051b0307031b0e0414011a180a030c0501020d030506183d1a030a0908120f04020a05030a05060a020307260a15 63
    0x15201624840e203004501680c0314242200507106d009201c142c4481d03038400100312241d01040030300e95180254101c9402d44601000301c03048032022640c52030000c0004200705555401d00b8002c5420130914940400c031050205290151000303148281030104100980c1000982898050780034240e8055075807820a601d4420b100402903881d0380b009054180021b05a100c28400c03c4440394106806002c0020250300da1800314840000c0b401117501501c101e40c07222003107512a001d01c0c0d1287c0000b074000d29400c134040310f00b0100510050055103900300d40754103001e0740c48240302c2c0000b00051210000c0840761043c800802a19140b40c10903082d0030600b40d12960031055660071641c00c401314101c0000d80c2c61071802c00c042503010780c600004404000301c05000f407074400c0c120b2041c001c2e0300031203a1546040d9106d04060b074454a1250090143d0030601c00200c0d040002e5001c0c3d644a55213080040048646080c1840171826407580062001000310510001950611071840801000c0d04455152814001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 884172661 1106 884171555 884171557
    0x1609020d1503031b0c0506130e09031303170f070302070503060a02070b070c1e06050114060c0a0b131509060b030303010b27090405060a060f0b 63
    0x240704032000ea1501c0001c412640e16450f42c0f00b40c0004940c40d803038191490b0b0001d5980303e50b108800501d64407040300414001000c4d04038180000e00b400014003003500301902c424040d0744203001080c1a6004845c0f500241c90308601074640048600c92032074000d105032543c600840c4c8002c90341e8001c0540025400058031012820f44105594a100d007401324003440c4405080d102011000c500d0301402403c082e40740f00e000e00c00341928151400c210800c183e54003981110352540d10070041254180100000c400c625046604915000d206207009541da84486009014890084041005e01d00304900e011120382e8080180c121014411003030b00d00902c40380710141c6100d4240000c1c4011403501004403811384068464a42c2401c01d000c4c400110b10340555440c40001d10316007038500c407513920701c00d61601c903603c0780000313042d04e2070081c1295040c0d458580c050320156410f0107080c03000100041c = true := by decide +kernel

theorem cover : BRFrame.Cov 883992805 884172661 := by
  have h0 := BRFrame.cov_init 883992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 883992805 ≤ n) (h2 : n < 884172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
