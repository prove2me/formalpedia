-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1913
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:01.938757+00:00
-- url     : https://prove2.me/submissions/caad9ece-fca9-426e-87d7-fdc895265b12

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 343884892 ≤ n < 344064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 343886142 1250 343884892 343884899
    0x13602040b130e1b01050408060712020f0c0606040c0e0a0b1e0a02030a1202030105010912061b020a02031504020108040b0a1b030b010206151c02060d0c09081501030201020a03030b13090804 83
    0x9210030713000b008582c10004184000d000c1108003041481c0c2000031410100f01082d16128840040d0050013030348007000703d01050b6019106004071f2594483c0c1000c6a080000408a0609841d0100140700c0070745c1281024a050204140100c01007941c0e460031003100113480c0041041641c2075010400200050b04007140c90038415401c1842e03006c3c0340181050550556040c10700003002200c072031007003084240f90042a0002e1040743e910a02c4882e4444624550b101d0b03a05002030354450790313410300304d00a208815082d020b01607014842809580d05030358014031501c5644508152400c042c10f010510390ba00c036000040340410301d50043d240034494501044c1c80301e02e103001a04101e401070a00d04009a4020100741d15550a2408000c2e2423554201100c503140303e002042240c00f41014980005283c041d103501c0460f001044501143c0c907a000325120800011030790341c60f1580c02c1c40006d0150744405107000019010f038220a03803c41002d0b141c0421020200c0e00304080d51405a4180c4101c82d00180a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 343887392 1250 343886142 343886173
    0x813030c0519290c0607030b011103070b0103030807090e1306061502120f040504060f0f0609030308070807030e03070c031104060501050f03090a080c013602040b130e 73
    0x6181d0202040c0c0b603a40d00e140140f600810703401c1250b040c28490304098003420300c00d40003084c1c901402140003229031500d400040580204100c0c0740ca1400f1940003000004112000811110555030069004010b40d20355035091340d01410150801081c01034030a8041031805208a455200700c8907014031036442102820214211041d03900b00c0d1610400d440728509204e500007900200400b45203140e0359885404040c3c400083c0655041564002c0c24241d00142c1001244074aa0079200d500c01942c1091b40d60f1401510914011720004020500d018002071600d80030b0b80310251f11505c00e0801045050030051402d0543d8401882101e050a071140c051003800745007a0500034505c4152000c2040d14100000645140034000b092407602c0000000110289800c0c00502d251a0b44050203c0c0c40d010202c0c0703d030f03000e800000303100420f50205914245640c0e0b4940d4820149505044140305512a55001d0001034101589600c0d084643d03c00503000c480e1680c843c0071060150f0601826918580c1040d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 343888642 1250 343887392 343887409
    0x618030a03050301051e03061303030e010e0a020a0b0306090c13030206070b0a0605010323150301090f1511090f04090b070507030905030c0a06111009080418050c160813030c05 77
    0x4140c0190010343c411011903c0c00948c9503049007070100803480080d45407400f1005010f95a907200c0e101c1d401c0c0f07150200e0581001804000d4140300f00d41c9900c050780c68680800190000702c6006912102e40340100c2e520003141d0008180504074510300f0074002d17441313802161196124810444240e52100c042100482c200d00c200340180600b460140074244800d01d1141c0d40c51030304003958400202050101e00a0a000c454180d440100030700280001c43c0c440c10b04403061210100152a125502d0040305c02d044003901c0f6a2808502944083d82424008000d110365442d00464041c3c11035034480c2c108010807050030a940c03140400759601c03640c500491a00812206c2c40c0e500c00341c00381d40b100e0000d1306c040d66612150425295103140150340d09900310340d46442c0040c1c010510030003e14255406d014406a00020019141000111520b0f14209000e98081794000ca52052040c403003404040201c0030145e00814209001d0481107003052164504040e41d01c17441d0b801226000b100580400644c10140c41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 343889892 1250 343888642 343888669
    0x303120117010c02100b0f030d0804050d080108070306110c060408030117060c09040504020a170715050c0d03050c210411090702060109050711030d0605010e0a0506090618030a0305030105 82
    0x2804050b0080c3c001940e68054500c0041c0c8840e212002c50049032944184503085d0b29009049406007500c200700035209072b41c2981c0940c0c03e40680619000903600410965040300d244200800c0c51740d14540301c40006003071148140d4000d200420660040700010801c80340070368010441c941c2e503545000035032115040c900c07030350403da90012010809401249415900701190a99010906549520001d0382600261700250700603030403041c80115440e4002031140c04e850806d8210040414a0541a83d6500442c00d1450a56200c0051242c0b4144690020f5412910718805103003040c4407644c000303400c41d581060140380c110036841040280980c0d042040b014510a541ba4111800c24180c002d4482ea414000c0c2028151580c0204800720700c02c0d5901480d207092001600e840305040d10038080541100e02c2018000780c2d511b0480c2d00e040c948441000200c80005020070315240d1144140003032a044003800b11030144c0240070030081a1014810b0328006840b940e0341f0f80c1c1c1c0e1760401080050a201144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 343891142 1250 343889892 343889939
    0xc16050a03050714030c03030d020c010c08040b06010f050f0703171b04140d020d06140114060d05100906030c1809121b0501020a0c0c080d020d1202070203031201 71
    0x1a041002c0742011440700280c135611901e0100e22000300340420300d04003c0e180315503014440099070007445101940503002c40c4210b04028001c0c8800b40c1002c07500d00b1810350300503000d80e982c2d501245256028100b0324411202d1820305a0804407203c00c0700c052504080b00903404555910303000400703c041ca420040d4080d44800b005004101000f1071412140154011249092560300501c9196602d1044881c0042d50051070b4009020b52460440d01800b170008090301c500c0040c3c0000b00705402d40c42c0c0506030f1a84080c10340e5040c518074500620103063301074106c085910780620701140c150b01901550000d14040c400502c2c07070b00c0c980300c402103000401c1c800e28100c6038504085c240c009480c60341084071809a91600300856140c040e40325008508210006000c3d600c00240d11031695004100c10400c0b40c0125400d001c107540d9259525194065004000c0040c0c00c40781e5444040e90182c0103035281402c084400606000d426030100740756078010b032001030242010200401407039402940295000c1e8064 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 343892392 1250 343891142 343891159
    0x4051e010b0310030f06020f031503062a0a0315080303040b01080a120c110d06061a0705070306090c12080405090901140f15060316110f0d230c1605 65
    0x3010030f80d450034000103040c03c00181c2c0000900c0141d8043c0e4212802045080307641c0c1c1130501c419010103c0b1030302002d01a0181c1000950400c0c441c4c60304244841107112007245404c1c483c210f01c40702d40d0002c800b0206041e520010000791440c094503001c0a032007c1002182c7d2814075080c040b10145c1e050340b1212881d8041074100000a0b81500c7c0b1000111680c01c15540c51091481d150300341c2100002c3c055009040180710406020194001c4011551006805580c2410b0680d80704c2a45c41021005003160303108000402c00154113034000b01c0c0850080f00062441c80d114070402c203502c140440c0030f4604003400304050110345051400523400110180013003001013000d004400b850342d001040b00181c440468001001d40c0d020790000001a0401840c2030354a2401c03440a803290744034894403034001581030500d04140400010320003a8404220b008140300541504201d4019011101d00c44a450540f0184601e1a403413001404080802c0800b5110300341d52003002e03000c070307014a90107a4851f0060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 343893642 1250 343892392 343892401
    0x604320a060510120510050105010207260a081306020c0d02090a0b0102010609020d0f0c0329210a0201110718090602090a0305160b090108060f04090204051e010b03 72
    0x3840300100c581c0000c01081994603281035040706041c69100080005141c14810f0802201140c1d030303000540310680401840c1d032101c004a980f084980034026483d110340c032440f041e800d00002e071428040b00c0c0804079544c001360360382c502d407640d04601d51111440940400510150740c0502481c62102e400f03440c0c080c11000540c002618481c0c010782001b4102d580d0764000a4107034400e4000d50003608000c1402d55840705164403d07002031500c0a0340e160540e15041c24120380910a020f6010009469960500c60340c490301268002110001d5141d036104468850400344440e40c0040710356000004000b810b24580c0d10300015000c002180030000136a0000d400504c850008075003800050716410200003801c010070b103802e1000b07208402c2c1942c0e01050f040d000004014001808924016207140d21149903607542202c403c86020b9025080e012416100003d200ca040140c6c0b5284000401400030501071040e80100d07017201c1090b145041800ca10a03501c4007141c0d25101b1890041c40c5019400b85149031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 343894892 1250 343893642 343893743
    0x10908040e1504091208100e090708060a091a09070f1202031b031c020a020d0506070f05040501020601120201030f051602010b0108040f1704081006090b01020c0102060f0a06080604 79
    0x10901c0a200e14000481c0840d031f50101910007501e00c1140c005264103010b1069503540007607100e24542c91040c0b60000300701040303d000344900c1e2070340048101e034503021580003800c41e586c0c000c1026055101d45903000030b20192003109000184119a2254030340c06035030061604010a8030783c0348203c00640180860f064900154401c450180c002070000e840c420f051049013000c036010b00c00303907003c0781c00c401a20078804c0c04200e01e0301559140d110708040443d2042c09840034000c0b84201c6016800680041001004800d28403140030310500d00061005071180c840e40445005070303420300790124810b01c60101d00f0b809202d00c24140c039090a103c00949050380d03074102c0c0003420807001003008002104200504a20300260b401070051407050b24070360503070180858000c3c8541c0c4500034030b01c0d0412000f55140d50003c10300c0300d08848180d0140c000c581d40e0480c827208641700035089072800790383c9080000d00f030001031060314043c0d4800c8007002d03244005080e6201e0303040b00d40780400d11806030847c4400300d03552 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 343896142 1250 343894892 343894913
    0x4060b10210c21020c06010f060504090b12011401141206011403030c03070501090b0109060b03061e03010903030203040b060604151412011403010e0c060a0c05010908040e150409 78
    0x140d070007080400c03070900c084a80f02c098040c000041c00c28040e4541c40244503401500000654004550b1680c0e640d032100420100c40d071041002103031080109110041c401c0d00b00700c0324054080d0603a4500382100980500312021701c0309200320009880014802e044180a1040201c2412201c840b2003504400c1038a850741030602c0b072000c91501e450340c881c100340c80070300c280d590b04880309066a440e92070a04129000e840e03ca4030440c0d41800078000404c00c403031a480360300c0c259400040f51500f169540c0091142d01005165070320740390300904d59142c42c555401d02400e014540f003a80e0150303d1341070525242c104810041c24080c411074042c0014000034080c4046842c080d2201c0c5080b09140c0450702d004541c610402c080108095045000071810410b0800d00c28144502a402044404030103c09543c44040710700301a58008010810071003054032400100d650300d4010400010300300100d82d150900c0380c1c410f030310600c41140484100501d802842000d0105403205036011301007101725559048081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 343897392 1250 343896142 343896197
    0x606010210020706090f21170a0506030f0313050112020702010f141207090e060405061c02041439070b0a0248120c1504060b10 56
    0xc42d4007103001d1003400a650000300c400e40c0c11010800881c51281010000b1900c0660001e03c1c0030401d180452032948281d00324502e050500c0980400798483c208124040c0c07102919103a85880340d00401c00c902c1c0c00a000034140c0c0d4400c01000042949010005011110305214581156105003e00d00c0540d030400004002142180740c040d0b8128240c000d20892801440d6109074100280400c0201064128641c0b900761900ca480f0010b642e52014204419250100c442c15048901c5000461b40c0350141c03210024058401400441c131040441070400d82d1400844d12180c040b404403c03280040112401481040706c4500600c405c9a64641c01190040c820b040740105031f0050300001550b9000f5a078141e50f21a040c8a088006c01d10303c00100e0080e80f4108040d42154400003503255007100c0030102205a4407403104090042c501410600520580164116441070701860681c52030402001034020700c214451400010001d0701081803040d00d080702c00360b00051004289580101070090014110b0f003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 343898642 1250 343897392 343897423
    0xc120301150806030a0804030807020a0b391005010e10080712020109051002060406180b060d030315080f0115060503130501061508060f0a03170a09030c0312030b0306060102 76
    0x1603d620011030b141039062040500010404a008010400104014084640200c03002c04109449103450305a502c1a105101e0350042291210014510091400001000c5601e1400c500800801259040101400110394400e60b180014400f07a6219007109070482103c4110f0010b45040c5000c0d955114002c1c041e021081c8540000c132011a8481c42c0108003900000d84200c040e2819417030046c2d03694031b055408460f142c0c2018100d07074210700c2142c5564000350b04039010507845c1c0c8034081400b00400401d881a010542c65403510122070040b030041c000240440d000912540d80c09008003400c4460f11189400382e4000d1074400c103d50b5610006032501f0403038010b1001e10a88447c030b040fa0040c64103078040c903109a51582c034a218203030803071394fd144960001d42c2d032100c5000d0031100b00900d100103800300a100180c401c86510f000030230080540a111014100580042d440351a034a840c100103a1040324514101411405a690b01d030103034105400060380102818204040007075210600c01d40440070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 343899892 1250 343898642 343898657
    0x50c040608060d020604150e0f030307030c0f0f12030c0521070215010605041706060a1a090303040306020a02010e150714090a0603020406080f01061707020c10050c12030115 76
    0x1140e6405103005900340e4001c2181d40d8860b0356501f54641c00b000d2a2080c000316189035a89400f6090440949080c0100180076500d0005195400d4030b24039040141a00c408120f44c00c0c100004841242940246000b1114840018003000008040c0d40c662800351041003414040d07004500220020034100245940031513405669004c2d0892030300812815080714103020a00000b030712600a001001074031009801101d048410398076040c0e4030303d82a0707071490b000600c0d00c100304020114051000c0c158090a014149003816080001e8030f141c01c11380050395503d80c005094003402d60248260f0070120545000341c1000b40e005403106450704802043c1d44148aa003056041140c02c1a4040300d07403c401c000c0140d120b403070700c411008001790041d0044502149902e0085100d61414581b52812600e256981c1c00c034014480100ca0502c143c040c00341015440b443d403280c0802da0340e8100301c0301c901d1095581d0a0305d502400c50342c13030310341408500b140c000c904c001c200500070840a21421004681d5a090018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 343901142 1250 343899892 343899901
    0xc120616090e060913020306151207031a0910050c031806070e010f09090905060709080f0604020f040b0315160507210e120601150e0609040c0e04060306020d0609050c040608 76
    0x21400b40c90014001e40c140235050420030700c14900c103101d00c0d04240a90b10f1150005403280c10710356071600e5000c0a0b007103503010031104050407201031070035501512080594258551700088a01aa00d094036101c4415001000b00412004007000000c100c424020080c5a142032a00c0054600247c5181c10345c100401203180807011030240c4040c4004000301c20042140141c1c5050881e00d41034151150710004940b8800081c40c0e200001c2c40080e540701110150140f5110340c0d003001010030b240086c4580080c1c0780c03159201d00d90340600109411000040c2000070390724140c54a42c2d0b21a81c410220401d01406001000c046a00c1110287d030303148074a02802c00c1e03014a00760075a07103036294130310040d030013401100038a607013802c0410100d0490fa1142a0b01c550240c410100ba11b02c1c0c440020b101d500520184001c03034071850507030000a040c64a43c200f0300e13803104500002c1802e888107030b04140e900b41d40004a150380b10f000c40c46103400030500070004200300d0522000c488620300c11032203180100640b100104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 343902392 1250 343901142 343901161
    0xc070602010b2b170c300a080c09030721060c050c03090f0604080a03200d0c2405100509010f0b09060d06080307110916050f0c0c120616090e0609 64
    0x140c0c0501100381c21070f480d400365881603d2091030303002d9520054806c660000401d0300d00c610161000000c0b00e44824a10796510900840303590040c11000341d040c850204005010070018031001c20040488201144201c1c840c20700c40306580c1001491810094100001700c0340090100c242d408880044920111301c11102c40021258059600200d44601807101004c0802d60060255030b4520f40484140c003101105490160712800c0400e540700124185640b200001041c59905001c42c3d43e440200030100e459000c040300444008070781058280c42001c009200501e000b0b01c43c20b0040c481c54041d08055410f001c2a0015400380c200024041e03d0081001d02624500e5008880500a0f17501140e0301c0d0340040c01c1c015070700d41d0301c8800c450240300d4007002f284200c840300d6003004050900703031252403500102c101000100d9101c103030740c001c0303c1c020800701c00b85940d124198070410000300c90060140c0c0c100030205c0702c869002800d10700c05200d800c400402050745000c5145a02c4041240d1040742691345140c2c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 343903642 1250 343902392 343902397
    0xf0a0b010522020316120204050307060806060c0d120608030306031903090e04030801030c05120c1e0604090f05010f06020c150f270402120f0c0c070602010b2b17 71
    0xc070240007100b04070300318420150100440c0c2c5030355140c010041b241d10305101248940d00a440d00b68014000138400540900c9189401c442c000c1c114910b0040700c0c490b0b041c1040c000000340000210320708180d00c0c0a00860040d18041c24a003005117286042c45e900103070361400c28240c6448480d0380380c004038040c14054412007000340369501c0030902d607191519005000d42400d0004480d1a45580000300b40c0341050000344000000141c02003240c40810f404201100615080065480200442598854840c0d10291000707040b92000481c000b20140048015510142c2241d005802140c0b001c001f403e60010f07038001b8041c016184c003d03042d201504807400038170030046044d021886c000303214a050f0200700041a090350f00c5503020301c50500302408020a91284400848280e40d0300008100f00042c0c0b20100340c1c0004144008a14040755044c1050800800ba4801d40c0940d44d40d012817612828207803062041041111700750741c200d0103e18108110a100d104014003c90105a1010b10341c0c0210000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 343904892 1250 343903642 343903699
    0x72c0a08070902130e06061602040b10020c03150403050d05070909051e010b03010605090418051f0c050f031909060f0f110f1204030c150603050f0a0b0105 68
    0x281c039002078403410104082d40c0001801d1460340c008200009159205032115802080002d021a15014003030209120b07404101c0010303640255100e075180e59590760986904070b54201e54004e09150101c01c4101030900845001100103040c00300b0030000003075401821941400b03100c880c00140c0b0713282c82c08100c0c0d4480c140d8003c4010580340009211498a80c001c10468001444c80c01104ca80e03245c802c0554140000e105407008144140040340326031070071fa04240041e00840f400c42105801940780c492070112004030741c0480c2c01d01481210003d0f5135070f01641c1c04c030044504103c1e2400c5c1d50a00c81c58a9480028070b11404d60581d0300014101c820144c00814086400180c203210281c9524440c40040080c40c00c032030500c520340014100c103d030190041d902991616410941050307000b2982c5880b10800510480412007003103950000102540a401000104c404001a00301c1c00c3d80b60191034401030045109a070380c420f030301c410b00007450360125505640081e0b4140c030f04040c1103d200403100c0340400707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 343906142 1250 343904892 343904909
    0x31305010c1101050912310902043308090a140303010609050406050d030807050d050f0f0901052505090a08011517070e060a05060706060509072c0a 65
    0x905a0200a91100c6860742156070b0740020001600c1e0b402c2110740e503c61514141c1040300040c8180c42c0383d00700c05145504240e04e00440e03c050341d6102401001c4910044d08240382e0365078003203818000701007400c05031782c145888044c151201e5220210b4800000c000c2300c00b00410407a041d0001141e90a0034001c40810726400254042a44441c04940791242c109000c4c1d14005a44260002003901c1d1038003a410807910050000f8104448a4500325000c0c4001040441449002c02003400312401d584901c611840ca64154035005081030013110307003403d80c050080101a8100814410080344085510051081700f054094195100d0207080e640b500408120651000a00c200090190019013040040240c0d44500c00383c0d042e10342070706aa00c081d480c0038000103070703100039418001169203264550f0001d000801c402c00c0c16595400040d201c0c2e100001c203c44061303c610f001c0099041201c0c0080c0c11030400d0511003c528800c44d580505c0400107481001501d413209200c0d22a901d4070030449002e0560384 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 343907392 1250 343906142 343906151
    0xb0111100f0b130f0b040b1c060219030204060306062109050f0d031a090412030e191203140c181c05060f0c040f0b0c12030702150a05010609030803130501 68
    0x150300c00390044c00c3c185509201c4505003008500c0914152203000d82012008140c400c0151016001c0c08642042c480c045034802e40c2086000313000c012800201c0a5003481c0c1e40c015036500d04004006050300c0d0a60301000034040754031650301400b1015400d0200c19190b210000039120024240740c3c0c50006644208410703400b41500342c9012641c190860f00301c041007000c1d641d101100800c03c3c4095940215400351144400d5075800051500c29000390001e2580d82c0119800040700051030316020311000c004a50325415501900e651503018021244c090f550601c7d1a101c038500f00c0c011140300c1c441c4144684070110b04040c0d04072181d50300c1044240e515030324030034108002d22500d040303642c40300b05861120444540c0000281044081c0d070803203040e1004035241c0e0601e1131400088008981001d5200b151900880411140e454a00b402840c4520001ea000305401154018a4188410081c0c500f0ba4400d04010040c001d56401540781d10032030b540081c085070340350354032000801610104c100050055090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 343908642 1250 343907392 343907419
    0x302010f05150913020114030406150e04060515060d150b0d0204061d01170903070b1f060912080f0f0c010203160e0f01050d0915020a030b0111100f0b 66
    0x200802c803a404141943d1000380e81e00e48110740c081c1c01c190280e0081c002900c1001c4041c0d1541c182c005150028452480070801c0030401188100701000e40d0060794490089204000a01c4060300610b074005908501b54541184014046501440344188040000d500e4011007544052529000707030081070340c4407460307880c0c00800310010042c1d80584903c07000075404c4401050711001e00b01c1e0401c61000f051319081074401121605200002c0300401c401000e020501a210124010140241c0314842d81c90001c4000304141c401d04c08080300582105003004250301092021240003800b00701c1142c2c10843c2c00780c580c00c02c060506154402c8103502c880041c00480c0390404024150040c40c000c00d007000b01d4031400e89404208036400d01192034041e0b400000e4402c42003c40d4081d000821000000040100300d40502d1388034001e440203030b036036442c2130164009590101c856140c45540851502403810000303074404441390a503106059000359600c1582c5e41703c0000400c02907400303c06100005003000540244 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 343909892 1250 343908642 343908661
    0x206043201061a120a05060d050f10060f0f1a130806011a0c0c1e0d261e0904060e161701050105040308030c0904050903040f090212010306090302010f05 67
    0x1043c0319016118032082c2e030400c0c12000b060152603051901150010746581c402940718045d24003c1c00c215000f0380480b2210780802c400340201404581c481000700b04d042480310400c002c07583d00740d015008841ca0403005010038011505020308482c03445030010090314030400c0300215842443c420340340c41c5c00301c0c1100050000c404901c0d14102c03452505265200280d01c55000c51b18841e005c1c18580c0c2c0c1d00684028900c034906007021000c9035411103c21143c440c921004500030f43c003400420b440c440100da00d00c2c1127070b501c130b085020b14206800c21890b041c106c0c000c0824100e400390550f80314600c0c2c00442c000b0150f445903030200c1c00a00303e1a04164190a2810558000000a00c0c0307220018180713124500751150507100e82412a001a950b4925003483e40d11040203540001e07181301824042080984545c1c0c0d101e0003803e002c0c3c10707441c0140d60b81d20301d04007134400c82121b030ba0f20007015140107101d1001d2a411020701107044a4000300e021a4840712807504a0050481000c02050145004240800f005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 343911142 1250 343909892 343909901
    0xa02060403021513021009090f0f0b0d080703111002042d150513030803010e060907020a0507030b09150a06090f021303080702060c1212010509070206043201 69
    0x501030340030740702402d50700f81410501000c2141d03002c030328502030148040141001e19038801c00084502e081200607403a040e0890655040040e2821401c0c2c450785020b0f0480528032440e540381d6403c0301c42178041003440c0c0c1c3d007483c1c0f0301988601409000300b0034200058400140003014081c0b450302011981c1c1c0340c480c0c0000c0d0840c82d2084030084501050f54200003102c10101e03080060b40d0620700503c00d8001428000c488a500c012180c000803c1801c0c00040001c441401442c00781540d4000801a03107003103410301c6407104000340604115441700b000394021440100c0c010080c3d9410194401680d5100035440b17241124024503555030781d4207070b0304100d0081010343c0240c4c1a01c059000c14404010614004000d0380101038151644c2d41001c8010000110000e00400209202420b905d084c000c845000701e041884a86041c034584600060b61b2a030030300d2012807180506009c9903600c0c100e090004000703541e0480140014480c1d2210603050300110902c0680d6440045e454184100c01c41c405c05500d806403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 343912392 1250 343911142 343911151
    0xb0f01020610050405271005070f08010e070905040f0f2a0503060f18040c051e0d032106031e0b0f1504090813060203040b16060f11091311090103090c0503030a0206 72
    0x8038500350205818500c118245c07840c240c01e0b550bc90980f80d09021400c2d284101c007402550030700c00c28040003c0da60315030303009400d0b01480301c25001458020180c101000d0f2490081703100e07003011103a207010074010181056103061110710320b0b0036a1a079a44001240b80800b590903131075400070034000d039002e40aa210301203c3c07059115840c84074400d981d40e02803110081e03d01442c03008040e20880e180449080801105891500030701d02001e0084169401c0084081100007000105494403010b0080c020889080c80d00c480c0803048a0304110065160001074540143c04075035203094840104e400c0d00f0380040f0ba07120020000703104001007540c03440c08480c140c0c0024240e01c07103150500d100141e800d0001c4252003c035034420b181035117820f02d410a58003800101e56422200981e03209040070007001c0b107229a50038484840c3c42240d81d0140c2100700071469050511000c9a281130180000f0703d00d01200c00e642c941802801e0208020345280350003c0082d809030070541d003501c8041200c0c10001d41c00034105015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 343913642 1250 343912392 343912423
    0x6032f0307021506030c011b060c08010e090d090b13362f07060c050304020102010e0a02060f1c0e0a14010c0507080a050d050a0b0f0102061005040527 66
    0x80f00c80d07102400c00a41d001c8608a85c180c001d10241906940502010700c090200400e14004450082d60381c1e800705da402d940d009000491090046c0b016242880a0507041256400144040707540301d18024681541d600801c9852040031628401000014007a58003030180003980200542080345040701c0c0044159280801d0400180c101c4040c4810f8815210a218508042c0e8040094846d0905440d140e4480d01d824000d010002c00010519920580c0344100040d65002d030b5a00342800024203640803160f0a8031280c100983d120016600d410803960101c01c440e80540e25080b991100c0c2d885d050000540c3c034200e13410003031400e90480c4081503944000d0f2291100b032000ca00c1c0c41e65074900721090710322440013141c020051180401c0801000d00024030541ca0400c2c90030619003c803206541d01aa096400303da166100044507290541001105501c00e1006049601e4003206030030804d0341c0c40c8196405541d80d039010540300d1000c61381d40600c200c0400740d61b4a601400b2140d950380d079849030003172034034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 343914892 1250 343913642 343913653
    0x90406080c04151404091a160905040c09051002032b11040305120f042c0919080703180303090e060609011d19060504090b06040f06032f030702 63
    0x1069003c03944801c2c2510309519880100f004402e0520001700f10201040e5140c0f840e0b00c0501040350f0050021030720688103d001c0f01710710180c21101420090064104034841e50404010500140c0e001c19400c0481c0c00c101c80d84542c0780b1101c0026070840c45491200c07012040074085c8040e401d0403080e2050030340903004104100845000f11a885540641d000061098000010384200110f0300d00107042d101344441021440e2940e140400c506021806001c00c1c400c0d0048100b9590441103c80781d00e5200d070800c009002a600c041c44c40c0d41032504056402070608001040c0e6009161060740546004030a00046c03901454903414050207001780f520650421321510700010700ca1742031607010764101000607119950599071030714240d142c00c56000c0e222500000c5125000c0c195942e40c050060081c0129103e040d502c50400c1e80d46000c3d94028210103005490800c8108511a44246600c00311081c078500000e90007041188a0707020300700d8004c21229505003070442c241c0309481000030b50249603140c00312034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 343916142 1250 343914892 343914911
    0x70b0405030c03012a03020405100c06110406090303141209250f0e09010b06040b0d06080d050301120312090c17010b0112020c03040e090601050109060924020102090406080c04 77
    0x60a1700d46500482c080c02c0106a103030480c050841c801020500011b003005030915440b003002c40e05819046115030700241460b03031640c05024043c402c10f030260141166140c035240c1083d030007904400b0325101c02030400c014801d110b94400c11180035120400402d20b800070250034001141d503950390300d200c00625101c0300744401a00e00001c080f0346004032501c0c0e01c401c240e418500079400058000017440c414095407141701107501a50307884003c4c80940a44243c2c2500c80d0466414101145c000e604003094940c814260120784a4225003900d04403905000c214030701070040d1504403020381c000f1211881c0c0c03904100100b02003080e541540d41c26140781901460b001903030b81004900761862050300c24041500000042d1112420750010080b254520044900d007d54603c000c0c090740f14210749a501b150800e10041c0625039000075860000c02d00d0b4130b8002c44081c107100c05051025816008880070092602012011a00131b4040e90082d42009104000c026900d040c01ca03224026550513500c643d140c0110503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 343917392 1250 343916142 343916149
    0x3020706020105100b07020f0a09060f1403060f18011107060e0102190302090f06040b040e060904150b0a050d0b01080d020f07030803042f03100902010c020f060c070b0405030c 77
    0x1d214000c00769441e0744d000d00e84482c404055018203000da8000c000740400d0000d548402072a8002400700d0310300003030f052f80341120700380c1601290b8202c0280b103400c000b4410141d0760b00150454201200d8030686556850b10b000c00015032078610025400c5500b441e49140d60031200c00040c02d41207004040500100c04070f02d0301a401c078818600044446001c1201c4003400b544258080d0290020180c420b01075000701c000010069041548600d401c0d00c40041c051259095561504c7d0300a00d081e0b8496585040c03680d5540555207507150303440e468554926101d111907036501ca008004220203496503800d181d103400c0c00789603204240100c03106846182c0032804428800607108103250b07aa90041c1c013000f0304540c0d0740d00e0300e50b0010340192001c07a0110840d03038210134070380e01515a143c0741110303049a121000003814180b409085902401c20314111400340980d8109a88030399807541125401c1a008502000906034094280d40300014400c0c00e00c013151058078100104244d5108408440c0014500c1040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 343918642 1250 343917392 343917401
    0x201030b040e06150102070801060803040510030e071e091803030e1207020112111b0f03120c0c07090e030904061e0312020f0d08160e0609060c0325030207060201 71
    0x2c1c00400da01c00800030300403203443c200380110800c051043e600c04684c0c440d21942516480c0c1c11051107600009000c208030320708142800d881541500f02840b0729900050b455031103806600c03a01a03c4c0e500e00c483d180c40d102d801c00d0004098801c2040402602e00600b0306115071a604030012804a49880c5580c40e41107c0007645240e148400c031061032a21555500440304245982c7c044541c250300e0b0500080640c80c0100641031301c0d41019a14105d40484541c45ca10300340c0752100211558204209052211400d12103540c0d100503084d80369585d0b10344028095150a0180c0c1c00a03250703a19100701400890804001000040c0d8203c9041c86010344441c6258400340d051031b500071448400940030000552074404500145d2076900507107100c10744138080039052107030004501001400110810100d44003d400280d1015098034240c50480030f0140070555510811020710f00c592800b28195220510400443d041e0001110000000014654120860084d012011000f500a01c1404501d16105205c0e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 343919892 1250 343918642 343918661
    0x5150f090a0b030f0a0b1e0606070201110331090605030a02040b0d08030903030109110910051e0d05040c0605030f1501091e060905011106060616020a030b040201030b04 74
    0x590110340d100c80004500805003030702c410b5054050b0000806043d00140564400c960003600d144030285444034070b0358074200342c0c6400c4e054400c03500c02c24001181c4071318042d600d00590a0901c040144201801c1c280b440c050803081c2491030a08508194149400c1c005010300403000e4180d01042503200c1381c0700c406450306d034011960141d014018100c054601600070001c13050001d00380101d844280e4a9200b030a0380120b40c2859190700000041140c2c034410310401e09000b44043e40c45003007048490004204520a200b1041000300c08a802e54039190902030398500c4401c00240070f0fa40310516556040030f44401c40301074496401b1540d000429074000c90440784110980c001214241d581c4504c0810072104844203141048100e101c0802d00109010200690051180c00c0182082c5412002000034000d03410040c100804081c02d0b25208100041182c0c0085d01207503a2501d4603080500e90703103e2400804044d500007800c00700041404803520007540164000c0e40d041c062143c01c9802c2c4010b4480c03c08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 343921142 1250 343919892 343919899
    0xb10080402132003070f08010b0a0305070e0a08010b0a050d0b0c07060b062101050f0105040e1b04030b01090c1412092d190c0515070b0a05150f 63
    0x4001030010b1411000c80119031440480000e40d060341e06402c240606140c800007254050000180146540c000300d624018899900d80038100307605001d840300490250700c00070f505068484010602082c0112034481000e03d02828569800da5509640b501a101c5000c030107000718065100440c55051640c00d0f03215031a040b03821502c040d1984510007001d076001001c26200155074001101190780c07104000c050b43c074046084004144c881c00305050741c460301a0702c01440340d00044965107240c0d030010141c0d030803640c51000346425591118034070300c040d106800c04013603081800140481041411400710f81030f0f0340507560170010326005c4601921005a02c082007420642d041c000c401e10191040b03076440c0e2140d1900255107080040b0180b1f000c1c1c801e055102007030b20072581c1c98040380908041008012000110184070b2030564180c851032041a6a8080d040c0100402c014049410b40100103c5058940c081190401850f09002050040038155018460040c2c1c0d2103040f512845c0107908400c2e0b505005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 343922392 1250 343921142 343921157
    0xc020d0204090203011107150c0543060b03010614100c0506010905181f0906090b1614190804031b061a06090a0603020d0e010e0f0f0d020615010306081f0b10 69
    0x40d6044811940c0300303110300302001c5510381e003014501b40000414142f0803000c0301d27101508251a00e2401c0d00c2c08054194000c0c2c0c5403070410424801d041c25450007012065800300c40a103442e032401c03600a0180d800c068440d100b01e030b000050840079640110b00c91201e0382e080c2a5040e80c111030054540c4c810301c00c04d001e40510b070711210207440348507800f01e04400d108103000181c90342d40c0c1e07417461041141110405140002012a17805070703a08a80c0200c8240c41094105207000c040e42e041c02c445e80880c0c0800f40c10840c001000400305801f400191160844485000c5e00b01c01103890b040d005800f000c260721881d01910501444d43e4144a01a601b0300c2d0303c020304e06c090700c0741070050413802500f01d20450062151200c14554a0800030300c074024a032459080034140440503003441c54502403104400b2141390307008024150515901050b40c03500a0b80003030540500c0390000c1c00480207020250802506030080c03403089115041c07c0803440c1e007a1440c4020030320140d400d00701040403200f100c02c400404500007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 343923642 1250 343922392 343922407
    0x40f02030d0f0c02191205100501060905091504020c0a050102040510080403050a1805060a02010b0a0b04270f0212100f1d060a0b07300c020d0204090203011107150c05 73
    0x400c503243e50017206080b4a40d03030780c0c1c8591040249144040c00e8a0a420001c2e0119801e82c02c0c1c01164050010740c10316815032840d050100c1e1801c800209030344150484120302c004580c0c0c4540403540c0c22a17040c0115102c0d074030942042c500035401031203600d10a2840d101604c104078082c401c02c501c10b40e0161103180c00d04050034010f607510080e0b41c0d10781114142031100441c4594a80000e45240310480d0300000e4220355080901c41202d6094220021035002404100b068a00f04450400d0122003d0b1084045000240e41c66001c0d04210141c091064008194070710066107541070280710f007440c811405d01c1113644500780d14419601e401100034000350f031400c00c034501c00e032121603907042000a050100469603d140091f1203410290007140c8180d88040000004200c1c1c0341001400a00141c44541d50380045030094140711354908001e0080b02d650610800f9552207034030100b21a500030313000f8421107048401e4a015039010712000c0718401ca92035101c0844081c0740c440c04042d0045915101c1c0760082d07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 343924892 1250 343923642 343923649
    0x60108010506060a110f0f010606020c040b0d0210031104030b07020d030510050103090201090b03040b100b0a2102071401020405130204050906150c1009151a040e0c0306040f02030d0f0c02 82
    0x2030302d412114403486504600c251b05013082140340240c0e10444000a85c2c18202003000b8280301c2035415140c403031400c08049280c103503290564070700041c1d8101c0d481214180922401d40c0a004050a860322002000c0f800105001024031181d109000d0b5a00340c9425070f109c000305908490f4150f540c0844002c8000e021702540d4002c0d401030140d603005040c84180310365a8603012410358801c440864031342d90190184001e4081220000010b006800d08260034100079040003404203510707074000ca20b101001000e0020310f80c880e904468120380c00000505402c0300030404203010758807602c41d113400788a40162040c000001ca01c2035a0560b1001001400203840b0b103000c01410742003030500503030804010400c1c8030542c0010000680c0243d0031250210f000695401e01720450000d11001e01c07582e90525600b0329150311558441003076458203d03400511012401d2a5034502104012119054030961042c00305021070400e1001a26208404131802c801860000704c51446808041c5004140b8070340c1d4403001840d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 343926142 1250 343924892 343924907
    0x30a0903060f11030c0a14030c031f170c0310020c1209150d14070305160c0830011a340b1603021903020d020c1e060108010506060a 58
    0x3008440105142220f82c9441029a10a403400420050005100c035862034005c07564602809504405508510740000c01c0f207541e10000342400340c61250b160032400c0c10880a6190030207850083c410451480301002055568980b400b2802e01c20712440d22403100000c8640211400c03229050040c200640c4114034800071504000c2000d580110124405640001c3c80009440303001070842000ca0440440b18003804003c3c401340c514001c25046c03204026240740403002c0e100000b4441d1420449529240c200418035000d03012060210707480900d0180f10886240e01e41c0d0300820fa0040c003409184c0d03030716000542120541948407440301c80c01d112211040c885203182c241d8081c54244100b60300b050603081d0b10140f08101d00d007210f9000d091010700000c1e0030a110344512460450030214980419040107507010700485000008150300000c000b441e428154060342c170581942e0301211429510102d020300003c460b0550080705114600c00022828014000e4034003c8101078a100e02c1e001c5c0d10441250b200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 343927392 1250 343926142 343926161
    0x307090501080606220608090c0d020d0c050907050c0106080a113d1805010e1203120901051927060209090f091e030405010f170126030a090306 63
    0x41c1880704100e01348102404c0d41710608400e100b65003050400401500ca6400038111034810b5200c641160f8083e250448001d407501d40440389455011064a040d81c600c01058002036040350004081c4800700350001d01a1400c4e11007480240980c640341c0c0c001540d14002d03940040c1c40040894284080d60500402110342020b880d52182416290008299940a0f0342128481c01400d25408009d2a0780d1244043d9171680c80d0b0000b110256141400080c4000e0b424a00c851003848502c115100304001001203030030341031819602481e50326089900a00a1078120b402071049100e441412070a801c881c86600740112a522012032002e4041c040881141d02445046910583c00c200b024407503529407895600c60400101c51280b586401c0c140182071120a6914454200040c1c0c0404002100481035606a613428a48496030301e038101c42c211098500030b072040702c00548220000c2100004600c80b4114140543c2c0c2080410f00070060282d41d905c60035807142c0000d8020030381480000c8683e0840d5600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 343928642 1250 343927392 343927399
    0x19030e061306020c04050708090709020a030902030a0f0c06080405070603020d0e0105240609031b1c1a0c120a0902030f010c03060503062203050705070b07080a120203070905010806 79
    0x28041e1030548403074a944580c01000240e841342c90044814030b001d004043d800b003405c5c607021140c2c0c00c2510405550761403a0080f00006a00801c0340c41e20f044c0b02e5403182011540040486a40c0300c554180344020942c900c400b550034009100000c24210b0007424210700440d4448014562a0b1612a0440003034108000d0108800d40700c02901c55112400d0040038010740ca03800d5243c1001c4c0c0c1503564041c1e44041050401c0c0078085c2444010000d91b400300c1c0100001c101220071414421846000440182c0f211915a0400d640341074983c1c107000e10a1041844400c14182c6884641c0301c070759004016003d003001c0030340f4560240d000140e080345140c100d0b0f440c8a00c0a0200c07908505070003003d41c29209807507030440000760341c1c1008000510b0100000e075088100c2c4501180d08500c246803e00140d501c03036002a091100024409003000003c020450040694000140d00c801040c9080c2c0300644c0310341c0001c0e00068032500d03c100b81c3c1c800740c800c4a01415217a1950360740b03603103000c0041d645070800801035a072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 343929892 1250 343928642 343928647
    0x16030207090203040305130602160b07060f0509030301090c090323010f0518100608150c09030106030809090f0108190302010b06130303080708060a030f11040903120e19030e06 77
    0x701d000080c00510b0080d4802d0312565200d17241d11813011810310f25513109408550208800090355910606c2c14010707075560084a81c0c0e9181c031400c004014000f01e0050303006280c0b030f04041103070205010011354140e44034500e080c8a44265403008459030b102d00d000140c0410b054500e54824840c2d0114070744a0032000e200003003207030000310411a045640031580141054007102550b0a5403106010341074494442d150b00300845820f00b00309999403d019400300940303143d504041100c80c071061041c2c0e0500e110080085c00046d40300d16240300750380c01031220341d80540f0040c400706401030180f001d21410b0700e0780800241180241c040007140c0d04007040030f007502503541e142040c0c001d94a910004046000115030302d6813030145145802407207410001c00000800c01000300b880102e96481c0e840c0c030f0031290000c0e40d5001803081c904041d84207800002c800b550151820b01c0c40c1b02010f40192241b85104881c0c10f04102840c0b43c64505602d60940c4107680010031484235005001034081d04000b00c4968002c0c10060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 343931142 1250 343929892 343929899
    0x1a040905130c140a0b0f03010506090a03050607030b1c0b0601031a090f0907151d040f0f090b090d050904020d0b0a0602010e1605010e0f0103180c0806150616030207 72
    0xd900b80c1c040d0000100e04012209039091802e2a0032035200600340041105c1c0761000d03200c01c0030075a00040c01990320074040000d0f012410303a0385000c510060740e04030041d07036940d060110000d0000c00c282c618460040d40c1c241203851402c1200400034107010341046451201ba65a40011070082c0b40d240600c03a42d94850401c0006180c44840d401c07480b4041c200e488000d07600309490b40380d1809405134000c900468002c6000e4400c00e84c00490383c409050340d024060001d10701c41d0001400ba00500c01000c0e6054070740840f803040c24003c0e80040e090707103000343d812003102c1e00c450140c16218200c40b02c0b0200854010072a0052a0030158010441405000b000141d00606900014014a4141c0c80140140e44408251414100501070112441c07402040700002c0762400001800302003555003901c0c800c030380110b1700b80007690190300a8030a0000400051441d4181807400202d80000c500543d8441e20038140065511a90b86c8007200742c0071002009103040c1a0016144404d01d03051450403801c5009900700003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 343932392 1250 343931142 343931153
    0x70b030f0a180b0f0601231c050402031507050706020f22051e21060a1a1f0207050301020d0e0f060c0f21070504061d010801060e12100603020a1a04090513 68
    0x101410521f1064841e0b58041401c5401c0c0c40070340c0d002111141030b01c2e150500005907000180c0d045100124902c4104981d94090181d925000b0740102800c01400000d1005444601070700401007000d081d0303500813040201303400790003024460b8042c282e0001d1040c03600842c1e4415240b400e840d01c9000400b40403002d2681000c6503541d8410030128501c5501c501c1c1840b60380a1540030f0210780e0703000c13011002c4a0401107000240c484241c800d002c8940c0d400c481c0c5181c4042d100307102e40000343c04044c2c02595501d0314000c140c001030882d5103605915025014030218400404240d0034045c1c180401d0090420582004641e03882d40002c0c00c030300d201884055104608640c0c1130000b881981180c42d900c0d1103910300310010b8011020914904508a003401d1400c8090381c1212203181900c00d6881c19004c4451004041541c1418140820b4424403404004103107940131504070306d003903a10941301146103e5595441c945011042c02500c0b0012100b88400c3c8102110340d440280d20040901c01c01800401d9601c44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 343933642 1250 343932392 343932437
    0x504090c080f0601061e0e01050306040e070e0a0c08060f101b0620120c0309121209010612030c060b0a0918020109120302070302040e070b030f0a180b0f0601 69
    0x411000d50041401081102d42050f0540e4090492100d1b124030403c290030000c19864040700a40d0501a01102040107074035030340e02075210305841d0b0040f181d1051700e0b0040140680011203035522400d00f4a20345640c1144110f110078001c420241c582c418420f14101088400b082c45441e69003003040e541d1803030403000e5035000b0740c01000d4000d07040000c95102c0c0191410303011010314040c5070060410440e51b904811941262a0302007207642c06070340c42e5150800e1007402c1019003c901a22404003251801c5090707107903d48a801000540c008014056482c85841d84800601601402140120030504041400c0382c0044010b840c000b840087d210351284100c0c0c00319079125040034001c94400e0491011540c1003405ca0014082d9a56002003071162960000d40d51000790000901454945840400589007000341001404410040342d03204d141c11031703090112100441d0314072600fa00b040c42c09a07074500186017518080f6000640c40f0115526a1500100001c0142c85141004404d00d9001d40f01589443d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 343934892 1250 343933642 343933663
    0x1103010b03040c120308040b060411120f010501031112150d050f010f0b060f1c0c020d080c090109060513170307030e0f10110a0507030605091005010806010504090c08 73
    0x51403501e0342490f08142c840300406403c54412a10360b2440d19010a07000141598055408101d4810b41e60781c40c0041400740c01c038130f02034100800011a0803209000c81441d404e1080360340c1d120843c400d0ba41c4600440070f59409902a10b150042001075044184542c3c50280d4012152140c03011100d05030380115001143c4000182c030560018010021194400e02642038141034900045c090403447d0b40000d83d05100780e0380c05003005080081d00c00055103926048110010000108228000c402c2d280a91644a0b50b00c11000046407400001e4050200b03505894880c981a56145406030074101c007038505070b00c003801240001e8600500055081ea030740c0791034028180003201031030301d40809180c040d1140c44141c11481c03199100c001e483c120b80e101e41480c880c81c40303003e16180c180e520100c0c0e611414401081c3c80905180a035003008000d000c01a049103008298002c11180c07202c01c2c0401c10000c84400f0300500815401034001003110789050307008881058014281100020b54611000d40b900c800c510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 343936142 1250 343934892 343934909
    0x1c110a1701050709060206060f1f03050603071211010302180a1e0602010618200705010617061501210906051501050a0207030b07030b120705330a03110301 68
    0xd0501020100a006450f08400c01d41042e40426080c4074000e91540001004140190601408010345584001a9040008081011884031200b07180024050201210124004e00c0f50301400a07684c415011180a142c0d007280380d0f14429088140114003030b40c04010030003982d5014a184801310f940d42c211a100409610a11058048803001c000349041d92642c00b80b0150f9140090421500980c4600a02d0503105a140040c03200c0e000d82081e000d4801880c28110403460105141e4104201584120280c0f0714400c192106003103100180c40da502d1048405c140101c0c1d40800c540015402032200c070020100308880c003400751207000d00b41012520501400d884a81e00e4500340036082d1441c07041c1396402c003c2072070007074908004050065a1350145110081400c12001c00280441d0300c20b6000b0409850f000303195203010003e600c100e42d9518114060107201e89954020000444a010020684240c540142d81c005200d6058164015040092084141130310f40ca1440640a5641c004502900c60f20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 343937392 1250 343936142 343936169
    0x1d010c020a020901060903170706060b0c0f07090b22180303090204050702030a08010e0c0f0a08040203010605040b031e15010e010e070305040305270402160b0903091c110a 75
    0x40c01003000407030381170344610180080c4880c24404903c220380303104035160301c51402c29039510350762400e1402071101d581302035805075010503000e54807000801c1c0900c000030200102e0f5007080d21408030004450090413080e074440e20381d03003000f440f9840500841c1e0012050003c0000c0390360004a40541c44011010b084002171354a02003007045241c1403140380d42100c1241700075402c1c8000d401003d04101d0b01800b4044c0d078101f00708002a0341043c003104883c0303280314142c0d01c20b0b160101c21001a1003507030103840403403103542081000b140d1030500740f16524001c80300600030280d108a0454021110700340c01c1c914203190046a107044841442026414020302ca00703003c8490030342c0340c201e181c4007145028085108240c1418140000f0079806000e9034044141000f500c07504200040b2240120800031145a07005800880c441280788444407000400600a52203c010b1303580d1081e82945038810391111690106002c40f459100c0c40004030303600c102da84a1a40c40a03d04104000590082c5c0030340d200301040c0010b0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 343938642 1250 343937392 343937413
    0x706091a010f090e030322110d060204031109150f0d06090f03020f03030c070605060f03010501060f111c0e060f04030503072108060907140d0903090e01181d010c02 72
    0xc80c4220380213a0310490141d825030500c81c0c20b030076102c800507482100c01441d40d0f40c20814822444903250300c000c0e00800403042d0b40010700c0c2c110065007040c8000c1c0c40030703440040c4074506400c118143d04e2003011507072440000b29448004000301c0c822445072068115001c4040e030000a00be83c40b460700218010392040c0c02841840c40d001b807500445521201c1290400d0040c8800c0688190659001d144d008401003503c0d501c44022a000204c0f0a410340d030300d5030811000181854220f4620034403200c00d5981c1007040c2c420100031031764440d0050b4230607405400000c040c10350503208912a10b0240f5005104ce0300c0e1404901c4012000d0f08290426280b580000404c2010412010800d08409a600c800c00121200d0400c0c080c0075580c00030803844c05404900002848030f1301c250f03414001200041e099079101e40080b8160b0700104002c050440225900100100b40302503200e01e140e040b01c540c2c005148001d0078440003031000e84412040c5140b5420040e80303000e0703882400e0203483c4002200d40e0040040450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 343939892 1250 343938642 343938659
    0x1012020c060901021e0711040b1302030f0114010203040f0911040b1801020105100b120604020d0c18050108160302070503090a03030206100e061302030606090315091b060706091a010f 80
    0xc4017030342c48100d420810069000401c441d0310700c012440102d0f000503001c45144c0c007040c19100c501907e0011244000204600c0313210500ca800d0503100382010070b000d9906a41d005990340d200c3da0007a5060b1404140e0200140d00c0d464001001c42076440704023904150750742696000540107110b1512501c00e0027001d0328001d580c2407084684c48035580001001b40b41c03800400c1107052042310405d55000b04204002103140d00d45404039111405019820009103c82c000001c0c2103d08020072a203242d04075440005103580300798140c5000391482000140000c0207900290f00a62054408981a000c1442065001c0e5180d030b0300d000046010b60058007842c84c04400f42100c2c1c1c01290843c0094820b004244a0340341c43da031101d40c00d00e020708080142c3d00e480328000103505010340310340640c0c10300c5050103044160800326000d60146107070204a07414110007061416031089086c0c601c80c0c00000c01e11411000c21850f410001855001c3d0740680c0080d0380614a2224100302600302d2002d80e0080541007000c1c4a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 343941142 1250 343939892 343939927
    0x405180f0d0f0c020a17072c06090727030b0720010e0c012703060b09091513030c050d030b1201140601030203041401060311040e0109021012020c06090102 68
    0xb419454611403c3c40e103a4001600c0d003119001d00014040c40000290440904100400203031400b07030300e1001004440c0e049040c603821650401010000d0000106803030b030400d804121b002d01e800da1503601a10044032088100c0340c440c07200c1c03d001e420312f010001002c07420310b801c1c450240c01e00d5640c03200c408a103007008680c0001c400d00d5001d2a82c5c50007200076112400031900c049648801d00e0f10031241d2101c0f02e204400d1a82d80e1061813a0185400d1002080240f01d60043c206d00c02c09450361065030799007040c8035481d5490b1241c400c0484440c0000101c0c003980340d11103c10070034460308001071411019280c00b80b401010040100100350f59186803c110325020b448000c980e0a070000a11480c5100510600402d07030142002d81410340100216041003000320312125140c80c07090080146950740d013002e18a0302e103800754081c080c40c80e0010102041c141030080c9461140c0140c50015040c1d900783c1c086030769140c6540c0c40c40c5055401d02c50720130030603000e05c03a840c010001e840015840d511801c00005411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 343942392 1250 343941142 343941167
    0x2190b0d0b21120a03020903030c0a020f010c0f02100309080d0c02060c070804170f190221060718120c080d030509060a0b0d0c030807060605040204060e0405180f0d 72
    0x182180700000340c0316100002e010203840c0e9050150344d1921528402980a4043c0302d40c0140c2c18040440c00d03440f1a4000162012010f000b00c0c3c044618019007401924081c1e81d2410250454410f0460000581021aa540c1c03460b11a45400a4000d0b001d4032659015005402120110b944844c40700c003015070f041012980040b80b82101d81d180040c1e941e030f2030b4540e1007a44903080d2210039620401650b682c052020b4045d074101031007512200403a40c080c1d9022507050b20822841840ea00030308407140000d21100c804400240e030000c140c9034a40080941c0c14440e111500c45480c45140000305404004210407524148540c100f010828109004a4280341d130f0700400740105441c3c1810064403403000154103030030075030490000030304a0100000c22040b440d80d542c09084540c5030080007040140c2c940c01444400d0154078100089910303002008181e200d644030310000914054410002071820307070711441d00b003100c00f41403010303115210044a00304180c444480714160850310703007c07580c2500040c028151 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 343943642 1250 343942392 343942429
    0x30807081501140903010e070608090a030801051c02060d23040209060d0303090506070c030f0e030d271d01170604140c1306061101050c03010302190b0d0b 68
    0x6500d01003000405141c81145503070704001c035a041a60316803c0403070803154640c1026000f8400005034103040c599606541c820840000e0400300080c01242001c20710600c1280d050343c1388102e41c3d1a050400c044d09200c00365480041d0426148000165a100020001d024408001080c0d03900c00c2c2c2c40d4a200c01c2800e08545802e685290204401607071100f0101741e1001003100c42c00b40c1d9090034102140142116200207046100780010f102c1e480340c110000139074242c0300781c0e01c81c00f100c02c800004650480c2c030884010340503840344030304103c0d840c020b0000018a1000340011250101c02c0400040030160f00d034040d811411290040031006a61028001e003d00411850b9142c0c0795014000c03070755150801800600000000c003500311000005010440900c0c078000e10f035042d12980064000b004080a1080e0008030b40c42c0c2092071071700310040c0a01031280700c0c8000c0c81d6003540e2864080c0011080c16090b1a241081044400314400c0c004002610101c8820800051200c06c000148003040290684804c42c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 343944892 1250 343943642 343943657
    0x1a031906031407090e10020307050f0309010515030f0c0f0f030304120605010e0f0609060a1e050102010e07051e01030603150902030d031e0c1809020309010b010801062a081204030807 80
    0x405c40001910318220701c1840d60050ba03a940d66103003261103009050b098094403c000040c016140415040075018400c140f0040306112505c03030426644024581c80f050180c0c10a0600c8a9203103809a030041d103114000c1d081c06429110140001c4c2580e1041c4c0180c05042040c0b1452014005030384280da02500ba0440702c0030003420002050080303900020440c40c4103000180000303115480710f11200d4014654104908030788400d140300514000d0380b40c05040c0c010b604c0d1049034424508005840c20440f080500705001c00701400030400c0c480034818001c5c0e03040c1900d480300040020040c0c0ca070f04108500008000401d50704c28810141000d81440311201014107107002001412440030303c0c1c3c06080c50b034000c0010500b45444007501c1c1d12214034940c0f00500c0f42071000190302c50b49a00258030500e4200002c0118900e40c2c0015548000c080c012400011301840e03410903540d400fa207601102e2185920110882230745d944d100f1035030790f008081030050314800c3c009000c201600100c20942003240c034103007942c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 343946142 1250 343944892 343944911
    0x415091a070c120c0302040f0212090313032907020708070501020c010e0906031203090a02041b050405060c0709180203010b0301051909260a11071a03190603140709 72
    0x60424114060f250202201189a004104010783c2110003564050410700c003c602d20301408000f9000104c00100c8003a030403002800780c0030003100312103a1403508081500041d0031750302c03602c2030b845001100c2880304c0700910312124180c629203500b42c807811155005010f91800c1c1385007a801c00b000d82e40014150b510540108242ea07030442103000c030844095400c030181e661180006440c145d80300c0d503524142c440c00414014140008210035003014002d41d014800402180d901c02011fa60011401000070400e000c1840701d850200c0007008130441800c119100b50b5150644402110704180d0341e281e070000703003031851821810280210761050030120001c004516103059060201c01030301c2c107980002d66440110000308043c503180791705e801410a00c62030700d810481010740401c0c1c0c880f040220200f810003034922031345000002c13003e058440b0f03150b04007000020f280251501e50006882c400c13192522180c14846c0b00b1692142c54019406903003070a0154107003801550810364250041d00c840c50500341c0f0348 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 343947392 1250 343946142 343946153
    0xc080105040e190302060a0b030a020d06050705210103060c030513020411070b0f010806180a02040c0e061c0b040204080703020607020d0b0411040f0203160806060415091a07 76
    0x141158030569010900403050000907040c0074070740540310440c48001840c0402d1660009a061241440d810104925895001003603a506003003107000f50300c5110b03c2d040074001480c0e900101d41014184c1402404d101c3c0d280b04088190307140c2c4881060780300c0c1c00801081800503c2c02074503845415810300b0030460425028106020142a5001c1d00490700d0b48001340c03864950780c040301d481a820940a000e1418945001f07610918284607a400a20424020640044111900d264405003440003000204480e500340805420082ea445080c00303803608102e004c88e101c450090544070040c2c60000705921101c1824404c642140d900c4a00881c41030005201c580f600062201c2131ba5011140d2503112030f180e00c00104900e0780c0500041c0785500031824441001034041411f180307004200c4042c400d079280c1d0b5130010300700d0004480780401411700d03064072180076001e1507008e60490405414540f404d505c603100003150030b0a021450000a820200800c81c901d40600d00e04203a00408003c1d41c40c0c13030010384a9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 343948642 1250 343947392 343947407
    0x1207030206280c1107050301020906180402070b040614070f0c1502040b0c07030c150504090209010e03011a0a0f063014040302060a050c161707050a03120c 68
    0x15102d99030040b040580764010002d80c90722544405901c01d0100324000c46000342991803081c1001c1e4940320702007001c601d51070103001351040b001b8094050b9040401c50341c500200450201c1c440d542040c0e08012100200380c2c03031a4402c6c8110b00564001c5a014880c2da0403200c0c40a00030006000c00c200c2c80c40751007903030307910007859400186c0040c0158281003004c1e80450080c411503000400c0d01400140403000c80001281d030034101c900409483c91007540d204403100106100d1910f070000214100410700822026902802d40c50340c040c509a4403c2100c000030038219070050160340040b012020502c43c07145440c2024101a000c420b49122860785440c401401c0e040002e440812001079414440750940d08410880f0320701e100681050010880e100c0903117010300801c1c2c0d030650050041d14005800a20130740101030042041c0c0b0b40c814039110410180364540c410f526001c540803c4c583c0e0f401200c0c10f00c0240074001c00c1c0d025401406220f15145000782c003041e100c10344809001e00304103030071b0003090300b0001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 343949892 1250 343948642 343948651
    0x803030a021b06090327030a050a1208161d0d060618060b0d0e120406120c0f09170307080f0309010b030604120e01050f071103010b010302071e08071208091207030206 73
    0x502c40300580660035400d065106c8198244c0702d4400ca4000b4803000080420006000d02240881449015030132a91200102c44403100c0da0701d820a02010244110407030008032549040e40344104040c400024000300b10402d09a42d4103459240034001c1c0e25000c00058074002401b40b040110b2494146c81c140c0c280183d450000030180d441840c2640504240180000c000680310490754498407071740b001d042641090301044260f442c0c80b0600c4134850144040c0641c1155507124074031580d19008a4001c0d41000b811b13402c109000a0103400001169000038215654054a0361a2030f894400c2490782181c0314504601c1c401d5001c8410300022421103000f070f8004240901e46480700c500c80360010b8600d031251807140265420002100020300240c492625a01c510441c0203004401208004406074001e800c4080c03d029150003100807003000c441c02443ca43c6100c1d82e000c5007842c0d01520b0700071450401d152010301040382201001070406050103018420b5403807a14181c200034560320000e60303601d802070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 343951142 1250 343949892 343949917
    0x6120304080a0b2a0705070f180504080409020a0507020301050604090f080903030f0d0b0111030f1b010f0e0a0615180b0102010e061602060604020301031e08040803030a021b060903 79
    0x10030059100e4004089401130000c40d460300c005070700004d6407860703804100259028081c114020842c01d8840703002d42c04586100780d1140e4080180c411400050102400403180341c50f0410001034011418005415295900d494480d01c50b02c6a00501d803d541004100600c5145040c0c0d1a60000b42c8008150181c55001302840351907107500300101e880c501c41d030b804032140396070080341010300751150b80c20481102c0001e90303503224400310460f95280d4034002c100c50b06480c4502880f2047d903070300140207281c0810130400c0001c030700c80b201000d5002c101d800314441000182c00c8001d111007400101d002e00c0c00244d0340d0384449130540780ba080e111130309a6010080ac40c0308c20f44405d100440744c2e10035000400e0b217036824016903a140c24444141115031040e500100054000c0c40001003803480c00e882940d04030ba4120005205004d40d0003034201c4c400150400885401c40309000111700c4143c10005580714140388400165203c80c040c4250207054418058038209900c00e000704514000080f003640e01089880 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 343952392 1250 343951142 343951163
    0xa080103031407330905100905010914030a110f0d0f0507061415010309080703080601110304030b10120c0506090616050c18040c21061406120304080a 66
    0xc07070410300c034000d00500084031004900c400340c0181c2130903d000103c0e81c180d114043c14040c244038191003500801a10b190800f440c000610300c2141c1049122034071a03000014000800d40e940341403180181e8801409034000714a58003801d402080d40344c1203080c100001c0100203061f4260036500c18079002c0d6001001411031007114050300400648000c2030303001c8000d21a03901c4100031040e40c500c080b6090070304201c280b69070003440d501901c6010311140d00010241d20342911510141d441031030140c074560420a02d05401c1250400910150001e54403411841c2010306080721442c00b5501260481c0d0440000c00324890b0014841100360800c850741500d51684581c01100050b425000750381010010307500180c03510040220100c0c902c200003104558401300e8512000190700c80c00030894004052540ea40d40034040190b000000c1d03a10300c1c00403403040c0403043c0e1a60356141a1040d8280c4050000010001d0010a142c41035210884e090050700a41c02c151030000440d0342da40c01010040c2c00c1150a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 343953642 1250 343952392 343952417
    0xf0a0306050d12020607030c0503010e100b070311010507170a0b0a180b0306100315020903010b040f0905120a0f0806031005010308120618011401020c1e0103060b0a08010303 76
    0x80d04488000c0c14002e1107010712542605004400060300310340740c00103008400004a406000e4030861740601629500c2c0742c1144c3c01c000080303400d85000343c4014094415401e0000e60f030850600102281c074841d40c0d039520302c800c0c3e45080c10301f9100042d000209200f10740401c000c403400d402081c40da003c451043c0115a4003120300210f020009540c0080e40b44044001151107814015042610020001e42c01c0703d9855030703041c250390b010f0801d46c08014840e0042000107038092a1607000790902101c000c000142c4444032200050454031540310030748003191600c104c481848000c0c089070600070410401145801d0010700002c01c6a800c00c0e4900c424481c0350800304a0030b450400604054201c0e42000b00401e50712820314120a410044038038203201020300005031903041880400860b80106268080c481c2d08081c0030386a481244124113045101300160384007195038214600641004180e0017494000d0b82030001429200310303400c1b02502103010041c10171500d52280400341120b80500d4183c101200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 343954892 1250 343953642 343953647
    0x50d050a29011404060c0c0e011a13180b1f02032d0304050c12010b0d0201140c0a06050115090e06060903100e03041d1014040b060304050309120609030f0a 68
    0x3c01c045842500d94003190101e11203400054402c1214014145800029510300740820011000d0066021100820803a00d4500312180042c104a265203c01c9644c102d8981d000c5120f403403d00ca611801c00c6403240c1d41d1403618240740708500b01c020220030f004401e1014800019650340b040351414500350000c04240f503044402465010014100054559900d00300b604216a0328210901e000d841200140d6542c1c24146052080143d0b400020b44031203816491500150b40c0341110042d40e048001c010080300307840502c140b045103072051141000203020b5041c1000030040d02d4100c0414802c3c0120304005125403002d1a41d05030b40b0100444640d682d0385540030200f4103207540b40b4003010846041070041c0c0a0303e03a010002d841914200902566040c0a45042c2c510541c2c007038236003030b0740160940030900445240a14460198002501c086021116034000c02d8466004071000d54290b00b0211700d040c901d00c0c0050207144a40c0c0341d100149035504103080100d40364411200048483c440000e000120b060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 343956142 1250 343954892 343954907
    0xc080904020706020c0c030c0a1503050c07150c0305070c080403060203130803010f15050a05120603031b031308010509191505070203030609070306080706030f060312050d050a2901 79
    0xb0ba0260f815521480320700602c40c0d44101c0400b0041c401d002d0207101d48220300308503454078101c3e420003013402401e2340b0550055006000107042c52840072000c10200f0701207a40100326100740d2000301000501c1d01c00c451401011101c01800b81d804001d0221160b1000c03410240544003500e400100040c3d40c0d07180c2005500880411020040010401000010b2003032400b421880c01c0b150014201483c40318203c000b00c4141c0b003640d400703a010503010310041c0c03140c0d039025812980c040009412a4070302208615042551f003000344840342980e0000849921a10100321060001c3c58024000c1c0003a00389411905c2c1c650208442c501c01d041100700c111004d001c802e510500310480158020407060a02410094880e030088071118050340c643c40100d411b05200344a000c044850b500c0c050001d150505074224040d2aa2005c20102652244000b20204040180540c0701c6400c40c0c6845503500c01c14240316080e03480050108207840d01d0038051400300362071403c80d40300e000d481c12098480a000c03900140e81130b6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 343957392 1250 343956142 343956157
    0x8090a17120c070303180b240a0801020a0207091401060f090f1401030506030a0b0705090a1e03140609030417030c070e060127091d0102030405030904050a0b010c08090402 75
    0x100d80d80e014865080c105400a0503110302a45d818041142c0c8018141000728510070001d10841100c0002400ca01c4621700d2109100c052407540fa00c06100e00d0009900a111600500c13800d075030001d1240700050b010407400005201e07855040c012a4075004040102040502c0303450240841d144010308864070940002d405850031406038501c403901e50001e000c003418042003c5010902d0080850304600e000610400040d901240c440000d0755208401c0713806820500072542c01c0300001030082186140e40403143d0700402c2124200307041d10b1844c20300040024000803513580c140c00113024446001c1d4003004540035101c0080783c000140e80c440701018514840d6010841c0540510b200104a00740702800190145000746d8900a40030450640000d0100c0030100400c140120544100a10000c80e00408a00341078218028103140c89900c1c071a09991007110115099000000c0740102c5107400e00c28960001d02940302004403402500000c1e10000c81203102802094001c90070103050f030381325012a03c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 343958642 1250 343957392 343957417
    0x31703090a0f030f1b0f080a0c020402032406032e050d030305011a0f09120c090f090106060806010f0e06090409060b040b0301020c0307030c030306030b07021c08090a17 74
    0x4015060900509191a120f212400201a105a00b482440200500a105800c041e0820a1b822a944e03110041d50150f10250306101d83c250895001da9100e1002e0751180361005040080c00807008140301d01e170f24243c00c6261080d8024000c1c032203101d0002c009180100003004104851303064002101041184075070203107034070030181d2040008040c1c5c03503003000e4100d43c500c24114200100010084480c0c0c0654415500d8024041c00001e100e45003e070400e07540d0402540c140c410010b80e0401213502076030101c5a1914284c42402840030f24442403060b040101680c0c03130610820700f0440c0000705100d00b00112071303040011110132901e09966040855a190400038003c0100425500d0044013410404008130710075480c00340521140e04060007291200d400d158069840d100d52a50183d40d581c0e030409054040540c0d4141c04000200114543d078014100d40d0010a04100f2101a0044001c284461403003000005024401007904c00251903042d164000f1510345250401c01c040c0c0318a000f0301548108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 343959892 1250 343958642 343958663
    0x70e060f09190e190f060e030c0307030809010612080702031507200303040c0e040f0609081c0e032a0d050703020d0e0906061b0d05040801060e01031703090a 69
    0x15450381d58140d01d04600040c42c002d000b03a002d00c4030256250300b580c0d1550100301c0c81c144d100000107584401c03204841480b9420000c2d50300d500200315407654020302078000303c66200042500916400c588900e0f441034603940284181401c04000c0442c168114000900c0703160b0115003c01196010b02c040c80c04044401c020042c0c1c7d1a0000e4000c1c0b5000718109410901000c00405a403005404030071030b44155000981100d405150210ba000ba520780107109072001d500304070610300050002d0044255450203013001d039490f0910303420886050f0101207008124945412008450140007100b540c00d211084815070f454580c0c010b0300c803582122241140300c100c1c013070441c8074040d45801c04050199580a80e085440e1420810001d8070800e840052081e8001e0004002072800d2030400000d1881c2d4000d0401852128251100c03149414880504e0750701245001c80d05014000c02441010010078951000301025459616007000d82030031b40b415681c1c81200000082c1d4069000c00c00d02d00d801e90310561915 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 343961142 1250 343959892 343959901
    0x80a12020f1c1b0b0619080105040c140316090c020a02041b08010b0412060f110d14090325030c0206030705040f0b030103020627041d120c070e060f09 66
    0x200300c071944200c0e00042000185540884000e005400080b554844c454102c00c0e11188100148010b520f88514034407510401c0108030404280a80c0e4082d0b841188181c61660404016402454140140c540030350b014018110386000d140120703d086611801000425040f242d00407402c0001203003000c6d40090424162007207500103110155000d8a070740d5200300e01070341c0303551581506210b0340c801c40b90132045000201340828016807000124440140d400039501e042840140001d4110710b10740d548240c0d5907a020542804020314086d0f03c42540d4010310300e0251020f0500071007001d41200350702150498083c101c1010b0007524040840d9030014940e40d1a4604a00014a590700c14054091000041d0300c0000b041e030ba44e4010390b0b050703c0e4002c0581d030a250341003004c03500d42c240c44004c01004507800d0382001c056484900c900320080903807207a001210b240703181c0c4040c5408039001903c3c81d9020200550010103a01054039001d507602207104c90529154240040d040e40c0160b491203510051010521 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 343962392 1250 343961142 343961173
    0x7050c07120203060a05070c0809040f0509250f0608040204182003070515031f0b040305011505061b0106030b10061d13020c01110c0a150501080a12020f 67
    0x7036400d03038800c5045070150381c2c5800c101d1042e54004d441c010702203080c101003000052941c070003400c400b90010740002184030312012904d098900c2905c00d034083c0d4104521940442410780d41c0c2c5107110030b001d02c840d211545090054100901c481c410349041244840201d021561260841c0c80304501d42200d9072045450b0703041142400862926070b01c407503064920285494100859100c0c1102e40042020044888138150280c5503400201720300700e030740b101c8103440c4805c109800c5c2c07101c068841042d119417124150714101d0308568049103070100055065108020f26500d00085031a40680c040720050300104c00c904442c003402d4560401840040c030b8400b00710450b6a44120f0300120380550742c07514101c007018007041c0b50142e4095807103500450070501009610409800422004060f10000520212640000307500c1da0042a0440c110790480500103003400200e090307500c0c0c0802681000c00c07003541340c840011b13625000c00703a00820208044079074045440c02400400b0417040d50303c040d58143c9200b076644 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 343963642 1250 343962392 343962419
    0x40f0b0a080703051905010b030601030c0603060e0f070c03111009021323091e0102040303080906010f0603090c05040f0b0321031b04150203031617040b07050c07 71
    0x418003403a4203600c001004140001d460084a421601400105d55070400c00e0728003c607003000644656403114544900d64031304110003802140503d400d00703031a5007081e03402416180c4541c8000301d0014a141403080c1e20085000e02500100c1d6420041c10045052a00303441054420851945a0007502800b0307005410039080484841d01c21105400b40000c581c283c10211303000740a05007003038422000842e83c9080d1300207503160881e10400171914540200703001d50201e40e51010300e0341e4450350085005c0081640028103160041c03400b101602056042141740c01c43e070502c51045500f01500c42c410002440340100f207500103040040e000380400780c80403103148003500c4012034540c024803490380049120f5826a8040c1c2081c04040d140515580369440d0038079000e407600d45800a1060100b0000402014580700003518011603005161240f500a00c8080400340060a5405006e80e0f01c8184002180d0b118059a104e9032014100c074840d05c03100c0341221580686e2004410900c5504808100910f10560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 343964892 1250 343963642 343963661
    0x50f0d0203210a170103080307110f070b0d0e07030213110d0509150105030c130902060408030a1211030106050d050a0920040b0f0603060d0305120a0504031e0e010c050c040f 76
    0x20f40c402131081d100044a0050b0f07003403002418605062000c101903074072030f070b40080c1e00420800880300045032044d8000d007000c020340d12150491400140d00c0d80c4d08641b86c000d080802c81c0c200042c2c00118034580100e2500b0301b44407480b10440b952900a40e640c042000b090343d115014a0300c0c104428580445000e1791010300250841004030808000500c0d0310300000c00004500b4090304001d020055202548060800d10b4000c03a8070410070b102c04120380f50308001034000344038265030b005129610aa0103500b25910346c0d0000706543c00c1080184080c603000011a032141008803130009103643c4884015005191481d0000c00c40b5002c46c0350011071403c07514800c13901c5101200c3c10040e560090081041e003910003889181c000c04140001007491900141a00708107000303003031051401d0107881085509810880e12124601d42e80d41c1440103050b40039011a4040c11900c0e5403000d000030280e00a02000c1101d01c00e00d0411400f0b120740d900300078050000011644d4058418022403281c814000050404c042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 343966142 1250 343964892 343964897
    0x6030506181b03030f130801090602071e030203030c070201020a020d060203011d06030c0d05150f04030f05070b0114011106040507150c08041a07020612150109050f0d0203210a 77
    0x2101d180c1c0050520070070528038100a0056117040072514801e14144c000380c800d15881440c0d0328000940f00e03820b00070b00300c42034840e03034005a95403443d251031415401c030718000c0915403000d2048200042c0d0000100d03500145c10a44846c0c54564520040780b420010100003904a0b00740582c070340c2042034035009941620755040c404503042d0140015100c9411080720f205030701d94031401c41038610f818001910140700303000320245da0680051102c081c210000594040312403004545c1004245036100e01c05003e1400a0b01d08245010034136126401c4181060103650304904081008003003d0380070f0032b01c00401007420401c0d190b4031701d40303814442d84031040791044146c0340c040c00c00c1140155102d654000c41d02e42d4851011400c00b42000c441450300c4042e2101c50402100c10030443c809030380c6000c090840820750b400b40c607049162101c0105a0000070f8a0800c2c1444501002440684e039001c40280c001c050940b60301d040014540000307454480100c03c000f1002d00c000380a841007138990343c020840c1d40c0458 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 343967392 1250 343966142 343966153
    0x150b0a0602190209040809060c07090c0e0904022b080711030303040209010b0904150b0a020d03050c07020603090a0605011d132003011407200c0a06050a030603050618 73
    0x8403410303611010074224402d842a1481e201c0c4005151003121290082d00840c0d6880c201000e080200300d055210101d402c041c1d0303100032800c10a0700620300070341c04018010300d00303907603000351420104408850142c03000340b181c030020b0f940c05200e11580d84a52119900380b07111022132182800c000350240d0090304190303100000c0f01c55540030780c1400001c80c0d006990140c01c4a071940c2c40c104444040303030403010105900944541d0510035900c6449008000b07030180c055210b5a0300c1d1901d1001c0c0c0342c12258000c4509240c104020019044031103410383c5c55080e01641c00594a41c3c0d41d1803114104104100700804182c6404c001150310480c40e00101c2c594068000003030803075110000c1d4030f0008000030400070300207180c40440f00804a8486d40041d103446c1c0103000450070910644558040326802c48a820008032048060041c40d0070209480b803d40003890094250380b1072407004100c04a04600a10381072000001306d02c0b01c07261207a40705000668000c03041c0c803020700384083d81445840448201075117a01c1107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 343968642 1250 343967392 343967399
    0x2a0d050408060c0a0c020d1416180b0a0603110405090903040303020607030b100309140f01050703110702061206130c1706030115061b08031807271503150b0a 69
    0x48204e50901c5000d40f1690160541a400c03c03004001021045030014030039100014485410030002941201001400b4280b504000c8034007a41c803140195444858103020541c091901c0303c00030141a620b081c0703804101209400004c2d40c1d6031090b544a140c1000c00340003000300300c91011010f4401c0e43d03c25070035104180c4a002c4124280d40c0d101518548c043d5611107001c0701c9501030785c0022041449001c00a09111040b5891400c01090b480041030b1a5180d10801c1440c1c1c3d03240c818201c589903881c100c03c1c00c29220750089a514080c20304226071048040001c95402c0d9518140690350035544402030254004004d03004050b0907540d42003000c07500350100840c080d0315043c01444001c560741416490618a41002112164400703071052040c80c412115580105462200452241c010844411b420b9184001b240340360481a6112400841030191070340340c0c4000000c6110b20621140c100450202c0c1104c88545522038980c0c002450500210421556110207401514185204540c0020304640c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 343969892 1250 343968642 343968661
    0x1060e010503030f040b28030c0e0102121903060506070503040513022104080c010603050606030607050c2e0207060507121509051f0605071203020f2a0d05040806 71
    0x1402072022044134060000340044100d4401900408811102e81100343d001e10745120030000c001c2d00346800207521003040b0554140c00800e1420045400e04c000c02c00c8a20b50707408d110320b0303000c0e00f40817240101500300c240780424866042103001d40b200500e41507541a142c07401c1d50b1360b030340309114150180c28524000f81a085080c0f00b81c1720018082c6a01d5100100d813007000b000f540301c0041c4110340d800002d02ca0b982d8010000d2140c2d0000e9403040000b00064109402003525290b40103080404102007004000c0900ba4046a0700501502100e5007440480050340d58030003011840f1456042c1910208080c070501103560440c1c0c0c00707003196440303010003c0c60029043d000c2e540c42d8214401040c0d80080204a40800c0d540f2155214014503100740d4044628000360075201000e41c440c0700000c002150380000c0c05081003400e41d0b03d19050504629060011701020f000f800b604c0750020042c4965141042c0e803090304800360702c0c00d0003000c0c2950f82000080d500034003e50000e00510516101c4c6c03d002460400c4c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 343971142 1250 343969892 343969897
    0xe0301020913050403180f03022103040e04081905180102070e15011e02011d160e0a2c010b09011406090a03300216030b09150901060e01050303 63
    0x4101620092003482e440d2004400f0380750151007141000340302044169801d20981c41100038250640c040035603580b03513004028038400520500c10b00c0d001c51184103021a90008202d5085503031b1910401e0141c0e0707a508040800c3c2c050b446c88070485a19800411100c4e5130310100504c060702d1078180c1c0c41d4594141c1001280e4a01c490f0040300c0c980400c550100c1c1180c10982800fa42c2c0140500d0402c140301582415940301983c1d840c41680036039154589070100c01c820780040810b2000c00c0004008190501400e00d9448825104070b81a07002e04101080301020103401c52800b9111604951201860603102c4041e1600781c1008842c055207088250380d003d00d8800c0c030440c12290003040e869504541c1c4005c011090744101d465030f6100b130041c2e100200081903041d00d6440f81070780b04015505c800041948011001c80c9200c14411504a9015201110f004001030000d4030b80280151010b940d89450712803401600c0c2c2200b580311440c10040186801e4150802c00c2500e0160100c0d01d11fa0360fa810a1683d2030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 343972392 1250 343971142 343971157
    0x213020d0203071b151109030a0f05060f150f0402090603040b100506070804090e0a050f0307061103010e1306061a22080601030321060618050102060112260c06070e030102 75
    0xc803440440e0140e001000e1b0850f00c0c0114001150600c1c00c030007000020b03c0d105c180380003141c000c0150000c01d418080d0920465912402614900d0910302c1c1c04000741049c0ca10303d80c002c0e4803a2508001d80d29003520766906454150402500c403a6803801d2034203043c054000102c548210905a60754040303114146141074894582d8402c040c0c40c145030500f06038201800c5480000c00700b910501001a0100d42d00b003000f981421500c0d0041c50f41d074281403e1810542c1e003181c02117170b5840c0301017004210b28201076070150b1348043d1004c41c1540e282a14038017540a0801070348500e2080d0301c2c50300e55040c1b0042200082c00e05d0f03503004440002200c811001811702c051144908482c580040707004001103400780c5070782c80c210780410038540c0243ea114480e8400b111401d0b00f01e0303400070704400703c884994400b050800010b0718090009000384d6240000014a4200303200f0300030038001c066001c4c0486480d51500f640c0140000104142d00d80107074144440d9038000442d5070400180281c2c440c03841da4201807003140e510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 343973642 1250 343972392 343972403
    0x30b030a1e02060a121b0f034b1a060307020106090f060914041502090303040b031501090f03050618160602030c010b04021201120213020d0203071b 65
    0x200821500d508003a0014812441c91400300c0c5004140141c0d582401040b1300300e03117500d54501c0100c400c54813104450501500e001180384145042c41801c0d0849946c00c5850360502d0041400844808160075400700b9410411314001c09001035030f140400b900311030380d03400038205000c0b0000858020540640380c1300d07a40341289400da140d042d00c2e1428440c004652240351400045290759544a002044035a45000a65600c7ea5032000348000105c41c054000e00fa158800d2004003820700f130325a240b280c0280140c44400b01d5000803801e115803000d005440040c800650f4581d1a4600820b4855900e0611f2860b60300050000601141a260401d055000c0e02d030024018206655410102c01c1805034840c4280d000c0c2c0f013408148080d28502100143c06007440d0b501131a00d039501044001d0030759240d1110340344124014420102041c4590040b2411030f00d451055103050301c000d0010944911001c000149600c1c00003a28030346004840c0c000b14058101d0307688456803103014010a03000c161558800508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 343974892 1250 343973642 343973653
    0x3030b040b0f0d3008190e0d030b01021f0501030209090d0c0b07121802120d0c15090203070e0105090a0519090203070b0706090b0702060408041707030c08060a0c030b03 74
    0x42210400e09030084d912401500000c0b2010581c540100c541c40d200000024080b0420404e8001c140204060b1039101500f0601400003039681003a240c0005959207001c16a9844002105a00c2007020a02c001c000080c20b0411184519104000e02400d00041e40a1002100031a03160400003940c5a07040284d51307141014040765a07990f40d40b01801610320f000b0800c9490304559001a544203041c04100e440f058034040054500c144171031010a09800781250304603100c40190780303405c80c004040244c0c0c04160400510342181640e001000000c0c0040e4151003020700202d0307500d00c4c511609043e248100c071072200c0390303031a001000e0940e04211a01c4202c2d09004030300c2800108550086012188002c00f503880894079481d00c0203490700501d00a69845403180444030034850000401e9030440b9052010b0f01d41c0b80b0b46500c40d080c00d482184103035010b41228150f641c03102c49083c0143c030091644020604002c55543c01c6a0b43d50710400d90315042c1c210b142c121501d0f00d207402445802003841003c0c003c2e18 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 343976142 1250 343974892 343974919
    0xf020f060a0503182802010e040e0615010201062108120903030a14042d02040f14090606061c14010611011a1c060b09090109140c03060a020a0c050a03030b040b0f 71
    0x70b5505c01903002281485040300600c0300701c2e650b40c06022003040c16280203050070f00d0407801c451b0041035180a61419a49400018044074050503c1d030f070340c44407a0f5020300c1c0503500d40d40f4040409110741484000030540d40c1c000c2c048411004802907020381440c90080c40611495400803050020558000741207151050f6016011001403500000510201306907080a6206402103415a40c0c4000c40b140c1290791800002040b98002c1c25003500b100d1940300a0450f4944440418194821640040840d0070400d00890145400d60010748054001e480c0b11101035075116400303817110180420849455081612131824000d2000d0080f9260800902c160054440c07145c14102485240b64240d034030303d407529103480f4a503c4041c4941d0191540030000206c400c2c01c0c0c1081c02d0f8110305c000d001305140d008852680aa540e001888942110400310010b940d840081c03420f5a4103084848002c02c0c90091035030110626825502400001d84155000d0100c0d2815600b004885204a80c200e0703031000161081c0c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 343977392 1250 343976142 343976203
    0x100c020a0e010b09010806030f07060e19080a08071e080d060918080d020717030609010e0403080f1509040507030c0506090d0807020f13020307031a0d0f020f060a050318 74
    0x41d00300f000541502c07127207107600c060b00d420807583d80c0101e40441e5641a031503d0383d0910360503081c0406450083d503c541030034405016242da2480e44040e2125801196440a00c20303a441c45030082d909403107040000d40a00e02d0070f10b01d260030140d07a20010910f04900003800c5422802064010b607030290410b1a20a0b0681d00c2981d00d4008040a9070800d80c00e0100d41c0c005112a001744101c500c60803080f58491602c1001c018250105070424030074034112005200021340c021005c1034011144503041c0d5504d1f038480c0e030207030488105021916070200e102014801402000b00710388058130b01800000200030f440d9018800180f041c03490054202c4d07540b504440c045981c001c003811110f4802000a90113540c0180000c2034610800800003c2c80d50000903c81c5194041c07180620a100f004081d4600904103c001094007440400c00b40817400c0003100041195100940d000710744a0040c005615080500f0b00103006400444050182a0140d400740303902c0704000070b007800490100441304800d00441400f8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 343978642 1250 343977392 343977407
    0x3060503150901020d060b0414010504060c080702031f09060f05060d02130b06031602060a0504080405090402151c1a0a0312020a2001033611100c020a0e010b0901 71
    0x1010340b035542809404007015440c05690014910314080d25190340c100108a50f0541961865030306000042000708030480d00b00c085540215009400182c480003207001090514855000003011101e1407100161429500d90082601c10b00440c0200078100c50b480d031000445209450f030f85d03071044803200c0380300c0145800484d5503140c0311091800300b1810701c0d07030000c11416002601c03235901380c42c41e00072602d945942c10001141c0c41b01081030144454102a20f07800003903c25409103e024409031400507043d510380c001d041c050f90780643c82455862034000c58030011002800031a0300082c0c20b0441038000c2c2d402d5401c2d100c02503040200340181661640ea140c1072075241860014003940a2100c2c46004504000d04075801341030000a4042c02130f80340c400040464030308103840d510903168121402401c1e20500081100c0f502c0c41c8582c90140000741c2081e55400f41790b03d03815507000409a001103400e40d0b00c003600c1540341348240e5000c0001c0d42c507515000f59000d024010100010028071402082b0741c450402c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 343979892 1250 343978642 343978651
    0x301051201150303053a0f181b06020619021b070312090608040312050714040801020d0608030f03071d060a090806010b0f0306150408150103030e010306050315 70
    0x8101d9002c44441c40340700c4043d4400d5012171000305801e60345c8160940851421a5035032802c26a02c0302c890b0514445680d00b003401d0441d04d94910500f601c5e95069880040f00f004500414030b142c0c110780c43c0a2000040c1802c01c1c0380d012443c50130015090b400018264021107103104c100d1030360144644041c0080d0880d6003509110144042110003080c2c2c14405c80d00071b0750080c1a403001034401c51001425400481e4852420030082c4400c01002c0307903005003203446036140900c0100c1c050300c1c1d40300200c0d0447c0052000c9401d52400180024500340d0543c020203020340920300a014040d982c0b28400e03242d0103040e006e4054180f04100081300d0521442c084850b4540300038080e040800414003003101c1d038002d041040081500d000f010302440740300300b00050040c89240510b41c07030420651422225408003a095600410b1290000e40d11a4411016140600010300c206c840c00c4d0005405803c0500c003c4c4815408200e00c0f1030101c2c400c3d40310380241e00a948001d4000c007501c000752002d06204100040c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 343981142 1250 343979892 343979929
    0x70308090d081c0203060103050105121e100c171b1e040b0703052d041e080a030f090608040c0b03040204090206030109150906030302060f0a0e150f1b030105 69
    0x6030410b91006100500c0004100801030726446d21500140803504107030407641c441d260000d090300510200140b181d442640c19a1404200b01d000c1a00c1e9182c1400880b20700707080c50402c0410440d4a0340003080804203000625620019201c009807102c004d16220342680c4542801c00040e1105640540c401d8a80300b03803103117114901079440e10340c240302d500481d00c118006000000c00013075407031003080000c407002c80403002d03121891614401c0500d24811072082100802c01d5240e16450724007449002030052034002c0c15150b000b01a8980101182100007111010079000306000c0340540c400c54100d441070707500100c05c610060604030320007403c0d04000d2040f680103407621308441c016210700c00554020040d04c1e0001c104041681d00c840312401c3c0079041141400c0c9006020400709034001080e6403c45000584000180c03900c0f0400800780c0510103a60519116688680d0750340c1d048182c100b8441d200d0f03003240c0d041d60f44461a6050360405c0e0509580d10a039003e00c0140804d02c0c0c803130403901c0400b8080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 343982392 1250 343981142 343981147
    0x1e0a0e071e05030105070503060f090c0919050904031106180a08070204021606060906060e03070e1308040b09010f0201180813180e012304030e0111011b11070308090d08 74
    0x20030019080d45c0084501c003001031300c080244405414841c0948080d00c1c003c5402030040c3c0340000b0a00c0ca41d0054803003541c8103400c8200c1d10950404050f00840250101510b40005403605041c080e2414107039400d20545881150001144501c034016000816400740000c0c0c03030f42042c0ca4864a519030807540c401d80e03102e5400c00031129590310603041030011502c50400410550314145819040750807544c0004180405c02a15040716039002ca44d420503904600e94030407041d01c1d4441030500a00350901e00402104001402184860669018201d404001daa8a14800001721070403400d0310110840c6200c1031941503801d20010f000c000c09031450704464482045e1032903440040c0303644910311042118805560354240800010280500100112920704450545011344040800c285000780003400b00000d56054924a030f100d03185102071201403000a010745481b40c80d0f55801400d0901f450404540b20a107205900480402e61070101e0303401060355814070041c04180080c00c4900b460494810004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 343983642 1250 343982392 343982399
    0x7060f080a0f06051e19060903140114191802031f0f18170301030503122d07110715050904110f1305041107291e0a0e071e 54
    0x406035195000030030b125541c01501d01d901c0c04d006c1c441469505850a24480050520503690003200303050403658030920f80f52482c0c2c4541d030420b0050641c411211410009901841040d17450015541e4403414401c1c0d041054004030201342e0b05405881900079015000405041c0018400701050411400b1040300840d003003458448110489a5604500c0c645040c0402000c00b4003030b11400000740c44002c085c0c180e20355411519007950381c0c010b00b103d0b141d04020400004440a82e1179440042d001c4e0742b48001804460092030410411208650100008400b02660307128044001440811030303410344001c02d030128400c40110b91a03800560090703003281d11a618003280c18101c1c03009094a1412002c55238960100301a902940a41c43d0301c5140b04504040f5072500304800c0104458500b03034884244d1545e0703205942c410300390560042682c08800005401c1041a45c0c00364140221230030030326041e24960752a10a80c0c030442e070000d925003425900205052040700d8404504088e03e040006c295585141e8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 343984892 1250 343983642 343983649
    0x109030b041e151e0209180705040f09140f04030801051005120a0e0f0c01080c091f02010615030204031a061516020109140f010302130504050a02090307060f080a0f0605 74
    0x210300d0901d468a84e6440e4041182941e00f56103261041110340b003545410720610000d03441925030a6211049040d5401180c0c05a010b0404c03100103142008003002480d582c1c5003420018002c10146604105640000854210308442c045118030b46c1901d40f0b005070303401e02041c080c51350340320f0303102c0c0013840410095240d0760110184000e00c2031a240c400072600344880b100c0c1c075052560682d1003002c1d56004101d0100582c1e00240010742c8030000015080e00c074001c881c0001e01180c0400c4503d900011501d03c10041c0170381c10f41100c2c003a900c41090019450009075012001c1740f144d80b1000d89003544020700851886103684040b0342220b4024440940f450495601e22882d034801c40100c218095800f202e18119608030032020014840d184201d040c0e070703c24001007060050300811550415a0020300903a11642c2c10500e0805084083d10401883c58aa00c2c0d110003913102600c418441c2c0302d0b461000503050712500c04c041d4400003a030354054003502c400520202802c0080600a440c6841d18002310303080e01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 343986142 1250 343984892 343984913
    0x3200f010e061b1306120603140d030c050c19140706020f070b041d040309080d020a0606091118030a060507050d0606230d06090606050c010b0109030b041e 68
    0x10881c01c0642034504045444503d0a4a400500240e18405000c1c01d4980360403050000111551802e04d2245071310000040e4008002c07980008200c2604c000168503c0080010b4000c0e035a00c0d143c9040040d802040c00c15185409800820b80a0350700448210202c0035031b10310380325501481068001c20003070340000c440341401d032150402b03401030b0300904126001400801222000700704e86000140341030f00340741e854003503803640229004400b12010b02140805200d42210380003000322405550444500300e40094403424040016a041424801c0220309000e50303105682d0200460f0440390725019110710441c40058001d814190300d4051407025001084550140380d110b00d4660769110395030041c05072214120fa04135000300342046100131840740354140c2c2ca03101750704001c10121000d880c0c1c800300303030480043c2131550020705229040140c00140d43e07802034060440c0b0030f4824024032002d420b980044a1440c0b141c44003030040e207580c1000c02d0209082c0c02d0741d86582c0294040900b60002c00761100d82000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 343987392 1250 343986142 343986161
    0x70f020405090a060c05030606181815040501090c0503131403070b0609100e060d0204060f150f03110901030207150603050f0c12030a050309031318050703020703200f01 74
    0x83d042040c84008010152048170f00c0c440d40e0b41080b034110705140b4080340250003400c103082001c0c08030315050440740c1e8868081c0d41032004000c10007516841c080c40d03941889609441e4041c0510f08000c0041102c180500aa020b00041d41c6e40b2242140c0d034100c44c4d0342c080c604804090f074424281000d010380d00c4200f440181a01d5005841c28221828000c0034480f0500b4010542c4940010244040c802800e00c10b040b25000b1200301c9a0030b10b9550640001401010550711002207401c141e5400100b14002440244094010340c0318100002080c079002e8090300c440e81c600d000c2135901000703402810740c000d9010304a030030702450103e9a501c1ca032000c40b8040340c80541081d10240e01103110591010b00401000c9094030041c1c03102d444a5510401715540da0003031040f0401401804030005440000400a0b100d00003e141040302c40345a460101448012075400710511140c01c081c00102c0180c040c0c001c40300c40e19403540c1c54480681d5103801e51503e802e440452a071450054103d2065500703000d01540d44035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 343988642 1250 343987392 343987411
    0x1103040303081b09031c0e0306041b0503032b06030206070507030c0b0c0303010b160c270615031509091104050a0605060304062003160e1c0206070f020405 68
    0x10b41003820062180c1100c800050f4107010041081115680300820f907210032000c0342001c0d92032402c01c0c41068178010445040503030188030320380401c41030ac03040044400e035072081440310032203250300c41090644074421400c02242241a40c0401603200d25001c01032a041a0000e5001407507035185d0380010143c0d8410a01a83e0710b07441040103105200d510714440c030003080c50720100751920b003c500d1255102c1c00140714001d480740020480e8068071007241055052594440c016100e041c0d210b02049038904200700c0c0c40042e00d20550040103500300a84204c900f641d150020002c141040200114042e11050891b50312141d9050b1700050300742c0c018000c4603a20780c0321b0240e10070b4505c2140c0070301c022a04c0c020141054903090060800c2540c450108a9400c01d030840004210341c840224805035034046030484620f503131400030800281080701c138500e00408130361340d03201e9264170051010008480038036010401001260444140149030020050040b544101c075003e8111085800103400c98100b124001407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 343989892 1250 343988642 343988657
    0x1317030a06080c01120f060306140103141b0f120102030903070204140c04120501020f1b161a0d060f090b0a0605070b0a02031312050c1e030703050306011103040303 72
    0x8440d00316001d14009486000020004401024002041d0100034102100d032142d4800d1020001260341d003000014540102c41403000000c0c03100c545450900911041d10b1006204450403075245011403419040d981d0000680c2000c0e100c0000c11003002600c04444d980900d441c40011400c48080c005107100b0f4000f1406107440780b144d40140010342e03c469605500c038012140c00c01010b00c4444041d1000d031203000b101e007400c100052074124024400e454100c022a10007182002c19441ca403250050048911019104484480d038201d0010001c64080d01024094607004540c0611400001e009000041c10000c181c2580c4c4e980c941d00081c07416002203113110b40b00c00c81a8584d06002c201000141a10700e040d40c6040100e40ba00e003107543c006030642c0c128a4001010403d914500c011034080300707802c0000b209680f1030180c0040d1095203c8102c40e081ca01994401c0f02c866200c500f40704800e040810041d515120403a135049400360b0000f0416070620400c101c50101c46482007001c0d101542c400d80f02d41d00b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 343991142 1250 343989892 343989901
    0x30b13050d030510291308060c041406030402100f050729090712020d021302030a0504020a060309081603090b0307020a17181002032b05060306130b131703 68
    0x5600c421a5080030010035403280001600c166450301e0016400780340305c00d481e1529160707500140300368550741c406038451103000c00340103400000d50010000c5070034000c014958071407000e0a0240d54041258041c2d0700844032440941001d0051110840c00d07103d901e0070070318020303040c0d60b48410094102040025000050201d64040d4804071419402100710f40c000c007425441d101c00c0c60880c00c2c0e03801000b0b0107444c0447c00d0008544503010242e40d81c4491500554580c82c101e1010f030000d20044800740e12441904800054160280c0320700703900d20341c1200e03c0c1803030001013072150000840c10321030032000c03c8480c1c580054900024800b850291406a0143c50070745160b00f00150000c0845400c864400327010452000307500070449400f0398500d010b640d10b0a0340040d03410301380c3c1540620b006100b00350011351101c2c00300300c01401e0781690031000140c042142c0c4d1110400e069564108549406400600794941e101042043c1803841c1c0c049480301041d0703003195250703641c83c1e202400c1c14411002d2010120070310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 343992392 1250 343991142 343991161
    0x1009030509060418050a09020d0312060e090105072c06070213060315050a0b0609121e030c0f0a0c051c020d03050405010e010c02130f02070c0308071713030b13050d0305 74
    0x2e500f1026040d007e0140b104a50001200510800c10040c10b0021602807040d0074170454103c1c0e0000c1176a2090102d9621f0585065800b9110407580300c80013507921803c030340004500c1071b564501132110024051600f280402400307519401402c003641c0c4405000703840c0703000490314001c0c2d401039841913039140307009062211160305480b80a852680c880e4101059000b40342c5031001078500b08002100e2030303c0b2504210003000d04101c100c0d400e4043d02103003000c0340c941f00c2000100030624a1280f030202c1d00084c0303100030b1b541e450b400b0340391000300001d64000d000c0003a80340007050703034140d003000d0701000c90300c1d0500d5800205440307004641140070982c0801d0800c12507804c280d00c4141c0d04821308107000d180106600141000c818a10701030304060b540c040c3c6c15101c038855416078540c5544990021803803600d905184840307822003107048403164800312050011118000c19108413902c04402120710505580c0c44100780c01e4020095070840480c0308002d1b000c5902004409045006520002164208040380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 343993642 1250 343992392 343992401
    0x3060114121606020a150b01080f180a0b1e01050307140a0f0f0f0b030603101503050a0501050f090304081c0c080d1b03020a0519020312010906051e01021009030509060418 75
    0x15031b2840c0e1034541c400b0071030390300b188010360312107070b511440700c0196640740b0b80d01445034081c6000c0c4c105204182216003000001e040750b50083e0740038247c40c92085101402d03400d0074942402000d8054112450402120ba511f1007036000f01000200644030480c1c80e2105d0101d10a41548441a807034a202402c0040041030710007800600410b180081c034628203017012039914034404294802c00c0380d4131900365050710b20940070b41002c0d65010301607a10340c510320b04080d40a03041c203403120500b0114000214185141c000111001c03103c2ca03101511051005024040b25081800240020300044c0042c60001544800003466199101c250001395000610440b840c9c140d03280d80008281841008009003d0740c0200a4810744107035510040c0d0011180c0000301d046014107280c24100704030381400441c0c4408146c0140003a9503056443c1685034026900c88190700f04102d0a45002d40c000d1b010740c424040d503640020802030b000f800d00c030f80b03041203407804078040394070607440052a114010141e0b851030009003c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 343994892 1250 343993642 343993673
    0x17161707050a14010e010e03030610030b0102060f09010f0207030513060f052209022802030f0a0e150a0c02012c0d1b09050403020c03060114121606020a 67
    0x645400d06203a99240303030703690880040103400c25281c2d6054480c6440300350400c402607000c801c001d00040c80b0a4015950fa40c100b41c442c10720038000d8802d00c061141c400e02c1414a40c1c40c05034000e00094891302c0c801003090701d0280509141d95250180d0103401c0c805400280442c0d4170a940f0181e60720018245900411215040744c0204004010002851a0f10400b5184641c61460300060500024924926040402d6102c03000c000d0001c2805007803002c8070f000300e909503100701c100e1880c040021402240c5903c00e6185110390711009129004030244100b0071440c0d0000090b103030050b14015014520280e4001d0203403070b0000340c2500e2460b01107503400b405140c2d07099400c0c14101c0c6015604042459034107120a8507030b00512900110340700f4000408030b400302c000141d400c916821600c4819030700c05000c08680540143c42410710122041c00c0c0001d0090403107210b06041c00c3d44c02800c1c810091a083c4c9107024a5071032280b20640261180c000030650000d03e116002011a11ba0a25000541d135000c240b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 343996142 1250 343994892 343994933
    0x5090a030c0503061602030d0e010b030111031b19050a030e0f0f010b0616030809100515090609040b04060b03031b030d0b06040b04120819020c011202040503191716 72
    0x200c40a9025000000e460718181100c0002c941d127200c0781d807483e0043c03820320030840e4150300704071449a401e44100300550080b403c0c805110001405c5140c00601c40c41070b00755444107620060b00110700c040c8500040e1034030190a24000c00c4c40c0c04020f22261a0140107000c0c001075030050f108112a5540900c0303501c40110050340c1c0d090500800b0f0307e108040c1c05c0ca1000c05028032800708000f6407544810301443d58841d440e90001c00c00303401d15010807038a40052176030050040c40c802010440ea4a800682e41d4412580504140042d580b5680c03200b000c0e021241d8020341620051016140c90f030000e1580b003a8030b42c1368500554492241c000d0348400d80d100d40e02c60900900c801c000c1849811030110840b800d503105442c00c0314955450f072070812551310818800003004c008030036219564643c003049008142c4400d984004c0050003c10f848401c81c4180d200d843c5c1e00d5444600c0358004540e403a10007509580c01000c401c40003000386154030916511003e07203100000404041e0008000d400340c603103401d001d60039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 343997392 1250 343996142 343996171
    0x51005010c0309180e03040f08010b01080c03060d080418050a0c0e0109060e01050f04091e0204051305150301090b040c0b030f1302030705100905090109050606041505090a030c050306 80
    0x50b240940601d81c2030190305843d102000401254840c550000e4403180b021904595490b0f030b40e10080f0994540a0056440a5003002009146584100c0446020302409007045107580c49240030401002a070517411103018000b8800015075001101c079201042d1148c2b81c012038076141032201107084030500c06180d001e01240300c2c1d94192990b4419052003d65400f030406001d0303a00e4550050311a405411445d80d20020009400b140140c00b50b00015074950b400d9840c0c20000d12100e000700180c0c0070b1406040c4c0c20030b0400802c8803400300c180d040580c01c5000c0d00c00091041c041440800d003500c0241c8820b488503020700041c442080940e1020000800421042c00c1c150300302582511340140f4058a51074081080c8200f09040d5130f010700c5040000c21004140c0d43d10784074046009070620445100c0d003403040005800014094032140256482140c00601c000c0c17525003081d41030900424441c40410801406111403c1c80307484612100c406940036600142070145450201850000c00a240c00c1189404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 343998642 1250 343997392 343997417
    0x30531120c02090a0903080f15090106030906182a0317070c081f1112040b0603010c0c0f1707120302030f1302090c0d11030c071b0602031c09060c0305100501 69
    0x1c0c407c90f00320001e0007901c0a1501c0d904074001c03404810021040d0300c0201c1c1f400002d40303a90954080d1a0f83c0e8410b040600c010100e2440404020411072005460000d007454644c10081d0361614039111050b84400e0f90804a4a030b440d000c1d01d4110300d201d8441e24120000d810002d011412a8141c010488800203141418000c4222062081e00c41e0f540a900f903107410007217024144020076601001c502a0701400103290504180300100c00640307415010f946807811310320520f4855141036241c5074100c11030f40e90505055580702d0340d086100c44003800c0d5140c240100e0b40090048280c248030350840d541c01580702c0c2403100c9003000798140501010005229025000d0041c1c5a18203080d83c045c8107240c0040e2034059916100019105082c050690300d0000000c102400b5104130142071814004c480f465400403801c0c0300c40c0c0f6005000e00892001d40c0c0300f4020070917a00c0059811100e000d44440010962503400d07a68581601d202c1c4c019000425224003c00000d0f003510300309040144000d2130303c500c00e03100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 343999892 1250 343998642 343998647
    0x30209010503160e0402010905030d020109021c0b15150d1b03050105130e0c04020a2708061911071101030e06160c0f0c0f03060c030531120c02090a0903 67
    0x2034604c0703019160705000002030107680c09003800d04002d10010b0103891540804c0c0e14028001d0900c5401244520000d01a400b0201d003003140803500c050344079046c00b55030f444030200207228a8440728037a0340010b550741c45050324a80c1c50040c0400c503a540380c0120380c51045030345060080500441501c2094a0400100800e0341c4146403074107041c4c1045400284025032605043c00c195914001940250000030f00398241c035031045004407403094244101c11115462014091000c0017072156030859031142012403218010700880c84507809203044000343d003a01520b50381209400002c1d055540626180c1100c0c0c59503094080c43c901c2c01c031110042c000f00c0c5032498045084d9685d2882403401c03c14414001e034100510f840344203c5040e00481c1b5840385542da40b0303c0303103000c00b201e0004481e01d90502c601401018000e0103402e0103006c1c40b260300400544841509c200007221603004008a20080c0c0c4140d02081c208080307036010001580c0c80e18150900303030040c000552001b804079000b003445c001c051070109a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 344001142 1250 343999892 343999933
    0x5060310120606092f0909010e18060403170907080d030902060409090503090111030403020a0308091f020609150c0703180e15091e01090e031209010204030209010503 73
    0x200307000503641c61000d0500b0108020022a0040c0c0701e01032810b016048840c600a145d15601400c0305261100440d000c1080d01d61741c050f00d540a5040784070070005000b50300c840036406174491942801040030400c0400b610349029002c1d14141e0100720480502c5581d17101a102d02507020036410010100a49094003280c0d6545c6c82c039420800301a0b54103c00350465031283d08840041000342c4092004003150b00704941c40f54066100140030417004a44050702c0e0f44080140c80c00c1f0380e002130903c0f08091071500c1e040390750761280e803440c0d50000c1000e079581d20844005407001020340d030b20b078001e043ca85051101540380c42080754170400358450200401c4602507050b012980043d42c1460540883c500e000382080c14428142c1022a080b0300000c1000801000c2e009840311602d001c5844c42d60549841a05228102810010301030f50446000144003000d100c4e08600046050041240d2902500e0109918401010399103040c959400180c20000e5281102d091400b51200b01c0c09010000003440c04500d03043c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 344002392 1250 344001142 344001149
    0xa0308160e040e01051e04050c220c0206010302030c061e0d11070803040b2d09030d060f0513020a02030301150c080307050d050f0601270807031b05060310 68
    0x4000c50140e448540348038161101003404080c2051007039100307459619020302011142e0810b0354a414140e0829028940400c1c0e014070303001000351061000820520014607050300403a041c401d14003918400100c41446205601802e56020741080d5045204040c144000030316160720619091280880c459420002081030b4003d68144a0b82d8030040c11490024001c881c81150030440c0100f0440144824000103621661103039540106603a6024174070b100c5040c82c0c5090a41d50603200b200a0707100d1071082c05460b000748015085905020040c0c510f501a980160400b40c1d4201e00342000304540d06094421030702400b0f0807207041d4201101e041c00299203020503c513040c012540da902028409009441c0740d902640c00404c0b4a40c0c80c41d103050007800d01d6220b4030030300080c1c070f24040001da174250403804160b0003810169948170b427180c2d82158000500c02070382180504008900c00006000008000401c011440750b21441c2c001584c2d075140350f80c0c98171141c0c08240501320070020400c064109950344001d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 344003642 1250 344002392 344002411
    0x60305151e0303030103050d020c1906050d060e01060e040b060a0e0904031e050405010f0f0504050409050712050c0102060907180f0209150c1006180e1c0302030406060501020a0308 79
    0x500380c14101c01e80c4003004071807075010b00000001000380100400c600c41504010b40031102c010150b0740c244088041000100a40c801d45040280b0100e4480c07001491070844a907404245a42c40b075220210300c0c1400e900180c0482c0c01809a00003c0c200ba0090b5940340c001201d8040c240007200c400030f0907111105000c0c81c8240a0300d4006410980240c10700311600700300304064841500b544502a115510a019241c0800c2d58400340d0b03c185485030724041c403080d6081ea5018185450308080c0000340600c1c00003119180540c40c07010800171a42c0e074a99440c18000c50042901c0c0401a001908106010b0008405500320f0801402107140e03000c1c010200d601c002785d00083d50542503a00c100207004000009920130b0080c19414900f0807400050300d592501f580695928035030039082801214030138400d94100130901c400e030304612615139105c034540c6000401510040c030388002c00345801790400642d000200ba07006c010b2109210f028480d0b000540001c0c0000c000c604466240680000002840d0001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 344004892 1250 344003642 344003659
    0x5150a11010c1701052205150319140604080a1206050d030f120227190306140106030507020316020f060c0601030b0903210a0b090c090a06030515 64
    0x10a40300d845191000d2081000802204400c09001004803007100040400300c00d02d140046050718011200000d072141c41c1c007803164540c40c070101c1c580182200910420f000b100809104000391010b20000d503c038400140c0741d2026410b03514043d00703200001c2510300c02c9540180200000034070580111010110941400f06101d00c0742c201400c081c0410383c0120ba00302c90b4000c000b800305908000c00f03000c020f2440d16121700901c0112031080c100d000b0080b10544140d249098491448003115243c444410080c0400315005140d00340181418281e80c0116981c03a84e44080c003901405802c442d038054241c81c074051005003400d00c0b000350389000d0030540d1000e0b0030342030103c5000c40d034500502c0405120040e0400b521501c0459181d07442d07250911060320440514400682d400c10007004540408205280c881403002c14400c0d00d5450b41801400d045105903a5440c040d002d5941d02d9005200e5912510b5150396000c40d2414021700f00384c958800300c18103007408140901c10115008041c0e030954142d07112103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 344006142 1250 344004892 344004907
    0x108011104030b1f080c0f061603080907081c0e01140304141005090c04060503121b2109010e0118050f01020102070f260a0804060b01020c030717160515 67
    0x241d410904130018100203189a000200c004e0041a48240340e8011034030f01580c00f82d40700c2030007da840761142c2c85141d524100a6440080d0003510740c950050781c10340480d0501901e60009501d01004102c00c0b410103861006407001d0642d00040d4035001d80401c0ca8000354500c4103c07641074a030f00000e03100421065400340300d000d0100080100c110481c000410a00c00c608100940503103464002103258080e50801101103045d05000410141c3d108032400443d14050499241d0210203200390b60841041c09004a07120001a00d2440403200141d013104103551036070003000141c01403402e80710107410f0100c08803002c48070030303501203032141142c90640d91510302c00800e90040740244603850005004008000700281801140313075003081c4116100305407514400d495000d4400341d01a1039551400140e41c3d40c0040c0005140307812204d16000180103c0d1102450040003e092089540151010b030304040c14102e2411010020810501c1c1c1c4a90441c0d0b1080c1000007284800e500c1841074a5090030008210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 344007392 1250 344006142 344006161
    0xb10180b040e1204090b04021908040f05060c040509150d030f030905030d0b0405180307110a0308030a0905010c031a040b03071d071e231309050901050108011104030b 73
    0x808070b5050241d0302110040052100681c21a0042003402803400e5103030f40351810a48200c031400900d030080c0c04000303540c402c0c04031000d10005004032031a600d078040e41c0c800243e04100a41c001c980c3c5000050312141440b00b40b0100c40e800800c0450b89205103120080303680c03900e0300442043d0350035181010540030404402d802070008010020a580310001d0038621102403039109001d1a42d044a084c003d548a041001c10031403501c1c1c1810a16030410400780c3c0010700179810010411202900c4000c1c041d549407140c00ca01e03002150908000ea4581403440c0400c0001e12070302d4260803050500700040788842442010368200c0000c810701841d5540e40c60409a5400c1001000500a81c01514120384407c250046095402d86048010541900d40c620b0024802040c04450304010364070100c10b1191111446004509030340700c4000a4810814080e0008600c080200035065400021074a800d01003121401c4400583c0a411542d00d007108498181442800300d804403504070f12880040e48842490 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 344008642 1250 344007392 344007401
    0x15071208061210050604061d07110c04020a020307030f0f0203040302090a110406050406020708030315040c14031305190302151807090b0123030106030207050a0605130b10180b04 78
    0x562000c1c0c4556400203c11207510b401c8107229403002c1d038060059a0382c1c3d070074005000d0b210340031a9080c1d0701501c0014091911030051b00d82c074030040600304c03610f100030103000c50105d0f0310100e104001038000007017140505800400f144a00300541c50089809141d0100081d264000c6000081c49001400e000c607400f00300d141c010103056030980180350340e03880e030b6010054581d80c45441024094068041d00041c2841c02100303036446403036002d02907071041401300300700f20081c8020803065091000610806010102c604091885080100d03070100081c01d407810700354a072010310020780340b04c1140c001d60100000e074042075a03a00604801e14001c110348030b204102070390b40345040d0a60441d200e07404000074003031007a03040301c41220001c1e00c95002c914400301101c7c0c940c1114000d5503092060030001045101e04c2580240f41c118021015141d17030729015a1820b054a5007034990f050404101181e900920034402101178101104010b40b101700c1d49010000d0150304400a50015803550b00e61200c2d8190b04c580e0030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 344009892 1250 344008642 344008669
    0x40b0406080d021203010b0901030902010c1a0912161e120503010e13202106060f0d2d050307050708060a140103020f01050408120301051507120806 65
    0x2050102503100c00081e640c0340c03030703948406006200e001c282c04400c600c0030044905031100c040d0424a400740410042d0090301c0d090b4412070401c41c5443c07060020842c141808040010742515a895a0038085407492400c25100302c01d01d10309500700040701e0503084280980036055401440c860f410079404404000d619000c0002a02d00000756000f002c1895108001398107031003651086003041e4030f40c0c102c0d0400c0001c00d840002c10780161240300083c050010301c04d019180800500500c00c0801c40b00310312502c1240f50b44ac0300300a91042c01804814540702c070003139010400680e0072500e0a4801e0703c4841d0102e1180800407446800180c03a4910003180102492900780c1000440384c1c0c07200280750059071143c09124a0b441401140301158400e03085014582c45c195042175065686c1e400e40d020028001041c4040b1814000700f0400014120000d000c1c1d6080001052040b68884d89003a06228903008074078081d9407030f020f08100700030003e10750420f03001107420030380342c100c00603910800454444400100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 344011142 1250 344009892 344009899
    0xc031413082107180617180d0c02030c03060606160f292203030e2508060c0f0f071505010f050a08010c20070b0406030c03050907030b0a0b040b 63
    0x20305660b1103100c000415010381202c0da2076590551100201c0900140140203401c0010340c07038420101e4460118402c150400210b1104042407004d0b00300c183e00d070103484172225000c203815000315029490281301198401074168060600b40c50960001078a601c110840c040715884d070146101f003448011144010351640c0b141c0b100c442034402d581c440b00c40312654034903401c2c103041c1d0f90000385952242542c4206440301c0c200c0301c840340010b01e0b070302a8003410005100d0f242e988521416000c80121020880622142ca004050841401c0c8140c0741d08200008010708010340d03040144084240d40c610803a1411021078074110348a440600e00140011000000e0740c0841e401c10700082072510710820840300303c0d40100d84c3d20a1255444001900742c52260050f01e010075441ca10079440341d940215055210100c002c255000282c590040ca601c2d07803c607400c207100103995124150300c1d090300341c840c50760094102e0008209551440d558941d03084001040301042944491407aaa04d40348c03600a1294060f004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 344012392 1250 344011142 344011177
    0xb04060504050f040b13021602030304030804060809030306010c080c0a0c03140106060309050c0d080d060b1305030c0f011809110711180c0304020604081606030c03141308 75
    0x1944000d219400c1405043c3c0300340990006090245010700c550100400003600c0e800903880400035900c003c0d0000c0014030030f070b40c1c151101e540050350184010310255200d1110581c449090800041c10703004014030640b182d91003002407143c51380e0006d1000c0c01444c0e21103800d42e903401d5228042401d1041044004080500040c004802c101c480c2c060100152420b600800c40c5564840782282910710016016245400c0a009105a41421a00c40c8034440c0602e2004d45001e0307080501508440c21a40520400180030915900c4034115101c80001024120000c0004000060020310414400907400341841241c0e80d07100020803e4405005c0104810002080f0007414002e040c0c00035071207003200700c0707100084034000049894030100703850f90380f84204110040b56841c0c3c16800d4035944007502c1642e11003020302002510030000c02c01c2070340007105071030510001840c0c048e016080e2910ba161800a01d42800d03208141da0081c008404e5000010041201c04030070107041000407880f6243c0708407a4a001c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 344013642 1250 344012392 344012399
    0x1819240504050109210e131b050301090b09040b0a1d010c0503010302240304060209030307022d03012007020a030f0c031401020720122410120206130b04 67
    0x6521a03550b55000394080c0c80042002d84180d00303000b044a41e4940804c14401089a982c10300d20071f1660f81024180d000121840c124024010b5031080c0a032442c0020400001840600078074025541d241c4000c1e45c21046034100345c1d4552580c18001402c80c41201d1381e441852007000c88085202031080c2140000b080303005a106001003955200b400140d0280d13080005049002c45031080760f40200711404006802c50b02c5a0391800301a44c4008075150381071000b40400005a5a07075500160603244505030b84d4032040140611102606580c03d000e072103070740f4000c13000f503d00308080c003402c406000341c00043c0c1c2d80c0c0040380300040051820b50009404e0b802d0b0001040704104a0f10710090550b40100700905d1030000c44600f00e8280e00c50007000078204680000f0321030190488010048080000601c0c0d8180c2d082850506840c0142c50151721111001391200c0d18011800c080c400d5804c5003912030a4030800741014070288040900081c000d010f00e50004001c03a07403c0c2050350400140072a45000390b600d654 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 344014892 1250 344013642 344013653
    0x40e01090c080d03060f1214070504050109050a140402010816050d0c020708071208040308030711010c0e120304080d0807090b0301080616050c06060103050a06030503040e1819240504 80
    0x349010070402207854442c020440303002c0b018030311080359040144030020702192303941c1c84c0701049001e006211a01c610100410580c0e2180a040e001e400040303c0040c3c117207052502d95050324201201319804c404c0c14000e00c00941d9020011690154071400c6180740031041800c11205489202c100041081c0b419184100c0760b64086520000c44848000315134500b9203c80c1e00416000102d400207140034010030003080000c094001548e841a00c0d4103059a000d210700540500323403050b8201e05400070b0390050240c0780d40c0c5048070042000c003204000031420b09003000101541e80f0b2070107503c0340a201009000400603031213200148090320611030001d4481d40c0d244001c4d0b035a0f160603100401001c035640c000c03044080c442c20039903100110b55401042180c4455006600a090103042e205420361100b00110100340100020801045108030f180c14901d41b04d50152010700500b60103d5041d000a44075080001c6c3c1c50b04407000c2d01c0c2e0006071036000404450070481c4004062400400c01034240001c0109109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 344016142 1250 344014892 344014903
    0x30a020a02070806132414010503011808030609061906031e0515010807030b04020a390813030f03020a02030f010b011b080c070b13150e040e01090c08 66
    0x280d580031101c0c480d07140d01c20203484200031542840d042200b040c5c0300340410005c42c42400d840c0151816401030201200110050f100301031000c1440c0e03114000100200d040034450b010310000e00080000c08804165102c800503c00942542c0c8a0020300f000704840e90b07200740c540d54100040c6800c3c2d10b851640c4c0e200140152101e05242007170f0741180003032020341c000c8a01075035100c0c809070882c82d010f1818030741c01914000c401620f02002c040d941c0c08580b941c0c1c1c40d984010b0180b035000340c89451080c981c8554143e8500c80301d110f0500202d1001c050300500070310403000500c44962000045e07448001c1d0030b00c040d0030a80242d2014084642d0380c1580310a150b004249110b20300d00070740c295400d40f400d0100c0f03175003a650b2080d805070014881500400000b071f01c10381c1c4000e1440c4180700031403506c3c2d2036070805460140780c3d4206c0b02e04801c0c0003030b01d40c03212040c4004a100030401da006400c0c1c417403000a80545482041c9090b140a29140e0596000d40402940324034411079000c012280d42689903090f1580d80e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 344017392 1250 344016142 344016157
    0x314010f092f0a0e040510061d06030325030e060a0503060117071e0302070804090b0a150c0602070f05070801051e2a04320607020d02061b0102030a02 66
    0x2040d20301d503810009900c00040c002c1045000d4844101d151500b003c80944840061003a1900d0203014a0a200e04680c0d000e40700082c14454401c01c8031000c03540d00b00d0390791500a01440d10030361082003450701d07801c400188042d0f04481402c01454128850600350350400c420390405901c01c00004801c940c854100c1c010f1409128282e89401002c6039004c201c0362990380c192000400301c1c440b90307880c0811034a94051012071001c0340c9000341c10704a030345d0703141280741c1c0050b001414190303255000b0520a052006000c0001c2240d010b0020f00d0144090010b840c821017000050300880d0000342800a10064040c2c5184e65544201180c0324165980c2c0c04030b0007007100b512020071800b00d6844440c0c511950106107030260340c5800512049440704250b8588907910003c881030b180f0424003000601c918104a09201003520403150318820302c04001c00000b0302c2c4114442445142c00340052070140c0c903058000e040e0954191685503594070686414800e50480d00710304101c641c000010403c407003d091b000380400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 344018642 1250 344017392 344017433
    0x5042706050913021005070b100302090c07170a0c0506092a030c1009050d03020a030f17160306080d170702030f030a0504020a120b0907080d02070314010f09 69
    0x2a507031200e0420545040c1035481966081d04140080054500307105aa041c215160801c03d2a02000c3da48194018a04a81c8000c0c10180741104000358240030b00c0003944000701d20002442d283c0303969280403024072084c0d0301212203078010489000050140c0b00d400c2100346c00100311022450000a49aa5415200c810138002c85003001d030010f03440199100c9079060303000200030f046480080b03028004142111429141041380801000909480749000400c45601035400303000560b1103420003400c0808280e08103000c00400c1c00e0300d1316060742070304000d9811940c20043d00341c00c182078680071000382c00d094208030040c0c0161204000c85036082500004099031744a001006607542040685e260300421004400501c0200001141840d444c0d00440e0300c24401030040c1146500c990515113103000300603080720310155803401e209501c1d00070440180148102d80051500c0744400c50000d4540c00e01d480020070070b00b00d845600b01c090000390800c0c1701c4141c401c0d40401500d0341a082100441c400c00001018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 344019892 1250 344018642 344018651
    0x5210a080c12010b0a030606180b0d1413120c0b01120c080f0703110f0d1b0905071101050f070912050c0607060b122e0b0d060e070e10090c050427 64
    0x3040c50251440300c0142030302d5a131101082cac0c40c1c0071213040503034400d03031840103000da480c40840b541d81000b84903d4014040105c22aa41841d5442d101d001d1144012680c03051100c0c103210500061403001c0050705552504401480400062402007004201c50b004071001d4040c120100d422500000b800c04210f1f4010700c20b01040e420044103014090201e07407421608078401e426401c0101d500604900d8290b60a0480d244180340d841c2501c008a0740c3c1030b1810000601583d83c0708082c1c4d10240a10b40d0011581500004075003480c0ca00a4180440ea00c1100310b0344081c10b08000c140941401300228041c0041c2c480b40c1d0700d0b80b00b0715081000b409008141ea00c20080c10303204140454000640b01c1581748002ca004104030040059050381c030203580115a202515501900400d45843c603108809034860f410202d01e201c404c24500d820403090341c0140c01614050020002c00050100400c0301b202c51400c000101d64440c60b03c112054400c0341c01008905c060103459450340501c80564086522a4000822 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 344021142 1250 344019892 344019899
    0xc030706050708040e1902040f06030515220605090411030105090303090a060b1309030c021203120c070204060503030406020622110910050411030405210a080c12010b0a0306 76
    0x740c5500070020040c04050341030100303002040c10764000503000f11170707400c0113290402e509900390142e03071160308021605041c25604101c00c64060180540110b811584030801c11411004548660a02c1092004043d5800b4401d43c0124495121901900d800307400303490703a442c103403c086150791110081039000e0341c6403100040c2500c101109a0b80140034050103800c01c07002c181c40740800342c2040541c15031312a0f0346103006101c80d001841040d00c2c03076203c0e46802940001900400085203d01c0840340c1003a0010410030000320802e092346640844081d40c05500d500d654008900144000c0c0c02042e05844006000b161762500051014441d1504144440380e0342c43c207030100360302168864002022032140c0320588105281001c5150303480903210a05429082d0369400140a8500040c40d0400450001091006000060245c10942c10f1400060344000b0440c3c0c0750042e13035102d845650000c0051042c00302d0b0007911000216850140700a88501d0b295031182c003503407000d0b4064213401c07011034604900007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 344022392 1250 344021142 344021147
    0x918020403050c040c0f111501060c050c01080106120f09020301180b06041a012025080703080301030b070201140403090503010c080c034320061504090f050c030706 72
    0x1032880035199140d15484401c85002e549483c0500840b0a442c0105070b0f0f0751055810070b1802300e0080c16690394124004c0f1040c1403083c109148114000e041200031001482041e4114038400c502c110301d0103001030f2002d40003e21600600200500942c90b509001a2025481c00b4243c0c4419803401440080b0890310b5440c1004101d0b01c10740c3e0b04124150307510051000540c000c0c0e0446a08403030644040b440604200780c154102100046000c0c00c1100d9000c0480b003170a5682c5854001d000010b000302416811030301e804209010511004183d110100c0016030b200d8400c0d0000b54400c40314003050901400c0c2458007501403038990150901039031070300149058a034400d80890340103101100546123151140319205502c4508902d003c03104441d040e045003104403945400030b4800040c90940044400181ca00400d403012502001007a881c60720403030055501c010030040e801000c005064015180030398040703005000e50a001414095550440f0014030101180b03022040d00124281d0303140e00d07240c0c08103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 344023642 1250 344022392 344022401
    0x201080c0301050109210c0f15021f0e0307060f1b02010c1707020a0506010e15090c0406050d1806050a0c051611030f060c1c0b130c0918020403050c04 66
    0xf110300050f030004081117111070304900111400d00030303021962141e080d61101e4213850420b41c4809648100036000300700c044261552610100040e00c080d0010b0344d21001201e981414404c941e29010303039251500c4041c002c3c00c008070340c0c046a0040c010300200d40110303018130040801c03d01642c4a1002007407116800c900c10300c5654440c40d81c680301c030034400c4001080103a030584018803c8003540300d2081020003290301040b5840c0200b616001c1e0440b6403400e6060b11a0028030107d200780a444803d0600007861101c074161026548280360050701c0306200c450b420064001c80700000c0e003040203207180000703011554208510580076413800b0300800001c1c41c130464040c4507098102c0d4040c40760328201e6000900e68000c041c04040010121081c803d0a05a21800c0440070344a10685200c000303000d11070010250702c590300e50468410108050074223080802e40700c000450144141c0e41e40c0713940383c0718414010601c4030054103003070b250401c1d045074030703400d690080d80a804180c60a21441c4101740852800703008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 344024892 1250 344023642 344023649
    0x4060b03010522020c150a060503010c1707050904020412060509060105130e01021b0d08060d0f080a0c0507061218081603020c03150613090302120a020307020901030305070201080c0301 81
    0x40c20000f0844803040c07009450036240801d815502044241c4080800f000011912009240011503d05140c4060802c0315065405580030340d040c0700080d12881c1c0c1001e00c0c040031040502c5014a20b542d910b0742200c084c800c050b03100c0c0d4894070120b4040391003405050421703281482244c00300b180e03031610758210b0780ea02c60174803886a00c60352440801c040c0307a110350050100644000005400e104100c03603440711094200c880e42034039510000600c0c2e421a4440b072203e422110a6407004130b420312640700c070566204041d5000c1c280440003c0c0b15101e61744112007844259030004161445140c03210300060854910540c600007950402d82c2401e92107905100940109500401c02864a0180d481580410700d910300142c0070750041d0b80d4184000c2d1070500400c4c0c21402185180d800b1460080201303c1860f081110180100f03252105060000c1e8000034070407085944c5504184e210381c00914100d03e140308080d0004d400010041c000000c054010024001c0359202341c0f42e0740110343d95140710203c240070034403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 344026142 1250 344024892 344024899
    0x609120405150705010204240306050f040c021504050d030c02070b090103150915170606030d0e13020c0607020618030d0f020412050f0f010207020315090a170904060b030105 76
    0x200030001c9207804082c2e4001405212581424400c10362101400ca8000e58400704007100b084040058400000c55056002315060400300001e604060100380b006c0c40200e82c560113151394a0071482114000c001e4440d2621007103070b100000746094a0250b03101c01500e000e05001c60306140f40082c00070300101c4c03001d094079064098a81807848103001103024150705215032507180065040801c03000014090865001c2ca4801c08100b002d00d0701704200c5048098400801c0720b5000b02c41841103a07503000c900a071580529280c100c50050b0802c0c00600c6620303900004460079480096000803c80000c1401e41c4205515002d030382c541d51710360000c9000c88594441e0300d1041e4008020380c2c02c001d101c940c049220341a9146e401410562982c46034105100320120a84d00c41d4808016400b18600421800c281030442d03900a500300800c503408280d54000740030f081c91030319848400241000c00704200b20102650810201200000384120a051170307805010180e014070f050040101c1c10782c0c58002100d04807840607 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 344027392 1250 344026142 344026147
    0x21b0d0b0609100f03030302041802070816062d051303020a03050d0213080a0b0a1b0c021203040e040c0621020703140a0504090e06011208210414060912 67
    0x701c0c01c00409100003441d02900b42d445110201d40c49980c010041c0140d4480d840040c3e9450a01520103221100e40543c3d41501d40100320ba40d00082d134401c143d5401100d29241044003100601d4410058500c65480c2c03000b03507400c6914040f01208081d0341e680724401c004010000781e2034006031a1614840c000000e00941d012400c041c4c00139110b032000780624000d0034001030529090800c800142d0100742c0c4031100340d81c0207445800600003607000154114000000c2045100c1582c024426030341000c40b81c14042c0314a545110303042d5201c0d91048007102540b4001d0743c0d030326034a640c04401c081e00c05840076030304207089090226066000d0b90103040604803d2080b885800705403000700f0007a51250004900300490406c0b010342d046001130182c8250f900d1030b210961214103009144013150329840c04c0a940307603c844010000c03402442c0f240c0d4203250300094850fa80342c0d04800344013418032214180d442ea4080c024100424813250b244410031400661050312010784806400f141e5940402440300e11a1204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 344028642 1250 344027392 344027401
    0x30405150a0e09040303020a110607020706030903020c06031e07031401091a0904080c0d180603240807060806010f0915020a0c0b03060f1e09041401020a021b0d0b 71
    0x20001d815200200e01e0106400e031500c4000c074198031000c0c4c800b00e000c6500490000c03001c6030001c2c203068090400364000d09441c0303409200259921a90b200e03420502d81d0318000e04040c544203010583c4c8007240500701033794906240040c09098a809a00d881c40c040300340e0003041e001c6120b070042403044080c080d01d5a10301d900f0201907400034054503541450a00b0110010003080c1c8030440100d00c264010044903403a00300315000c00d8200018084118200301c440c1e5004080c0000d03110741e20f810345086290002e102c0e44000090000e00c020542c0300d85604821480000b00707050700107181c00c1035810940d12400b01e9242c100043d03540c40c11104c0d07840040f816800c414848200e4036480e1005d6907140b8811101d1120b815121040c10301e01d0f036080124a01c40010804c005820009500d900c0c04c0400da5a09000c610b00284c0a0702c807440001805101d1000031011506001c00d65081005020580d80215628514440065902c0c5517045080124000c07000f25a51549000075114940c0d540001e08403000f40da5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 344029892 1250 344028642 344028679
    0x170f061b0a0e0306180106060c031713140303090c12030a08070212270d081804090c08060f010f050a12050f121b030301050d0201260c120603030405 65
    0x1404407001001030420048030b069408104441c001c1d8824030340729903003001c101c1c0d8407070030350700300380c002e1414041103144201c0041da01c0482d113285c0d0303d034001059080d0303101c91070202001c3c00c00c1740000e40303a0301c02c0d50041040c2610210007113010310040d104480017039400d0424042265000310b22508150010302400c1d072024040d1054a920201d01c0c810340c0d405040c020020000e94004480c0500c0c008034454a10001a021030302c1214013240484003845d88035080d684403411407080e2010000740751503d49083c3e44544480d0080e010303007070b40602c2c0441515162980655510000c03150f00341030710801000000c5041c10104010140c480107050724507801d08040c010320a401116070700301c44a22400e080c40014003c1401100c00d10103002800d140c3d00d02c9003910002c401075014045a030700e0f410400042000f550f41d80c0d8910320003582802d1800c03183c1b840d4044d181da09403003207903000700c16200c400c200001010030b5001405904c44107501401ea0782ca811041c0740c3d50b0702542c0100d98001018200c041071410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 344031142 1250 344029892 344029897
    0x6010906030231110702010909020c0d1803050709050708061e010c110a0e010e152b1505070f030608070308090a0803041806090c0e040507031401170f061b 68
    0x1c45a05490f4401294184400c00700c0341000e81c2c04604000205101c801c560f03102c14610010034a0440c1542060070802440da11000000c03491424001c02150b001c4008100000380300007150064107513000c83e9a5584a0406040215040310004600e0030000344685080e202e8600c0c030f9603c022107540304050b500c00568011101080a0f5044040340c0c00b880210ba0300c160000e00948511211003443d0b51401c0c80e5102314400203401d80c01511007a10b25140c4603148d09054210701044086039002940c0241403014088054039409004000003174110b8941b01201c0c0c007c140241015a610401e5140b40a030440c100c603014044c000d00c5801c441010008500c07001c014000c2034000900c8944880e5480910710300e1940554407500c00100080c8032480c12860318410807000306607105082c0800c0c00e101070010701042c00786004038491942d070004a45128465400208080307141c0c0740d108190358551070724120f403036035928448a6034862000a01440503011603c42e010707000644aa10070601c403200d4545154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 344032392 1250 344031142 344031199
    0xb040209190302030105011a0a0c030c08280f050d0207020102250e13020102030d0f0204080a1103010c09050109030f02010e090408030915091b03010b0604030c08060109060302 77
    0x56000d114000d0a5540e9072024052460100c030301e14461491071051500b9078805a000c0c00341450350005441103588420121100502c403072401101c074035840e14013a11483e00d42980907080d800041040186030915801541c140300442c0d250001110004004075404c2c030b6020503900002d078080c00b102d400c808690f006402e2803132050040d556a03192441c0103031000c50482c0c400b500000f41101c0100403281c00714203a10307005010481d40f4042025943c001035560300ca10088414444e59980f810894048940d0544000d400c1c50015030309003640604009603c1038150164500c00e501e404400a034036030003801a0300c11902c040e1284c0c0c0c403103071943d107411001c02c01d0500c042c0d051158082e9800b00300c2c0e442400d1144501c0c8103020b850307200e040001e43d1a00d810049103c00c1d0300d41070680d05000030441c00050307500841514500c01003414001c0307408640502241132546030090400318011040000701c070525016a80002c0c00c42c0c6283e82c1e5018500700b44e4a1910002c0e40014030000e0843e850f07820341d602e04210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 344033642 1250 344032392 344032399
    0xf07020913050303041b0603141f081e0c060405010c1502122701090201020c060c0c060c0609060a050708060103110c0715090801140c130306020a09030b0c0a02060a0b 73
    0x402a2688440f0300b960300888045074000c190882c1c9140810054411002400081c54108003850740c4901c0001c104001a0601f40d40702c1c5000400410b188558900f103001e0000e090130384120316120b480c190001c0400304407451050040f030b4050b031b0182c00d0400c195000c59405075034a08104806446103480344081645412245808005180300d4280034012540550603050010403070240c900000d01c00444c4000e001480342e4103000e18140981e13800550310040c0502102c009540d002d01d200007515107002020002d421990108541413411000300c0c119225a07046d009482190b680c0a0050003254002c40d12040401c00120210b8090b5200764002a05000d8a00d0214901403080150b245804400d42c0134404003070b030303010710001f44d29805441e11004000e2013000344450f4586103e1500d244500400d140d1100c040400c1384843c014481410100444c0c000c0411542c40480d82002048120280000e60f9420947c01c0841c0404440c80111010b5000341c0d4081c15090315824100c6010b05004030000381d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 344034892 1250 344033642 344033671
    0x20904141513020111061b0306030c030f01050a18030c0305090f120c042906070606050607031d01090302012715030614040902030304090e120409050a110f070209 71
    0x40070041d441802d009450140400c8250540c91000510840c00000310000781d82082060141626141166040012203441d0711522039a17840c2c0420300d015055010f40e40e25105a000074009401b040d0301c8030340103070418802803000100e0034003030740480e031082d150050020b00daa55044c00443e11500c05400c1e80c00d00104201c624440c504002225098144480c3c00650812541500c403440c0900c503036401c030001c0d42e4600381440d01d20364000500c4480341c07561034020700340000c03204100003c0e540220003500c4002c2a540c0c491005040040030a0034020761a4861901041d1003005036014101203821030368140d4032468451240c200540c01c44000b0140c1d209802c81b00c83c804281c91955000030400040035a07400147c061920181c9481c0d82c0f04d001c10315010703920300341c40100907881c04400c0310207441030500c01040320a0140215440c100d008028540c10203408900803540d14900d800c103d0060b03480800038080c848081544400e144907501195075110030820010006060100301598004401d414150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 344036142 1250 344034892 344034913
    0x30611040e07030f0c030608190203030403170309010e011a040f06090e010e011406091803040f15110d0e1207050405070302040e1602031b160f0f06050702090414 71
    0x4001d18241da922001c40d071201c1c001001c4a100b0b00c40ea00c11800709140500c0084d203070501e03840c5c17110ba1400c4074603003c080f209009425505c040044900031540301440311901a40e0707030060000c5400070303a0902055428444c481603030610501a8010001c0c40070001e8040340d03407000030000100f10307825580141c00e403103900c005070310555031040d0303100d4191000010a480c080c9035075282c2118952202d42a82d407043d10181300701526000146580a03010b200ca01c119902c803951490300c3e60146a110440303c54100078080340c031360500c881044c1d00c581a07803109154031105220740b9440b40307240d2101d14000791021104040303600d06503142c0b0303000e011003800795a0703c41e880304003150175140110f8241000c01c0d00001c0402c4588090082c241d032100400c1a00601d4a400d80c0c0001d4403441a0001e0b070344031480040344000c0076130060222180009008003500801651402900c0c0402668480c69251840c00d8200282885c05041142c09140e4020700000d4030740da40c0d0341c966515002082250107a40301d98816031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 344037392 1250 344036142 344036159
    0x60507060e250905040b0a09020607120e100e010206041b080a060506093106180b0403020c030106380412020a1508042a030b2202010903061104 63
    0x3440c11034034070400035030007002c102503015000c01c40740d011001c0a4509410000800d02071100740d508200140c1010540301e01500000700c440c02840405050807403514803060001c0c0d081116285011015188542c00c201050410341e0074200c00802503001d600306000081c00100c0813610b070516001940c1102c003040f074554000a1400d6900b090454001e55250240000c9240891100358000b01a0805014542d81c9640d40884c0b4411314928005070308a05e0711800800c0341035041400b0700600d00280ba0481251810310103121842990309034094044c3c20018625400d060282c031068440d4210b14480340340700c1e1650080c140810001c80d000210987e041045490b02c103038010401000310720320000110085004110790b4802690000c202100c2d020780b0580da898004c1022135106421030748101d007407121b01c034100c10070074034030b151240da007102801011017000b021200003809400c02645031402e5012048054104514501020740402c3d91014200300041d00d64103d04100c1d1600e4211034202030b43c41405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 344038642 1250 344037392 344037403
    0xa02120f10020304140d120207060b090c0d0b0301110405060d0f06120501050702031e0a0c021c1103030c1f060519030506131101050f07080714100510060507060e 71
    0x10601840c2c0c00105000500144140700c40007650703030101810f0244a1703c070000c2c0c819241001000c0c0030b203402050340f00c1401642d5204000451000e010759000d440c200c00103141550100d40c000824a213020704660f120f080c1442a407446240d00030700a07280c2414078040200070380000600010042e101e0f50605407805807405814018141da000c411740481c000e1400c242514070061812003154001c2c4441d03104030800c20b88003105521100255030356101c00300301c11541440820f402035007140144030903501e0440d0079980f516803039025084a40c1d94221410805880b0b20501c800c0e60003a500a080440d468030010301c0d1403c000070b94002c000380321540c8401260620709100050352600c01d6aa074100702740502841229801355540c9130720b120300c0040b96a103061051940f0800c0d410000003203444294403140000f1284401d810880c1240c441c0010720780b61442c03118402c1249402d00444100e4250b90006000300b85c01040e9042c10910124101241140d05410900d01681c0c1f4030740b1860707015030f2110203216 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 344039892 1250 344038642 344038663
    0xe0a021605010e0d080901020a120b0103090b240301110a0f021e0703031106100e0a09020604030804050406080607050d05071707030f0507020a020607061505030714010e0103020c0a02120f 82
    0x1900c0c2980303420340301030400e08001b400ca2602d070740108020b46416a01c00b90001307031101c072041e000801d5444800120020850818002c00d00d4120006004049084024500e002500401445142da900d40c05050030384035140007280d211003041c41110f041502a44411030309580d140304980c13108501c60003511034404071755051410f5170006202801456031001000b80041000e900401280c1801b0b074001c0070216261207090703e460303984400304038009226003047c5080c83d0000c00c0706444680341c0c24084402c0d800351103098841c5242c42000036000342c01003400c1e8030800d1980c07036290900b0320303007031540003e460300424400c1041404d82c020344180d000456194000d03170301c60350001403442580c901c16045070005400c0340255449220f0b54070042c2d440300c003100c41199000b0408909042040c40c0950401d91680100760b160041140229844010640c0c02010800c2642c3c3c0c04c13084d49000005604034850712420b5201c54103c0640c1390090b080c01c8884c000082840404c0354000d00030703076a850b41070800074071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 344041142 1250 344039892 344039921
    0xa0e12031005040c02150a061e0f060c3f0e040e1c0513090c2303040b062416050c0405160c0602040b0307091e0e0a02160501 55
    0x8144149003a6410314040a00b005070b8080044201080c4044d6440c02ca07441c03000322640c1d0364400a104841e060b00090010f0281c00940c030702c181d400c1160100000e0041c0a820010000c1c3c100c00100306104110410405400141040c80c210700c900d403524204080c410440c0740080102c0904280441c078000703d042644507a51000c1450100b1010001520b460002c42c803c2c680c40722140000000b111140d40442c003070300f403c109a850070a4220107070a0800e80d4071a00340f50f45004049031603140c100403041c0b4080c40c61103550101c02c0d541c400c0074000340411f0b14050003450401000815074201114030000c000c04d110101541c6000c2d002c0d06001c55448030030201d0312250401603030310401c001000810f0000c04200c1d014003091401400c900c4a00034460320000401416035554014061300ea411580540107841009607645130598000d031010080d449000803005074441c8840e0302603840c01000041d5a000d14520006444882050780079401650070341940820b029010400103c1c240701c0d040402c105074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 344042392 1250 344041142 344041147
    0x2205400c0303110115060e0d05010e0a03020319080907030201030506031f060602011a06090d03120f02030f22020f1305010e04020f010207080703151415030c0d15050a0e12 75
    0xe40060035a170304a00f408003020084d41c81409031a03003280100d1074081042c1c030410341000d51070030010b01504079100703600002d004401e021800d00d6408001001c0407034042c408200c025001c040c04803980102112005015000180c0610041d17100e504025007010000f811950717410545e8280c42280d0441006400035a40e1b02e000800c07030f80b602800707500c04498500c2808028615502c020802c1481555140d0344140c014000a0b001c25000750303568000c1c160b04d407400300030381c140440c211b00007940283d4070120080c84c84030016044a01600d020b5268480601400404964039803e101501d254070001030b9101450b1140e00e0001040c2d4810140200113490703c01c0c103103003400c0c010720a80c85098200da9046402031803080c4280000061b130303241100d0307000000d8000e414444825400074250502924050100d070014400505005c0e4564008145c0440903130300f01c04008010007844c50007061004000ba18034401130300b41d030b1000c2c0d4002903018860900101d0300d88458141c081c1000424401402c4a4101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 344043642 1250 344042392 344042417
    0x30606132d080c0d060c0207030b090102120105060a050a210c02030d150302061213060f0b01080705250503090d03050a0815060706020304112205400c0303 68
    0xd0aa03401c004124403409003100340485004a40107541c0f122010740410348602e24001403910030800c8030021904409607403a541440321002340030750310070480710b5010f01c50207001017507500d041c034203e51508040342c031740c02d00e0410365200c1500c40d69046c901c0e01905003442d14800a49452501980c0104007282d0f02847c0d0303038228081448110352010a0503c0c00d02c84140041c00103880381401ca071900854001c0c607c005981d02484e06007090b41014005240a09282d010400c10b00346030400c440001090f01d07092000d81d50701c10b0071a40390048040b4464544000311082009881013050145050b0040090b6450b18508001180b42da0503440411800110001941010030380c1c4005030f16041003015009007115548040020168002e100025007041d0b400404074013044a07030f201c0c0c42603105020380201c088003c1c0340c00da800724400c004c2d522040e0307608103c0003451002e003c0e010700400602d5841080d091001d0008103c5804402410b82071512091030700100c041110101e8a500561080d640c0861001c0c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 344044892 1250 344043642 344043719
    0x30219090e0d0207300602090f010c0201050313020d0f0503030126100b010302130602010e25060807140d090201090902090f06130906030f030f0c0803060613 69
    0xd0442060168101000d8596903503400f0411204540c05031008580520207031045a030412902c4035011045e02107a18070508104844d000303403c407030340704403101112000c071000191259185601c000340001c1040002403808140e50360142c02c1180040c2244002090b10340c0c0703158101b14070100a54041d0300100041251202d0a2100341d00070b0b20841c1d0001d815006000060740e10901c001c00d8100d00341d02c41c08d21072101e910a40c1502e110b40c0d04080310b10155036803400d001e802080c00c078642901d1400340b030b8916461424101605104403820082e400e00d141e2915604490b02c0d80040c000b07000b0056804a0008421005409845500c0c203000000600211790b10001d0600d81080d44040c40c02c074014415038500d0703030300c400003818020002d031b840655402c01d02946401c40c0c426900202c01c0d6920380310010003400001c100021a8501c0381d11080705501284405441d250b00404c1d0080012104200141b01420725801070136554001041c0134260340d48030a210701c0300e9420000c1c54000b680c541c4010221022 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 344046142 1250 344044892 344044901
    0xe270702030705100f0902180402010216050612180a050f0727050402040b04110418200d060918030f050a02030706270311120a0c0b090703021909 64
    0x504034001503103044002d541c0d1645414075200b1100c01d490b52101c60041403010754104e060016801803c560626110850100c90306000703603016030043c0b107504244051850040b00c094180c4400034140381c100301081c42c202941042c01000c00110b02040f400d03158018904112440d50940b08402800c201659000360714a8420710741d114078040d41400407082c2e2075980b4100e020b00c00044460b03000c60280e070790b0300106015104451145030010b03d0180c2c01254107800b800603001341c0e010f07400c064188030180b09880041c1d442ca14801c15580e6507591500d20032081c1900288610801614040b5580355a003080038121441d8810040001076101c0400042542c0b0024120100e8900e00344030742414a5688d00035641e0095440c0181074641c1d17200e03501d01c003101d121000c25041000a005543e05038651030010301c01c2c130ba4081ca1851510940f402403140301e01d01400c0d94030359005551034101c0347c1d0309030b03d80b0200440041d15090842c020f4600120141e105c0501030b0140702092424003070010314244203902240c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 344047392 1250 344046142 344046151
    0x1204080a2607110a02060c0714030102040518040627060c02010c0819112b090203030702010e18090303090c0103140703090c0915050901090c1e0e27 65
    0x40e1420070301c84410714240c28503581000c2c40307151284000e010300114624290314000080e50011300450040d014540004515055032040f4015404101103038082c10300f030f80502d004441d0720071907500e074140c188406403014a5000740100d03008180c003810030010b41000c0c1554007910796071917001ca04400501189000d102c1c006092440204401c010500f401002d9a8000d401c14040000d0a01c902c071165990740c102d00c1d40d0803203000035180d03212082e18841d4042c1031a0f01c144c1100d40305c808008002e03010140300b41c550854018014500e0800564011070b100340c07503901201d07403280b0030951281c01501d11001d128822100f500003141d03070b4100821554a42110640c00d9410142021400301c41c480404aa068002d44c0d0741c140484c03c03007110f00d41805400c12a40152006a10304505092124945528074048038001d40300d20000e41d8030341100c201620074150031a03004c50191002100000d00007450038120b8041844c0000e101c40c003140010700e040c1c46d8204dd0f0010759424540750315684200b4010345420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 344048642 1250 344047392 344047427
    0x9030201170906010308090d02060c0f12040b030109151203480c030f111302090303030402130e010207060f050705040e070804021c030215060a060903060b061204080a 73
    0x1540b402044455a030b49050000130445800402c5c0350055440340071041040740d900620841d11500a0f03850f240c0c1d00d40b540c001c3e9840500c500802c1c0c0c10005000022038050b01c0c40e103100342d85160300f001c1c045006020040e410852817150300000258400c020b071034028102c0d02c07950702c4d01070380150003150300c02141d100000041d881d280c0c0c00b01e00c01603c08140555000d078114420002e0360b10003078200240701203219030000e050030901c015000100032141c12031140301c03041181c00041d11810490031800320b02600d590715030140d00c10400702e8054900780207000d103002000e81c0701182d1240301000d00b0342a600b00180031904651900c11440010ba01070003030039032000c003524019091034600090302d1003000010b071010051080798404a015511007262510941801044006070ba040c00d29000703580e07100166502d10074080960100b5070f240303001034211044980070758a1850b100d040d91500001440c200c0005948298100444c80020419070384151140780039032192034a50b0f81000c1c0243c09061104900b100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344049892 1250 344048642 344048687
    0x210061d100b040e0c0c03030405210921010e010c0906090e0601091205010b1e010201180c0501050a1209050a02030615150703020c0415050f0108041203020c0709060609030201 77
    0x4084000f5101210078107400c43d182034a400f10388441d00e200d240b5510095000020820050001c005001411855242b032283e03544140600300016900a40b003d07203070b0000c2e510402c000703030189104080c5a2001d08100015249070300c52591404c4841140310b581c00b0030003442c402c000300380e0480300440040c9080c60003070009142c8071000920184841c0034111480c03035004000d03001d001c03003540103030f007002c5c8094003008840311140000c00307259030101c2c4003a0056007880003072000540c44803030b0104590ba2110f4031141076400c10700151519080100701c2000c000e800c0c070701d030820340040c1e00602c0c481a029002400300c0384041d0041c1414114010424a05280762407481c04030b0340c40f0380710044076004540034101d403950140d150890610201d006202d0b8424100300380369a003450355650392000c8910480790310f01400d40746c0005642154049034041c043c1c4060301f03400780070180650000c10103030308607000fa120015182c0a1003811140190411000284c034014140115600600b1004401118161290 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 344051142 1250 344049892 344049899
    0x3902010603150504030c0804060504090b0609010f1d0d0b010303033608070503030a15060c05060c280909062102010c030210110d0612051506010210061d10 68
    0x1d040030020541006003c2e9940e0000b014584540e21805000b603201e181d450742c5e0741e500c0f140203095805c0340c054502d01d0b40c43c0040c944810701d86041203a41c90401038480901c0c1f442280000c0d0341c96009a14034030002103209119025039503074508100d00041c410840c01507554194203004007154428030035140d07403420700e0951a004001700c00308412420120400d55104213a079150400c4a4024a03400030b105103c003109001048003143c2003480a50904400c0b20073300d60365010211030880203848003401c1c94102401107000c00d1500d4000345024800050302e207009803003001050080104011003200081d145540074402a0070364000c2c0401000c2c16485490640001155410354000c40c403c020705000282c3e40c05410140280620030003101c1054040003520b880840221550340030924540115241c904085821516100d00740c24079500200117003824102c41403030842003140030701000d056204203111003980303401c18058039015154411440070040640031031a4494071000e010103060b0b5a45002c01e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 344052392 1250 344051142 344051153
    0x30108060c09061201080d1d0a09051e0408031f05060307050c010608030301090c0801090c0e09040f020d0305091e45010608070305040c05060309013902010603 70
    0x181e08841d034186a280c1d281c4031800051502c1c800c84e4010761000d480c4600000304020041400320b011200703600d601e4010201c42c4140300b0400f000d0291103501000221003400010103030307401755900404601d80300905080c0705043c00c40d090380840f001c60345107000108003c011402c1d400f40303680d14004241411041404c20000500070300004151504000010480700d00700c1c04250041c5005005080684e5940c2d61036604001c00f500d41d4509820101e9181000021108107510038015504111760b00c03079132101e5280c400c210203020094000d891a1811105000240e503c1e84040134019200f030700c45503659211207083c440c090501060022105414054a4246480d00c0d40e80e451810300504001c01c1c07440055044800104071540302c0450f180d01d0240c2e59030b240c194242c640c4c0c10f842d8192980c0b040c507640c01100f10305481c0e0032940100072402c030304020400c1c1c0c01d1840156030000585c6002060b41c1c1c2c50344643e0056041d609810b4400600d440744400c5841d46c0341044942e104c40b40e44000d010040c2146c650 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 344053642 1250 344052392 344052403
    0x10906240f060309020414010b040807300512030a0501031106030411240301030f0512041404050703060b070b0a0b1c17070803010e150604030f030c03050c030a0503011a030108 77
    0x5002c20f06803241d01c1d2008540d5258060030011041c040c030340a042d61100107400303c581050180c403500348036141012a442481c0e02c03d0f0030704d905101c44100402030108000c10301080d40c2d884111824410303031040040d0703107c030300c0f0156128000d94940043c0c0c03589181000d03d0500128090203014000410030320010035542d6065203c0007500f42d60240c2ca2000a198202a142034042d4030f00803440080000300410024810550050740207500301e8008841e00310f124a1b0f148a6803241c480110100041600380c1d0619400080c2d10030158207000840d16541c03a0100b800760b00041c17003200d030040248200140d91b88984682080200269a0f088000d0096076146150460002c000703454101c03014010a46050b00c1c50444401e954000021501c03035940b4040c4124036003050720080c0108004020055603400d00382e06036011250400101140c909190b2829614012080c04c04d40410001300000e1480d0441000100041070080d03a0300781e500d6250641c482c0298401c8045030314407203400c000420510b6000170741e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 344054892 1250 344053642 344053649
    0x210a080a021f02040819110a08060f10050a090906060e010909060c09060e1c080a020d08250509010e06040f0f0509101701020712030606020c10021903050c010906240f 73
    0x441014032903180c1490980f852801f10002e07400303810320b200820103039001701d49580690404001d03154280c488040071150304c1c00034024260094600c410801000c0115006114a140280e0000a08035194807a441591100b41c1158620944035248a000c00c210307482a20358240e1b55103031812065090210040ca0064103608440c825076644d51880008903842d5002035140c4d500c92040c42d9108200600691100c0030086071202003600c070130025000f6100101c1c02c0400a1030101d204a09240760603054800e80c21040419040080143c103014945d03e6400c007d2000e06032100180c1e984601e0320062001c0180c4a81005000c0d099110501c03940b0310a040ca10802e0314500c01d9003503400c212007000c050083c01407500c054008440701428111460305540008241d507055402d4800000e150010b02c49245065070144006034006002058000300c610303100254035103c1c4c07510701e01d4500502c81c5607080d6001200107a4184d66220010b4440c3c4400030f00010000d0204500c8203038403490981d100e110503000b4030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 344056142 1250 344054892 344054923
    0x30f1609021c0f1d01180803070c0c03051f060b0a03090203101406010806011b021c0602030a06080d14030708040f0203030307020a021e210a080a021f020408 69
    0x8090340d00b60600c003800d0b9420000e5800c20002400c00b40c036a8405810500c082e4211881840200800c07000103019080040c40309180d282001d000d1643d4079141a4030007480076040114407503004d000200d1001007400254051001480015400c10340540720115601404901c14030f000c0c0200841e00c0f4130016196280741d10f0400180c47c07421800486e04011008024800f81858640b61800070412491940d01644081c0e0351540e05949410064540079504003000f05104c0110b00250300501e02241e060032009402c03010304841c0d484982c0c40340d003681c0042d1080700865444031014840c4000c204150040c011440c0f40801840f1104008036180e448042d007100c0402030101c00140c1171015440740c4410680d809000c50f0340c0ca1511040094540075008401c0303114081c4406d00c0d1110540c100a043c030344071002008907241c005540f00c40c603414085200f036400c1c540290b0305c9400201c0c1141c2d0190038001819000341c020391f8211000c17080c000501e00086001c080c41400244405000083e0000740d030342101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 344057392 1250 344056142 344056147
    0x6010302090406060519081b0607060c0201060b0f041409010509010b030a06050a08060708060609031009020301090203010501030c14101205100f0801090b01150f050f0d0504030e030f160902 83
    0x1420043c010b4032680d00a55007050700c2c11100440c0024601520048032001e006903000c0b000c072409685045009a21070503405581030100c4804640a40e00810f602c0f003850000140956860002c0c001a42050800e080d0401000c1010008100c07408260004004100d0311101e01d917041c1400150b03031200600801c001c500c4040006115640130341c1c1300f00050f004c000c3c402c2c56020364500c41241d444104551000026601c0f1010401c0c6d42424400d6803058800180031300b41408c20b2143c110010700c03101078183d03415900d03980300720050f031030030702c5245d01850183c5a4080c84030b04007258041d5409124440703d000b800d10340114a4040c0d84a1310a9a580303a0305507000c952a16842280e0b6042c2d81e6640000c0742c180c00f0074100161805055002c450030038854000008240c0e0780e1442c002081250303020780004104c903040e6210155104000030312465420000c01814944a200c15204848007120114041070701d031500c580c142d00e0108160b85503c450b076001042400400d8550301d20900aa00c94000740701d401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 344058642 1250 344057392 344057401
    0x90a0b0702070305070f090f0908090f1507061401060c110f130e07140a03111011010504030206060f10021e1509010518060f010605070606031e0606090c020601030209 73
    0x3400740342c00554220040315400d984651000151200c0c910a00c050b043c03400922001034211809809240c0e0f0b0002c2c0c0d0141032102c20b2083c818160220040c050344802c0c0518103144403001c60001c1c101c400e00490000034444143d8840c201c04083c103030040000e0100c1c4010034400200000c3c141c0043c0c10342600d12540d001266000f00c1d0b200c0c07801c140e01040741d0b0f09050720038900002c0090760b0003c6902c0c5800d0010504107040c18880e510b00640805054200343c4114404a410b0100140d2912582840d19000511032aa9480c1c21110251400c40040c0c01c9002402001d03d040c80d50703032403034007021200c0044004400b8000785d03480c5a525905000c68204030700c22501154240a0085983c2d0390308040c098601e468151030703000308000c49440d503d05214118600900000080d924031661144444840340d0342024810341d0983c200e101d084900703e4440034040000f4a41554a001c11111581c10030045060703860004242d8203160002c410311494682007956560380095920b0450350140d4103401a1f441c2c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 344059892 1250 344058642 344058647
    0x307030e1f240b0f0f07260405060d050705130b090306011d06040506060c0a03090302100302190c023c1504090b0402070c0308031e0c0a0f0c0b0109090614090a0b07 72
    0x1403001c81029040045083d40078001d02c40c03103101c2c5c401825000d04042d0241c2c0040c402145c0143c0c09a540c100300c050000d95103000cbc07a5409241c010001781000c1e410004601600e000c01002c1d604074542001000c100c51125040070807216014185002d514480881720b0b21030030080c10402042c1b14480ca07100e401288140d1601d40c122921602c202060b100060220306024010f51341501c4103d00482051070101c0b20103100f4800d42c1e241c070074a0f0840791410420107e0880780800b81490903684000e1144100d40c480512900c00002044410f40c040403250406840403020034200c08560f000b5800c0010314070341401c0001c203c0782034580c2094009850320680f0081802130140c80310003061840075040100a01401c0005140b1070700000030303505092450171184d400c1d00d09080e00d80c1d900740e010078405240780b9030040107884132745000307450300342c00d40031654907250918502a804101840d03030300c10b0030344103101c814040e100d8040e085e50b000002904115a0300c0759a990f501d14003610300e100100c080b44004d803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 344061142 1250 344059892 344059897
    0x5040b0d0f0c090501150e03010b0d120909140702010c03060503060a0f02040504020a030207021201022d0705060117070902030f061504090203010e2502070b0307030e1f240b0f 77
    0x80b000d08200300c40e40c1c4818a5800c42d03001b4812913004907540c08003540c494601406203900300c10029005d455403a095588408408032420160400c3c81400d01c1c0100f00c07d1a140300c0d284188426000c514824100000d0281c01c44900b8401034003010f007020030500584d20005071260f003019008100007101540304000a0080c000c5030440e640c011b00000f0602001075050300079054540c02210308081c9151541980d03401c0f0711071030f00c1d09042001040c0c0004019004076500302c2c0301010441d405807503d0025561141441c40036084038ad4084410440d04c00d20450805c10b03a005089070440c114518205035024054400d0000c22643c4031700c510ba1031010700c546042081c0d40007001207000c2903481e540c580121400044080703030558030790740c038a048990031006141407500902850750007a2002a080c031140400c4c55000928600c1419180c2201e001c40503400c02249031410403030030520310750803507041451065815200615007216007070548005250003a00c0c1c07503c11140750a00441d9500c4050040c143c007030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 344062392 1250 344061142 344061149
    0x80702010216050c0f090f0106140909070201060e10080309061810020105061e0927120d06061e03020a030603170c0c04020a02030d020c0c0904120905040b0d0f0c 71
    0x10b0020701c804100f010000d00841c00f02c908035041c0c5400b0800c01c003400748000c0200ea00c90111100c5000400010703000300c600525030400800c503d0700d08004607002c10100e0070160b0340080140e560303031010004810303440340b06504170034500c5090400c4c40c90024010703501c0c05280d1a5500c034200c0010700510048410000c0e400e17001003c0d0500d00300e04528080a03000b810f00719001c5014002c0e60407140e00b074510140703411820348001001e840e042e46500340ca104800350302840141034240c20442c1d82007a45400c0280000a1291030500b03640c0307030781c030801d05070a496141d80080d0600003c5074104590f0f0001c900117070441c030135a1600603200e03522042d040700039006580c00584000f9000c000108221404402001d140320004201c07005403036035005000880c490b0040000040e0014402c0369900c040325001046201c03410411581c1300070495000940303a5000740c40c1102d003c20000c21254090703410028850040108990400040c0c01c00c401041c904004598000d1503048125490801c00050031007801c050f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 344063642 1250 344062392 344062417
    0x60a1d032506090302010f0309060b04020c07080f06060a120602071205090f030a2f09010e04120c0305070201111c052d040b130305150420100807020102 67
    0x2040111000c032070851034044004a0180050030200e111030090a0440c1101c1d4107a550300c0fa2202031060860007000e00200c225002a01c40103001e081c4e0740d55001809006990303070060610240b91150040ca02184440018865000001002807995403030303860b03404450702c864204408021030714108000707108106004011010200a004540360310101074645040240e0304c2e080055665020150b86800042c8000c010b2001100358007990b0110402c0c0d070543c040300080c00c20303404a480c000900310324001d800110380e003201842044240000e4640c804007000082c10039034442c0d412500c0003000c0d80305900c0080d06005405081d140011020052880644680a8514644c5010101c0101960701c82e04403a00c41200c407049a060141c58042c00c116429400300081d454903290a4150031541c10018840d4541d034001100080407030424403008101010380c0c0c181c41c045103454541000c006540c00000042000750f100f22501c143c40f4002c886c100030744903080c003142e41d645e14901240a8855031061401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 344064748 1106 344063642 344063653
    0x6040b0a020d110f0717030f0103060504030c050a1505010f052412130b1803030403180b0a0207080f0307050703030804020112090b0403080c09060a1d03 67
    0x2124580c0c8400031880314106004400950000304e0f901825201c0002d9a008004c9000c05049420308143c203524114249108000d2a11105005c001c0006607600c0c0030a09050040004e9a1a40d60180c119044102e407032501b1a5010708080303104507401d08203000412a078607041001d00c29690040c050304014014801800280b000250500700180d00030032a045074210914421481602040000d0019125501c0c03c613441120003040080151170a85210301a20380201c1142e40040d05441c20394a0b0650b0940c20b2400020305511200a5901c002200312000d500030550404641c0000c0607185c02140710340e400b984a129602000b860780c3c12442003800001d00449240340c000380180340280e10b40c80500d0061041751060318042d0b41ca2400c40c02040101070b84a8800c6131b025038040034503414017071f41e000030402e0303406074110210070300c03481d881c0001c004051a41c1c65480c0b010010f04842 = true := by decide +kernel

theorem cover : BRFrame.Cov 343884892 344064748 := by
  have h0 := BRFrame.cov_init 343884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 343884892 ≤ n) (h2 : n < 344064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
