-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3400
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:45.825566+00:00
-- url     : https://prove2.me/submissions/584fadea-952f-4646-a30b-77f935eae3de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 611330935 ≤ n < 611510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 611332185 1250 611330935 611330971
    0x120309031b060f0313020a03140c0904020904020d03021c1d03390301090503031e1b071406180124050409020d0c030b040605060901030816111323 64
    0x4401c5400191241c00245d92005029005030360301100000214850700003001040c140d003103524141421000d110340602c000108000c0180d4401ca174a03035001d54101c0310308500401600b401c0f80ba10074a0150980c080000ca00e50400c1c15030080580b21405601c440c0e40741049036141c09040e01c4080300190510210b0000c0401d120030591008403e481003880711000102101050002c0d00f928003811060710300d504000148420400902001000b41c00700c07124a41c51800e02480c41c0e14400c03130101140601d03c0d00800d5020410214420005560840c40f0884880b424604002a005142c00000c4081d035842c000001007212003061211840000c0015178001c034038942000d0001410f001e034001c81c4e00c400100030100004481040c444060750144105601c14a000c0c0780400840b4405030505220b40a503800410000c0c420008075a0341102503038084600c003890346441003134405400000c0d64000340900c24003601a441c1e60000048040703a8060503050706442401f0800303154155585d4000ea03501600e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 611333435 1250 611332185 611332207
    0x3010b0c120a052b110d0c030c08011203031104031a0709060e0105130308042402160303110f010f0c0806100f180510030b030d0311091e120309031b06 66
    0x3c40c0c02041d40074031501c4200d004c2140c140101d6004800c02207102c50045800d4800c003402c0c0c03080c186c0e8200a400d0030890b10121107800741800405100f501a0303071240c40c4180007010321a80080002d0102140040e864507141d1030b00003c140d11848282d104d0704c2c2100300045125200d0807100c0704640068070b07940c03c04001c1c44011035060340810342c410900d00c101d1000200140c007807001000146040300512194020484025405020300110a0219441004032403054509000e000c2e0071603070706082005c4006107501f2910b00301a41580740f10510b502e0504507100d1900d5a40100d921a80740f9030b83c41d00b99580301c1c810045056407008000d000030382003080c46031500d0f000d02d090803003a21401203148552130b5214000f48100c068a01503400003502c035130450300542001c01c0307015041e102d04e0505101000e03400321001020701402d50064480c1c0130015000c0825144120a102e8010004d064031006410004250f40c1d03d9003c4203010f4000c0c4165001e90320903c06080e1810001000108000d19090724986 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 611334685 1250 611333435 611333467
    0xb090f070e0102031603020c120d120905160816120c0911160807120f022a030601030b040c0b0c150a1b2102090d1e020603010b0c120a05 60
    0x107018103500c000c00a0392401c00c42078100c041102e1095004002c0011000284910400d008000c002c0542c0003104070310050b5000f442d01c00310041004d10005200d101387c00d2140ca00403220100034100e4060002c0803500301d0012413810380801000341340c4400710b640c403052800012030414002c0e04000d00c0403020300c02e00c9001c1d08040603c0c284000448d080c42c030810b40c544400341400c070381224140e000040541c200301104403012860b1200f41400c1440d1902c0340740294641c0814800c130b503081e60010140e5481d504030703a035590321040000750448803107686902e0a144110001d50b4182c0c0c06007401180094107042e5442155441c181c5400078040310f600341c00c0c0000701c1c08405015506101d440703030724584400005045040e608842603032180311000e0022003030288a4403041e05800c0c480e004100c869919212002c22100d4142e010304500700400192201c030888113046800254400f40020000902a05e490003504030460040281d9022000720303220b1440500c03400030710a000c07580600c150040800802 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 611335935 1250 611334685 611334707
    0x90506060906190c120c11012607020f0708010614030c010504090902131404200105090d0512031812041809050a060e0d0206010e100b0318011406040b090f07 69
    0x3c02c01030751042c0c1d5a51042c0c40c44800b45a40c1700000c40320020401400329070b01700003002050070308000d9044a1031404100407400b503903005010004041d0081140b0300d2080200b0440d450b40f0000386c071005a212508140606860300c03a60101d850514400b41c4c4502c2c1c0400c1551071004161241880e06241ca02c03024068408448160782c0700071503800c000c4010b900c1d4010141a022400c14140c614a000d00d050030403650024a5400303110514403003458180d8019007280d000810460708034550700da4615140385410081d0318525845200407081c081860081d0710040d05150081e0b0a41d90160411404203803a80600e1080600c21f0303103500700c4c3c886601000e45c4481c4a030350141c025141000710316120501070300c60090205520794029010030801c540e050040c0703805448440c007071050908040c2d0041da610305040c011100a260004080380800c0800303100c06d1910000c0720000d02c0203801c5402200c0311144102c4401d80105e00704501c040c0d103840c000005230311502c50444100000c3c0c88100c812501c0c1c4403a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 611337185 1250 611335935 611335937
    0x1081c080a0b03150613090506010b07060605030f030316020102191b06060b0415020c090406020309071a0a1713030e01030b0406080304031416140f060307080109050606090619 77
    0x140198148584080c0541a560880c80c040c0c3c10085c140202071160800806001c1d1060360319017588000014008a0180d0448a04a0049403220f605041c50b0008280c50343c8102d070300d8402c905804035403d0022010314031440114210001074450841c0c143c0c282c0c4a09840d81c14041003110440e107441c0d01401e0b2002c41a08840345c0c41d44482071030380c4c2c0c000840d84c40c1e070001c085040c0046010840240e5880c00703000140e4003440a010b10003910004108503440c003800040c6020340100c005020781c0030070000c2c0402018141000d142c0c00c16800d0844016921085003440010284641b91400050100866001700b490154446425003581c0b8201c2e0003400e18082340e41095103c0061040320b0b56140a000041c01c3d01c1805142c1e00e924500e001604182180d516803a00c1d000301650300f1851401031480340407154000c008468640e5120001000c030460302d600260b000300003200780004e50358031a500c40d041c2c1c0c102d4141000192243d908000c2e071030040c0d0320f0866100d102006a01d0401b40c0b0746d11001058150703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 611338435 1250 611337185 611337191
    0x6040506061312141b030d02030703091a2b0f06060819020f070614010501090b030a0b0406031e110928060518041101080103170c0c03061e01081c080a 66
    0x640c0d24464240118001c08040101030017002451524007030082c1c901c404d05034001945400c1042d54040e00d800181d11031300a82c2140b00482a519404102c00c4525116000e0fa00080100d180908140c40c48000d0750790f61501840c0c406130220182c0c2703510034a01540c020382c40d0a0040d41da05c0d940e070320780e032500f51201d488415004d0000400d040c80c00400307044500e11031070010621001c01d000b038030b403d840c0c1684513a04201d100d4030b0401032000884210381e003141c00309802042d24025a00814080d02d180d5100a0046200c0c02415444c80390304d00344412003d200d60112001000c88000304212004152801558a0044400c0303505500802c18410010384a4490200d0340c107544d07000060f207074a0088980c0e194215410200070811007171080c144a15030090078000d5403541541c80c0c6410840e0340d00c0c1400a080300004a000303441c3c2040140100c51680103041310306514100c9200900c0d04c00c00300313207041106010341c008a05440c01207210344030300c0c07031b007a0501401d030007030100407100c10034007a01e62a44d640d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 611339685 1250 611338435 611338463
    0x1050412020117151203031005010c050109050a060e100b01121d0a0b0702060702011a090603012a030b0102190b07110102180108010b070b0420060d0506040506061312 73
    0x1c0d00f07041240300d00b408039142c4442001132000e00190894407548400030b9002041080f0040b00035407816010340d0002c0c1b9212102e039450f4501140101003110003d0010b00c03600c809072003045051f8010090441c420410360350250034204c0d500c001e41b503520381c806000c21b0a441900005200c194840d12210282480060341340c0300210043d81805c0d561030080d1120303003803101003102203501001196007240240c802000031103203403411100d0b500c109502c6030380b1031079011001c030790165025001480c2c0241c0250a0f030b4507840444c1d90700414401c200581602180c2000c0b200c682ca0340c00803a40c01410144c0100704c2600e00d00660310807150000060010083c08100e030410491080c2c24800360401918924842d8281010800090074400b01684209014613007004000006011000c82540141d4400c04195420b80d20016611a821012600c40d4001d000441c8050900415401440c0964426503041003162650002c0c0045440340c40c8900b80d408a2005080110940c03078501c0702c1005000380e0071084604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 611340935 1250 611339685 611339717
    0x30f0603080301082805060402061309021602030105060121050703060312020606010e49290903120702010212040b0f0903311e0f0803030402010504120201 68
    0x381081c4c010710204c1d4042640f172040c200700450302d03991410742d455820400310f843d903072071660398140288000d01400001c45c2c0c2442929800000402905500c08155140e12500b074095010423514001a03200350300f440c02181c59075010700e4820040042940b0b0b84102113045a410360050807000d01610105a80c4030800008607210000e00145021198081e060380d08108000506124040c24880e1144621180e040100c82c10600744400341038400502c0002c8000e0b002024100400da000280401d4030344a561340204014a84050441505c2100c600c20401104d41103074158070301182c00c000d15500401003441d0302214070a060b5484041072001503c2c0c01c0408040c0d0000d02002c1e5411103400c5204002c1c07054501c0c0d01d101c10f940c45501d0000540c01d02d0748400045107045030521031007003c10500303901082c40c40c01c14010f00026054611040c0403011031100c0a17000001c040c4114212441c0b140004241d424001c0122809590169900b508090030070400440440b201003049050050360079211401c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 611342185 1250 611340935 611340937
    0xd020402160501050c0409050a0209100c030e03030f0406021009050c0d1e0602030708060910060e0612010311092415130906060e090105030a031b0c08070302040b061207030f060308 79
    0x1655186485e207445038906461035084c0d034406030080c05030900600403103115844d800e040044800e000c5c50105060079141c10240e40300e14181d90215014000098440d031b0201a41c00107004440c514bc2c00c84d160046c000b1080b0048808076500100503801c0707211450311614182c0d005c50360050050241c0799030440b0400803003107581e4030744400301c51b2070b50080100118503411601040c0e000c142540d00c15041d260804070b02860040074006c800074401101802c0c54141c482c81d06889200d848100c82014a503100c0c1880c0f5070f4001c281d40c42c1d0303114808840009100000038405840343c1403004000202842c080c4041108020b146400100030000900035081410898901c15008210700c1c20300160003802c1420041807030320103181850040344a0300040005480000d10658419010f25100c44801100e0b0700c030501c0b8108060004d025220f0704280810f003580045680c50480744210790402c0407032516800c0c08038500661000c888400d002e00006100c55001e6001059800640030001418580341da440d6255 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 611343435 1250 611342185 611342191
    0x70507050724120203061305180a080306100224071b0c090c0e0d080f0c03040f0e1e070e01050c0102070f0b0f09100f270c0e060d02040216050105 64
    0x840740b500c0002610a070340101d20500c40f0781c810003083d0315514102020609816504540b4610166903030001b40102207002c2c0312500300380c000c1040d01d01001c4281000401600166425423051941c4208000800e00004035840c042c150541c60380e060205019400e802008001d180d0010b04c0020720690035240b982094014a81d8032070b803440007540b03060600074006c560022403140280702c060f1403464442c4e91544c00b040041a440000141d80ea406598010054061101b056500740710204d004074000b400220340320142c600000081031260740b4009034000100c055040e130810303110608003190070b036441001c0d800710030b80301814400c2c5001c81c140c3c00542283c1c4076141c10796280081117020010001c0c0e004603a600000c0c0c18840ca40c00741404184107440300703101c07980c04003819a01c8102016142d2150440d50a548842c000029440c80e003403100d000116040d4000c40d800e4800d90310109202c002007003a40e00400c07028001c2c180d084810f42c05e01c0002c3d0b10641000209121300301007132000807002d00a02d44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 611344685 1250 611343435 611343479
    0x40b090f090c0f030c060c01090602070c41010905060a032403050309090711070303030902030f010510060f020a140307030f090b09010518040f051608010b030705070507 74
    0x8180741514070309042000200040384500300802c036494513035070005520350302c480046910a0f580c1020407819030042c00d208800400290000c40c558041c000c90124503004c50f8103200c40d00700720210f080c031445201204440458408907400300c1d107480e0410310a03400b15014030181440881c040e22400000c0e00c1d40c00103040c41d4002519441c004d520300312881d50410303142c44046055401c0c4c6007035689040e00c0b4044c40c21110300880b1004c000401c01c500c1802c120800d070320400c09551070b254807420002c01500d8108000d074046d100318907001e0901b82052181b00e1040c2e44080c00040d0701e80c2003100448240b69440c8030601148a11800034010402800c120128800424000d5a850742d0301e240183c4a8441e14040e43c091100b124010880740b4030702030458007502024a0030759074624180e80e5140c4142810003000f6003261400c0068480400c0e0350b801180604200050394460390041182200d059409000317104030007c050012941450146001e80012071080040e540c0340c980780e10210f254011b204000032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 611345935 1250 611344685 611344711
    0x90e040c03060c111005100b0c0d05032802093618030c010e0f0d1205040c0819060b03010207022101140915010f0e06120712030e1017070c02040b09 65
    0x7c40c813425040d000704001c10303582c00686d0800c01601040b0362a103c66409050500c032001001940600d4000c440e0582c102c620510212440b1401d0100802500040340c00750080100c3c2d0721400842034020106220300c1140f5942e556400c0c1040095000f031200649080801000620862428501400602480c40c0640000503405c2c07030b587c8c201c91824001c803040070000c2e004040f9001e1126400382d203031041c80d0410703034020800d84c0b101d2a0000a640c0320b94813020050045104103c50404100700c0e00d102680a06400d01c00380907032a041500301c0c4501e00c0025808840c21140e090384046141d80145039152070340002030000c0c0302c540b0b2078850031800c540545082e0400341c40d590090016a62050140108074030441501c0d060178051210702c2e6000c2c04444c411034042c92040d44d07031a0308000c22801f90484454064a8041501d009888418001c86452080003420040154540309012103d5603c5440d18654615110035800b0b45100300c07001c4007a80c00c103494032551042501c0b1000d0441c001c22203d500a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 611347185 1250 611345935 611345941
    0x70902070b0a0c050903060a0b0d081c060b040602070608150409030903060e061003030503090a14031804020f031b090d0f02100216270516090e040c03060c111005 71
    0x18040f504018039800038014240002682900c002920360381c001d00f02c5a00180400c000800921000741280005108000c0058a0300d1145c00c03d21010096010f9038000784100f648034401c400d0701d03000394064000160700c156010455148a540119080140686520740c40b285810108064404050094001c51510041081000481d10070201000741aa003c1e00c9141480e090920240019100107010000080080350450b10107001c00391020740d1045107804100443c040c072546036004140c1c90119403585008d42c0c00c5509160080741c80d001f003000d040381e00d5070b62440c7c2d00d0980f510b840440b104450034244080140380c0c603000030920303106014a2000502100c01c0c81044013004c0d01d09021021500928842540b10200518180940300465500410300d540c03c0b1410b2660088201c2c00102c0500744010b200f401062031240981a0141355070300d1050340c0d103039044040c52050550b0b006110b00220507080000c9100c0f5444695880b0440c0307410406e0318150f555242c81d0542d1a882a84543e0380d40c414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 611348435 1250 611347185 611347201
    0x16020d1b1712100312051c0501030606150309080f1b010608060a050a021314030a020a0e040c08070605070f060209040203150a06030b030c040203070e03060709031101090b0d0e070902070b 82
    0x200340d903c41c0c3c0000a000f8800d09540d01c416100b92240d465800340300021804285011955800b0300c8038203032140040000750b9481c100400501f40350b01c20007a072200c84c40128101944680100c0e4205500440050b2410700034102124142d4055061894070b10707482107404034605000c2c01020000c1021030020320060801c007070607a00300d0b840a03002414403407040200f4107039207100d0711204c000c581907683c82030207100240f40428109469200025413001002e040840d022400644103806940a40791b40704409417182d103c0386d0ba44ca030500580020400501114000074203d05501c4201e40c0300d509c015080c4181400424140d070002e903440c0c64407160000c80b058440c100f003407201c0028203542c9418001000307002c01107521003203c00b004501654001000640b0180590000303410040050111102c2d4640030000400ba905580400c40d503850300f291016046d988600692401d1360340c10642c6031700d80f0003030080c0c04005004441e203083e902c0c00ba095000804402900c003038070b12240070368419007051a0500e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 611349685 1250 611348435 611348467
    0x2715190509090a0b011823010504150302180306010302010804080313080307030209030f0102030105060a080414190c1d2d130506062b060902100e030616020d1b17 71
    0x40c1221801c6c0701c03902d007000914015100f02c40c403000c3d07001c86000c0c0a10b480b8012103e5202d039400c400f10904140689202d8907901d9401000b0002c107150048507148100c0c1c040549a80003840080e0000350b1070004180070035010fa00440c0c2001e158242500b0f000e215546c6d015294000f12a00408a9404030350028281030600c01c038098001c505000318503660610000070390b1130007203403841e10400c6000c40001e800c0101e0740e0a802c1c01650424100e0300c1c5044000034620380004407030301c00c031240340340601c00144007070000b000d841c400003440c50400b007076640b400020319090202031403032040d14180c1441207040f58200e241e541e026841a45100300004118144689041d00c041c6c00d050190f01c1031341c4000c070300c02d55089140611001c0c030141c0e81e50b041c1c042e003041070240000340170180d4844036a441d40384120740c1000c0c40040102d070541c10784020750384141030784100c464071013103541c007607000b09503804445441590038055005810001c001c1031040341d103850314241e0030494954940040001c90245c80701c010f0f2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 611350935 1250 611349685 611349707
    0x120f090a0e3918041103040c120b040f02010507020907050406020f060c03010621020a08040606091a06130305120a03111606020307050f2715190509090a0b01 69
    0x80c521080c8045200c0b08480360720700c0c40758040c1e03103420041000800320054403441c1283c001c00034800e0006503440f440100040d481568119410110050000340d030300d407407208004085030092820311999643c2d4031100001c20f40507804a04011f801c00c01000140d5481507083e01a110741c0d0780d519182c90a001c0d000c1d24040c405401c00c0704680c001e4040003400c8001004a90641d10540f03070030314503810501d09000307011085040c480049400410704000b10356004110a00c0b480c050002881034540d1101c1e2401200c00317030302040d20104844c0c088190641441d000034201610080b03007090031aa500e031100c5003000002d484d070026a0300002900c0f0900e643c0350082c0d415240c6d0808605241807421301c030300e8608114810004220030340210004001d42c1c060401c1da48146a200e4059a4803070b001488501c900c4115210540e40c884c240c1c403a0102414655600c1c610f405807100c0c0c040c40c0188400c400307841840680f1449080000030821404a502c484202c2030040b0103040e00846c03110201000900700e0320f181 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 611352185 1250 611350935 611350981
    0x306210114070216050f041103010806150405010303020d1d030f0f01140907121703181506010e0909010e0109030f2601031203110f07031d03120f090a0e 67
    0x6005149106013000f64107004442c82124041c06050010f0b01140145c4000412480f450802200000302180f001c5900ea1191464541e11040c1819200400044603020300000c2d005130f0007500446e881500a108081c60099890b500d003c07481d800350006864203158040c003205542000013072000c070440034051140c00540c0c1459140982c5440c810840d525000c034410081131820b1180b070481030003220b65001414032100888142c3c2c91915190903100407085030103903912072045001e00e2913301c8003140d04034080d181c16034501c2d0854400c0c10030400e108001900801d440e56031003c1601e03000c1c209110720749040d84a0b03241d0364021622540041c201e50740c100408514030030400130300407103a03501e83c030041c0c19680e01c0724000880d0f100d00d48081740201a000c03184101082c0000320080014504005004214030a03a00c050104615030a400d80030100422081d0301a401511118011720b0b041000d400d03c3c104000815082200441c00074a039084140d029074008255401030050303800107074282034912185 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 611353435 1250 611352185 611352193
    0x6101701110307201b011815110f150612070303020a03050d0e0a0506100902040b040e04030210110a0e03060405061816080106080c0109080309010503062101140702 72
    0x301c0c6106066448000c24141c20410840104c007141c13480706040c0041c103d0184100c5d030105051100000d91251903034401d5011800d0b501e20401030001c0000d18200341c90301d101c0000980994200103459400050301d109016010b103030350000d0b80c900304020f000341094101c580c0403494140a02840219110301000042d150070030343d000d00101c0d800150b03c0803001d500d803034810b03550f180360440c0d50020705801c50300002030300888942d00180800013030b10a0081c0f42c085d5641d10b6081c0c0d00c05068080380300702d10907043d075070005220800648000f5600d05500c13600034010f03600821a424440c000701e0303040684c5000c40b030b074002c00c003040c105500030b100d0000040160010700c403500b46a1200740d62440d0050803c800c0c02011100709603c20411301c07207540700c21174000e0f810200585030716a0901a051038010804188651000c0b407042d580700f01d02c014101c3d41802e000c1c510300107045004407460381c0000e10b044d03008841c04005045040d01510f40454240c1190b0002400661103080c0c0b0901c410007500020840d48 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 611354685 1250 611353435 611353451
    0x30a1103071413030503070b0a1a0d080c03120103061505100c0f0201050408010f091e03090612021c0c09091a010c050a05010501261507050a03060806101701 69
    0x207045502500098102010240c035035071905111094483c07941c00c004c00600002c6204c0c0d080041911300e8501443c030b148024820800d15100c23080c2c4124113840029800505500082d02082243d0300801800c404002a01c0c940680ca0a0901c1d050100b03074000c64000d940c13030b140ca0b4041c400319014000503000803140d0b03000310b5200d1000100242c84000014090701c50840c0c0d00c0c011a801017048a00400d01c0c58001d100c0c074185035030b2480062131610002c5e91013103c800020712004452445182046501d1744030a048141054003c880c5508840c40e42d15083d9400c01035500e10021400c0e0070400b5000d51031001c1040c802c0e43c440102205c00580c4840281d40c240520222000c810880d0141c181401f0300e4265011590750610510b00740e0350381c9014009501e02000403459020480b0075031850410b03020b481700d1180031116450399520000f00100d641c6041e103401726108500c94801081903c0442c5000314280b5240c01d201402c201d0b003900d5480310100d061004100c06144044400c0110200350001c100140d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 611355935 1250 611354685 611354687
    0x60209060712091802160204020c07050405070c0b091527070e01031b0501021911090408092107050405060d121e0302070c0510090306020c01050712020711060f1e030a110307 76
    0xb030702c4a51b00030721482e000f1545e0500100c8c20030848004060081060060f41051200074040c05012071055604098440010b120b50100050540f4507990903c208281d03980da01a81901020500b0b96100c260381c00000c0c1c2d650049010031440d00908103a6048007a19495031130001c610000c41d00082c480d508a09000b005240e0b004149151045040b100321128205c1505e01a0306901c0d11801044c1d201e2116000d120034040c0190240040b2041038075415000341d40c0c0c40c10340711900103204045150340d100d404103028905054200d207401c1613001d030001d2102138584c3d540702d00030818245860006454071100192004541c00c9020711543c0c00e00b011450040944ca071602c3c491954040d480c00741050b51401d840d96072007140501c00454100a0031501c032032045403083e0180506071060000200d4461416000100070310844080a5000d00d2034000c0d285c018042c496190810703004d800c0f02d41418402d0358102c18941003035003c030290001c450f076501d142c0074500d07104490380d1110110601c0001e0040003095 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 611357185 1250 611355935 611355967
    0x40617070e3a0c0f08030f04030f0311030313020108100f090b0102030f0a021005072a02010e06042606010b12061f02032802030403060209060712091802 67
    0x2401a09485030202e511440309070540d9269550511060201e2000c0e0a041c0841c858058064844148040003590b944141c0b895480c0242c00b1000b50045041104100040c1c682240a03072180c4a801c0c4001e414440b601c266003142c104980e20301c420b541802c546c0045683c014a01e036448040c28000061040c1480302d188003018450154490a03a5590040c4031aa0300800c1515222100000e03940e03a9011102002500d40542451401c401418400410f0206004138000681003401d2610031085080c440f640c101805803505c4143d051000441140b0480d03101d000041001c1e101e042c1020b104650f5000728540c00d10040300380000c581c2c002400600100721300c1c40449454031308880302c4280c2c0303440f2800081e40307110f0841d010001e80a148020301c9501d80c0c01201522840032440303040c0740422009922515507038040754504006810400041c030000707a242e0302914681c00f01404036800d280071a0b961240c126450601800800e41c0001c0420420307205010710104d10041e01c10540c01c6c40b46c0d4400c48404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 611358435 1250 611357185 611357209
    0xc120a0210020d060e01080f1902060a050a033b010921050906072003010c02030f0f07141c0e010e0904030201090506070f0e0d020d080705070b040617070e 68
    0xc03603400061541c3c04040d250842c0000d0414440180000d5950b009441d42c1c0340c04050b54101c9900030381030b1050a4010482c24000c445070083c100314a04a602c41048079560b1100098000303040d51900400d403510214071107426113500266100c4071440c060f401c0041c084c00840c0d114007450b03041400c0200050b080101001d082c0c102d40080039105c05089100f55000d0007841d00050700044045046070038070182c0001c04c046e031160500c00d0220051000140350030b03500304101c0c210260340100702d5402d05400400041540040100304981008100c0d03481c1e0200da06409410601688007182c0711030100c1d848001074824600c03500300b20180300542030010740142000c1e1460361142fa080400101818004c0d04010f240c26401010348009242509000c0e10700c08001285031300048448020310b00700c1c28100d28103040560024040041c0e100fa55440500365030104400311040d0040e01c07000601c90388408050800f0300902d889000c071884400041040c0d60200620440400c86021010255901d4550488807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 611359685 1250 611358435 611358463
    0x221d160f170f010e240906010b030603070b1201050415080a020906010c0b10030c150212030403030b06040e0604140106170c0c0726010b011407170f0c120a02 69
    0x712400040501c03418050000000c0c0015400e1503c40c40d50f1803c00720b02c2e102e9080c084000100b101c0132401c98040181400c8a07522110341c4424014054407251401456000784000d01312945c003a2140b000e91801d820003900000d80050809c014041d80ca0310340108008680c1d0588d4442c4490f1428080503507424111502a0040c41114049241030f40318902e10601990000a41c44080c00c182110710f80740f40725440103580c3d060300f2100100c1c03c00d0690645002d0700303149900405410740300310900412503001810440500d40d84800c11007041d25107002070702c004c000d01c05903021940b9065080c0002d0700c502c51080d050600c2e4000060000d10341220300c10301c002014480b003151503507a20020509a1144191a44007403040020000d00110b5903c041080403507100d0440f40a0245000614242d8000001941c04122002c9441c582c07d0b44040181c9603060107031035041031030314480c2500c05156105100300419098000b804d05e00024041200e089510012906c3c1c1c1e00e1b00441d011b00a407a040c0205501e0b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 611360935 1250 611359685 611359709
    0xa052a03040809220b090606040317040302220b01020a08030c0a03061e0303021c0c140715050903012426030a02150a060311221d160f 59
    0x9400d00c60380780b041d10182c08000c2c02c41c09040b0811105800400103001d0043c6100c0e013841003044c514108507504a0041c0406000a81420306650b0341d84041005d01c0307405580c840041c0300c00009680c803143e507205020a2201c210700c000c91490146000e035609141014150f611840d02c5900043c8031300122684070242e021000e44035007034000c0c200c000e040c00741d10081d1020403088880100219a03054041141d1098003214011003148000b1403109500c001c280022442d0008281c000c5922101074801c00d00c0314000f03640c900e0f5101c0e5815000420030b1941507000031030200d6000c802d03041c00d110340d00d2515840c00788031082c4c040c0c04018000c01096800b914140c040c003100001100070000400c040000001e2054a8440d030b800c04000b5664039000845005e51030501010646031180c40c0b29031001d598005c420380311188441c0e8140201c0541c00f400c0b03200c045010814821008550b481610000005c1071968450881a00d004510741201c0741c1c050350901c100c0c01d0341044500031160401046401800c218 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 611362185 1250 611360935 611360941
    0x60f030711010603050d120b030703121403090d090618170a05060c070204270813080a051f0b010905040e0c100302070506070807020a2303070302060a052a03 69
    0x1201d850585105000003982071050120030000003203590070542c00c1565880351040201d41100042d5140350030015016080600e0500104880104c00c02c070807001400c0c0708a0104804482624a42c070803508111590030480803459103562060301b18008111500d8010794883d2030408071061416a4420440b1030307034074503a034107440d281b043c4170200d501900030003641c10500c0c00c40000007490780066400c9108601e40480f903590101c1d2400914030742000000303211032104255965060316400000c8922000e01046000500108104402001036118001424040360000d1010a550180603031140d070150130500c12032001e0340d00c0360000c81140d00c00ca9002c55818007265449042c0801c1c1d003030700c5400540d1281c143c50340d00d401da001001460300c910100c80c402d03514100c0c1154030300b10075507400c1c0068008c2202d00002c100100511000001c4c901c14503140c03140c0980315a8074640c0b00243c2180036070010800c00100041900c5900ea0102180102103440000060355924050b03244200b43d044000102c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 611363435 1250 611362185 611362187
    0xf1c020d0c030312290102120a05030a0b0d08030412051201240201020c1207020402040f08030c2401270501060c05060f06011b0309150525080d090305160b010f14060f0307 75
    0x210f5808c052040391516940c4044c014010001c1c0c2c4121410b05180d400d00118031041d00b0140d00c64224aa00040a2411510303295a03041d600900d03019a1003c0003018400325001c09145603299000b0880a44150082080d0004185209100001c048107591044c0300c203030201500480c0b00e0160007401008141d07204520b100050090259403c4241c4042c50841c020401c801c0000050129013030702c0f0210341c1104440740101103160914031249513500360307100040010358030300070180b2048a020414800b200313040001480807a28240d1114000400e41540c1d4004d201c2d0903c465034104d6403450000d0a24076029001138040800b0812a880b0118040c100b8818540708007946070150000340d203030b41000f0500c0c1000800a030010fa450f612000307084210480d01444a03000c40c515298003003115800c0408441c0064006c2601000590611804020440c2e84840d1b001c0b400310140e205207800241941011917010140d1001d40003c0201c9402890100d02580d800c01513500c8030b240f8000c415900d40c1c2c1ca404c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 611364685 1250 611363435 611363443
    0x5040206180612130b0a09051b04090609080405040e01020408070e061f02100608210c0703060204090608060c03242206080c06090f1c020d0c030312290102 68
    0x100820810544805002c0791440940c64290002d002c0d0241c0c40171a141d6107001d0003103c4613904000c01d1580702482082106641c82d178110603440000f48005920b5083c0e44a03d02501d405800884c1c074100002401d100e585803d10840c01248058802117081c00d080c0a03603035540d03010341c0c011541171030240c0001403000c0c0c4ea501c1a007184001071050f801c26860b0400400f13540c42041d8107001c103180e4108140450494400620360181d16030a445132060088100e41803102980020640d10443c09150001b101188060009000510100030001050392501c00814200b0402420600d800da4040003030000040c0b0150241301d0100040302e52403251011030300060145040d5000b29000011251404004904981c0c00003084400c0c1d4001e9480e940c0001c420483c092103840392140d4803c61038084034903517013002c81070205030044950100300c0d15030b25600026000b0000720400c940d0086010018001c0541c403403020840c3c0c40c0592020301c001c0646441440c0000948030000760317940c03061181400940e200f00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 611365935 1250 611364685 611364697
    0x604020f0c010506090a091a070921060b09010e0a1e0c020f0709110a0305091e1c09060c02091902030c0d140f01061b0c0f06020d03050402061806 64
    0x10349565a4a8140415020b02000c84000344603249210004000c90018001c8009480c0d000001606404480c0c800c0e600ca00d04c05443c00c1c0c100702c24401c0204403080c041c01e0014200b2514144040382400c00d00d8080701f500c8509403118040c1e500140104011100076500b2a00001052030200b421754008100002000d401d01080c5585424181d140194603000b0170b07180340d0261441c098618040e1600c1158007614008040600303294000c03c0302495080c400e90115800a4011056424a20b00760002a1000b2078000c2154099003000e05440d46004402189940244440c1040800039190020141c41d40d0383c1850068040c00b180b03000030740d64212050b114070213003003814000c640b2820b00290450081d040448146681842c141211654101245000d4412000c807244900160b003040c0d421510b0070b10540560b4242c40b124030820380004c00f01c00e1403070003420010700c605400728608040285802d0040e1204411b0500c0c00c000d00004d0b0703c0d0700003107030040c20382c03600015102c1d803401004c42c166208036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 611367185 1250 611365935 611365957
    0x16080c0703050f070c0e0f062206090e060f100e010311061e030a0b010504030f0323030f0415020703230d09050c0a060206130221010c02012406050304020405060402 72
    0x180c4413040003040356000c1d0503200c25803540720541d6070f24108100c4850054424a41c80780f000e0000c0c1c000401054400c804411810102040566840303140d98203560141c5007020090704010200708504001822580c5e101007404940703ca06854044105040401800003400c0c40c2c9441030404c0003504e9240884800c2c641c4080c840ca103c0d82045240c0320540c10030303202d50f0489414210141803540c8208203607002d81c0d821059044c13860210796005c0e41c01e40201c1501041030080000182c6500c000704001d5840760f8007040c2c40d05e01c4c510f00340c9422007540000403070050807544144000c4000c0781d4840224421511082421040200166002c1d196400755410002c0351071b00b0140e04100300440400c00c0030203540141d480d440d405494030f00503038441600b140c128101805a00b299400340c40c0080c10190001001014080f40341e103e8006142036901000424026030b446511081400c04086180c10003d140120b030702c41090304160303004060303100141000c0d02c075035250f0f8045031581c0d0b1203504880920420f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 611368435 1250 611367185 611367187
    0x411060f03091605030d08130c08030a120c2f010b042a020d05030f250f090501020d02070603050c091f0e0114040501050d0b040e0109050616080c0703050f 68
    0x25074240e668080c3d4061950b03039060526000440c0c0c00e0010b5002c031120000c1c0c0301e4450650703641e211366100c08004c0710103441c4050209000540d95070b05000510413103e00341d032443c40801140d0303141d00640e502100070700100002c41101c04071640e03880a003106113100c07505104844000c0580528090171488806503801443c103a015500c0c8d0400340d0b050081e4041d02c880c648044da10440c03080c2e0304c5103400c4071004007081d020400120700c1440214080d41c00a404c1e80b40146c070520b685025034440d121441220f000c40c050020a503030040d00184000c0c0205000d200510780002511402515540c00b44211401d00d03480e03501055603083c0d51400d072801b032880034000e010300c4540004506500c02d81c1c49881070110307031034400740060f552103991a40580c3c100410001c2c42c0500d400d004440070351003501410682c503070301c070404903003a6203601500c0c1e15040e841002250303149203818018200346002d0300031240744512040d640f150302d41145c40c00368440d10403242503444040034281030b107891160481203003000030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 611369685 1250 611368435 611368441
    0x110f2b02030615040614100507060f02040303030608100516050c0f03160b0106020606010e0d0303020913020d0e0102210709080303040b07030509011404111201051006030516080411060f03 82
    0x207084030f507072807802c00211002e00c4000d581c0c000994180090144036030300b01c1404030400311103500400007440b155100c8c4e5070006842c240014070008a0308190002c4000a4030350314204a091005c111403403c1d100114001c000f2800c0101c1e520040e580f0301c03100d0030180003011500b045040c0e4140f05003043c0c0c20080041d82e42c3c0f040c84103a8844a000580804c40700d41880340004140c107840061300070b1203908180c5600d40a11814010404c0140f1516070442c02c042c0c00304140c51640d00c0b01e0b03c02c6440940c04002c09a02c4840b550b281a05031802c4001d01641c6030301c14400180c10108015481c060100040c0881e411a00c81c1902150400d400341c0240405200c000180403c026541c11413911078034030741da010840c030b49400604600340c8419041202440f070071400400c0125041c140c2c90103190000615921203c40244101820b40314212a080000c6030400c0003081240d400d03001c2c4580c0185000e00401c603031803541c140504840c00c0907001520404001c1c6108103140c441604842600303500740e211a869203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 611370935 1250 611369685 611369701
    0x302122d010209180601080106021902012307030c0201020c0303072a050316031e051b0a05030703080723030a030b0402090a03110109060504060203120606040905040b04110f2b020306 80
    0xd03a017030340c0c5507002444010000801c103101141c07030018044500e0754510a0500c0e43c0044915a00c50000c4a00603144100c0505414400b44010600540720340c450320811682d50001904041080c8809400381c0c10401c0b003000051007112541d007200d010300d154043c01030b281d10708444110420350840ca03050300c61940d14000800c00c9030442c904880c07190600b4007a40c03101c5180d140307541c1c20a2000421940c0b0881d45281080040c08400402d640087e102141039950781000030300c0c0124941c401e036111030001800109021124100e115040190307500e1016034010118929940e1040020440030142d03112a01a241d5940e901151503000c0000c00403009607849080c860015240c617180e40380401c0d00c5500004106000302d095504649840e0060340c20010043d60611b0040001040e0343d500001c01c200101d03007003101e07100f00c0c0d02507030081023450b03405e15261802a0040c40d04e42d00d40d0b84030340ba4801c1e03014140d50758400d82105040c500c1c645540014035940d803410390220380001c0294503004400c20400d400c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 611372185 1250 611370935 611370979
    0x816031401091709010e0604181104030206040501110c040f1b08040b070e06040317040618050625020904050606010311090906060703050f12010302122d010209 70
    0xa80d0103401040364010340a00060308850b140500100300180600224003000300c5000500540101030400004011030f580c00540c1503402500a540000e54240c0a04940150751090707a0112640700d12071460181940c00183c81805103200e201e04204041081404100007823250320300d58071024000b403008242002421f0041c05249890301c00f4103080e2406450f89030710437100c0600aa400054060040d121350307601700c8101801524098001030208000000900c0c2c6584854000200d140d4058480e800c0460040841040c204201c5003881c075440709200320703a40c00f011125000d21b030068040940e4680283c28140f29805a4065400540d240410040c00b1012848510a9009a800b040320300508140d011441c00352504940d004100b400009009082002c01060a0741c06420118200724099468410039804504441d0850481500400850816140348841808900090000d00c140a0343c401081c40f00003101a030390b5070b0071141840c0c842400398119203820302c2c054000c240d840c82803000f070318203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 611373435 1250 611372185 611372189
    0xf0b1302031b0d02091c030e0f0a0b0310080105060612070e0f181f03050c0d0501090c06020a03020c06032811040807050a0f15180905010e04050601060206070c15060816 74
    0xd48100c0020444c6c0c01c1030022a034030f030b01c0e1b040e19213075041d19001c800e0100500120000176044001c0c49000f140502e50003000d544503890f424004190a424901080d082d0385024081900941c001e001c11070300000c0d07804441c2c1c1e00200344e241c031410340c04081000071100b100304d11f012074000c00d90340c15200c8104180140d03244034140b03403540e0306002585c03801c0c2035107103040c00c1c400034105030040d41a103040d51505070025903886000d50004103c9000c240c0f01d00e201d00341240d204c04056805a4644010103406000c5400902c00842d18182503241c80070491480382559000e54a40100003480c942903440d160b801100b0f07a00d0038400b1301741c4464031450b0b0990380c3d2080d4020140700f403425410014071490110000020341d01075802c01c800081980400b603802844c64171140d54043d4100201003505409032164600070180031520400c942060304160f403c1042c103070054400c5400081c2000015a0441d500c2d0752180e90101c804c00c0d440d20203806001c01030101d034210514500403c10003810501c0d1007051002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 611374685 1250 611373435 611373439
    0x702151e0d0f0b12030403240213080105060609211c02030a1101020a1b060e030f03010603230c0702010207081912050702011706030a0b0103150f0b1302031b0d0209 72
    0x20702490401008246046242c0b041000e41c000c000500c00a080f03020034100e0801100091415024400b10340e0081c1d0b0003d030300700c02c2b44141d8103908200001c0700740100e942143d029074013180b03003ca45802040c200c04000ca10108295600d440c05000441c082000301c01c1104203420807420200c08a00c0252240c0c07018101000003155030005e4108400180b0899585640300d4035a40505410068105c012800c250419540242d03036035065400c108040c40281171340000c0200b1140d8a6040c25400380841d00b25106a540b204200b240b4030210ba5206410b031a0051075403903281d07486200f00d10040781303444403942000065000e82d0414242c4002c8081c851500544250b0145034a842048008c4038240181c401c0070740003800028450346c0040d1090742d0304d6044140902611070030700150312107401c00d61083e84100d41040d0303d0324640c1710f031644511440242c48400c0f40e0078042c0120312400102d81c200001c2c8945d1489a0000225004e10412128012015081800503403203016a074104c0d8000d4000ba00c4a43c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 611375935 1250 611374685 611374691
    0x30c1204032304050d060c020703060e1c0c053408060403140309030901080a0f02070308060108101a030702032b060b0432060d0518030702151e0d0f 65
    0x880302c500740025141516001303030010796079440544460014090052035181507024510703011000c50147c0c0a280d075104802d5008285400c0400c03442e440c02402e04003081d0401c0484080c4000060001c10110024202034162074aa01003201c501c0c8200701804001d081d503040d00410016400d0400304003540700303c1c0a9121000c0c240d0f54061161454801200c540066030410443c2c40304039806055816000381c94800d0006400c1c80c182d01c488100c1e44001340c00d801080d00c0b0790801c101d0390303441409154480c0148000c002814500480c488160054100c011070040011002941c0c844c400c1017a203a100d40100d040e40280c40c8940803491400c141181d00040250070400b01040f202001d800700c4040702c5810010102c564030b458000701c1124020b602514082032044492000f9030744440150000c840410f000244038200994821211085001c2c0d40348a03801c00c0c000100941c1e503100314150549601d160345561101d40c11118000510710260640007030310b020a01c07801228155004007882d20390f0311010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 611377185 1250 611375935 611375987
    0x1104090213051309032a060507021501050307181d0a2910030b1e090f0106170c060715050406090501050a090c0b0f0c0709021e030105060f030c120403 66
    0x41c040da114032401502003010302030440c09400d03c041494286500e44900500c01d500d05649507c141d0728103403182070060780401d0b151204200100710860040c10114000c04a20385402c00e071500150103809640031a40c0d55848030307410340907491488038a0b40e040300240d81d0b694080d40b4140b040440c0c02c680307400c0c548071102210b040c004d00411000e40900f00000c0d00550303642c515541d103100107074005c012444c903403880c2c800010050070703d1508038050001c040107003070402024100c403070843d4010b5200d9140c50318010100c1c0102c14003c11a54200b10040c0c4001da5980c045090403120707516680070380f0320310034503143c10003062040c90703400740c1c181c0361152000313000741e8840740c05600c00d480800002418140a01008200d404517550043c0303c96802c0d403031428240103014a9480c01d00b81c09a202c1c50a0680000302c849050315841ca2002400300d50b6030700349081d541032102264050044410300901008000045030b03071211040d040d5440d0350b44402c04010b407450a4034004000010200903420442e20070049 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 611378435 1250 611377185 611377219
    0x1b09060c07060926060112021f091d04120507080412062712030e0c1503010504050916051c12030b030d0906080a05060a0e09010227010e0103110409021305 68
    0x34142c4800c1000017010140d081c562581c800041040c81260720102207089140001d0b400d0000c046c03010b81c69215034600a16007005d442c086811501e0300d5407210220020840011182c2c100101c43d081c0c41c3c64275913160006454200400c2c8220f400c21400d1500704c0f441002045030360b400458007840030f540100300320f85241c2c01c0903440c0c0d040900000c0c0219001c488101c5010310a80c0075104400142b4211000c03000c00713a0100304413001e4400d4544ac054000001440942001d01038150002d0a00c0e00404101d178a14528007103010b814080d2510420750142c004100c0758079014585483c9801c0100c02060391000d11010700113204880d21103000b4003030480b02203061409041c98004071111500c0341e962951300c00401c180100401842942d001d104d80d074010450481c07150f1110300c503075040c800060399a40e42c0c61b0782e01101d0002c2082d4105070b41100079000740b03c0c0d9100e180c5a81604081c00e02107200341211406034440c0c01907401008681e4408072398042148036840c8110110b8400361070680c0c5202224003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 611379685 1250 611378435 611378489
    0x2d060e0c01050901020319120c262e03061a011806090b090301021b03120114010509040507021015061103070b040b0709030605070504030212061b09060c070609 70
    0x8200d13030243c0c005004001c0c041c0d403500b0001540d480c0e40d2824840300c1110450000480f000c1403808000104808800b0004919a00f03114090308954503415203286491607a4206550310345156400134440c1f92300618069106920440c0555030001d414040c01084040400000c1c0b254100c10b400107001314801c074040310719803040f00c050707404541e0b400d168141410b40140b0703142d120455460705590300700003060040003a820f00140961601001d140d403501d00c0545104030b60010f82005c00b07150080000040a40c5e04941182e4000c0c0040d100446c044c0e0718804282d08040340c49040c241c110741040c8180040c801c070010080207407180b032b4940c442080000f40c02107580703000c0c00d940100490f5844001c100460081080e20341e001013a03240160f0038548950301d1509460040d82d011002c00c901103414400c40c03400383e20140505950000510b62450210139451600420220481d1003020001d40d181503520b0746400c4a1014581400b01c034061039441e54000c0a0b001c0612407080318009030361000e9a42a8900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 611380935 1250 611379685 611379697
    0xc030e10050409020c0c10080f090f0a02040506040e013b030f0702150423060c2d03210f041a15090f060103050916032d060e0c0105 58
    0x66074040c28141003450642c002d5000105210b101d10440c48824116a541c43d86502040300d142c1e02c2100b83e06111442e0b104c0003c01520305202900201c8117a041c10320005420b503041901103501140c0c540f02e00d0003040050000460396500303942814034100d060842124910a00032210860a190302c00c588801c0c50b014851400214154004210707178110304000c0d170003402c52a0700081a652651741242800c07100c90f8030583c052030702ca5102c450003140c88600d0003544042e0f0030043c2c03103080c50030141d500b0b003d8882d540f587c1c190001654101c14140440700c9403010400350069042240c1c2c1e26a6042250442031006507035001252110358000303510304440c521040c1c02298005801c0c149520500348100c0c24030350061013511362030708030b00c0700740d000e07503078a02480d4011601e5a10380c0c0c4850a00200060603a003000340f552008cd4803040741030908030048080b12048a400910500080c60050040983c0b0b901e0f8907215000541190300722424004c0342c0d40710030007807001d10003200c103440c03111070064459009907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 611382185 1250 611380935 611380937
    0x806030115120311160617040b0601120b0301062303010e370303020c3309010b0405090609060105091009180c08030a14040311100516030c030e10 64
    0xd0000304003030348034200154042c600c6420b000781500c803030b0140e2510303245250040d80502a0300f44070070050b154101600e6005a031284209141910709500d46a81c0030310090807880c108003c0c42030100c03a00010351322030b1805280040c0240052551000c030480800800c100046030900000d92045c01c80c41c05100d803143e000d0b070000281c03825083d14a160041741c80c01203051039120307000300390702411400c1c045000c8540d14031075207006880341740c41c0d446c00d458000303510240d52015907102c040340042c98581c0c42c104046034421950a001c0c0d60f5000e42c00d8054900c43c4825031f0458109401c2c803950500108006114001ca68110740d202c1e170361501040349811080d07900381c00043c403480e014000e1216603007000080205a0f81410389103021030341c0d804004607a9510520040e00003140c01041d29030300007240351550f0344013031140c0d0800e82141c0f10ba00c0c0015844818500c2194200c03904103c40340070fa800d83c3c000100307020700c22000602c5410040c005c00300c500e5084001803030390091100703185040c40340c0304803e10341 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 611383435 1250 611382185 611382221
    0x315040b040303090203060c04081c020303061c0605010f0503060c03010b070b04031b080a030623010c020a1805040b07080403121508010e0d020601080316030f120213050108060301 79
    0x85403680011108040c00550405031122020000340e18100205405092590a295900c6180285150400300c648141803080038500c0d09580b0070f03940c00015240c1000044900843c40c0d080c160042101902120008020301d04140c00000c82104003006001225020b0307094039034560b44c0c4900820148400d0183c5001c0c002c081c00030f43d0110303500f0301c00070354050300c682000a011820003480c0e40244031001d0080f500c5850006002c0c40240e4236000b0745004041c202406007900110b14200c56005a104000904001c1b40b510380c01e0640d0b4071015010001d101c818031245040780b007202c1d020040d01301114140c0300e18000c48081400548140c541c01c0c0b180341c059640422400042d02500c3c042c00304a0140320262480c01c2000c03c800e44c081c4200c1d104402c4030802003100c00c407075282c00707428410141d0040030139800a0011403000340803000b00e0200c1950500d020303000c10340a44800d407030010028500600c3c9500c0403030240a8420710601c400250f41d02602c0b8540b00d070b0f80d00e804041c01d86044200102e00605 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 611384685 1250 611383435 611383441
    0xb0612040605060612090c040c0309020310090611070501020405010801060c03051c2022050a0b0a0201021c050604050c04080a08030c070210020618070608010e06130e030a0306050315 80
    0x10258003543d00054002c0c10700c0d2030311078099018140d24006841400340d542044845030351510b4503114035210540c1d03505048c000b42c2d542e900000c0d00c40701040741d406030f06910343e40541c08010041c0c2c00003503515a02146540c0b0342c0c41609225000350018014140031505031400810030314060400e1000c10365041e0384051400783e00c84449503000540100103803040b80c66007100f0304007041c5014075204940c203a503055034841c00d0010190307601c0b0514100110102181000a02c407988807240f81006032002080b0311a80c0c0c11802c101240244549200c0402d60000f40108920340d5010b40c001e240034100c100d82c10300407501c99803d141070764411480f425074607503c03000500b0f00280c5250702840c0e0144895000700d0070031659401040780095081c890000603004441002a010786030788e80d01401c103266000800e595810004003801e00d88040c0201c070060301c0b16000082c1c007990f40c080701183d082c031800d000344501c0d000314580907a40e4001400b41c4000c00d0170a1004120342c1000203039440b04007010100080d25031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 611385935 1250 611384685 611384693
    0x71502120403030e03150112150b1807020c030d0807020d020607050a0e0402040b040b0903060106050903070306052a0a0e010c050606150c240603150f070c0507080f010b061204 77
    0x461000131690113008076026241d16442003401c0c24024158100c0809840d849480c09001c0d6030600d201c58107509180000d821007644560100020195038065a2180d903220010140d1034040d046600320382c10301c210b482950040350300007189030080301160200c88031104030210a0341c0b100401c580a8000a07014822003034014412400d403c880880135000500d4292102540c02c0302c0e03803042d08084240c60000603800e10701e060410001d401080c4603c1d105080421040019846108901c070180c0340d140c03075001050554006c2424214610070f0030300d0368200d91081c884810241c3d000242c0202c00b0441144020140754041c05640300da145d4800050001070741e56404003c44090b0040140c2c0001034144404c0240000c20000001085180a04900c2050000c4c0b100802d042c0001c00d864001d070401529440c0708561003c2003178000c10758942c202110f0f526020120381e01201040041c06501c40c3ca030300080c3c1c081010031840d06001c07845000340101e025000502100e81f00b09900810807001c00380c0014045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 611387185 1250 611385935 611385947
    0x10e12011a0a060c12180806130c1509030206070c09140108010e0c0a09150807030f05011d03070311030904021204151e0b04060b0c011d190f060204050d030207150212040303 76
    0x1190a01b00d80080964035080c20302e103851005c4841080d5124045242c009102e003840c40f000091030000d004000319071580780010014181031000030300400b00800d4007000c0149041d180005001c40110170403c035580c0c4400494440c40a228940306940703010505840010081800c0400d4040035011103e2646001c101078000c020031206c90a481031545800311320103000b070100d500110b000707821609020400b802c189007101d40303045031407503400340108860120203008419500459098109602aa24060051800c6120780603425078810310000e0805180c04c0c01402c5240903070f000c1c404e443c501100783c1d041c080c2210400c14800c4910700c44a43c1c54a07460009801c92410210090404290907070354401070036090b0000e090b8600242d4590240c040d06030b102c8081c01c2c41703154403c0028400001400000504900f00d52030140c10300c81c900b1494000c2c48400c0e01181e00500d000740c12681044030030308001f511080d55014803500c03007540c40d8003044020b00c0000c840100070f810340350040c5880d01c0c2d690103442e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 611388435 1250 611387185 611387207
    0x30b060f16020a08061b1623012a080601020a0b1311030109030c1704090c030605010206070216140a1d090f0606150d0e0105070806101d010e12011a0a060c12 69
    0x1950341003200c4030001400a07050308201c5604800c401c1081c8c200f61134280d080d01c08180b1411004100d442c11070035403148106410a00303106074103000c0a1750303d80000413410300b9010700f8098044103054091018000380440c1032001240202803100c0c00043c040205426600380010140001d200f880000f0302041030440340300d0001d252429001d00d850350704c44481d4180c40c0040003403c08640d80303081c208455601440015841050303803029104c0c00c1e0740e0100d241d0401280f8001c800b018401c80f0b421492a4071030040d100c0180900d00820303808104150b00c82220341800f110a603065005101807510450400640540110f600800c1d02c020b01e0304a0342c044516400c5400f200d404107440340010021080203206050082150750340d251150f03e041d00602103280180f601c02000c1010080703404c081c100d8a010400345045091070200b40d100507902c0002d090305c0c82000020103075440c0228601d100c1c0004010840c10080a454000d1810785d107000640b036103213070400701801620700703c0801e104071481010700401c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 611389685 1250 611388435 611388457
    0x20903120a11120306190905090102030a0c0503040209010b0c0a0212010b190e131109090a020f0d03021005060d0503030a060303090506030402060702010c050f2d0601050a0303030b060f16020a08061b 87
    0x11b6045d035107038010b00582e14203031199021a540003050180c0311880780610340311161581000d500d03504003070703000c5613520005105640108802284040543da000e1000000c419002017145941510300c0141034002c00d401c483c40e5102d0110603280a40044000b00c1000c00c13108480b80b80c00007070f5a032480030040c4164020301100c0884403038213200002e654030303103449010710380aa0050503805040d2061010780c0c0705010714213200724400b140a10000e6400a020056460309900100e00740e15440c02181d1030b00c804100041450001000b002190729555110900b1a07000f560340042907030b507613424814548410b075406500540c00b0041e450155000384e0859120301c2c4034100f1107901c0c41301800300604042036689050b4004d42c12a200d804102c00781c0000300756892075031001e02001e501d441c0001d41c4608162100405154a5030320600854ac1c03480d007a108a9042c9901880e5542c514110004144000741c2c0124403400f19180089444140003c0382403060407a0035482c580c0c0308201c0c3e00146180c016100c506 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 611390935 1250 611389685 611389729
    0x3070201060b04150f08090c010c05120a1d040b0109090504020a1a07033c2c030f060606030c07021302210708040b04020112020903120a11120306 64
    0x102c0504400c010001055468a12401025440030061113035080f6607500c02085000400c0c40008030010440580d1a0000d0800d102c0c0000e15160013420111001030360500c45001203204854560810944a440d42080b50301204911100c01000101c50a070000c1d580021101101400500ca055100c1034000c1e00040c5800a202e6450300429602030b00401c0a400388800483c1e60701c1007540000501481c0c0384070f25414082030f6540e02c86204102c1c03400002c0c0441c04050f003c1c80c0301c502e001e800c11007500d545918a4171079070b00704105405120400684518000e1052409500a8550104246004501c001e1040c4e2560b182d41c5088010703604090401c3c3e901c45143c00800780300b10420703c010044600540c0c4079000c4411011354813980104024030000a20608000708800200008280780d4400ea0900345500984c40c4200c17964000d02504c00480c1d0144a4084002d848000510242c202420969100f2515000b0b100400f5110201d03070702c1d01604208184041441c526111110ba00c0e000c0c1840000307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 611392185 1250 611390935 611390939
    0x10e13080a030e0a1b050a3609050a140d0815060409060306140f090c0112020910020604020411090f0f01020118140d030b030a0f030201061d0907060e06040b0307020106 74
    0x80313810440d120900301c0700c0c1c00e0601e817020450040b12000c00c1c01894100c80b2401401d1900b440104903061805d070043e01d402100000c3e000d010007411140600b140c6400d42003040d40c20602d403d60740c40100582c1660032019904072030740640700c002070540090300a992101e4991320b0328581400414161030310107520020610000c1015080340c40740c04001c40c020b43c00030410044041580c0e030104005045020300d001804e08002d440d0000280130302c964042840d0034194441d190100e50001d0146c4065142c0c44280d5206c48086d00750300040a03401907000321000c01c150440440c41d00a1071050300c1040e6007060400303000c6001440c00b1014100c44540c1800082107042000083c0364409800c840300302c034140d07041562024904020881a041c094440c102003200c0fa0101c00080c0c0c0e05d80e0b02c50320040c10303120000e4803581058400c0d08842b00400e14900550080200d03010704100b004021299808144107004002440d944a2200c4120300000549200e24080c18560305d42c001c1d034002442c8800750744d00d0f0400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 611393435 1250 611392185 611392211
    0x140903100212010603020922200d05061e0f060706062304060506030a2307020a0b06150a0c0611180118140f01030b060703020c09010e13080a03 63
    0x401080c00c00c0d680005070b480700c40c0004034102640c1a0000010503105101c80e04050f00c0704084031091b000050700c4515064503100820703000d098064114034119550001100d0403042d03400181000c0b242e8143d00380104d64440d803d0004018501081203034014a0120303812103410200181e20740040e0140009183c04600d49a03a81070324050341c014a114966140c48184076964400d405001c4d500c101d82c24856a07103030030002080c074040038055007005582c0e00c071000e031950726802c2203a2411410700d440381c2c2070f40380c6040301a45900d101e000548200b00c500000403000d1410301004091890b1018115081c103c02040441d48602d03800000c8681941e60032044040fa036a200141a900101c02804002540b8140c0014200019401713501ca0001022030103000e84ca003110074000304114191418000316049200413805494600600b54000300005100c4050541c0460031351048402030700c00c003505903a202c4092540302c07411078903114448060590440054112401012184214500400c0034500c00e91 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 611394685 1250 611393435 611393443
    0xc03140f19020f0406030209010c14060618090304031410090b070f0e0906041526070605040b220b0c060106120618050c070b042904020f01140903 64
    0x611800c141421800300031400c103211006140e80c00c510305040d4241405074060214900031401100149a000702c0d0025181e4411300b100d1042c260001c0b1140004101c24a80030b0b00e43c03000380d6187d40030721003100400007500062009540101c141400642c0342500d151074800c4044074202100050b8007071500c071101031202a000d20303d040340c064001c001181c00e01c400003602c22484016020306100a01c040030f801c541d07a4074040350b482182603a010508641c000820b403085d03001a00b25200c00d142942180d80c0320090342540c544900c40e81d1040354813880d00e42e031090710075009038030850949030010404100d406e1000d00c00140180200ca850b03404e00e9465102c58442a004844126038640c480380c0100038482d80043c1120004540402c100100c1d81050400c0a4030b0429050034085291070700c01041c80c41c2900c0c030441d6004c07600074103aa0024105454150115292000845a50580d002c0f0f43c03c0c44441c500c001500543d8010a0443d00c00100001500c1d0700d0b020300c440d40c04003541401200160385041c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 611395935 1250 611394685 611394691
    0x50a200d0e1f0c1704150f1401170a0213020c01090218100522090c051005120601140711031c0207031b08031e0c0a0605061018090c0314 60
    0x2042c031580340880c0b059820304a521107012901040352140c194208030160072291034001e500410700030740b80c0140191000181280d80c10800c05207103070844000381101504425410384004400200b0304001c00304038185d40c1c001c04007000e036101d10010050922007840f94010031b4803030a00700000c140c480b05500003510f04c00075009031001035040c4004002080f901244c128020781b108880768024451608010705102040524a6880c6a07507201c00d0414805d800b09070000402004100302814038070904020b11503000119010792146410700800c0196006080214031000240386442c103241681d12400d130300989940f0416003501581c0d000d400c04007006401e00004903010740040400302d1030f500d000004d0401401e4600e480c1400c13141c09100044002c808c030707030b00c10011300c0019000803040c2c4244600c51140482d01890361080040450400605401051007000e00b2030b4003890306103030078000342d440c812032050201c2c80f800308050510142c0f2166000c1c2410b046d4134074001580c09041c2010546e100f00c1a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 611397185 1250 611395935 611395963
    0x5030303010312080a09031d01030b0910060801060f0c060c03090215030907050d050606010f172d060d080307032c010507020a051c12090c09050a200d0e 67
    0x1080f4503505141e000321015411100d24001008107a00c1d680300285a2010110741c04034080307210035a20400c0e88242c000740e220b070000500068060505c0c2d8100d0015022600c140c10218400c0b030b000282d040e02516002055581c1611000d4a4140355034481d0000c4c511001034909255480d1000350150b285c11180c450301b074040560305070f543d080c80001c00740351140d940d11042c4a0004d8100000003d800421000c0e0008820708100f0182803900b01d050b518040b070b044c10102d0040d00001002030340010003aa00c02003030340345882c0142d00050900d00d449c440c40215a19078018a4191000b00026101e2006503448140f138079001409440020b9404800001d4003034880310101740300341c040080352013031003419001100d07800113094800c401d41d1469100c585108062000808106160000074003401d00c0b5180e0300c807c01c60801128000d45031121529003a0b0040710a641e25000015901d80814440c0701003181b4040c051442400001c02d0142c4c00341d2200c0121b104007500c80300560b8901030108001e69130380580b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 611398435 1250 611397185 611397203
    0x30a0306080708070605070f1a09010f05010e0601020a02011808032208070e241201020a0201110901141303020a030b07031a100c030c02060301080a0302160803030c13050303030103 79
    0x18006840303242002c203402c03808240e005450300700400383e0070600711542107070f209050301080c0b007540c00e1001d403d0300004501c000c548441e0003007200c0d600065101400c0d10096500400440e600c034400d00300c000102f200c60740e0140e409459170002541c0a0359086a17128103802c400e0480b15114100e550950300020000084106081061003400c2d00c030440765006030001d00c0081803000d1601005449042c0050301800e121382c0300118100711048640710410400344c002e80000c03c1d11564201340e41c001d60100700e00c140154600010320b600042d1050441c1c411460503500c1c4883d0740e0040407551215400304c584d81250704140500000140c8510000100070b60056145003094600350758041c09594a0341211141c00400c0303100c464079035442c082a401410318a00c0d0196401003546010740b0200c10807000a90f02803000302c000114184001505245035109500b5207801c01020640414100c8460003003c000350000d00000303005600e04030240c501c41940c0a600c2554560700c001003800c644c003e030429030700811 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 611399685 1250 611398435 611398439
    0xf04030c0f0501180611090d02060f0408031611010905010f1b0b0c1e0406140a183f0204050c0d1418030a020a0602030a0b060d020406080612071a0408030a0306 70
    0x11680f0800313240c410422503c078601f903404400100301101000d8000d115803c0811405c15150098081d140542013040c1104d64503806c600105029101c904c0c800c45151340480f03219601548601049411100184c460543d4803010030002e5a203150003000d004200c00c00d1885403400b2803080e0842602544030803511035511074914140402d6451081c404450807a0f04110400c5155817115a001c011881001929100c1d10210300466181640f59000c0600b01940740c0c0204a0581c142400130900b0320030300780a2041d0803c9062500c00070442c0c84030344105110b100c3c0890244c02d25030416030380004a014114a00f4214013010700440b104040441c506154044c2041010242c40c42d0045a08014100460803c07e4094000390baa80e0364410042c130342900400842e10140c29070700f044c0300030840242101d80315490100480c0094200d4821900042d200f000852503605101d011480032408001c00381240c00d00301022004072100000e254004000304110009500c4801d2000d04030801040c0d502180c41c1d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 611400935 1250 611399685 611399693
    0x11b0c0b0919270b060d06060e0a1a0d0207080c1c0c0b0711030417100f0204030c061d090109140a1104140406050a03030c15050f04030c0f050118 64
    0x401420810052110110b0341840708200c40c800480600c40b240c40c4041e00c1840c109040e00c060301c0c0703641803250042c80104101d51265a940c00c1502602c1055440d00041c4003100c04006511019205a0990080140082a8010404000f46007807144004050302d0680f040d07903070a6240d880b400c0040b500d60800407218105142d601c1c1c0c1407945100a00c0c2c201c0001d03a0030780300c07944c07800d4021b40032100303010740c14624000e400c20906c20f4600501c1141190405c0c540c6161038541c8440c2407494648055140c8400950602058426101501d801013441300301241045800d41e8800c0c1318541c9291185100010303541140d0755004900d020700000f000c08a054410321214191240300503082001403400c014424410220302c0041d642120511643c041c00d000e5194003260040c2496000250801810304003c4180b642001c11014864410103000110390907840401d0100c620540d82240902469004140803c1c03040c1c09504109000e8161006404020381d00c83d42151041d241c001e5507802e64480b408140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 611402185 1250 611400935 611400949
    0x705280620030c0d090c0f0f0e1012050a020d0809040c110c010e0d0204240801090b1501030b03060106022103060a0506030c0d0e0705040623011b0c0b09 67
    0x109441d5104411200c1490048a8078040100b0110b0390b44804641c800325040340da00580c040c2504a5002c1402c07070f03100d401a286560040c02000b0903000210300018103006640c00b07091140c1c00c0c00d00203074400360a150a6403000340401c1020345940c0b18105000d80035945000c2c3c0301602610035034600ea030301c152240c140400e46030740901520034010940c005842c043c10108030794261010074685203901c440d01400040c4205d0203040c0203500035103041004141200344c0b010309917000b866900b02c200030b00d95403c2c01c0d0b400da072500c00000741600100c9001c140c03800c3c410ba1400c5880c01d014100801c0344042d10300440c0c03402c81c0990200006074490951251741c05c14180780e02440310000301801d451441d05101103a5820f080b407040358000e03440040002c2081d0030040c02e40d0407442003140240413681c3c1c9004069a0749006000311845076251000c0011602480805000b06c1228880f0b442c10420a03007005403000d251072008100d0104010b000640040d800c640c0010140c100c0d8064661500c40d250300384400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 611403435 1250 611402185 611402201
    0x81b010306060e150c0f0111041a07120503060111031908130218060102030f0403030306050307050a0608161124091203181603050d020609010b0d030507052806 70
    0x1c1c80f0f550054000c0c0d40e182c0d40914074a81150742c092540c1d42002c0152245041e52460540c0c1c1c9951900c03c1ca1086850040007c0049440a90f22200028050f201030720080c4903104c00102400d01100e1400350483c0260040e66026405041150742e40c610074240a0a503400801c0500f0444038007011858001c3e08000801c0e00044803550040c04408542d0110b20481c0207a8071001c18032201d4070004215a20030821106551003000718a900d440e0340c0c0c41c02602400860113541e202e4016101d010a6508090a0701e508666245c1d64040254a90001e8080144801d010000400061140341c09000e10100004400c9040103080000f40c030440301d2a03101c50f118050407030011600486140d10240030310100783ea400003040030030381e02000d0700300702d1007403800c4508141e03c0700010201400000740800891071454004240e006d607455643c0d9843e4103401c0303400500205078031414807081c0d5000f1910400162070100d00c5a41110840e0750b5804804114401c00c00703094040b10034810500b002c100d4140240340c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 611404685 1250 611403435 611403437
    0x7060c1709030a031514190506160507090b0f0405070c02190603050a1829010e09100501150f02030720010f0201050402030303010b0d020909010816082b0504081b01030606 75
    0xf19081c10308003046c0428002580c800d105810385020f00c100c0007550310100c001400004c6c038041d5104244d940300054504054400c1c1c9907030284820000d11881c0e00d00501030b5450340100700f80101070f92072003088000c00c4040c200300c1c10080704030b455400513107030140b0720640070b10112080e040303880c40c062006082d200010401c800d5035003080c0580c082419040702c80d038042079109807285111155a00071a03441c80f282110700114085990000500269a100b4580595405003d60310017451410328081516400c0c441c0e5800001c820702401c3c1418454182071035036490900c1500d1a111258130f0f02c00b92045890070701034040300d551410520300c0d030f04401d1141d0044620b00003071059180540009450b400144601405000c00003800d03500c1d02900e030b04030391412500030904031465840340280b5a072045403a1403007a40740c680309004a05248005041c03880881820b0024102100c0006600c05103802c5031005000d01c81c00740400b04443c1c0091021200740340455001101c5801d078940018155001c0c0c2d84080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 611405935 1250 611404685 611404721
    0x30501170f030301061b0c0905010e0a0e1f090c0305060f011d0601030507090305061513020c03091203090d080a09060f0503060f12030f030f0a0c0507060c1709030a03 73
    0x40c4066008070a8a045030010b0828800b0030001001c1e00c00070482080b001010082547c03404501c003021940032034141c492040001c0003564483c40940b007140c00301a5031041c280c0c01340c030024540c02d0701c0701c8420161079a80e08020030b61101d1070f9664070304060550421112034000d5820070008018191255004144205600f814148405c4841d440b400300a07100c1c2d41019100d100140740300b40201404030086a000c5c04403540740c540381d1000c00a405020400d140b14820981e4020a6101c144c000d4900441050f00618580060001003001000c00d51101590b01d0100b400110b000f651980d0000070b0320f0340140d644aa440a00075001040c89032540c019005105490341d03403a640d42e9222040d40da1050055500741c0501e0101070005221040e504a84a458880003455000229a040182d0301074090240440b90307903216901d01c00705984030341c2101d400082c0309010000c00b04e1720b00d801c00b13405000b0a05100014410408184ca400a0100c500d440d2946c000104041c61503410322900f40480b465003549 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 611407185 1250 611405935 611405953
    0x905010207060b010f0507060e0331060e13052a0d0b101d130f0b1e0d17211909021f090503030c070602061f2106090303050117 56
    0x580540501f44000c4d09556072028101c60030a000c008445601c10712128200388041003a00344900421095503481088051200004440c0d0213010710012410004103031050551003000b101c0000c02000f01402c8000c0c1e40041d00032840c0b148400c0c04420f016a0f0b81c1c0c000c0ea00d0002c2c0d01488252010308440e28010308005140100c0980d01c44007040d41c1c0d85082d030054a040d42d044d8005450400d9119001032041d182c1204010510810b50100160450030fa40c00c491604d40261810800e50340003440330b0300300301c01c44003042c005110b040c040004020714400c07444c1040e0724240c002150101c0c0c080c041c000c1d01d100205101c2c540c04d008102c000041404c403030511044a95074042001c050b41d180d424241c000414001c0900103000d04800d801920700502102e45075a41e2048a5036600300070321805000d030142c1c10110352010543c400050b105001032130340401e241d1400a03040c0200071000003100e8916071901c0e0080028030140218206140a42c1e03022a4550400c4091b83c0b010240250f0480550300000301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 611408435 1250 611407185 611407187
    0x306100b031302061209010507020d0201050c0a0c03020307080f090f0d02030a080a260703050c0a051801030605060313050c1e040903020c18041104180f05100905010207060b010f 78
    0x4903035000d11903400b155441d94591000c2400d0340207401c0f030080084148010040480015445988608440c1e4210f4075200380485040e402c0342c100780c507801000d8004021700c0d0031060003200481170f4603202c3d104880c030701561034071480c11540280002040c04080014a495203281100d64000c4400741141c0c440c0301030400d40d00190781c03030301d424a00410007030011499000260141c0c000c000700880f40c611804010f0003060061100f0b840446108022a1514001c00c2c5a00300d00c1003514060826a1280391604e12446a0803500f110201007403170401d81c5844012820fa101c160146009280032000382d444c40a05142c458182100c2c072040c2d83c0a440c503a884540466030300041c5821164094178001410301b01400c0803803c10080b03045050300061860381003011203c01107441845140a610b00303100200c8034a0030401a206d8140c0307101325500b01d10701403c0c040380304901d0803800f0a206508850010301180c404100b07036600000140e0b031036540170507200c013071040501401607011001d03e4a003100c0444118 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 611409685 1250 611408435 611408437
    0xf1401110c150d1d10090b0103031b061812180e090708010e0318040605010509100e0306070e130b21010204081023040206041809200306100b 62
    0xc00034400da019440c104402c0e00401c00f21116280c81d0441400041e5921000c155594001d040590f090702caa62900c506203080c2c0c1c840c48026507400b04002e1607991958404a541000a072100180142201102400189948035807040c0740e002c04a444c1200010b0f0500c084200181180d81c41403090070070b03015186d17645421039407082e02c0f0007041d208902d80b5009049440c140258024914640ca0010844d040910010240200e40d0480780d624030071070514410700065400714842c407800302e60184803034941490b2400700014026154600100810b20f13201c0083d28040d401d81d80f0502044003001c010440e8100002d444000c2d00c0d0f5500188010203000e00881d01c14043c0d2082e04007401c1000c0d01c454250b1800f90100c80003898080d080300d1172080b42e0080d19000b81100024900c0c82d609254460784008204182103115031340007405541450301d040c07050240d1414a8001d003403d556a80388000009100040030300150804406102000441342c090525008001e08001e1516200750810007900031180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 611410935 1250 611409685 611409703
    0xf170903160c031203140c040f061d0907110106090510031205130e0604061410110f06040614060904050c0d1e050a03031109091611070f140111 63
    0x8044200d1034403490900c44405007003038000601d040c0355500000e861380d905070001081c0c0010f40900c071800d83c07120b9540a00782d05c05d80c45070000f0a540b84030b08019103802402803a80c251200c1d840700c00c0200415001801c810b4040300c108012902030118144005000d22401001c1e0400d054100982d0614a415400e90281440003d00300354a4008070440d4600c07500c2a40d100c0c9009524a8800b6900c1d0070300340240074000c5038801d00461800c1000914075025224184101e08040c101000d03981508030201e80e2004984018440c900c5003045848064404001441c07040f800703004001860405084410000c110140c440da10504801007400046140400d1558170705030308031480c8490244901e05070540d0021081121a0100310341c0e13464080c0503000c40c1d6070094600c01c1d80c04028582e40600c0c071500500500401c1a0001c1030030380010704501000c01c0510307901450b420030742103000301091003610300007594102c03000e010004201003103502e00d11451044080401d003030100417400c02d0701000342c2d0740100c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 611412185 1250 611410935 611410957
    0x90f0b100e01060507020301110301050607060522030309050c030604020a0603090611030408120907290903030712091401120c11010f09260702220203070f170903 71
    0x2480110360030312099a0620014900d00e000750719990f80d2404042c3c05a0403001d003c0e802942801c115009400413403048905858009049600b00b03a05911450000c01d401400e400e020010304003d211042d078038081202e02d45100ea0f0b0041440403070f51900a0518881d1204640680d00503c148001030f5968400002500e010b8500007841c1d01d080c1c10010082d00c0c041d9140f0038004800002c0c001402803d1005000411b14168000c64070b448030300c5059600c3c008c52059010150080b0303048103440c034507031078900d400400d01c19040707040091440029040d980401c004947d0881980900d29120f41c02c0303d0110001e100184000e0520205d540002c0e05811213075101c44e1003e6610725190321007034014140036490b0b0245a000b00400082c000c04a0010481d04c64262004003011582d00c142c001c10310103658040d40a40f02031410041d136603003402000c0500e42e100340062007006098840e1541d69101440c030a0f403c0b42c0d02da80d48805050800340c07904000590340e400340c85141007008545400003040394488808 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 611413435 1250 611412185 611412203
    0xf0609050c19020309100905100206010602030f0f070203070b040e0f06010206060f0d0f06051506090607081e0c16060206040203070608060f060c030c01180f0204020d0609090308011701090f 83
    0xb1001c030480c2103100340c0c028680d010015040c030301c2c50a40d001612106a81058801101a903100c160a0360390f03d1007449080c006901c10400c050120b40d03000c001d0000e03d04c12480b06410240c0c203134006400c0c6015504280007160010800704050422140c0b020b40042c1d195020041c20b043c0b0b200000d444240047c81a0300a0641502c8009035440340e0b0b80300354101c0d410400100740c014a528116015120584a43e0b100fa8200ac8007a4801d140c2041103800c40c1000030702c01445d10910395500580c030b400216512514007000101030034210a80d4005060b4207988001800d1081920100940000e5058000204540c4103c08220040e2400a49941504c040382044441c596035070f40015054054940c0c3c858000d100031842d080c0595000015001d0b05454200900000c502c1d1100740b400000c8070400a48002c1d8021111005400c21754010429a1000e000116095489140d15803d60f040c0300c80071000a24040010010200066000040595290003c1c00343c11440c1d00c034144036002560010b000c55030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 611414685 1250 611413435 611413477
    0x150109151b0206030411030d021f05040302070e1302010216270b1002060a05090307050a062a0c0203060f10060e040e071e0803040e0c090301090212010f0609050c 71
    0x410821050a600e42c0141915600d04e4035140c4130750b076102d40e5020a402442045c41100084d80082408210384554029074180d02d1000c0c582d07040900f0300900182e040d40100d000104000901c0717403030749105400c1504141d034100d07500d01c00280303043e215100032010a202e156051040ca044000c0070b0345680704020502e003550041d1034000004003030641c10168041d20307020400c0e038403035000304040d4031400703481c001000300d96511079100c0d49900c5400740050442d000500080c0010311594416400c225401402001c0004540000403011500c1d01c042000f05403110f24200071480d04103e050381c0100c126071a0346640c1030042c040c8001c00b2003800341d14103000c0604041803994403030754042e00c80001480103ea443d10b5076143d6618201e451071a01d00b041e01e00300b80000c2400d03100001164110b0310300444c80c4002d541c580e0030030051504960a075607890754a6030410405a5070708c4085190b500502d000000c0c88582c100c0d04081211a9940b265140c517040c80d00700460602e02c842519000e190300214200809 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 611415935 1250 611414685 611414717
    0x14091501061b02010e12010c030b09090c0108060d060b10170718140402130905101e050405180f0c040609060503210c010515120102131505070c080615010915 69
    0x2088103030641c2c0540c82c1041801d010380e40764002b1492010283c4080038241c89a280164580040885032404201c282001c1125410043c0200380b085018207000215240d00c1000114580640c101c004001510b55900215200300425499000045414207604004142c01400c0c1d14401e81d20503141511030045054580e86c4a070b804445050407070110072802070b6100c1011030000d110a454902c2c20325030002c408140d245400c20802c08401c0d5103048008443c0c900020003000d0304001f0100c00c050700200792003826000c002c01102140101810103481342240445c02d100c01c40b0180e9210301c06183c1480420012603d000c1091445003039035081d40440e00342c0c02c60112010b4071070195484000e43c40d0004012002d01202103412500004032034a06000e4007200c0d10b00e00703038094141130302c0a002081d1820810303000e400b020141000140e040440c20b0029a40301c0d07890822003503200c2d46454000f40200840303600c040c1d20410381c0003003d0801c0daa1090420f01103640c244c1164280ca018000d01c0c4020140712 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 611417185 1250 611415935 611415949
    0x3060613020c060109020a0201060506040605040302090a091b050f0303072307031b030b0609011409250207140114030c0903071814310614091501061b02010e 69
    0xb50071420101da405581d6138007100020b603c5180c0d0b000041d440c001e4007046514110303040b034045840c90b03581e007418941150200300c0b480740c000c0c0c4030b003040c15a19154500000e04a0400784003000b04d803400e6a59080c945024801c0d40c0400201117442500100f00c1c0701d00003040c0401080c0002c450009041c02d0700032140d2000d14089107900b0141c01044110f420740c1001101c414050141ca00c610140d4059490709000c0c021203000a0040d00e45940005000340106d040541707010b60301801c90342d444a046606443e034182040c005030008001a00300304010300c20305030501d04003513010b80c0a28220640c40280b180300c1d880d5010180c0b2400c00d0060005082050b5a400c21201024001c005134540d507070003030a00310348010020520010b8034001c4080000b1000185101c0b118140b09060341c0d24041c201000000003656165207004484480c1c0c2c4044103d07001c48140c0750340b44210b240074001c009001d20340a4400d881072051340450f007004014104c600d05814001c11007200a0744c20300300b0615040c2654002940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 611418435 1250 611417185 611417197
    0x105060a11070b160c140d0f0614090d0e060f030619051302040509070906050319020c03030906180f07150203280905010c0c03022107060c02120c0306061302 69
    0x80250045150420314200e0101c80400c103118454444065642c6c80392810485081024680d02c4410382d0341c16000726019440c5502220700c100000202115040c031790f444414402c1e04c419040350f0005090340480d50b00a02c0c40c2c0c40da50307c126034150800030b0b01c2440c1070b403501c80107011a0260ba11011030b060b045078401c4480c405840024a0a19402041010800250418031990f40f0610b840781c04039551900444100090750080d56075145103981d141044256a1085021560103d908000d0301c0082481400a1b50003070030104040c0106003400850201c41c0f01c1d0b65500c11801e500990001c84c10003000044105c11101d2a803c81080c80d10301007411317415401642200103560148902c00b516084c140708403512a900705447d82940a6140c034011035100f0700d00080180260100041440036260904011546805070f0407411035a84481141500b0308900364489004944000390170703c2103203450081718490f02034210050120f4103050001942e5180c0241c01e042c01100c11050081008003160105c0700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 611419685 1250 611418435 611418449
    0x408090d0501050a150b0306010f0f110109080a021e060106080601110a050c01020706030908030f2a0702040b091e040303020412260a0f18050405040813060201050105060a1107 77
    0x815844d00400303d5015045418286906070708220700880c1d2016048196401402c06954104068401c40c80a88401040c00310140900c902d00c884424a1b8909001f1240902d1081c3c0d5640d4642072200d001038942080141384000e1255140716164940c0c17030024a0604585035460718540d25140c800041c0e44142120b10008168002e40c083c0304148400000d03c2c1780380407020303030883c8c0d80f0b180e0311078085080f05c10012005003069810404100036208520300a42c00c84000420070300d40c0240324690072403020103e4542c07120707440c0100d186825498203100b441034501c010f6800d80c1d81850070b0091480c03e0346812040480854122010a05262295040e07402819140c4944403aa01c203508041250840444806c00c40c9000003000d40030030b800d06004c5e5113400f046915608441200c0718800e07502c40100d000e266807500e100410009403607455020340f43c0100e0041e034006540c0d8401c500300b940346481641010040d68105001080740b501c580c03041f035a00b00260b14010b00d901381c3c0e80f11030504100d2141e0040c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 611420935 1250 611419685 611419691
    0x402090a080a03081510140919080f07030c0b031005061308060a090308060925080601030b0103090b010512070506030403020c100e0105070605070203130602010605100201060e0408090d0501 83
    0x45120040000c095100c2c60007074a41c9800d550b05ca030090014008905103c98110320f00401c40b5203002d0003071402d090182c0e52401001d042900c800040b41c0f11800c4409001440703a041c520030444c402d420302c030b000112400d100140084508503228020b2659a500c00d03000d02440010005064160191145010700801001142d9881c101104000414418041e2504602910011821040303152040c0e90001c0d90589850b20030390341f02c1c0104401540c1c01046000e810010040328941c540401442c52090440f648980d00e290801e07034001400c4401030b4118906161518620002003040d407140316044800480b104010318500c4682c00d801c1c20b80315071200d0f411800100c01d0004054020480001800054959030291042e242003218148101140760f03010070400c00c50b6a020444981016500011500441e890300b14150450005251258042030050755900024019454011114004401d5920082c0053f41c10030703034100b0001d8800b50000709002d800191040841e20307202c0b040002160408020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 611422185 1250 611420935 611420939
    0x30a0e01200607091409070e01140307080f070c150506010507080c0a02280905060a030f03020f01060605090105030c0a09030203070303090f051e0f0a050a03200603010501021504020402090a 83
    0x20030b55628043d00e6080108005603c0407800048110481c620054001c182c01195119000140c0b90190341080050400c03d5000501200495410055000708460382d01d172020b9103014040c2c00c50312070010300b4040c00c001c1d80c06080d20100b0030b22402d9062841010600140d0380d1600780050760140700f6290011708101001c600d0f801001e401180d1000e0b40c1c0d009860b81000046d4010004d0040203070361188440c041440c0000340180141513100c2d07036100201600c2e03840c405450742c075103405104e40260100d006a000c655502c107a00c400307008400081100341001c904141344007002801e6070100038403014560302c0218540000710320031f80303041c0f005507000390a4519554803400c004044005a001740c4e5407021480c00e00040324141620031007445001d18011400d05100d01c2e0800c0610854056407980c8040780a03c00b05459403104d40060085126907010b1040d071400c140303104521100455400d01c1040c061004211036600420110400304018180c25216511440021300a004090f90103802c07100420f00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 611423435 1250 611422185 611422247
    0x14040801060320040c020604331a010327020315070206070f0e0a050f040b03100e0705030a030e06070305130b07110910090e070305030a09170304030302030a0e01 71
    0xd0b00d2943c1041003e207000c0e4034070103040c031058070890081180141d2282d400075000c18020380d0780031210800d41e6981804201c89900341c810a0f000100003600e816981c04110703401c14a9042d0141c4031002c00c0c01c00b4840c015000e6034685000d8001101d60180b0b641c000c640d44215641806000140d4508001e60005030074150300007903079124200d910202003414074810300720b40350013082c110010400040c407d0b08803d0401d4240480c40e4180d0120b280c0082c0c48244000565a0a01024200c10041200021080041d880300ba00d0014250300172406900181e40e5100400d5201c0c1700c2203800341082c7d072000d0750b5000301d2a04035441c1c03054010500c8061500c0c0c5001c00c100c090840208056401109450f510032118801c1002d480819140c862055800400c200f098082540009440c540c2c00c500381e9401c80e40d139072101c0c1e04591010b000c1000251130103205100c1f0041645043e1f0204403010025030400b8203643c0c002c0e6507482400451414401c0810314001186c1c4510b14116421307551001d03020803451103102c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 611424685 1250 611423435 611423453
    0xe030a03090f12030915020708041401050d051603060f05090c0307020a06050405030d0f180213091e02040c2102031015020609060c1e030a060f080303090d1b0201140408010603 77
    0x1040b1b070310f20001c103120380070742c40c0c24002d030740c50150000c614605e45071038546503108111108401c02e05000f030038016144000b141d4801e55102e201901741101e0000f12224000b002c81d841900409040b0452107030900480d12414a480c0d40915070800080e580e40342d595040e450580c2d5050020b007080c1c01c040803c1704020010020b0400c4001c1074000303014218581380c611003a240604003415054000c0e41c9003501501d05013450207180b010188000800c001d8a840b207080100000300400c1d00030412521990460419104141208059140a0600304801e60300403101000d40107000011940210110302440402e8440d00f00808410750b80318405800d296019427030322001c4400101c14001d000c001088008000100c50062aa200000c2200015441003211035000540038035038403581c0346404a817002c2500040805090004011526031030a48070451034404000e000100300404110220501c2a80001180072990309082803000740b00440381c90b458078001c40e400329900b0340c248680082481400c2d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 611425935 1250 611424685 611424701
    0xc08030405150415080a2423031b3001050601020c0604061812030c0b090a02060301121109150102070503160e0a020c030a030f050a0e030a03090f1203 66
    0x2440c0031642c2c5101180140b80781c0154880e01901030781d030881003103d46106045490b4003507448031000460901580d041d0b040c01c0000340001c201c094202505000d51006407180d0201a41c84452907007101d414000826124580c000f1112901104203219242c2c5070707031b02510b07941e2000016560640d4240702c459030782c0c950009507004080e503501e420086641c81d4808141d00d442c101c006402d0034075182c900401160301442411421240c60018440812401845006031300c3c0c0c01c1c080e0350340003481103103410704400d440806040d0b17150540c800410100180c40302416641105c41c40c102e0b00890840d14100900301a081080140d8001842c4080041200100301819140c03502a4202c642d4144c554091580e90076600049440d07a170542c407000c000c00c200e190b8a140cae0212003403002609109601c014185142c001001c2500400d88510b040444039840c3d2003156407210700f0311014808090540041c50b1203102c1c1030390300820580ca800c0c1c00e074181301003003801003181607020102c0030300d0003002803005000709112 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 611427185 1250 611425935 611425939
    0x204090c061b021f02010f060e01050a0e01050a120302010915060815040209060409260a030f020310060f1b0503030603060612060105040b0a09050f10060c0309050d0606030c08030405 80
    0x10000b038902144460301100c1c80c03a074007030444071513142e207920700802228604003404219034032568152031300907032406800003d0050700010701255041c081048040d00003500502a421450b2004001503920b401c104000c885049107184810348103400c08a02400c018100580085c9840c8030200b1446034540c000c2e011143c0180903a00041044e1407d50900e06050303401a40c85085200441c02c90b00c0c0503448020705921800c601e41001808410131140e0003000b10301201c03a50300100e6405074854040c044c6030001061400c045186180506801c1800c20a47c0101010031001055469a480c0906201c480e40607902a070f946401016250070f0f0303501e0b401164524000d0084101280071810002c91304034001d5950000f5005680c2000103000040954a01072a8407000d0030f20009540c419900c58240039000303100b155a02454040c021142d0404540e0000c4200500d000002c00465405420f007010346400f2030392650900310500b45800506904d4001404001158074005800c2d1030020040040f1402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 611428435 1250 611427185 611427197
    0x20102010b01030e150603011506050a034703010608100c0206011a0c0a06020324100c060e0a1a040302010b010507170307020a2f06040b090613030204090c06 69
    0x105000450035607411500c0004c0d654010407982e800b143c0e01d0a41d01d940840b0241c0001044105184100348044041e840400414800900020354039414000c42100b116610b4558011030a5041407e044600b001d036810741c92032100315115602c02844e40b220b18800f0000300207100507030700d441100b501e480050080058840c40c0c26805a4a6800410018120750f18614522031001c0c003050112481d07401702c076414403240102c48009002442a201460280344815000b19100032112201c0d9000e115102d001e51140d04010101c0c038101e03034060701c00b000c000e502c403201242681e80241c43d2441d02480c1c0308018014041000e103441d1800709041c8841c0301c0c41c0294001c4c807070b0383c881e03000540305449500c00c040d200002010b82140704a1001c0021038000d1280e2044842d02d024546403441d81e01e0007410050700c652281c05400812041005c0391001d01102144c54a103000c0c5403d044500c54070030445094010324010610313250800e40314072000000c1d4dc002e0803d21040040c0d1811050b241d0440c0202004148 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 611429685 1250 611428435 611428451
    0x4032706020f151b090a380d02070203010e0307050303040b0a020a050d02070503280e01031a040e0a05010c0302040905071b03121e0b0f0909190204060b1602010201 72
    0x102c0d140d0070500010408000e488048203002400340818400c01204c0c010000500580c4036421000020b01901c80540900613000c05254426010341c1e000140c0d01030304403008005440c03000b04452407416408001070f5520700e180b01081c0900882c241440a074080490120203020b0b0200c029807040388504450805950b510341080100e001d51030020001410500481803044142e0b4010900d2a000c5c0d01143d090401c842d09031440da101e4040c000354000840b0b0070024480b81c000c2d45a894901c13090905100c0240c9503c000e010303484150600c035100340d4903010813a4140300c0034020064240c0e000b4000f070040741c01403007018001c1c2d4420b10812428030302c1c01000400403403045020300c0036091220a1030303040030103984088402e00b200c240c001015039921242040340540c0321108440d0040040b07804581d00b102c070010070411855080a0302d006d08101010003200d424085031000741a075200c5178640d0703841001e00100d4010300e50f07038014005a8400040c2e03440c05592912815100038401d9009200ca00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 611430935 1250 611429685 611429713
    0x10b0a1701030b0420060d060906080a02010e04020a03020f030f01030b060d031e02030d02071a180304090207050c0d1a18030901050315060f2205090606030403270602 73
    0x60002d1001800000100f400328002031030b0b90224403501c8810284540d18041c510000031000c0d0b125081d519045582d8500420803030030140a040014030440010704056030b510f400103040b0304190b0340e06502c43c0d580058902509402641134811400840c10055200c0c07900302e0820030fa4a40a000544041c0034500008201d86002c00711030006e103601d0380c0c80d90480c00840000401c5507070b07414000402c0d4041409160003d142074400b03032501d00c1c010700490203d00c0154060107002c00000e01301c5683d141d01d5004e510b00a1800100b11021504e041c500144e0312041c80c1070507810040c0000700d6552150030a42094240410816040c07074805006141c0d08079511492580c0440010320b14a14a0940082c0103000d01903008201542c3e100164101107491100001e001441c0c9a202030408035960001188107424445601c2c0e0038215100070041c1d80d0306031801e0000082e0518401000345104600000010b001c040c4584460002c00040151620340918a4241071400709014000e0b14014442c1584840c491 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 611432185 1250 611430935 611430977
    0x403031d03030a0c030e01031d012003040503071515090912020a030912480e060d110306010602010605010329013009060b12060a05060a030b010b0a 65
    0xd038541c0c3c0360f1145030500f551702502c0411482c3c241074180340e603c40340b049601e11941d00000300484203038000252005150183c640107841c400d443c409400c030600401000500c00021a600590002018141d000c00c010841000d092100031040400c03081e520006005035494015660041c03041d104002822900703803007269140c0c16500060b0001c1c540031400c00400b15442c0c07014203524025480740e1429171165503000d80200424419103a1034400f901102415103428448403816032142030710151840c90301d9002a11124058103640c4244110450b46080181500d41d401183d58060b090b100b00b9030792442c0180c02054940b16250110707092400c041070a02d04400803040b00c049600d601d120810810004480070350300010b060800407600000c0c0d1410040c4145510800c48040c040071500066528084095980004803217008401c00310b40d20b1110b80020a0a40c4e100c0c0f039010000580d65100f800080d100c0b44503500182c1050340850010a402896030002c00c1004070b01e0712094007181c102a044041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 611433435 1250 611432185 611432197
    0x608011b021504060f0b060c07050a0602031306030f0204051c0210210c27050a0909050c2809090624030b0405030702120c0315061e03120403031d0303 66
    0x260030b0001038005465640502119501c81800141d400b403070301c2c0860b405a2082580942d56401031004000a01c1d02080030b90291a0f14130203141010b0441a99201800240c0a03400605131121b40c14400d500843c1d041d1401090700034a104020940a444207460001c01e02d2305034020800784402c0e51006000d218150a20002851b030400c0c21106001e50100402d8090054810003002144040c080041c2040e03056000410140c00c41c3da4914050030031025074800d80c0141540c42c141242d00700458004545a4425082230351410540c1c1c1c6034041303082c9981c0700315043c5060582c401c8000310b0f1002c0e450380003004d920301c61041004840a40d9100400e00c0f001d050480e03a1600c544a400c1c00000c00c90700509811078410000c4a01300b4005034002450a4018071040980b139021410a000601e000c02040d00c8004003a10519018100303240891050601051b40d00d240200c000407c04a5844c01c00401c1da0100121080a448945a1500420f000100044c2803189100006038005500d804011900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 611434685 1250 611433435 611433463
    0x40b150a080f0910090c0f0b030a0513020a0e09070b04140307050f06040510140720040b0321040f060c050d080121060f0504233d0608011b02 62
    0x80c81000c440d13910703000340100e0b0034101c40f0540900300000d40da400c9604980090aa0103d13111f07140e14081c0b40c25022150002c00c400340a040140d10000543c560b101c00c0e100380e502419103030040303648411025140c509a54040c0354103150000c3c00003407803d58050741c0030100100320182e603c100c0c0c2d500c0c10000ca0000c480041076010404000c200f2403490b128032800c01c03094503800e000c070402240755107004036504840d80c281c640094504100d10303484582201c00021080440c0c042158981c0100840d03a0340421070540d110310000400c0005100c40381c1d9040d5801000054401654a502c55200800d0300030741d0003003140c0620134540d95584881c001c0500754141c1d2030100805180d8400e0107629110400c00d098159182540e078201087c082d541c40c002c492041e40900d00b0161119254051a00728031071031465400d0682200d500ea0710b4110881c0c4030381c0585c400801d811107541d0300b04180c0a00807000b08030312818032454000c0000300c00406400402c0080c0c0d9901c81000944039491003a0385403480e04207009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 611435935 1250 611434685 611434693
    0x70203060f0939030a05030703021b0909060115020f030d09050d0c080906090a121b0506040f030605150d030f14031909210e0301061203051602040b150a080f09 70
    0x2a841c0e52601821202000001c4c100c4070604966181e45055a01c00101980181c000c81540a06c2c0c1c80340e40d0b419040c907503007521086001e18001034029141c1a0600540104625800312410540d1003080260304484250081d26500c0d00d240014a00400344600120351034000c451000301050701031008141c0c4c10390400c001c40c0c507000c000f40c200542030b40005169a404060048082580000c10b0385c40480c8500c04d00101d0701100c0e0300f0341805024222903018501c030364800c01091254014215004049aa0040c40411070342c4444000c044600c44100d611500045000c004109056000400500300308403a122490004c0880807242c08d0361000315000c0d5405025849a441034a07284d80c0100c0141e80030b0400c420366240e40840c280751035041c2030b10f044001070030503240829030319082c4103420061804c00e01007000e001c2c681c2d07000b0384280510340c08500942d015040c15020b40d00c1d030350451451840e0050446c10440d418004c0c020580d08450301c60000030702580b0008041c94081601c05014841000c014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 611437185 1250 611435935 611436013
    0x3060a140603010e0402210c040e030906040513020706140103060b0a051810030b011e1d070c05030409021603030c0305040b130317091c03060e0f0c070203060f09 71
    0xc0c10740003a005e00f0490308070b09011211800b4080803190b4410510f02030020340300c01c000b5001000290341c41854020340c99041001407100d2555040222000c946c010b03100380c4a50002010140028016a500940709c1c50405141991124507450140d068a1007a01c041103084140c40c04d002040c00940281a00000d0580880003002c100040e6644e05c204250304c1441a15103030340c0d44480d408400e90040c1e0a000e0b01044030110000e10921820103080400b6440341002c0000c01c485500f00005402c003414844410000c070140700c0144101d40107080c071050190360303510190300308100b06038116070250b001038981120305c6041c03803290040c1070103141c002401c5000d540b181040009400010b40d400c4007030081c0e20010014a103a0301e140e0512601403900609543c244509090401420024070981014900081440516650000a5004610380000201c250340e41503507003a19100d503000180d071510601c2c0402c0f0004130081ea031184210001820350700240310100d07100400b580700d11818005281d8200071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 611438435 1250 611437185 611437199
    0x3020604060c0f0f050c120312070c0c090504031205090d020c13060512030a0f09060504272a02011a0f01020c0901080604060c08070507020d0204060f0b03060a14060301 74
    0x7800d0b050307000c1c0e06065103100c40380c0d880c9480386003100001c40b042d41151a429026141ca98034282e02c81e040480035601c0c09036401640c1070802e0008100e44280504681e290b801c0c0030040e0708040c06084c00c0b00003040182403d06001e40100709204d0b10506180c14103002a01040d070205403080700d5605030b0001c1020311010310030014008200201016a25600c00c40010f26944841281d11041942005155200c0b800e2000815408954024406015140c50100211a800021a022115101460642580c002030a410300300c46c090300b82d4101e141064880c900d840305049220724040071070340002c01e80b0408104142d00f80d620310b6075040c1442445698a4100d0705081c3c0b90010740d810140b040e0745100b0100000940f604200781c01c24500341d4401020070041000703034442c0c0e41c0c2040050030510100e180c8900018294072600c0d20080c0100e060302c40c0341046407540d17007084000d03045041e05159801d855074000d0b03e01d80c00403601180301c0d1104400c00102d010024412072851030000d000b02d0300d507a080c442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 611439685 1250 611438435 611438447
    0x90c010309030c030e010509031002040306050627060a180c0e1c060b04060302090405062e060f0201060906171513080a110a0c06081f062a03080603070905010302060406 74
    0x115040c8a4200230340885590144013002681041c80b01c016210f90031030810000b207980043c041c81c001d504600f020b1001c01d103060884840b80d412000c01c4070103607903040d010a1511a86030300c4940ca603244442c008030001c1141d0440b8500c8079040d0340302e4112944020800c0088030103004c0071100146456805070126019400c00c421031480a80003159842ea40ea0116503018400c0f50143c90320340200c0d05018650344070018a103021003520200402a681005a030600b0200902c01c001c28010420005d01da181e00070f401c0f48008024103c0104086507940101c4000724190320b9200341d0314000d0b550100030321465204160300a51903c001030795039112a03500d0000c00d0b480303d4100c84c14042d982c05020a00c14082009824940c451404818100c2c84e00d5006881104060503440d02c8419030311940e0703400081c4544000480d03580d49014001d8500c0070600d0035500c411b03a4140d40c03075a40360b40042414983c1001e141401280203504440c800ea548070182000ca482c20300000358043d6041100f0091a44504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 611440935 1250 611439685 611439707
    0xd0201050c0d030b01120903022a0a0803090a08070812090d05030a1805010e01020d0f0c020d0503040608092a37060c0819020a0c0e090c010309030c03 66
    0x30409038075110001c4555442d0000c5401daa600007925614040c601d541e00618208290012510611820b801550044c1d00ca10000d14034074402c4403180301c121a908810340d09014250b80150540e90b849817149103694503a1f0000840740c0c000c2125110001c2c0b40200000c110f030841d1200390141c02c6030500030107580415400705500303984c4118a1203420000c81c80920041004225039203d402c143d40c0d04461042c00446a64840c0e0705000f2441400801079801065112090000d45004000e00c0d40c4402c081c0c400030080c6001a4000f81080c034408100503001000300140d460380d843c0c8104a80c0d80454040e510b640c0c01c07402c03202460441d540d0001000c180d4814940180c0000d03c94840c0910f000f03201c41071a1454650220480d040a84046a80c1c20303009129002c0d21441c41d0540c6624940d40302e0703a52a01c10f80d00581000c40c00d01000780f140d60320038405601c030640c4c000e140e0b1180c00c1d82d96400e240302c00c0060b20500124001e14482e4012503020f0f228071400d03940d06440e00700400d0040d4400303441c5200c1d01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 611442185 1250 611440935 611440937
    0x3021b01140309030c2a09190c03020304020406120c0902070309050d1a0714120c070b1602070f0f06111609090b1b070b090f07030606140a0e060d0201 66
    0x101007040d1000704408051071103410003100954403400c070aa005407624070180780d001c013072030303030711a0011024011006400010101600c03c02e1113515140100e804c618000b9018000c01407420080100326680b40e002140690f001702d8003400f404e40c60b0064a880d11402000081c1100b130b0b540010010031040fa00a0f00600e07020f4141054001da541c00464049035040c0800c8908004200c000f2500b141d4500700031790440c505103825028800c50503000390301d510804003180f80025614000985405140003110f8055906c0344000185081c1421440070310242131802e00d0140c00740784800710341401140c4d40c580c100d0745000d010303030760b2036103031400c01e6501c0e03000d00c00a042e8038040c8036884c03200402c0400300040204544035000410000e81d04040d00c01d040d01170207e41e2941e000d0b00341108105441807d031003a844d001075000d501d035168030000c2841c00c00c1d0023084044c01e009181c000402d020440e44003d00711464442c903015641c0c95101001003421040c003d04101c0014140410204e040500340941e82e84c1c41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 611443435 1250 611442185 611442197
    0x2031c0207060c050307110d020712020d050114011805040b0a0513050f030c0f0106050303040312092706060f090611030706050a0b0114040305030a2d0e12070303021b01 74
    0x10702c1c1c45490546041059290100f2800401d101425a00c842500b513440c40304005001c0603071800c10300944800f101e20070851070200341060001550307100e0411410b03060388030000700420b5102a0400305025070920424194640540342c01c0d8207155140606886154020116001596900310400062902800464010810150a500144041044802100e81d0308000d507280c0e04100315482c644202e896908031140d0610108101030345002060718150b95020394400104004424112404e098075070000104c43c005662501c4140c5114070300f56800d500f101001e001c401d8580c8000c1c0da454100c85c01c1c810001d41035603000c00506201e2a42301004040f01010743c0d00d02541c649909068960698103e010207907119980781c12983c00c00c465004880c04412440c1c24545180c0780c00b910380c020700d0204003c3c44034103a00700403000c441310341441042612030340c1c2c800c00b00446c84000382441100201c1074000c40f80321039541d542c08000122542129030550040046d80d8249101990600c030401034617040c054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 611444685 1250 611443435 611443447
    0x150c0405100c0209010617010302121213060813080711030c060a0e09070f051801180824010b0d020c01090203010203090a0b070504140103050403120e01090b010f050102031c02 77
    0x1544540303440310000c9942d15508001c4103401048811101a4040c02c180071109600c074116644c00e100b0341c3e04481e01103d0718140c1e117440c481d565050103a6034440000f0090002140d20710008100c2c0c510090310402d41ea02c217099a142103856800c80c55030a805001040b06021400c00924030061841a003200a42034415240064010420035004000020013042c2c105100120904185040d150702501d04c0c07605200741d5040c0c0201425034461090120101d0740300a5a40503113034080c54105060030000c07007a10302100c1d5a84107064407206620b1113100f00403c20910060046500c9031100d044c0c07071050351031618040303119000000079484009040b80c0c0e55283c0c03054001580d001c1c8040c1d0302c41c0301c009002d0456403440b4a0110304040005000d00c044c0403007408140318040c0f0345840304080350400e003800211512181010b9450681140c02d54020074100090314180c2d00064112140e00ca05c218949440fa07602e0305820020b190303d03406601d006a1040c4140c5810403024a800071800711142030061801c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 611445935 1250 611444685 611444689
    0x50303040b0d050f01060e01081302060f04060206100320030a0215030414030307080f040312051819020904030e0a090204030501060e2202010f02030f04260a0302150c0405 75
    0x180166101100c0c0810104000310100038038064035a0140c1034800c464035542c149000600030207e4849083d04021440d40010310f0400b2003590008036940050001d0b484280440c000c8400d503215010300c0005024140c00305480703a4480c0542c0c01a80d50000d01034100b040c006c602403240a5a04032095418032400842c880540c580b1184860740120600c202c666074609030501400400d06203001901e00e034020410070414691240e401070b045804000915440d84035403c3c100c0f410380355008180281480c040500980f03589007501100b83c07000203815030364840d5000b10706064401c001000607421640f2840040d00103403140c0c4c81c1da03420002c0140810034107603d6038103100480e003260300101c0d010380d500d0030284000c000e003e6105a0100001d140c4400b10004411511200415410000d0502400020801c0d40c14000d005540340000c51041c441d44450356030014007013480c201420001000d45015140504a802240c204841501a0000c02485110003c2c2074040c0100525480c054601400085025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 611447185 1250 611445935 611445937
    0x1b12051e0a0c0906090605090d0c0b12010e01141e040e1e0c0d2f06071a0106140a0c0c030b130614070e01030f02040509040f0302060c31050303 63
    0xa64075840300044903036900c200a40501901e81061040c03150103402041010391100c111907a99905880c01c8640641610789490743d030096070860900c403d00462103001d018010424103040741e86920b500d4070266603998010304840c080c18030094028a8401c00c1e0100040c44440c9090704103405400020038100001c5a6414520308000c035054818440c41d104000800c20000000d0040c1c080356840f015030042e13a80c001601e0ba8640c1d0050700c1121111603030038580c2c680e4040010070400034104699130b280a01d0594100d044503d02000805035140000ca0340d01d00c580340c90f0021a0801d5503043c90500342000646800144500c1183c001c907006a0200000344048141809440c0404045101c114549441c4c81034400305030f0801c850000d4441000903640d4021382d881441e140a00300001e164031024444000381c801c64002d142c010048a0900080151040c1444001c500175426900b0390784030600041c03000c2c4101ca42c000c84180915105140b110400030b045030625460031f9002100c10382c0c0703034042825 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 611448435 1250 611447185 611447191
    0x3030a052116080133020109060509031c020703050403031803050307060506210c0f0d05060f0609070201020325110609030415080c0f07050304030507080606041b12051e 74
    0x35001c0070304003082d4907503001103140d4058100701c0340045c542d46400e011100901d66a07054441c90414448000d404a4000c1d808003810a130010014002490014040741c1c3d242d1004000328000e01000d101d1102c201c1d034502c2503d6141d81c6c1a82d40764503080c030315201203602894018000c03900c00847c800c0080007a100708000d1010038401d020200e0f80d450080100328200e800541c090aa190b214120b10350301100c00718a080000c0d10454110310840f402c2008541040720f1210002c0c034034401c110900c11a8200036407071501c1807170121450340280d03840e24000c80c00d038041900c5008030546803404000c0c0b54418520140c84a007243d02e8040c101e6510100403915041080e140e01c41b5036000060188419500c10b95202c580040d24106580c10b0304041c084503c0c41c2c8603001081840d4140868240c080200610488005680003000ca0b0056512400c0d034640325101550f026100303034036014005e021400500040040d121160f01c0360300700c8108243d40d25001e010003d010000ea040003800800360340c200c10704a140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 611449685 1250 611448435 611448451
    0x60203040c12061a0d030f12060503120c012d050703021c15080d1403061c0501020414040903050304060c020c030d0206010911130b0d18060e0d050903030a0521 70
    0x107821a42d80c80300c04d03400e062036843c1e9008544501541c800b107034001d80d00c4c1800000610b00031482184c0440418024441c43e0040c42e8140030303841d41110b441c1041409081d24001c900300030400d41c090034074000010704000c0c030000c540710a00070261600680c07a510590388034400d03041c05443c00d10307601d140c017103143c142c1740000c0b203103a0340c0364100580c100305868270801904030140107018181c800d01016050a086030046200c1300381c0000041d110340c80d050b1484807028880e000c0ea41040c404c0b80303841d5004c1e400601402c948050840c00c80b904a01e418014005510380548960f4515142c503182c1d040034004a0b40210250321840400300a5500d0411030341c00003940c503501801c095410001d103081901d810545051b900101805070180440c0340340461030031544d070450760b195164951000d9802810001c5400812101102c00d13000901c00d00f504060391000550080c0c1e50b80050b541d009032030314011007541d03c0d010750091000001d9a4011801031131044050401d14014030850101e4034030340741003264494 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 611450935 1250 611449685 611449691
    0x319051b03040b09070501030203070c060914070806011a07020a03020415030803131728020709051005190e010603090510020313020909010513062703020f0f010513060203040c1206 79
    0x941c00344d050042d400640401d01c0d0941c40c40c2800900145a00d0810708060021940c4520400410424070b40081001002c3c106541c24aca80c0ca0402c90b444240034403440036602c4901c070204100036894021200021340c010a0011000d0658080c44010040f1040801c81c0e03140c1100301001052400c8003851040400004c85000c10f03019151100d441d07144296550500c02d0203010b1f60011942480c6103010b882d40c3c1945125814441090491910b80c0c241d00c840d001c285070106100c070000346c2340524070603038005a0780e4240c080b5400c13111a580311218810b000b00300102900502c807141c0700ea04004400c901410803280c5405030390362200101d910994403184001d110344002403c50419941440e8001d07107003c000c101900c0c10005030070011454180040c0940e60303c82e4110819500e502c10800500d078200c02c0c1190442803441c01030750340c02c566200b902c442c0c4140540d00d0061a41406030b10704c00c07440e5481d00c14200c4070790755502000c0d40000d4011281c91034000008601c035002e01d40300d81031071030040d4408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 611452185 1250 611450935 611450941
    0x30102270f0a03050601050f01050f040807170a03020c010509040b060d0621030e0402030403030e06092104060203092106070302190f0e0f0a05062d0319051b03040b 72
    0x70828018481040d4051810380d0800c201240c00421080e044541c01c0c1d40e211000f01d0303000b004a0320b074494540d240300814000700740400c100c0c00c00200340095038541e00300514100c01d000e0a15684002c502c400500607400b0010849032544140e016040a00000c1d1000c241540c81c10002a56034204041280845503903500400040ea000b1022402000410a080d403000001e030710010440030b801c40c0000e008030740020115080510030f601540b500d920100a0341c401d4105249501c1d100c0d0310340b8041c1d000c0244081d041c4400750f01e901044400b26692038004626010303039041845140c0c2e501d01c01041d1840030781007004188403414080544103490aa40060b5200544000700013105c14402c104000c00003907610502c40c00d41c1000241829000841d40c00c50840a5800010559500e030b130002078108a010501d032002c2d505140c0048076a080d64210341c004c0c0350314010802154002216605080000b14158000c80e6129900c4181c0100f0040000c866000e4030a0700704d00203500a6500f02c401c40c1c50b41c010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 611453435 1250 611452185 611452189
    0xa151205060a1b0f08070c060207080309151003020d0203030417070611061303110109020a121e02100c060b0d03050406020c190902090315100302180f0a050603010227 73
    0x80390520306040c2c080c003215103143c140003081840604100350038130100c080071503001402840140401c80d0b102600f03550b903910a00d400c40c1c0d0b03500150b030814070034440d030702e103111150042c0c01640d4403600c070300d00100b14a940380d9020401c1069001200340d030180801c02010491081005105280c596000f00800c0c3c01c81c40c0c01c800400e04400b5100310b03e04ca40001050010310181959034032899074240c68070611a08840c100c10380104441e520096004803642300c0011a07076800e000c1290614007525441520741404125401c00188054000307501121103400600c045015140c1003a00c5800b810300003645017510300100701c3c2c0480700c3c03405070003155000c1010800503904029810500700c082d0b420600000b010115988014a940900d80e1035035004220072281d45c0301000115a900405586a46641405100b0a40601960009034040e0400c416150064a84000001d001e8080d604494172280e484030f078010020305020300126450f54080050700548594004694070f030341e507a2012500d4080303100007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 611454685 1250 611453435 611453441
    0x1606020d0e0f101a090411030109150b040506031e070e0c0702090a0c090312171009050f0708060d02012f0d26040501090c0306020d0c0509090a151205060a 68
    0x50f40f000100d050074491484401043c00450303400500303441202060302d4900c2c0c0402860042040e0a80561a01c0d00c98018030441d80c840744002c9071140810002c0700c02c924244000c2d40c00482c0c09540590020440342e103d0b2288904d0300541d50000e1094605040c4c403215008101c071010b50f07030340303620000100383c5000394a0040300d07a641001c4400010403a2003e46100907084030310310f202c00740161065002245070f881c05204c000240c003a26a56151309031030040e412030080403071401040b5901b440c00d400540b2016000303002500409083c1c64915059503100c0c100800d001c1c0350203080741003100c2d884642108802d0940e58105264031488884200f84840c001a0b1401c0d50510107a0204241e0148160b5091042c00a603d296980352401031000d65031414628094011039000601b00347d0094000010710103141d01410458400c050706100ba2888c2c48070490b1280a491011580480000c01190700c19620f603002c1e940801030507860610a03640d5181c0301e07a1480c043c2400b55480c0d08404100950058544 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 611455935 1250 611454685 611454703
    0x501050a0902011706031606021b10080a050604090c030f300804081b032d040e0a0902151e0f03010b13080a111c081606020d0e0f 57
    0x204007501803a00001c0c004a228550780c8582080341000c24240d403400e00804d5421440a981401060740c0c90f00025580c429465100c49070a8141034884ca0b64078081e844509008002da45001740303a220704450000416001c0c0c85654000da0703c803000800900c1002d8190015400b800d06420401c480781060f03084c0da0404540004404164003001208050702120500e90300c500d45444181a075461400715840c1c412610f800c1e40d0090050700401641400200818226101c62013400f80290580d958105031411200ca50800f020107202c14010680d220700c0c40c80d80420420404074141d00d450300442d5000045421400307400000043c16185803070324041814016420b00c041a203000b15114035034600d400b040c010301c64000c200007251103041d41c00e003030041d000d09500016168040484e03e441040184140040c40c0145040200101d12100b1600440812900b0114661420b61000c001c01405820321004a41c41c50f820300c0040506071144c441c00841c4440c00b4010401440c1498605150104c20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 611457185 1250 611455935 611455951
    0xc19120f060f0e09120a050d02041716060203090a090c03090c0603020910020705060d05180d02100506060715050601050706140406051311040908071202150601020f190f02031009050105 81
    0xd40d070170724000550303001c03200200001d01d08241c450503143d07040d1000c0d01c107550207802c44d410900c40210813418045403240101142e252140c049542e90381050b40c4a0152031125a4440301a20081042c80100d82029000c2c040903e4003744004250380c2c0d0b2a0040744641101d07000a40c00700f12144141450350481e00c10000c24001030240c81d180000240300c51080b21010203a640c0c559000c00c2d071a140c1e03030440105c01c041460983d1203e0030340020081d40c4101a1400e0a61a0700340700c00f08085040041c11201e4041d04010920f404120082c868806010f0160005040000400210001c03404621480b410211140c41c00e04060901d81888010b6807000790045105016544240c4c0000b42c03441e0144040c2041600e0101d1311003800d083c107800c140030b1080054016000400c0c10001168082281b07400341000d4000f580e90794503101c3c01240d0701d80c411120b1150070b61225044081c001c80041c0e4000b440c07440380b036510404080315070120703091454610a0745095a02c80030068108082801641c0d880800c0e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 611458435 1250 611457185 611457193
    0x6010912021c0816030e0102010b0d020907030c0e1c06060501080f0a0f020d110d0509030408031e040801110a020606010c02180601110105130203060c19120f060f0e09 73
    0x241e00081c040c01d4590301c0c040c4008403800c81c00410424108207031044480d207054242801030781420050104000700c01001d00651900380702102615020280005c000d8019001c60300a50b2002c40c01d034020880e560198080c462084810703560b650b41c050411242c004524400c62050300d85262074426240c2c180c110754180406001081560742d242140c0d01c2d03000f64606000f2441c100f280e00510000c1c031440c51090b170540c0c24201c4543e520341c062401001c030040000c504100564480080c1506e81c00707680188074064004014404070019100c43c4804d0603800d03602c0e4946010b544e019018211401c48241070055080415211130781501032201035070100080c00c10404201e102d50014140d40d0003903548074144140000400d042ea44a01d0110f500300e02105c00030895030038800d4040d00400c0c0c1f003103002c9210384102800100c001050505440800d1100140c1e0196070000003c2070707800034084900d640c0c0d82d40d61000c4545001d00c8078000d410041c0303510803c0d600c02ca800c200342c501c00350034014400c44560380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 611459685 1250 611458435 611458469
    0x90105090604120509040903051809010501050f0c0115090504050d02010c021f1424150714030c160e011e2709110126070c030c1208060109 61
    0x54003080c41580141d021003d182c0b000d00340b0318259032074014051995041880d0100c180d0130140c02c08024440f1306114844a407a6106440404c04506400d004030750015001340451803412003210b0140c41f41c0c1c0e10100010900c204000d440300e00303924072a030010b81c160f5105d06c14001400010700040801c030041b032000f0300000251802c081d59034074000300c60b10b8510a03014a4601c5100f0305030701c0104088002c80c2016100e04001016a408a240380d0031802000e1003005089030a1805441c0b2110031403441e20014103081c2c0701c2e01c0d200341c0d03130712a00e200c400540810041e039405c045003480f03040c0c0013417128803890314210308058000f00d00c900160010003041a1080d29400c4240b00c8040810458803600300500c1c151010070b1603600c0e0a01015403603c9480c0c02c0070790080800c80707100c1c04001040c03000c0c2d030340c4d081c9940ea07800b00816440d03010504c0c4103200d0060002c1800140302c3c0c028246003070300034100000301020707607540c3c4810305004190740400600f0b4802840b00c150b0b445903450009028024110349000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 611460935 1250 611459685 611459701
    0x609020906011b02101418120c0904080c010204080a050d0314040f060e100c0503040b0a1808090103110a1e110d08180303070503100b0a0903020402030604091b060305090105 76
    0x600340802a10511101202c41d40d410712602c1500100c221250782d40c0d032240b420940d80696808210138852040c002443c1020079008c001420601140c0b00034060b07411915142c860303010b02e9102181080840d5007c00c000306d0098020400030030882c0c0b141d0010000c40c5d4912000030105c80a10821030a80e2031401c00f4031012400c41050411602e070000c0c0d002a03002110300b40c0d40d18049880443d2005c0301e05041008400d00c1d04500503500c528003c1640302c603142ea40a00500442d07400c96090800ca50050705000045031a010244c010080107050004000000800d40c04880d0070501d2001c1c005080ca0385403046810000031404052003036401c184d1800e0403070320707a0142c6958440071003200708a0a100020004c0441c071000000c0d03c0046420303203690b810303c29002400d652086401e035041c1100c44800044000041d0102c800801c0155140380e48581560700700800f96102401c0d030b680c45a01d07070504002041d030002e141800c2c051488114550245811000b40c1910701c010072910b666450003042041107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 611462185 1250 611460935 611460977
    0x91f05280c1101210213050f01140d06050d080406120e0613110402190908030909070305040809030114061002060105300105091e010e1f0204050d060902090601 70
    0x19071003515000200c0c0b00000403103000681e00e9454802c02c03c0c40030154002c81003903004192403000d5402042e040c54554080c44184401860700741d0024000301c03442c0c0125054000905103003d0040400b0524aa881000070f24550b030100c0c06827403142c0000350811115403c045c001c8448c1901da803050041c40c00c000c04407522044000c1103c0101446099501c04001c00502181a4507000800454540143d43c551400300c0504003201c00c042036281c07001207040b82c40001502c1072b40b08010068480c40e980c00104401628002c1c0c4119200401444082c1d11550b0a000b48501d4124510007040d1620b04042004000b4180160304002c1d504840010301188d00d0310500501c4015080740b065149140c10300c5d500d642c2c01c0100f580b212443d4a1f110911441003c003084059140d018240d6074903101c10310a800500b00d0341c603d20382c500b02c1d0f4401804802e04440b05c03000b0085c100a01d420040c00c166561011555032507d02508507a181d9992030709208500e4080201500b100080c82d00c100d41d010110008084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 611463435 1250 611462185 611462207
    0x40309060801080a240902040e03031803043f050d180807090e0321070e040608061f17060f01080a0309030611090406030b040501050106030c14091f0528 67
    0x210491101500ca0840f4140c1c000451b07803940a803007045848240d0311142e03203a400c191001101081051070b044101c0704000300ba14260b48003007422410032030881042c2d41c02c0c3d0360007080140c410300040c4e600c848401d40d00149086c0da180500090700321500329020082802c000560036080b00d02c001c01c7c00340104800000c040054807445080064002031070724855146001d121003902c06489a03603240d2001a415480503405140c89464601c0c85620202c10803066403200d010711000c5501c05c100180184646140301400380223141101030002d0b03140d5280000b20441080794992543c403140502240d5640c6007415401000c00c000607201207252590024941c4800b403001400260302e074540706501003480000c42c0d03600500140b00700b020503900c1c5404030100608035020750303455182c1800010801d02030b005070030041016641c0d1100c0000100c145200c66000b0810458200742144001022146080d001e08250300c1161a0136454845504a2081001481d413000c0c6116181c0c030b80d82c40d86180c0007000140d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 611464685 1250 611463435 611463473
    0x606030218010c052508100b0d02091b0301060203040e10060f051e0415110a050d110f01050703060305120403050c040e1f2403050c10050c0303040309060801080a 71
    0x38083e26103051440c601266040700600e1a1020010012043d1504248071700312041ca4094524414403076282100f240c1801c504103030031111003a0b611005240a038860340d484801c140700140c83c0e10403c1e811201540098201c0320260344001070901c03401403160030450b07000300e0208481a41030b0400000a00070085045100240240464480820701180303040080c001c0601c101591640d960b1080c0b0905c0040c004111008181d10b4091141100800304040c60507079000340080240500090703049410451035138590125000320790207610f4640d000c4c00b500340180c0099034080b40d21170640c10301c28200340c0c401f9850646840c0070041000041c1010444101c206402c4a00041c9400b401c0906801c0c190001d0801d0ba00f524070a07040c0b00040219440320f407280082c2c142681c0c2507007090f403000308110618000600307141d0084512821500c7c03e5100c207c40f0004915000e4100184165850314503002600c084003c83c00000062101a40c025070b80382c01446202c00030250131065486400094a544c0c1a4503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 611465935 1250 611464685 611464697
    0xc031e1b13170606010306060509030606012f0f1c021005070306080a0f150917030a0204120b070f03020a05070f0804080307080d0e010204150c051204090f060603021801 74
    0x11160003081d00c0031400810321200c2d8000d00d00d080c040300c951600c2040711941d000c20301e0700c500450b03400d11420a4a90000010303005000c240c07039000040d140025900205404001c8204800c100c000310a16012540c11307905008011003240041014204510020480e04007803503960807000050340000c140724070300001440002c16444450045010706025044140b10b44a0f40211100700080003c8108903203028610900d02c840350104850191960240d020703101c9802c3d08000c103d0002028001c3d038011016150040c40c169544c032200e0041d80c2c2c0c0500580d00c3e10416009c0090300d50f00041e49080310f07100c80c40d0852a001005030054a24092003a010301015035440c01c090420a01404807005820401c0861340c030b5060618042d0301c01e130b1206242044a0307043c6543d40902000500030389061340d041e81401c140360708020000311603441005030240c0b40382c491841c500310740f00b0b40c0400402c05005d001d8400300d03000e42c0d8403000b002a92210b074031080405204016070180c2c1d030480102c0400301603091a01c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 611467185 1250 611465935 611465947
    0x613090f06020a0e03060a020a0c03140d151d040c0308030702100f0e1005010e0c0c0c0604090e0105060109050a0b0c030c01020f0403020a120c090b13050c031e1b 71
    0x203032042840c44200a204500c002032225038150031000d1440f040c1812012284665600380c03e04050740250000b00d4086603903603003440d000a00500c000c1e1030360241d06040d24100100500715900b40d44c451040b18000900d40b030018804452010201b8169000760104c9480500b031030ba0301e50303582020703910000c0d0100c0008800700340250b109200295680c402c00c00d083c4401108145000003c281400e2514081d00c074844060304030f480c0034082c142c101c80404060711420741d03a402d0501e000d9030010806002c0c50103070b0048540195a56000340c405803801ca80006121800c21071110b0840310060605410b00c00224401c0089540e41d81040c8155079200d05013540754440000741520354001c40c0c0d1680e8a030b5001107850b0354004109406401101d0084070f10125555903040120540c0508000c0030740081d19840d820b00c60703081d040c2c20000c0421005050306001d80d80c1a03668404460080c0c41900300ba4400000344510030411498803203041040314500741860900c02004055a0030a440f031400392140401c403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 611468435 1250 611467185 611467193
    0x80334050d0209130c1b050303070e031c0909060504050f0c090303270a3206070b04031d03150406090c0b0a05030703050708041214040b130503010c08061309 69
    0x1582d0901e040039107041d44031198500104d0142c40081a0580041c00310107161400b102014007500b20660058050340c550384502c3c00480300d6008183e00a0340510600c9180076084500c0c0d030024180003603594907000d00d20b0401a03554284d92681e0710051041d03080c402070003444a4282c120326000020803100f1542d1341c5204010034154040d075035034025400340f1082c03ca41c01401000c400b4449500481c1d19103450794440f00c6503407400b0070f0280c8405060440e0303040f101d450f12103007003081542e00d0020607040c1440720036079550710390440c01c07603007100026183c40e01c0000c658269403a1900032581100981400d50100e180740070745003270040c0042c2446450300c5403d0148064801100003402d00c5142d101c0d513a000d50200948240e1094541ca80040c1c0f03008005044944281111401994400c042b48071514050004584650140c1c1405040650400000404081d218024180c185e01403511100c0980b400c0304050840d10f20b0040c04051250354810410141c0d2504501e001c204159100040c46040e5428 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 611469685 1250 611468435 611468437
    0x41d0112030e040504020a120605042a060e21010b120118030815061209070501030902061615063002061b0a020d0309050f0d03020d05160807080334050d02 68
    0x842580b0030079230119000b040c8400354211a1282d401202180300580c000071a0b0100302c00c526042e660b40b000b1a4206201c1a4420b00002208500040440984000540004c2b103100003914402d25160764500803d0031a00f0041218590034003800003c01540030040b402000c0038002400c01401c0003c400c00203079200c1071101a4910800c0058134454451802c1c0c402c1c0140584140d032040554829400002800c0d0722078010540000e6000e0070b918148194155a442c58408550085886040e07081100c4039921091040c0802444000c5404002e52640b400084111813030300381103480d428804c0c4030940940c68510884911404503004588200310b008d04450402c0e0b08100020741c40440c0300340344814117a10245501c15101d045443e42d071060450010810424603808009015800120001071554016000340074138160701d00040241a4131940c07941041e6002d2030040b2074680021051014003542d81070010781c0d80070904241c44643d10004060034000be0800043c008101c000243d801074644290 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 611470935 1250 611469685 611469689
    0x80c0d05070906062f1009020d061418070f14030a06110d0b01030c020a03030b19080a050115080a08210a061809020117100b041d0112030e040504020a 66
    0x18408016031a100d544c020480d100c00110300c0a2220008441007001110005a0411403c0b0000500020411021000152a49880c2660311260300078030580410543c0c000c00b140340c003504040b000340c5c0c90304103c1c980c04000308112950103a4004174040c02020a112829420b40d8103041090a21072003980000b1b140c0800900020021410710420341c00d001c4044000c1c00720021803103014010308100f40d004508407106103105030010391010b904400420302a81c4003003500407002c0c0003881d042c01180a03a00290159078403040040e4840c002c0102402001c0c030038002000306114140d07407800d14103c1c8035070383c41c0503c102c007a0034240009010041d200c12007948800b2941401d074016014585182417000809043c410213150842c01c02542d06040d0b6584280c841841d07058540b10006c030601c20580031580c200602c41c04200c490340c8004502c00e90508058030052000032407444148541c03140c8100e0001042e84400300010b100c0c5030000c0007a401c521818a480c1c015a000940356807140000380308000c0ca6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 611472185 1250 611470935 611470949
    0x20a030c082b090303140c0711030f0706120b0111100510171c05090a0e04050a02040e03040306140f0103080306011e0e041a030316050c18070f0801080c0d0507 70
    0x1001e1841c0e0840841c2d00f2525030140680c0b000c21810245110a69103003400300d805480c003c00c10040c2e800060b654a200d207680490140c1101c1c04154003001061905141c4c0d04083c001c130302444040a403007401e070300440601072028600103502da40b0654010b681c582984040a00c034645030000030364901c0703001c46100020810140044100d01c01000340e140c682601110120502d038200c4060007110b0701683c01c42c1d100001c080c0c60031700e20702c0c50b01955442064010b40110345500030078a502d40540d896014860600e103d50740910760702c07451480c052040742c2c41004901010081801000ba0144070901184c0c116a0803006259507503560000407200204201c14810b0b13481060740c0100c4403141c0c03054001445610a40342001010354800e180c03003440c0400c00009a069200700031500c0e20940880b01440181d00c03c1003101d40640e03001c00001c3c80c0f141078a070707102e5244180c84108414030742d200d00300200c00102400d00341c40742d5060000c0307242c480c10204400c80c026081100d2950812000304030800c020626 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 611473435 1250 611472185 611472247
    0x11121c0507260d020703050409020315031014131b0902131406090d0f1a100506030727120b06030d020304270605120703030f020a030c08 60
    0x10060250154001c1c6005841009a1144507141100c000c40240b110821042081c0d041c441103044000c06580b08a10483c01c11038140000100c060a0b4000b131801000f8501c2e14403904031407001418074102c442618107a4417030424101300e01c0d0482c000e501d030ba00480d00c10103c80c0c0f80100750400d5042e072428101401001d235282d90340040c07600b0071940034200c000a1501d01442e40f0751f8600b01d440703426070491080395102400300100180d81c83e2050484141074450401e4101c146810780310103040c1031070383c8400384d050380d650000c0002400820001401918003214010304509065000800c03522500301c19004010743c10b40c140480c55015242000182916480150381703080f54a042d40e08103205076452402881a524011a030318000b10a403015503140c450400c4c0e150000140040003000c01b16100101241d983e040403840d522070340182c81c01d0382c40c0c010041540500d5850010444403c1d1100c001c219088012000002580304001440040d048010241c0b80c2404c40b1801e00403d0ba0300c0030304050150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 611474685 1250 611473435 611473483
    0x4031218050d081017070b03070e0a06110114190c1b0302030d061d151c03030b01080f0c0d05190617060c0715050907050405090c09010807031112 64
    0x10b4403c0c500307071154104480e200e283e1039480e4000b0700102844204640c86800120042c05031030381c2d00300915840703900c0d0302d0304241002c42440803a040c440b05800190009100c0b00301c43d56241c00034001c040703043d80c001d210b0504034a01003003003a200340f80c1c0c0c80040c45800d0302d0707100b0074408038854081154140141001050413849034034010b50b4991043d03400a22690400d2000580f9000c44641d07000130104108900319650307204481d92100303008410300c09501c15171a060003400e400920f000c070150b5500c00e403000152001404005048004000c02d10b21284940c0803c011280c82103c00f5607032203010090012503151244440641412044090041c03020314041000500a580710f4a50700040302c4401625483e440f0901e40090301d00c180d0310040c19000d09101e19040b0700c501c44c0d020350342c801c520405642c44076460304002025620280c7c0c050076598026084d0070300c145410780105006080f07040051125518503520700001401020000c1d100d0a0f5542010034000c0d02442610b406040f181092104030b2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 611475935 1250 611474685 611474687
    0xe031204030203060a05040503070b0703060b03042307050f130f02030f01061d06030417120903131d0c090a09291009030b070311040e06010f0804031218050d 69
    0xd0440d1100781c0c40b074410715010a1141c2d42034491b55001e150444055441d02500b80c44400c220310014212000301581c403440010003020328805103003c2c1d8841c200140400c0e0a03003800d081086065803a02d107050700444401c20580d500ca07400800300e20800e80307528100380c084001310340040282568160382c1a000004001038206101552410b0350010f0300d038488170403403601c0324001032600c032200b0300e0300581c0030004540031500a040c1c0d04800840c07111038501d40a42c4101102d40d005080e1138840380c5500104a12508001641c4220060b080c46154828001d4549031001258540276021010450300000d5540050b01d40c402e28401800b0303d81024440d80d00000c075a4595014220341c4000c0c1c50341e0341200d10085290250389041da5400f80d549000f011425902c880c41040c001030010b6092550b90707010000480ca00102400050480801c079484914241002410000340030901e2001c00ca400010080040d40152920110347c044a800181b109103031060034140d0f081d0000042d08032710030950544511 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 611477185 1250 611475935 611475937
    0x609020c030403051207030503011a070501020a09030b360a0c0803041d06090a1a0a0f1a041d0a06030206030901091109060102030d050606070f14010e03040e0c0a0e0312 74
    0xb00d105400301c03000403c505884a41340c1c05511b07001400504c0410040000720504452404560614907019241030308030383c0e500c0d00b240d10210468002ca04142020414061100d0b581076001581680c0310000c0f14100c9481b20700424030312100034100c0c18080e4260038010080090900300d0768881111300040341c0302c140c503c2d504e40240c481c14000000b0b01c0340800e070510354019410f0180b000030b08040141d44038011030f00c0141003a00800e074201811f05c0029000344c3d03503041002e00149080f00c07200501c01d091034481c0380040705000283d5104802080100b100c110460000c0c040300c0100f40f120f554586589038104081c0050f903102039403103030f0b02000b4040404e17010350000305114800c1c94104202c0c031240c8103000318404101c3d059800760b001488040c40ca05600e070003a95109500808a03071515909540b20310410b1400001915500c00c8400041d001b150248244006d1540107001036080502d0090b00e108010300c002d04204402d0404600082820b0240d8440d035540f0340000d0960307500340200c4514600c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 611478435 1250 611477185 611477189
    0x10608070f08010506030d05040339050109090207051c110a0b011401020d080712020909090309010210051003230708160515030705160b0405010b1206070c060f0609020c0304 76
    0x35413801000c01c1e074034500000c9000213000181ca50f13500302442e40e01c07210180e048114a85580c132200d501d070010302500307080d14904c44c17010700280c80c4070303031820140014803aa0894024084041c0304210035004110001684507a500510181510140c8401302c11500d401030209502c0c080d2045005010800000341c1015050701c000300e014100e4189103400499071040c1000e82d910200306560081000790f44a501421a8020400da01514048403007000c0f4000a0046030b0000f00c641010940a166607814005000c1d255603c1a0610203801c244400100c10100c503c002030034455501c0d8900c00c010100c010350004c0700c007130a0995030f00580d6071008540701c828001000100c140303a40b07000f003260301d00010303a1000d04880c02111419379440b100241d600340c0c1b005490369076410140701d000d000a201c01d14800d1150344120008519600090148240110516042062900034004104820303910032100380303900b900642d011455012107121000180791700d811904041d800029030b4a84c4420002c02042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 611479685 1250 611478435 611478449
    0x110303040b0a0b030a170a0908030f070c0501140f03041106030906070e04021201170a02191a0403051f0e0a030903020a060e09010b070204110a12050a0204050d03050c010608070f 78
    0x603242141090b41750702010000030922040c9a00c14442d10203200d0103080c4482484c103004440a840341c220a00e503800c0500c0d061428000010340004005020300140b000703100070b08240c401c81a20806841050141e00b6040f803030140080002400c0c0700424005030802030f4040c04903541c1c0c0c1040300340d0b2038551208442440214034601002e1001d030a00b4400c0381d18504103092103410076400e080d0070740b180b12036007400072a10b44948590800980ea548200d20302841a280150b14060b02d0030201ca00c59880a03071030304150031401c2c802040032030b00120300c070450f41ba07411040c0e41003c0e21194404004121041412450748501007405080640040b000000c1d2030013150303070100c1142c0c0c61108035030801c10302c000c032174010041030700401050f40c0d544090041070744010004146021a03030107904894104a222100141840310200c0940c0c0240c072039a40c02007110f036000c0d4580b60070500807940100300b411001701080300004030f07100d04035004e5000b10040c101d18410350340b14981c0d41442622500660248103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 611480935 1250 611479685 611479691
    0x30112060e151614030907120f020405010e100501020703080a030c1124090604020307170a150912080603060705091c030302032d01050618040c0513050306010315020a110303040b0a 79
    0x4050b5603104040e244071b054802e00a050040c24210b6051068074208012602c030882c0e0000e080041e81c5901807030340a895900a512403a00d403060840b402c188881d4800303410354100c88000d0000c00c02c10005c030389950006082c0411941007151048403000195080880a8090030303042100900121a0100240c14074403605401600e130b41c04096107615050390001d5140c0d019040c1044040c44030b120b603400300000101521981c02841d100c0309001e0314402c52410b2003640c1d0791040010040307400c1600081450516280105152540120f565940040c0c80b030002c0c000080740b01c40560351098240942010740c2008100c80c001146806400380d00180d0704102109d014540c01044104003c80150280c44e0260345079407164a00424400e20f58810314a00c881d0f0741402c410074005840344c1c0110b030302454655030741640da403001d0b001495217841c06e0341001c1d1081d04843c00402c0403496101c901340c04134800400060b9101d62414058400350620368400100e400080100800d20400d0b2600c0c91140001c240c0078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 611482185 1250 611480935 611480957
    0x106060e030c040e0d0c14070f0e1303090504110906040b0301170d090b07060e0f06061018092d0203060a050619201002041802030112060e1516 63
    0x1043e95040c0c858078013164480c44513680c501c0d200c1c14208500c10300030002001e032403a076021080e00340703070968124001c40d206034403040110075011040c5a910000d184000b40e0036a1482d94020302c00c403d640308052145844080c4000003001031421148004401081c95580303907990030300248242c05c02d01c540d0040303007081d03c69011803580100714402c0f0325403e40d075100c60b084e0414544182c5070b00700940c2aa00d8035550310502605000070002c02000c4012100148524a00a020411403100f1a0300a03000c0200704d1810b02d26003419400d081080e50050b1344042081d1074040c0310b018000165103480e410507201c2c4600b13440c01850302e0f401035004a9056842100840c3c42d101444420f1240d05207d0454451400007000c08502c54482c40c01800f0560046410343c00341c07000c06130b140102c007004036454a540058200302050f6651400321401c5c0c000c41040d4110361410444011f80110390002518254480d02e051030140d4046c00141c40022400c442100c41f4145039003110145145428480081118000c0d0303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 611483435 1250 611482185 611482189
    0x30305151c060921030b1002010b030c060d2a03060e15040b03100509100e010c082403031b010c0e130b1c030f08130203060106050306030f0106060e030c 67
    0x9150303003100780c290340d46003060260354a100080c5151041a1030508840c201e003901c001003000740c01440c010613500446c201010b41c08100803501c2d00b04c80c010540e03140203050300454a01068001440b01c04030790a90310b44100d10411400f524582951441d030f00d0b415100301c2c0c40700304a03000f1080d181003582d0301045156142c00d1301c40205030341990015801c10802000e0155854180c21624601002405452940c940040c951301560f805a03102261a04046440d41041200788180d90441c44104c4c028089020a64406070000c103016089111030811104810b801c940c2c1c0004500c0c0000000d000c8940d19940c00f4801c0121038421407403002154200110948800c1c425000c400e01e807070004005060450f04800c005009250f110103a40c2c1101c1514011030030407807018800c080b010300a888008540c44807200041c00c4280040c0048602c1c100e091604d00940c1f40040c3c100e041d208581829580d94460000081c035000044c45601e001b0742c00c045020511030f03401a109501c2040039821146482c80f0401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 611484685 1250 611483435 611483449
    0x41b0303080609040f05060c040911030f0609041b0f15022b02070f090504020306060102070e0f07110f0f10020406020307021005220503280318080a03030515 69
    0x4405400a03511a01185051401181c0c03140c0081c4170311a40480080d881d5501401c0c03000803140709490030303000f06041020010034041c0d200c3c00c1c003a642141d443c51805218024a10402800300c90041980000060400400d00c1d114410002c035403041c1c03d54660345146142d41d6a0300342c0103d0107110b00451000110a0000418408040200c2a110045203064401000780c000c60760303900c02144110329001488081841d2900e0280000d4400402d591416005040c40c00c100980b04a045500011080204544c00e070000c070380200d0f9051a80889071140d0008841c802d5090729902030501480160b2900083c0004845501640d29070644203124901c44941d0102e004a1040102603001045020b00600e0120100c01100784242805402c1c000f48118404130995008419154411000814000c2e85000c003c40321190102c601c50040c0300e0324810352800d543c00601c0c1d004060101c00344414140315075401d400750250400604560a08200b800d000f07002d44030990f030540044000c036100c9019400c09503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 611485935 1250 611484685 611484689
    0x6160314030f0403080415020d060512070501020604060203040809180601020c04110a0503090f0d1d03060705220515040e1312050d0e0106091e050f01050411070812041b 74
    0x341591943e81c43e00c09845540700104211000040e1707045007070807112284060240302982040c000390660400c010302c100c0c9240303805010304030351000900b0001aa800288941c0c401d60110000d41c513602d8500e4000114090ba1000310743c0102c01d000d04201200b0b104502e039214038826402c541601c0440010300084494441c0d80c50381481c410426418a50f02590040d5044100501181c401060101c1490304000190b5200c50000703a044104056030303815001300c28459881280504418100080e000c3e10510411b4651520407400e80d90a0403200c1c29008100f0041c80050706201c1e10101c9821605036543c400c0c0101c134958103080000c03070500090340b13a5420006610000032890304143c6c01c0240c0d9680c01141924480f1507c4080c2c107200c418084c0580001080000c6011492249100d2000c4690301d02030440984c071072400d020031500d00c404040d090f04481080d40c0028801111101d107500318401d001c4040d2001c400081d146200c41481c8012500c21401074200207116000b419042c101d480c1d40d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 611487185 1250 611485935 611485951
    0x1a0303030105010e130c110d0504060804060b0103090c06050310060201050405030d1d03130609060813020907140414040612030f21050a0509101e1a0616031403 70
    0xe000520203940a6000014003010090030400b40c1182d449428080c0e48041e0181d0000038180c03441100035440030018120a40d6241c01c01505050030440d00400750140103202408882d1174130a04201640603038040311031541c100b4001089151a6180940305510640c1c0280200004d99000030300d0b18410300c902030103964020051490034900740321b5000039142c80c0d050903145500d192025100120104010001944405031750b21000d0b103041d9016101d0b80d1582e00c00f030203000d030b8841000105091400540100c6904544025a649800f05d046030006111003422420070000100401d041c0701c44281c40000410440303052241e40c1d1076800314480300742d030403100034003140e26003005c0c180e8139028103109030031700c80d0017158000034680d440c1e50b200a66200390b0703000100d2996a014400580c8042c00490451100c550040c4040166022619404146e51084511959841c04c81d0148031620f6540d0b12500c01c0010318042d25000d11328001440259110004c03008200e07800f00320084200e402059921070190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 611488435 1250 611487185 611487187
    0x6160e030a08040506030c0f040e1504060303080a1e0e10050604020f03010e04060221041709150306060c1e0607090f0320060412051e071a040f090b041a0303 69
    0x713400d061280d04e420181943c0354850f403d104120900720b225014000802070009052030340e09000c0388a10391650400555400380c0e080c041c06101094100c03500c2d40e0444188400011620a400c11094540400ca40748209081c1403002c4d00201810004105842036401c1d4820070054079aa02004101d00c60903a20402c00c02d828001040a1074a60040c6940a40150707400b6140c100c5105100041219441d0000070141c0300c0d80602041c850381200001c800301c0e04200061416000300000380440c115001140080d190001c0003c0c0c0c1c980344d04098a00340217080c0100c0710309a40641d0390781d5595034104103d150a21900380003944851043c03140b8021514450100c98006065480b01c0860b042c84900000200d981406c8400441e01c500b00140014100c06460354040042407508500785500000881500314244401070328403180072171000200c95110f01505c242c000051303101040b500407030340304404686801000150040164126115a40048408004010010098141c510206540540c1641c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 611489685 1250 611488435 611488439
    0x607050a120624050c03030c030a150506090d060b1302120702012705150a061a07051009020a03080f19051c0b011112090405070c0302120f0c06160e030a0804 69
    0x31401e0110841403000d440c18500c5c1c9844a011603186a0080d181e4003074201000040146401c03440c401c034040b198091900b000b0b1649041c000840f14080c548040d441101512200010410150701440196001500c4101138407507100c08400207402214150101c3e01e8884001038609106110303403d450342c88203d040c0a00031b0707805241002101092001c44403172213180034130128200c00a064911401c1102c9020403840d0034220040044200c42c2c842e0b5207261420302a400008501282c4240c0da50203110300082c40401e18000100041c6542c0c1c800361410b0310002d10355510202190061024181062540c0414115a00211880c4c03041c00c104007001c4a0f900082c2d01300c1c1b0881d81001340c800c501403410442c5492064045810420b003603a80030307401c0a00184c40d60081c00c1c40d000e8191301880a0801060024950300c020f0349501c3c03100107041c40e941c070000c3d044180031580010742d0503000e40704080f00c1051518940d1404a00c007544184e502051108103003c06501d00016803250041e40004550b050034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 611490935 1250 611489685 611489729
    0x120f09030304061d03072312090913080c0d020705010912110111030a05030108070b120a091a04290126010204170d030b0607020a030f140607050a1206 66
    0x400b4030345403d021010440456074030108100050b02c80a40208100154401404020701050b601c80d40042901d812002e4070130110300d07080089d6101c4000544082d9106d030350710f241d02c0b01d580415a4005007101c401192000805000090342e1070312030055000c80394082c4e102c02c01503800720050b110b48104042c0c4100c0c01800601700514150315010181800480844110509030031900032041c0340000030b00200040000c5a000c02084005018007400d0354603251002c0e4000320031072030080120342050b84520741002002030050070002543c4001d1007141c41810076185c0b182c100e90b88100c0003001043e80180700007002a0200e101812642001c0c10216101d4800440380c903110301501e8200d000d9582400006010740d45031000f0b2402101210140c00310311030041c0041c04940c0901c46844c0514000d00100005840c1da10b19242640c0d084031008d00704406c5403600d219030499508090442d402040148000160003002074042080ca640742c840035880c00c0c0700d0400072954039100c0d035030040f150402150303d81 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 611492185 1250 611490935 611490941
    0x30726061312200f070b0a051209120d021b010c05040515190806130603050c0d061803020d0e01110d0e0a09022701030b03070506031009050c120f0903030406 69
    0x354089003020303e00c04444841480d0b0070341181248503003a400030341075400d110f841403110b00007414900b4030850510a0f10380004180340650315800d140c0690340e0010900c003640802651210350f068101e111358030178803030701140065000f40381c01c514580e1041009600c1c518040c0240d044400c0d0565420741014a00010010010200e10342d4100f542010450401d00c0040c03c00d0510b03e90340186c0340c58104e404d152040c8000034080202045030541703841d04c00c0c4000340003c40da05540d400c01b100c400080000300d003011401441100c00c111710076525078070302a00305500800c1c55200580c3c45e807109041004440015290700030b0036586408160081503c495a182c003a0200740454070015108204640c0c692440d0400c1364082d03000f0003544440c9821440c40031103140f203940c00441c0207180500105c050907010075079035906405018890140400019088951104048020a2012400e1126082070040d40e41d01b41c0c84484241c02d103400b02c0700000c8440a0800c0742500441070940118516507450301c43c8002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 611493435 1250 611492185 611492213
    0xb0a0b010306090f020a090807031a151c0302070f12020d0503071401062c2403030d27020102031207020c220f060506270307260613 58
    0x6242e6140c00200e2009541c0c402e602d000992040010780e11040101e0181c100000b9030720031011603000f491b081c0000380c4c6091408a040c1001080003c0035210340280403540f902515031160050700b002c20807588040454041000c40780a6001c2d50700603901c030101c0560f2004640a40918485c1c0e05400300d0050030011203600e01c0074041d409482c00c05c82559219503000e0750a5074041416910b841040c404c5140141032441c21203402c02600041251100e00307400401070080c601c0c16100e4503803c04002441803082e1034100010003c091701d50300e040314180c0000814141d01e036225a02c0c0655080d86651240c00360506c07000d50140c0040d0706200c0d490704407031a0128010040340441c090b0102c034038040e4650015044003c4450240c0d0105944001c1c0542c04644030325821866650411404121a84640040f9084a9049031000031a02c0032803e2080c1c86482a91100b41c161244440005c0c0800c0035480e407070410000e0030f11040d200414100d03120b589820544071045040c01c44001c410018010036075042c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 611494685 1250 611493435 611493437
    0x9100b03060a0b1c05010909031d0d050124080a05250f1502010b0405042001051903020a021209060301061b0b0108030d230406020304140601090b09070302070b0a0b01 73
    0xc0c040d89502c07210f001500900c000050242240380840c264440340d01419000d000108001c115042c5a618003c10f440b50140c4280d8084c81402505403a54880d030402c50950703508030340240907203000c00300d6040c00d425401c3c44407120024800c1c404240c0b0784011582d580c0d1103802000410640e0102050300d420085121070002e414850901c4c001140000005040001c3c042c0c44440a4201e495a030040d0070b6030001624240710700d10740020000004c4a81803680d02c0104032124a11601c0700620058425108850500c004084200880c034880b5901d0f400400854440358259400070500d01070181c81c502401c2051980701e10180300502905108100c06400712481c18811020030440d9224403a880c2c0f0207030003650710b41e000080c820403102c1c4035008182401c0e03888001c00c1701d01510041c40600040c8043c000602c070a400002060038400d441910501e202c0b40c4000b81c4003556581d44800006000d014440e40c000c92800001070b0046000348240c40c0b509400c03803543c1c3d0715559200d40040003440e100740014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 611495935 1250 611494685 611494699
    0x8250308090102210310060e0a030b0601030b0901030b0727060c060605040207150b03032703210408100c0c020118120c080717100b010207031e0c0509100b0306 70
    0x1e070b0310034540107020b0000c4c048a02e07160f60b90908807900c08505410703400c40d400381304000d03541c001191180e03007103401125004031010341e0a44400c401280a0508107841c694815178000002c4103010901842502a500c40d4985c0680c00540e600302c04aa1028071030000303e0071a0812042050760f02072604842403500c01c000004406032604000b0301260005001950342610030004c1c029640300d03511508000e0ba900300d0046042108a6155084040710040c9050009000707032880c40090700e0400c10380c408884544414004101e1340c1c2500700c00b5400038401d10580303104010781060100d14921517122134480a40d58070358824404e40041d503c10094960f001ca151310f14400c00601400c0d00c484510515214100c203c07202880e01101c546031a566800504892901203c1202d10b002d0014004040c00381402c804039041c90030200507030410f505076202a003004c80b0100030615410145d1208080c041c85441342070a032030385500c1801000e6108403850424000c1e40030045c094010080095580002c00030144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 611497185 1250 611495935 611495953
    0xc0d08120403050f0706140a02040b0a2007240512040b040201110d051c0231050a03030e01080f1b071407080d021b0f040209040212040c08250308090102 67
    0x84c5039141c0c48100280d846981d50030440e5100425050030682111651500350300303044c1001101260751080122641c144035040101a1521484080030300e41012080161031019544001d05e00ea0355452035031090740744084509000c441ca000f4002d94215090541e041c0c6010b590390b43d602d0080300000b81043e070506c00c0d840607c0460a4040290351034082c555554180c41c8c180038014180384140402544400900500240408500001c0b1164601c041c8a80703448100e45500e0340ca0b8112074280e00480c0c0c0140742903002005168009602c00076402007aa504a0150340d01c1c903070510310041c182e078041e102560900c2c001c07901401003006000103500074a511056200c0c0504814503204442d03202000c42d400c0111035100701c80e01031141d5400f035211841c030411080064000660b0108007420068400c690100e50440340b0f031190350554407a1200d40c0340f00340b81400c09003003210840c9858031a1080c244111401c04500d19046a542050007060000401c04c10b0304550398a42d8541205004a0452256a101d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 611498435 1250 611497185 611497207
    0x41802033607080f060a020723030909011202010c06020a030b0a030c0602060108060f060118050319050d050406020303061c02090406150f060f0f180b09030c0d0812040305 75
    0x2000381100e03422466030035200803450701c40c2014059032094580e5007060568608440340401c1c0c007540a005e65400503a146110301d045c001c1e0b00a02071841131000303448030006000100000040c00b600d07004840812043c0c0e61483c0d586000c9c282550024002218028240006030254014020f00c0d101401c000c90040300e12004180b070640154801c1e9203a10b4103000400555030148402c0d8090f00082010f80210724002c0c0c050410044040c1c801c0f0304002c9080c060751030800c3ca50b4841c4006e010014142e500741d04000036507501040d010081542c40380640d0150742851400364080354110349840e0091400c5070344400c02c110b0001c41003842c048030102480340c9000169a0141c1d00c41c49581f05400009018810038180d49685450740c1000c80540f45c0311005000e5107400c03c001c441d11209a00c1c0655000b400818116800312200002c0c40800c1203401c40455a41c041a000d0844a003058044480e4429010102301c600d03403212102500c0b1039401c02200c0740508103d450300390b0280c001c2c140b1600c0c002507028 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 611499685 1250 611498435 611498491
    0x319030f0e04110d091a04030914130617160f03030c0f020913060605030c01120e010f0f0b03010b04020307091203020a12050301030303050f041709040f0603031e030204180203 77
    0x30201000c15991982442080b4403100c00e90702c01180c0e95a0380000b8541f0b65405000014680070741e031102c0b03a100c0980306c02540c40c021601100211a00f00f8484266101403d15500485403111606409042c05110201030008610821100c01c005510200707465601d054400c4c9401f290140c49480144200c02c000d6220505528003400050034103003c1d5070103904000049410980055101340c01c0200180d021303a0707214860741446008003c0c00101001c0a140442c010801c0b4514060440d040c40d0540c80e52507600d81c881042e0102c00d500901010501000b084100d200c100c6420b40070030250310041c01402a4103071442031992081c0125501043d040d16200d081501094022000039000401402010790500486400c0011442036128030300302556401000c4403000b840800e0540c0109400f801c1c1d503290b420041d40a8220001041280e0306c03810001e1401030170702d60a00d00e0740001d5203c80d80c61842882101d003124203502c2c18131030440700808020040d500140ca1800d4959810341d0715180015085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 611500935 1250 611499685 611499697
    0x20f0c070312090b0304020108160314090616090510140403050304260c101b0219030308090601080a03030f06051e030c0103020f03040b06031501140319030f0e0411 72
    0x7010411011241c034005100340004e400074102d490040c003d103c0141d070000e201c0c0390000400a4120f03040b5291040c2103008040d600642140c1101d10000e10007400b1010070340c54002e03a507440201048600134041590f100015101d02500400d014642500240c803510444440c0b0740c0380955a45003a5403502c480f03247d0b401640000711091424041e4050810729040420b6100c070089010706420000e0a00060000c00d00d51022000c0c09910350303484903100803641d00c0c24003950740101181c0c4501e0400e07040d8a4031807158002280801c2c0b642000c0b4120a80014100d03040700e25010007000c2140040d50110080d05041e50748289943e01c2d0b040100e129034850800704c0300f2890742c034900c0301119414000c0528040500001c1414944100101824443c682040ba5031190308258207000c41c0d01c5080102e4508011001c1c6080204800d00c004103015070768840985810301d0031030850f0071b490f00040000e1400007a440d4010042658084c4440044c0d01441306001e8440b001040058020313a60f81d11480c00e40d01070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 611502185 1250 611500935 611500943
    0x50d0f050a0f0b0312210a0e0c1c031119060e1b1003110f04060e041104050a051207031b0923160e130f0614090103020d060e0a0b010302030d031e020f0c0703 69
    0x81c11091188d0404018440d0001c404841074000703841c030070041c01054610402d000e01000300c1603540f1000719504111190188a00c00358905605c4001d06049005203076038071aa86036030090200c66000b5120440d1a207859010081c201c901002d102c0000790000e000d070f060302400d10142440140112032020001d04000c240944580c01d03101c4014040108a07944030000b4dc14620b014401400682c60354143c0c40f056071030580d030144003424048416440d0030819440285801e481c840c404440101d90700d540030031241c1610b001d100c1103038207042c4c04000049408060307480420b4080000c8901c50341220303480310700f08181844c610350000390340072940412008103100f104517141c403c5001c060507680704120091100c180d06d299206041c10000c2d10030714041c440070340b0501c03000040c042803084d1580202040020cc00c125120405246014100e0603000d1106911900800e903500385020300038050b0300040500c0b03544c2c00c640315100d462884000c3d008030240350b80700d10003805407031420001049544051802 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 611503435 1250 611502185 611502191
    0xf0a110a1e0b0f090303060103020703050d020403081e16060c11120310141f0225030b09300904020d020301170a0b011203050d0f050a0f0b0312210a 65
    0xa4182166082c002405aa261003e80010007645000220070350341c200c1000d19015239601001c6c181118107010b907030008942c1c0c41c40014004100150b0700002c05191070003894240190004020106050094005203911083d1072004400000c0240e400b030900015507050040f40051051801e901c1c01300c0b0112001c000d00b2000090149994001d441840200502e010035003600404034041005800c0c50315140c5912000d4401c2c03104102e00070b10611010700d27880700740300c0340c2803c4403515001400440d12068441c0f8400c180030031949500440c0c55440440003028030102e84658100ca4800481c0c1c800b0a0038001030b06028940031070b0780da40018071112030071520141c1c403541081d088039080790685d080e400c403036030007855903900103219280d40904403100c40c002d142e203000300c5040a490034030481c065041c405140483c0c40707010441651041c0d0050804800c10010701c8400c816681c00c0f640044902641540008000e003152a100c1c001042031218802840a4481c00c003510308106a0b81905d042d400507803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 611504685 1250 611503435 611503493
    0x200304060b040b1203120406141e01050103091e080903030c0c0f090103020102062212030c0e0105030c0403140a0b101403120d05131b09050c0f0a110a 66
    0x580781c05543d00c980030448100c000030070500456a5a48201c200c0595002c507400c0004007444102d5000107192000d080c014081840d01074400030b40040c0c00c1000382505601e11001281c9944284211041a036200034070200702500c00081c603a04004c619001c48000e4402c008101c120f803800d0000d42001032b13074000103282c100c0c8580100708203820746520311401021010300410150f81c0c0091000c0d00000e546840c0342ca01061040100c1c541e90380100d01610084800000c0d205a5515078400940710b6800d0b41c0312020400020011503240c44152400b0a0461042c0028808207102c600c0c1d0310100c44545088900400310b0703541c1e01151090482d07014000540f440020042c005890011010f50354007180a00000710300d080c0481d4907030080d18204460b1a07514400140d1880b180800200d440c0d030061042281030003014042e002c54841800b81c104020300348004a001c031200a820b41d02c2408031490301600b00b00c10280c0865071600034900707400103441008010b20105444044440041401c0032482140c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 611505935 1250 611504685 611504689
    0xe070503011505090f070e0607171b010e1b1009030606081f1116030e030106030503030a0b0a050904020f010c0807030201050f0c16031112040b0901031b02070306200304060b 76
    0x303003008040e0071918004004000c002503000308901060082200c43c55100d2109003400303e0b8500a4443d07030480a240018804c5450f041e1481006403441d100c8003d02c0341141c2c481d41c13b600e40d56185400b8610307071009160015a45042e140c4400c0040da54a40301a489a8039180c941c181c40c0c42c1e60040650350000310341038030700000414681140c1c840c1c4204c2404440e000702940c0405210720703140040714002006104040600c14031f034a038100c0100074024001d050302c2c4d007003403038403580240c8648501900d08210075a640c2482c1d201e002c1180c200a165204594498003030200700d0b010044c40b54100b101c400c21100010701e106019105460190b80002007524003000001c00d00d20b0081c0aa402c1c1150a10050b060b40c4182252240e4980c0d0626201c00c008050b10542403030249503040c4000364800202d0b010a0fa0920b900c090518101e00340d0f410720030500e000c103103000c1301d80b4031700310540058000c00300510124003290840841030204001400d0b414000c00b00c03040f13f0f0380083d40d003264000d4031404100998 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 611507185 1250 611505935 611505949
    0x60f06031c2109201c06020904060509160306050f030303010b09060c0d09030506070e030309040f111b190b0a02160206270a05010f110703020a06020604140706120e070503011505 78
    0x3c0000b900c1002e40c541003010017241400610700000e0a550300001e00c0c44168031f56800c441c00030940a04542518100803003407075040201d140ea260b000074600000041e540c0341444001c050b401b00138028514590820350b101c0400c0d400700d414a03420030340c20842d00002203400c0081540b180c00036070f502480315007180342150405501401c1c0000b0410000c0c400800d5a5000c000c4401116040302c4c00903160f001880010040d001c0200d82c00405403000c500c541c04410307503c0da8141100c0144c0d051700c9a014007034146041300b1040620182c84030705141d0014080b804590f00900e1840e1102d01054081400ca9000130f40c80d03408a45002c8400941c100a92041c5601401d2001e00404c1103c007100d4550500c4002022001c4e984100d2040000e0703440804803000c0d043c80014095500649040403545d115500a5600d800554044480c0140d04c0c107404140c1001046003030540f1044d9494865244a149012025060152441c40a80103880300080c10743d030b0074071442c012000c41008010040740b400e0100504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 611508435 1250 611507185 611507243
    0x1c05120a0621240b030c040c020c0d0302070b030c0405010f09030b0c0a0c08041d0c03070c150f050108070602100915090f14060f06031c2109 62
    0x90641441c0c0148110701103510614281d80c0385009000d02c9000300d00380001c11403000c112500203070881110340d244111007900441021300007039088800c28202041848104c410682d803140058102d0241c5114905c1c0c44c2080800c114083c0c41103928040d280c607850200c0c4d9005890361101e028001404220030758000c0011150000c090902e445c095195032216407032383c01e000703000c900c5414001907004909401030101040054200107410b48603a141e0140e59954400040350000f00e40744080010000c103103603402c0300c0c4201a65920035050b5007843e036454404410900b60070304142c0e00c2c0c11340c81340d103110300d8440d9038021301c505c074001c1140c05c1c82c000c006400c0c08145451640c41c2c80c2040765003c08034031804002c200c0384410200001d0711091500f41007042d1451860000d01e1002520511a40c001e0000b425a000d50038510448a440d103907003080650b0399036500c120985110029200c41138a80c001c001d5550015070044084140c411781d000d00a085400c02c042c201c880000c0844207021882c0b0017546c8401d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 611509685 1250 611508435 611508451
    0x90c08070906080709140105210114150a1209022d01020102040b0f0a03060b0a0503072c090a0b04090c090f0507050304060c020c10081b040501201c0512 67
    0x140078148044005d240030081c0c065202c0e84010a20362882591161f03045901040d040c4908003061985118150403e460a101d416a88001602500e0203072a008039003000c4030707803910b080358a888a0044103a17400c030321783c00448050513511071111015803a5070400c500c0b58600c4042c5100480d040000c0b4481111802c01c261781160b04c1803005100308444081141d0b0342d000105000c503207d0b0080d0b4001c501602d055000344900880100c0c20007807141c0c00402841c003401483e00e9000340c40700050311a440400000d000d9022600130780d51003041908182c498a5000038054801180e1401044013181c1581e2116004880030a240f140c1001040e20522404540482da81c2080c000c5090103c0000c0040c00050030141504e95141e11950826000b00803032184148043d240120181d02c600c8040c1501d90b045407000c58880b1029642400007031440200d03010355405846010914142166070120607021181c4282d081c41010000e00700d0003c80b40481751003100c00e0340c5440e40c03094205445007005102414402c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 611510791 1106 611509685 611509697
    0x207122d060546021308010609140103080702040b0a0f06140304050c01120f05010609180c1d0f04050405030c0f0601050112020703020102120405070515070c120309090c08070906 78
    0x1702c02c480b403420082001ea0b58444001d819500c1d0408140c0c00900c140c4018000a0f80102c080c0c00d2090010f840010b900039030402041580300305811880600c0d05030318080061941c8900c030342401791030b4000928111305190703403016a02d0800c484c1e05030500c41384d100c070312544003580e501c000d401441c0401d00b400556074641c1c000e4800004c038091141036404140d1544002025401103816041c0c02d591891000004a580d4030000c165601002e0f078005207a8000c01000e035124001c20303000e1401180515500c2c4002d003100c41c60310b62801c0b0310710030075000600104161780c0c11510024a20b00719040c0581d6403100c0b480d040b4020710418001980b484901c80a101c24003800003008402e4450507500800c80c411041c92030941da00640800800250a0000038448100107400c1380a42502c40c1c2000003000d92517a0110f03090303405242c54000019a80030810210a07072014a1301c0c010711081c1448 = true := by decide +kernel

theorem cover : BRFrame.Cov 611330935 611510791 := by
  have h0 := BRFrame.cov_init 611330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 611330935 ≤ n) (h2 : n < 611510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
