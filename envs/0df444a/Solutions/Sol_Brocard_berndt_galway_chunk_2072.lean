-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:51.122526+00:00
-- url     : https://prove2.me/submissions/b4b88e28-8cb1-49a4-a8cd-3c3a280e393a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 372482014 ≤ n < 372661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 372483264 1250 372482014 372482027
    0x9080601060f1d04060b0408010c0c120f1202040314060903070c06050307030f1a011209020f15040f06030207030e030c0f0411040308160c0812160311030315010f 71
    0xc4000e65151008840c115008607208070701d640c41d96100015020f003080c15039549001701000340c80b12900c040c3c0c0d42c5150400300b50860301c14502d06410320210103402401301780081000074602100f400d0000050a0500046410344030000000029900c0801c1c08000e200746142d240480a8004040b030b80240c0713480a00594901a002000709400c00000c01404114898030241d50444145d05010075041c0406101009441c0440254100f84008409081311981d000300c403d800b151012404100c40c1001e600070034040c118401800b030141c89108480d8001d1910502110010100c00900002e900d4552200a002e580300761019000500c43e00080400c40c0f07408110001c0900e402000040992001810310010348504101e00920034400d12000011405520051070604855041c0020080840c504004a4540f035000800154480c29000f440038804104403130f403500135102400c95005030303032070304454085a8040c440128040403050080e54800c040c0015010102600c0740794a5007001941280d86 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 372484514 1250 372483264 372483269
    0xd0b01140415031a130905070f050f0f0607020306072d052205040f09020a092705210901030c0f050405040e010908030403080a06060309020907030518061609080601 72
    0x2e030035000104192541c000d0788420140080c2c0c01c3ca0318480903000780040d04002400e44540b2505442d2aa03040411038107004001c0a0a00000020f00460405003c116582401541207006010f918042d0280e43d135044161503a1395402001c9402070320786810010107000d84404143c03245072401c0095070403040c0550040b036500310580e903504c0c1040000d1042c8400001c0c0b644034500d6042608034082050b80b114000c0c120f482c0c41c2d840380842d04003d00d106000515540340e01c10380b145840c0100001050980c201d07211408003081495031201081414614240f545420070010865080000c003c400d110b000054018800243c07020001d01d0110b2109039084a501242e01e400500100018003580c41c1c1a40015043c0241500010f000310065803206001c0d0b100380c40940c00700d80d540007040240c8029001b98409415a46000c1c40150b406a000c9500c102020b0404030034180c0700c10004244d008500d806480c019032a03811241241400074804007050f0036000540002a112100469003c4001941904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 372485764 1250 372484514 372484529
    0x190203130302070e130b060a05040e152a070309080d0c030201180507270e0a0c09090503042709030e010e013212090106092403020603090309060d0b011404 68
    0xb0f40011b5900c0c0211002c00525095100d000a40040b416031507a11036881c039400309a006002d0003455100000910000034146505881c03443c110006041684409151a0220041c041d844284030314099450a203140c00551080c425549034903903450340951300102d405d0203074000f007046500c1048100a489d85402d4081c2865105600c10400300c41c00340e4074810700c45a002e4070304401040e280030107420b980d01038000b42019800003401d4403d02c0400c800c5000145101e5004010101e0195203031038990140e480f03805814000304002c0708183c00c4240009d01c2c28081c1c00000c012800e02403601400c3c01004030005400100413104159540d40945d695128482c41c02d00ca90301100811646454201c4100c000c800e803400090010200716002500707518007441c48403001042e014201079040d41140c48180d02d10355076204000101e034117034450b00038000030341e60141e40c21952950f4207000a841e601c204030145400c12400074280e00d01d42403c2e03100d05030500c0c0985e103024060035249100001801940510340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 372487014 1250 372485764 372485791
    0x170d0f1803170c030408010515120c060a1e081f0503060c03040606080a0302100516051804061a0d0b01050309030d050709030807050105040c06091409190203130302070e 74
    0x2c00c01c50401c41c0c1056514220961600b00704060f4141150490f610400c0d882e9110740030710101c6c0110070107011108209440a0b01d0b080c203240c00c07440d030351401c004a40307015203000078140192a04c600074031a0f400c406c241882c08255180d030001010300b40106c82c0c104248005078040c0c5400300c469140c12003114002401003440352121061402c00da48064800c44960b50755070300c0040e80486c1440708010041c0240c000e02880410b1940b0300c000e80310000c05403040b5122003c0e070b09403281c0e0840d055034140304224a1f414158080c07a8085070040c10035030003560f0200111f091902d031000c1001300428084d07102070030901034440c1d40c00064070b41d40030a0351018100e4000b400761400d0041182c0c8501d900c0390062074030702e0300c6641c4c94688414070380c4064002c3d54941d4680c4200400d00c85600840002000a403a02d20130706440c00303a003125114007002803035104050500200388500100f000720740ea41c611500c1c003155a402c02d1420301340d01500529048000d40903014002424140071401144190380e44032081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 372488264 1250 372487014 372487019
    0x1809070510140319060605070b0a020a0f052a01020403030212070c0512010209040c080402040e0c1003150b0d091502120a020c2a030f06160e0a170d0f18 67
    0xc4203940c00042c6010a0025004019404c01c1c0803401741e0f0008140d039440e890350790001410102c14651000b421010703041d0042026402203540a0000c0c0103190305c9241c030b5a243c001c000300c010a1242c40d130100b070815600600c0d5010682c1410f40c014401c680c480d400700d1721404008040700d10503004144001d42180c038524030401950170030401d80180498090001450000305000003005c688180d5085000070b1401030812086082c2403080c0d80051008000900780c014a0200203100300d03601001002c00c150701c469aa0389031154106c0180081c20052034141e468500000c03865000b442c40d120706039005640301c3c1509100c13412030710840302d1052041215081a030b580d50030120107980001000203151051210846181d460150501d0213400741e0034815048c8a040030070035207407140540c40140680c2043c001d00030000c6140030085120096414440161410b50f40011800e1042e07900100107815010481d130b03e500030108492075420104c3e141c15070303081340b408411074040c40d41c00d290390342c03601c86000103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 372489514 1250 372488264 372488297
    0x103050c011412010f030b01091b05130f030f06051b0306010f11010c03050907060f050711010c120314010f120b0604150f0305010b0411030a0b0f1809070510 69
    0x68100c04900002961400f100b9040c0208030b5002603000548010040c1c8091040084507080c150040440400600c43d581c100803400c0303400004c546980701407002c001500340c8403401c0d00c440140104540742224200b5a92403c00790f202c001e0a1b4008c9074500d1a0000003502d20345003244803102810350341841815583c5200c019525003e56040c40c0052242424003910074150900501000d9029594007241038100103d07181c3c0342c41c0054101c04140010540c010450719482401e4803001038200c214840c0214046005880c011545200541260416a0002c101c180c1540102450b40c9010807203080c00c1c0c0c0c2e1040803048a44a6000b0b24652101404100d000716490213081a08250002c1001500c2a1006401c4840940503130200780c0860790082c042003440000c0c0b0500d410782106035030500141d4584072042c00e1510005204032245d03940c0b03046165080d2a241d40055510001811540761030b200310161480c450021958404c80788139207840412181016a080203205105c0d03111068a003410105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 372490764 1250 372489514 372489527
    0x20d0c1104060e09010c0210020f0a0302090d0b0405031201060e0d08031503060a090203160e06061b01050a06081902150d0f1a0a0b1206040902040902280e0103050c01 73
    0x10350303a0094488030082908040f103d8201d000d10751010000a000f44194406414880c40000708046148148200060035001c90216002100d062500694407c0040001a0440c14000c00035104000314410081000760002c014000d443c0d042e040c1641580c0d0f40e0342c04440720551048215004480300500c030303000443c000090350300b10701c020007051f0780047d000010070f2034107004448040c2c0003600c03041e0b60415410184040ca1044070401c1030700300041c0c00c11180345180711019200c20301801c40024042c800e600341850070019000184004c1c0654244a840340000d01058001e0313500714050130030100c2c02c945464000754940d80c0c0c05021000c0110811040340a00d401c0014400c000944407140444028100d21a1030300c400c020316030016a40006c41d01b44032000c9440d4000250540c000c200300da4250104c400d840798404021900410400d103144003050180000040094000307607440f400f011003d242c00c2d07229070705808051881e4603c1d03030b4422561100103401e10000d0860b820500100350b90354030826 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 372492014 1250 372490764 372490793
    0x40b040306180209040516080102030606030115180f050a060f0f2f030706050f01030c030b04030e210c03150a1a120105060f06040b161b0602060105040c020d0c 70
    0x300d40302d120300583e8000c905a280121422100c17608100040802c88049213500d4010b462244003c5085140c40030100300544810300940c0541d000c0610030b42e0f181c40c40f4401001495500121403281e150b620f0611b80e560b0050340c061680700760720305040031407050300c100102100c1300c0c05540e031460300a039010001d54030580041e4203040040e94816021a081451440e040c000040074002540d0316401428200c0c101c0d04090311560340400301c50010000304024603482c1d02030302d4220244c00783e281c8a514054805905054400d6007004113070b0040c011000c000c0107500c8c0700d5107480090700d8400d8100c5003050744804007034007407882417102113001c141c41224542c0704529040300c0c0c84034000584050000510f1400000a4000c4180e465000300f15083c00c002c40d40c01c8800d01e0a4a0309030529082041d11203540c01040c1c0c40032205601101c104081c04540d00001c201422040c407020b1541d5100d8400030348a6000f4000c43e8080ea0a004034181314520002b001c105920155513200042c2d000341e134801c00801d0000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 372493264 1250 372492014 372492041
    0x1050d05060a05061b4c0c1206080102160803040c0302031f0c0806091503010f0e01020c06150609121f0504120206010b03060d080714030909010b040b040306 69
    0xb40010070140c070303100010709980304c010300c840410448880d8101d181074030400d11306110b0f00d50b050306245400b2141202c000104401180703c0c0e00300545c00c2e603940445a009940b480d00505014058012a0300070700514082c5d03650340828811951030303900300b60a074854240300350144641d500d000b5001c0f460450107180c005208206190743c0039541d400180c40c041d10f10100e21441030005203010346c6a01e079441061264042810303c11034a191031000075100c1c1c0c000070070a5038642140454050595020b5100c1c4182d00c1308280200418681d44169074001d401c00e940700c0065100e5540803a0341c01d4510b0301c120310322540c000c00880c50111050280006d91501c0080e074000c03403083c0d030074200e60384070f02d0214000d80400e060000911441c2c04d05001d2544851400c40350b00359000400148000131101048a52000d01910709c100d01140900d013160880c46220400fa0940300d00a003500600c08002c001011032640495040146980740c03040504903200380d100315100b4031000c0204000203010781e00010b0005408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 372494514 1250 372493264 372493279
    0x501050c07030c03031e0f020606060705010914010204090b121020070f0317040309031b03050703051507210f020403051f0507030204030209010b0d1e0203060a060305040201050d0506 80
    0x1c0381d4400c407a00c0308a07003044000c0b0306200c09801d040c0d01001d1b804144607030f45103440d0030240d00f5201c0203502c42d10060b01c0280a0100000d0110500900b50040000c082d440391413403451544111070103000f500030740a08080c1c5410303d9030340c5540d823500d22200c0e00384042240140070030350700b9801d56070000d140140c150030702004151030010146039408090000d4501401c00680c4003069403038018280c103180704115408520100070300021030342c0800c80d0b50641c0d0784002000c1c56107081c212100d90303080c0720f07034401000da2017800e20100800c100440d400d0010041085c01da0802d0f110044103440b000140301844101c504805910030005202d41c112690402c40c20900528058403030b100e079030800c105138240c680c00f8000c60581441540080c400c49a200c0c12a103821404d15066034000388810806110707400440c000419000c010820a512803a190082d02c10030103003150ba24620940690400c488861041104110014249000b40a42741c401d5a050351414a00460030310000018400a0001904401c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 372495764 1250 372494514 372494519
    0x180112050c0d0c1d0f0414030f070606030209010b07051c091805150406120f060b0d0515060102061018150803090405010902070f0209130c151e0203040501050c07 71
    0x2104400b4071840340c01403a0309029581824942d440d00c000040303091111003038040c1007040f01c0305c0020525410039170059009000800417041c903441d501805201c0140014001840f008100407035114004403032094840307034001d03030740c800d25100d46003d00d0b280508590081c214211451703c6a0090a11b048007a05180540035183d4140fa1140c0380a0340380703055003d40d210b007070104490305a403040520400480d801c1c08018181a081038100480071002011b4000c80c6010804011154001036410103000c9c01c2c8000c080b56a003443c90762401e23040044081991220041507541d48041182445003100c4c002d000342c1d940c134001102c4945503411910345003060303494011076070902030011031100030708105008580b03600380c00d01040f08990044c0d101d440060b10401503d00000c201c6200464040d8046603064034030341d6454090700720b8400b0030703800a008017400040443c404948203c00c580400069542c841103210101c0d0141e444014450800090303403041c80104120742c450707001092070202d08000d41d041c440e07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 372497014 1250 372495764 372495769
    0x70c0b0a0503090c03060903190e04020c031908091c0203090d1104060f031509020a0906030614060d0b0126030c0604030e190620030c010b040b180112050c 68
    0x200036940490000d03200209003c1d412808010140000508801405003414810401030b0b6a2041c00c00c041c40240e00b4200c4500814042d080540076014090815542d038204404210703101d510111003024104e006080403c8405e11620825110b00a01030003000181c0899100401d48000143d00c807003180300400c240307891901c40010704400584160401d00000b00140204800c2d2026508401341d80f125405c0d0420118140441d192009405030400003002106030000c0740c0d0908180d044162900c1c01c0c41800010080c50382d0000051401c5240055070a445120409c082c03032170382c000090a0394007e10018020764000d011311406207040f5101c480e081a81e024405402c6401400290748170383c20003003c1006068001e441500c0800d002c449100500030b4207501c400d4200950301841040141d600b070140000c14a03440700351014100d007003c485d00d8541c1004c034940a403d007002c0c0c07103018500b800c020001c00d0800300310b10307103609050a18403411607003001103c1c8a62042e4007c00d890a1040c0004c880464 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 372498264 1250 372497014 372497017
    0x10b070f082b0b2814030a17030f060108010312080910180203070909051c120905030a11060105030c09040203070504060608010e01060e010f030902030a05100623010212070c0b 77
    0x790b01100780414241c8a44041009200d403690f070460040d00b504440894443c046203400082d00c0211884490101a003000b192a203a00f00c080203002e401410795031315940c8070840155108505130440d2000316901e047c01159014400e20005203110251414090030500807507030315602540c5041140c40203181c2c51038490980d888101007500406092042c3c0007541003c0c02400c020700090602032100100740d40d02d090341ca1007035a42d200c81c841c50700d03500f008070b15114004c00714641060301424003c4802c01c1c00c1040d2a0361004a641c00418009075402c100f0000c0843c0490480e1310090161503000c840c20705004d440300380100120388c14080d174000810603685a03c9120003400859440c81e50720341c100301c1000d040c1c04040c0c00c00802d201d00140070000c1d682c1e010402d03644403031030b500c5c012948074601d10203c2c0c500003404034003c02c03501508141444044850340030004403000440c000c04250050040e80c04284c090010a500581109009504401d03c1500801550344121000f02400351b0707071803184c0907a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 372499514 1250 372498264 372498337
    0xa091a090c30010911150409020a1d01031b031107080a082d060607021201050705190c0f020910080106081b100c02091909060c0305010b070f08 63
    0x4410b0300800c4501c07030104014040c0c00c0e100b29a0700070020145183c5680c03081c4c041e130440b610302c540c0c107601324080e11508990569009100301c080c00d40d00c3d501c40d100083e0120b0400c00c50480c0b15002d0000954140d0700c280201d041900340c0c00c040030442e18449c001100078000c1d909042d8110003040000340300007440c9000600000e203090780c84c2a03460502107584400d0303da1004840f01e618044c1d160341d0302c24000f100b0007103130440030071a03886a5814981c800b24440342e250020140055181c0307400c00c507050b40c0190051a04003404207c24215248c00c440903500c8542211001c0d0011941c0c0c8030000060030026040703500b0100403402c201c0034035a1402501d0075205240c001401d59080003e851207401c8484152800c1c0381d804a40110310584034402c02020f200c4a424040c0c403031628040401d0340d0101e400100f162100e50b061003880f445445040090180c204a41b41c2e40c00a4546000091056650380c16101c4c0c099001c80c19614600d42d0340c030760703c0c0d1a03081494048840214030300d103200c0c003a02020b003a180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 372500764 1250 372499514 372499549
    0x2060708090103110403170306011b0b040c06111209060412060b01030b040209060d15050a060806120d0f0c1b18141302040e010b12150a091a090c 64
    0x3528000700000405446145586002d0100140320030b01c0029804404800040e03a4081a10f44a6460400403204440020100b104520a080212060000c00c0c0d9009204a00510100d0000307561000100c521030055407080d942034000d1180320307840e00300703200042c10340c0c0400411003414a5204c3e841041c80c41405601183c1c00342d0b4a0600140307550701030040006224080310304506011044022418a2040810342c05905030340e0f0500c12000c034508180b40000c0c040152850180c0d5031511809401141d0554055120340c4111b100044907003c001495034642c035980d59541c4041d281100150b5092031003010403241001030b4101050000c3d00030884400400120009118041c0d880719600c1c2124101d5080005a0b26101c04000003220603910050300315506590001e10440440c84040c01032400060319a4030440c043c01e207108a400024020f02c06048440701007034141c441089031003c80317040000040040614a40d044903aa4040d00e80561214907801030395842c02c41c010029480e42d85c4d003200d091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 372502014 1250 372500764 372500767
    0x31b02190510021c1503030e060703030e0f07030203250e100816090f0b0a051c0f1a100305100e15010923060d080a140d020d111e0a090302060708 64
    0x880c610994055041c1e55424517060074102402e54034000d10890210043d035008441c002130380000c0611960100340c1c1a680300c0e06944040780019a0980c4540d5284001c1c1c0c0b0910031600c1640c25001341c4000340e9100c2807544600c100061400e49010104a00106078131200f0031710100024840000303100541821120802c1100d07018203000030002101d0540c0d14403440b062034140918000c2c0c803030656600a403581203c0c840468a001803500003038001001004141c07a5141256030100030390701442c50203402100c0000d018a5a4408140015124038400500340b58451498044600c8042d48190074800c5400c040e02e460010b10218030032042403c1e40181034260341d5040c1801c5080000b04440e14240c0425030140c05818000005480d000c4d10340d00103031014000081060f1550b0095410540e400f07120021662502c40d40d224500094112000c0c0d00001030a1500040350102c002080f281f140410244080541056040801c69a0003c80c440414440d13800404005a40c030800500180d92050600a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 372503264 1250 372502014 372502057
    0x1413030c050f0715080906071b0f050303040b06180403080c09040c090906060504180b030a0b040309050f1507030806011b060213060f0f031a04020403050d031b0219051002 75
    0x10700e41030a1250b56400b000001014001b0410000c2459a0070515903d02030a1232014402c0da0140802d41c00d40041c40b4104202040080003808001303107100300d0056580d10b08950b00c80041c0310401d0000743c0700c0c83c030808400b0000750000340111405030f000145008818181002503000c00d040300c200c8041080410f0301d07020b042141a02c0d9006400c007900316490b1050a0620b0511104401c07640803205000194031b070100c821040e00c0c1000f48a01840d0000e0741401c41d07003014200608101801d000c1c090064100c29400041c0d0b04114400240381420b403844540b4212580d281117490312009041d5504012810007481404002d000968018a00445006984803005480d0254203501c5501c0102400407060711030700100d80150b50340c400381020b4240842c45800c400c101a01054401158a030311501c04035001c414000000b03900303c0c520809440130420903040c1d048076840004020001c500503407090740090000d0103402050081140306008407521115007104510982c0c112280d4a614006100c502c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 372504514 1250 372503264 372503279
    0xd0902100504150c05030d06150f0c0308010e060f030607031a030607050327030304120f080f0a0c030b04052a030c0f03070c0c14010e01031413030c050f07 68
    0x24015041001d061952034a49407542070403400c1410300c50a400c0c41000c1c081642807001c00c2c02190b154801c4030302d0070803542e074031400340d010104400c1100c00006106c06107a10324040c00340c042c0d49192a01900d500e2034980c42c110001e03048000c000c1486400c00065a0b90244544040050600403c02c43d02c0c04075512604400c501800101c1c514180c0c0f00b0361005081c803060300c2d001011203412000b1105400ad0394201c010f01c4218182d4801c0b0010000c1c84000704200c2484096000f0395045002030b510820440120030741101c42920981e01c0740c0c0f404000d0808100d85420942c4450103044560402141c4102ea90700007500b210300880e4a0180300858500c000c0925004450060f520394016000904500340382c0400300d014068220f9401e40e00c000040410420790150811900050b48000301c0c01c0c1e0b180d107424034100400c60300310005010548140c5038411540c00b9003d4507022100f600c0c0d40c4a1640e8406c074801009070b04c42e5400b941402000c21440d03001c544140312120710186a00000c1c003019260926 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 372505764 1250 372504514 372504529
    0x4050313060801050f0307030c1a0712080f0108060f071101091506080f06040807030e0a1707090531020402040e18061501022d07060201060f060e01050703080a060b0d0902 75
    0x109106e0b4000f480b0601c00100e6492440d002d5615010400240742d2016599111501c96603c002d0000f412042d0b40e00981c40d8082805031140a00c1c1035900c3e4180d80c1d0f038103c40d0f610b0358152070700d401c0c3d43c0d41400001c1c80f0510990309c01001113804000451805940d440d01c0501017041d43d021707041d164680c2814001c0e0607007084410010000d800c0204803034035190715100418020410020200010104003d00d107a5651001c4d5000e4074411ba10b44488402907420300360b540c2d0080c820075400e07906000001c2c1c140d00c08800307800810326118103000101c690245400d4400c41c0200c1c1b08a0340260b00303010110f0701c02e0614a2042c49403101c19240441c45070314500081c5400c0c401001002c3c8400c201000c00c48907680401c0d105a0048c0d662418140200000d1610b01035001c0e1121200452051140008505a0542044049036002c01d18013024907200c10b0200c420000c0401c11901040d003c000e1440020302c2071340c1d602e900021341c03400002c0103a2902c00400044d4003580e00030000c11b89030003c43c02986007050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 372507014 1250 372505764 372505789
    0xe0d020103290a15020613050109060e0f210901212d0605060f0d11030a1a0a0e07081f03030305090c040b0a09021605060a061e0308120405031306080105 67
    0x508100340b10b10b104c4002c0d5682030081041c10300030b00080c15501089804d4118810f4198000028003150306401e400f00e5440c081c0c80c1d184c0c1c00b5803240d204808203440f48402522221031101c42440d140210240041d40c0044144203400c1c203664880820404440b818400c40d0111030b11008110004420f00b0081c560094422504240182c03030450704008a56801c01201c103114040c01183e5101c002c2101550000c00040c0300d000c03500d2100000300820740c0c80725840b80c0f00801001aa105400f0301c5241030000007049409416220b194040119011343d0140412945c0440e92181000c3c100080380b0a010041c00c0b80d40c0124080b03902c41c42400f030185000d010441e40c0c581c00351303403c0008083c900b0004a400002d481441112a400604401c0442c010305500c3e0380942c104080321942d0030324030030680c0244030703522074481d4400c0d00b0450700601a520400c1c0b0000c480d0003c020070304010b80c500c0c111801c002d0161040303c40380320402240c0341c0459840034800041980e519000c901d503240c41d0910002c545502c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 372508264 1250 372507014 372507029
    0x41a0105060a030b0d0c0e19110313050708030c070f06030513141216120f0509100e18161404090c11070e01140a060e0d020103290a 58
    0x1000180900d48601081d81c0c0070302d07078a20340800c0c444642c0307010480440040c1800340c003420942070045001544031002d1400f825800d18107502210244071781c2003c80320792502504080b003080000c640040786400c803040119000d0310079581d2066039440000d295510014000382203400410b0104111400512104010542410240a140b82c1260542040f440f081c20040c01240300d855040c003010010800c0c1c0b205100c424640b15680c90011006503111ba0502c0411240c0021110805102c04c0c4115503c9000c2045a1a0349080410003010403010890310807910040151116070809190342d0f1203c01c61401481e503903070307900f2414211005c1c1e80c01c0c210303420301c4028080c00d5003403001d122101000315070403122010341c00038020005c044125090041e190040c0a00d216045012a42d410120005030484001d0a4000040a00c2006000070007081d84519008070b24810032804160421007041c2c2031181c030524002070341d501d5442c40380180841c100c10b40c0b0314503e45460701c00c901e4181f5048000141401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 372509514 1250 372508264 372508313
    0x2070906050102101a06070c03111c0609110d032601060518030708010204180b04140a09140105090a050f010212180307020409060504021e010f0f17090604 68
    0x4020003c2e586440c1c03c0c4401d0b9480380d031031401400041d050a0340380c01c10600103000f5940e407051410452904141e0303000569400150b8078800400e0f240010380000d020b04c0e400741c4d0384401c500548404001304030141042d1400628203000010035600e0780e16500c2c0ca58400d486400140e030828002010303000d042c10304000c10f004400010300503160014244c600382308820358054a1680722401180c01d04001c4e9004012a600200d40410840ca5000e040b044000441c1c0c010009000000e003040151940180008451b0002001040040000e500290754541c0a000b0b00301000014602075402c40d0300c215080325150300021001e10400009000280c0344c1040d0100030350411460450f2210104806414149a503070b80720011084081e0500c1030390812900180b0400c440041c0341001409010110390486c852840c01032505a42d602c482158102d821041e5209400a002d801f01542c00c20001c6103040f09003d07a85075901c0b03c5031102c0070128820100c40c0050110340c1002e2609801804100002c6400a0003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 372510764 1250 372509514 372509519
    0x20604020609042c0619020304020d02100201090b090313080f071203110f0c0f24090103090615030b160813022e09080c0906060c0c130c02070906 64
    0x50382016102c11030401c0714006000385041416803070035460300c010600001c943d4400810542d00102d450303071046003800c1d1403201e40341800c941e0030101d210480d4004d511030b401d08442000340c18425003c5030130500500000444900c40d48580c101210210f0f0004085d9000240560658451b19111070007419404001e203851180425055210f0401d40a030040402c4485005400e1510900c02110306804001c00c1c0e41440b0f4003c000c541d1600080784507030b402a41c0b0307a01103089030309180e910f05d1551803103404101e0145262195180316607214623140e50405482c0c00000000c80d226100e0f02484900360051400198a1442d01144d1548020302c24504001003254190004d80c000a05e81d5003c680418a84101c03d40c61001071429900303581000c0904503403080490140600c01a20000e45800341c440d159480c0d50344070415500d007580ca0886803c140100701040f0607085c9400030704030803050601a51200303100c0c40c02051114451110b603416403070b1101e8540c00c440b80c062041402810702c00360b0a000490 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 372512014 1250 372510764 372510769
    0xc020901030b0c0403080307030c0f0903030507140c03010c050702180f0106030e01180b0f0a0510060c0c0e07020307290c070303090210120f060f050d050304080106032102060402 78
    0x14030000d80b0411034880022550702510301210b0296a00c1154a44c8a0800c1600100100407140030324000c43c2400d6140c040007800740091404407030b45a9280c81c42d00300c640d0346150348451020b1648941384294904003c1541e001c0c00343e2000400e850751100c0d12005940100480c000c401d124510000d846c02041c05500d5020207025815079226003808140b401d29900020f00622885000342c0d60001c225406074100700044001c00d00440d041c0b0800d0303000341c40342000703042141c000350b80000c06075811090420100c2d01406259001500800f9030030740705552011880c121303010413645080160000950b074010440d10f0040c06c000446c42e10014044035000407000009100d0142489490309004116a81094880d07000025543d40c007801d408001071a0031009064480f021441401d014104499113080300094440e00e81114000640000c01174540411700810841c45e0505a07414041004085440f64090140000451240c0c1410740c046416080860780a45c20340c003c882190001c03000e000150303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 372513264 1250 372512014 372512029
    0xc1403040c0b03070203040b04090b01030e01111e1c06151107060c1b0b0306030f01050f06090601090306110304060f02120c1803120711010807050406210f06060f0c02 73
    0x100c0107070b4201640c980741c1e840107034994000c0303500c90614003500203004a0302070b6054009005a1000703072001c1c130100b080896603c0c2612040d0004000d480818400b030035551012220380c0c0b01c024043e01e9031501e04008030b070410007448484008182d11640b01c644c10840304080c8040714200502503d00001c404204c0c5105540742d21113031007030741d040104030041c90040c00101c140001130b0f03052600454007055076503003600045400c1103801320710902481400c0030340c2c00010700070207208030306984010103166180000c202450401800080c10007071090004000103086204044140512014850f1030781b600e8075001d001d035050209018001d03030061200c2103042e0000224260440d0002c6142ca4649103400200340200c007400c4001ea601d84142c02c8100c9000c000c1c1c8000380310490260411030504012040191081d00040d0744000010b2020401080580d201c0c455545002021700a4036801c0c10601d181c45003911944685059102c2d40d40008111a60b00805200c140000506001c0c1140815400013402d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 372514514 1250 372513264 372513269
    0xa0b09160f09030503120703020904020a0c17040803120a020f070c1a0a020c13110d020d110403020a09091a0405060f07080c1815130e0108071a070c0f090c1403040c 72
    0x10302529001041006020790140c401400c80644110b4540340692801050030ec0c40d584140c41d078148041c0388042e440d40c0841224140c80b2804001c515001d40000c14a880c10801000d043d6125800c0c8044020ba2070311000511070140a50b000001080c28070080402400c0000e8a07000020000c004000303800790042251045038004549500c451075000c0c051001416480740355002610f4001105410007200b60b0103409810200c41041210f80c0b24001142e00710320460201942c0304660740300400c0805182c0e0442c4141c02c2c07065040308400c0d0f107103820a02034040261030454070303030b0480c20800c100b00c40100d1416500c044507290040c0107040c0055a20b0b240e11417854044015485000c0520301c3d903ea0b450518089481003440d5561142150300c03070748080b00240148406801d51800010341080c000880d04d06450200e5a45c8600405100810000354400e00c42114a89a40340380054107041c520744100042c1038140b401300e8500c000f884003d0420207192040c16000400744248804243c400d01007005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 372515764 1250 372514514 372514537
    0x40c03030c1b0810060906030305030f0a0e030a09050924010c020a0e0907080d2a050c0405070509011803050a02010819060b1206040c170a0b09160f09030503 69
    0x40782802030030034440041108080c049a040781600005a5403030000b608040101d0113501041841e40f035044a0055442c0c078400900000c8062000c54480750001d0b004503085440d0001c0040c00040f010004c60458200408100118400043c100000d05285021560006901c240e5040040c02200100c1140c10f40c241e290781089258200c120464451001b941c000d050043e540810f01d16003036208a90714a82ea01551030a809030004036002d0038092510800343c1c0a0102d42d840c2c90008807500720300d109014980c25521489515080c400684803881501e00840161756447c0d9a4250b800014154101144a40c0c071031a84e44501000400d9005c1502c1585a5091901e0801900d5a01c642c0031054000d0001410080ca004000201403441c040148200d080414264603141d698000300012039808481d9500481d0414481600d0781141890060f481400707400300040329507005011408928080316200040b92091000341c0034150000b0f00c45480d501d0500d45640d0f0381c4d080d07540b0540c81c3d004030640b004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 372517014 1250 372515764 372515777
    0x91112070f0e1801060905120309090c070209040c061d01172d060109170606041d240a0606050d09020301110f031008011a150904150e06030105040c0303 67
    0x24600c0c0c0300741850108924003c00703c101800200c90a18001402071083d0408541140000502428040917052503241200003642c10020844140120044010a50043d00c5d500f0020707180180c0d10000c9a5024902520728080340f241080000b41c0300301850b05030411a20541c040300f581507030388440c0350f4000401710365107a0726544848000c40c44111001e44d84d40e041c1d460152200c0c40e181c4501c120140300760fa090780e0310000c0d01e90700caa04032043c280a9600b1411a0401030000c0d80f00c0c00c00c0d8000040031407614080c4040d405200b4061410030301901400752890782c13051050002d041280c007806030081001c540400c046071800c00702400d94402e4184480c48a034030780008409556081d440301100011100e000d41d6034034014003003035000350300031504111800e418540c0801da400c41441009020301207105d020902d68010382c20442141c0c8400300e50b02c01c0c1c071020450401c036622130b400f42000c09146aa6005120382c202180d03481403040090100340240e2520003001b011032002c0000e4011a81c050a152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 372518264 1250 372517014 372517037
    0x203040f120f020901180f0605010e09090f030315130606020a020d050a060513060c0e062a01020a05040e15010c020411070f0b0a0c081009020f04030606030c09111207 73
    0x20742101e0008070020f94010010000002c808141c0154141b805050000c10080700044c030040f4800c030b96090241e5400181006401406410100d008640200101044403481c2c9906c1c040c0c00d1869008940706400c0e4000c008903881542041c0e40c160007400c0e18a04288589401d00200270750f1100101c00192080d516103468105101c014401c0c0c800c6076402940c01c3c444c07031030480c0f0711070904e03100384208446261400f4a0303490503501c90328440e550f8190040c075040c548262078883d011001e241da1030000e0b400742e4027542c08509010920007881c0c58009030301c2e459156460202e0702142490000c00001b0000320080e88030741d0a0382d0003078508a0b040d9045038002805000c03d100507007140500440141554190b100c140c0500c0310800c500d912403005003000340059084244103d50489042c0c50086803004544020302c4012180d0f0040c004001403100003a0802c0d5aa8a804042d510141d000340c070700b486203283c1401100c245001b820095500d0074103091034141000008904504c000740303800100041071429 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 372519514 1250 372518264 372518273
    0xa061d0d030507151d01090b010501080618010e06030607020d0f0513030b0a15080d020303060603091c030204090c090605090f03070f08010f0c02010b06070b0403021f1b0203040f12 79
    0xaa4403c0ca8001e9100780c22589100c44010040505005120490030424032a940600c014081c4469003030744031011040342e034030307020040d224902c1c042d06540d484241f04490305610ba8400c00e66030b0081c180d0800d1004142000010300d0706003403026129104640100c07200016941d00b02c02e0341d442c0400d00f440d01941e02c60b422100500c0043d4150401408188200284020000150032901001780c00400e08924556540f01d031507561118200702c0000b5070010f10010b4014074086001d941d000c2c5d0040b055481b101c9607040482841190708000c3c0c0f0120340c0c0490700b4044c103003c83c032079900f0061190610720089801d040d005007580c094116203e1107580c140c240d841060300c083c01540001e207405001c4801190b00e60700014060461038130815001ca2818070400f022900c1401952142c20014260601e04000d0b915014506240100290154030480d1491032031507811851025a003204c5107000940161604010941146280a4103003103520a02060120542d2200380c00f00312403c3c010b6011209000b07242 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 372520764 1250 372519514 372519517
    0xa0305030c0d0e0f0d020102040f0306020d09020a15120c120f0b10050d0b100c020607051203040b061c030f121506023913091506050a061d0d0305 64
    0x9058110703410303c40340d0440c540000808040030002c0780103944a03510070282c100e00301e000d14800d01080c00c40901040020174019402006c00807042c00e4042000f01c100e4010500d044603683c0003100c220890404140120b81c44001c504003203070022814003882100a1005014030003845541042e582d845002e80c00e0070302d56a0003000640409032034400007440c0c05002420913040305000e80701090508144071094034200021460f071402540302c590311181d0680134007603250040c66084400344111000706954200f403401444c8a14440c0070746142074600f00c0c0c24025803070030f0600041c030552503501e98a800240c0000e245107201210303207040c596040000c40d0010250441d811002070020071a44040f4a6650205a40c000b061480745490b20307080368901d070f0440303104155840384030b6a540d80c0e54500d0b00d0b2038100140200380c0329101d008642d01619440b12101242d444d152111880d9030341d4401c014504100c900140103100c24103055600700c0200c080181030300d1544049a00c620312216480f03080600500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 372522014 1250 372520764 372520777
    0x6060702090a0e0d21050f130212030708040f05061c0203070201090c030b010806010510020d0507030309150b090930070512030f06040b010c060b040e0a03021b01110a0305030c 77
    0x20840d0031440c4002809000e11612403a171460159010445044540c0507000c0c0d00e02038106030495010660360840b2600c60f074030620001b2640104c18503442e40d81070004001034603031a8002c04000b03036260f00e807400003010503803e030b404a400b841080c40100c400f519141100c0c0d400c400c038813001580d241c3d00c0d140708900524161030000c20300c5078600004002d00c000c02003024140c8003280e00b210f182c4c2c0d0725a010040e0600d00c054956006070311465080e1034040c8140e01600e206072190602050b0044250f44d040c0705440070b10340d28440d07d6611a03d09042d0300c2c00300c018607003119040014140010707011000521100d5407040d921010603a040001c5900e11012048451103074122040e22021901c010f000b0506520695045a42e21040d6010958900c1c007841802c50004058440003440d10195403058064440320340c000341d1050f03031a142420102424030503511036910a07805002d000030502803c00c3c042000c58400c6c0c0c1004007840d031983c28000000340c8842c006801d41032840d00c980e1900082c0312140f0582 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 372523264 1250 372522014 372522041
    0x501110f0d050109062103090509010801021806040f03080c0c10090e09031603030c02070320090f06030a140c0616120c0c0b091c05160b0306060702090a 67
    0x240c81414600310001601841400301d0302403001d0790381d8125001c01d0b640745000300075900c000212020815480d030501045458400d0600c402c01c242d41d40b00241000b0803da20250240e500041c1c04a080e940b5034100ba424442d003100c045040500b81a211345108506000c000c0000d0b0300050040b404180401071004032100040020b195100102001040007056214515a07a2020008500452408025540501041543c1c400d00044c562011000f8110311310090f02540200100440425101500482084254012008100703510418031210314001070402030b03182000d00074030086541c082955148950000d408020f00210220403608000408080d154040c000140781d4015204120a80035220b0003100c251101c42100d010503240c3d0000c001e002840000c1c00d140500415200e00042c248000c0d01401101402810b05404128003022a4058607558000400d0f52070100b81d4060740c034090000d56200604505241c0c0200d176140c002e20400030b109582c00c10018211a002d903100744d01b0803004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 372524514 1250 372523264 372523267
    0x9050703020405040822031a06011707020d112d03040b12010515090108061207090f0204051c080406120e060a0603030f0c0b1617010b0307090914040f050111 69
    0x7485c04158603402201c40300030341e0400b071014003c40840304051200712900700c0005035602a5256103400d001100400890600440c01c040742072107107200103964031400c2030350010300c0c060601c40000b0705811454480d8070f04076445504a102c5c0395441032008540e4130102c1d00801400f4001401441c20340c0601e801c250f0340c1400c0802c85006525010744101c2c1260000d40b800710760120a50301c480391070b00c506400180810b0000000c0360031403d1050050502031440001e81b01c00581702c03c021000d4a44e00d888907207580e40c0115051000d4a020162120034401c4030000c0703041c80380c0c1640c902045020303074441d002c1844104859031002d244150041c1c3d0710001007000f940e1951520070f4100f802000c0c9400240c000030101d807442444107000c2d040302a8000d403c403078121a02e90b00c22503011440380150700b140c002c002841c8054001010406e031801e01902d01418507940742d207000400240000c109502c05a8840d003041403019a041c00d140a0301d40140d00b001c2130b0203103100d15060250250282c200100c034400390 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 372525764 1250 372524514 372524521
    0x1170a02060d1d0c090705090904140106051002210c0a11011202041203030f1104120503071407030b090114060d0203330f0f061c06051003030f02060f060409050703020405 75
    0xa0200f032022240d01300300d945084685481e0400c0b2614012090403a03003211455011502040708903042200d0287c060b00049415911030b408134101c0002d080c04035016070301401d00050104413404507958410010a41c05050201142d1059540ca901c0580a481c00d4040510300302c0350703403181c0c04006c600a82c101041d55100d030f9a09103258001c0490328190000781c0f500c03481d0b020080841c003403140c1094200210a05103410242c43c204a942c1200c812506484100034080004500c0c940a180c9100c1c1383c0b003d094654514200148401d5000f0407440e420303407502000101c00072804031401c1d04200180ca40b61207001e81440400e140c941444901c1e13030000d1900305c008461462003150710f03102c1495150005000c3d195084840e20010060300e8452070945000c00044050034420488142d0740b5460418901181c0503896200898074269404007180341905020700a058104003004601e420910060100f454260b503140428030010740000e100307948680322101845020082d6801654004000300140d05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 372527014 1250 372525764 372525821
    0x20d020409050f283b0d1d0402090d08030105100f0903110f040e010b1306030839060f1608010312050730110a020103020d0e030c0c0901170a02060d 65
    0xe10305d00070307000c0c4804d60540640f8001808905c5a0207018070380c42e8000790390007002035000e80302c80c2146000c0c1c0203070782442054195070b0f4039554141128007400d4101d940b941042c003807295500c07040d031108050090807100c0b803203e9039100c4656002c0740c0d040b442c40d2990543c08000680350180004410354442e0a141c12884110012360050002c501c00310703124507180444040f0f00c41903441c24880070f400450b040c8440c6042403543c801e05000305a01010141e0f0b11035410113a52404c0303d02810760100c50b07016404001303070390458180080d0800340300403801201c100700740c80c010600001400300900040e008031044040314051419600d01e00d910001a00d2107e4280b4040c41002103481c1854401d00150300008481030f010b6134150925485d0b000141c00344106540054003e58020100b01880b5503841c0c1120101c27000500151035142c9501d80a0b044030a03107101000a05503040c0c10025400d46000c00c181103540000030510b040c41c0d4143c460b552603c024001860007003100b400da04000c242c0c0004580007a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 372528264 1250 372527014 372527081
    0x1120201092426010e180d081006090e19020c0d0c1110020304060c1106120604110c0a0312020705151e010b0901030209040e01020d020409050f28 64
    0x280786581c80d4001074241d250f503007405500900040d1140c902400040c001200103402240e4000021020504000b44030a03106207040540c061450029812030700303101b10020a007000500520051503d000c189007400d4825112074006880382c640d0b0300032510611013050041c0c040e920800000e4080c1c074003d040d0b08801400c40b607003914003102c824aa03c1010011480e2030080310360b90409550041d4140b5092500558500c961103d0a645d41c0c600381c500d00e80a0303039900340104003024800c181d07503440303003440c3e0140010f50310000c8500b0760344a410b02ca03508128000203190351020360145403000da20b1a01c50318040092180e108041c01c0c40c0240411403060343d00705414280a4880c0c18051011074900b00d0701320340c850400b8012281c22010800200b0301d15031082d0054402e03103200401c00614021003802181c226405000301b41206e58001c181005442d03403502c181640302149003802e400618201d05080407105548070011034070204120000802c042c5a800f01c0c400f010b0070312940c05040c6c501d50512041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 372529514 1250 372528264 372528329
    0x5150d0318170c09091522080c0607140a0c0311060a0203090f0303010303021b0414070f12021e03190c0c1e120f02030d020f1209150112020109 63
    0x2d44140510307850107040c90b071400c52041039498050003068240402c598034550000d00108040741d44d0101070414030914411641d0803910440700250f488c402005d0f907604000c030040c10002842040c0804540d42c81e0390004a03440445645808a41911a0310b42912519404001e03101c06215840c10003454420682c02103008604020864600411800310b07280e90784000d010003001a0800e0328a103040d10b00722000c01e0b40c0640014404a2a103c1d5031002100700401201d05100080200c26510f80c1c0540020020b40d07540d6404109600d800001c9078034100200400030785450b5200d0010000d802d0180107007044264a250131000e001c0200803802c020702c1c10f4804a401d684101144c3d5803049246a070401185289500c11045800c1c8418800d06440c041e5003010902c081d40020064000340200303510050040c0d041640f40c49032180e050f00b400c3e0300c00150081c200c06150b4031003401200032052200045044410000c002c42d030806031f620048810150a510240d140d4130550fa445110200c000c40b107048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 372530764 1250 372529514 372529559
    0x102120411060c0d05030703020d020d05040212030720030703140a03080121170910020304031b050102030d09060603060207060218010302043b041a010905150d0318 72
    0x465540904110180c410004010f24540c480001901100d004d2005158000803a06005050404048095040e68000c0d020f00c080310b60350b13108110443c0740115282c2804420341d0001c60a181c000c1e5900030100c41880100006495824000780650750b0800c01d0101459010941041e03424081d00d0301551900354503000c40121f05c2d00d000100c3d9143d40c090700b185060806a0318500e01d10480c0c2c460410f04a4043c9401c82e0b1803070100030980c000c4d180c445d9030381042031107a8000c503621451030070003905001b2620341828914003054004c100580c2d000080e9401c8181c8200300040c0c019661411400408991b0b0000b04040d001054110511049901504412444ea6060400c580e00b600046040384624002e2190b210320780b1848001b0400e40c00c14141c858440c5248940c00f01950110f0001040c0d82250708039840414410f2201c014206c00c2415070040842103030900c42c030304003030007281d0b01c850500c01d041d40108404003010003494400d4141d0764000c0d00354502200035540701e2030012058400d1070b02402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 372532014 1250 372530764 372530783
    0xe090402030a1b1410050f0d06050909100509070f0e07021011030a0e010516050c0106080a060207030f111c05131e050d150b06070b13020109050108070207030b0702010e01021204 78
    0x301d1360800100c40e50b14030b1038030fa0b43e142c50204804003802c1c403038000100e00013016580740f00c00300307583d1a000701241c051b01c1f020b4001c1075401c07551246182a103c3c000d1200c0c2858005a004110212095000d9010307100d1421200300981c1d13401008916040d05d01c059298810308000200803585601401180035040890060150a4a881290782038441c01d807101ca41c0256072409a40110b071041c00900b40c2c0c0c0b14900008503030580e0300d02000d032401800c10402d07200b440d80001c02008054020000824004280c280b40300b00c1c0c212500065190000b801c140d0310750009003600d1401b01c510070030485002e810f202003500c80e100c8d220000e03141917040c0359045051a0f04111000303d16031901d01c2a03607034020750205090705402110710100c40a4002e440300d56800034428032503000081c290421143c85240b04c80720b0700400c50090b00004100300d02d59400181400708034000d210580d64041341034800e580d002040c5029039261050224010040c5011030807095202103003910142a1035402c99004500504100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 372533264 1250 372532014 372532049
    0x120c10050a0915091502030601020f03040f090501120302070501030b0402210f090c0618011e1211031e0711070e09070803040807060804030e0913020103060603020306010e090402030a1b 81
    0x30200c038401c5002030544214240720172846112900295440711042c410786d54104048012103241d43c000303411840d0201e8580170184800206441920b004020b44051000003e9042e03d01a440340b00602400f410140c898405184545a0780c04403011000a1141c14a0000c9d08a010615007041907132080c1001c0038040106081d0100041c0401c04140c00400f103600d0a10010b04441d0300071103030b41d401d034180880c4a01000280d40701d2960304110078465200e04003c5070240103564101c03035a51200f802e640b01c0600911209100d10b82c90350002013503013000754a50382c03070380e8105607904403404800001c40e210300c41f0003051940420010a00800c0501c040710051341c0c0707400d503040c0c50340520700400301198003008007005010300c1540071b01d41041c06404c0c25406054a0360102c0c0001d0400c0b10900107a080d000a00710455030315101ea04002c2c4964541142075041c4200000c0c502c2c5541e145152107028803801060965800b0320446091a502a9510b6001240d0950901801c11103205e802c40017050a03419 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 372534514 1250 372533264 372533303
    0x4050c03010510180f110c01150317070212061302040b0423070e0418020102061b1603111506030d050c0a0618020409060b1c05120c10050a09 62
    0xb4503000c0c843c49800f00814a040000030f9003040031031070440c001a61561071283c4d0618482c401e03180c20314545100c00c1d68400c0000c1607036080d540202426280d045940e281007002c2102808001c5441803210a040e5440ca007600000f4003081d050280186603018020502c0200301510351060061842034034184108000c0d0300c10041110b030344c43c0081030458400844034110400e0318440703ea00c20400d09040c001c800c60303403011808a51203600074101201c49841c0079400c0d583c04100ca141d10000010710814800c10140c80381220340502c03100c03085000c0011810783e08050041d01c2c5c511003218104100d510002d041840d40188000c280c131068028029000c8944503c1c0c841c804841000407d0786c010b012604480d0703156001080c041c0701c803071844050001c4000050743d6074040d00007010300070305c4049154103000301044070326110b002030307118500c16801b03442e00000e030040781c4030300050b141d40b2a15440301d020918050906030301444000f605458001003200702e00765a40701c602c030701e80255008031421141884 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 372535764 1250 372534514 372534521
    0x50318010509031e0f0a0e0102030705010905030301030308010b03100b0a2a29061c0503030702010f050106230f120c0d0b01082208040803070c090b1512060a051804050c0301 76
    0xc840c0141c1720b04100c01c10210303000d2103003000590010b02c101d0345403000a445a908503288900200c60603000000100280760313205294034050441c08a03050314500344203016120841070b0384a4203000460114080c4902d6001300162090f10a450300c0b000402d402d00c0581003050484594103d1f1011500440d00f0a40b40d801e1080c0201b17181103401001039a1100401c10242882111040301d01e444004d411000103030003400510f0054503550000302e0148001381502c0706403001608401e080001d82c1d003000b19100e41d082c1d9076103400701d62240801e81e524000d0b4008040342c8680c002c0c00450304062014031581104401c000d02e000036600d2410403000b6105001151074030819100d031191440080801154150241e10034840280315508a52034181d69071246406d60308160000e940d0307840c082c5800c0040350031030f01500c1c884810441c2c5c1100169102c10801e801070160403015608004014001621501ea10210f44003805000f0064910318000146011143d0343c202d0303040303889005030254441ea5040501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 372537014 1250 372535764 372535777
    0x70f0f0807140604171f050402120c0a0506030a06050d03051908130212070509090c090912030f090703050a0602071e02090c0f16060912050316050318010509031e 71
    0x1003205141601e092200c40300712089407000d510f18014403c0082d2181e13240706d41c0b407074041c880000c081001d2409004010060311068486001c607003202c510046a0f5540900e50700c1640d03811101c00f5182e0321880c0d21b170402000c95030840740e0805d082d049000c0031b050f080400742104111100a0540c01201500704480c0400181c0300100c100c400b071810180140303040040b0080301404241243d074015560000942c3e005e100f0303101242d0681008400a000b401d0040d191580101028001c0640c60700c00b10a40c5c080d44801000b02d1a00313813182c40810002c1009020300c100540d00441220340840c05801c000c4020f5100070021034180710403480700724180301d0200840340682d0700180601010364500004ca0200d0707109100114400303000708988103429040070002c200d0103000340c00c0024844990701d401030310390601100600601c02e040c401c000e0b0440180036122f04100c100d2a00c0754903074654505141e80b04902641903101d6508080401c04950b5002028050300360004d10b4030003904540d845041c01522521 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 372538264 1250 372537014 372537019
    0x120f020303160e040f051008010501080a0311150c040f0e1302060d1d0c03010e031206100c06020a020606030601120c0b030606040f06030209090c0406020a0f05070f0f080714 76
    0x148000b580400915540681e141d03400c1c100100881d42550014045403880e8114808096a0b4000c0c400d085083e150088058000749008000e00d50428507020380c1c81820f010020304219198481c0d0407040c205001e054154402c0f426400c0107401c0c0000750708220380050145484034045c0d00c034009840c0051924040c01003e2010705404680f9494007030090035403140b000c030280c064556241c1c5480120000e001c15107201000b0180c0301700c0050104050955491444920841c5c0c420312a1110b48903160041c660003450440e0b0503018288801e800352151300042002415040c40030584000558000c1002ca120320360880c1500c2c056030300e6005d0400f480708440c00c09130161903401014451094014011500b208000344240d007041c1c2d4038200e041d03207844030390049400a038002c18900c0c5142020049a5008880101520b0a103410040001d640d981020009414485210940800d01c1818017001c009403020708114102d940c0c40b5901c00c030706210f0310f101c2c641584c4601c02c00000c52a0318103040c02c0605500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 372539514 1250 372538264 372538267
    0x110d091e0809040908040f080c091003080f0903123c1b0a17190504030b1512060709050306090106030c231003240f090f02040e0f04120f0203 62
    0x41003d120041046900490b0744180c2004080ba4219010000100904001c1d00810007800010144000c054015251050700795240c170341800083c100c82c003a05e40003034103100c03001d0315400c6540c002031800910220705420010000fa00e031010100003884514000c50042c1c08211b43d4849000079008400080402c0100c05804d1017042d5941c500c3d21966003448804a00310740c0844065190409030101d1030115039444040010f040d01c18007105641c0c0d94110243d4103016060918640301c12072128002420f404581705021070391104c0b0341c0c43d42440034401c0300603070071a026440d0007a405400c1c1c044900499209114100000f14210014080c0405680e070102002e001d141c81c082c45048011758112803400c0c4ec240c030300031117480b649582c1910450003441c0d540c0800c090074084504403008414405000c070039454013005120380c41c2e402d040380301102c020b03040005200b1307104c0718148000e001d580c10010170b1546007010f1104120491569074000c038003e03004000c05c0d5001200076103003180c0425426000d40c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 372540764 1250 372539514 372539527
    0xb0f0102061323060708070302090f0111100e013c09020102031b011407030212040b060d0c09020301051804030c02130608010203070f090b0708030103060f110d091e08 73
    0xd007100d02c03010040c459941502a1030888115a60b6442c0304480c0d4615544580200014541d10662241d0000800c8c1401c51a0540250105403c11203c108603414041c042c2d66085042e01e0410283d42030341d01280d800c125113100070b1040c501030480c2c6002c50450890140d51440160300700c003a200d10301c40c058510507950940c0720b003c3c04041c0a41900036415800140041c103040c5040400095401070b1210001400100014115240c5507024008104062040c8880d14616508048141c1c011346c0000c8240034075600c450020309040480368008101d088455000549044c1c82e4018606a480031a6022580b4883c601e02d075503105000c071070140000d01c61404a4000d410700b40007489074407428004c0801c1c40354070b544006013642e02c00c1d90028009003204460301e203261360201c0c07400080d0003c01409441d10409480e0140e1600040c0405020190b84518540002406901101b04200f4200308240c0700cac5c0303401003074000400549000303496040890103001131562001d22118062170740110b6203800c084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 372542014 1250 372540764 372540781
    0x90105180a0506030405060403031803050a2106030c090b040b0307150e06040305060f010e0115030209030102070b0103031d040203060a03080901020a170405030f03041410090f180b0f010206 83
    0x40040c8400360040d035424400720741c1d40c40d000300851040d1301800c0103003560f0405150082c100c41d0a941030282109406d0300020000741c1c84011502001c4c0c3d0351a10000505840c00c0301c3c0c282440d074030b40c100304031031070288000104203080c0c41520403100602c10030400c031031840052100b0f442e01003030608c0e49500066014052203220662209100d07902d0320340009480c11040100785564001d80042d12181d110a04110b2503c105c0c50f48507014008285c140d8060f54500440001000c21a0181805054000c00c49017090785003541610013154200807c3c40c01c0d96540e08000c2c01c42d8102210307180715810b2070822400b0702d041c01c0c0201ca004120207803010518034a151503103403e0b504108070351411802410715500100b100005550040144520503981d224070304010940360000c3c0c004503503d5a0414002040501c00608150f00b8081041d41c414800da038481ca0f01703d510303e0301034016005c121600d0202180b001241da6805500b00410074040110464001c10400c030908034594140c0160701080c002a140c6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 372543264 1250 372542014 372542047
    0x10b19050d0c0504060b1b0a030e04110d020406080f010b16021e03060103060f0f09050a11060f0a08041505091b0307080a15060509040b010306110d05071206080102090105 75
    0x14020680004416143ca0008040c1d03240399200b030118220108030031700451000c10240081c40400030080441200c159000b0b800c95061402e0140b26030381d02c0c0503840700d80f5400e1041f01d811124000045503159200d28028107060300a846105042c0070301c00000c190400300c03108481d0102000401c400b4494820703802c100d2800c0c2130181003002014080d44d00c1d08640c900300441d42c0a10310815001c100c4000825017681192001c3c0c00030040301d8140910700340441c10104000300059042104119440c0f00000030550714403c020041c3d604c514000307244906550701104541c01144142601e00c1410000c45140055440542c0d0b48413150304180e803180010710460f49090100341025054400050344ea081c03040c01c01204040a5403440f46030484406200300e00d10030340e006040101d55402f01820203444034600418140001481207986503441100d500040d02a200c0c16840000700b80306514000c10005e004440103201a80390600303000000c40e14002c1030003541c43d10001a52004d0810031010030601c4030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 372544514 1250 372543264 372543289
    0x11030703050f0417131e03030f05090906130207020a0801150b1801080703060b0a030203220b0a150314030706140601022d0601060519020a0f030c21020d02010b1905 72
    0x40740d2001c1000201c02029480e540300640344052500c81b50b6183d4240902051a03214400082180802c81c03107100d82e80342c44a40360002c00c00d4500c80e406520065058000b88a50040070390301003201720300082e00755015002134040500e030420030942c1c56990003400b12207000d01511101d958004112004941d48941c03403240c0d01003281c1c0341c00705d0010394601c110b08056008820f2000041e07000400c01c5081c801c5001d1100c1c0c0c0d600d00c00700700400401a5294101076120143c03003181019198a41c540c0030a070351107014000b664110742451000e84101045540c0d0703602c500004c440c154201101c041c100c01c03d2010140c800c0006802400510b00b04072800c010942034a0026608084010542e8005102c10020340740645a240c60302a82c842000c01404040b00c59403915000710340c080001140060162222003501c1c80c1c0c0350408540f00c1c42d0341d00c4d044401c9041c0403410340d0400038a0794801c486581c00a5003040c0d503081c40d002042613a441000b070110502410910340c100e2143e413207017040346080001c0d59048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 372545764 1250 372544514 372544537
    0x70b011403100501080304090b1203030c0307032c0d110c060d110d02070510020910050708120a05100f0f050d1406040303060612200307090911030703050f0417 70
    0x70a44020842c0b00c08031542038010500aa001040034011041103115040030780804507020b0401c81d0005420030703507038030004000403580300020000c038040a01a8204692040e20420042c040844c040d04101107880d078400701010700d12418800d0380402d0301640360140c01c0c0b980d007409051100203d00174000c483c0c0c00040d03440c0d25640c1d6580c41298900c0f01c5805080400081c180240c0d40b0515400e02c80c0c0741910401d080c00320305104024450b001c2d540d02e01c081d522480642000d689481040c102003100b40100720511101164030010000ca60072242d0205100c2e03030b145150512010b844105000c5006402d01805616a00f00c41050295141040100408070303c0703800b00301369100c4000683c504180082d142100425102c2c601808003d0b00302403e00d40c1d500140900f003201c11441480ea00c080303032551022031103c89c0c000001c501e001e4421922100606080f21051280718540ba01e4a0f00c6030344101d64400010b8079003070104942c085041203890150341c001c150754403555082c2c080082c803036200244150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 372547014 1250 372545764 372545773
    0x906160c0206040e04021503010b090915120105010302130b220e071502060708091c02010b0d0f110f090406020c16060807020106090c022505060f0304030e06070b011403 74
    0x5982e42c41c001d20241c0012456040c2504140c41030140c448481135001030910014030040c40076540c480140c40000c0001c4420764410303192404d26901081c48400c043d904a181c503084190644015003055040b2442518107c14001d14514107800304c50a0342020f641c031400c0c0781c03441c454500b42d0340d244140440d03d00100140d10014020b01510b0140241c0c021182103010b1305c042c10801e42c0501105601440c0b5040107001440c5c0b110106440d036032607402c0da032a01c0c90f95049455609100750302041300b1040207000540c41c8000781c20155012a40050b003200d060401500862203410000c0520494560140421100d40c88039030710000a9001a042c401e418441d00050300400c09805013410000d0280d41c070f4900c44c1e420308403002420341c0c81035000850064105001c40c128107600149500000080740940d41e00240c0101c0d801800c50700a43c4419407181000c5000d0f10a005e4180065004034480c3d201c03404410140428480c40d40100d032006015030a003600100034441c5020074200d2481c60040955 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 372548264 1250 372547014 372547037
    0x204020d0617010f0501140603090a06060603060315090b01030213110307030f0c02010903083112120903090306050c12091c0905150901110f03030601090905090616 72
    0x1000c44140354001e40c1c20409040141c600381c0002e1003074980d0004c800105100c0c0758145050318a00180309050240949000000100001c50600c0070300e011903440081440002e03a6210018003420160005035990401403414035020040761041a40441c1d1160b51400160f10315000c10901082900d540c84c001516440455440e0541500440c4607100c02e840000342618400b0058003101c21080382030081d68501188100401d800850070359000b2506403a0f00c4001484e18886078090080c020b054004504103407a0200f0030206000160031781c00b49a9070040c40100d61a0300c02c0a035091508047d020990400c002e00225036640c100c968400443c01103145800c4160641101e0580304850b0605c0c681c10004000d0301103043c202248290502c0da10b0080c10142c28240000d40c11f00e0300c2100381c0f00d2410005081c25032a4003034041c0c0540806040305607191008041e01490310f96004584182c00213501310008604142070388074090003203c3c2039000707203c2643d42110b0341440c070b2a500d00b118203002904054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 372549514 1250 372548264 372548287
    0x2901210c140f03011a0309070b0a0c0605100515041a0915030f0402150f090d06180b0a0b0919110d0e01020408060f0708040308041707230304060e010c020402 69
    0x5111141d0030350a42c55407580b4005a030003104950b034099400c0350100b00305202a98100040000c2078440206520342e17600312500c0141d9245c0c1158100608103400c1a0801201c2c0582d1104d10b0104c65080d102c040b02c00b100020322100d00e125070b01131084800305c40740320304d11544000b0028100c00754000d0840c40306d4582015418150b50002c5442d01800441d900070002107041ca240040f40c508405507049007000c0000340d042d4158010745154030300840545130f41e0414000c482d00240388810240103180400c103030314105514402004c176212100f8900381400b480b414141a003038580708070841600c1104208a41c0b8261020300450440300784152001d120400c146982c0d03106001e400620311000603a01c1d03242444603400c0c250002c0c070600380001340004110203240c00c9040281c0c03082d41450084815902c0e0f01d45410400e41200a001c131440e0041184010070041403d84220440050000c42c0301010b8100c01e60794911450180b040010700300f807414091035000d007850040c0720b0301c0180090304001c00044c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 372550764 1250 372549514 372549517
    0xb041e1505100602030414012a030807270302090a15091508071a03040302030f070b01171f15030609061b1106010311132901210c14 58
    0x100c0311100d964038414040d00d502500c410384028601c6001850030301c0c0c40e141034a414040500c504605100108512000d850280c40582100001e07c0b40c0f0a24924900d00f4024480741007100c128012850202c03828440c0c1400200003007120400300b03020b100242c25070f424091954405040c515509440b001003409410001c0c0c540e40203440203810005841c50401904002c204a40d809090907810859040c440001d400402c00c1c007c41c900c281d40c0d9600d031907600d0202d00d54440e80400e80c2d226080418000100440340003100d04980c620300e541c2c141e05510810060f2208082c0c3d044240b4200300791075000e11031071103822a2140058103c84080d0301556a1210416681d1029044641c1651a840708010890b0210a00300d5000a80b4100c40ca21028001180d5140d1041c00301500ca004003040c0000550340703000042800018000c410b00040c03000040c884c0c0081c805a01d440740703d9020812000b0300d54810111502007501c02c8443c1c40c400103408106900500c0803074801e0007080907200c107402c80d2000860 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 372552014 1250 372550764 372550793
    0x7051602041a0102070b030606090609220212091b1c021203071e030e0402070827030606030c0604140a03050601060503090607030e150601090f09050f060a030b041e 72
    0x14001c00c2e9491010000904040c1150400c003504030080c0144103440c1c03100426a9800d282c20340d10b82740e840ca040e400141428460b07011191180e02060740454259050303030080d10000c0310350646144142c0360104565240c43c4c50980c0d001912000010010252030300360403203030994510f10b00380f605246942e004103082003009440140f0a5000042003020804003003444142c418682803c1c80080c9400d5400400c0f5200030400b00f40700301d8001c2008401e100303c40d002c0301e440c0c54984504500b01c04100c2c400f1401d0484d60300c4080e2181c024200001c18904002c90401c01d036800c018400d510701414502a075001c6038040d1511a0800c1c448840400098402c00c01c0501034030b0300c3c0e140c4503100e142c07000510f4602480101010101428102c00c810082d0001905801c1d500c00890000041c2d6a03401c01214000110340c041122203000d520005001d410541c4414029204414842859a00c040a01418100511008100105d0100001c0c0441c104103821480d0404118030640004140c1d00c6002d214044072 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 372553264 1250 372552014 372552041
    0x30e130c08090706020d20070b0705010b28090906180302071514180427020306010b0c030327010609060e0709031709010207050a0312090b09090705160204 68
    0x140501c82c080c0750410030030000b042c040c401030503400c02c1050001d000c6080032030803e000b1310320381420f040080070500c0702c0300140000440e610303107441c89418658060913019203101d0207010b0701911440d0070b210740d0b201c80c0f510a01c03014034415920300c1d0600550040402e1002601c41598446083d540c03070386558558002c0c14083d80c0140700300d500f019403e001207101c003150f25051100c01911071107420104c406848035144403040161060036800007103006005a8200c040603015080303003040205005c1142003803114000d1f81150103070ba03201c1d0f80310a1644645240c0d00074682c000d100090000c4405807007100f00c010a0850110301c0f01f2184945401d5403400d400018995481e0f0704280150f0307a890369401d60142040c40c003205034500c0d54a1306000c880c250784040040880c00940c2d901d9603402008110000c0801412017001e60341d407400c100c540d42c0140a106000500c410f10300150344040c11041d01c11102005180c0d502c591260a030a83e1142d0040010b0a0902071150b21040903a650b4070078054202000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 372554514 1250 372553264 372553277
    0x10030c2a02191e03320d0201060819050304050f01090b04030f060b060a09350708010612051510081501030201020c01110a0b0703112b0203090a030e130c 67
    0x41c40391a4180d40d904581400c40c0c92243c40e000c0002c00d8502c240f04401c840154206981103a00c1480400c1169000745a954940b050080c1d84031181e50550000f41141c542d00c6c02e80e28140104040101800e44040f03000e083c80d0320a01c42840305290a0200480c000d0b814100008010741c2d0780464852074200b54000c2da1442000b41503003041c004140280351400d4011a6020724043c0d00d290040c10480150082c10b80c601460300c2c03804c151091204051040c10404021401e0340e90080c814599290241d01070505a54207040b00061a00c03c4070300c8440480ba80321002e4608400101088214290000c20104d604aa000b2000031044000d00042101040300a8140c2540d8110b00000e8504045114030604018540840050101020401c1090107070300040c0c442682c3c583c0c01044000e4400f4400d003c0e054500081c004400d003140e071000c01840000c1c01010746110f107041c1046030490100301c03203404a80c0c20014450f00068410312404e141c00760300030000c13000009a03900b11701c1120031021200000c130380d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 372555764 1250 372554514 372554519
    0xc0501050c0a1d01030f090627020d1b050d0605070e01090b0d1112090a03110105150906180703060302010e040e0309150706090b0610030c2a0219 64
    0x142801526400954403080d1494a40c0c4404020300c4144946081c07015452035108004680c1e100e500f000c4100c4c0d10a00c4107010205540c1800c90082917000800e01d03201c41c4144951032800e4452001e2096660024058604101d0b580c440c21500450381e018503041e074103104c0011442d5a43c00c101d08000360f0240c0000109850170420261480459161a43c107001a0840c100405800340c8100d682d4014980b0001c80d4805c801241100a80100342c41400a0319101042040602f00043c60400d140e001c0c0d5501e10b032501c0c000e2003844c02c0715815215074000b00a100f02c0c034030684c1441da91050300002e000d80b0380c2005080002010305088030a40e40c4000081e25070200b00195031f4040c0c07015481c0b402c03c40f8100800c40517110155900c0c461030003500c0c020040f502030400130b501a031003030302e00b5035402540c01e2058901600e80285a5001224a40c0c422021480f070381e825648203100e00a044807860301d0b03c500607924010a00c4030b051a00095404003180c0502c26030068076000104928a40041c102c07030006030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 372557014 1250 372555764 372555773
    0xc0b1e010b12060d0c09020901140c030c07060c1509031707020c0102101401060e0105130305010606201203091608010b040e030f030c030a0912080403080702070b04030602030a0e07060c 81
    0x2d010340400d106429a8100741c010400d034007010070031100401c00059417241104c00680d00410001101000f454002c41d01c8244900040300900c10840e0480940d400e0325182d104c10740301d580004001804181083c4191040f0494642c0b1070b0141c1406820702c02680c2410440b041c58403001141c4080c0182c00550110655580401180c0400120220706000f1031007405074032140440144501020010028540400c617405001212a9101481102c01500b85c490400134043d1440384103401c000390040c4116410220401e03044070300c00f1028006022102e084069405107500f0142c86140640681d040200159640b6003561005041d22000825514030810421040b01c0d00400d0080b40c541040140101c00700c901c4048a911803840200d0740c0d1241c44000d0715400805000344010321031805084409038043e04589032620680c4296100b403101d40c0c6041080741c45000a03c12042c0c0b00b041031200388006441c0d9000340d913106100c0348000a0548500700560701d01015030b0300940100b2441e481d03e80c10310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 372558264 1250 372557014 372557047
    0x2a0d06060216060c0803071b0b0103051b03060708071b0507080d141204170a08270a02222a05031909050a0c0605090405010e04030c0b1e010b 62
    0x480444211010592800102601800741c1000045c00346070700200140005005040a081c5030006c0c2d100101c04180300d01c0c1a07400b848080c00141d49612800c5074810a0701144a0011680d17000500035050a071070b03142042c0c9541801510328010b206ca02401080541240310402441d0340c058002441c80900e000c941c9410701110204510402040001c460312401d0000f040342c2d91040c8602c5603440a6543c1e00348480311110924030452002d800046011f0300c0c0746d0100400380110481702c1141d81c40040e4003080f1038160707120983c00100760448171401c405894880080c0440d601c3c0401c2200d10b0081c00c03600c0604607540000c441507020a0481c071008860300c200041802c44826003001d13447e609001500c0760522080080e2100b8543d2102041300c1000303401e1100300c074410740c442e46512907540c5401c0c001e841500002034442c0a43e07c0c00c800090403094000d0440e004540503216070001410760f480704030b55003000402082301c01ca03560070a0b40d1604241741142e03000348403151240b625400300f8007000d000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 372559514 1250 372558264 372558283
    0xc110d082b05100627150e030601031a09070e0a0209040b090a0501320907031b0201020a12110f0304021207081e0a0201020d03050a0b09090c04232a0d060602 69
    0x4260280240320040050340140ca042d14560541c540c0350142146088420140060304030340c25000302707800001040300300003c81000c1c2c00b40d850b42002d560754403201c13140d07105a0b0780701355401c1914040110300920710320340c01041c10540251000c2550980240420b0301c014007695403a9940c0c0d91140108807450300d060041d000c8441c010340e03904803c2a1307803034145d05051419840910407204000440c10007801395004424184000c000e651400904642c064004d421a01d10700011480758551507944445d03e2141035a03090130003044604012140104040c5500000c2041ba000310a0b041c101c12010004c024020080140314000c0c401e1000c1c0c201c0240461354280517040c6030764025141d250050382c010410a600288030302d0300180c0d40d42c0325089240648240b00400307030001403070010303c18031520118103502d000710b09032410f0004030098020f1000e80e4401c80c0d8500801c8a002d404905096a000c02401c080b521703101d41241e200c1c19008125030558010f0110400741ca550302c104006443d01802030902 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 372560764 1250 372559514 372559547
    0x902130902040b180d120339180305030301120c03051906060b04030506070e0604051e030708030906030403030f15060e18060d08030406090b070c110d082b051006 71
    0x1460006071b81c4807480300d407500030007a00345074a94140301c1c11001210304001c035a00f82c28071058185485500600000602d032220000000c240c00c00c044080103003600154226948a03004514681c81e00c2513019594907016011560300c940ba020000110340100004080744098402e86105004d042c070b0b00074126034880c0d1005c2c0041d08203000402c08035a0104006034400ca103814401004140c40b00002c2082c031a2f80c10050303003c40d002c04092184000c0c140c50050001b015001c071000d450311203992a990717003c0c00503515404207042001500003442078020382106880c0074000300311405c404000078445203a9400c6140025a02030b0040381c00e1400d109078222890321144803a60506001020840702a807000c00980b0281c0d000000c41c041003e6640041809a00500120302e1824100c1006140310309001041c1d520f080210030b8414540b030051085001c0d136901c0030615140c480d1107a4080800d940c0362090140c41d034002408142801303040d0040d103125050030301c49900018106400076007158018143d014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 372562014 1250 372560764 372560779
    0x90d0b190c0f0e010306030501020a050c1b1011010906020f0c0c0111071205070803040603050f070822051504030509011205010f03080906040b190e10090902130902040b18 75
    0x10001d40d08546030301c0b50880c081c80d00030440d99200d00140c0141c1070350350004045600c001409000e0590000c094138030350005400f41c82150003030510443c001d1009282d1141e11000c1051a20b010501800e901d0341c140b1802800400d000c1015150103003260002c020280078941c2c001981c4255160520400868000c24201100742040500000d6031704c00290081166101200700c050092200800c010b1006018103011640d4950f200c1000501038541a9a60a51989044c000c20021030003810903030700c1003201e41c0903100710380c805a07100d02c076110800405403407a0055000350110104038800c0240300d076009446041d81c5000400006041d02e4005482c8120549484010311881180b4000c2404a07500584003580728540c2000049907489564424010000c00160201070045806002c4038505460f44807110707403002d03003810310480c9160b503c00c0c08006443d41e0302c144050f083c15805498260010104440010344640301d5908070390064101c075003245000300e10110403101c0e10040c0000c0b0803060300c3c01c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 372563264 1250 372562014 372562031
    0x9180a200f03060f07030b010c060513020a050913060207030e0d05161e031202010b0d06060302040b09070509011d0d0302011a06040f140f0d0b09010b060310030204050c090d0b19 78
    0x40348102000c0c0c005d00415480c0ca4000c00160b100d0b10103018499003041c000c001c541003005603100b0141e00e20208a026820b403500020350b41c03402c0041184145400c000743c0d0010841b07642c4030f4000350301480c0200d081c4210085402c0103519075480c45020244900014a44641f00500715038000c141e550050001d08941601e1840c003081804400040340d074411644180d080003003000740d01500000e0100b9400144c060fa400091001c16003120b005c890017541c040282070141d00511034144006c0312002d0125004114088565104400610a00070001c402007000e20f61640024140d140d01d050503070050b91510038018921480e00501d2183d0303641180d9207441d281c5080e140d4a80345409100d0544403a24884508050307442d0005545071600d4018041c0840300c3c01483c200a059106940c03107e902d40c64851012030b030341084012a409480c560400440051460342080064680100010504135040c880c11030262944803410425a125004072803280c0b0f4034000070309040686001c0011610b06183d8403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 372564514 1250 372563264 372563281
    0x512040803071d030d08040606170a03140f1c0b0a090f0506030601030b0c0f0408010f0e060610200102070506090708061e04030305180703290609180a200f0306 70
    0x3002c0d0a1040d0a1000941c0c0c0c860800300b00410190303000100ad08604070b060880044041645442c240c4251107003030a40009a500103a00e006401c0c081c0714418080040304510401c61090001604800b20003081c0d40e42c0d5080412150444e590101c5181a142e10b10210300800901907035900042c1603001305800c0d0301d5900c0e1100520750207000403554190004505103500c41500032280588440030007030284a249000d603500408201c190318985001d0f00700811450b1500c4141c1246030300190ba42c0505845804e200da0020520101000300c95640c2005510300044050003014800d40389a8064042646000015400c1c03001c028454138030a00480c0155480c00503540d0000e030040d80501e40001e90755a070002009088810b240004040d102c1c1c1ca000104029501100c50380d26096642880c40c40814500300044948083c0d664641c444000300c0000da02c40024195204032910500454144522949801c0340d00148524518a1000e15810f40380e4241080c9207200480c1c04142c008200ba464460700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 372565764 1250 372564514 372564523
    0x1e061e060a030b1e010609030309060e03100b01030623030f0f1002070303060302060d0f0614030a060e070b070c0f120816030e06120f07050703080a0209010512040803071d03 76
    0x101070440c2040030609401070f04942e01c00d139810302d100000065850f4003000c0c01140481c4411000500d01580c00700d41c0c90320502d0100c000b544007800400c0c550501e2003884001d4071010a002d8100360f40c40b2000035001011341d07903aa007804250b140c84ca460b001110107140c1068448210b10109038025030f41c6000c2c00000061040c6400320000340142c03500e84074901100608043e0340060b52021000c1612000e0750003c1c0e00a030784100a24104120b016071700d1610140071303a11102419416082a0f00078404a0755603008503140790f2840d4251900c1584400d041c801c2500440026190100c40c0c072002d000a521540110015200100869402c4801961084094843c1d22a0f180075a02c40c201c000b010580152890821004018900e6031580c90110750b4000f90502200c104c0201066031010a10460041003180d401580503610b006460f982e0440100107540720b0110035040040400c00500742580c215021802944213016491742d900700582c1c01048040c00c0103168894448048501045580014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 372567014 1250 372565764 372565769
    0x6051305040503070f031d03010507051c1103010308120705030103150f1d10150323121309200307030b03030f070501051801050915091e061e060a 64
    0x44081195501c91520754194000d10344028092141d82e8018000c042d08102150b0b03050b2060b03443c91924114900415003601ca00b0f4482d00041001000840480300340507001c0000c00c0074010004c00e800c15003072941c0c65194001d0780255114680840c21030034213222121859013203081d52800b02c2c2954119281d2002d102c80751910940c5050381d464140e60100743c5604080100100c941d20f00e042e2a004842032900d070580001a007440e03c0c506034010312116182d280480070340e034101d400312207000c2d04421400c0c0e9003400c1d8a203142c02441140e04c00e004600a400042c0407004500c1c00c1d011516140c20b80070002e442c240090300301c014641c44000c0c103201d0030110980f984085245404501b108161001c41d0440c840c03115800f01e01d10000400909204054110900994680c5540c8150110f00080e403402c850041c8c43c3c2d1640d036000303024040202c1d2520f50a013034020000d0f000b030783c000e0602040d0041c03180030311035045400c0e508030004014090002410b00b081458030102c01590601d065400503440e0440c90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 372568264 1250 372567014 372567049
    0x17010b0703030b1818010908030f0405070f06051306020f0a020108060409151401050d0c03030e180a0f050a0605060d090303110703110c041a01081f1211040605 70
    0x10038500d0505200e504a81090303500a80a48545541009502e0b8503050480d91002e0b07080308211400d50a860521403071041c1070b000740d851821910b07800c012902240340500142c6061007454004030f40d92401024280040480d501d4031035490740e0b0419591002032040c1c2c0b049040d034100307a461108c2c0000c0881c81d031910950900e094201d55503804c001800818102801618400d030341fa0a80b20181040c0d808003205c1108841ca0740710b144c1c1d8130f90030000e00400d01080248144d5125200f080000d01942080f03850800080c440449440281142030000108442c00c00708540c0307540030680341e40c074640b180c642c001c560040c052081c5800c150101c0c00c140b00310021084069174590408040c9403003a032040c6002300070b03507600e25961700d0f031414014203040700103000c0c01c6c00c0d004d8190368105900c1d1501c910601101c0e8411083c20f043c60342c400560f91400001c12808608a81401840c250442640e03240040c1003203603600c44829041e410400f010344010305545014915009082c00255650b224603001100d60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 372569514 1250 372568264 372568267
    0x907051b030c0a060f050a09031d06040b0a050a181a030903040305010c0f0e09060a030f030e040203181509030f071a0106091e030c050607020103090b09060402030d17010b 75
    0x1403159040c41c0d03100b030a8841c6014011000c800c810869550041d051500c5105e2003401541c46038039008085502d0340d9030050201d400300d24049440962128114000d11008114500345a40c03022803000d1a403080001c0e00c0003400005220360305e15000038440d0311050000007001c9450f400c1c134189640c280451007800c0e0b09203001000061016000f0012900556400002800300031290340d03014080d110500e41c1400070031104800344040b42058043c0ba8840e0500900c020410b602c1c50b1070b44494030b001c0d010140d0401502d8000981207459600085000c0c14100380b084103100417a0a9203802c02150000654000360f408081c08001c101c00000e035601808040940d0340e4410040c5030001d00481c1900109074038106d081c0000504642240c540011900320042c040340100d00c0401040080441d030000401c040840482032143e03081c80c6010700780c814070606002501c40301c2619009010002100e041e101c6500c034001300030450405004141100c6004d0800030580b4407580f110352000d1405006d1078041c10f00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 372570764 1250 372569514 372569557
    0x8010819020a12030504181107140322080c01021504030f090e0406020d0c050c1c120f02030417120f0a0914060a11041a07060e0304180b090705 63
    0x110b145a000060201c090031001d003020030324001e4080e030441e02c1800c03403070300303c0894201c001100f5006a47c0c0003000c08610510303080c0725036034400d03044440905007003440c031061100c014041c0507862a00030031989143c2e1154070525005402d0715180d4030254643c115000115044040c202a0050507049585410b1000b021000000200c4007080c0301d038028020594008140014014560b00401c6100c0d500036081c400d10b00d4003c030982d4244079600b443c40079079001c9242c0c41100ca45925106594409910304000d0307038a01c1c0e03414071003030714182060342c1003165000003800100300c0241c9941c002c56000341c06180c182007140b901b2042400000b042016101449030028601c1501ca80c00301662952110700440000c00c1c2820031aa61901201c2d1101c2842c40e00540903111354038101036404a52011080c011500080245021650032540741103c3c2107440721507030307052184107101034400342c01903400c0102d006c1140c030203450035101420714007401001b2440a000704550b0100884500001441c2d00c24003040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 372572014 1250 372570764 372570769
    0x3140709061e14070b041e0510050c04080307030302040801060909150f0b0409050d08010b0c03090d0f020604030516050f09070c0c0503071d090c1c1104020706050a0c0801081902 78
    0x2103d0444241042001580e001088907100400780100d004a55014030060180501c105480e084407000e01554003400d058400c020302500099402000b01050034101503407805482d1641d04081800c501207600801d091043c40b0091042c5001840b1700c41c41441042000c0e03c80407142d940c4910601426a114400b01300c00c142e203038110081042d4094001c00010070341d42400764032622b6003006500040d82580c00003a1540c06401658681c400314006580741c03880301010420b81c6441c1e1001255445000000b20000d659004080e200541c0a072001e4240b424801170f21011411040d08418400c0240382c0c1322890300e85801400f01c1d4072a4031414041da00c61842c0c1400242044243e104941c54422200085451030040d10041d00c00700e003151214a041e11011440c43d1a010004101c070740010820b00c01d0b03008c803c80183d000813264020450150f6850100c004035090b80e0041409941a588540900c40340e440d00e0311650010700050320301209075506040465071501d60003203800013414881c0c102c500556 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 372573264 1250 372572014 372572027
    0xe060306010f0b370206090f0d0c050a020301150503060a15030303020708090909100c0201021207081305010e01022505070b1809010305012a090513020909040303140709061e 76
    0xc40c1c00d4581c9050502c0031300c81d5910503a108241c500050254101244842c00005400311074001d07494041d0074001d411b54011074425001071030903030b03641c4524003900b009610f0a2140ca00060080401100710302e061505041c648100600081000c030b282404088440c0f10300105042a00c0c1e142ca000740e56013145040440040c0034011815600013495014012200f200140704500c0ca02000400e02c40c0301c003003500c1a4200d000d000c8065402c4005200050501803180d02c050394401500704c81c00740e088503281c9409003144d00050506500c0da50002d071b01105071076401d0701c0c400c02015014402e0b03503500d51561019299486440765150602c008240a15110442409a10b0900d001303080403049607500c0c02c1c41400703810b55000e01050b0030314025808103580d01000c4070701e083d80b255895a13001c00f8509001d11900d49200d40c0b6203c242c590034000311000f5950b01045500440c0240d90204201d20914141c7c0030b4008040c0c1789605000350740004102d440d800400c0e0048042ea0150841031082e01030005443c1c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 372574514 1250 372573264 372573307
    0x60406091a03060709081f021303060930120216050a020f10140d06050d0f0606091802010c050f15151e041d070f0e060306010f0b 57
    0x3560500c14120340707850704442000c028040c22001c07038501c0d40303a030744007501c500909010781d5106810100007000c0301c600703802010b0b20301c0016540052038103115107141c001482644d00105c8003d0703165102e000901101d9002a4080043c0100f041103030035019648201a48015229005002001c00d02c503100d1003880c1c1c1600c0640d0075850405007810342600d08281c50301100c4104911540e0040c0380e0070403505080c3c0060481800035218508504036150000d522030700801c9142c90640d480b81400702d5262504501040351502c142c000904100c01032403c01d05907041e0b501701c030915614000c4070141c500c00069040b0882502800c29080409150070700324203000818448584600c20b2000003d03803030075001e10780c500c103150390702402c1281e91241003040030001c01c500005100501c130700d00000861400d40e00030038200142c0d0f01c6d91803009451056181c280a001d0b07000000b0416030550402013522900e460551107941200a0030445d03040203500311401e00c0c903004018140e04007007210030180340c0682500302d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 372575764 1250 372574514 372574529
    0x2120303010f05010207080a03020303040b0406201801030c1b0311030318070b120c0c01022107020d020105010b0703051c02031003020a0603020a080c0a26090c010c03020304030b060406 81
    0x940750384a501184444050703104603401480b54a0703001070911808602450356561641c040d40c91521151103800c02120041c2059441c0c50307851082c200c00c1c4028a002c12044030025a401e500c4c4d8603011280603200506803000c038145418407143d512601e51002040c4e0041c00b480110507130b220a64101154219910180d0882a01c00041445109895910509101c450040031501400c0d26518203228a00640d2200c0020142d1080403400708003003c405004001c0342c840005040244911034514000f0505440d04441d844034418018007960600100001003010300080c0103552421303041c3c2145104080b0040c0821502003405680700001030300a29014001c0201036481c0d0074094a455076540c0c0d00c0c4007ca100722030044001a06a0007070083d00e0f0910120348580119507210072840d42641e0040c4105000c0090001c070480760b441080107165240741e4104041501c82c80c080b400c81d45440800080d45051080c0851548002540001182e0503603a0041c581e2a064454001180160000303401030710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 372577014 1250 372575764 372575767
    0xb0a0e0c04151a0f0301060c080d0c0c02090604020c0604021504081506040c080c16020a180504231e01140c030916060f1404051908150c03060d021203 66
    0x242c01d0701c540720342d04050f00d418010300c140000800150795514410f42080e207500030014401041101e01900d000e0110900070405646051540c2d203501d01110801417044001c50421003600065003002c80c90594028800c0d58110702e03100d0498016941d036107005000074420344843c40c0c46605146600c0940d00200200c03800c072110022115030707032445030714122402c5c0d01030761804d9124007806100d01c00c02c50003812808540c914000000810060040600c44141d81025200ca000103030540010718036510840745c4080001d0707505051905aa0308221003c54105c0b4111611031411010f50110b10241007120611200c100620f407400c0c003502404040f035507102020b9100e402c202c0100b500b44010b42c031680c0748100361740003c25550f402512040d898000e03000015042006400300c0c5004080c104e24010085069505280e0703600001030314903202020070b041600354400d04200024082003108000b151460401e412898200c0c907028071400b004003030900c14840011280305645074110407d035041070702800d49 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 372578264 1250 372577014 372577031
    0x6050702030c010510060906081027060e161d22050a0615030c0216060e01090801020a210f09080310080307120e03030f12010609060c0b0a0e0c04 64
    0x40d46a400040d0450b00c50750074080010400c45108034824180c1d641500d40d1601c1c00d0501808503606400101005c1c680f00580d10003060301c0b4640c40542045482420041c15640e101e2a00e82090350300d00d5110ba0110030b03402c41440003020141004640030b01182c540f203030545000b16100c20340d1402c3c16039002c0d00704180d15681010201c080999041d07001e4041c3c000c0c40152107007440b41c0b08550031031080307440b000c9603030200a0106102e03411031808000c6510484031110010800020800ba00d5800340c801700381403a40d41c040d956044400c410040001070021810140100000703480d48210003a0200c03405910032401001c02e0456100311740b00d2a00140c1000911010302d0400040e81c02581c6506455604410006d001e83e0300108407200143d000300c0d080c4c420100d094065668411403a6032a9042c00300340842d01009005101410f100030b005030880289500d0040050304840060b0016810401820480000320300402030703403074120440c020b001650380202d54286d0305008002da01142d010381004401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 372579514 1250 372578264 372578267
    0x271c1e0816050705040b1002100e032106030f0724120f050901180201050f0a09150507031407110d081303050703060b0324070203130305060a110c03041a0403060507 72
    0x40401d0f07400c02d42e006c0041d0b028100800c1250b03440c12612100580c01141800150000c0b508032440300d841000444e410030240105240141c000b0740b58810000f131007441008083e14041040f6540f81d9260405068203506090751100008190170202d0380f103074a240144041c0d103105011a0f2004d40528400f00a0055080381d1800030b401c040d15007840300c5d800c055401341114000713921402c100ba41619000d00d40742c10780b80f40c0c10558000c410300700248004c004d070025058082c01010030274040c80d6030703230130740d0f41e08241c5001380c03401b811581e04c404511030620511000501d00c0300c00075012101202c1d48061100140b07442002840f40a100c0421503030355040c00400c01000003070410941c0d105810130301c2643c10400605641d08035000c42402100481903580e0901d6128000d4207420050520680f4909403a5080e10308212000d50700483d26603111004000c0e20034094070501c0b18210305082e0b914078082c4030444041d500e0055000b080440c2c541483c10003a810301d40000c980066921000a009601d8003120 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 372580764 1250 372579514 372579523
    0x26040e0f060a060816140d0e030a0801230910180609060b070b01050603040c030f080a110a02010801090e01060f06030209031b030607080c271c1e081605 67
    0x100c941c042d1001620119425000b00d0342c141c07107400d249a10f107680a8001004484110380c1c0ca807282c42100742000394107441d00990003007c55100811000310350310048010005d0030440c0588c807920310190041075040c1c84018124100e0140c0c1c100321550003d90f00c40201d1034044000e00d03440445410083c046a0a03d01d02c690040c00c1101d410082c1000015075a8006a880d8411614010684070880005000520301200a160018040c26011605544a5440c1200c41b007a000d02516141d07808180303950a10307402150050a15000c40103040d1103102a0f00207010094103002c2c8403941c940310140008881000d5100b280200510030f148a40c40c0c1e604c00d4094000d51096443c03d00034060909000c481030302c801c40b400c041401c094000d1080d46d695071003c0390a214041c250070000f00c820045110070100c072201c0e9000e83d44603a01e11142c41c20114040100704c81c46160450000b8050760501c4c0042080508041c42400210001c501c0001e0300f460f024ce02403090040c4035201c903130211704c901e061050004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 372582014 1250 372580764 372580771
    0x5030913020919090e0c0907030e0f010c090e0c0a0c060c0c0f0b01030519050a0b0411131a031f110405090a0501060914030604030e0a081e0114010326040e0f 69
    0x40082c0045600700b540c88450303400c0c503150000002c4008c40c0c0c019100e6131001c906142481d0603070780d0600005040500f035500310048400001c2e002203042c0502c0443c0002d280c0c014000043c1940752a64086000d0310010040c00081c0450395184800504a4000c7c0030b202c609503807080502c2040e840510701450741220a000071740d00d03441920fa41460b200b255000c620440340e00030000b030222400940d110040010010800c4034030703100c4004c0390481512517540c6c440c04128200c6021500c2603401c0c4548101351600c0511600c240d0000034120445000300d642c101140024a00111342d1000000c0c1030ba40d0f61080c1d078841900070000c0707001c00c144090182c0c4124180e8215640e041c1903c3d0b91030265450081c03290104e141c0c0b5812150114000902501d03c902502e440a03140d010010740c0d4000550138506403000c080c207034480110190a4101c028810450400c010a0031018954195285c01d610000e1402d2003d6000c0c00080c01045440d101c40c044c2c80050544c0d05d44501c55103000ca41302ca0640b401034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 372583264 1250 372582014 372582029
    0xa2a060c0c06080f04120e040e01020c0610050607020405040501060510050a0314040305030c0a03060306020c0c04150b0f1c0606030914070e0601050a03021608031e010305030913020919 81
    0x21a0085a018450b04034180a054130114031507181d01c1d5500da00c480300f82458152001c0c8961441c00b81035544560082111120f28440016294032041d0b00082c10000014080ac4d05c013420180c1c1444950344410070f9030407864040e900040d03156030318070b0142e0040225400c003a40c4407480c41c58250038564040010804d40c00642d07014007442080d01c0716244000300684d00200801e01c28000070300c080a0f040007a000000803403a0104010381c4d01e440d100102e030300c441d111010311340100318141c40c81e003403500812404129600900707013a5454030025580300d0081c40d8047c20b03901c400054007040d0f110344180013104500d010301c08104444d43c55030090008d010044040b00d0b5a03d03a80d80190302000f0208840c030484031a00f47c0c42405650340001110140c0c807203030030f00050690a0080b0203000300300d0385129810501c900130007560790a014502070b000420801240c200000003000500c00580c000c0141e03074a00c4425125460010001e07408500a40603411007107410845402010140d18002030f40001241c034003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 372584514 1250 372583264 372583283
    0x7092c10030212011a0f010e0909030c0706050c0c010309050a0c0e0f0c16020f0a091b18080c061803060703060303110102040e150402120703020310060504080a2a060c 73
    0x50040142c01d80b0500d0b83c007105c0502d00034080010070300b454881da1151039814076203105c0c100b2140b4006207a81001381c480416592010a50650b500c0e0100180005459503003401130800c050384080c9555910820101810541c440100c4010444200702d0900340652140078184801d03160002e200658500700c6000d184007a0301408203038001802e0f000c49a104c102005200c2d0042141e03024003110032004000d15400c0010410700060b00d451a204201510310050f200c100caa809002c2c0040900120045020a0317160a41040114400000d100d05a85006030380b17041e1110b810424112003c182c4190254042c0601c0341040a40d541c554400410f80744a92140c952140200e0005402c030b00842c00703103402c0c2e403019002107900c05082503e4200024070051001d8a4402c40e012405041d907000d65215012036004414804a000110517080c050065403a0031410240740040d0742c1d654900c1c454002d0161980389541464031009410480e41c17a60542c0c000c9803c0e5540d8040080500510030b42c2511103038607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 372585764 1250 372584514 372584539
    0x111e01050f0f06040c020708010e0304090608032802011e02031609080c01030b030307050a0b01031203111602030a02030f0304031104060503070314030408061e09010507092c100302 79
    0x4418508074080c6002c0505480c0d641c1d0344105010003400f01480740e105510070642c000480c01800d0140c0122450484095510360b843c200524090317651542040581c0c1e00140412154000405c1108803400748151007031120781c20242099004015030100e4070f6070103810806030007565219400a6000f050000240070b403040c14510b080b00c040f100e42c00382c038000303400882c0041c0956220b0b411080130003c0040c250b03440d00f03905550f010b1421014500441e1750600040c01001480b00101c400d25000500c1c2c202070104609010042030316208043c40e4904216001c04100300790340b02040511165a400b47c21196494a24032180783d07203810a200844000980720966042d9007824014007049410150081201900716550f1782e03c2c811204001041c43d100c01c1c0300000349200208202c2d400340d00010b04e4003070201100d6485480c860402070421415a0600c0c092000590b48442c03e0811202d060321a1502141d6010901c0c0c0015080001141d801441c08180509070301d40060110850b0706c2100d4005900c2c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 372587014 1250 372585764 372585781
    0x90f01080c01030b061801052701021005040503091005070b010b040f06030b03030702012003030103030305061305040b0118090b01150201180f1e020607051609060b0f0a111e0105 78
    0x10314001c031064001d42c0510441600819074a0f49168008050425030b003050200b516040340120350302040942410b4270140c038105540c05101d2081075280382502440307240340584030140e4901c50300510600581c0100c4e0102e000c1440360080d500040d0740108618040d50313451000e0700403078106010300c02d107481142a000480300d00900c00c10b11110070140145060000540066840c1c480411440300046c1d04d400c00141c0046081c00103502851007520700044c1360400e1800d00070010890010010000e103484148030205606030907490441e1682410840600c1c0e014604070050300000ca00100201c0e079840022407484214000d088141e400c81c3c1c0200008042c0c40e140d103009011124015181482c035016802c04185a15a09101d213070300705107210f0b0400019404207940f503020102c156400c0c0c00c0600550700307181c805035001d401401c2c43e0106200302405d00031801c0651040098078000581c001500d030303100502404440d204e80c020f65040c0e42c01e6000400b0107000015070700071840125403a0500142950 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 372588264 1250 372587014 372587021
    0x605030d0801090228111002070f020d050f0d031b05040608070c110d0312050a0615030b0f04090302030a0809010c09090e0f0709020903060c0910180302090f01080c0103 74
    0x1255141c0c0c41991a1040c2480254001e034890399480170380e003600c800e11401c00200e40d08800000d9490040700c8540d0310b4018204940f54041c19a000c0c010000c810208446a200c0140c190301114043c00d040194a0134926000010007103242c64081d40c0d2407040250380640c01050304524442038210720200c1a1000c886911a03402114045801d8034049500341d8428000091800d2080c901d52814003110800101c80b003042100c2100081d07145102d060f0640600d0103a140c02017444082400031070300f010900030300c5000c440407a00400d5a9410800701c23a5981c1e8901040c98680580200030304075050038002d40b20350005c00e0940100c0c0e50000410304803a0705128462103040703203903130781c6c0d512030f0901091201428520301d410030148508200e5012041e014002c000042502c0c0c8001079584c000300040c5030030700c14020481c1c2220101807042c41c00d15220030600042d1003417146400220500c0c107549403043d03020b5641010390003183c0f500800640c00c00200703010341a2400c481c00c40d21030159040044058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 372589514 1250 372588264 372588283
    0xc1302120f2e1401030902090c0a0e151b03030f07050c0f060f10050d0803040f080d0e010203060f0301051501200604080403021f091208070206070501060801060503 72
    0x22100080028820400d4440e00364100900c2054046038118203210030100041a03481002c205a03101410800311815002c4805092821700b8280b00003030704e640014010050041c03400c0110003000410a002a2040c075100e0580840100992188001d0f200c1205040d00140c4400e44212504001c040c500a00041901d200341203181814134140e40e50881203170582c1004451031a50711940d58a40d44407001801400e2090041d00106641e5180140c82e107584014664819070084d00605164400b048110302280d034000d03044003002812000c03a00c0e141c40e1521507410164855864000d44c04005c070810340086005120886200d40c001078080201401c0b039806851403019104000031400880d4010401d0440c500340b10702405072030b0306448160740d0404200b00c0e421200381d10000b8040c07045107003200303005903d100c10080340722150b001014050000c980030300803c031030b4031207402ca000100311820045454496002d01519214811403604901900960207504429400c248001c651801d00140c840c0c072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 372590764 1250 372589514 372589537
    0xd0e010c11060f07060e01050f0601050a0905040b03070e0106090302132306030708011e061703070305070204020f040618060f0c140a020d03020d020d1407020415030c080c1302 77
    0x20800728900401895600c000c1060300300880600240f40880c42d41e02c0b0700c0d8406446000003140b6882c21031a0420401d070300074406030600c00144200d0f5409640b12010109070340003940c00107420f110032170000f490320000b0b5101203407054a8000119001d0391007200681241e200b80c802e040e2110a081d019002e4a81030703042c0140c10848081400419083c2d860900d403c00c1024042d0750855032600d215070300b03581c01e0520b840d0300100146003442d8102081c0c8036030030003030001c0c0c03124542100700403a0282d2644621203026040010104451040d0b40e1594100d448042c3c1c002c847c84d669135030790840a004960809983d80100d151102e0000d43d05008004c0c0c0240e09110b0340d0b580d142e23000e0b030380d4940ea419503500c496542c882c0702e01c0e0101e0300180c64145400104501940040054000e034440003032404014000c103d00b0040c15401c3c1c80754403c400000c1d626039650482d004220700306015a06900c50314668000760890303440c07a000050030382c000700d2141105007041da1015000d100c50890001644a100260340b03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 372592014 1250 372590764 372590783
    0x10060515030709030503130e060402070309170115170c0f01022d070602031b19060c2102040603060806060906040509071e05010f0c050d030203090c0a080d0e010c 71
    0x31040340d2214020340d4031049074284811041e0700e80c2c0301e49155400c103405240c103101d0444010b102004c070780444580d100c8401c503025880d00f0300f250b8004010052611444c00c1802c4604103603041c2c1402904000d05840842c107002d600301d0354401117500703038030241200080036004100800001d0300304401d0b80d034941792061f001040c078080380b100507a180c1c501c080092952010707800550700300d200b42400072500a12042d0b00035a11600c0c1e00b078400d07140b03003850104241668010003401c1401c24420607050a0f140e00440005803000c061b181c03e507a03810481e601e0280003240c905410201c01410b41c06002901c495543c00c0085070703211440d450ba0b4190030f4494503402100a0009000c40c40d00740c02640d48000300b2000c0e100c2c0141c0c0c1d2030781032206050f0386c1805e10101140e08418040da50b031021944444103034925021403c0000c0380c0f1841c0e10380803080c07030003030805400000162154200b0440f9110714003020384003e000300d5503084441d0f265806600a60001800303688002420342c414400c0c0c800aa40112045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 372593264 1250 372592014 372592039
    0xf050d0b090f01020d0b090a0c140f12040606140607031e0c061d0106080114130c0b0301030f0b0c1606093206070302040605160501110f03040c24030506060c0d020f100605 75
    0x5003540e81000703a80307580a0070100031305115503011100c4cea0140d84200c20100703443e41000b8034942c07050208450240544000d20904c1c003c280d0006140c0c01000303081100d1945400c0803e811a8242ca4074280030f407899082205040031149548c00000b003000c4060000c1081a88071071100d400d0b41d050810400240a80f40085522091002a4a0200ca20a0b01c80382140c139551000c454858009074416206444001542d90620404000c400c0d41700002941d0103152108c0741b454104008110715010b0712059032070002c0000c2180c21808000e01803511101e403e40013017000160341502c2c51803c000c910394012100400c100324083d000fa14192442c580700c06041019040510041c0d0f000211b080c1c82a41d220015400603240300030003451494000d0001030750340e203460308041000d041caa0f8800d0000120b008800200945900c0c0c000e0310340307941440c2c04039003511140e00141e224010410018001d000c2c56212400c16500014044900c501c65000c0d118804280f006c0c00e81226142d104071a040041500031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 372594514 1250 372593264 372593297
    0x2040608060909160308210108240c030a020904140c0d060f03030c15110403080705160e0a090f120314011a030411040e0d020708070f050d0b090f01020d0b090a0c 71
    0x35040503071f08450524841c4500b58403040c010b0348280e20100c032030b80011030319000401c1c45030154a40001500c02c201d5070750030b0044543c0842e210040240303445a501046080469607550003100781e90f02c1c250350504a80c00c02a4144441d907215015540e0b015141800001d03503e00e00b00072035003c41b41c142d1104103000b100d58507140c3e40346040400c0e1b0311415035202001800c00322010081e101560003200441d845c4c01882c40d00303510341202400f0114481d45050307000c20820841e140d1056105039400c501040040701481c0c241034002ca8120010008055451440d08140d89a80180b01204020340e54094a980e2103240b800c01d40360300c0f09452251541000001c000c03418008400f00d41e9500540005000700b030008000e4140591086201c0040e041584100300c004810424200904141c5606044061411000540e0307401040303001040040b0786e00004440440070310031115030b10f018238000c2d07540350704411045005061311814244070388001000f1418074221740c0301d142082546500d641d4002d0851092 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 372595764 1250 372594514 372594517
    0x1206130605270a1202010212043815010804152706050907170309040903030b06030a0606030501140f010c080d0903080612010c09030308100902040608060909160308 72
    0x40300444154030001d03141d03000808402c000e840d220300c4024001424491800b9101c034119800f00d40116801072010305041000000f60640295006080c041840345141908014000c40e8032050350684811440403d20300110306128415082c01c4554400c025965005540100d8140d8010b800075000c000502d01403d01903102003212a55034007284c0d00b6200e04071035a00d070f0034811a0121045504c43c0d045c002040410400e480141154101d013840d0075021494007030b0340c2d009201c0c10f42c1c030590300c810354039003458000c2c2e0100a04a001505465491030301e01c5549014ac2034031b205981c002031134200005000b25417844540b6a51300001e0441041010100044074407244141c81074a503030700c003001410072088451140c1001140f00c4d03240e08640340b07416000c01c1100c94843e000e283c0241d04107001b604880741e203c3c25000076070b42d240c1044041a142c1c8a5070854905080d081441e21a00c002000300d40f0940160300741d8400c0008440c081803a5840100054a41021800140708000d90000a0000039072120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 372597014 1250 372595764 372595771
    0x6040e0a030813020319110103060512032205030307080a020c010c170a090b0313051203280b03011509051308040611030d050a050405060a060b09120109021801051206130605 76
    0x400703c40051454207155207243c121180f0803034083d1f154015074000d55805000e5200103102c01c0351001c0b1600402c041054803845903403219011402401500c1d02807405444080c17014000140c2140e49076001031401c4489030380b2443c0a44058420444030152075132040302d400040b158400801440350303c2060103284581c010803074035010301074140c40c045913125001000c1e52099409400600380070941d0b042c410705000d80c0c0e00034074441703010800070040c010000c48111981101030011002158030510325450091402c040d0300c40d8554280120f070015040c0c000c0c00081076808280c010806a01d80b181d85410106400200612100d000e01c010840706005480609000d00d000c0280e9141040c8034045c0000c4074001c96122441c943d0704c506000c1808000c1040382d0f032100b0025001c0000d5828150707642c40130300407850100d122b1200c001c1e1000c003048003900907038031196020f07089411420394403000403090320003401540c2c01029a804009040200040c12501806100465031a02649903c50b0b0000d483c008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 372598264 1250 372597014 372597019
    0xa0b010f120b0d03090906080307050c0d0f0c0909030e01080601090e0627010e0c0f030103170f0c0d0f09030309090906110406030501150f0215070201111206040e0a03081302 76
    0x114003a10160301d511018000803031285c1d40d410310560500c5d40841c2101d81d642c0010301194014400c260020340c00103410030b01d14004550203901a0b506203092406030102810003420303121203500c00940c08002c0e402c042505442511950010f079841e400464500300100c483c103000400b6520104036002d408200207070042809005081e142c607040005041100c00034692036031400361240104a8004503540c0d1540000300404031918280381507403100e15902042c000a03214032301106e9006145140c500c00c450403003504009103030f2180031000c0116290184450400c020448410858a0042c0b081402c00140c03941500c0d510344a0341041e007100c00428801794101c8995a561115030140c08100c00504000c19070303a540807940358140310750042021111010390080c0088101c800800079000304a20301c070212209400d107219070b10300104030301403e10000b4490040b01d0000b04081e82043c08a1034520441c0152402d0012003c000d54190340e03250523880c003900240308280412000c9841c1140001d509000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 372599514 1250 372598264 372598271
    0x230714060a0309080f07030e10020601030f060213030f1214031608060406031416120f080c010b04020310050a0e1e07090503010c0c060e210a05161a0a0b010f12 70
    0xd10b90030368099030003800203801051509232014000e2030a04070304d1416040342d01c05441d441d455030f61104407502022000400e56500480c14164140840c50481d006541010301c0070241d25507803c00340011041490007000207690303618120b48902e481c004490203069400c042c03815480c0c3d01901164089009001640d0150710740c040007000c2121640a000070700181c40280031402400d0000c0e00d901ca280b580440e44000b040300701c1e03c2c046203952007000b403645d80201c041655400b43d142c3c901e0041000d2034600c0d81c001d01c0882030024402c01c80c0250300542d003041e0f8000040e80d40342e50002c034000d503044501d5120b140e2003030120149481c80c8098079421a0700b13401d0030b00d2401c0d05c1d200081d003911100f0800d440062004d5800ea400d01502d80558144403403654042d00340080c206420660b002c5281c41d00740c0400c0c0f40042c01440807480380044501c020a408240078601c515464540950400880358081c0801c5800100b030b40402288a001c14900050b142c0b051500100b6500340c480707680c1b601140c1e280507074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 372600764 1250 372599514 372599527
    0x10e03030d0213080c1f030f0614040608030324130e160b2d070b0412030b0303160b04020402250c08011521230714060a030908 56
    0x1010409010064074214001d030302d07849940c240884040160740a8400303503221107030100c0305440310200c4581c6141a010304402106100105030040d02d5151120740b80b80b841c0c0032001a50000b01110301440400c210f03000d002c03a5a0340c92245642e0300003941c0640b040c20041c0550300c42c40c07805807004d080b03822000e401c44555054a841d0070044988048411303001e600b0520640c01623442d140a644040c041281d00107082400f0a00510004040034901011119000c400291802f03c041c0544610b140d01200c0c0045a1800740b8058203200d4030015040080b0342000b02e1080b085ca404000c0d1010700d001034602c2c10440003941c80e014a59980a48181d0300142e0030031445080c040550401b1500390740c1c548022b05400d04514203220400580c3e0b01a8807940d14040c1d85003411400184002c084a5041e000003e00d141c2c50300d021000203240a0004040101c4072092140c0c0d0f030650100b0480340d41402c0191042e0350782e605040340d01c040e07100102c0d6070f12035000c1020b040164000da10482d00035000301c0e80350741002c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 372602014 1250 372600764 372600769
    0x1031e3008150f04021e0a02010204060215010b2b150305100e0312060112050112050c1e221b03060902120604051906120203160b071e05030703030204030b18030a030902010e 76
    0x51084005131f0050350002018000700d40c0401118401c880362801000c0c5542c540075503408540100320340f0504072461600c0c241c101200d0080031840106c5062400c20100315104598075880c20544400c549500440f51300c5071600d000c40c07182000d203000f0320024502d094260810260618801807010341481422816010f14080340d101d618080c018004110820030b00780d0601c5031400307540b44213051082894100d452842c550b84080441c2d00501910f00300501c0b0048641100301200721205a420986824405099007001c40070004840c0b00030b80b8100289511041e07160164440d8031440d010000c0980301258a9061a6001030f9002154070404805c03041e000c4041000d0700c200790300c01640441400a1881940740600c6a034099911150790034840c0d074a0005002600e018011002c0c0c09802d0034038240c8007019070700d00440181c541c8202503c1c1e45029a2802a0081d0453302003076800c10f40d10301c000361190f0350480b000035102e90782c200114100208120200c01820b08040124100081d01048441c1c3d41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 372603264 1250 372602014 372602017
    0x60507081c020a17090c040b12011401061b0b0c031e09010e0c1219020a0305030c01200a0c02040b060d060e0a1401031e3008150f04021e 60
    0x80380003190150b41c2e42c5450b84000c010f030405082ca4030000d81306005100307205400154010071103100b0703200402c40d049010002503100301d40c0040400e0030f500704618441098801c8030b0b4a07068400300e4942d0ba202c072038403030110842d61480b02802000c1c1003400b400329951208000c05150b2040e5520a01c828952a0b525100c042d6601521750300b03c0360b0b450b01d0030b010031884103024108140c0410385e100c10031034030f811681035a905080104000c400010300c02001c00e41d100c0c3c2151a000c1d5810004580d41d80c000050418001c041100ca03241d44040c2449500d9402c0d18110304a800043c01540c4205007072180360200801000003082e1154850810815150218260b000e201b008100540d40c2003854903004115a003606c45030003809180440c0e4a0042c000541440400101c0588803c8003030000841483e03c4c0401a51b039210300402c5080004084a942e1090804940c8034200b650b900310050301d500f01d05403c0035000c020381c02c0d0701420b25074200b052400c05a016042001a0142500e105107208104a41c01d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 372604514 1250 372603264 372603307
    0x40b070b0a1d0a0210050f03041a011703031807050409080d140402090103060203270303041b180f060504060f090b0f060702090a1d0d120c0906050708 66
    0xc0c812080801c14021010302c12240c0840a0544510920301c468844949642032403d009205408040882c80094880c500b41e41004400c01903495490070325082c20001e6002c0300e800400380308044000070400c1400150701d1365490b080c2c0310066040d52140d4030980b01041c03070040503088610460000046965840c001d890405000f009003559800c858651007060300d040c0c2c4003555240400700240401038503072081d00c80c110794200c40d0050b103980742c1c40c80d0345200040a03810010202c2003004440e580240110055000398800c54071003510480300245140702c12210303c218001581c03580444c40b003000c1d5a40043c1000d45c10b1040004041c0d444d800080c0840f021604000e01c4c19145460603c03d010640c8079400c407400003181c210007140a0440000d005200300300c070003805000c48030003059500100d078110075807006106100746104c01d171402045d0343d102072212050380099010320581c0000c59140c070540d100500d050380c540071514103112080d00c3c0d0745d000b900200c41c00002000700600080d06018440725 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 372605764 1250 372604514 372604523
    0x3061127121209011e0915140703080118060f0b0c0f011103070207080712200d2109360903050a0809010b0901090f020c0a05060403021903050d050a02040b07 69
    0x1154a61070000415170091526180002903000d0a40d05010b80c00042e0f50b0101ca003c0324440064095450084030001e28000200410304008030f940320405801c101020b0594502d88058503c030b8580e03001103030941e030042c070504403405140c07201481500703148002001c031041d010041b00c4245499140803400c5400c3c86502d00011140070052086455050003801c00509124000f00701c1103003407140c2d08070400741d032903c010b205420b0503c0d061440c07051600a84c03100100200540d00003141820701007510703611618003243d04904289203040140c004c04520060316030300101c0000602c1404003203001000401400c07444100c0c0e410602c20503030001e0048042441c400d6841c0c0e610744083c20005441d01c000908100496410100030344078640312160980c1c111110560301041d02c3d500303100120000d20442c1d5500c0d0302402003210843c148a0002002d0f401144a5822038000c50003e01c0c136806404062036006001550401103141340d0300643e08020342103100d1200040c81c065840c3d804085c9a0710404040340c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 372607014 1250 372605764 372605767
    0x71d0a0e0618010305061f0506130614040608400b070305130204150510091a030c07030c020114030108010e070b030c0a0809031e04030611271212 64
    0xd900e00b00318500d11407000241c03491074200e505541d01c480d100d02c4002c10100da2490384140c480700042820030048001c00c4080c00c40ca681d000703506903880d940d450f58000c41300446d0f20282c402494002e000d0480c0e08550b1555504201a180c8803440300280d580c85031606000c803408104140f80b000c50190003251a955103c0a8501c94528540250041c0d00148520141441d200805c110043c5e64107101d5040d6504480002e0041172800d01c10440040c80c0e0405074003c070001e0318103510150003200581c00e9a03900c011944035541b421042e445070f4801269404580c00040c404540024002c464110f01e051050409400c120f01c080e1101341c41c1d8100341d220444607074413407044003001103041c000301707010b48030b2140b50300d01d5032a10a944078494480c881041c400c01500c0c000050110380c0074800d4814500a0030891424086407a0343c88213160058041503a84a1610038001035082255089951411400780d00c0240081041c1000030482c44041c0030b83e420031700c12020030000d14400c0c403c03e070344c025040300c406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 372608264 1250 372607014 372607021
    0xf210803091c020d210608010c03020706060f141c020603041101080a09020307180b130c0206010603050415090201170c04090606050906040b0a090803070305040e070c0209071d0a0e 79
    0x10304102d22040c803000d540001d403010841c00d030b01c0b240d2400c00300403003034001c2c801010514800000340f0241d803049000c3c1d464609000341203581a0001d0114500850003400402e850303c1e4022081c001c00d205080041c11164140086401c00000c4080d100c4507807280e4103004047c0380c01081d040d61044034121600d0303030388010200031580c008145940211001c03808000b15405580400e1380e0380307058008d070a1401d2002000319681e6070311303410100c1d2410001c2c0c9288c840d2130100340007801030583d003510340c409801890004145240f0a20449203c1c4d40c0086040a5100c500c282201c01084050010b904022108960405620078004070754007900c01007803401c0c1d442e881e010000c4100c5116411040801008000310002980c0302001d50b419100d1070740a540c0da98218500540306050580e000441d1400041240703001d26420001030022601c2d0709510369055500c07490300711003024035020029889611617011032240c61007600500000c03519150100c580740180c1c000903415100583c0202403061644081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 372609514 1250 372608264 372608293
    0x3050903190210060b211902030c1b0706110f0c01140c060f04060605030102040303050f0a0c0c06050c150426090414010503010e0102070c23040501030b0603010507090f21080309 78
    0x1000714006e10350b10001c81c9403c4c124134505840e0704011448485039008000701d2000060710007150f6019400000040b014a8130f0b503003907034550780389200d1304d000302d40d203160260306c2d0003004245d60340400d03207100181c101062a00c1c01520400d030f48144d285031548080c841c6110b02c50302005214011049800c15000d6480c01340703048419984d15410141c081e074014482040026004020759a18003040a6030503111107800304111201e102c510310203808440d504100140b803a4014005190800101003568200a1190701407072002c481650018a140c0c4950039205114031291038030365056141d491058503040d441000101a60101070305400c0030941107004020501d4244580034405000a0003941440940d403903550442c1c0c01031203007100d00220148000841480030a80c01e9030514010000c11040d40c50f410b03c508032200845e5818000e41c600b01c049001c4e01d0091001d141101d0301e010a0342c5420341002030f46d4000642c69484400d5044501c0103400008202402551044e0010703030003030100ca02982d05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 372610764 1250 372609514 372609547
    0x1015020619110a1101020705060f10050a050d06200a030e010e0c0f090c0403230c030a020a091e1802180c0a08150d03110d03050903190210060b 63
    0x4070624000d10b8000800c4030380808006039403026215007004120700154070301090181c4240c8a006159014140130864207851840d000c1e40900b02007068188101e40750001d01802040601031658085004003405001440f039400121400d003032030350903000540c240341ca20801a040503801c1d401003a121458910107920034030908401007039290082090700c00660100d40100d483c0c042d954040c20041e400990a55060421500296440045041c0d4581000c1c0d22030590015a8240d03291400340c5410360b842da04c0c002400e004440d070004c0c95900e0852500c04d4200007000c14051103100d485d051140004241a94804e03005050f101da4000043e5881500c1045502a03214650003034119650301032000600800d000d8a944501c80d0501c40420348484001601407103e0141c030940c4180c0906581c020580e10040340d6207116082d9080718031904c00340c5420f60640c0c6c0c00b03d411148541c410302c504050a10341c2e0742c59504a03412401a51507900385030b0640406e07a4a213820a404010b8005100030800d0003c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 372612014 1250 372610764 372610801
    0x1a06030f011a060f0f0d09020906030616030e070302030703140d0903050a02040f090602070c0603060611151003050604030816030b031f06090c02071502070302031510150206 76
    0x810040b845014280402140c851016010320004694010b9182c011011035004101c950344d45902d880045039007030003618101030304900462215011039101e00340001d00a0003038010b000702a0072481007000c224010038081c064044079104034540000075031404c0c0550805180243c280584001103c1c400f03500e025804d0f4200810400700081c01c01c0413070400705002143c2541103602003600b00d16110490080c1896a0340580018030000b030390b508002156414204982050700c00f4807034250b40b000c0c20f60359403508044050039038108480d0528140340c0d1000e801ea01c50031003451210f03416284c1e16240d1521070125811000f00d60030b00d0501c0102c0e100043c4200c0c001c4003600d41400401300e0000420f8490007030100f00048960082200e441d04507a03900b05001628001108105400006500030b695040d503100380e80c1c1c6240854144030982d0700c08111101600c4c1c02500034242413a0000d00c5103c0540018460000c5502e06040816080d00110000c101c5200e80c0c1e0040026040c084500c00001000c903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 372613264 1250 372612014 372612043
    0x41103160303021b01260c0405060a18090204060903060207140d020a05010e2e0b0613031106070f0206070305130f0e07031a010c0807020a08030a08100e011404091a0603 74
    0x46d00b03050982d4068192211800300302454052031900c0f20601099113000d603400259010070080348145140b544406094902000c010129100c156100c11031400c0344580c0c080c501c001090381ca014404149103130020f10301280b107000d602e550552811004d41c10b024a848480d40140c1103582c4200500000340140800142a0009010001c507500780e02d0028032902c0d1075201443c003890441c007102c410f0960080d42391010103090b00781e982880c142d4900041c100d03400201c0d0f0702080001d4481d07042c20520161804554000b42c001000c0807070b6000c02c1080c0e0001c90b42281040400c00c4230b00281c81141f030010740101a0480d01d10341c00d83c1031005801c0002401066501007514102d95000c00b09400628860104000e00b03017203454070b00c0c80c1400c010034821010041d42029072520009041c90000000b031103825030940d100d00d0aa100d06844603102e40580c4500034040c00030000510480c49500741c043d41034080200001403c1d1000c0c1e5034580b02c2448403039920300c03405100c001c2048604003400a2070804020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 372614514 1250 372613264 372613277
    0x6061c080f091e01020d0323100815161107090f0615020c0907111014010f171b041d06061c021f0327021017041103160303021b01 57
    0xf000001c1d545c1c540201030300e00705500c405a184c41030140c4203071041f0701c1c6010207074480c044c54072084a018990b0706d44211861407080e002c03c1500b00040014940c040c2e2113030000d011705481e4400c0102c80e0444a52444a1b5600075035000040d8000300780324072000c650342c0f03402c046441d501d40768001542c0282c40342c041c82907421514458289950b1581c3c22130384541c0c141040300c0b403000d8000d00189410131042c0b21400319031400098021001002159078129078030728608030f603415100e8071001c03070000d0b00e0700558459a000100340d2048594440c0c40804102c00500000303128003809131058010210b1003041c10b0240c006500303010340e0b41052048140b0408810003202c0001d6050390210303c0a405040900a000042c180b207400d480e8800d0b00140c00c0f1404408240c1a04003913128202d12513403048000328401c00d0580d00321081c540c018018a020a05004038020780395486031100c1403500103404580d40d05018070404840040860040d140142d03009600403c0c2542d400c08901c0e8030841030501c802d040c043e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 372615764 1250 372614514 372614569
    0x1809050c0901062c1011010b0a0b030106030f02070c120b070306080706050c030f070308010e2d13050111090a080604080a0c030c0b01062d0206061c080f09 68
    0xb0812010142061485010840c0038501c040c082c00c130f1020241400c0e4010306025038045904e90084880c00000130341c80080002031081c000f044a2507140344078600b080e80040c001000450b029510400760501044009881d0060301d0781c1d8045c2c01c0700907400407920302440001e008203100c0e0f0b8200c0c02c1e40c00121810108081c0e03081000355a542c08041c45100d081107400940600300a50610a91300302050121149403200741620300500300da0320034010344c0003000c1440001120aa0741c100c40c2044100c5001c642a404c520417028071004400017000071800b041804017040c00510f09101d148045803003007444030349a90480301000f0203e45281e0005d50550320800c14000030504030000c5075442c103403506103001e404c04170b842c0c1911809501103000d0300c0207814100008180d5005107864180826002e40400ba02048403400490108001d0806006910040009046040117008005504490b5040301c5080c85c42e50342e00541c82d48002d040c444821004034000c03420741480c07400034400d00000d02127221106e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 372617014 1250 372615764 372615767
    0x1216030807082505071406010501021002251e060209040b030a0c060818030f03010504050c07170a0c050102030a0204060908120d1104030f030c0b01050a0608010e0408041809050c090106 81
    0x492410103030640c3d0300b0580c0d5031800b9a01840489840c1c0d90301c405050248012040d4407629a6005d10032940540107201102107681210310880b900c0f0035010020400f134160a41125800c4040b40a04880000369407010500b02034004655154007881108003680e140762410901064a80b450f003490f002e40c1c41369a514001403a148440e0b020345841e807500070559502c3c2e1181800d100d000300503100c1d05e40000100103d80c9040301c40250f0503140305031030601136502c2d164041c0003c1d100d08400a84501c101807905480c00c4c032420010f00c03c0c48403900d0020f441085a0300ca0300d003260b10541b1403c214a6000408010481e00300789210010950007001d8480c1c1660501d082010740700c0c105241c01201c1c0d80c1c1700348a200c94469420350f0069908501c148500d40300520b0050120fa035809030035903441850000006540c6000c25810301501c1c00d42e0b03501e48969103410020020b01c0b8014208441201c028000400c80c040720864000d0b505658541c0807502e4840780c1002d40c00c148030900401d0051811000501090303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 372618264 1250 372617014 372617041
    0x70503040b03060409020d03081b09061905090319290c090102070e091f0506010c020d02031e1e121605070519050301110403020306040201050a02121603080708 70
    0x301c5004046030760300c0d42ca120000d002005001130087d449910f16082000341988000c00c280f15140e00301d40c901d40c98840d040802c0d0315010b9100ba207540004200b150392005046a4940c102901580c20450b0400ba0604002410301100720342c62000a042c03500b001007482454040d843c0c0d00c00e400040d1710081d941e014a94820380e44010001c000c000c4001a01003181d920803c1030300e004000e8024815110f09214014584840300c1080010741c188c50074170100c854003441d11460b40030b60016190904200e1040d82400034819100d00140e9040c091011150040300b0011000b011490000016010701c2c140c1c003000c0c0700641c910308141c40d010740c04450700013160202d190484007480350171407000150851a28005281c480150841500190420f032491440280050580260340d001c070300912081c039811200031300300c1c021440043c0d07046e03102a01103805540544000c1003030400c54410755040110100c40c40c250365010644a8140750503a8a180781850761210030690043c80620b442c1c81241803414042c03510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 372619514 1250 372618264 372618269
    0xa02060402010f0512073c0c0f0f030305070f020703020d0b182a0d080307080c040f030b15011e0f0203040f090605030708160e1909140c0607050304 65
    0x18014003d6500810501803002da0750501c20115589000e80350070780c0010070702c81b60701c03490343c00501c2062010301d210b01c0c00420340609030341c00343c260103142201c51208a1707500e840c01d4415298034900c414844c000c2038000c103071000880d0098801144a04242030002c200c10300f260300040454000c01d10610050b928071440e4a60f203900101c1201081c0c0f1000103005103014143d522452a100c2e1865880c00c861451403504000c20201c0c0b004c0c000c04080030288007060007103040082c0020001c000113446240900c4626800c42041007245003041c2c0ca4540a10310342089800a560f079040d60410018803101d80c03e400a0200030a2a213250640c02802d200c100507000c86c0000424000001d600c10007092007042074900424403800782d00f10143c3d407050508010080d034001c0d203019019652020929070300c00200e8088003160103202500300d9140070391080c480000500355602000a041d86408510190300400d25950f0007407104103e107203200000c0078901540ca00130b0328041e68040c0a80c1c0702241d008400d4070304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 372620764 1250 372619514 372619517
    0x3090b1201050f04270b0a020a090b0d0605100c0b181e010f150806070e03031c02120705030a0c0207061d0d1205040e060f060901050d06050604091509020a0206040201 73
    0x1040182c2d00006409085a4400d20340001032140615036000c00c015800010f03913001e0703410103c1c6c6071180d09038032080c4c4c410035001d200442ea010304100320703030050800200415003c2c0318001440365103031301c0016404040440d100002500d020402c000344050b298420b070304040d81d0008818480010b030b811948603109410140c4142c1440c0083e0702644100b900700c5580120303520303010405001c4109134490840202e0081c0500c40c826031000581d094001d040341014200020002c600300b54200c0460f4081000054683c4841c40d001c0c400d001486011400711401358130540c440340c0c0c43e4a81651454200c1d800030603400119401035104200ca65040030800e5208101509108041c81e81c4402040b028403c45070024407440d01c22080d201034540c0440078000344e4078948600820b0352a44810420002101810a1743c001c0040148949039130003107000708030701d00c4000d102040144d0355400060340398005500c5414000d40781c000129040341c5511540740a00191102141040e8003a44001c1d81c61000500090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 372622014 1250 372620764 372620779
    0x806010c02040603060c030e1002090a15031b0305070e04060501090b0f070c0308070c0e0103030e061b0f071e031e020303120709091d2508031603090b120105 69
    0x5549440d0000f501441e0043e1003881071a04400004005000010b5a0071703650003200361056402c01140203d540032a00140381880307090600c0300c0c881d0b10038855549182032596441c2410303081e49400301020001000e5890006191400d0720001d071020703031f000000c03900c1146004010301c510313a0003100240584030031000705610388013041090103036403082480141484641010001c2003205103002012058441e200080c025a5100300c004100e18081c080140410319030039100b0700c03030306021024042102c0746a82004400079955000c50520f041580e0076880c98101500c10b210008206980d16130b10320907030480c194082d1031600c0c2e01103c0d828884210601c064849044000c2d96010000d407504407018601e100e696081c0740030b01810116040c07103421505410a40c0305803001f072110310b0700c1d0b04400c44c080183c2032100c00e40061410161141c80c0841c0c81000c49000411902c01c10009060b0703165108042413410700c0c06080290150320341d0380c00444d2a2800300301000c80c1000600c0d4035030444400760f80c0322 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 372623264 1250 372622014 372622037
    0x610060503070306030f110a1a0307051c051503012f0d02070c0605030f061e0906040e1014010f24021906050f070809030403020913050a0b0a0e030901080601 69
    0x210090610340c0d10140036020f01045081c14086403071f0007002d106034119014110203a5854107605503084441d07040c26003000900000b0105409400240202c0c0eaa074041d01c0d400702072900c0c001048074025500d10018004400c80c0c4e800d00c0c282442100c044c06503174070f0070319440c0c1049041c1c90078412039020001c000070004102251079001d035405540c012544240c1440c120780e1500001051a0401c44501d2007120106010030b10905103a0064010002000c00d9990629031080c244409160041c2215400c2951064038201140c0140042c40244103001804034000340d188050403200c03d0182c00c8180404400c120030000c0302c0207101800114130480341599491565002e0a9003403144180c040b030b4514207130b401507400300718a980c0030034403800464025070114ac4406c40d048903514412141d02115620401c4240301601d8201c42c02c42c0d006052185a01200603103640b00f50031301e01b40d000700f250f500ca01c040900c40c07240c1e454010081e80000002c002c608001075a40000c0c64060081d00b074605210041c40381 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 372624514 1250 372623264 372623267
    0xc020d2a1518061a0f010302031302040f0b090604060f0618080a1101030f0b131805010f0212070f0203040e0c0d110d060519030303230106080601090503061006050307 73
    0x81e0034585220100304040d4041ca03012884403402d2041c2210898580034400b2800e02103804501c82000001d00500d500010940c01500290710151415440b01d041340c10031001a541e13800358400602850b100440d030b0101d81e409005101c0005407510f480303181400d05c00e20200d40c0c514041011a225880e2925848115031114101407056800c4a88039000b803980d01344c00d103c0700e13150900304001c0a0340e08009100d0405002c03001c540003505296400001c4804550544d1007a0700300035102140c40c213890450101c15620103085a8040c002c04c1c0c5060b4001c240c80c180340721000d54490703111203181803114920b014818002d40f40d20031030150740d22140c02e440208040385c00c2ba00c140c60b008101c80d0310820404003209550300d2a40c100700d581c0c046d658100400811a420a084000200307680a400c89040f241166001d4014080c034400b410302102121908070300b01d50030310039654001e203011b03194402d007802c0a0f000100a5103444e0820b40c06a84880117000c0d0080707625240c0c104987c420f2924940f20b403a014030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 372625764 1250 372624514 372624533
    0x3150402160611031b0c0a021306081f0b0312121503030a0816050a1b050c150403050d08070203070f0305270f03070b0304060b0109090203010602010c020d2a 69
    0x2629281c60500b04894040321040210700455a0580d174403040701c3e140c002022284101c01d260f03200e0350000610400182040d444040c0150039000c00400c40c59112000d00d031422212503102240003c0303818103004080c801e48144010100c05901400c5d0600d406505460036200783c9809140100d000c00001c6d0300c01c1152a0080c0c45c0401c02400d595403001c003180018181d900030f6402c503518800a44a83c00e032140114110ba040305181c0d150a00800c0224030305c800021400c04080d206405140e150459030368494140c100b583e03c02130074a0361a607045041692500311450b50b00300501030394405000c80c05400209546910b40c1c09034070b0310000c01951a040b5a94014242024030300000045203221074944a04a50074001050303501c0c56884d91000105a07441d44207100da01c5c0400410004034020405507045011200d00c181045007019903240949000ca81c0300740d2100c40180d41d2080d00205403039040c0420300d40040b8a20340b10304035900488a4840f83d02508a84600d250802640c000810881e8072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 372627014 1250 372625764 372625807
    0x109021005090a14101110020c0304080c06070305070b100e0a06030b0c0708040e0c07150f050a060806161403010305010606080906010b0d0c03180c140603150402 71
    0x4004000c428503402014110b07800c0050320b140324a11a0502049181340110312240c00e0b500106068095100c07482c00b82c0c1c1ca0b51140409202c207005a2000303100028050004140c800c41c01c0e07009660b124175201042d400c0861004500e40303e00802c112078000304e0350010075162000e0300440401015140c0346c030082d1400b03030268042c4c1c94001d00401085020107003070380a0f40c11240102e0103061a541e41d820590034600c00c05c08010920b107010b22042c44199010648664009a1350004a2500c10551900301d900e0300c0c00d9042450a80d2078070074403044580705018060b00f1651401050201a0910b4030181e100e04004100c0410340c49080c101442e00c0e07204555001040241e8081969a9610780c28028060031241c0030f09408078203014080f0302c1700c0c2400103c45049640c0401003500703041402545002601c4400c46a10406445680c05502448212091a00d09100b100503030f12103464030610962001c0000407191140c00103100700030660072079076020a51807504980040e40c03110b22030348540c1030388082c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 372628264 1250 372627014 372627019
    0x2010207050114150301020909130212060c1809060a0303050c01060f140f01110d08060a0806090709050105060a0203030a09060207050307080301060e040209100c0303110f0712111b03010902 83
    0x200250140e40340849200d8016070030300f0041e9402808504c141401e034420030543c1c3d908a50040002080c19402041041c0010300c004e005841c00420640c410b4135042c1e051b01c54441e14080040d44605000a440541e6151081030b42c0441c40c2d482c1020010301111182e201c041c040c0100090501e10a03102940700e00040d0a01c86d401e29021501d840080c4c50351a186400c6501406019404022540c02100c12249000c0a44014650540d64620440304240040c200341d40000d030816011514250501040344550005402051010320f0300040000343c40bc1a8005070103504104003030100b1a601108881d0300000b5410b010403a0061894420300a21401e80050124000803c10b20100003009000394100c0300d040d96a511640004000c10080f0310440181a40c0b01281003540e4200300d000e4a903164102e0301038280003c42d480854211a41503000083c101c0f40200001084010004d107021a481c2d03c000501d00751441d4810040c03043d0343d528122520030b0300c000300c20319810599a0250011401c15901 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 372629514 1250 372628264 372628271
    0xd03080702100c1e0504030b010b070804090e060a0606050408151911030a1a0a030f11121609020403050706110106051e0915010807180e010b03010f06020102121501020102070501 78
    0x403024020300201d1300c0b6a203031140380240070706540010322840c01d55082ea5004040d00000364a440c441c40000c0e40511400c48030084e05000024002c48944210340c240300c3e4020241c030807483c080c0390b130004175402c54100c24248002400240041000080e5040d002d551803100b032901c90701c440c9883c141217202407038000f00d1a8244101e511008070800007440c05054150010b00a07036545503100c90528a010a04a402141c00e000c100040b552545800c2d5138517026400400180a412000c200f079165499020f0314194001004442c0d902d04c2c8808400040040c00c030114145411941c1c1c094a81c08280b10f40c40c00c2041d00c408001d082c010a5100400a2a0042c480b0141103181c001041e601c41406500340e100300c0c81000040c0702d0b103c3c0c80901e240c880b0016996130190380c0d14a801135440188007012405104284040403500703403d6002018060700146c214241c503076151248468904020b600004110b90042c4201065009000c00c420340000d040320b4180300300078180780100d0081c00780000c003230702c00e41c02c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 372630764 1250 372629514 372629531
    0x7020a0506130f0f120b0a090f0507051e0d032703030801060f1803060c050d151a340b07030c140c0705040509070308280c020d0308070210 61
    0x104400c8070401c841503100703c1c80d2455a0f60a0603074002c83c05114003030301c000c00000644e0003d005951419402098030000181c010b007a51980d0084070b802c14403c0361254008039092005250070402010811a45603010701400c04050120391a000d800c1c1005003800740d24210080805440340c040400400c50314060003280307a807814001c180d0407080c402c3c1400310300c14019030020326200b110540012454002954860303861681e440c0300a2a803003642c1c0c0108001401941c001c06210b006a81400102400144100f41815802150072504100780701d206c1d42e007002a11101907868800741d43c40c1c08501c034010000040482d03034050408405c00010400c85014080082d143d4060f8002000b1520940d0381022400350403030707002401d12039052000e00d29070200380704000c20b182c19000268821114000e640340e1036074a540d001465000328501c103055000101136150902241000801c0c0c04bc0107181c46104002140c020500d41c00c42d5031400380801c1324940c0004c0300c440c0200800c506801144804122480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 372632014 1250 372630764 372630787
    0x180301090b04080310060806100f0302130e0907090b180a0f022101061d130e070f0314010203060a0b0c010b0a060e010305090606030c06071b0b12070c1707020a0506 72
    0x10b100b21045d918260090b2404259a4403828050f407040c50081d000e200d4480e0741c04404c3d518485080003403410142c080218107144103484103c0e000601c2c02d0a4414018100070141c0c9086c581c5503003003404880c4ca8004100240e58030307c9601d171000e40103c08200840c0c0c850b0071400f00134020010078490014000101403000c0c1c4013540c0010b9040802d48070044050341c030b43c00304079900001d100503004000706c10b4010a1092905038100201c808140c640001c1e403103007402900d81460b00540c4580c0f03007403010390300c204240700b1074021220748203190400031491480c0c44c01c0001c520790740034050101c44034808150882211403d5112050300003008020084039590f0301401450808840c020a00007401c201c0401d0480c2c5001400130300441004000c1d10070304203458180203050f08902c00c183c9101c4840601d6a44401412508030040c00c03441d40079558035a12840b280e000004054101000c100071008164003040c45c80307182080240061410543e180710b9400044ca260344140c0115511480000341261640c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 372633264 1250 372632014 372632017
    0x708090906040b01020607030b06190528080a050c0c0105010b09011b0f03180b0406020319020c15030a060902040902070302011404150c12020c0d120204030305180301090b0408 77
    0x122000c4695414940e2400180010b0307a074890320303260159100340045181e850003034020481c1c81d08060807140c00c1c80300c1480e8504058145c620010046500024080b010200c2100381d001c002280c1c0d00c88041c1500b03001e0b0b005000303090050840c40b50700e070388101144203052074404403034401c2070002c001c0c440c55841e00d030944600c0e0300c242159400b0410400d01c80b0310f40880142e08180441c0c02c140c50501c40481906d00f600c4401d0b0104452000d0103400b80c0100d21031200f00003174000707004503600454036000d5032502404002e6000c2c40901c103542c00408040380c29a2003026215400c94a070608a80304c0d224412184040c0c80150403e143c2c0d580080360105075508154054031515000364028490811000605d0716541d0042e2800340c0f0b8464009034000e100f14050f001004008101e2400318040c1c1d8980c48044202d80104003625440d400c904150702c2c0c0180c0c03000d11400341601041c001c40c079107440c40e5405030140c81064820a070321480e02c5034135a455607080d4010021550080a03000d082e02c0e04d4501410765 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 372634514 1250 372633264 372633277
    0x504050607060e0d03060f03020f04020f07050105090c0108160f0e03010c0c0b0f06010903080304020f0a0806180118060b030712240204060507020f0a030804150207120c1a0d020708 79
    0x144e10503a06008a414407900540003260001c0b40700d900c4950664081c01110040d0340546600701d5000c0010788046440540205221409000006441d083c4071041c40d08004180782c407641048952000d101c03074030301c070021801c22201d21030411040c804801142035401c0e40c5400e032556070551900d00c614546a4019546287c03691160003e0314007640d8444d0b502e00c082c50f0548000c0e0004054401c1480003c155800450b0090300040005c04d0318940080021448002500b181303549030490820301560401030f554036000f01d07400710000e115101000c80c440d4810b4005d148050b0283c1e0f10b5206141e140d440c140500f2003c0c00c62200484510340c101d080c003ca0809401031204030024a81024042c0c50341e251007075070186e55482d902c0e5480c29200307070200815002a601d400398080c245600020006500380c008000824181c0426640e000240d00e0107405d024183e84540342c406c8482c4840800542d90303050280039a2610fa034130880c0410811001f42a6009250844448510005082c024040d869025204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 372635764 1250 372634514 372634541
    0x60c040602070812030c030c0c06040f0b060d03021c0c120306030c08010603050316290612011103010308030907080102040602010209121f05070309080d0b0109080303040309030b07050405060706 85
    0xb503900d4500d10b51356a020003115440708014404541300b682e1140096030014107076008503061844c040829400c054058808036800759011080e0800c000a40071416801042200c085000c00c0540c0c40c00b81d00c420200034400b504c3d03000c03038901e00822030162000c05040d42d0840003031205020304640180040101e400240c514418595002980100500818043d030764080055402c115000b8460b5140d0820f0f82c1e421101860100a581c01c0c5554001c402c0550755421030002d245802c1140610009034400f40031440303136034146903c95211f01c4001081780e0441c1e07400800c1d10358a90f1a5284941408016045140340d940005000540954150064510244100d4040c030704155002822541d40c54240341d00d40030075522210001c01d11b40f00381c1c44194070200c14100031806000c5036035402440d91114648080b216900e00da08015035070301c200f01c1d801409080300110f14506107501c01400c500e40600c40101040050b200191115205d10180c0300108000362070b840d11850545040c3d000b4015210f070042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 372637014 1250 372635764 372635773
    0xa110409050906090f0706051e030f450f06092b0806010e0406081002030f0c040501140d090c08101b1d18010e07020c060702010827060c040602 63
    0x151381c2c4402040d4840c0383d003480c200405195190000569070341e041904800d003848540903180d00000e40030b00045125000da0a04404286002c0594091042e012201d50010560700018000d02640030f000c500a5032581032003c10709031200003600741c6840403004d001c0c40140294010321002540c001001030204500c0b0007044504081c0390700f1240320001c1080084001108100490300d00d5024240d90392a40358050300c041105038035000190f25054440024443c5981d000007000075200d05038900c0b5402816905400d803070a40fa10000a00328208040a40a4400c1c00a6100e400e102c07103501c201d070880e6010b4414280186c1ea0184140c03a030000c02404401c0324100b004800301c2c0341700d102d140c00c0e0f604910b485041c500c44c1d1944e0224000704041208507000b05c0c080b9000b0b07030011071a544050080c00790740c032409154580058001c3c20405400078480c0200420b00075800141e8010000550001c83c1d10500100c0500d03403080381119013618a1243c019004084c203024032150520014030941d00d1540884 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 372638264 1250 372637014 372637021
    0x20609010c020604032109050d0504230604030b09010e012a020f0601230405280b06042106110a0906081b0306010c0c061d0603040f03080a110409050906 67
    0xd98072000d08590040c00502e04c0006420180303560254110006e000e24000642400c00396100351800c0c1e0010150400f01310081410048030650100c0c403001c4400650000d03299516901c040380583c00b039400300a00d01c01d042c60001c1e540205c00d5010b90004024040280140511407024024504a0a2054410f541d0501510764001d00008039400104001c200401c070707503864200101440318005030041004400030302d522509035214000c403070180d600c0640740d00740703001101070031030f0f5100103021b0001c0541c0c1001542030b1583e0b00d001c2038500303d0f02640c441d032019400c0600f43d2080088250001042036140401c00d4408442080c094100c00300603486e11070446440780406e5903d06d60803105100b00000110400351140b1800740550742203101070400542c0c0c24041c2e6180900110242c01800c0010000588500c01e6101030142031040d81d0243c0301a85181000d480d4542c0f02d401001014003881803a401080000c401540012490000543e2482c1c44a03280c519100c0038140a5410500e54468400030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 372639514 1250 372638264 372638267
    0x403080918090618010905060103110a06140a0f0c02090f0103110103020c0a0f050109080c030a08070305090c040b130f0914060f040b09070902030c0c06180a060216050a03020609010c 80
    0x70b000e00241c0b00146015a1104160402c09500120700701e801c0d52601c000c40c0000d80100b1115020b1449118800c03045013400003441140115948240100002e01045189100021045400c02d28041c54907121720014044107880361603074610025041003103502084075071030b5030800c0681620700c604010705134140c40c0c00c011026401035180100070f030b0b0802c1c4600f80001c0c000c00e0070070f24414820000401e212130991076119841d04640003041e481e400001702c0006003a48100015405482d5007000c008500301410015a520501c1d108036000c1d981d5804032035142c0e46d80614640c00300c0c00c40c083c00c0c084032030081c0307500010380b4412604442c2102658428444004042104c0d03105102c0d0303600c4008070f44c1d0340c1d490740a800e44018204c00314501800a0100d51003070140021840340c5c0e120006c8e2580d0f520f68150f0036281c44002402002c0158407560b4403403601c2c4011828041e25038005001503298803030401c1a82e07448020752802001480741e044030000f00f42d00455840c0c8241c130510000c02400994140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 372640764 1250 372639514 372639559
    0x20112020a140903150112050f0d0918140a0c0908010c0c152301050306060d1713171c1403010303050c011e0518011e0b060f04030809 59
    0x400d038046111140300d506951982d002420103924002d007224480002c9000200548001b070f00440c0070784d900142c200c000d0140c10041124905407801c02801d80340c6c96000014000e40d00c174000c102850700065a01c0340201c050303405c003001030342050a06813804d04001c10300c2001801c203040c56801080104000183c02a010b10030658608103d0b01e512070785a07400d98501001d00351102c1882c500541d183c0004c411003c103c1419040c088080401c418607505010804d0300e001c0005060500c03c12a200d60039002400c042c2a04201c508000f42250311364a0110903401042c1d002c1e00304980e021000000c100340128002182a0141107040903203009142d0480203e403104020144081c0c800400c07c01000000c1c480c00050006081e04c0c1c0000800c024038400c18455030142c01052180d450711381e028882800c82032200344104490000080140303205e058100e881c007540c4030a0a000140d0f40e012501080d0300d5203402c89190441d110b0500d540c8607261300e0890680c0c0c108000f800d02407940c821180f16980040032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 372642014 1250 372640764 372640777
    0x90e03120c19080610030b010203040305150a06050405130201030515090421140f030402130e0703020a060e0a0306110c0706020102130b09011b14011103060415030b0f090717060402011202 82
    0x2008080310303265044050740031f001e414403201d04500c4104000404030304c0c00d010f41c10551407a50084419400c041c0070b0181900c10b2508041d2055103088140242c04400400e0400f41560a090120391541c0b030340e0201c0100e4040a41403a0400d13080d00400042022b00001144461030194490240038010744040b0b480081010b41c84003002820004400380103145400303035070b12501c01490340002c460900c134001d080d40d08840f050011070303010950a0045181081216010700244e02e07000605620344030000d0000703500c0d48409809280c1c1d0351124001d40c0364817022074140d080140c088414070360307441000030b000313511103800b07900107525240b00410510380100c11604a458141d4030b0790401c000c01152000d42c03c511010840319141c10f074410986c3ca03142030142d054039010440e80a03481385049000c0c4000d9a0b00010880b01c43c204407001400011003400c151500400040f00076a03295440440b070310b1400e40150011942170720280c54000707104100080c1e091165200b80d03220300e030351001a14032005900031b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 372643264 1250 372642014 372642019
    0x5130b0112080f07050a02030142170d080105010f1236030e041b050d0b19081c120f090b09070e090f0304090e03120c190806 55
    0x120041104a20340441054414080c0541e280741022400b0400c0c201e5021a50495894116182c00b40a40c6002c0c80307903004d104100a00017190401030316000101d0054850f804000340042c18000c1d9085031228006805080c041c201455440e16601440ea42c40c40d604500000251943e400800c10b07520600c80d410384584140c0f1482c2040400c0082000508440586841091004892104c10740c01c0791120300810382041d15034080c000610b0070003c201080c00c6802c5801036080190810b035501c0b1740d00d04801071511524240742c070303581c1c0011420702804d00560110780c820802c0700c03840c3c4680c0f9000203910803500c0d80003c5660601400c0e00d4621491880c814101c04100d1003481070510120540010412001140c40010601c80c00c2d9949081e588003641c410802d9031041c41d0911900e605c2510091700003402000a0181d18003c800c1e0964906c51401100c410f1521410314034440300e4204260381c0115075014046030340b450041c0d566a9150410910f00f01d407619a42402120103000f0304001c2d00a0902 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 372644514 1250 372643264 372643283
    0x304090b0907110c0904030c050d031e020903030d0b060d09210e0a210b0903030609010f0311010c0311030a020615011d090432100605090402010c060b10030b040513 72
    0x111410021781060081040e818406201202400580180286141844241c03000100010302c01c2c1c0c52000100301005504005204020708440d50341e00000f0f40e588070590b04000704580e107440001c28058040c260400040d0360410900004000c2c5001d912080701c440000000c100ca0400b10045900d44d1129580d2078000030750b03001c1030121303c0c1c102920b2034041c0b0880c14a007002c0180e9540e1a046d0540c11540c44c1d441d5000801070003241e02d0000d0400c2d00410843c01d910700c8031070a507190102e41042c03054036907040c4402c4401c40000c1500404c110502c019a0000b980c1d102c041c1c1d6103020b501c6840403169040d1a805400002141d58001e0020b601055110700d40510f008400c03405001446902030426550b8840300ca0056001e15500c0841d03030060b200401103825042d5004182c5841c121690065030b00590418078248901c0d01e030005801e0303005030240381030f0b041c202040c01c03c08001c084201015400c00c2d01c51030200f070b0b0680c064000e0321801c101a60204031036560303212441d00c52100c01900801c0881d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 372645764 1250 372644514 372644533
    0xa1b05090603060f030c0d0309050a050a060807080619060c0b0105011809020711030a1209061e03020702040e16141002120304080d09150f0501060e210304090b090711 73
    0x4c1119003442000c4003d802c071500840018000307000c200d164041140001c1e52014140802c0c10003c04400080505980040b0214202000600249001480d81040000f144005001e581d5540e003c40e0000c64000303140c61a4035100c0100030a032141000c410b5410381e15074400042c26502c10b84004281261050300d90700807a0610308154080c4d407102d20103a801c0d50144401e51101c0d80c0c21b00c42120960300c295180760140295050103040c2c0c44d0703240d00ca03106105880400c44640c441c15a01902684410f00d00140d0300c00c224800a80107010700e8602081078400c3c18440c0e260280450440410740b42109021000a101c1c4d07010003860741c0c020001280107800001c200205d040300fa00156401c503101ea0605030409a049005604550550406490604010440303086020151017010412662514240219030401c40e002e030070011002d00c00e50189203840c4407807800b17040e0440724005c0c3d000514256592669140d02c00c9014214010b18584291000b4000c15400f034003c0c40301c3e41c1e00044003000b40c40040d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 372647014 1250 372645764 372645769
    0x60a052a07120312060803072f0f01051608090a05120304120309150206060f04021612050c010e0606040b060a0f05070c090507030e01060f08031209070e0a1b0509060306 74
    0x32001c021010321041d040040c0002c80e040c01170314090003846000b1074580c4007038207001030540980c910400412900c603410b004a00c4020b13222948019090307a03191640e00030000101c0f401d10074810802c58031901184e01781708101984008101da40301c201c0e008168603458034104054079204000e20303920780c0e0080104100c8840c1c0082601c3c043d9000f03081c40d503101583c90680c1014100b1029007100160090030030400b9610b49043e820a422501b500e00318101070f0303c410305400c0070120f0040501020f0211480000e81ca00c150125401d4501c5c90009003e103400d40e000c020b580e4601030707800910480c10002035034481d003022070a0b502c441000380e440c642e030b45902450580b40ba80c00358400303a810126891303002c00c4d007845a0080340e00401c036581c0c00180b41c4503041102d50841300140c008100301880d2030410410341c280082611044040b840000d01952a0380d5030107840c10710247c0c40072111020f00d00c00c0160b51986030340444072030070043c030310720b642c0c0102c00c3c2d01140c40d8031810b41a180d100e0700030301c0424140d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 372648264 1250 372647014 372647039
    0x80c0a090b0307050a0b0319090b0720330f010603021c02031303080c0f0406141608040806100f1206090204060f03060609060e0c0a0905060a052a07 65
    0x180c4020b0280d80d14140c45101050158016400403240b000300001448854001802d41003100007401c0410412942150b42d5410f0902c006000c09040051000031600c0d005900154040d110b000d04d02129840740c00090446501c0046181020454610116142001b40b61034241ca2040b80d00c810441820703800c203030042e0020f4101c50f210011a480d000d02c44d0607441c90720720007140030b42c0c00740556288440703041c50f00900300e900c004d1203003480c02001e000030f1204203100c80665041d43c1481c203000303400841c0103100d40c65500030241c00000a804941c000c50610100707400070401c1c2d40080c415102c2d141d032007001c04400045c0c80d20030400c071480c0482041213151000e030041060a441413a0105030815a070300001e00340c0301d040d044421110f442110820030040b103446403100401c0640703c148451860000d1481002c85c0080640d1000140060000955441410010080d2400500d50340c0c6400c02c1000040c0190005451000700e0b2a5858006a44641003661440c000c44600002c4c40d10760304008124030340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 372649514 1250 372648264 372648281
    0x201020607110a08030411090711120d0e03042921060607050706030b0f030606060442080604090203210d090f050106050d0309090207230705040501080c0a09 69
    0x164003da0f00c1540020752508001c40c091809404040e1300f8590000402038406409001d003000c0c004d1100305e414401030b020655140c014505a00551100f10005a40d0040c0a0050241d9024080050b0105054104031304900051945844042074800f8070580c140b02441400b03241d1500281006942d40c24050300d00503580d005c1b00180605081c242c90f551010b2401d0f1154208802282d101d400c0400b56041010016424032804c0b07000305004c1c200301d4080b07102c9100d6030145441a40c10303814141801e12000c80090307018100500000c014450f048800c4045604200b4104002003500001c9085850705000300800e01d03070000d000d48100f116078950b0b40800025041e2080b0217aa090002584800841c8540400280a039110881c0103c40703180442c00c450041c0c1015104401811030100400c1d4482d0150080c1e030215440103079104544c3c200301003100c0000e903004a1420003403650313040355074012030140d0441c0c105441c01d0042c0d03600c4040541c0c890a8101c0d6041e00542251010030a0340d101c1d4002501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 372650764 1250 372649514 372649547
    0x622020f12091e0a0b0f040501110a0302070605011202010509040f06080109111203190c050106030c03140d0219020915090c1b030405010903030507230a0605060405040201020607 78
    0x1a02034201c081510100742140d000b0525000b640103c21100c1e01900088006035860015283c9101150769482107403030302518004411558000081c03c0103401d50208448206405110b52141046c100040196101d0502100d505003400c0c00000c40c05011420240c5072a4142c584504254081c018000180040e102d40001c0b56110035000030241001e1094000e50750148101015104507001801100c01e40101000f00980c802c001e203c5648041280150b140015443e0003190081d443c105540584816040a0300b0791011480c000f080051110b199208410302d041640c1c13400b11b5501090380c80d080110b4003c0700100119058400500e06214050b030701601c030342c4040391005228000b203030151707074122401d64404d0b60000f61015600441c1c0e0480d0390780f0349250010342c5842d0424000800d808400d101c02001e009001c5024020810300d04141601d00d0091410100300d014a1107600b43d1319101a03509849007494076000c900343c0d00b01406100d1103581c06030010200341c2c5820b90211840300c00d0690380789 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 372652014 1250 372650764 372650767
    0x3021e010e12010c1b0b010e040602210106020c0d120e180703141609030201031116110f0d0f12170c0307200d05030c09030f070e0622020f 61
    0x8601c0c0e541c940b000310030342078103000000e004101d028001d050304042c07482003d110704040031940b0004614074110b5055410040f00c28500d40c456103007613800381c014401488410070078100313400004043c1707080d030038100d800f20742c200c41000126a0a20a05000c5100d0190505c1c8140c042c00000b030740139403c882c207aa08050000d640041050360340b9406040d06940140001e6103072103842e12411180001c2e642c03c65a90f4001c451030781c6080300043c104091510000b81419154400000c01c5850f54013500c20140e20354004003041411850524590125030a116204441100c5401600e0600181d0042984d40c0540700ea80961019105d2a42c90309440d01903d04200750f20110783c00c400448182c0a0190401030303120354507030370000c2c4041c01e4980d0a90101d00d880507200040401180001000b1070f07248441d0410b01c0d902e4030307881d40e091520f00c038008100b6090303c241030340906078240015014044801100c0c0748016612060304005402482c000183c0c03c03000c10310070742c4a4502d4250b0041c08980c00e070f0030255 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 372653264 1250 372652014 372652037
    0x270d02040204090c090803120a0f14100501030c0e211903030204030b01050402090904261303050606010302130e0a150909031d010504061d0406080303090106060903021e01 75
    0x301640c0c01500804950768036021204d11803a00b1111207006030811308061800c0c900600058000803000400ca000200d4884d595154100d240da402980c0504910b0314528952505001e10440d409591060728000b030301c1c298045400d50303c502c00c40507000d42c009005058a030030b1050a4100c030b0b900380201d00744034001c1e4900400b0400d0300101511800380310380c0300035841e01c0c40c0d81011014200140d018501a5004101c90316041d079034100c0a81d0b226a110080d00b000c01419140804e10268943d1000c40e81040010148116800190b0050031244204d040f03d51035595000110107074050703403802e0306503400e8100041c440b00c3c0045524a0348085028800071b210559030000043d508910740c40107000a50301c002c01011315034002c0ca00b003149445848010385001600380000c0030703440b41c2d108101c00c208440819401d41c01e44004101a508801841801500d894001d881c3c0c032940705980c008a075628140700021607500900030760003102c5d001040c071020003415102941d80300000c1c4980c2410440c810002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 372654514 1250 372653264 372653269
    0xd080c03030112050c06040501050406050d0b090106030f051005010806010807020c0d2001020a020f041d0105040b010510021c360603110f07031103120f0402090c270d02 74
    0x245008010b480c080f02c6030100e460a220303082107035200c101030040c0300c100024803450342c2090480d000c0f120a490712a035240c28048086006010b01d0706041c0d0b0101021000140c0709a02d50000c940180c115601084140c85091220128030040d1184502195140000918640c065100164031940380d0040d10544591580040c60340c21703008070101c1d40d011403d0700e0110038864840340d10700b501d1001c0c002002c84881e9900000c1c2100381d107032400da2040d0340b1130342c07200e50b41150b1400396034504601c80700910041c1090301d07202030100d009000366401030409580344200d181c800280c4000842d21142e92010310921031000f141c00c246074048003549020201c4030761400304601050100b0519a0800c8142000e0806100905032111400540e5181805006104189001d041280e120603030508081c1160512034810f01d0039801040101d041d650703414000c200b0707170946c00c8030303902d100b540b0032036450401c1c1d41d58a400401c2ca010360140072070390291000c4030003000d0003090192000400028002d19420b0080ea00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 372655764 1250 372654514 372654517
    0x30709090503120108031602060c120f0408010b090708060906040b1306031218050910030b0a020a030b090f0f091f0b0f010c050a17070c1d091b0d080c03 67
    0x10844103039000061a41d07800f01c007070044a01621900e0061458510340400020420000c1d060280c8100d00000e200026204104098080e8000d0a0000f54907074500f00c43c40350b0700f034104e841082c0c02c40d401e00700762502c140740000c0160300c5610a5210030900d501d5000900c404518020241604940e44110104d956618500b020b01f030000c070180041015810341c50082e1182c01d40d80844400e01001009200d45420001c0c10b40c0305540c0c0c240c2e14520641d5451410300703140001c59002500707000d282410301c140810103030005c0440c07000a88091040490343c00502c00020011110000440080d0300806d046682c0782c580c09400402d40b5044502c01d048429402a0300c52240c410b4144865452101d0f500a043c41541d40403d00001d00b0b004003528425101c0076104c84414800426840f40c0c00d000c034100140180c252500f00342c00900c409402520340e4502d01e201e4030340380d4010f8400b1000c00c3c0001c3c2c6403240000c1c0c58074503040d045580c80840c00040284001034208086c111008042408040500d05e020030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 372657014 1250 372655764 372655781
    0x2040902040e31080c030405060310080609150612010605031006030b0609040b1909080a05220b160302011e0618020a0f110f0d0e011205040f060b030709 67
    0x50786a200c1e402d01c1051001604814040606103540e40c844450f0410400580914490b8000c0301c0c8917940d401124085045124982209034002008800d021025a03c1c00221054507103860813959140c6502c3c1c4595590300c80c1002e28007040099200050280c02d00c03010640c603040c225400421010744a00000e814400f00001010880c1d5903448100140840558001d1700414142c90b18002030901d41c64007513102200500c201c4443c9a150b9581114501590103402d455030000c4807280c9a61340b1020043c0f4680c071904010001034500800c0c0d100c012601d00155040301c4500800354a07100c030200340885101c8040740258259580c1c0c0340301d1594404041020203a4030f110a10024050341880040c4041d000803003040517465106000b94620300750003400c040364038460b07030816a50303094040340d00c14581501d80506000c6070068030401c0b420580c00040c240c501803426258100c07121b00c40002c49013226402c44014044159441243d8007064136544055018a0080e050300c40d600e0b02c80309803000b52183d11 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 372658264 1250 372657014 372657029
    0x5070611150c0304060203040201020f12040e070815040f060e0c040609080d0e0f0d0f060e210706090f0c08030306040f02031510030e07060207050406060c0302060a020c010204090204 80
    0xa403020004410600c40c84100114141412281c0e0070b02e4041118140030080c402042a81d0020110381968020050f01000319000c8045407154a044085500d20390454401c444008c0b2015011a08260080622911403490f621030300405082c0e1070b04100c00b902c109070040404540c2c5500201d8070051003200c251103007a800614644d6146481d030b0040400f889079001030f0301034002c401c0b01004d040e8000395885110808459480120290710000340c6d0400c40d0800080c02800300c41044800c000080d00080c901e50a8a2f080d0740c041c03031616250030342d034140800b0141e080940411100002070503176803217034401e00c0c003984085000d940d00b55a8581c822007182c1001119500200030050245414098030b03804062100b81542103081402c007410301d070f14031950f50300c0c82400c10901c103204c40341c03099200c594080030030403c0384c51503507079008081d454900307500986001d582042004900c0070b015070f100c010f09651560080c00329903565880000290050704c06015955000c0100060010321800500058a04c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 372659514 1250 372658264 372658277
    0x917130312050a09091a0402030a0b120718110906040e09010501090603080f07020f0a0f030c0e010305030f0f1603050405120706082d04050f1218011209050706 70
    0x15410148101c1c54100d0100c001c00004002c440b000540c40301d00041100d20104020418201c10618800c4910740100e246030454804410441485815007000300f00714070a03a41a101034039032a20003031b207032031080c003a0130395844100004109411190f0721401440844505d01ea080c0009000000d6959106d5801312404101800500104010a02c6000e006146260041087d0b81c9140d44d040480e0203800c06144060602082c0e92040d52102400031200c004010500b090032500c844100b80b4000590006540741c4e010381101194411802d0400d03416290080019410101d0a120b1040c0350341c0325005030003646c0c82c00e018032580c4003450024500d01e0391007038507203070b844070b08000500c2004140c40c4100855540090804c0101e00d03005100340e50480c44444029898020301000c04161004000e100c248500e480010001401004900c42450710040d40950b0180500307403405c2c14081c083c4011a8038180004003d081056009140781c020014002401040c403d0b16500c4090401045034001808241d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 372660764 1250 372659514 372659519
    0xf051b0a0302160e06100f1b050102040f080a0803012c0108010203180d0f0e0d02090c0a030e070e070e2b03020c0a060912230a020307090b03060703091713 68
    0x9030f122580f000b4002e54680c1c00100c1c6030240c00101c5411450b00f128003440440c0d4584042140300b2800010103009a0002070140c072080d03e440d5000b98001d00c240c80d0b4004000701c01190307242c03011400507081d98108410505607401c19418854404055186420642031040c843c0e41c000c00b02c40040b402080070740b00050b02c91510442c0c02080d91507505840c8115085031202101d070b00e4004414006000c45480c0000510001c00007161450207612070295100d00c011042007007264108008012030030b020764003804408030341030000381c0d1550a40a20703905043d40c8000101158410f40c400c10744568003c100d8004054101030904000400c0300600309600c0b20507203aa030525404000301c40b1140d000742c44a414440c80c1c40380051108166004251500001c3c50001044c05a00c1d40900199010340807802000740d003d418260340d441084104a0080c05440c500084941c400e22444003900400303006010550b0b201c0e8130450042410f40400c617103034400020041c0001242e01d015011b07404070030f10725060b003a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 372661870 1106 372660764 372660793
    0x1020c030c0102040305150108060106050901120f090209060604180b0301020c070e1009090317040510060605090301050f060d170904051311010f0f051b0a0302 70
    0x20010503610401c0070198010b1040300e02c254100c47c0c1d801c080c900b01d85d50080c000d03c100caa580c0c101a0040012901500007087d540b88140744c0700001410501c1000e0480e20300351019000281c0c0c4800d25411820000c0307504d500a07204503105410540303816034009a0b881008400407270300341c03103c2084005407002d4054480218941e010764041e03507210001441d0180048513005100d1024070320005017658944101170f0708541683d182181d0021203400ba03a2003032000f501c22141c80c800d4201c0300f206900305104130405400d460f5a042c0e650070207441007509640006d808454100c3c0c200052003181c5c0e8507050325180c40c9070701500b0102d49801d0306034002540d00941840e1034125017000200411140c8108000c40300f10320070b1401c02c1311000e42c100111800d000d41e500b4480850039406079410518052000fa01e24203c0d401c000726840d08113620180e0410351048400c5000da80880200da0001 = true := by decide +kernel

theorem cover : BRFrame.Cov 372482014 372661870 := by
  have h0 := BRFrame.cov_init 372482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 372482014 ≤ n) (h2 : n < 372661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
