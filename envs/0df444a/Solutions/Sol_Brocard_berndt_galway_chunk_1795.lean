-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1795
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:42:04.163157+00:00
-- url     : https://prove2.me/submissions/610272cf-a2ae-48f6-8ea4-294facc3154b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 322661870 ≤ n < 322841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 322663120 1250 322661870 322661881
    0xc060403030b01020708120405131b4d0a060212071d091902091305160c030804061a03010c09030204050c0f16080702030d020a02010e1f0e030705100305 67
    0x41c04004000c01101008150a41d0348107003000c1c40d88a540701d41c034807408014194402415240d00a040d0000d0210b400b407080411101001e060619042444a424400144100c40c8000c070214065585034103308030001c088074082e1080c0c9c8090111411503268402c00f880300c400034400d400104812000cc1d44000c28a00789100007512294940101502c041860106403129031200d050096010762140011800d040c00c900c0300340000c0c4901c007070b400d4111080998401d82c1040c107402c000d01604038080340780c49003851418126901c80c2003c030000c001a07451004107002c2030b0b00e17030403d1141194041100751308040c40301c002801c403030b9444140008130f004060304205600d01403041c3d990007021001024a09035101c140c018a510418907078003030074031200b4480004d2054030000c1d2a4841c0d40a000c8400d40c054002c0003a549407030103a0201e0004005051010351350a2025407100340c1b0003406010881035411030020f441209404d412140c040c4250880040d00d5a900d0600a2519095440014060606 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 322664370 1250 322663120 322663123
    0x524060f1b0d12060803090f040f140103140703030203190302040905010303080601020610290d050c030a053301030b0316170c010c120c0b01090e0d08060618060c060403030b0102 78
    0x10440038404043c44c1c1281004204004000c4a030684c1c41110301d080100000030000780206100f4690b008d00130714102d01c80070030300060380100c1d040e01d0080040054942035207050581d12052400014010303002440641c60380e21111141c9031080d902d0f07080c0541080d484501c008210b9509a0080d0006890b00c000d0044a58040c8283c64201c481c0700700e040c910707909241ca9a03104040c42d203448401c000d00310841a0259070030754261088101904800d0203142004846411a03801c181ca1254440e45401c3c00f06a90490001c45e03c20740561210703400403c1100e0384000c448543d004001241450b4130341400c1d11641d038013807001002080c0c0710fa9920070a503051080440c54030b1a0302403102a142e0000100c200143e8104664000b940d50042d03800a640c81d20400881e0300b1031007403c00800402e021400070818102540040780404200811902e000064501c11100c1c50001c0d62410b40044e400c001e8205a042e0410a07003074a03c0c1c0c0600b54525150803500c0f03552808100319401c4d00000c1e912211088250703070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 322665620 1250 322664370 322664387
    0x4030b13021905030d0c020301110c010903110a0201080a1d121b0606130e19030207060e3a02270603122506090302010f0524060f1b0d 59
    0x2450318502482d8185004070b6a40e40d82ca08450042c0143c803845482156801d41010205402060f282600e821003a0807550103040100c80131004240c50402942c0445400102c0f0000c60360140d41c4c60714039480e000c1280f40208100a0364100c507081942003022442c000b00720728401e0540030318840d660303500d402d002111510710140c1c0100041d0466814410307035984400c01036980d1140701c0000030359400c1010089150142a4000107074050060f10658103154010032201c0441d0016256030301d070f258015042150300302a121f0010b040310306014004042c501030405000d15011103c1920300b0403030050300024040c000c5400703002d03500d43d90308051211002403d550b942d0405030a8008081c0a03074001180ca00c2d6000d40d100c2c40c030380400c102c200e018800d0b20b40740301d88841640000302003286240c10f0400038060055000c19203192820305022407100003100c40c42104a03400303da03e024001807040c0c208607403a030141080d501c2c500d00030301020102e400842c554090880f4240000e00fa038004c410006403d505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 322666870 1250 322665620 322665649
    0x9170a021903020d0213020403050d0e010f03020903100906062d0b090907030b190905071d0d06020c2508010605040c080115120f14010902250804030b1302 68
    0x5581c00410058541c841e6003450180d04a408010780c0c103070040644000c0c01940e102405c0c601c0741d00002c440c1150424450000003c6c2a61203030100f1582d440190280e1140003c01601239100d89001d15049003103600c07541030180300d03804c0800c040e80d0b2045c5c00781044039a40b0502d240c3c503400c0c00d10401f840c0e582c0c00c6050000c1c800d0018031800e142c0380a0014a030b03454000c14002c10705071180403a110f2695840042114000c40c1c0c10100c0106032500f241d4001003008594000c0403441e6030f52464010726208030b01c0020341000a00146000c8015036038503010350050f605908042c0b14001e80c0000341441d880c005008045061001840d451920742034a007900c103181d001a01a03807400e49a91841c49d0f1143d0840e054468207505a080b40e441b5590440d02c260400c10000d00d0503240074000c1401c3c035100e400403c0302d0031800040c44216600c4030308000407842440007031030544e5840280340490025240854a086000e08013150030180d0340d032240300f207040040310211491400001090700318504940b9140015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 322668120 1250 322666870 322666909
    0x1101110c07060e031c111612120c050d18090e0c090c090a0b0f0d09030e01020d09050a09050603031e03271b03010b0d050f0d17150109170a02 62
    0x45440607942080d44117480c85050402140d0400c1c1084243c042003049406441c183d2480c0045640e603040540000c00c1550449040303502c0c0014440c800d110303c400000468106015040012030713148181d9203801d0380f4012003120320301100e0004100300ca601c600481c07462808081e092001190081140750040241a0140030905010500c0180c441007a80c00a8890000f0202d54499108160003141d0040007011540c0e2401d10000f00105a0700c41e01d40f174000d000a07000c881c0c2840c54120306840c4402280180c60300081c41d01001c000e0380081c0e410154005d0703006019070749409003014503140c02000000103001e48031000401d1224640080040955004603902c03400804c01000c0011510303047c140c0401c40c0350440ca0901c5070007503070702980100840100101494101052031070b0075070b180d66040060304018010510140d1116005807040140e120001c00902c125070f49441001c540043d83c9089541009000e40020649a0342840030200e26080c41d001414494214030400c1000380c0980180780c803d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 322669370 1250 322668120 322668133
    0x20706090f06030902040e1f0c0f1202090a080d08010e011406090f28030c080303040804170c0603010803120c210411090c0301060206060a151101110c07060e03 70
    0x2a91001c01ca01c0964000389004900c424a42c000034002e0503200314201154026644507065400c040c4040820610480c9020300c420745894000380c1d0b18105010340507001c2145000701a1108660b64024004680028001d1784000d0f00c500c083d5180101340c92001c804180444018424454413980582c0105150354090366142c0c8401c0224841380504004240200e0304803250301e00c65501c21901081c140400f4000c00e055011008601c00b0351030f40c42c8001e4036225403030075001c1000342001c81160310564004100d5850217181c2149d0100c0b480e0320f11503100702c50041d440c40a42d01e98500c0020350080071220011602c99008001e5a0700214020b0084440300a04000c0c0b504080c0710038600144016001d600003441d80d456041200c0c1c0419290309403540201e03548100300803141100041c40c16103080364201c03144e03a601c2500b0b10440c1d162034025048040c1c41444034000b00c0344078103000e81500c1c0394403002059600c1002c20070820b5401c81c01310f0b400701e0340001e0f40074028280d00a90008018030114020f002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 322670620 1250 322669370 322669379
    0x60702071203210b04020a02100f06061707050f19031d0d110f010204080601030c0b0405060306040b0f0307270510050411120108160801050403080a0509100509060702070609 76
    0x100d807a80325100303661000d0b1400f0f01d5201550307071244004480192007550303541000c11000351101c074402e4951920601d4a000010455400e100381e9003038500e40d88a5880d14007200d03403002c50f01f5900409000030003908106c60140000410041c15402852500c02d03c0b2010909601a05aa25000c0401801c0c111174151034901500054442c40c100b540341410003840322224101d070308090001c400c1c0d60309580005400200303a000000c02074101d130300440d60043d0243d280c40070300256220300c1c07140d00d600c0f50040c000321700d441c0781c180e0004607003082c01406044001d90302c1010074148070303540d889844402d81341600e0641c01038115a80c3c420690100408000785d1502c8012604140d8440c02600d02855882d001915a142d480e0119501d120a0310726a0030030350703520b481041d510110341b030034003507082c81151002a0300e040500030b9500513a41510b8030b0480d2b80d41c007502200204001464a0182d200b1500b01341742248407885418007465564010f40000e01d4481400303460248190700140820110036410803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 322671870 1250 322670620 322670627
    0xd0911040b0303180f010c0f08120705030403020304150e090f040b180a0605060d0b0a020307030b060901020309090c1c090218160c0f140f0d08090d11010617060702071203 75
    0x44c03480710407a611091726090b000100c1322a07451391001040b00315800544028000c042c030107014401c1c82c0c02d0a82c652940d600d04e003150680000c0c1c400801503807082c04140404000b00600c1c03404c000301860700c45841003581d07000817840c500540740e82007114503200a010500207240c03607599100301400038000242210000040d65040d0f2040051700842da110089607281c3d6855445084182e00300c0050b00701c03801c00100b642c000303510645600f0701207843c04442129504000c0150383e07080b003058024508107619038052012070079008120341030080040084a4580000481c0a44076000c3e8406c00200301c1e5003407041c0550304180e0074a007280d001e0150304002135400c1c103805440a08480c7e141184c0c00201c1d910740306030400613508005008845018910308400000904080d550510f80c1c11507511000700074091301c44030780c1541c4c429020f41003d0240ea101502540d9041e84001c100c40c00010754694075015a1841480403051b03090980280c01400803655041240300d000c0c3c1680c29500d5030450407682d018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 322673120 1250 322671870 322671907
    0x30f05060102011811061b0d09080a080d020c0f10140604050c160302010905030a0e090601110c1203070209011401141305010f020c030706080604140603210d0911040b0303 75
    0x402c164405020617501c4c1d1110381c1034441c1c04072a03a403590000c240305190b69842d40e10050307812000800c0c0d500001340403070b0300044c1c17040d0f510b400100161a0442c0080d2841c080e52240d51051001e214481001c55108070030005259000d0708000005110001c40e080000100310250013140714a00b040e003441101a107440480c1d151000c0300030403800341c058a150030382c094000d100300900316010220f501c0500d03903040604c8135240710301203131240c07001e5407840010340b201c0c004086410340c96400b41b05444c41c141001c5140350708001440c0c04aa0422400360f000400c401026001030340443c8520a1002c203550300a0031031081c40181b860f2850a025030142c0040300da442c41d100745ca0421842044d9603440c10b00a0000240e0400d018080c3c0712282d44a80780078000b50415250304d402140380401100ea0030044c500d0036402800002c2c0640840c448803400380407a600c0d4032154050340c2000700240000f120a91084040349481a2400c1c000c400d02d0f10104001c441030014100d010790020858030a90031702c0070400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 322674370 1250 322673120 322673123
    0x1e09060807050f150f1201091404031803050a080901020705030d0e040c0311031303022518240815040206031906080f030322170703170106030f050601020118 69
    0x590540d5000040091141c16508180d804e03891400aa019820200000207010b140c10114111076966a210704207400c032043d64014000c0c9040c403101140c0000e104940c069420843c13078804141a540b01e859440c10104007110031228400001904581c0e5601480080d000f4031048010f420030782050800684050001c60803d48241d81e102d8545200500903271006100300d00c8071945527213030303d082109491010845c20f015000b501c02c1c500100c0400901e403130002d2080e2740f903003603080c1075515001c2200d2030400400e540c0034085495030380d0b0b58499075118803014280001c1c48484c0c085949040100b5041c540414210034405a4810800c009a161030040725001288400c0900069281c240700c040142440e40205407540190321500300c582c1c0d03000000d1070148054a4030087d0200c890805246034200d854002800c1e842800a4000c820081c40d0191100ea4002d092140c00340c64001c0350b60b8184003007600244d021075520380c00102044078034410107034401c1c0c00b8002009040140c88000e100078032118130 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 322675620 1250 322674370 322674379
    0x6090612090f06090201030f05010f17030903160e07020d05090108040c05040c0905130c0e0904110405070c051e07090e03041a0702120111160201181e0906080705 71
    0x290124100e03648a42180c0b500007102c500e0101c007518080700500340021043e8002402d085c0c0b11410004944500745c12101107081c5041342c20b00e41215124689011900210240000d00014900344ca05001c491103150300007060060003130602548601c116000750000003158006a40140103e030441d044640c03441c002d0804070640d070341d5440c101100e849541c20194000d4200703400c2c00e69442c0c20110300c40a4a50440300f00350303014450201c4104640040d8151000181e4503100350303001c0d0510405c11600940a0020301c04803251590106003501d800362581800a240c52030b0407414860188512422441452a54480c444031450080d40d58007482c01032280c4940d55040101c5007060400440f001492065240d481130030181203112a17941044209034042c134a840c000f01000e07001841a03021320488514601d040100c00e4000b120400c80601003281880320300d000d5002c1d01914040c0040042980d034102c02d1100c071b10010180c45c100159032191005a042c0081840307013446c085074500c1512807d4a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 322676870 1250 322675620 322675637
    0x12030103030c150615030b19050409030c0813140904120503070c0b0108010c110f061f030212060702100b0306040f1a010b04030302060f07170702070b0a050405030f0304060906 77
    0x52030300c3c03890950007041c0c59491419100103920071003d02c1c40341d1101c2e0b154401708144c1e0070000c14403170340c14000c0840c0c107480018030302c0922880c5440e41c09103d00902900e02007060300310a60794035409602c500c20310751440111620401c03922080000e81e0f0074110080d03c40554904207a5200103603500c1d460001410300802200045403144075144040e0364903080107080300907595030f110325030090050004190010340c0e0051084980341d00040e1075145c0984060003420b05640e401004000c0c0362500c0d030802c000e504841000405603880381c1c120000500d00c0409441141805d12010780b50102040540204904150144a01e641c020035140c1c0d000d07411044c900010310142c80e160350000c00059074100c540c0f070040c001041ca14180b0001d0402d50f442a0225400381c0c40c1e030070365000d255600f2200700700010a0084488000585100102d8018499004440c1480d803200c0c2102a250026000e02c0002000404c042006207020821f415000404001a514040c1060802080d15907140910070521008a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 322678120 1250 322676870 322676873
    0x30c0103061d09031309061e0e0c09061e0d0e060601020307030e1206011706070215010b0d062106060b04080c060c0715051903050105061b01090c080c090912030103030c 74
    0x1807003107805c031040c80f0710080045901c40260708000e000502804420344030002d400c240308000043c1440549180b00103205141da074030440035001380d0284900b1500b0180500c6000c00e069080f0104598034011200c049845080c01040c480407140103c403c0c82c40d0350f10107000d018041e60040106e0708016054907003214600540b0001c1403c0c00c1d0303260611040c0e84601800001c03820b100d0001d40b070f200001e86003691030036219807404a82d100e40ca000c021000c5002200100242e500305c0005018005400384c0120b4056651209400c1503183d007682000b440203907128050070000340d882040050402c100e4010704150402490039a1f507203800c0381c554000c0c034000610140281041102d08014045007500300710505005400616a0300100c11110f0041e050014001c040ca009000d102c1c181c1d40060500341c100080b0140d1500884140302d00807402d9503030307604100c011890940301d40001d0203d250003803420901240c24003440980051a01c0d10300c0e0030101c8070300d04400c800411a07044035054608110411010b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 322679370 1250 322678120 322678123
    0xf01050d0b06040e090609070806070e0d1b14040203011208030405070902180405010e1306020a200a020f100909090c0b0c01240302180c070512030402030c0103061d09 73
    0x10459182d1001000c54001246000c11403003034800d006880903141c0036100e4144190351403030a0f0040201c1901700000080b9014400c51060304d414600908211710f406c2d847d200d0701c070000b003d0010307480302038422070051194401924103552148002d03582180f440d8541030130b05950014048000f00300100000c007080601400b0803c1c04098040c41d07404668a8420034606001c0142034521240900d0603c0c1c0006098411406400d1050b81560048030f40850b482d40c2e100001e520a28840c014048131606040c412342c000480803008805e9480108603c42550040092640c0e03003440d2907124085c0cd81000d80302070340c07180007030003114603648000c9022521403802a0080348650440f00d01000081541380c483c002c1500030010905c0c0003440c580d0080e461070420140300d505c600010350000003801000c501c5003501714100f03600401c215081d81c02c240b00c0d82c0e60313182800700801001c242c20101001340415460144503480701c255007400c041040f549808903086043c41c064a01d541088003400c00504041c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 322680620 1250 322679370 322679381
    0x1b0618030306041d060108060105041805060403030e010e1608010e0f031602060d1806050a0605060702061303080f040e0a06060c0b091501180e06060a03170706050403030606030e0c0f01050d 83
    0x4a101c00d95051b5030b192110199552400d1082602c100e040801c01c210048a070748007100703142d4000010b44625615601e0640c0a841340d0480703038205640c1c0c2c84051720154407e005c1c2401d403a0f000c030014024280b60020883c2995025800104250030400052800c4e020000c225034100c1c482109480c40c040d03190000401d10301520904000729402c0240c2d11801038000011001c900c3e1003614200601e8030f4503444c5500320703880d5004594101c901000014098a842000b0f024480c45c000c0c01030703117000d440ba83c4601140c0c01840001c00140d2010030103020300c800000e0f54a6000e403c681c0300b00011460400000d03c0c070190840b014140403980f10100305600c4091101e0381c4010f030440b00011083d41d403419041c2c10b0040c6602a075003075601c1c00c2d515542e03444012070348a0240d00000c0c0290303421800c50316042480890881c41400e845020070a5200140c2c07076001e62407045001c0d480c0002c049143c0807000c0e05035030700d4070301e05800342e0020911040d05a0716107502415189083c40c040343c5414109490740300500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 322681870 1250 322680620 322680671
    0x111030c07120203100507120f020c01020c01091509020d02010c030e09040c080106080a0c1e1502011409030918060109030804080304031112070504020f0d021b061803030604 76
    0x1991602003981c0841d03881100900740f0039812508200c0301c41701c80100310340054440070700044e003030b40d001074190070142c1040c4075088c650400140f07080080c00c3c4280c22680000340041d803036511000e0501c03e100e06c481007000d0482d0100e800f84507191165000858031101c01000a0602c0010035202003414841c50301034550003405810400c00c1e080030b0a0a0110007081e2092138500d42c02c0007008201b110011803060800c65004c80c00f00707122800c190321550003400214140c0303c4409072400002d102c610810020308141c8085d000000d0762544000d0841074a00000e0688401d0b40c802c1204c1c415130b442c2c0c0341d014020594101c1c4500c0260702c40d480126260380d81b031b40c809004d030b400201e004200b200002c4014800c82e4810b4441440c1d4030000420b014080c1034a9114400b50382001004120a00b440d8001b0160038a0002003c3c2c0b42c920821000805c98200e613141203802605220b05072000700040120713981280c010510a480962001d081c2a80ca100c0200664062610f0780d00d040049007a800a40e143c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 322683120 1250 322681870 322681873
    0x804091503060e012c1212040b0c0307020a060b1207030812060f010c0b070210240506130501110a021012050604060e04061517011410050a050111030c 66
    0x241038908803000c03021881c0400d8641620b0181442e02e982030512821050100100340c242c02c0740c0038200e00031560440d001e89550136020b21088a0451156180201035001c0b0f007100c0942642042e00f07080d5084080148100807008080060000031030300000c46d402e0880d030082001c03e41c80c0b000c07004190103890701c4845150038404c19201108028008001d44461400800e807084e050381c85004000d107021044030711a011032007400000b00800c8007011011b600074a14012240c0202040380300c00c086501c801c0300e00100701014076150441507400040ca40c000c02c0304440d070710b052900c900a030b80720201192003003c0c140301c0a0300403030301e100301c0621866491940003410301640a0302c008000d844004450041e1010034a0640082c44501e4144190005d40f15242c0711501266282d0341e032007004200a0402c1c183c0740419241c0010f130000001c844081c1c80014000101e00c00300d441099003c10500a40350101c807601595003401039880c1e01d5100e108a0700309103007441a118000892509600c916480340c0c445 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 322684370 1250 322683120 322683131
    0x62202090f10150e0108240d03051210140a180209030709020d050f1003230109140f010b01091d06120601090603140d170907050a080a0b160906050304080409 69
    0x300344c0020300303e0a1010b00707803103035250380c2c0d240100c090191081d14540b015010600c100c0c05098200102c2c100ca209100c5e00b892450403180288000b030852040301ea01d100000000020300c00200000c0380d41c0e0780d013581a51301c1c40e48039040c006070800b240440c800c52000b295011908000302c0c0d0b01001100002e0841e180e00b15603840140e00d1080c040d0100301ca80300c45900705100481d0741c100d0600c071005c3c00c49400400c0500925022440403000352a84c1d0070501541d9228a8180d01040004906041003424030008080c100c1174121002e0a540e0741c2c1d140c582c14082500410000c4108000e03000140585901c402a000da4410000840d41ea6209484038414890440041850341c480d44c0004140c9029541540795a14103840441d40d845070842014005414849006016000030010b9900311090009940c1030300e0722080410501d841507423103140c050340007100503810711040021321a042001008070b203000d80740755003002e048107196101c2c0e00100440000040c05104075a010369010703000301d0350b05010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 322685620 1250 322684370 322684409
    0x6090d02041a0301060807120204021e1b06011502030913090f0b04020913020d062711090c07020102060c03040f020409120f05091c021809062202090f10 67
    0x107420180c05540350213507280080c0850030b040d0000c0c1c40c0c4120b034801d0b1a1082800c40d04d03420b010203500008030319510800030300308003840e5400f13107405410b05101c0040c1c2865040745483c0440c0c509001a8407260118401d0700b000d603011030707012084600c040300a407201c1d154480c0e440d03055401005107100107444c91841a1419081284007480e2074001c500869170400340783c6900b5407241d920310409030300079844024076403084001007440e00260840305a0000700032100420328406c0c40c2c5000b200300f00b01c400300060392a0307c1c1a403800b00a40fa4001842120301c030300b000d0f46980081c4d42c608014010140907100032000038100400030703440e045940d5000d4024842c02600d80740c00c0d6103580c5240b2a0502081c0003004c40491760384904180e0326002c0004018440000a0403011210f40d0144032099130003a01240031300c412480c04031800e5020b0518000104401d1420002d1405d01410381c803240d0039248204201600540e0718942900e800070640d4092800540388c4041c1c0b040040200ea01211b1008500c0b0f00401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 322686870 1250 322685620 322685651
    0x506070b091203180c01030513110d05032a0303060d350408011802130c0e03070e0105090108070617060f040905010c12020301030503030a0e101e0c02030307020c06090d0204 76
    0x2e00620130f00101c441c10410302c801901914022504221144000700d00c9201158410303900080118015142d880e00314165201c69080d1b40c00110702214510400040694070f20700c01e80441941c94000300551b0550a0120010b00070140e0444090114240803010f440780d44840ca480c0300c0d0702000c0700550703145044c2130f40291549070030034410304c1c455529054412426a06060682c007904d640101440c1c0301001c6d00c0c00c200000c18040780c9100800205044941c855102003146078094141480c013501c00b517151500f00516090144c100a5007604203980407c400ca81018844140a00344d850481899440c20301003580d000400d0f04007580a810044614240f14042d0b1001c10003400c261b980c0100e06004144c3d01c0280d01c402c0c40001c010364003c10000701d60103a194024025003030b1007001c1c2c1d030b0107140204807101900c50302450308001084441042000d4510307841b410708881d907280041e40c10351415000c0651038124920540d40203800010310035256a982c0220604040e900a0081129010108428 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 322688120 1250 322686870 322686901
    0xd1e0c0e0108073209090a0209010b12090d0e01140d1505150721110708010c030b010809060609060a08010c0201150b030906070309021305011205070f0506070b091203 73
    0x181052008190f1204004500000c90340a00701c0c2d000e1069030340610803050190a610092a0606c14010300061800595070086a04c1c028007404030101e480e08500c007954080f1030000b40c00000d00380d022010700030b415034000007603200c2c4103001d00300079a1100c545100d00c0858400d089081441615040810000d10203030101c50080d2041510400b10005008080ca00c0500c241400a0300d200b4180307441c0c02411400800d50740c20404030303142201d000c0c0c46440e0030603d400403c0d0024440c82e5100d80c0c44194071917041c458003101c80700c01d18043d80942480d50110752104070241070a805074511000107050780c0c9503c84000014441d18008101213000c46400078002c1038441d030110040e41e00c01ca40000d14211382802d4030b004190400140140707496440c0c0030b400500f0f407110100d030003003104404a0001d100a100d00c0e4000c0040900b01c401c0f640b030501c0c086080801c0d9130015526020701c00320a1005480303040a81d0360303160380291040515260380005514140a09a40d055400800010428101c000040d00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 322689370 1250 322688120 322688129
    0xc0923091e150c0c12090d1202030309011a0a0308090d0803010f050a0f060206060d110409030c0204140705041a0904111201080d0507020112140106030203150d1e0c0e010807 76
    0x1c4003541e8a41945800e514442c1301c1e030f0281c00d580101e004da11040440c500038103135158010b2a0365904119942d1701035680c98501041c501680022042108c2111300380210011203014100301d00600300ea24000503a01d2040e0301000c3c19001c0041030940b46a03e800c2d890a65041e006a110768403036139100e4040d5240c08003409000c0c000d034200100040d01103042c80000d401c0c0c0707a80d50058020b640d5401c06003d1147c415400c2902c0c1c079a08003008a00d151102d11581e05094040d030b41d80d492286c003900521042d81c0c031010007400348556003002c00c54090ba01c1403c1d01d0903174681301c40c3c02c44081280703040e1400a000e400c2000343d02c245060a0030190001210090005610007403060301c140e81d80b411516100c4035060100004110108070820041d8420101624800a095400034085d200c01401c030141c80026007100c0f001c6a070000c1480344050b240328008164450494084040f850301e82d031245100642130b00c140784039000b10300c8020100420100c0400140c10624000c403c9503a40f25910340c0d40d505188507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 322690620 1250 322689370 322689403
    0x60f08010c080c161b060e0a06050a090504021e12040b07091d0601091d0402010318020a09020c0c06031608013804050a120c0923091e 59
    0x20031454481c003680b810b5106080c1203400c0340c2031412107100300604038030503a4100c1d0540b001e072040d100b2010400c04000c01030136159a5140946801c02d050000c014a582c111000340001403100ea85426404160f03c400c0c0e903c10786002d0780700c41c5944a15010342ca14013440442c24100840e5451021900b408010b2080307000d11440b401a8603821415030b44182c0b02d002da4080c1c1f6891000c00c680c112624108150000c1c0d040c034145841d02c2d902d84c09120150f8222070104164a0403c0a100c190360b0b142c02507542d03001d02c09120070744402090380080d20190007841521003054010540d01308400d000d02c0441c900600140c141c80d9680b03030000d04480400ea6440160011422400010802d08400d80c10490911402e20f00702c00b14102030041c00c2c8210b00d901c008007100301d13400c11020071152242a45c000041002082c911001c00052410f05a0400113800200a4034a480d0111609102c0810b41c40d02c3c680907046440029180c100700d95080040184c2046c140007803070f038070302005017400013120340c0c80ea1600413 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 322691870 1250 322690620 322690631
    0x50a0801021306030212010b0708120a1b08072c03010e060106080c2106040b041b08090c0319080d020a1d090c0319060e1608010605040b0703080a020706060f0801 71
    0x15404e401324010b0b420b220380601c60704001409014940801003a129004814183c18441d841014a85080b03048131503000c0551134455113088244103401c601e054946605000ca840d00e01440c00501103a04a07807400d4040a606041400c0240c6c03180c00309444040c080c00a10010043c040c20941e0340d0b10030b1082d0350002c1c10740c5001803440344208040c0c46e02c251488042c041140070845550b1020340c40034008a40c407035a58000c00549640b207201c1c1c440c1d5980d8600030340c54242e80f801e00213414140e005000b40b0320358200d4240e20407107640200b1950900c003040b0b03000041440d01814030700024096074a5254000780b00140c102000768000c0c003154210b06210b1880a004100442884038040054a40300301c507100510128100c0659812508038009501a00166582e030f03c3d0045590400c0079110f42d03146e03030110b1500003542c81e44179041c94050602030504d070340780c185090a03400b282c0c403800c840a01000b5980c8081004024540c0460708006e801c40300503c11030741c03910300b0600f1014130b83c4911403841d0f2804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 322693120 1250 322691870 322691879
    0x3020105101e0608070e0d03020c100305010e01030b040f060c030603020f040209090118020c0613021008040308010e07030615020f010b0a0f090b010302070b0708010503011404050a1209050a08010213 87
    0x5082c194210507200510501d60b02e400416141c80e00c003d4020400c1c4900b0305048100780c1c07214800c01550b0340c0698010240c080c0c3c400e0031b000900208520907410503003007a0060140700d08510300381e41125032050110071195264106051460517410004245c01e003045c1c0c240034016030640120050301c0c02100c1c1c0040483d040004c01040b0300c203511881c0d41014100d03004208801c509058800c48025031000035183c028030804107814594103c44020080254212840c15414821403120351001541401810341c1400e0f2009840114148500000c40702040c4c0005c1d2098842d8109074000d005494003030a10030140c09019440f51003400ca695802c0d860004181e600707150040f03c80c0200da407183c92459101e8106143d85c0c003c0c00c5103000c3c0b51305150302082940700141001400500c10703100c0e507075000c0e110750402c0101400d540c3d0180d45034010401d05828800481c42c0454005011a40000c03800ca0846001d41c05540341c20b016880241e100018041c00500840190000c01d11a250049490912501d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 322694370 1250 322693120 322693139
    0x607080708041e08130315050a1116021903110130020c0313180507030b0609010c0201110f0f070b0301031208090102090402040b040503100c0e010e120a0302010510 72
    0x101c40240a42c0030f600b2a81c45444803100f40d4a1101c2d00845440307141440301c1c00c02102e020080d03441101d0890700300e80c03814140320582c030503030780c00800c01c0f001408000b241e50394282d61406280304600082c0b880d010a001155580c0a01031880743c0b4803040d95003180d42da41013407444009448a994082000d00000c007062051110760b50080c0c2541202070070005250b029038000940180c800c0360010b210412411800d006217a113074034001c0000a000300342c0500f145886100f078417406003c600500d4200780f552009036640c03100342d03012802c080c6014034a401250004807072038088810165464001d00c81d81660742040441c038a601c5989240464003501d40d541c50802c000d200900c4007824000d022441c0e00e4009114003440d0360807c0c10600054200501e40c400101241d00a62201e80085400a8100224101032180445402420f501000074208031200900320344840d9031a181001805c800c10207603507442812503601c044002c0100c40345060985006402003074207039007448070340325a088001034a040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 322695620 1250 322694370 322694387
    0x60b090906090d0e030a0c091b020102070503030a2406020102030a14090c060a051e0403030909020306090402060c010608060405030901170c040b0904020c030a0903110612040b13120206070807 84
    0xe82c8002010180b58480d011100b50302000701300c41d818011064294089010840c541c0044c0c003040c140010310410ba29103614811440c52686003d42e401130100d0004540c6c0813050700d0384050300308400301c0c8420f0700c2040c40b80210b01915084840403410000450700ca0350540c0914401c032107684041000c441041d89810111400703e403482200d42c00081e02141c2d9080c030501405c02082d203420601d0034031303000d50400040040c60000080010710041010401d2503400b0320001e0003000e52210861940c00c00b0004103280030300041001e07000d9100010310045402095104e20002c141200642d41c05080c00e250842d2079a10854143d40000e40c04c24101080d100c0e000c0c3d1880c0121401d00480d0320b418a40350309442c00750804090a07034880d90030720169a00f00070a200030b00c0c41302146d80c0d0701c0e0b10450840c40c00342903041030b00c1c03030190003520103010892025060401142e003207074001c03102d83d5096403a006140e201d030480780310060000c40c8602407204040d40009159025411988a0441c141d4580e00e08441e140ca = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 322696870 1250 322695620 322695631
    0x12051314062208370e0907080112171c0203190203011206270302010f0e070510080c2203050d080c0a0305060118140301240501050a0509030703060b090906 68
    0x10440460305100862141340c0c00120030402e15504d09440d503400c0d044688034039038000070652010050800d45800aa0168815140d080244031541400051a268020035000501d49490b07448116204a00c10090702d0b42840285051032070342500d4550900650410b030b0b1404188441f0300f2106100050354002d03a416265605920b40002681d901c07004090030034003401c007101020b13850394021a0007802d4140c444035406500003250310f201d129aa01c0495040c404402e803d50801001803003103030345240084104907041d28007100f0603180c4d003031000501e1143c103280d00c440000d410319216480c84c00c0790344072080b68000e40071307621891420b80041e19005812500c1446002c07080100c00b01c2c0358001d90005401a030103140410200d42100d0540700a02e9450f0015130b03566101d03144140551509004105400917404088800c001e90306402c441ca81d83d1a014060612402281104446100f102600e02c2500020111402c00c2c5d0f4a0400310000c1c07003820307050350103005c0003000155160000250140181c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 322698120 1250 322696870 322696883
    0x30507090f0b0306061c0c0801020f030f180316060608030a030b03150705030c2107200c06071707080412021518010807020c031b0a080706120513140622 67
    0x402ca0361b210840c4005041000c6071040e00c3c0650109aa0030700348090580510109403a0369281030524840b03240342801071080c0b00003110381100d080318050200586454001d5040c0d03101c0007220500c0d03d00d018041541113808148004500c1011007907164110310f00c0b1000603402e49448100360601c4102c01d00c6d08860031004202c0401c08540c0035020703500101102c40131084603071103070580300e08a0301d40442c1c00d66004000610156806010003c0c035502c1c060a0045d040040c9842d90551000c50110b0107043c201600380880003c48042e020032440880c3d5500342c0c0117001070703929501d0700200c1c0d8a40040c01402d900902ca203c0c024050601240207d8507510507a00c40481030303290380c4004641200c0001d15042c118000d0b0b0030f058043ea1070802060b441211030071007110310300001c2018003a515810340d02902d140d5004020803caa1134100c0841d20110b04800c40c04103d6548001c000542d44980e16030040204041000c000c24020001c40d6060164004400b080c403009413503020b43ea020f401000029100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 322699370 1250 322698120 322698139
    0xb0c04080604080901090305062a07210905090a0f060e01060219060b040e06060f0f011e140f0903011a0112240b030114010305040f020613030507090f0b030606 70
    0x300c1c2007500134080c1e4883c149010240162a0f584041c10104113843d0841101c5002070b808040600a048980c10101054041410891a601c8001d402c2040c601c52440d4543c10024003008240300f00f190f80e010b0f0501500c5580a810701c010450b0040604a01c1503500b14036107480070462202c241d0005040b00c51944c01800788480040d09009101ca0f0300804491241c1d5451600c54a52074a0145544520100001d051a840c1c00e60600c111880e0740e940c000e2161f0008840d50600da0307085412070101c0300c3c0c1102c0009510349054001d5814038040d80840c00300e0703c40412205104e002c26030040440039410780080c840c252040c06a8944007a00c0c2d070200740851502120380000055950001140205985003c8510340c40384800c11118a0a0b81040004100000050042c0e1621140c90b05160b20280f804110b145010b441e05002c200034031b140288107100005110301c003d0303108080b0002031900807040e602055668480c240c018048a004041128101f82d0444c3c498900800c00b24400c0c540640611503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 322700620 1250 322699370 322699373
    0x6060f061d030c301f0501050a0b1603051e032d012d0602062d0402010809011401170706051306081e0406020417011a040209030106050415030b0c04080604 68
    0xb003c2004401c480404c012500754200040701004441010b4404002d510710311140c0125a1068500c1600424041c00880c41e04000d030034502d40444a0b07003c00d00c9d0340c24a002c40ba40c40c0c125004d224010070040c1e00f0172611342403c0000c0364440114010020031115030a030034409070032074101e0101d07100c050188040303c0004100a11a1584040d1648411318a5100d040c00d61050101505080d800000040c1d11074070810459146a030100d8a0908141049070501d8581d00300310303403114034000c20007030400c0340c01c01c0840c0c04c01000350000141c4a640c600425100c0d038498280e18403445a0100381d504a1080100003e000c1c1d008100f1034140768440015a9591f5060003020303a143c41004e082c0d04100c00d00002e0003880c4c8030071603040300c2c001c3d40b1079031002d0303a00c0c1d2425151070b0003511084004291030345040214911181c0c256403039040c000301500c000d602d5420500001c0d0042c201d80d0301407a0060700707140d0590002d100b00e52014090b00d22503201404191079a0140c450240030b0f0707004000c0c0d85c1e031040e400b080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 322701870 1250 322700620 322700659
    0xa0b030c04020d11031905010803030c04120609080d0e010c110c3001060e010603020a080714040f030f05060a0510142e020705040507050405090406060f061d030c 71
    0x415081c03c5100840d000b110311801c2621070740304950300f824501d80e11403425500c801c140030b00d50051075590300035030030350400d200100e001d841917104140302030301c03031086007030410606804c188141500441d0542d1581600704143e009403908400e0f426941d481d00703407080807180c081c84400702c41c0f6603424014410581c464040c00900301c01c160003c0180d40c415801010114500480905101c6010001258541c50a802c10803124010703040a41894010700200701419800804243d10140c2854140300040c8415020300451195404c009841c144044000c0f080c0161113540808152081701181c0345a6541c011441c12030346c0660340c5050740c544042041280840a00401c00340c0540185111080c414206199001c0d06800d85a015191130000c1c1e1113141c1034051250303000130b080546e0280218079180c40000c0c100d00c524001c1901c04c6122001007014440e0a038007807805080140c84034810315880301d001500c4d8102c0c40c00002c501a510a0341d8110909022412011440c0080c10b8000d1004c101ca1428 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 322703120 1250 322701870 322701877
    0x3070203071421031003050d0c21270305030a050c16030809010507051002070b0405100e032203060c08101401020c060a0c06090b071101020f0a0c0f061a090a0b030c0402 74
    0x3a914036000b4000800800c4051050f0144123059486901c0144510301d0500d032003180c0035074009086001c03002020501c507044035020481c0f0310440480d020050110040080341c16160f007001d0440c0c88041100807205420000504014007540100c50000200c042c403081c00000c00d000042c00ca060911251071154080d20140030914030450990740d42081003110031040380c119507000e0324110440300034001403040c1030140c5401819440018402c00400c40c64483e070f07902c074400b4200084078803625024689a01c0c05640d001440c4e0010b410300c030119030120028011041a10381c1100d001038000001034941c001100031818000607005820401c00324401c10006421115095042c098008a41030004120384102c0038210301c500003445032810403a5008003c0005070070081c2c040c1c0c0c410849400080000c1c016034035800c850b4606400034140034540000e012614150041100381040c041d03a110810300e8090440c0c04c0ca080e60100302e6035499000c1002942d0b040b0806035015000008a15414103054005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 322704370 1250 322703120 322703131
    0x3011107020907140304050c0906060c15070c06150f0f2115090606060e06070308010506090109080d02010608100b0d020f1c05010905010c02070b0d05070909020307020307142103 78
    0x248010b1402c04c181812241e00403601180c035900420f2010380780f40b410340d01c0c50343c02c03104c01d4035020700701080016107580d038010420382c00009080ba800080e07501441000184a81503202d02d09100c0007a14020410904500303009404040900d24008501400d80002c0042110149501000d035030402088100605001e003105582c801c001d2680c00640c1c0600d40183c4011512a400002e02e45203480380081c81000b840030740714840e900030030140021030f40c03003103d0a05641301118600ea603800c0407001a035108010340d000305000e01604a480108903010350051046880e41d200750340510740d0842e4444100c50804201030340c081c1e4103030104400750130200076a8070020005003441c42081c00110018080c0d04440c00c08030340307907911124020100242030003007844040085c00180781c641e0501031507003294003502109034081d80d5208009001d20303120f20a52002000540300031544c074240254001e4076603200036019a801c1c0e6000344100080030002580810001c034127400e118851001203640c1c4516072010700b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 322705620 1250 322704370 322704377
    0xc0a060b06211009050903040b0d0b121509030f03160201142701110906030408040302150a081501020304090209040b09070e03190506060d1406010603021803011107020907 75
    0x19480a4007903414141d00002516041004510705422162261052501321001103810001072107801000002078506aa8681c2c031080e480b0186032070024003c2806400e00340d800000ea10720011518004100010703041b00a00303c50f48150b41300300c074150f681d1082224021165008000050b0406040d584a5941e1042840081068031306010384092038882a940621000100170700c42042a034440d081c0b81a643d410802480f01c401400f100c01060701454150900507840000050708101d9104111006194018841d440c4d4420302e42d000b00642e008010705201040c08034010900d480340c0ca012014180300142d0046181c00d0510751003501075004030b80304940003900c1d00c3c2c82c401190f444840b0948190090f50f29100702401e400109031412041c042e50000e1009c1c800041c0c0046007012400755401401911258a1844a4505901c0b03041d94424100078501a181c0041141c5a05030020442004000e04407000d02031048205422030f40707282000c1c0110a401c000d044014140b051400740e10240c08d08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 322706870 1250 322705620 322705627
    0x8370e03100f02180a0e0105010f0c0b040507090b010305060918030d060905071812030e0f060307030b030715120507050c03070c060201150e0a2a020309090c0c0a060b06 74
    0x1401c4006a403808841e00e141607802244800350a003541c1012034100c2c030b040700c070b41030300519112100307000e040c042c007905040100c3d00b000c0742c601c01e010b1400781e00016480f10200703101c2c1c98a07080a41d264250781c02405134190401d13005c2a8658803a00600e4090000140443d140361900301240219040100a02c5480d0200f40b08240c1c01030f0143c4640401480500c4c4042420320340420000c01c001c900e100c400b000150000001c1c40140301052200910341d506040155000030703c400040e40468041c032009522803400404c00030040c2d4160007030544018180d044070640b58a403828000150b10407680240082c1c000d051031010510107410154000015081a6207051450300300b290469100c0c25068500703a402600c104082642441004200c07404404252501400c02c50080344e2a00068841060f40c0d4450150718503600d2980c042404014000c86055402413840c000a51207412400b502d83c860362384c200000e46102c500314101d500700101000a05101c2c440c41d40c40e00300038840e003540c1035000001403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 322708120 1250 322706870 322706893
    0x20c0c0111100c0305060a080f031b07050d03020d0816020d0c020607050109030503091002032419060e090a050c09011107051003020403050d020a05071415030408370e03 74
    0x43c0710340204120f240c0e0f4003003001e00c1d00f00705114100c6072581c0400d06030382c8140d0000d44516070200903502c0c1004811094082541c4241245240091a80049034040b9180c415001010340004603004410200d07210102191345401c0d0006c8018000004140941c006181d600b800760301c92000d0300d0700d43d4130092071503081004545030b0341e0844114210442c0840c0e400014040700704020401e041c5036100d00c0c001549140b8100b42d041d05607100b96901c050000e411030b6080704690342c907206c0c40702c601000ea104600940c1e5444400170311603041d01c40d00b02c1c01801c0c2c0300b000c01d0000303029000702d92052001003142894200032030011034060100d80b8204505008200e0081070966946002100f002c6080d6030168650703003541000da0074682c0b0b40d0220020342d40118000000144d001c1900c40845105031403000d520b000a40110b140c0551180c081894a02c0010402c070405c840c0328054440242d1104600c0001040d250a0810040c10400c100c4281f100102003450558030441c42021441805410b07100c506162 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 322709370 1250 322708120 322708153
    0xa05040b03090a030810061704150e031c020405060306011b0803010e040309050102011401030b2214061f050907050f0a02010b0906010203130b0c0715020718020c0c0111 74
    0x940d91210b00e5000a006042456400203145400048080314084464a41400900141e0f60b460030580c01118450014050101322810f94031034244146080c0094810840b0454980e80002c80000d801466200361a00da0000392003039406407500600414955111000107580b00620b101c0703204410884465a100010b541001842c02003140c0680010036003400c0c0f501504904044d001903045a151000c484840c4460031b0b41e00b41180d80218910303240740c907205d0b5108510f0000881548001d07074070001d48002c00c11031603d4500c0722174180c0152401c50f207842020050070707885440c0300509020820070520140c0b5110100d15000b42031410210310b044003039159594150041420030001d81d40d5194210f6079400c0a0404503030002c0c0900c0503500c0c00c1a0b8120300d1000c44914001e8158995011480a140c0c140c204040d0000c5d1000d50358081440001e41d4001795581301c1c2c2d0080d001c5103403050742d401040c42200d00035200c6a815120240428054400044a0130302036490300a5003449409c1003481c0e804903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 322710620 1250 322709370 322709377
    0x4020d090c03051f0216020f131a090f13061a0a0b0904200a050c1e21040501050a0c05010b0909010f1409070312050723010c03110f0a05040b 62
    0x841c0d0090030450555944400c1d55a44001e900313201a40104010750740303591840007951070254119554a050110301000c03442c82509100325480c0b0b689800a49030302d10f2040181100c0e030460440d14200c00e03036105e40290180f24000d588201c414000d415031700c0005000b07034001d035003280080f4a00c0d4427002e9148001410303980b450382c48100702c0c00c0b00040984490409028141400b00100c088a07030420083c10714040b00d210746400c1c13108003c004900070407908000d1202d8103252400321108443d03d03a203135986644680c0314032101880d2444108150100380d0318031080d2030071510145c640390b003054941d540942e080c0c801c00d89c0444d255582e540708070242d40e9400300000d0040b82980c000241071000b4210660403903804a11944840703041c0340800139066000140c4100350703603100342000b4001c1001380d4251003034011030f03c001700a0700300003c4072100030b0000844042d000c10000001e00050344401000d60461b11b01da500741d103c0d10300c10804003020704400c000601244089180c2186440d5a860080d40c2c50741 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 322711870 1250 322710620 322710623
    0x21204060c140114180102070807031707030507020c011d040501150e03070e0103060e0f0a05060a060518010303030506010c080409090c05180708070e33040b03010504020d090c03 78
    0x5000c01d0400041c4121654040089100c2c00c00030440d100002d10400e50801c1d008202009440800311407460a08003901603030946940400c11702c0c2c03140750a2030080c2c101d0028011900d0b801d00b00702c0008070001e1090045034000e8000c0d40240542102c800f00440d2460142c004451109074808030229458507248569802000c114500e44002102c3c075200502c240911050365200b98030800003400448002d503420342c110380d07202e0000a11595031448907800c03c10903583c6442d403030283c403d41805004000c101c4511402d000341007081044c1d03e8000b000840251102404c4050a05c00018400203001c0d6000710741080b4141400c918042c19941d4000140d8040c0d0840c11405807100c09000411050003452000740c01c00b11599850031104507143d24441600410398410070810314003040125004071002e101070080a083c02100200d0301100442c00c001d010004514030800e0210365803444203031420307102684e201d440c15602d10391074542080040d40140e005034503020342daa040c0c1c00014110703011080045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 322713120 1250 322711870 322711877
    0x9050a06080a0b100609050f04090314040b040f05151b010e0a06140a020901020d210e1f0b0303040911040503062401090b03040f0303060f080a0209180607050a02120406 74
    0x140350010811307450a64135403211040c44500c40f800d02c1242c0d01c0b00c8115890140560f00001d5101d128241181c104000751010700c070b010000200807440351200c000600c1910700e9610320f04805581c4009100e03c3d0045000e01100300c45044c02880c0007603c0360010f1900c103600c0d000c000b0811492605c0150f0600d1080c540444048d9958081b00342600e401801c201d502c010785840442c1054403440011351184040d821400400138040c002040f240140b10300040e845501c0e410400114520810380d542d1800c007905502480d00d0160b4501c03400340228010341c00700c51000740107142854981813000c0050b041060a03609114414003022500b40c8040010a219032401031b50100105c808014141070b1840803801c442c10840c0e0321000740044180c40085a030880e0380800401d030302c044a03040880c001c081c0e9030008018080416400210240f002990843c0103000b122104c2c0070380c4803031401c0e00352104000422071294200700001980740d4050320240042038204d0042d505180035001040901d5842608200f011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 322714370 1250 322713120 322713143
    0x23010611070f14030c030d2a0515041502030112020301151a1308060403050714060f04034505060712050702011403010602060708090102030702060c0d110403110913030909050a06080a 80
    0x112084151051000c8403403030348511156140c0340d09862b600b49500744405442d8101c08103007000b1041d58001d03c0001428021901c030358590001c9600041241c4040e84030b0340c00c2545c640985070420741210700721511800e186204240e1040565441d4202d211084188661200002a450300904c8458840c070b11981e10707c0e0342c6040510300030500700d00000c00d18241380c1c44801040755490341c0600041e0070030b0705030030441c0c0320310769850050510303c1c08501401c1620988810320a6060003000b240c019069031070400e4100151074034184038040c0141c5402405c0c1c1d41694151400040c000d0005101d50350040c54004100c0080075003001c140d600c00e038009001644048200300031107034481111034020717004500030f6182d8242003500961380c00d0040c050003000c410010701005030140c203520851140113900351003601e80d680da0622451244039003031498003480c1d462001030002449030f0107840d440c2e80c0c1902c0c0e810307800341020301000040c8002811505425520032011441c0c1c402008034580440c80744415030790 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 322715620 1250 322714370 322714397
    0x1809020c010e030c0a2006070606080f010b1309020105040506270d020619020712060e33070e13020a0215240423010611070f14030c030d 60
    0x8441440642e5071080e003080c0041c001655001c19400b03840c98100c15070032120030f066a0b141d544014000007180d445400090301e1030810034103030030050071141d480d070907031b0f56158825403020300b40d440e400b0442e070340020100e5002c0031003406944880c0c040c0b0300614040b0300700b0391641d0114040b54002e0103141d20002c0403c000000340001c1124421b071802045d82c1003080700304250702240050180f0b81c0059201010324441481441c82040514014a820001d9803666811428041d00900745200f0180090181001019401c489c400a5200c0b42000e00c1a0081e04000600703c00304109000d80107134204220070030075484bd030303481030081d181d1403603032100050b500c0c40c0d144006440e00c1503182072239a84540c840c003005228a40003504420003014031544040765a0700b940094000c10700c032500d105281245100b0700340c0001c0c0e034a407000d06842c801d4549000d00da00c04d1300503a076a101584540184039104003402d0210307203401e060220260134064101c44401450000007400e0003070440c1c1060000e200000d06c40b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 322716870 1250 322715620 322715623
    0x816080a0f180b01050117010302061602100c050c09041a0c09100503062427030714100305010806010612090605070201050a060f120f0201050d0509060402010314100311011809020c 79
    0x41c0100024240480720401d101fa490840c1d840c1484060320400012070791040404241010440c019401080b52098120820019000a5500a007a07596120f481c0c21400c03c1c1c101200329a000d10b030081503025a01e002c000200300c0c501002401c0c402d10107010f2000e5001d58403030300010050703450603454168481c903042c424044184080341d51643d0910300800742c458400c4210040f01c000074002041515003450b505202183c40c0c40780c102007500b500ca0b025000804801c40e0b1401c16003c0400ca40b03030318481c56442c0c02101503031001c1c00f80c5400780d00b010004206081c01035507903002041000300d0102e90700d240d43e103030041107c4045030032402503511070040045500700780c03103564050140000c0018815003045407611b9011001c04000340307007415100340001503a0240c010344541000d055010b008900d1300300c030382680303881301920100d02090410780e00c0c488800034840384ca88903005840a07074a80703501c2c41c1c88260001c01000c0b80c071410b101116a10005165000e034212001e405415009a40c0e002104c0740f8a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 322718120 1250 322716870 322716893
    0xc05030409023a050c160606060e030a051009110d03020f0d020d0e040506120304080d022a09060a0b0c010204150c030f03050907090f0e0d0816080a0f18 67
    0xc0d0152200d20803010710180b20350400d03c0c00349050907400221030b0390b04450303801d25100d41c1c000070818000b440c4c4250100320080e00504181c500c0366a4003180103403004203065032500200c000402039040040d0030f00001000340c0c80000d20500034400c3d04803560700740c0046402c64400d0b00d002d40040c0c104009110001e42c041184c00414503180c4001c0107031030b0744050020446101e0101a5100b562944007095543d40d03030714145103509024106032030b56160382d5032680740d55810780c4010381e0240c081d5400d003448006548080e0186524440803403242103200c1c4007044103070700008102e558044001440400d800c0c01c034102811300c11015100050f55a030814003110000d092000c0c0340020031080b0040440040d60012070b140b11032000d81170102d00f0340c1b581e1074100c0c1800141e411081c042c502c0c0080b00b50b403d00540d0080710070b2800c40c205545218941c20802c85507500d044406a41000300b40302801c09140c8103040032039018150050000e27412080c5a140402c0e11031084103080340903815441c03542030021000340c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 322719370 1250 322718120 322718167
    0xa05070e010810090f02070c1e061701061b051009031112040b0a0c02090a092f060a0306080604030f090f060801090b01020102130303200c0f09070c0503040902 70
    0x5842c0c10b190815038100e600d68640102c8032041e46030303219880c0542c200c1d01510a11944260842611a222a54201d400b40c007086e4507818500100c1e4001002c0c1d016401c40c000c01c2805451001060703081100c1520150400039a034444100c1841540300400c009008010030a1662200810a22000d050050410351301c10301d003010030b4001d103000f48102c03183c4108031011180c3d500401030b1184482c000a5622a1004202a4008502208005650000c2da0040ba0182e21840c05042142800030440355200c680d00e071203490000f183c0d500d0340b62900d04680a00014641407801181c0151244440f5081c150260340841c08161b40402440c50607400c0303103580740507001215407130b00c440b45421030090516006101da084410754a207010f9210340d00c00c4d011128075540c2c880c40c0342e098503035a29000342003032806446d040904548903000303422030f400843c50290307086004201511080311a070070004000009072010060280c40c0c5881c03400180203001800050100d00b03801619204400b00e00102403410344d24 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 322720620 1250 322719370 322719377
    0x1309050309040c1704021c05070602010209010f030b010207051c0203160501020114090705010c0609051501060e010215060906030a150207110909031c02040906080f010614280302090a05070e01 84
    0x400b8011030030b88031a83c0d50b010760100c40b40704403100b00154442074021458805442409127860105110341c054008064031002a6100501080002001c8085400c86100a801a04031081c200500c3c5004415804124480315010203c5402680060b00e8116103a4240c41031001e510b108111942e0207114140700d0980d140072515140c903080c03070701d06d4480d8014001c181c1407005000c1d03114240852a4070408070749604c04100d0f0050241032b05035101c2501c091003000b0004500070015000d55201103030541c20a07945810320b04c01340d26102c0030022218801445140c05114680508020445a015507031030a107030360500580d00c0300d10f17040c84048410b80030400c900820309070091000d140000030880d40003000c00c100d10f022031001403944030003074841c560201304904d042000104203214042156110008081c00030002e065940080082d4503003000d07100b590100d2103244440c0600b0311240750304002520102190141030b129070000d0441203086e984150b400756500100b00c0c00680101d20440044000d08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 322721870 1250 322720620 322720637
    0x9050a110402041a0d020d060909020307050618060715060e0f10051809011d0c011805010f050f12131103010605060306010e01090e0703090506010e04050a060b1309050309040c 77
    0x141c000308a001d90703a03803201d100130002500d100140320b640c15030f4401034140b40305021865650b01200094458207406901c240101e410018542c0340c00c0b0119089242840b0840e18601d901c2c0e401c01556801041c411303558160404400903440c542481a0006060100d140c82000c1c20511806010000c0003010b07442c0450b60030310144031658440c00280e894030407242010001e40d889543c054007400040100c0410985071004089844002046803100710070f0a0b81e52704d034407440841c8500c2060b022480b880d800705003444488103001d4807400061980304040364a4074542406181c2501201d04102c0c0c89240088040084030100980d40c1031907402e1001c214000d01500d0309043c0081d00507c0060100e505000c0010401c2c152a4010028100103014904420070180380011015001d8202260300b2512400b4200020030a03c5854040c41d020715003007801821440543c0e56500000d0a00009241e071001c105140042405514040c81d0f10380391081002d0340d20740b0540000d001c16110003681e02418003d845 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 322723120 1250 322721870 322721879
    0x50c0c070812090904030c02030f030c010c0203040e0f0403270f060e031209040905031204030e0d08030a09030e0303070c05040605030a0f0b0705090d060501080705060306031b1309050a11040204 85
    0x10300944103180e00845841455480e1480c054551f00d2290000035054054042d12110042001c006002c0c2107100000a00060030300c4072007240c07a803045010305c58019180b0404241459032040d041c9920502c80c1c18005004603c940c1b43d0041c51000b0300c01c1601003a081d000c14000e917049955203000429040c1170210310b00f4440f5000a40310540c0c08125070301c1d000301240c00706a0307039245d4104242d000e4108060702d1351451580302443c02004212002c0d0003081c5101071510050500e41ca90840b0b00e60801c581a0564607030138506d4001d460301a40c140c4c1000034007440f0401c2e60364140001c0020900c01e103616940d491600080c841600c8196210601c03130717003100c185007020910301d000a242642e17008d032540348140d6584000b95004d000e00b1180c140c101e035841179180300b00003466002078181d4404100b1a031480d0ba03074004100c094032044944036016000f085104143c1e100414804400b01e00c02170240641070104070310441100c170480c0003a102c0d9400800c0c00000d2181d01307a2610404c4905407010340c64103041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 322724370 1250 322723120 322723153
    0xf0812130c150f080a02040506071b08030306030a030c060b0411070b0a06050303090f0a030c06120b03010203070f05030a1409150105060702150a09050604141f1b0201020a020301050c0c0708 83
    0x2075030b24050101c072030000754003017503242d044074090200144840d45600803400d182140c5815401103034400042c1500105401100201f907a1280c00003c00a0000107016981210f44981d0f482e02110f8030b40d2100c0400000f552a402181d210000f00b001040e200c0341203080c01c4091400291800c1840c51070540244181c1d00d000c0210354202e001a1a081d0344101c1c0b00003c0782c0101100c0d40f01a01d1102070b0040803540d0b9074800c0301a1450808407400b4411060684201403c0707100a40d400030115940082080a680c040c0c00619030184529030300003010504000225407e600444000c0010342240b440e070315924024440342d034050201540c4507410400c3e00e5020030000b030202c000500b15000082900010141b0400010002d0000034248070b44480d82c400380380700c01c211750340001032040298040b500041101c589000510611a648400c0c0310722196038941e041c0120301100364110b010b408040005610240503860043d200003da0590722000c00300c0650030443c1c16000085140c00401130248000b80c0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 322725620 1250 322724370 322724387
    0xd020f0c1b03070501140c010f090c1d01030f021201090506070f090317070819030f05060103052806051206011412030d0f0219030b0a09090b040f0812130c15 69
    0xc0c02c0000c0125000c904006c1c050007425420407066007050490801c4413041d400c4950424896141120003d80f07848040c009140301d0509446413080000040001c55044400b40d22901d0018003031003024180380010b00e0a48551002c1541c159010380240084154000d001d01888015032a000800c030f400c5680d40441e00c241c801c003414500c0d001007442001d019212007161030640080c400220501d01035440900501881d5822107445464580081c401c1e50083c00b48034424000d010320500818040c0e0140380030403040c0c4108000082c1c3c3c96002080c607448030042c40310b402880100420184d80340c80f0380340a80d4408105418040c05010400201104000040d100c0c28584024007003000243c03041300100034000d0807890249150b000303012009640c0c06038420020710030141d81d01c0c00030382d4943c2c0c96401034400719030009000e54003202c0010049100e00c010304004074402c03030b44680307010181072402d032540105407041468444041d00b1042003100584d140d00c020b049100c90383d1548200781d20003614106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 322726870 1250 322725620 322725629
    0xf03060f03060f04021e0915042d050f090607110102040b130911040b0d090f0807060e0f06090703080f37020109030507030c020d0b0106050c010b0a05060a0f050d020f0c1b0307 77
    0x7200a022300009907030399041800228188659060320980c1302110245a5400f50200149e00e0314080209001d07524a02d0314a1080d4090402840c840d100d0a400312100801003050442e955800d000100e141400807000b0705415105020301c16140f81404d45510803501d00c444410b0140c03034108410001001302105450b61241100750020741d80201d400d0400a00c68a0f00005110483c00641107041000c2c03a0b000ba002d032504c0c0c104542c160702c414031ba200e59604055510030042d43c4108810400121190003c1a402a060904506100301510380c00c04040013401c0b101081000580c0b14500c50f1270f0030400c0d1110b400d0701d100a0010f0401620301400910031024040c0402c032035500013909640b40e8141c86100030b07510414164281d81d45010040ca1500a0b805600c141c1d401c1002295540ca024100d50042c0d80000b440702d445d10085040a927405842d0b41100001d005040c80407030010303a031074806020700111040792559907880c61a030450403e071020090030315411a80088010320348002036180c0684 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 322728120 1250 322726870 322726891
    0x20d0201110a0b07031a0a0501020309190f03060605120303220501091a0a15081002030720060601032307051c0e0d0f05030106050f03060f03060f04021e09 68
    0xda001c41002410252602c0000d0120144041400300d003035031551050000859840c0b2110313400c0c852408201100540d482036500680c003c0c060548149464000e08480304400c002c8030303c55590b1422049542240c17a801a50840ea84110800c5281000f6400e18220b040c000091032071841c0003040e40c0a41d400501c11007900c10540004034003044801d520618409401200503036001c807004000c480705081c200c4a003040c0300e09000385c2d068035a18450034131042d101060058606005000303c101c000b0342004064200700a44c20b1740c00d405825409c0904000d02c410003001e06020301e0014005070544a500342c00d01c840b080e40006c07a110945210f003105400140500e8078030390701e08011402070700740d02d02215803050292828041d410904d0000440a140c80d220380c494402003000f81c0b40c15281400240b00e0000800c80410075070b40070001400013140c0c0000010b04d038000040032800400d1070940c089580380031403044031061000350b2600c480340580084c1504445940c0b0012480400c00c150000f501102d5030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 322729370 1250 322728120 322728137
    0x1a0304170f0f18040f0501030507050105040e0f061c0303020703080c031e040302031c060503060a29060409050405250b0703320307081501140c01090803090109030e0409020d0201 78
    0xb00c0c12080c030104203c1c1008105200c1c4010081600d0001c207803c0c40101c4040c4909007001419500075016901119031440f0007085581d10046941c40c2000000d06c85540030741c54550521104140c8154004102e0013544c0050302d1340c807079250141003c0d03409052106409414400c0202e280700039a03901c8145800c0d5040240551660700d402d80c9140225a0740c0c039164141012640d10070015980120100e41f0201c0480d14603444659030441120301003a4018007440440620310788100c00b10499000c2c902000d8100d601d02580d815122040f13a100ba035007107421740c0000c024000c6034007000c400c980c0c2aa0301c202c21269203604c0c21000d85224480c05400406004510101e0b1041103c00080d41e5a0503a100c508052040140c05d416801907004940c0e550100ea04440421090316003440324890584040e150b41d41010b4500c3c10300d803e00c1e00b2180140c20139640700c0c00003d0000e00c03c040950302419a1800101e17a24003107103006004480703031261583c0110318084041001da0744458001080c60340a00300f4665 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 322730620 1250 322729370 322729387
    0x30f020d14030316080105060909010302152a160501020607200111040602060a05091203092a01091e09020703090e011206050c0c0a02040b0a1a0304170f0f 68
    0x2809040341a00704041d00000c01088090500b483c000740000d9110b5540c0003490780c03607008224680c041c00c40e005401c280e00d2001840142020034642c915005c5070000c56007007142c1c101420040203070f06c0d00b80381042c5087e8010721003002e00c1003040c2a811061940041c41c064113050000b03682d403800408083c10492011069a818a514002820380c168420f00a00c01d05042e1101410746511034070981d001445100c001540382d68862040350300429440303000c1c00c0322940201c800d07034485d08050154101401900700c480104400321442400c012500d0040d002100c400c440007418680c880d601400c03480302d40010011300d500100c141803040d070f5111b52006031a0440d03410f081341d41d0040c6820912040481800200310b140c0d800140d092168070480d42402180d80d0040301d00182c0c01030f0002e18405030301800c007140040c9003540010340040030203030642c0030556a03010b002d00c0b40b403103207070300c40b02076800010501003403041c85080c2001001c003100140d45025102e4401d03c001d441503024440507220301051109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 322731870 1250 322730620 322730633
    0xa02090627010305010515030d02190602220e0106030209180c0412030e03010c0c030813060e010c032a021203070c0b0c0a110c1305040c15020a03080f01030f020d 71
    0x2020454203001030700d034a42e1285441d0340200020b0b51000031101c0850800d0902d885c000aa0012900301540540410307050023140d544c0742d8442030401c50b1403d4086c0161030006c1c1180590148800781c01c1b03204658145098805254a8010b030041000c042c0100701c03585040d2140340c5801d8001616641c0b000c02035a42e603044026078017480d08062141300c04440b0b00014117a04c291880142c2108400130049203251550a0b980c220181c47d00402180ca040006850841088005a0028011503002c1940011000c60500311b07109407641602280d40c0d5440391f082c01140603044404220342d81240103803000c4000002c0c0d5100705c94090120f080900100141d915482141c03040d0110b03a000805c4502070411004102440d00400900d80004140a031a001c1e40000052840c4000502500010402c44d414078500050f020051081d118804a807200243c41001c031440200d6080d80742e405002c0603c140e14004040040c0608800002141c190043c4046139080c40311224841c0e0481d0720550003801880c150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 322733120 1250 322731870 322731919
    0x60903030c1504050c010e01171923060a05030a0f0807020a06090e060d110f04021b03030f0906040804090203130f03050406170f0109020f0409020406120e0a020906 72
    0x10700460280098081410218100750382c0554440c40598042e000d00400440b680300083c0710150000350f010079500c01d098010004181c00141c445100d01140c1040302d40002034031848410700700c04489400030301c620030072500f100c19001041298010303030701890500000d42c2c03404440c80c00f801141c410a261010005198110b0764030503406891211115900c00c03010f000300e0300c584103010000301d207540040c0c0d01e45800b107035550342c071130b800a142c1c6614820841071114052200181c160841d070b0030461040000007090703940b501400c45000440d620b1030031810715003680101801500d120f52080d418080091014400c0e58141c41980d81c1c01a181e035034010200c0c0110a000001400c0c1d81442081c031001e02d079003c0300504c1603038211346a8240c42070480b03940071210300c0c04988102c001903500c0010f0060884540080480014040c01c041c180f40c6c503070a4440483c2c0c042e60003040811220344071048010054020142d005c8000130142000d680079030082088044000d20482c4945a4100040307464002043c1d136 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 322734370 1250 322733120 322733137
    0xc050405190905030d0c030203091b03030c01020304120f0216120809040510031e05060414070e09060118090803040308101208090301060f050a03140705131a0102030a0e06090303 78
    0x521076150b050800a449070b10000e22101c0050503c0041d110300f41c002d0003280d005580c020001d040d030502540c0118000c00c0125003c0ba4540402c00c4a48442c0300240041c5005501800040343c0c07003443c100002d054503c0d008148070541d0840311080d410203000c10b001170200c8a19011402c0c410321146050311403442560075076a402481c05040c07100c08034005420500381c92080b140c00c00403000e6002d09280c50988200d00515640c045400500054503e103421000025078030101e4940f1a1200c1c0d03a45100d51044481c000d06a1068004100840882c520141c0521006104001d4003406469502c3c81d48002031024080c072100310b000c200925496100700d4000d00c0e43d05c44010486c0102d1030328035429800080054800d60038488041031240060b040702080710030003002114454074558900603c005400c0104645000f030304000600c035150249010812a2282000200c0e50000c43c4002007905840c514941158410f0042c180c01c3c40e008091119002c4040b951780c0c0c2c840c20801d0000c1d140d072066082 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 322735620 1250 322734370 322734421
    0x5030606040312080603060c0f18180f070f090b040521010c0c060b090606090909070801060311030d030507050301050d1113050915070c06180c06020f0c010503040c050405 75
    0x500000f4691101c003940c06010110103880c0c2644600141c10564082c20800180c000010003400b0049000ca40032101746282c00b82c9800c901000000e9022031140085646100080c100810440b4850f40400034031814651418003200b0300d4144a48070305280200c0c0201c1e03000b10442c0c011005048608240340caa890100030080c407583c00c0b4604001c18051b550901200c5860034805006e4592806c2c042c03a074400c031700c007601d201d080c48074180c204030000c10702800c084074500590703401180180081c02140080c5000f04011602c04481d002850704d88540300e0f0800c0304041c501030502803c10350240450341100d1045032010f9441285061400c900c2c40c04581e030710ba0150503018040d880810a401c40ca21444032042587c44203601c07188020b80e0200201c03061000508110008800500e080d030080c02985000d40c0d40101100480d9079800e03450083c0e800c000c000d40e020b0910303484100d100b003002240c582420301c4c20030304600f45981d03251800c00513409414800c0d80c440d00081c4142c11388402030075100b01000d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 322736870 1250 322735620 322735643
    0x3020706260408190306080c0312220e01060302070b090303150f011101020d09061d0d031a180609090705060301030605150307090b041512060527030c0c0904030f050306060403 77
    0x240d0203401418035208020342c6002e004996232030340c5004112800c09810380141c03503180c01206482026116800c178140c031100804000085403c01d080c1c83c486001c0d080580b0010ba607841c4500300400c500c14018103011403503008004102812408035890504880145c60b464204d074840c100507a2164001803000c4125032001c580780b004604940c00605815028107030401c40d00503040403078144142c0c0c0103450710740c0ba40082c14006296100740c1c0079002260303212204804200da10b1002402c2d02c420190681100000c62042c090b0a02d0300108480e080340b0304400800c043c510f8080420444d0005110141c00599604005001561211044146c002004042d6030f1526100e602c43c4009041840c081d81c040d0b450a5034985000c0d140c0d4490b5019034062441a440c4a81155221b02c05007100408810007440e2350040403802c2d041080c000002e068120740a036482c0c02081c0c03003113460904410341c0c0911408842c0140000b00750840b0561480f2401d0b86005071f621394941011964a2141e580020300c0f480048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 322738120 1250 322736870 322736917
    0x40906090c05030604081b03041203020307150c0e0118050307080d09060e132013081023100e0f010801050702011a100c060603080703020706260408 65
    0x9501000103944601e0380d51100544890034196140c8040b20001c152500400002e1154007150079120304d40e42c010002c8034685a20341502400310b02100c1da044000d030340301154480400003135042103008105004d0382000b51221024004160440c6480c1c854188041412035090068551001c82c0c082c04001d01114000340d500c0c00c007a940c42445503822070006110b91001b01c0d803188030354081c40d40d09400500030130b0520015003084008101200c103030103071030110756441201100b2100150201b1402c140d100a2110f14195026081c079a2840000000078030f0800080034091485d1103101c4111058078288440c0d5482d2040c0d1601e034000c0c0e402c0340c500b5990280800c446600c165142c00c0c1a20507500c0207200d1a11141c8050307003a1200c014140c034002208190303d03081d80c10000b10403103110b021480c007845642000d13201c240450351217030000d4403c4d060014280e0103058041158200400d034034600108408045d030036009408810b80c2400b160040c0300000b25042c080d43e00242d510501440c4280c9001d06203e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 322739370 1250 322738120 322738133
    0x504030b011205100c080105011b1a0a06060203070c090b060d02030103052406030d03020d0b04050a0f0c050f0418020408031b07080c06030103080309010608030a020d030510180f0b0409 81
    0x201c02e08440c240300d50303000004c602c046401003030590303205515507480303e03420030740151501c0c00300700c00140d0310b0b0311000011000304109031090a0101c00000c003414040c2009841c03c815100140c000c002554010000b00000a8400d01d40104480420300001001044540007580074401e007128101c1440c00400003100b0701001007014620400400402100c51080b0145244036107030844486038103030002c4180c00e06031f60081e00101a44400d08030001405400c5000242c2110300940b026112680e81d04102000306c0514807402d00109958101342c0d0818013001e034032041e1071103070b80685003072510005c0011910320342c43c0e0151400382541c001902e4441b040301c0c1300010540380e0091021300522600d2000146410080303061b034070302c06018002602d160300f0354641488583c0003405002280d940d940d070000320b80303806001400710860950301820400016240040c26038201070240718401c141d51408024462041c1400140c00415a4005c01c445a18100c07000050241031103044e040741c20301403031034104142d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 322740620 1250 322739370 322739399
    0x2090402040b13140906060a0c060b1e1503100909050304050a1404420e07090906301104020301080a02010314040816050a020a06051206032a010504030b01 68
    0x13a44980c242c90030101c3c00810039200001c4d640260071540800131698068850303d81c100107036000340c4022940380f15060114900c10090440f51041102c061000160391620480c1c0c1001d0380d501c0e100550850800c2032411101940381c0c45603003244c584d02d050810030404103200382c40041900503c02c4403201e55407021055a161a80035551043d8900568003c1c000c80d50b21148918140f40c0d2150002000c06041800c29200c1e15502c0a030080210380e000101c0b0180c040025114040903903500d4002444c00101e20241d509503000007609204444400c90918003041009540b407484544100d20655103003045a09100901480380e08680004004510307180d002500c0c525443c402c0c1c0e000c021412000f208092180d505650091800070104200d442d0b100304039401c9543e00f4025004d17251508030356400101d000040b603000c90085680406c040d469408491721441c0c1c011000d5014003101c4007940c007203641c1400100c40105484041d802e070180300340d01c203c09a80141d82e228080a40558550b00c8000500740d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 322741870 1250 322740620 322740629
    0xa0309060b09010303050f1c020d0e0d031116260406120614091803070c06091d280f050f070c0f021c080315030c04090c0902090402040b13 61
    0x24101903010707045050030114641201d4040d5078450030040031300c40e8507070030f603010310071a081800711200e82d00c48001c040e00c010024410152400246414410320703403405c00c4408052710041c14508181a010002481c0844804041c0082c1c8071030504418900401c841d000d24440c0c48070542043d901d103810340f02c0725005106490342501c8140038016944010002d035501c0307004801c1443d101608000d920300380150603079000514654503465001c00505030a1458200c070105840c0145030140c00c11070301e6042500107015000c0d018081c034a5032480d19a12441620203444200c0c030103100c00f000214900c0310008229000309400c81030100070320134104070307000d00825925603d10380182c5c004240c074540102402c0e940300c2d912403441100d0305000d8007003040301016204260009028203030002c0000d66440f000f5841800181394104081c1e42d8002418a000d12510704030340601d180c0f801010204041c070400d07000b240c851440150741e440c4000c010030082e001d29444040380d1640440c00003100e0302410035070400d48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 322743120 1250 322741870 322741883
    0x5100911090f161e080103230a080a02030405100323150f0a05120102130f030c0303050c0109080c2d030702090411060c06191407050a09080706051c050f2a0a0309 71
    0x1148c000b07502005400d8500b8410446c0d10200c2a0000184071201502d5000e400703006880c10706540d100070504480704100100c002940e074a4401042000c458880300f01d074070600080050354900a1000d1070803030201c2040911074020001005240da80f01581003010b031101400d5210b04240172420140071350000142403e41407002c600201e04841062030890440b80c105944039080ca15548040d6907590040550218071354880200402050f0100024440300c03c40710000d150701c160b9140c803810140030100d4000c003921484501c196100a000056403520740d0100e803140e00c5911103241800085500420098001501040e401c3c91002c01083c3c05100d41d00c400c0d400030715011860b0500040324000714071044c0c01802400440d5040c1d02c84c0011f8030101845080101c1496110800c0740d14200d40e039070042c40000c03c0058140035641050000d5220381c000c41000b40300728100315050104120000304903044440c5011b01001001032000310054080c132a00000c070f540d13500c241100501030440c0b8082a0b41c0d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 322744370 1250 322743120 322743143
    0x2121b1201200309010b032b141b070302181006110303160302130306020903010c0c1a0912030405070510051305010305090a05100911090f161e080103 66
    0x2860060140c2c215403a4034000700080724031010050911a0000b0f08522190740d030300c0d6956802a181041030004444c0c11042680b03203a401a2103029601d01c1d6681801d0030007000502242c0302ea00c141041c0c80c0340560f0061504040e026070034030245403001c25407020394803241040c13112101010554045016410f08080303800c800303842e0501512030b400c4500e008640d95000b0800111150b100d010000c00c1da101c83d190161130320030200c0c41030031720000c41c0c0c00680c0d0241d40010490f142d841c00b4820005421480e0821072010aa503480d483c3e0700884461241140308600d00020f207144501344001d420494078420710390380303900302803c08d80d075142c001e402500d00443c0c840001c175140c0c0340504156240002c081490164150501300114040c01d405081e000d100c0c421103140300d002403c1481201c90741c804d450383c00503c412090916543c18040043d8441c024040501400b00e400c10068072564000345200d00302131481c8603200119103009120780003100b080750540405222592190002d8100da0280408000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 322745620 1250 322744370 322744399
    0x10e0a0c0f1706040605130e060a0c0203090d0f150905070504090203060a1e061403070b0f181c061a0f0109050d05030c0304081006061b0b0402121b 65
    0x181000c0e41c200c828046020015400c40b1030303207455415640288040c10104d0210b03502c80103c2c1d030080da13060008031110b4880c3e03860000c5e100e08115490388880004030901c13002e4000308001c2d40701c1c490032110f90302a80410921000b40174070342c4211800d49a110841400303884c0302031614801811602e404403024041c1220005051900d0702440c11b285030004d014101c01d8a98400c42c8008101415100095152065011088036003522900c4002c0013034044414000725410109070805009410070404100103000418601c4421400c0e40c5010814034071205180d4100400039103103282d01c8d05030704102d00c480401d007410403030290402d50118040c100a102012550400c000e0415100100c06000a007031480812803031500788240208a40a07605a83c0fa06a01150540c20b641c03041d0031580459100d8605180d03030612030701c5518001e161038074007071102c440401510b103602d80144c500644140c03003407004601596a1941c1418040b1500000c868450450010074040440c44d5034030300e48a00f813003103091403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 322746870 1250 322745620 322745627
    0x807030905030120031005030d03020c0111030f0f070c050a0f120c02060f1c09120206090f0d050c030d0504230705210703120507061b080115050c010203010e0a0c 71
    0x1c00514010b142052809030144d140c01c0e03660801002070b020034610507400030700b079101440070340380d403c2c0321340e50150740c40021082c0c1c0b5007565002c1aa44401007010020003c0c1c0407907941c01d181e0000c50b410404000c4c0c1d1500c0804848102410303502600e2401313070300249401c00100700c0c140528248200041810151b403500c09135980010040e000c1d40002040292112140801c0014010b0701d17200f0a0031080c030050101540103e0380000d4003102c00074a80300c081e02082e42c042083c0744c0c1c02004100240411029580d5090303d8a08144415060180101c1c018802d40c81c10302c103a43c0034a09500c030400c00c1e4600380c1440c11204607a00c1564450315040b01444291101c045480416520f001c1c1071004550302c0030020034005800c2000d00d400600410074040000b4201c1c00e59000228069940d45c0d40355100e504200c0101d5084c400c2100200c01034039460b09a085e00100b0290464020a0340b114211a201c1d10580b440e20a42150010300c2d4400000400c9621940301c84900075144c00f881080034140200094 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 322748120 1250 322746870 322746881
    0x60207140102010b18102103032009090720071412060f15131a0d030f0f1101020d0603060b0301050423070905040b090c0910090203041e08070309050301 67
    0x160400041005c14008403090a403282e08400c004051030910340d0b40780e4a00a10080c0a043c500740d41039003031820300906505004050742c0243d11030752500440c0140c0a07151b1140f1030f841c1018001c2c10a080021601402800e45030709440b600704109601240311241d00c2e403175541034010501c00c1580d0110003507413410401424002c1c2880d000c014545521003003080d0b482d505c0f00610515030111a1171125080e9160a85001184006040045041c8504060103000f46244081c03581c0110a50403207100031170313848020070601c11024204400c21038452241121803000520030215151300000300c0e00359840b81036102004590040d0020080019140105826100b0a95020303142410001001c0c11803148501070710b03150615041112900d5558008241c1900c07401c49042d10000051410010954414010b01e810408222007030343c101e14064101200185184c0100c44e01c503640407001800708040a20712a444d446e0781c507585248200b041c035102006501000c0c0c100c000440c007440015290070b05000d40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 322749370 1250 322748120 322748141
    0x5010b03060a09020c0102040515030702071a0307050d090203011b090905040305090907090503060a060302011b0b01090f02070203120912010216020f0315040b16090506030a021b0706020714010201 86
    0x18003085141107160b81c041d4100c0f28017a5075955007048009081d0703840d46081c0c030b0b403946021419900c07450120030107420310040d075105030020100d8581c0c0060035140700381180c3c3d0200d600c0c2080c545a90501151400402d0f01a100a4040d0b10b061900c4e042640c070b203904c0c00d00f01d40155464030360440d194a0301d1820f90300150380041c0801d80c01c0c0041c80c05450440960343c1d0008152500e031101556841c0040c1c13908000360b039403041140c2e541380240255640500508111091110340c403a1001d501d41c1d81c82c0d0031480c144258415035540d1400303480c22140d650111808590014101c8600244403800d52800d13601143c0c40c103116800305803803801003040600a440004181610304120b90000b602400507015945202a515014283c0032a04822100300c100307000300d020700301188803031030200021041140311030200c82c180082408200400c0e66000c040300d030f01c92242c0802603118170b040c08400700107001000c561103180c02005008a0440d90004070b85044a007010041c0e01c0000917071005900301c0395040308 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 322750620 1250 322749370 322749379
    0xb2b02030a2717070503040e0a0b0d020108010302040203060406260f07080d0503060a08060709090b060c07030f020a0317090f10020c042a02070807050f0a120c09050f090105010b0306 80
    0x150000880e80003c0000ca5200907007600c03600c0c00c10b240e80c03081d086901a40200d000c0035800e43c180b000707062a80c850a00b400301c0958010000001680002e005e00805200080c411134001000400782d40b03c9400000090001008040d85a500c81d040c030148008800480c110710320400c00d41880d01000052590204c40c03443c006861040501c10b8120303010340c4000c005940020012074000b0700e44000700700040c0701d102d00c0c0e0f03500c800071810180403500341c941101007144500c0707062000c5896418040b510200720383d4000d40c6580200640c0c800300d945680c1c0f07580050180e1282d50b100d0915210035000802e00000c00300c0e5440c841170540b100700170102100c10104001030303015116950b010300b0b0943c0b180b00500d81341110740c0c00300c1e9601405003075800b10105d0b0100c0140c03c080b0f010085000c041100d00d000d04000c07108510410000700228000307800e00d102e010421801005410b090000d80301172807002c1c005214050060b4035080c0140720045000703584019031580f0300b100003c1c1060004042c1c80c0515402031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 322751870 1250 322750620 322750691
    0x40f090615240e090115020d030c0504051c0605190f0218040509072403110a0819020f0a0801230306130c05060703030c02100c02070b2b02030a 63
    0x311285500c1c00e41e00c031200c00e004070342c0c00f000042d95030720310304600070002ca8100b904807a0a44600904005001d83c0e10424141005241000150490252002d071042a00ca11014420300200790741400c00658016003802d18100a20000c0703907142d6410340525640310802e2100c41c03e180c200078102e115480070b480c05007a00e0700d4a2419842c01d904100d0300101518100c5080f80d0f101c44041c0c0c00000503002c0c1d2141e280a03c4040303e00180c05010f220070230880284e181e401d040803120040c16450380100381a640071100c000041000c82d4a6058602d002c030390070803003900c0b4005498080e081c620280160009804485c41c20004000101c0c00c84c1c10482c4044c001c1c25003511440010784500b4240c2c40200d81151182d200415070391290009400807500a0f0340102d0130b0035080001a0401e130b00380c0d044035240e80c1030451260741c2e00d0300006c00744e04803070040102d150744034a000c5025070b08042444185007840720004003000107407520b8000d18017888602d482003112400310605299a540c0c0010541002a402e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 322753120 1250 322751870 322751909
    0x3070b030606070c0920040510210c030204180507020705011b0506040813050907171e04031d031b06070305040506070507031703010b030a05070e040f090615 69
    0x100080c54000070040d080b02c1c20501c0035510601216901c1d040800b41036071340c1e010590050314031280c8200b20103800103060700c0d05007460f0102c0c0e15400002c0701042800008004c0404180b001c802c084c401c0c80d001d91003001180d8403800010041c2d413141c40380c0e40054681101510314900c030f80c81402e005443e190001c1910358500070041d510032003103c0c40102101b2200d200000400c0c0188080d510581c4280880b03a640d007159080017480e40390680040d80903000d00760401c001507410440544600083d0344c3d02401ca41c1d04c0c5030154140703007a080c03c403220490345078060008260b00402e01c201400240c005201009000c0070505030f95030b04081c0c07112201310040f010a42c8130f0a10034000c0040700d000785405843c040d15500410565444030b40200e440380c0c04400304105000718540c007550250355010390180b40d54074002c040c80c09400050411203200d6a81c02c007142c01c0c1030141d0040b091000000e0f0042c400004401f0358480205400c0d14191903541c00e21807490314009086410005455a9285803803604120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 322754370 1250 322753120 322753139
    0x30b15151903020408010c030b0411070b0a020306040b1c14060c070305071103031611030a030806010f02071503091502070215032e05040c0315140607140f16050307 72
    0x45100e45800e0541c04c00c00451210020300511103010b0264901040c0c00c030540090100703c848404440b0a009000c0c400740001a03041c809150b00142241c00c0542c41e51141c50004005003107501480390700400d40c2c0e10703950510b135540f45007984007401941984901508a1a1151603071400c64804a0b10801000004c0000f4015000f400d50940214901e04100e0f00f01008a451351703020303102000e000d104407180d0b24104410b0001215003d5000da000d0003d40015645c090240380307001c0e01c0f07281445000120020503500c208228030060004000c0c0185041410350301400400703000c80150340c0c1d4054858207046011041c001c0300c401c00e40c040d20101034100700c4680c0c001d1a40014280402d03607040d80d802e134228a0060011310194030050035400401a141508100c102c0750341000503401d060a1503000208101140445011a0769801c044042d002c11000010b1051080c6100100804401c00d0f1001141c0030006125460507606000c903181400100300655080c041c80c841c40e50326034440113051002d80c1c0d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 322755620 1250 322754370 322754407
    0x6070c0302010204080625050403030903080d09061b0e01020708060a0c050c060a150819110d0b090307030e03150106030b043c1e02030403140301030b1515 68
    0x41d1000608040c0c81d861200d0600c94166820100c111844034086003002646144080000190505914041c55940c0c0580710b0f110381c3c4005003008001043d0230f106034240e034000742840b81d4000f00030015040c04a00740c00902105d4502d0030001020700358811b88650000a15900340c90f5a0002070843d555941000000b034000d0850381c10070040107101e040394a400c10815580500c440c0000032500000000c0601c06400c80c0707a015a845910282c1c4405a50494034819031b492038005089a0465003140041f96022051070f8000f441c40388d10000300300704544044098040350380310382c0d100942140124105680c40b820000c08002100310b00340104400c9019600c0085440b00250000c981103158081d0313541e4180c0715001c00d4031818900031800c6d10701d801030001c0e00d074a025200c404116000d074080c804203455003281d1040a19a5002001c0750a0501440902064408920307080d5520341e12840d20200c0e100341607a80b2000c0b40745800b034001040c94030410381a50800180961b608100481100b01c1d1040c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 322756870 1250 322755620 322755623
    0x1140309070806011d0f0621071503090b061005030a0f1103070807110102030c0912010617030a09050103180f020f06031501090f05030606130b041406010f1106070c 72
    0x86900070000d02020240103483c021700344051200000b544941102820b103000400d0441050484003c10801d0380c0c0b2864040ea051168019003092015003080051818450b83c0100d6a0406080c0d20700325001e44c19007182d14058401c1d21080b526440360010b01c681d50100101007030108038140f002400441e40380d0311018004080010104114407003c0c0740210503481600c10000144c1544200000c0f0b9800030f0070075440304600b1008501d03510b0010040000d9016080c841c0c0d12407030a0300058a8050340940016019240c0c2c2c101300c5208403484a03201d5036036400760200801092081e40001010341c064030940090030059a0222600020380e036442c0c4484600309022640b018001c6284401c5880d20b901940c0700310380071040d0061480b14007002408924142e0300042071840c403010180700342c1d02c0c0440c2d0280c025030251440b00d561301d044981c240c042c0005100d4160018075000340944000451300680b030151b0300a03201c091948410300412108284500d0210740154040404500c26910035203003d00e01a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 322758120 1250 322756870 322756873
    0x70c030206030903070804121208070210020f040509010b27010c060903020f01090b010f080307020607061d1c0f032a17010905010e07020304080c0411042103030b0f01140309 76
    0x6032846d900c2c1169900550482c03101c4585c19003690040148843c03035404e041c40c9a0074074244078641001c00a6a0312090840c15010940100f01c801c000049123081d50b02800c0d005116034119a118a840f81c00354000b000d00212000c0d045075a803079103c1d2603032400255002d041c1d5802500e05000e88404010b011042c2c800c60441c03141d81041c2c1c111000c00e20503513141e60b100d00120380d502d51424481784c3c0401216046058290001c00001c00143d0301c08089481c4183d200c5804107250813000792403816100c11481040150185c05080c4010210403044020707421416207072100000c4580700114211408004560b0501c0315040102c200180e00c100c0103899482e8510700700b5580c2d4000c40f000300000100380e002181c290b0b02c4100500ca241c994441e48d50b4011001c2c4029820700346010d9030281d99198900d00d9a01a40d0744605151800108100b141c000c5d242005d1184225402d100203034881d07241140095000907d05030214920380b60200000d07005480580d40c90000804100c800c5296034005031400501d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 322759370 1250 322758120 322758127
    0x28090b180d0f05061810051005030304030606061403040f061509020d020318061303031505060a0206070f0e030d1b050717060603060601140921010f060b070c030206030903 75
    0x26551055200c8681c070744600381404645540b460310300e150650140540701ea48604088001d113076000011510200180070b180800c00d511400042421125190001501030200040200910002e03400c90400c98400b507540303032038414416081042e54001503500a010f01b810000500118905402c03d11450b00c50880100415589001c01d400301c0e8411440e24807031540100c00c201e40d500106194425110615024000da844c122050a21181d0710314401420306654500080e41c20320031201d40c602414020386500e50300d4004140180d6260f10032200c0c1c0000401d40038020030105c1c8100741102e00307000058000c0001c0250510150340b80c0784000030368000312000201e46008038508010041c0242440d200040c4c006401881e101c2c00c1080040005000350301100500c405079a1040f40707a11007400130704a40c8c1d11433068100041c00e000c20f0b1094400c0d6641019141441402c2c11f5010f18008420b141c410400142d8070280d101e840d0040c4a406410900c44010800240c02d001d0000c0d0350080c3d1030821340e4035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 322760620 1250 322759370 322759417
    0x6090613150e07170706021624030905010908090f0f01120c031e050f0f1003080318060a06051003060b0a110715030c0305011d16050d09050328090b 65
    0x1382c0500c4440c806070640d201d14420403c0503014842201c801d03001c0c44051052604140701a01c4d1444810020115001000f02c0f42200d90310941c4070b0006281c1c840d0003800440c045090458054021411040c030a8114201c5078030b00b0301c1c1060711010000340685901040304519818403008000407200d400a0644802e107407100048528010050400e05690018240c1020740703040040c0302000305040801d00f01d01082c00741c0121074003c1c0c60f089983c0700390b04a40c0c90390b0302074aa60b424201c0c0c0d440a0310500c225400d100c9806090707000041594007d850244a464200d182102030720301c148078200c6202010418021074500c1f4004220942051000b194102d550b0ba1012621244800010700e002039510b5100c003070034a40c5070080d42d00610098800300400c0002074071004071900d000d0f01c010168000300d40326004150180d07007542c0001802c41e004106d131300c2e60340c105562658041016904c0c0308105004102c0b8602c1c448140b42c0161102d0f031390b4009118106001c0240940c01040300b203000b4841d0820203507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 322761870 1250 322760620 322760639
    0x206160903020a1206062129190c0c030e0f0105040b040e06011d01020c09040201030e030408010b12011b080718090207030f081b1605070806090613150e07 68
    0xb0080002103a031101520f002c1c2080001c850b40d0341c0040c030803140e080e03040c4181f48a501d0000c80150380c22100441d01905035891491030254661100b002d501880420000c041c000713005156200b1461103810301000307800f45011251101c0703604004000c105441190901400c1014000c40d500034103040030380c9001d8031042c94038155000343d4801c244045011003000403030f5900c00c1d48044a50120034041d1880c1c3d0303113500040c0d210101481d002d030044120700001402d5a21903085048041030140940e90b442d034035905102d0280240d400c545020300740c41003015023150740500c00c0502031542c00e100c901e090207010404450ac144080e2000007003218140b29000901c515481c0c1c0d50040c01903180059445060f8a000b81810302c82c0d0150205105030301081060940c0c400803140514400c8409040d91040001003505520b4401070300940382d841054804254102d000a00c9130003140d181040b603c842e5100707032102c44807020101c0010f1000004016001603000e054020024407000341d810358840c0e545030100c41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 322763120 1250 322761870 322761889
    0x20d02060618041a040f03030b19090c03060302040c0e040b0901050603060d060905031306171006050c0109050d08010303080903180405070c0f080301090e1b0607021c030c0b0a0b01020616090302 85
    0x903030b00503021b900808100360b00761042ca65060004c4c0ca0380003040300c60100380d200340c1502e4410303022a07030303121114840d02903c03e030b0100001d141d00800400902c200d484004000c0c980040341d09000d0340c54a10b1003a21440c00c130600750704890004020f0344c03031340d910b580c01c0c04981168400b08440094450228000140c030071f02c0a89024803140c00c0c91504545400c40080021041003c000c04844000080c000b40c1310405403080d09503070080c00c1c01036441c0080755100d4010700d10078802620601490b03800c2e800311903007e800b05040328026030310f8501d07585442e181c82e41ca074815965182010a182600c400007130810740c002980c09422410030100c0e200c856145c0c0e00d4032140c0240101c60f07128000005002182c030b01d209501d4010308490080c443c643c0e191600c00d104502d0000b03894410b12000c200c2400310b40d10a1000c41c100c03c507002e22920407044a207409417500583e03400c111060540c02c000a0f03005180781c4501401c043e0164014062611500344440200069141007000c2026404000c00580c45007941c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 322764370 1250 322763120 322763123
    0x51209010c08060603061008130f150509030f07120504170d021b0114070602190915140909090c030106141908120a031407020a0201020d02060618041a04 67
    0x460100841c0c480142030900090403070b44118000d01c2440400c0e01c1d014a0703101d0668190401542d15146c03215414511244c00800901801010503034000b000701d0b0000e0303c0d050003031940307040c8180d40320805c41c0c0d51240500f08031441c190006204035408030780f06000c0400c0644503400d0491420b6100c90341c02091b441c0283c9030f52216440b0980c4409d01340d134100030309403081e80000030382a006145080000d10358034084554101c40c82011a50300181311246c3d04981c602503507602d141600d040e0002002d40058024031400e142c02c4101300c1e2584030b45018102c1440707552040140c4900d011000000c0220185016001000d60f02c952028401036880c24071981d405844a41000c0015112003010000d68005840341540d54074000c01080181106c00581d070104503031910040d039112507100008030014080e4a115014a0028100b841a000c1d004202c81342114002c0e400d0351480c001d400c1059a407100c0a42c2c046801c404001150b011504885c1c0c2031070340091242d50641140005e03e0000b05080030140d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 322765620 1250 322764370 322764373
    0x1a031b1603020c1e0607060203180a03080f09030304120f030b06130f090603021804080c0105011508070e011b060b030a0305040503100506010c02121617070905042001051209 76
    0x2c001203803802941034124060302c1300c440910094800c021503c14025044000c00407038002c0082003c0e0028107841e03000c4d00348000708503003140c00c1c00d0400424091099640203c1e080390342001c94a486008002c6038429904007542001d11128400c0031601e805041420030105a6903030741011050303581d400103042c81c0007900c03031220784036090422508440c5126444490b15500e400c80c20401600d0341403040e40e9041400d00c12180682d140e052001080c8500d090403500c551901002045070805031280c58110300079a031b2049029518014180c4020341c007070140078007042c108906c03e0000e0310841300344629244200c0000c94030024480104c0c0c500800b11108801003040410700340aa82000c210207030503880120320510217402d00c0400a01401c0c0c0150029000308000011007480c40d000300178542d100c288043c94601140e80c1e514102c030181d0603492411941d0300a110780010944083d00034039001b960880503d0320000d926109941d06007c0d0710801d41c1c18841c0c14402036582d0303400c102da1036100d60320180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 322766870 1250 322765620 322765633
    0x30603010c0504050307050d1401020304051b0603042a210302010b01020607080c03060409080c10060512071509080d05040305060703140411010905040f0609061a031b160302 76
    0x504050039281c403440d000040280c140803c0109a0700000e00c0e404a41082e10850010711140c03d103000c061850811a107000d41c000002d100800100048801034410694040301d10110180c003042001d1100340c6018280f82c0e840c2002513203084030340c3c01c0c007043c442d030210021020381c2c3d583d420706103040340003c0c0b00c1d2418441d454030301090680a024020b4044001d2002c0d04c07075881d1055000d040120043c00400804401000085042c1c54980c03054184d560070242241c1c40700030902e01c00743c3d14a00c6007403a00c1030f50305020b0300050608007442c9501da403242040162141c2c900b02110645103005c4212000d040100d449400a0b07046002d100c1d1102d200d0031a611555207504600348030780360420190180382090300d007201e0814041420007a80303800c0303640301c003030035000c01040001203130086d5441e00981d91041c500322680a42d00300f00d522103422200091030038041540d46d001415140d09114801c13900c1c80c403007000020b0003801c4205030300c000c400070b030400e4a042c06600c412110a00312a200100d002da0b0154 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 322768120 1250 322766870 322766881
    0xe03090d0303090506010603060e0106350633030907030b070504030c080d05030403051c050a0b0306060301060b0a050d18150b091510050702040207080a27210c0b03 72
    0x5008180c0034044c48e060902015140042c8d040103007105118803801c00800300807800904080c40507969041520804c48260559100d0722010101d200f40c40c0c1300d204070745001d03010183c800860900b40c00300401080c07a10348490000b0300b0084540c401024a52a4000c400000c8002086484094041c5c2e07160b640b401c0c0c896043d894a46000a540d80044074940c2c0044207400c0c0c1142e0180850740e019505180c0b403500c5810310b03441020f09505101d541440325040c4020009890829484070100460840440f070042e00d581040c1400c035140d600401103400420800504014003c6006000c0d18014503400248c441420300ca02c00401412002219000b1030101a444d0740c81c0a40140340c041d100444100d4002e050644070040240c07901010740c1e010351180c10780c080059000703000751004a45c014000755640c91203031401a1080c0d200203c50404640020201504003410001c80c80d008212000d004021500f841500e94080400e4440f44080603086044003000400d00c14a8000410b03c034241c558884c20035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 322769370 1250 322768120 322768123
    0x22060905031e090f01050c10050108012c030a03090206040e01060e1e0904030f030608060c090a1e0e0a06090c0e090106020a20040920040506060f0a030e03090d03030905 74
    0x6020b400846a800b4480c403201d580c0d44000c040c42c0702500b400c0c01a554907e0504807410208680400a40305140000014404406410500501d115070180d4420030910750580304440f8031880701c0a0099001780140b0144502030b42c07041401600007407449041c55034855802d401c910300bd8202000141030140046400c0c14442e90311820500111032480c04a90040003080c00c078500100003404121005520100c1070340694010400303400c100c001c1d14928944ed5194002c95441081441c0c012015000000780340729004214018a001e03100c40111100c0c509a9066102000a0709281c032641e0fa4580025690b100c510880403001b503247c44454040f0b640d642000300d104c8050f40003100795040340da145400034524040b01c50500094501600505681c180810003c01210000a09d100c6046507080950781c2c003010701010444007242c09211954800c0148000d5005e55840d0541c031a00501500c0340484c020740108102041c004110703410040950000759a4160a80c429804a941d402544090107030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 322770620 1250 322769370 322769407
    0xd06090501090b010804020910170307150203010e0112060204090606030e0c370803041d060f1c03020a0b0a14090c030a0f05030d021318142206090503 66
    0x4803100300f000f0344042035001174485c00d40100020b115003400c400045551070480d00a002074003041010441a45103400d020396a0f0784070620964090000c40001c41c00c540c00750013103d050f0b61500143e04026440d00c1440900d001002d4402c8809540038400884d09110620400000340440c1e0b8010403030f04078110155003408005102a0301681c005500e440403854269038034600c2e42002142c4c40914941180040c4040c80381d6000140e040c01300250006400759402d0780b5441c407014009490215869680803c50130409c080629030b0002a500103110303004000c09401c000090182c01a02c03c14501566072002c50b131001c44610560a99078200e0041c2002e41e10300312075000064000512003150b41000207955503003c030800070141624909500c04100040c030660300c40a048130030942d1070b078846804580c0c03181c51038052428694005500454030710140e0042100c2e4410907a080d0b0074580700c200c048000c0c100c981c2e25886100f400d42048800190f4a072066034a06405140556159030801280641041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 322771870 1250 322770620 322770629
    0x60c0403060b030d050f09190303020c0907110a0b090309150409150506070b0c1216030b030313060f0216030c0608071d040203041e20040e030315030109080d06090501 73
    0x1e04c01c1c2e0342c03400f0a40e009004c461084c0490502d1a45401c40ca80c00200301081031150140f081d00a0000002055000940814854030482e143e0255984191044545031000342d5a40500c0d03021100110108502d4200c168102c1c02c0f0100349c910380a410408a8441c1d1102c0200c1d5040c0c4500080c100302c18502442a0356140c48007400741c40e00240b070800010800d0144403c00b07443d20f41904080b6201d000c00404580a40300042c5000d5028034001c0004181d206204070b010300824144440c40800b403401004851003d1144074402201c0d0341801c00c120390a80c2130740740c944158821510b000c22540342450140340114482d0010b001d00b68107040b00104520409002c003800e000c04103403003190001ea0100c90040c214401c3e10016103035a00d60520203004170310000a00c40500c18640e40303009014548403c404a2174040090b404000710110521085507a550303024281c5030028800b02d28048121003100303100081c01000031070080c482d5156501c940c0d005040000e0301e0303603a0b2a420404e0084c1d0b0b01500780140b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 322773120 1250 322771870 322771873
    0x90f040c08010b131109030a080309150103231207060e0709020a020316020f0d050a0b070e0f04051509010f06030c050a0c2a09091406130b0a020c060c0403060b03 71
    0xc001810220301340344086040c0250542c2c448100c0c40032060b034101980c4d645a802401c480e04d0701340a040094460b801501e40d441c0a0041600c43c10980c072103007440504a917800081040c2041c018403050a904c0b4001d200310700540140c03c0d00749150405c520140038510300611000030000492003490b0701e010b0b00d079400701c0c00140c014050061620340200a80c0ca8094007019298510a110310024001c42e8542e800c00b980700410a10300400d0007400540308408030312903850fa400948900b4000e80c3c1038210296130541c0100040c4d601c50050400741c02440c3c00005010302e9502c160f1440000542d000003d130040810840a40e20801c403203541406400c0b9070f543c95051403031030301844840060084540d03040103004131400e00c110007064400140c0c2c1c00141d1504004110003251116012406020354040555927401440c06407409813034042662402041030991603c0c0c00d00290b56620042c040c018003145090740d09110003680d150040c40103502c174050019021355520b085240000460308031400c214041d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 322774370 1250 322773120 322773131
    0x705131208040308070c090c270e06060703090801020f0a020715020a06050718030302030c010f02030c031810060303020703020a0605120703050a060b0c010b0a120f02040b01030b090f040c0801 84
    0x4286804216002e9075007203903a16503900c01741e060150806a107944401802441c10b28292021980700068031000c800900c41c0c0d0342000707080b0b407141042c00818022a942c555141020840c1c514180008100142c0700303041152001c1d50340c0740d18a08a070020b0388501c1c4640c1c2d0000c0c4005516038107001381c90181a000140b0051865840350003503850144480c0180401e42e0740300410882c13401070b034074031010161040c0c01c1d0602035242d03d802520b07a04140f0300c0081940c204201000805020b00035240300c0c0d40003100150131a5a05c100394650901f08020f42003c81c00f07408000c07120560700c2c1c003c41002d035000b0340050401034a5031040c050b4200303e40c2d00802c00c108090000036400307030100a15603000907030780c80d011490b505d034115250300030b042642c02181c458000199103969084c040d00300e028084070848210742c406555010084c0070170100c0c50300a1540700c4060039100185002e500c5600461410314000030015000400718000ca9010303140404540c603d40c0400c42000540c4518030050142c0c20002d011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 322775620 1250 322774370 322774373
    0x4021b0106050a1d13050307030c060b0609010e0609220501180504080706090201053007090305120f0714010912030e0a03050c0114280902060921030307051312 70
    0x400135801d030801850401d02c5400b06003208100034801d544540c100c0c003542e5070380d440f5203400740440725200300071600f090a1400a189074648401075503000329040c4c442941b07a074481001c00495620500b10745602040c0c2412920240040c0c400f000088914541d00060550400c0c46ca041c000c400a040291058284020040000c00c0325013501c00c0643d0105001c200b4044500c0140c416004d45810b2289400c0e0410242184001c1d8000020000d83c403901d010b046034455038030848002106005c09081c0340e0245981e4158904c80f0070003006451700b0516030500749440c80d80d407403c0c00031074006580d031641e4450a0a20a10401050f0051402c1c02400c00f041004d0f2051802912840c8006000d01400004900f460f4940d0086d04480120050490032108038540400315011b030580311000140044103840d90014540310b07510906480540041c4290f0409040c4000c102d00c1c0c001c00c8120740c3c82100851001c01d42c181e01000075601803041c03615401e881d00f801614a40159025510040051607142d07107000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 322776870 1250 322775620 322775639
    0x3020a090209010915090f0f060f080901180c080d031418030903030a02070e0109060602070b07143f1207020715080a0e2a0f04021b0106050a 62
    0x1003125141200580c5a150078001030f01d080055030702c4401e030710361164820620705621900c0301064a21a81c2e003440c4444c0c8480d02c50300e542c402800b403800800e403004006107482d801582d02c04e0748040d0b400004034816800c02d1903440b028000c8102107c20103004542400142001e10245074640e445240c200843c1e101c1140321000182c01609500b081182c100032001c409005000310f43e81c00c038016045035078408210b00003d544040510a2002d143c1d841000821401410f000760000c45110360700a0001605052a544c600d030701181080354055007041101c1b100002c06e20944403460001b2080d0100031040410b102c59180031140250618040d100401c1d200c40c40c0002901c003a014900c00d951250b554102c400d80c508825508500c00c201100510b4102c2103502c000c6640c400e050104061000560117011280d90341040309880928040095001d442c40c41148a21a85440f00912200101003e040445d00300e03801100e00c0c019000c04081c4e80105000240120801401c0075900032040514140401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 322778120 1250 322776870 322776889
    0x150423030f100b0303040306060b0301140904032307060c230c0604080904200703031d0619060b0a0c140a02031e01060b0c100b0111031b01020c0a050d180302 69
    0x805001d0390303c0f00f0800c02070300d0401c1610040c6a01074010019070b030303c0b2030030022135400c244201c5050075800c60040d030725802c7c107410581c09161300d81c039030b4840001c0000344000c145040013415000914280101408214140104026880c0d90780303840ca20080341404c44030055640c150407044041041001c0500d100d40040c0300d030f911940200301a5202d13001c040000707020740150001441016500b03c1c048510001c52401000020310079281002210f407606045288030a08100c0c03101035030411400100a075030400e00300b061584240e03000250081d1240030344101d9410650800d40095808000c074000c0028000c1882c55030009072001380240b0b85203500181d49c038462a01c11007540300c2c09113210071040c1400d412003c00380801e08412511441810a155075480d0400032101089041c50507901103940507400104000304003001851034100301681a1042078400c0c0d84c1c050081d9030030002d955007040c060013000c0001e403140e009003050800301c1c00020410407031689000d02d000d07800c010400060f520000c50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 322779370 1250 322778120 322778143
    0x503030c0318040b03011401061b0c060806040b0916170f13060612030e131b0c0201120e0303091002090d03030b190f050a0605041a0306150423030f 65
    0x1c0c0940c510000085405065181318081d011342c00c3c8160344c040384040302c042e10305030303170a40c0d0f204c80d060004805140715515030b109001d0514001c03441c2c14081e051044410b03a07072101c005800801c0003042100031030b0078508112030052650044040c0d48241c207074083c0a410801e41e08081001050915900800b14411f0180c118007102c804078001c00100202c58008400404188078203100c4040030381006840320b041c0070b4000388140381031002e000039a101d0340300e10f02c1410b0303042c0441552035046c404181c3d000699440107a05105072501e040c141070a050180d0b000000318140a10344909010580500d0502100c0405a095005202d00f80d0a43c540600075059140c1510300030070092101e40100300168140c81d9801800041204003140c500034061401e022140300b0307102d0110203607031000100c03424010b034010300c800d01140c96002c90f20407007464007640e00040001d00341c0805010307481140c82c65038440c0d44028001c04404442101420043d02c0b10070320300303070f05074090244280c04039240d41c0c461104116 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 322780620 1250 322779370 322779397
    0x90c1707122a0b030103050c040f1b12020d051303110a03020a3c020a0506090303030f040c0f060c0b01060f080711120a0905120d051c0209040c080405070503030c03 72
    0x100b004480d514800700200f140c1003180c1e540f961030303091198aa98130900740d6030180381014010414040c1c60301c01d0081c010045580c528443c46407601c1210030211b4183d514100c0c0b030f028004510710b100144282402a02038801030b421151191801800d680c1e102469a000368102944c40d901094010a0862229901a080188078040e070391805140c45607181c240007805000014100326454607140c0c04540c18002c8603240000ca6440381085a544501101d95815403c14008500b030040d4202d100c640051240102090f5207485000600c01108954070140000360502029010300c60b80103c002d000d40503a241004010342e52a0024120740310103800311080161003800c2c09503441061043e840074401143c4c00650725005654001c1003501d0a020b064030030441901440c01010002032045507180441d25801c1c14039410007221500341ca643c04501a000d82c007040b0344601542c5070b03c40c44a01103042c0d242c648040c28241050341c41c01009420550280d031041000000707503c000003d560b844c118022 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 322781870 1250 322780620 322780673
    0x1103040b0903031c09111020030c01050c03150f0d1b05030d0e031605100507030e030106180506040605010806040902120703210804030f030f090c170712 67
    0x1000310f4030714400e144090a0649030030318902c8811a640d086003810038021007054900b580b20608101c1039040e59002d04011a091845000543d003c2c100068003c1c002081039074202a84150840d00f1b6070021254418550303c0001041949468000300d42000c41c0162a2105c80781100000324500644a140c060404840c02038090a0401c03c01d243c2c4000c0d25024058601034100040d0240006410004062290140d009216500c0c1c087e03d00540440710002d210100d0610543e074161038581c0218030690401080d100f404856803007d024602c0100705501c807002410500b013849504803000504683d02c5a41020313420444d6a0740441465000740044600141c1c1040c2c62000a8106000f85c400b0034540c019240000240314242a910b000c14140c4124600c0f01e40c82d140301101e001100f1540200460320006088040350311a40c050901070542a10010703002149031a98544981194001000b8403103a0b08107084180702400b2010090080030001540c01016684049140880000704041101c015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 322783120 1250 322781870 322781887
    0x1080a0207021c0f151a010503090703020f01111603020a211509020909060901240902070c0b0c0d09050a0608060f1f02010c020610080d14190e040b011103040b 70
    0x410749200d44e5404240c21084600618101e13010348a007140e000255060100b91900300e5010b0300032a88030b41048000350001601b0b5a081240b8142c0da0404603040188090014400c030300f0810074030448481e66060307080c00a1451041000f41d5480341c00942c1c1c43c41d004010ba501c40b003103804102d052a50300400c1040703070149010081d0010001507070f010354450204070601096103004640380f8041c1142d00c000780b00203c0c4014161040c06a00107018540b8a0541000c1041d00c5096000c1d241e0184107094060495a41c2d8070314080e5500700f41344824040d000711a1024030760b40c0100039100207080035580184041d16065010301400340091640d4001d02041c0b041c0f501540d80e1a40741d60040d00c200e03815038240e07440648001d000b801c14800e244090b1166502040180c61410054811201c10031300030020b86440c02d0003112821003d080002042800784a02c1507490848484180402480d81da01c058444101003044296003100c1d02c9039041c4040c0401d00101800040129001e0b50300f04c5a0440d5038002d81c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 322784370 1250 322783120 322783133
    0xc1009080d0809120f030109060510140a091a0d0608162105030a050d050604060e040201030b03072105071205151918051506100e010c15050601080a0207021c 69
    0x1030880c604c1c481c2c8400180f4103000000a00510b06848145200b0011030740c85400748801840e180141c100480c000c0581452240c0c0ac801c0200030440107482c20340103160362003498595001e0010641c02c840d02012030340036080c552604c40da03401003501d4030017003180b182c1c1c0707803e500803000140c010010714111102c0502510345060345c014408039803200407a40d0b1a81040b9000f4000c1d0000e0310186203060030a03000c548a0320f054080d207019646c03c60f06c4d10107161150350043d40200007928116401d40641480041d0001090380d40c403010311140f82e03010420109070b03d445414403c1c19041b180c50482c0601c1d926011890004501d01d120080f40c6404025469412010701c61000c0003050070909400d11001e000900404000c0220741c81c8100c3c1262087c51104010354843e103c11a0125040a078282443c5500c6100e6003503660104c006043c40c00321103c494171828502e03801c62080c0004191154280b10613540e00c2905c01d40e10008d04035045041044560002c4c0d180074415094204616440b800d05052090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 322785620 1250 322784370 322784383
    0x3110d05011509020910020a0203060a05060d1203021b0109080301050d03020709020d0b132a03180503130e01150807030b1206070207060c080301120f02090403020c1009080d0809 78
    0x468005903440650741d02d400f9020358811000d85005c1c020614804480d0b40c000107110b402103600402a02c03003680c941d502480100b00061801781c0c0002806031100201c0c0b4240c2c0c501c14804020340d40507948044408a94802c02090303c03048046a250050f44804101d0740c2c0b087e01e040d190b046400c0901c0500728101289011300d83d4224024152002030301d64401d0305283d11040070300400392a0008e5030105204107100b25807581032000e000003a0044142e8003507419031101c01c44482c5a0a00052840490907205884041c08104840d541c0c40000d0401d01c2d078002c480c4480c000c111400e030030031196040c020640c0f0a40c0f05105540248103203040802d40032070007600011030600740905192404c02d482890320741d45010980d0110054001c52034041403642c4500c85040705290080c6003289941d1818051240c0030920410a036402440060408010b0380c071404580c0c00365000f60b006069041c2120104007038410140f810030140304402d10104500c030f00100b07100559021034142114240d0300d0b442c54a0a184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 322786870 1250 322785620 322785641
    0x30406050301031b170708070b0a0e0d03090b0f030103170a0203070807031b0305030403080114030a020607080f0c070801050c030412030b0102070906060f030609062d180203060108060a03110d0501 86
    0x8a00c0018198061700004185007220f0140c021241c0440c3e8900300c6c1c411030300c5140e003004009282c00742007110b03a04125000d41c900b035110380360014150b07a0703c284145580c1c108800c1500422400001003007404050350500d107c64881248ed035141c4150824082e40d40d00c900400100a520003042031010715000c1c1d2100c03900e041801441081d981c00901d40188294821141203000c035103103a00204140075800d44224480a010780202540c45154080050300d070810344003164201d504008a50b91050302c04050f08400d250000240920b60030058081c0c00e49400800e00c0c0c41d140f41c1032040001103080700c18000c00e80e00c464140003514031013240040303041c00703400d400419250742483c7c000542140d0151110174840400d07501040b070b050b210700d030407415120180703c3c80d60500403502000d00c202075619601241401c1c468030140800303a0b03540f8210128030f034183c0380d040000c0e030210800c129940c21044095006e54102c47e0080c409045a8481c010300c503001200c54050083e0310849000c12101354003218145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 322788120 1250 322786870 322786889
    0x105150c03040605030412080f06040e0f0712030807080714070206160c0f08071203051b121c05041a070507061404110307150c111020030406050301031b 67
    0x202d8441e4009000c0d45d1065404490080c4074aa01880702889a12098042c5080040c0300b18140c8400040001900025018035607a0080d050503140459041003580300600046008120000803420054400400140b8407400e001800080041c143e900c0410202d0384126006101d848507000d00104026004407400302880a82c0301c00c04100b0700c88825004000c860180041c3c003250394441d65226103441940c8603030213900c190b404040000a0040014000212080307101000307404000c0200d91610b989542008005040055400203501d0312150889091003101c205005c0b41c2455604c400b010a80c2000d035850704964400803610440c0300d84110b540c0280c21400138055548034511322900c2c98401d683c1100e006810a10a0310203040110f02ca50450318521021080c48202c40010307500c0503082902118800f050801e100481d030349107141181000502d590f01c0a00b410010051507005070440c0c04a11203501c1440100708036940041103e05407544016080c2a180141c8140011010f20360040e1101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 322789370 1250 322788120 322788127
    0x30c21040816170102041d0406090b0406050a0c0509010f08063601050d03080f060105120108150105060c0d05070606030609080d1103040b0103022806020a02010909060605030105150c03 81
    0x35162159442c02500d44401004407210708900c002800c0380725900c100924600e0600325500340b24011940d0a80c0a401004049000002c60fa80d01d80400305c2101c04071441d07980c0e0000d20a000c143c52080c1c0c20060554109140742942c01800a030002c203980742c955081003003040000308540c4944040d0800d02101d40c5034510b190081c000c0c0e441c6001d0003200b4100c4002a078000004241c40d1840461140c9501520740e15040c7d100c0c641610a5000d000305100c0c1031100801c00080d00212a42000b070003000008082c1c0f0100317040c0011100c8a10b41a40468822017090201a001240100e140140d007410790502036603425452400b4030103070080d540050449464403002205000c0d1613002800c105603412010068411410200000c50200b940c02030b00950700c000040c030041c1480240c606e111800444011103180c0303446846201c0d8030b03054016600580112843c0400c55805c1265800904402003060000c0b030b007000001032043c0814414944200c0c00001040c4c02000d004040340c0784c4848050903280d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 322790620 1250 322789370 322789393
    0xa05061308011509110f0f070f05031201090b09040507090b040f02180108280914072309090607080c130303030506010e030a030e010315050a140111030c210408 70
    0x9a142d6188a8800800d0a10415643c03413001c17441101c4010361580e6603036003007540681d480030b096000501c00711141803078031803000e000c0365040000d008840c41514418402d5810071908130240c0d01200d04c0c141c056038211041c440040d0010502405440044600040d01d500301000680548010751100f014a4400501280b80d2040c041685408074001e03202c50955490b64000804505c1d0340640302e0801040c808208400003142c8c0e082030003054021000016181540b1010b40e00703014065004110043e0680c001004001c404020300c400508101e901a489140032502c4a840e00801030121082100c01800203a0a01c0404150344414800c22107003001507480b0320740070f0300808080e1500d41c04078050705501075a0b0710700000c880d90420380c90344d40d00c071b2341614500054010744840000c01540062140b40410103481e0101104001c0501080c1c4044003e680800540303280b288800c4420107810800c20005412000030311018800d401842c402da08442400b0590310314003643e080b040450180141e4002c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 322791870 1250 322790620 322790651
    0x90414090d0306080f0c04022a100c03020a23040b03010b03011406070f02091506120f0703020403020d110102070e07050a02010b100c0f0f050102220609050a0506130801 74
    0xa4032920151801c1154603120142c00c3d1740c170042415408072941c0820248a541e0400d60040c01140c05e00d02002c10301203081d0a08804040e40e101c004d00155403003411201100c050a000e444140f0b403160070114074100c65004000c02880d40f0740c0c0c6000151006c440200b01a01204084070010311414150f1a16540c407803107844c1c3c0d41d80c000c3c820b44540421030100d0322281d140c03c5085410107940940c00044201d004d030700f4450300c440021b00c0d2050420300c0700100c1c060f60f200c003001020903500300c00303d0a100c0d18081815100c2c42c00094030b143d040601c144803e00050329510340103c8460b4000784450603001007280102d2514089801044608000c402480032164112025194080e00e079002440f02180020911102414004040380040e48a0251002142c4141e0502c41014003070318039940a03a0f41c5849036826a804100444c01c141007070208507110300440c031f1890010b01000d1130700c400b145180c80006441200700b4001e4900c261000240f81c000100307001c036240014241c0c28004c0c021150240d6024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 322793120 1250 322791870 322791883
    0x6280608070f201c030e100203010b0906070f02040207060921020706050c070e07021609050106020d030b040b0a0e01180b090c16080304060203100902180609041409 72
    0x19000308601202285074280100c0704030445482ea65075800344040d00008054040007984000e0145009021a140c403030242c004030300d400d0302580e86001c541d000410a0300c030325000c0325030b07244040f0074418001400750f0180d113411600204021030703c003a01d60443e0706103012030a003190720096000d48000f0b2540c8c2085032582009a486002d50500902440c0e420342d0301c40752110380054980180c100001c2844100d0266026000c000000b03022070702c1d51a2500b0307914143d2a015900c51000d6802161011003944070701c0035500150071300d00d00078055035142c03000280d0355040d1041c0c200705154841264a40a07140d50348440d0003820028640c0a0362552001c03146071905080c018171000c80140841d440507400300780101c02d44004040c10601d49603603084e10150441d000728540c400500a10710481d008150204080c5000e58040c00c401a601e080040e4034075040c000c0c560040d00780b036006000810130043e50700400300707451405a407081e44d43c1c908180003c00920300c2c2219038020300d4400080c0150340c4000902c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 322794370 1250 322793120 322793129
    0x9040203211b2a090a18080d0b09012702250c03020907020c031c111c1806020c040f0605100806041410030f03140d090201230702090628 60
    0x803800007044070440044201c6180f40d02d411582c1000030411034074965000030140e9582d14000f8a02c84070580d52041e659004220041c43d0ba502d44281c00103504d08048521300400c1d6981d2400d2281003070384225440c18072010074204029a0100e250031200781c00d002d91016643c2040f0707160103030000381c5c5402e81d252000d50000340c3c043c00c0c5900008003802c0c00041d03804000480103000300800540032001c40d03968441100080308002d03506c2800680311b03d04200ca80c607001e40b070703440c4c42506035021030005060000396084d03121119161101004441d40100f501404000141d50200304980310032201000760840340d00850b0801028014405502c0d4080d2000d40a403100711024403844220b061004c642013819034203082031841c01e407002c00006450141403400c3c0b510030f003469140b1901d404192040354025865001181d510b440516003190303442122854021200301c11003041c040c1c68801031340b042c011003c0c000c1c050b0841c100030854507500c0b00f00e452924a08043c00007c101c9040451410190441c442c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 322795620 1250 322794370 322794403
    0x180a050a0f24090e07030f1712180a080409021602130603060b030714060318010903080702010e0d2a0c030c05100905030307031b170a02070509040203211b 68
    0x32900083d180207085030090401c005251042c20f686685400050442e0100c2e00080f500c0d80c05244001600c01416243e0746e4141c000c0101d2612815802101501150003405500900d015100080d440015542621031001c001620b410b054105510f426000f003a029510200a590f00c4031740103d185c03c240242c920406081c80901510018150b4402190083d400300751141b507d0100b60342000d002030b580c00113820342c084c40c40b0070340380245c94212400340105400154440c2c040104a540900464a540d50000020000441c4030301d00200a0001c0790b840c2c3c5d607444c00c1500304824010501c00d8024030150000c2d2032804103036603494000010401d0740b003078070300a00c19851901c0380c41d4020032210717046a2001d405540f4026003a03030112420104c800c0d41c801d0942c00e20f490789000c51000c19040050801d005a4280c1d207182c03114020303280c100319501191241060508100c01a1000702d0b261b138a10403d01240d0b43c61b2000c0040d021035034019046071485201a28452501c00c90f0b001032503802d02d000184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 322796870 1250 322795620 322795691
    0xa02130b01090506090f010e0a030609030206011a03070207050108130501152402030313062a110106060210200c01060608010e0f191b05030a0b180a050a0f 68
    0x20a001583c0900007465500100b1b46002400d40d50054a8501610f60b0017480e40c000035450b55695812999144010b40042c2d01400c01400304040d81404440400f00380c0b41810700f180b40085009540c0c0b81c0602803d41041010030125040d041030a1044881a500130002d108013203902c964450000300305d200d10344010321400004217402d071007120000d044010b1540a0f5146544072083d01300b0a10b40304004403020343d50b90b00e07454115480506243c01111000461151000c01e03544010b19900c0014150800c40c0d150010400015400240207040c0314600790021499850b28590b480c00c42c40c9442191142c0c00002440102d0f5801c19407002060b54102c1e11803c0c2c13981d0300c52203540520101110190a202c001d800801c43c02d03061100300d880062000107000c150010084c0c94856604c42d0140b080c404100048203000c0c048405d03001d4070100002c00e03116980c50080c004030f280302060018000088160b13680300400c01064007500040c0c81c004299200384040091204040d040c00c1a0200380c00d4001c0342007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 322798120 1250 322796870 322796879
    0x61d041101140403081c0506211f230412031e0f290607060513020306090a050f0606090703152303060f072f07030b0106110a1101120609050a0902010206130b0a0902030a02130b0109 79
    0x40c0609402260400c00321401100c191004ee00144040100c0e2411582009820a010104c9010300c45082c0442c0310f0106013003114038440d540c2030401035402a0b002c0003000c510800da072110f00541d82e140c0d4002c000440e594079a071000d44c2003518500c0c0003030740600460080210407400005c42070f0000307105604403640016032a41d0ba5480d22001c0d00c0c40c2c0d03404a02407011402e09482604482c0f5800c201c042d81c80352a039034a680020000c90785103c80c0c1c00c42060001940c81901d01404030583c0b01c1000078603c00c051605600091440d2034000058107480305030882d18581c22520300c0425060882001101c41c02d035181d0910300b1000800344502c4001642001040c5500e001c04102260b015a2100481c2c000813051340056a1007140201940d9a060360740200260610f11409843d0141801e00320008841400f0b000090400000900c40312061f1250303908140020886500d03da40001114800a9542100c0c800a410030007150070103540f100222030b40d0f80b28501242d03c41d41d80c8038026241c075021143d45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 322799370 1250 322798120 322798181
    0xf1e1203050103170a05271306030f0305130801050103052803020606040f0b0604140a05060f03011e03060c02060a061d041101140403081c0506211f 65
    0x2408000c00880c803001401c0d84591070400a015200390314100340c1d0500310358400310b5020310800b04480b2081c0420441c0e50005003087e82c48d0450000c2084000e005003411604d41180c10402048000c0401a000960512a0710003910100c05021544020b0020f96507034180a0340e514080380301040c604c80350958911100145031000e641030342c0d25401421640c1d031000c08002c020700241121034031094444c103401640e0703a10305000b00060000720034850041032081003031040c140f110350801c5014401c10006680e42a8041d42500e0450303030070051500c117111444031055041d0a5903032008001905020035070b82c005401041c4248035152010b01044801e903100740e001d005207021803041078654203000c04100800d00e00c0814500b80d900604081e00c1d907455030000d003917056000da80184c51508000c5405159141100b14005e52141664800c0c04282080030004003c10485007003c00d040800d40c80204082d80103215085c81145401e0254246115041c101d60140101d0070041c400c0c03640100340750001045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 322800620 1250 322799370 322799381
    0x6031a011511100e0f061501080112060207020a180e1b0118051504060315050a171006080f0705100806220903050405030c0109030305090d0f1e1203 65
    0xe071025142240500140d05940002c0d0380d4048070701502824006440700c0d0841e000310241c1d2540000140085495070b030b003480c10010064400325041c0d030a034100c03003800d0784c3c800d0443e81900c542c8407005c0d2a202140c600708000344500003000303400002d039100004a90810000003100704919100c14000214801d2205803a200d1007561507002c4045103031004515449000441038140135500480412034482d40054100000c1d15880c01d0310b844002414400c5941c10300550300c5450f154081940f500b400c2c44005090400f1901680b401410316901c5183d90000030048109900602001003159a40316002907403543c12140c0d40c1103080c80317000b000040b00c0c200729000807840c503c6540c500880703468010030081140407001e040c0f032040985a142038000f1010344036010b40e0510984903903540c0e601d88014141810713549101c05040c460032510800c0400d42080403030720b10750800c8a210300c1c500f0700b40c40c00a06090728210050011401c102800d5900c1e1740c54000010380502941764011004490803084007a1030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 322801870 1250 322800620 322800629
    0xa09020420032e08010e16180c170a020c1504020901030b06011112071403090117070908070306091106130506030a140a090233030403030e1006031a01 66
    0x42000018140f0001d1400f020640140c4106060380b0614006482607500d0305802c07820403a5507601d2040c0303c281d02000034481008513800145601441d114030141030b10003250a80705155181d52040b45600e02c1000c002036242031000c911107484c03e1412601e03000390001c1c154144180b20f90480c0a103000e18648601e84a41d40c0184032440e076130308660b100c6902c420042c2038a8107201103100c071001000b00030720507010704810701103000b03456550354203155000b04e403141c500082941042205550b5641c0c0004122045201c0000c00c0e0030b139884140d070407214000140e100c03249034014802c1c04800c0200c15000440041d0003581e988a00065010800055200d04044461403150404040080d4106480a16408811200002446940d80000d188a03440c106c1c0c40143d1203554400703060451030302c0090000300044100d00300440034664455000000000c9019100c1d848000c00001c0c01c1502c29003103401e500d00c10400b6146050106201e050203031505000071501d10b80041c110700030703000050203241d0490707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 322803120 1250 322801870 322801931
    0x3080601090e042406140d02030102090310051609080307020409031b1401060e060a1203020a1a2a4006020c0402090a0510030e0d050406030b030304061e0909050a090204 74
    0x1a941b07001044005d10001d50201e805540910400c80640d50078031002e1512083c0c8007010a6034a80981101090ba252403540c000344040488140300713015000003650007d03070381941e00040001f07a40c10285e03400341d0f11500c09480c1003d0103408208002c104c0c04551750048522000780444d42d10f541c0b0040400508403201034110141803c10800e8850b841250808103000340141c841000c0780b926081c007001e940000c031501c0d0703c14080900611000300707030482074800d51840c000d104080c5446a000c00074400c2d01c81e44090810200f11455180040b24503028208008024000c52210402d0401c280f4101c80d100304409401a803560b10f04d02c0c1014000c0703a003c0344000300780c0d07401d541c00c02c41041800d95094111404143e60784510181c400810044000c1462144d1619610f6525040d4010166400c08140034040e0b0001c0c03004000315500700306e054040940c6c44803019944c4040340e10480c0e0000503a480380003c107050106022800004d94040c00d60640203440030702c006001c00100402810030400281e212 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322804370 1250 322803120 322803149
    0xf1706061c0b04060b0d03050a08060307050906040f1103040303050615030415020313120206061309050c090702190b01150305070801140411040f1e1203080601090e042406 75
    0x504060b040607070152040000044444460003c980a80b0b01d04900310701181000880348c00f03280c1c010a00c0c552041c0e0880041030027508060100b400d142c0301500c01e07401961240c0c07007005c45940d00e0304802c004030503558050b0344138507103401d00502070101034075614001c940c0b8100007940d01b2440c0702160b110b141c20a0010400c00d146070b094100a50000b06004000c0107850902c000151598a8804041401d41d00425640c14001c00308001d40c024003d41c0b06403a460452500006100400d424009200440300c155499441401c140e0604001010b00941d41003000c805204102901580034141c0f140c00414000007849160140c040758810744d40540860465001004000890f4118000b01440900007240b5403101b032b44600040e0300103800c00c00004072141c8052004011087c8290b140311446d00860044030b00e0036141403080b5000d20f001604101038000002c0c116402102d00d00014107480322440382d10b2401d810044041d072640300c15071f018403030b1104550040990f00d008003015190000305a404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 322805620 1250 322804370 322804373
    0x51305030702010c03031d1b01111b0402040b040905011508040323041d01090b031f0b0103090c09020c0d083d1e050117060405100f1706061c 62
    0xc48440c280d1003101016282c072031440c0615247c968590f500c240b5900180008910340c58800048200d46580904010501045007404d80c0001005203029180030344540c04e42d82d00d2004940a441a038106203007060b00000c0002d200e10300759003c24101c64158100c208454003400f0100c1c0c41100a44000c0c0004100107040804143e03856645416600a4420350345015964000f043c071143c03903941d40d201c3c0440180c0c010001240f40e401142180001100584074810190301c503a035610313222501c58103040340d44d40c034445e02c6c076402079012504640c1c00c0040740a0103903890f40d40801a43c010b20000b290790144218030380c2140d01a1809600031414544c440048220f84150551100750380301d44072840001c0d084100412907500440c1c00701515042c180c140c1503100360101418100100d44c46941001340030b06404a40b0501d850714150802c40c100c502046070703110340e1280c48030703424990051081000349560000d031440c0c0683c28106206903c00a4403440c0e0b450303100f08421021408100440c549880b00c0c0c0d40e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 322806870 1250 322805620 322805627
    0xc02130e0718060501090503060601021c090503100209040b0f1f030212090d11060c090f19150e0414270601030803100801020a02070b0a0215150405130503070201 71
    0x2141140ca0508540c482550742c1903180150032100c00036803041e40c2c0d900050040356400300040c0094801500144802c1c1800d1000075a60040c0d10b140075000c42280300820101ca12840c06100248001001c440100b100406140000e500c01010607204900c3d0444200311400c091aa404115000410409003603180407145c1890200c9074096204166082020740c04070423688819a000d0324000c0003d00e8200700100c0064140350001d8404400f5a20101c10042c00d5101a400c540e145031055600012658420303020030b00901e10760a0952821a000a001c41d4504079150300c8448075110b81d0710810003203145001d1008442464511880c060002c01c0060f202200034101c409003642202c1c140c00d01c00380600726160070f008003a0021a0b00c84800410300040d500b40a00c07000280c16104003c5283c55807001001c0c1d40e86205101da80e0f07035010041069141740b4028040908070140380c0400414a1800b0000196034401c0c1c0714007a445580b030702c0c0c0455114090288a01800c66100300254a419010340054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 322808120 1250 322806870 322806881
    0x1c03080a09150c03050702030c100c0509090a0f061d04110d080c01050702010f060e04020f0109091104050a0b071203020f091e1003050c0702060304080409020403080d0c0c0213 77
    0x9441140c07911070110001d85040785100b0030281c0404002030140c40c00e00c0050942e040070348840115030003800340c0000080081000a9010104040040c0d0000c0e080004c1c0d801d40105180a42e01c08043c0041000e80e4890340c0201c0e003031421107001003003c1c40c4c8030300300c03071072689100014140041040800070340041c81e107400f41c100c0c003040241076048201d101d03600d040b0240c1c0840d480c510319035155030920141c0c0e034090003010603c580c0c110041c0039181c1806070811020300014406032242c3e141c03400301000d69020711028800f0380b441e00c00520032815886d00b141c070b490f03000d4401c950050203030a40011b15001c0d1a01503c140d2580700100002214258204030040e4000201c1e80c00d414404002010b99652004000030281c40c0002031038000702c00b40010001b45249107284681850f06120403c0746840245c0b00300d9654070f82c101e55654072034841e030501c07410724003803500060855480050003005100142001d06501c2c140c9031420700c90610802400c032078490420794025044942480c000494100b1034002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 322809370 1250 322808120 322808131
    0x1a1302031e07090b030a0f0606120f0902090402220f0b01110a03050901050a02150a1a03070f06030f060302030d050405030607140706020c0c030105070306080c010e0603160c0f060c030b1c0308 84
    0x41f44000d11040ba002c202d8156910103000700c0c03e8485280200c900500410803048000201002100c8440d004500c4240307000708001d204080c002100c849900640790141c003c07182d00c4108021b01c1c1340e200703810300007401441203441c08244c1040b94201c1c001400030380310881d194995a90303403c7c140c41000546203904052a0b0300c05600807040d036950607411800b00e1520801000e00d000c1451080001c1c02100700e1a00040d5500a40001070207000b10051008140c0c00c0754264070740001c4400f460300744100242040c0d08020341c10300030700d0b070040703503150f4080080c0007504c4c011419a0b0480d03c6818003034402b1121240710481c0918103001a4000c2005980904190300903481614000306401001a08445c021151f080c0407941d90681486008000c100d4610100000e0034a40c1c050100d040014407103010041805a4000c00c01c84008d901c1d6100b010701ca1002c030b40c0301c2c3c24401888000e1801c8005042c0301c800300d0303000a2034a161039129191615455a41a850101c049028030a945007140c000000a0a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 322810620 1250 322809370 322809391
    0x30b0a03060e03040e01120c060503071b05060711070f051009081e280b04020a05060a120c03050402010c12090b0a110c060703050d1a1302031e07090b03 67
    0x2010490034060401000065400f5540d03850134544000888070068022080d44440c5800f41800a07076071807041000d607640b038141746840e517848540449900c0c18100000d20040002007200d0100a000611035024074480d4a50b206e0346107180c03c0c066611000d6120700035a1403a8802c04115a00b0f01031182c1008000b6031901401190300ca5104a1414200d92483d02505400c00c005c107417000c6090281c4804140041811907a443c004c1c188040b800440c460040d0604000c90041021540ca0f40d450000400018100c2d07901c440c1c00c49005400490322134003010740e2604000022044a11a200c0d5520542d070507100c4c0c407840e0b1455224122000300041901003405a150030120b5120003000183c0202c0d0815a681039406240f041c0141c1816801480c950050b80306000c181e00180c3c01c4020359260641a4070001072100da502d06460070015003601c81601700b22454144441c3c0045900210300c145070102e0304001000b6501710b0300e85514002c4402900041030540c0a0001c00704a100442d00f050300404c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 322811870 1250 322810620 322810639
    0xb040209100f1e021b0a030c12140703030504031415010b0d0e0f0705011413031104050f01050618121501151407030302161b090e030c070303030b 64
    0xc003040c0c40c88800d103901404140719a1000103210b0740000281c115586001510010442d01000a03507500f0000c407407031141c2c1c08401010800c0e034440c00314490085402801c6248695524a48000306100c0e01e0f405556004501801803420318000840c9000c076945541d9151402e861510b41000150f010f90004100c0c0c0105a804404011b400d00b015003c0d00754284a6982c40c02c0d00e500180480f050302103810400e8116a0251206000101d1061304075202800e0500041a034000c442c0b0380b92040c04415482182c04c8240801480000d240380d0741100001e407030070841a20364500c2c240c4940424462107600c0101004075601d000d03840380410440d10001781082800b0111a40e40500b880a14060101c2982d00780004014584007218000720800c40c03401e0444ca15500c00c212881c03e441001005401e054000550415541040414200564000000311100140e0084154803d0071070712800c52554140030034011600404012501d111007031600500585242d07130341c00c2e1301038840540b45550000a20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 322813120 1250 322811870 322811887
    0x7081804060f06020f010b0306070804031e18081504021302040509090303100f03030203030103061d01180606050a0b0304120507020904080a080f04050604060f1b030b040606080f0a0b0402 82
    0x9001e441e02600d0a03000c207609090404800a24042843d2030b481101e0307041031400781241d20007182c3d46400540510740503509644034141500c1200c00300040d0040203d0a0000c04421540f0030b4989001e041c080d0303848086942e540c1082c0707540d050501c015008145041d00070400602e00009241c10544ca01c14009d805c00c1c0d6207400107140b20004540f4814941c000104004104500e180140d000d0310250115039400f50840d14029681c1c08140801403509a4074506c50300a4440c418a442d003a4049000074049600c10050306400c40b0f2071990100c0e84d140c03c0100100704c03403920b0300c0020140c0d26100582030540c0e80b07585500441003081211007061000410150002da2550010207100e14007410502d6a01c24000800a1110500400324030000c0c1186d014040024400f14642e90480e400032000324600d20402112001030140fa0070300c170560380c078852034030010315015040581000000c4404200040e501c0d1000e6805070030488076404e9003101240003984840b8507900c40c0c140510080c0006080c18402d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 322814370 1250 322813120 322813129
    0x40b1207060905041803020a0807150e0c030105010602340f0b04030c05030c101d0910081515010507030207050d23011523030a1101020d0201060506070818 68
    0x103a42104000030402d070001c1c803903400d090184082d851112003240d21681042c0c1c80003511140080b50003404020001018010701c001c03100e6101540b00c217510100071070340e500c107846a0345000120b00940203500b04000003402500114803441103c13052a11001400d0168140716400015882c190b4030100a2080114aa8000300e03d0f4102400c04100703070986d55070841c101501c2d84c41d029444203100fa880000c10420b103232699110700501400c2403c1c0446022000303408070104000804101d42c0105070302d1b040104030008099804111810301042e201003516000300140076440458000304906814022080c1d254400c200070f100c254080d00c140c5600f682c940c0b000403440109440c05548145000348500450100c1c1d180e25804040300350005c2080c100030040000d811061b0307214030350000070301e02c0c45194480f600c16580044050000e040d940041c42d103282a910f68a03500c0341d0707980144141c210603000380340144501c1090700c03002800740c2c0c1442c0c0140c1d100513050384a03020641840d0700380c5001a8060300e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 322815620 1250 322814370 322814383
    0xa03090803090a03090b03010b120405031c05191503120909020d0903110c1e120102030a0207051204031709040b060c061b160f03030e0d0305060102060c18040b12 71
    0x11000c2c0940b640c02e0207030030014007010742c0750054142200c040004200412501c4115036140c001e607600454141c0c0c46091850a50148840d10144980b079142d0a003d0840198049441101400d0403101080043d50200084480b03031455040484040d03030090000c292420004100e5050518001c03401c5900c0e14816010707a0000649001001d03203c0c402c1100300340e00441402034106100005107042c01c58200042c00b000d0464003040b00300721500a2541258513044010360f07201440300300a5580f410031186c200000c0d801190141d07083e00414070301c031b030040751200c044408407900402c55203004a14445c03082c220b5440750105540c130660b81c40ca29800c0c2c0d00c40401400030584c41c40c5c007401c4d07a0700d854004240041c1c00d601118000e6070041007540c81e80c6480403441354140d80c00c14204113840c6118607044d0001c10400003140501d1003045941c01c0d00d280c3c5134111a1190a080e0f00361119034a651114807464003a8410808410b003036140b444601c2c0c01c06a1001280300303801042c04054540104e020b034100703030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 322816870 1250 322815620 322815631
    0x1b161b030b1603050f0402040f0b040c081b0405180907050a03150b03010203090a030806030a02040e0a1a064e0610050607031d060d0501051309170a03090803 69
    0x1c1180810412012030302900061580c00c2c1401c0c00545030150484003c0b41c4000c0000744541c0d50b075010048000303e16805400300e000c0140c8100310b40300e00200060098407003201c1a100f981d0b1080e14800041c4008010785080320703409020120703910b1810118141c4610000c1030b07c20fa6202c1c44400145503603620714607600071806030310814042ca52071001901592440f070300f0103000f82e0042080c802c5003800002c444400070b405203841c403025260800001e04094000002070b5025007045040c400110300405c400c5c1c0070900c1044145a10b15207002c01541010081310480d5104d400f0002c4201c04a104001e24501c03510700c10702c0b0726490301ea104100c59000000074241d040004911000c501212810041d168000d8854140314000a24140000d98203100701c020040402800d030b08000d5070b10080680c10603201e40010f0600c0d0300ca007042e9140c00020003003486068404d550304d401c0c1035070401d150b1069048a035081130a0984080403402000303807c4d40098880030415984072010800310361414051030141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 322818120 1250 322816870 322816883
    0x50f070e0702060603070e1602031c0e0d26090c10020f010b030c03060408130803040806040c170c060913020403110a0b0301060f03050408070501090506010603051b161b03 75
    0x10300785a98002c2c58000d00502c124000d80c041c1c00b0030b01142e2420414158460582020480e4003641141c040707046000d8920300e15050700010504141403c120b401170300c065031400040b110180040a411243c10b00410042c8000788851084c130381c0005c0f000c41e1a10341c0400003070121a81100c140f00070458048034141100016001100c440034429021f008039640640c0c22001403400b80c001c1c80019889910240c0002c220780d400103000c00480100501100c02801d0341001e41c7d88070360740c94028a44503402107400301e842c1d098500300810092210800c215520290b070004049040c04901440306a03484491705039406110840040440442400100040c41c030a00b0807041d40cbda0312500b400704420301c83e00007441800382400140301c020f51204c402203800f0f0881c50b0124050301e642c18064203610507842d0140880d402c2940c40d009000c1c0000b0014101c41c0d0720340c1c08214070340d282c80c0280201e004040344040300303180810030701980c444103400014a06010780385445610704000d80143d00302034580d00032542d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 322819370 1250 322818120 322818149
    0x10c0219030b010f03020303180a05060a030903020d1b0b090c060d060f06081303180909030302030702161d1e04030206010e0609071b1502220902040608010b07050f07 73
    0x10006035001e103d0040403031010b00703680c0600f5030f80000d80742d000711803080d40c0740c03500444031840ca9139840d41d02c440140382c0541030507610303103c1c81d000401406c600e00040c0c0141c07180c0a82e00341c0103031145c15218006401102c0203c0f00c602284e0322680700300c01c00707082c802e000d00c03c0d00001006a940d5000034441e01801c1000085e140d0701e00001010440116030004042c046424100b206038140000782c501496410720f0030b18508401140342d14101072050b08803034446441c0050030802c254050b0300540c050301480d000c40304000003407580d10381c1c0b240c00d902403441018020b82041e403001d104414042e8020100850f000069010380030b02010711042243c1c01c3e00141c0c440c0004000c0350700d04055480d0056070945001d0201c1c900202c01800610405541d4403094650303071840c00501c00321911080039440110002e42d954103411040e0000140c1c610031155290904000c00241010507108036000c50b601078691032aaa80f8051100c03150740c120303d0301a601c074015005054001c11302481040054003000058418 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 322820620 1250 322819370 322819373
    0x6020c011202040303200109050102030a0b030c030a0528050d0c03090b041a1809070801080c041e05041a0a0f060909050a02060f09150c011103011211010c021903 71
    0x6400c1e00c0040006525204110900119174004d015003600c03440070344011a902072035100c00340101200e801c007802552000c814084000400d8100300010002282242ca400311100100354a9102603c8001c1c06075200b507050400c00412012141800c003080e40b0050348244068445c0c505000350f042061001031010819a0b0801d500482d040004c3c00307240f4901c50410b410f1803003600301c4049a0803143d00d0b006010429008042c0280f0114040a00140c4260304070b013000c00019040c54000e0091504501450301000e80c0b44c03e05105d42c1c1f6850b00d0003510090201275000480006100c094426200003401503c0640e41208240880e4060420742100080310031040b401d25084500a400c50000b180c207080a140229000140e80800c0d1601211202c0c0e64441e03802030031000d449003900305500711141003820304074862810081d00410102d50002e00181e800c00900c24018403090082900800d00c400381800403440141e9081c88040060500044210b026000909166060120340740c0da103044910510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 322821870 1250 322820620 322820627
    0xa020d0b010e09160b1303021e150708040510091a0301050f01030b0f0103050a060f0902030f0a090512090109090513050c011404050f060702090c030405160303050a0f09090606020c01 80
    0x103074440c100c04040c001013184c162036640c0710380052240110403440418103240d50b40041da001001564000d200d080c548008000c00d0f651030008a038014400d070039440458402c115400215a0001d9002e456a0f19090a10040201010501c003181c0204448103201003801075018107407031070341c1a0000c0d8a0340c481d894002084240d04602600c0c03810503044c02700083c02034482520300b442c166400d080204440d640d01f5a0341c0001c120304c0c0e01007180301408c83d00015507411558002c501403d0315040c5c0c0d12095480756190800c1e2440d15000409686c000345102c01400c03003080151031101c07014900343c100740360348404c00000e43e8029a1599416050043c00e0401c1000402403605506030a007004641d0a4201c40c07007860301c4c080c0303100c2d950080108540d40070582d03841104841d03041d6801426802203081c21103501213550021a42100c8500c00c03642e440f628542c13080303012030449034107684880c40c0086215044644442e00c1140c06c003403000011010407443c146004100151425034005d055a104c1c590006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 322823120 1250 322821870 322821899
    0x190c05120f03150102010b040f06061b0c05090901110a0f18061d03120a170a0203040c0303120e0d0f090b030c0702040e032b0e030901080610020a020d0b01 68
    0x48156003020412040d03909480825694840b0300010419400110741c00141d000d001002d003810380c0989494100e403124111540124181e60190741c42e518405c010411124102404120281003030526031b03010441d07490803242140d441401c1c1d000103c0c8464841804682640251158801103500900f1040c1d4069010340110080b082140081034010b15010001c0e1035200503200d1000c00c0c80c1c0954840394561000c01213007180c048182c1c5055554030620200a104c2d40d071b5004110030940380e800105482c01168000c0c0c9001c0c43e081106030f40d406241d40d030240c1703500502c0c401f41e0b0400d40d16641c12008240003808041c081c2c1c90b068544181d207142c0706400030402d00203074001744d03030070300f000c0c0140205240c1c4501550f6000d1750544000070032614000307083c4d2450140303140b003c400d02802040d2a000030b04c40107104540d01ca04410511285918440c080d44038007503881102c0c00156148002922071804140d042c440c581140192442c038440780e00803482002c00c00c1405e0f51107252010041041c4807580300070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 322824370 1250 322823120 322823143
    0xa17041409040b0109050718240f020303070c03210e060a02070f080a03060b0f04140f0112110906041d06040903021509010b040e100507082703190c05 66
    0x61a1185003d42c2c84050864045c000c04407807a54520010340520700626640041b8000b06000e81d07450381c0d589803000301045683e000e25050311200c080c01c928983c01030440418003025a009142559a20780044800f1120f17030f0010360411000c1408041d500200c9090148110f6041c81c0114501c001c0e01221fa180683c0a840340801c0e910400c0641b003c50075515681401d00d92040185a4510301507100720041c280030781246002c02c9000440010380303401c0600610480300000c80403080c15070380038100800146031641403070210308402d2a402094049501c8014040f09601500e42010080b41c007081080d0042d41019001804420100c0c0120071705106150384540304031414444060b80d0b940080d00d501c0442c803442d001d090010080b413120142034209103114000a80200442c030514628a5a203c510442c0040303d02d1400b000b151026101e10110341c407400246400c0311a205411568049414170701102c2d20160105012030261a8044c04410396208401d642c0e0f2140b40c0003502f0030a040c4440300b1007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 322825620 1250 322824370 322824379
    0x30603070e011401030b13020a020604150c09060507060609020a02010906050a0e030a08040c0e0c03160f0e010e040603150207050d0302070308040206030702010e0a060204080d09080a0807050a170414 87
    0x1081500003a85400f01094404e10f07020580400b110b000c180c0a40d0490382d0902c81e2400460f1074982c16a00080880c45180203030412004d09400c1c4030040101c0f5248000d5000080c00c109080c0303d100d00440040c0005441000d000480c0307541e03608000304907000360a810740140d442c0d98048003400300e9801040c4e00400e45c00810490801391031000e40d030720b2042070401002d20140d000000c080c013440100000003801e4a185520091030900822050b6607c111244680a4900c845110641e0b2051260104518450b1140c0240003042c03c010760b0007411544015030b020361104004000201f1000550800081210001d81c44070010b162042c1825461140d0f04100351040c020040802d6001e2081d580040d011b440265407904d0300c0c0b0049002d00f1700c404080700c81c0d100b020400410000d81c0e0340100708641e01030301604c01504141108607040300f01b501c5801095404811b0507008144444000c2c031015100b04101d60f280c0e8610384d07a0034109002030074098011325000c6800c01201e0000b240f81c00f1035120495 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 322826870 1250 322825620 322825649
    0x206271f0c1701090b0a031203020304060e0102120105090613020c100b18010513090b090c0102010b03010b1305072c04140708040b0a020d2408060103020105040e090c130203060307 79
    0x200c0b80c8040c10014868841140d44490b02c038a181d40f100b035600300c0903640141d40034031000c102100c098003950ac03d85040703407014605081ba0325148018429941150700012401100f0707441c00c0b027007061080f409401c1d16480440f0000885154841e403000300326001ca10300142118011080c0850200c4641d0030300b2a004070689012105441d8881c000c0a0544030300321841e100e00c801c8050154010040309070b00400070900d2509106c00c01c0400211507412010036402401006449010f26086c2da080c4208103801c22201c0034003255070170080c2c1200e98008018a05002c244021242e1020b060440134450304405042051650003414107004001c046540c55660800b48c0c00d1403c0300903c4200c0040c07004e44003003072040125041c045181c040382c1e032003480c14034140304520030a191a058081103c035200d08010141c100060701480c00700f402412603405868840c105032900c03082d1192824000c1c00c41c41c59000c1d01d0300b011040d60394200c0b0408030f220f02d040016220725040d4141840d1200c0b54100c1004681e151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 322828120 1250 322826870 322826897
    0x71a22050a020901080f0d0c030201020f030a2f09090406020904050c130f0509041b0b18090115020c1903050d050c010e0c0630090c01021506010206271f0c 68
    0x2c7c81c2c042d02d203c03880c1c403161003a62070070101e009004614030705403d401d002050040b2242d5541040e00b0000d0003454984003034046d00d007030940030041c0070200c035030480d0240280e080701e25203020502c1c0d1050003010050f20b0203070b010000230200c0c4c1c0d00f220b583c100e0a10200c0d00a900310f01005039407002c1c14110181d0800c3d1418500012542c101c020300c010201c1e605190444240540700740349400a0a0b4a103446031140065000203a80458540c000c0380648441c400003e1900480c22880560818640190418003448014459079024283e07a0410700b00286800000095040010040303044455680c070b501e6844003d50a0b094a0080c10041901e50100000862907030728001240c2d40070341313000c0817881c1e0300c45004e605480031003408183d040384070304400400141002c0400c101540403001d90a86032844c0307050883e121400400d0720241e005030f11820015200e04c030f501e001d8901e00704044084000014100c141c4078500210819084c804e0b03402100640440a40c50041c0e00c0c415a031405c04803862501c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 322829370 1250 322828120 322828123
    0x10905060a11060114010314040c052107081f0c0906030e0f01060b130e01060903080a0c06092303040b0d0506150703020f06060402071a22050a020901080f 68
    0x90294900c900c5001680ea01c046020b442d400520300300380030986205603503494280351401c0100c8070b002d02181c00d148205010960104120f40701316401401c01861a05150501074503684c3c2c41c0c8114400c5200c011010241d03081041000001c0c07003488020003022110301c448003241000400b1180c5110308100b03001500c55040041c41003034400b0780c41d00141c141c040e01640c501d440c44625051042d0b510b02040419000700b0200140310801c81c42904900d06661100f02c00c40c500030900c2600b000a64400c01840000c003240c000b885410680d01e09014048078030780304e00d4221142100c1c01c440c081c2205007a26021000402d4900000c0704c2000594203151815161070680d00c10042807038090307076654001500a61303d100320494020251b10175192619080d18020750b80b00342d122100580c0380300e0500056080e00c0e10380202e8054540c0002409401d2010709180085a00043c080c04000441200c45030041054080c43c401c1c86802503006041810050052064903d4181c2204046400080f401c8184500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 322830620 1250 322829370 322829387
    0x1509090a090c120c15050a0c11010c06050124020309030a0204051b0f0318061003020d05120d0b01080a0e030717040305060f06090a09021302210c0703170601 69
    0x414a501140d00000d51400039080007071504441600b003691281c40c8103000b18407054200307440f0505c07042203540000020599a0703015517100e00780010101e4003820b0000d00240568a850364040c1060500004185e84860540d002600302000460174560724036440241c8155400f041c3d209400998980a240c5004c292211040c003c040d0051707899102052600070a030244035011008120315903250b08145259071003550003512011501b03645030080c04d00080f404a100d034040d0710503061180049207158284010011001070940d035500034500300c15040804040140824002d40600240003203104001505660002d0401c01d42c191034404405021103001049070111500100e051400030402100d07080180708a81004086004010034010610881218140540002c603041a038541d1000daa4500f05d81c1078140103580070b01443c10f09034201c000d6074014450f152100031200014000c03030080b001410015200c6045010002a0f8401415407110b030500343d07020700e02c0b0b00340154140040020402c0c031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 322831870 1250 322830620 322830631
    0xc14030a230702030a020d09050906092e0f06030510030f02210105010f170d050a0309080c0609010b0910360e0705010c081e090303040e0105150909 65
    0x303075510046140840d0500076041e035042414040420791805030402500e03a0002c595001c0580f146c00d44512286020b48044004e4420191510a01e039a0f41810001982000340103454200c010300c1000c5103140c00e0014496214108441d0324041074a8074500c01c0e2000f4065112004052a0405106c40c03501d00d690342008894001131441c610821500009212042c4072110440030045446920400c28040d04028121082c014828141b1603030740074201e0250b041c003041c40342160084070303280d66081d0041000d0302c140751403032800007003840720360359400140c0d800280c00c600380d944107900b00001c80c6001d014081410342c09030398240003401c0c0161010180c0d0f046001d40d0074800c0c000094134500007006c1c00101900301c0124950075000b4201c00c180e000405403004c0ca02084d01a820010407994020b04035058081c0e4001c032100c1c0f07800c1e49088034003292004a4502c001c00503042100c90079580d820805803005e4a06c0c01c3c030504040d4503001c200314034052407282002e00300005000154256840001869010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 322833120 1250 322831870 322831891
    0x313063e121308040f0e060a12110d0c0f081b1c03030504020319120815100e13090c0f120807290108010c0e0904051e01060312050d0c1403 61
    0xa102e0b80c90550541d01482c1c1101012407039441c1d0011301c104903030343d44034050395081c0c48408032103444403069400360362401009404040361414044081c241440151441d80c05010500c80c0c640e2150360394001e880740c03a2711610310f661145022003005101d184102c00c02e10000c41c1d02ca8003405990201e91406950f101c0b005d024148e80b00c00150640d00c0a1080180e1580703c5240480c820717441d842c1a9050f041401c0d4813600103010103000440d176081c04c04000b50704120080c4101c1a42031142d0741100c0580300218129040607480102c2881e00085001c0c03c0c6160340305043c1142101e051404007140c1103c5030b482000710070090081c0d0f40201d02c00404540c61540c00100c89030180e22018204942ca1460340c400c442d040300b09071f0000030491810740c40580aa041550707240d94118840342000a0407505031409080c03a0801c0c030b403141c0031011003182c5281d10100c10780042080c43d620b880c1d400410100344001f20203e1800141c1e9030000e009849041102105d505280c4180c15440390b802c1c125010051002004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 322834370 1250 322833120 322833151
    0xa0303200304090203010b0d05060f0f0f0121050105280605090324010602100209030d21020a210203100515090301020c07090b090c0313063e12 63
    0x40102802110b000e0702c143c0b03a080d55a540d48140103400f039481070403080b0340b0b14503000104409140c00e41c0355000ca66002003a5a5017100c5690402407003000c0c90301014140616000c2c00220320200300005880210302110020f003a40c5042c050000402d010703442a80768180134100c1d07002e04c114000c0d41c00c0990b040342c41d206840d06244c001081c0740000142c1f40300969200c0088100c51004029541c5041e1003003a4240c0301ca0600a14004060b80543c011203941034101200380b0710118441c0100c1c401d500050408000c1100b0203940b0344c0101d901040d121800201926100342c00d0440e50015420000100e40c1c045141d46232403071071220b441505025a500c13620f07003c03a00c410b244d211442030320b50000d0018003c550300c120700c100e1140d888400e441243c94031410400b0b11200c40c580811481d201303a100e20061484d59071902c01c00c500a0282c800e0887d0701c0707036039903110000c100287c2c83d007018080683c1c02c1541100c03132803640114100000c1924000707100c07810072041b044e030300f00400f48079003088482070000c49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 322835620 1250 322834370 322834427
    0x20607081012050a1202010c090515130b0310050111031b0c220b04020c10020721121a0d0308060a0905070210060f12080d09020405070315050a0303 65
    0x40310540e0b52007181ca00c0011603480c000e010002c03840c02407840c41500030810840484100381d01307030b440c074902c4800800c5c170020080040c5d052882038801d0900b07040440c0307880c0c80c01d480465000c01116030000c4c0f01c200700c0801049061244548641c0240209082039412018070030070b442d0790f80c4149840041c03101400c01240303180c601c080080101542d00144440303404020b2051907154031112100082070503003407400c54840ba00f054800c803058803100780701500d104032007001104007950003a2421110030207aa11031050000c104071035501c00201d0f03580c2e210700c80c000714041030042c2c5102c0d00300b60081018070607101d901c40e078881e41c031007040e030f541420022080e0703503541c3c001681e900301688141500c030b08143c100040c403940840e220b8078106243c8000c0000780d0b11901882480c4519001d00900c0e588216419400b050107000134040017040010086840d03641607001c0303019268159203640c00f191f00d61640800e120480c04600d80901025150b0a004a11f075460007002511003c604002810b0302480410703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 322836870 1250 322835620 322835641
    0x70602211602120c09010b0304030c0b070c0f030503010e060a05130b1f020a12080108061b0705070305030a110604020a150207120c09140f070e030a0c0e0f061002060708 74
    0x1a5541c0007089003446050301c00f607143c0c44003081e100c0b2601c6608800d002085040c42c4405483c040c54041d036540e0b40004940e80c3d05110008013900030018400c400b182100010064841c0884e010312956809840754504a400c0c000d5900281c4500d1041417841020300050300c0c0e14002c03072071600d4040e5002c40c940300e0000100b0f03490350860b80300b41c695036a88445c04103103940000c3c507103956a04c034486025486d85889011100300c9003c1c06104402d8011002080e0403600e076400c203081e0201c3c04100c4605c0c0c64280d81d00d0a1809425500171220707030b00081828050343d6000040050240c1c10100501042d2402e03a00041110311280a071030411601e1980d1542c0c2d00740708105440140012500140821341a400c0c03014141c40e1078800c000c40745041030700800c502d0f07280781042030244c03e0254841c186503d415034152045954214115014407034141c01c2000300b00a8407414008183e400282040da09103442c0344001388000500c2580105d6000707c41036071055000130b0103a884401850040c806c0d407111074400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 322838120 1250 322836870 322836907
    0x1b0118080f0f040b030115081603050408040509040c0f0501170c0f09181906030b15011e201c12090f0b070809070503121e03040f0507060221 62
    0x18480b488042030102d1a0054040190b058540070b00f101c8140e141c02c0641100c840500f00c5024a8149000c822211420f0290304480c1c0c0091107800c04608094491002c10441603044909507a10420150100700001c080d100c0140034010a180c1902d100c54042c4044600001c060030248118100090054542081e801540d200200080c405444e524852a0000020100f51001d489107a034020482d0040740c014072601040340e5100c450900c80ea6500e080c7e00c1d9000c40100710307640c140706500c0329204040000340c840318514445601d030307503500c040801100d5505c96802a014400e1b50300c000c1b10011400382031021800d00d00c8540c500203c10011019040c0c001d8a20362900070700c03a0801101030010000c1000007244507042d581d0710888250303102c000d01c036034942442c030500e030b059002401c02501401d116030090220301d4000c40e1705107610242c2071501803980d00480d0183c510901c90300e515010004240100001061180700905a030322810b01d00903400e1801c10900e0355652000901c085140801c1c0c4240e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 322839370 1250 322838120 322838137
    0x409110d0b0108011a250308041707020f0603060f060c010905120a090510020a080a031406030a0209010515190c05070b030114010309030219030e030d09120f1a09031b0118080f 77
    0x140f03c6c00217a0b85009042c9400a44044880845000c0d40e02d014440100a40d5039587e0010500c40e40d848070b101c20f11020fa44041c00307541e0041c8403002808265150031000700380c1c400d404000010540700740e051560030900c01c1c00401d00c2c0d6040c100268000981c0c01501d280541c0c40403038a0f90320740300c2c00c210268603059210000600c0e0790710205074010030303d8241d81309541e00120051300104542e1140101a02d407103010200a500c419608010706c880d04060702410001e43c0402a000e2520a401203803400d4155800030850014840030b8214041000a00091004007480c03030f501410f40d418803021f0b0740c030f02168400880c10903503181c00318010303d4420814405d06a0700110007090021460800512944a2501c114020301c1040c1488a4540c452443c510486068090750030031074003d1f68071099442590032040e202c0350400760301041040c00305ca49503401100c140004603074801c51f01c401194a82c2c0711040c40800c69250522040400700724481d682c00442d030108603140d40e02d2050002c1e104a0089908 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 322840620 1250 322839370 322839427
    0x40507110d05040e0618040623091038010314130c051c0f1106040b070605010e04051c0201020f0d060905060f060f030402060409110d0b0108011a 64
    0xa5400040d0442c008200f59020f110485100c3e0740c0c0c4c02c0030300207a16202d0801c451041011000117001c9216a404601d410880120089440c4000784d803107809050141c505104541100544000304803080c89402d0a01803103044e00c0301c8200131008504808000c82c0c0d5200f5000550081c24022a842a44141e0391541c440903400b038036061800359494051580403040307840d001290000301d4503103440300008001640030500701c206408203a03580c1c085010030003000c60f02c408240354100055520351015101031b010714008039486c3d550504003c0d003030310f8045e0300020b152552642444081345010034880c141030001e0360000c2c614252910100d00900c00c40a80c80d4a044010890024823413443d00a90110342c0e0381c0c2824029900e54404214030380300710554641d44070300104513550141c020749001d1940140000d107080d00f001d50707a414400030b070b070700781400300c0b800300400105281d02da60f080c0304424010b0400c3c40c0500d199814095400b910080c1c0340c07201041010b0100d01c042c004925200a280c0802140c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 322841726 1106 322840620 322840633
    0x1060810090c03080f03150907271a07030201050901052e05090112060c110d031503024b040b01030b180901061a03010504050711 57
    0x1200300c40000100b04000041841340300a030072141400142240d41c1e24080074140040004c0c0894584961540d4081c4074240758410b1144214008017a804061600641c0080f07088288503405092840480d01c584640100349030041d001d08d600c240c00a200a8455211460a98504880310346d0815400400941c80c600c4c0d001081606d80071500745101c402d0789800126000e40f1b0240c00c1100e600140e9130101040003e1845020003c28940c6040c0c030001116914042d11404040003020401d500c50711008003010003840c1c1e00005503070080c0740307003040046500610520289820a01d401070000724810515084d03040c40e40b02000500300798134104a800c00c0c1080000d101d80e01040741059a6582181100d844440111145022102e0142490b1528680403400d517140c42d049014404d42c4d0032122041d01c0c11140a0700e05651085074040380c1a42c2c1e000c8201d800701ca121509031032621030788 = true := by decide +kernel

theorem cover : BRFrame.Cov 322661870 322841726 := by
  have h0 := BRFrame.cov_init 322661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 322661870 ≤ n) (h2 : n < 322841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
