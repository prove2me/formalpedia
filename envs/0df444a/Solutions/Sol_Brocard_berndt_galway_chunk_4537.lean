-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4537
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:59.65976+00:00
-- url     : https://prove2.me/submissions/d8cb99cc-cdf5-47f8-ac6d-17f9c490d39d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 815827338 ≤ n < 816007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 815828588 1250 815827338 815827349
    0x604030807021c0213090303020c0f03030103020a172806060b03040c0509010506090607050a1a0412020d0512060a031b05090604060311150405090f07110708100c090e010303030501 79
    0x756004214841081c082100a0f80760313000308664084c04d01300f10a14013030b1140303e104406040d001d1003852904007080c0107034840c02e50344a00940e12503141d8010028951400d034040328071120f10740500e0b4000780c2c01040c2090114800540648810080d01300c0102d080445200504030a1401502041e44200d090003940100e0141a911055545a1013000070500007031003107660100e810030a0b4481410228003a01d1700501481c1034503032014480e190540c41d1842c17002c401c0400c1c0641000c0004004000c0d4040e00b240320244000c002600d640d210180c800c0c82060b0b07540e40220401030009030107544020401c03004d19440310610000003034010040106070160b0150f0b51081c007a582c00204a410180b09190440390003c002034013008140c000c0c01560b10790a00707481501602004080344a40b12a11024012000c040703030a03140b40b4040200414a55160440d070b2080c0e04540b00c100120b05001848919442000c40009525000386034103176021441c076130140f40f214100ca0000814107406601c10780c100d90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 815829838 1250 815828588 815828599
    0xf0a090b040b040914071b080405090a0506010824010c0203100e061611060604090c150804031209120f03140108010207030905031603030804080f19020c0d030509040f0b060403080702 80
    0xb0220744188540c17440c2110b44c3e90024070401c1c0010365209064041686003401031060514140e190000314420040860742a101c50b0f49400601443e9680844110b91201c1003103440160081402c9100d416a2400d040d46410082084085025990705000e00c4002c00b882c0b000c01c00011940c60f0380642c039102c0880b4801100f4072801851908180103418408a0360520b0015110543c1c840082100400342c1450642d50725801210202e04405901c440e0300c45c0c400140c503440403c2c505803800a140d0841c0c07020b0703100d22901b400c403c40300042c04080031031144c8505090142e89407031000c40840050001951200c2c03207048500000901142c10b500400f4a0350080d56810007850300e65042c555280d03201c140008000024030410000700384180d004d5504a44600403992420000070701d0808a60441d40280351240c006e110740480a54041200c0001f00005a411007290441c5450140c0315006424221b4016038a0b00c80100f2a0320556220a0003502c00800184d2110b403030307052880c020740204d1070490058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 815831088 1250 815829838 815829851
    0x120f01060605090a030b1003080705010e071a120606130e0f0f0f0c0903031b0d0306240e030a06050103030c050f01050c030a1515050d0f0203010503030f0a090b040b0409 74
    0x2a4403500843d203180401402c3c441100f45180d4902452941c010140034103042900c40100000395a24002c0401c24001c80020840c00384200d1703014100700242d44260354100180c0301401c102800041035440191200c41d00466607036440c004640c043c482c072002ca00a119402001245101600f06050b00038188440d4849040c1d83e00f00541d2042c1500b6200c0e0000405032000140102e440b4000520320b0000141c00d0303e040140890080610050a008501c070340e0b0402c000407000c1a03494400c6800820340411904480c1c94a84041d003101800801c4041c1085005140c42441d40c608024074042c060f4040c3c03003000207680d01d06000f484418014400c4408e8042c091000c01c0703550741405540e019603103031400140b0350344a03412240001c0c086810551589148440001080b1800e03040c6400c8040b0715444607941c0e03030041030b108000ca807100c2003520466441440140b04a03180081507544801c5003504e11a40d40f5903030031042c3d450015692021001000001e00800c03884840c80c0980111a100c84003403224 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 815832338 1250 815831088 815831099
    0x70602191a0711030301060e100903030509040f060e0403110d1d0f122a1e19030602041d1305060403051308010f020403050c09040309140609120f0106 66
    0x621080300041e000150211061494050078a04140c000c0954240541c1c01c1601c0900d003030031600309034044004648254600c0e0035070305040110b0f01480c0c4091404105031402c60b503001e446805940c800380d00496440c203110b045034000d980041702401c0c10441c035000b185442e24005001d414a040704e07405074081d680802a0b46402114050411640e5071800b00700c074042c080501000900d529103965000315040400036003a00d040c00f504071064403c186581c45e003100784005007107504c010b0b5242800364102807100410000c400b001506400030440703804040701d004891110081506800140840c2d1000400288802e43c1c081c07070400c0c0324994040a041a507a50203810ac08102e1640050031070b400181c0000c00092194004100c81681860f80d00650754031101d10782e0854604e0b840c42c0400030384c001014010700600b0001f026881c18101c0d8072400701d151542e4000c10f1a54903200d15200150b0407803560400d80d480078141c0d24600000380102c565140b03002503040e524180440740e01c40d10351920401150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 815833588 1250 815832338 815832373
    0x3070803090102013c0216110913080d0e0708060a15150f0324060206040b010b0a0c1e0f080d1a181305060103030f27031202011d070602 60
    0x1081c03400d690024101804885a25213035172420044800307050f07801c1005a61004800042c20710440c0540401030b0122020401c0c440c240001802d01c2d4000b102591900000844040440c0c0c0780c41c0d080b0b9008941200310301c219a2a001554200e88698040c000c1040000c01003a40040034240c481440e9200315a40e400024441e0042c2c600c1e4600094a00d40e00700d00c500c3d003c6d0300100c4a221500049a400140f050000d0800110b0b0b9009000140c0000081c0400e00038541001d6002d40503001d0418034240300090b01400400140703d000746045201700c2c1291009032042d0103008502d410a0f00511010740614143d185035000c04041e00d15a803404d40c11002d511f003800303103400c0c0200000d468070b0b1080315892401805c8420092079007580c03401541010b40010720901544d4001d6100391186100381c02102c50150291442d010940440003249010501e00001040c0304c4045980101c0010101000007004034050140b5051080ea403207a01c5103089014000000c820003101e4065003950013220441d400600c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 815834838 1250 815833588 815833631
    0x41b0e0415050904020a0308030c070203010e0c0f1207091a2713140703060221040206071212090302030d0f0b1e1305070206150d03021213050307080309010201 70
    0x511112100000d000600f00403902940082c0000c01040c90307039681340c3d0340051039482258aa011480d011501c0300842c242400f602c3c81030519100500300343d20003080460403101c15100300a00c501088088844031442c00d00c03090f000b600e01000244044030428090ba10580341500c0640e001e804002c080001c510912100caa4080400d100480e000381ca9801c0102c2c0c4005410809a81d001c00e10300b402c032540c04041101a00a40c4103000150f110300041c490581c200c88a042c200070002c54100c104401613550038216501580c1c00301c0c080150000d855011108400c000000803d024a428007030f40600d030300000940314050810320240304428503650326000380c9404003a0546c000801c84103c20140784450a400b0320341e880a000710000c80d5480206070107032030080c0d4142016800610a100744c1c0080340d400010010002c4d039032422007042542e0001c0d9101c5807040c01808030207010442540d4070710000103c00082c5070040480303418681758616039131a41d00101025000d5840c0001e910b035261400c00285 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 815836088 1250 815834838 815834861
    0x15121f080619230103050a1103030a0503070804031106181e030f0d0e0a060e0d0f0804030e01020c03030406170907060903080304080f0d050402041d0a0303090f02041b0e04 75
    0x514160482d2000d203409800b0b81c00c00000d01c1074a907000080c020300d070103004600942c000c00c02001c1c40c16003810315001c808031034003a26000740c0080081001c1c46401c01e0803a43c010b00c0c1c500c0d007070215985a050846402100811650081c00780c44103005022030a206003800e8486400142c1d03000c0340c05a10070340351a07005034040104a801c00d10040407440c000d00c001d88a1014640004a80090214001d500300000720400702d5915644490b401c5c206030007000232280d4010f00d03040a0403c444079100c05400d085000304020100901600340100a9200f800086080200a401c490b1543e4030303114054008514213010100c89540013000a080500009d1030a00321541a15518401070668035004060303480180306a41048040108040b404003030001800c0d0009403a00004960800e0710400c8160360700d1300701c1001e140030300b822000c10282004c110104c40e40c1c0e140c01e00081007a030a1500419944130420003950081c03410105006e840d00c0031b104411503001598840f07508255050401c004c40720307503ea40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 815837338 1250 815836088 815836111
    0x4060f1809170705070603020403021c0606080111090910120b150a091a010f0e0d051203070f093303090516090c0801031115121f0806 59
    0x81100030034001403480514580c0d10003007a00d160350384a101410074001d0310411071102c0050a10144142403222001a20540c901903141c04e180d070b0000703540350340c40910904004c90728500d03003410001a54801030080034814000e2084812803078048110b07801c602e500501a84074200011303d58003500c0140e0301a211038030307501c81166100d81c8a200c07100c07200034000d540200c1008400107981da9010740c03000c010002d40d1004101c0c1c43c040110586051a00e05e507490500c01103615806100d50004a1403921318030036540010f240300f940c1040c03864558003060051040b10000280302d940d0f54844603c0ca0340044c5615100041030fa40d00c140f9010306a00b1800c040024204445034807454940c084040e00810700e03140c00b0070340b0580ca44495051120f001c0d07941e442040f905600b00540d1615020b400300d015407500740002d5661540e00c0c1d5075503c803485410b8510483c6883d5001046640d80000e50b8160501e850441141d0320340984d0140460049102c8840d00c0c45401c02c1c00100b410740041d0f100e1041c00403018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 815838588 1250 815837338 815837369
    0x2160803060a05090f0c0307050c15240108060f0f091e090a0b220b10060206090a02010903110103020f0408150a050c12040213020d020d050709060206010608071b0809010e0406 77
    0x104800d06400103090381c01000010442c14884550810805417507103c81030100040d400e0190070cd4003172001c0402c0440c4001c001e0002607440b0382e00805e403a83c1c4600c09881e00d19405162a00040101ca030074a030980d841490301c0280500070185003003600300302d4a43d02c104865600c03041c248a507030b070401e400000c00d00c80001d03000130401c4184c1d05c4042d6000300031801042c84207425985060340f00d0710486081d2070600c41c10008000150313040055031742005914000d0001d24849400007802038000c0c1c000a8241580441c2003055a4403e5040701c1c07105008849079925140c40343c2025485080040c020a490000c00e00840e000701c2c00c512440780a000c103e8680c92400c2c0d24a03210181442c0e0052041c0e80c08050028100608a45400200301074504141c0060351085400368850440700054030b04010000410300a1040355000640117065420300d050483e03c40c1d940020031100072041100e0780f100e034030034180704004100f5808040c01300551300340c0f0b5030b05201d1104018071084520600c20000e24880030030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 815839838 1250 815838588 815838601
    0x3110c100c080126030d090f05060106030e03040e2721030705090904050a0503030a0213080606280f0311040b010815010e04140f010305121c0b0402160803060a05090f 73
    0x40c0b00b10f813040b8485055030f0504d41c0c1e0f424103070100e804504080d0344054441081c401005002d00c051400340903941403c000c00519890309550701d020f00c0c060301003019500d40c0401c80c3d980307080c03900404920303180b00010303425031240e103184d030f15003140d00f007042401c0e007441c0307155420300f17440c042620321a4045070b60740c1c1e04022241041004480c0040c0055509001c5e040108004c40c2043c0000d6205805080000d80d9564030716128195100040c1d02401042e0000303018801d0681c0d03514900f802d42c0c14100000100c0c40034903101100302c880300e079022890203039200000004021640900c081b08036811901000080030100064504a808543c1116400c40354a2a90b07174039801510350b0074080c8005040081c40f20005040c0089401c01034800e40c0340d05051400400030020200030204840309501400d6003445a41d0101031103941400c1e5100c4082c135285d420380349580e100c1e40d054910000c03480003007525840d100c1c1401005540159800360180741803a502040c1d608101101600580c5d9441001d19140d4654 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 815841088 1250 815839838 815839889
    0x306060a121a030c01260612030d0c090801020a09091a12060f091c0c17131e0308070609020a030506070518040b01020c0d020103110c100c0801 63
    0x44488000307018106591400900c0ca900c12000030089800d1144401050101098540403890444a04105072503070b800c805900900c03117000c200d100045407506542c60340000124010240c02d800e506500c0301103124031824425400001e507a00c0c013030b215012800d0b1105e045900341d1040c0071079600800e610100c200840959035110074a07000781c1050f510110581d4800243c4081d00840d040c0d24154016402c0c040c01c3d16070032100341d42000c1880d008190103140c1104c3c405540303070300c54101007c0c84540a03a4900f80070b031038055903100701c040b010490703a592182d00342e195854155000c0c0400c00c44490403440c956811059003102604c0e040b05c0600c1c1800c03159614800074003110f94003281c00c4520b5201c00030005000300700f1640518500e44503641c544940303910143d00d2155200801e0310803401e0510030700300350341c01240c400d240790030941d1410300c9801ca9000580c040c00d401d500384068070000041c80e4200040103c1d0480ca5240b4032842404400f1020904603004e074070a00884101000c0424014054100e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 815842338 1250 815841088 815841097
    0x40f03020106090f090606060206100e060d15020307080603060112111903030203300403031d1e070e04050c19120b1927080d05070f12050606030606 65
    0x24400071075440d845594810a44d900b41181e45081600d4000a0082018500404c40600b41c07610003040c241c60300300050701644030917100c0d1980e0070b540311000c0b5565888082603d61003680014840f031000c84410700000095008660000000b0f008101140715850b02064460488840061030b81c0b865541e41c40300745c40384040e41c0e01c00e5842a0354401480c042170100c4160001140650059500c480d0301c0030b25100c0742c03d41041d110345030583d8082400c1c0309040036400d441c2c010b5018503001030030240c0d05101d41640c00003021180d6452141c05404820f501c031400380099928400000d071200c1580c0c41420548040050b00c0080164010064114803800c00c00d42d54003012085648041201e9980c522000035951410801e545080040c0108020f240e2101c18480c03106410040c01c00c400316460044033300c594041400640b0800c1c80940400611514100351085142445803c04c82403c00c00009403209490b0410b01c004101e001600c01c55503410381c4a07003480b03000301a25203459552060108180ba621 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 815843588 1250 815842338 815842343
    0x302030c13060e0708040b09030702031009031803140c010e030d0c0318030302011505010e0307063527150c0415020601050301180f08070f2a09050609040f 68
    0x25581c2d0002200000c81c00428000c06064440380c1090401d804d0110b0400300003000444240d104028501c0144c40c00100081820340c008400a001c0400d49412660009580e49903a2909024003002c401d001d49500980300312841c0000300c80031280c841c001503e254109070221036154100e21407600081f8050405070509900c6440c1151503c052500c000c55040d43d00c0d00700b680141c1d0760b0034007540c00801c80c0340904094102424080d030071400386000a40e4908003400707858200001e18041070342c00d044c07402c580c1400b00d071001da00090f848008000501002001c880482c00910307403811103c0d248103c120443d41d681e40c1c1401500c8414108000c0500f07800001d410070090901c00c200016001c4191104040100155405011a545407004045c01d4852000228034080740c2c60312058005461607860540b4560311030200c68545449080800460401c090064004024000c00248950608440c0040c02540d031028000c050b440d80021400c547d42150003540092407070010401003090300105074803042c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 815844838 1250 815843588 815843591
    0x90311030109050610060801060809030a212f0c0a17091e0f0618010c051c05131202090601030e0a200112020a0903080a140f03010806100302030c13 65
    0x200303a8401d8a0a134080740e203d00030500080e0140011369114503014014480743c9802c40380f40c24940c1c50140c0f03e1280748140700621540403840030562544d464100c280c0059203004102c03881140401683c0c070800c507903d6103807010120810400140d101d0342501d40d07854104008000882042da00e40e96202c3c072114043e0741c41002403004804075034034032080d6080e81081c95811800d141e100014015080030551940c0d10407041444044030b102498086014180c40074070b8220040300e80c034102542491010502e4100206044000c9004503030007030700409030303070003409254080030f95a49607000d2018000d0000a40c001840c0c8007040d120340c869000b80c0b003078400040a46550139001c3d942d4010f6040c90a20b4000801d00e0042060925a04405a24003950000c1030952070b00e80190001000040e0a000042c04181c012400320fa01901c0f4030300780d0b0500c030714400750039a4a440324150000250006d12405101e0f200d10b400089401e111a481501165805002000091801390030130160440c003c2d403003903045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 815846088 1250 815844838 815844851
    0x1051014031513020703021b0609042c0708190b0703020304021c1112010221130b101a190503090f010f020a2319030b030105340903110301 61
    0x1c3c0d03509800d050302008007038001070f5201824a800b90030070b011101c1c0300c0074540c591034480b01251280c004846209404450000b401d0700d4005040c1080c00350000e805580c002042803050018a000400c8170581e86c0d00b100b01ca100000e0a0b0b4854000c11014000500608044021664060082d00a150040d10081c4160f40c208003075084403101148409054030340c10b008900700601b070b00702961070501a40c0703460025403a2607a400c00781010200e0480601052180100016a00201c4c40428441095020a659125040c21115010142005d0094070f40c00440c56038204402500303102180d000c04a40303801081c50300d02c148030aa86c00c0d0001010440725020710714804620300400c0c81404c6a90111800c016101c00700c9042c010842c1c98103003070341d410000100700600d640c0114a410380c0d5401800014085540314032410440c054215080c1594243d820842444404158100605c0510190a420a8880409182044d0792100743c8010501080d40c06605102182c00008800f01c03003500500049440c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 815847338 1250 815846088 815846131
    0x60302040c02011b11071205030909040f11010503011d0901061a120109021c02070f0b0106020a050105070e0d02061b030406110106050f0f060309070803041701050105101403 76
    0x2a118507040c1c050050759181c000c0d1842c0050b011000c0464515840d100d08044045004107542d070405004600e604140d4110100800104104481000d03902070700245413030900b85403081005004400c00c8a0480c8005441c4845520480540341262800c400b00c00c06420300150610380c082004d043c08106540b950307030209850301840c82c00303460341c01140221961401d26007420440342a06801101d20140108003c2048450307803004076003045040b25006aa0780078a2a15007460031104400070040c034041c0f400050416008078504900c03a00410081c0100e0380d13030b080d0480d41c508010700303500da0040b24040c0580150610a001d455081c40c10402c04005a080d00b00d241d00c6c6821544c0702c40700161209120308081d24080c022400280f00c01c1e6204202c5c00e013028001600f4640c00d4140074050300300031000422100e0104040710083c0420000d899403103840d41148080580139000c035902d1507003000d000044a0a00c0c4901a2941e191982c030700340c00400007080c12002c0c0e40040d000b203c09181001d400c81c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 815848588 1250 815847338 815847341
    0x109030b060d060c05090a0b21130507030b060108070201270c030602030a0213080c010203250212030c1e061617070c06060e130b060303040e0f06091003200406030204 73
    0x10b07104c2c442c0c0751152101a030030200403c05005070004002840140819135890304040020380d02d00c006481d88030a00c2d610f0006a80c84002d240901038014801c4480000612468800c1240103040c20307a41c4482c1a500c24809900381c408884900c00c00400344071380e40042d2000d80c50a4007400e0300c40c000031002c60340d6030b4480200341d8000b0340700d14519940c0020240e03003d0b60901058070041140d50054055607940c030001075124010358495a010350b441100c0702501401803010455842d90081180c02401d143e20540d13075a82c0c000c0c000000141c40f401000260314409401038090081c45400144040d03500c8607018a4110320100c82c41c3c0c2840016807a850000e040e031021070307103e14115079800441c03d206d03092500c2640d2041d0f2141c00c940350038a06101130106006103008603260415580040e07a00c800c800b0a28620a41c0d000d04000c2400106001191aa590381540520300403a0040e031540ca51940d42003030620f007480010308523041e0300a4140491000e601480d000750303004100181c0c981e070b217030003240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 815849838 1250 815848588 815848601
    0x102010b0409050715080f010e0a021603390807033c090b1b0c0301061205060c04060503220f030c1b08030f0c0106030c0b07050f0c0109030b060d06 65
    0x80d00c41c0c102682c288508441074116205040d22890712141c141800c000641f0401c41c1801113011000c0c005001690b41083c0d5012200c094061040e43e600440341420000c08080ca940c200c5015040016014828650100300303030236400d4407518070111801495a910303a011f42c8101411424020f0b2020242d0401e01010490a034207505455034410000100c00b00300384d10011032a0300420f1049041c01808200708540aa4915041725a0100040e00140d8600d601c3c02c10300c8951035626608140b0301103076081280301d100d00d0b0b0500c120211500d80e199501301441c80e029a01650002400c140300160707084204200b407100b42c071444a007410300109652102009019461011303404200403a815400b00881e01e2143d454141100c401c01000c40e0400c1d205a44030311401407a901644070108030007446400a520983c01564840d210302c03c0656544440d0409401071401550680500506241070f6071004c100c0d042c80c4807050b5180c071034090469580c0b00f81d802c0c01406280c0c004c1e82c941c0100c400110340d0721804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 815851088 1250 815849838 815849843
    0x10b0a12242304060608040212071a0a1202030f0403080a02690424090b030105090a020705151009061d0f0c131d0a0219030b0102010b0409 61
    0x1615003841c101482c900d02a518244070302944c80c0420030000180e010315643d8001d070f412109500c1103007009140301c1c60051960403040400c01e1424400d00b0b403039500c00040c103c00c8859150b40400d002002e0003101207010465403210882e08800000740000d00c690070040e0b00000c4418011305000821a510101d45500f00c04402024403d684014948040035002c40b100d036864034443c1d2720307681d64890f9000c4404101036100e112907254074a000541c000141174401a148586803500c8165032000c4010044260703180c41d00100303000d4040405d03901200002c0328141c0c0d2014080f0300c00b644400003610300951000109031654012580c408018074260110f0a00a201000c21a00c2da2824001d0f075004845180d800b1032414010020076980f8410003c0c4542d6220103844415075036075440811740d038442c0c0704084e0200111000c00341c000c222501d02c2200f0702c2142004000004296440c894400101e220b110741100305190707480d40b420417140c840d800954004030180b0003c94141110400b0400755007814508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 815852338 1250 815851088 815851109
    0x70c15060302131503030827030304260a0e060702061206040507020106031106030403020a12050d050106050f09190f0e01030512071a0417040605030f010b0a1224 71
    0x300150314105150352108290340004100480550f4a0310401300709a1000800b400500c0340059000d458000540d20b8000d441c26054140120300d00070603890313501c229011030f00c00d00d65542d0440062104080e502d800201501c4603031914503521402d803601e1442041a6610090400850b4010307240d400280403603ca0f002c0742c04645050880422003581d100405000c11685808001c1022a80e032000c022030340641900d80e0b66070707521141000c90500b1803420003e01011030f03020051010a61180040015101600c2c0401582e6215101281c1c20b1040c1d09684001c4401400420381d64901040316078802448910300780c07000e40d5a50764444042c030b40c0b540314000001600307004005014051144000d003440c0d03004038518140d0650b680d01800d914035412802c2e81201100042d04114401400c03c542c2151109102d0300c6654503940200700c0d81c03080b0303124070b1000a004000100400d5400588140442035264082041070b4140004024554200410300d40d242c545942d0b0034000400c80440b004e015020907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 815853588 1250 815852338 815852351
    0xf0d050a0606020606010905010c0203161805250302030a0b090901020717090d080a0201090203011b1806050d11041206090201080c09060d0e03130f0501090503030f090603070c15 78
    0x3000800c680d8103a0005040d504200701704081c40e030380140f1500a841090902c4480c030401800405e00c0c0168080c4960f008448050008c6007020a03030700e450684212882052041e5501e0103058142c1c0c0100038a1000321206004c05403041c2c0e4003076000b45500c00592500042d07000c040308005002c0090580d090719041c0d500042e03120910500750b0700c8031240c03010210542d01d0708281c1c4004c9407800803c100050560200428040e26081c400e40002c001240c004000b408039103001c40c0407000c20080c100c110301c041810a010b44114145210528085130355a8840c18108940c0008040190444c24034500004e0004c10000c10a0003002c214180014010341002440e200e1620001d014044003814a201040c0148014009030740c8900c01c4902048903002c001c90703800c03d9400d180d455401101001c18800001d01c2c40418840a00e0381c03004115003090f40c448490307a03034440903d0b07100e105031101c1518140040200c3c0a181c00e0490045170070450f6440c083c5598041e6485004201e01c0d02180c0c4160151280d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 815854838 1250 815853588 815853601
    0x31b030115080c061b1b040e010c08060f030c1503010e0f091b1302030f0a050c0f220f0f050a1a0304060b01030b030d0207030611070203120904020f0d05 67
    0x100384600728020002602000d82403440d41030b55000030359407041c1300d001c000030341c49480a1080d103524154800b250444404550724505034194010039062540524500340d104500b242c01402030343e005500c0340c0c0f2200c25a8440506111382091010303d02a01807081280003407681d141e0a46100026100785c8050391294140826a0034110b000341034003454400500a1000b441000f14100500c16280300d82c0c902500050303000f00740c9000030140d0714070030140302208000c1041c04d104071452050460a42c104010313541d07080c0070350342809a500700d9484d25105000561003c01c00c80008a01c07248612910341c032450b03071074100744032111081d0444c441d015020b0100f00045e007040c10b000c10180c60f82c620310b00107400394a030300030044d800005c00183c034072501e90340100300c6a40030344d008030071030b07003003e0242d07002140303030000c0070359030744614882280d0350303460020030802ca41c20600079510883da00030041d02e041d01403041c280805401005034554050781c200610304506002c00014441c2c1200c1101c041341924240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 815856088 1250 815854838 815854841
    0xa0c02031624090510030e120f280516020303040e040503041a0906120a06090e010e10060e010303051e19080709030309091d070602031e0f0405060c0c031b0301 70
    0xc282c84824402101002d020300d031703200021411084040d19000901c40da910f840e0134130301602ca000034250390b840015864260b032003a10040c1074400d01640030590180c065045010594042002080056410b00c0380c1e01005850242c001c0e40c10707000030112420140c5038205489403c20565080701d0f65840020208241142202d0318400ca2580d0b138604e80c10520b102c008980c5a01c201e42c25414400c468100150600340c0d607502034000741411000810608501c0d14000707000f041081e103941614440c0003c403e5140586018107001d544241c2581c4040c3e91075541e058940750045e88080044200d200706425111203c0006030040741005e20390070201c1c100042c005081c00b813000d0b020f64200203441c101400813a4100d2040d404035100034200188444103200200d20340a4110000b00150050304400540b60b907002001c0c24044078007d0032988404c1c04100410818031802c0100074404c2d0080c04100114034045c0050101c1d00c00c00c00949a24519a2001a082114081c0d40030480900380301d203010307182000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 815857338 1250 815856088 815856149
    0x1211131b020307030e011b0b0109050a0e1b12030409020f041d06010c030e0d0807080406020105130f0201030b120d020717070e06090705070b0708060418080a0c020316 73
    0x80d400030310315003c0552001030000701122949030501c0703030f040140d40a070402d8aa04480898106002d0081d55840c0c200300d1006d08401c0e1886a005418192444c01d26030002c0f92440303c1e200404040b2140314881c0b8280444900c2d4142c00680130b0000b4080000c540046000406548050104260751181070000c1220006144449407a0b1704641d07008110459811a8500e800c1a030941040701e900b0803003c0000d0350704101c0e078070000c000781c42c0401d4102c10080ca00010b407007940d600c1e8000340441d9840c214011010115100007804000e10075100802550090f03100301500e01c005481e003549011440341c080e15058400d800000180e010440402202241e640b8015510343e40102408460b0b240510300804508064000c5206030241804a4002d9000348100e407011a03001020028910348507001910454044480750b00450408002d030050309003502c0202495580030640b00c2c00c01d1041d200c112107000110100b00e80503c00c1209015010500c00000c000610300c07204040b00c032a0354001d091240900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 815858588 1250 815857338 815857391
    0x507060804030e1504120311010b2202160602070807020f0405090d03020c0a020a0609031e0308242809050c0f0d092117010609121113 59
    0x504040c03200207030b40003c2070041c1c280b049540444200310b54168280303512850348591007003e58031100d03c08050300a01e500301c11399010030007080880c1c0d400b8144009502c140c20b00c2400c006141e690181d1448050f4087c00da000110360351140190103031b940e103000b2030f032041c0000e50f514080400c0520031803078800341403254141c1c01c1c0d4050040e820400c1140c1d03905c2078010f200009054020442c000301d100204901c01c083e5030002c1c01d03e4040ca43e26100904000450701003a60101c111030340ac0d420901100c9070440896030701d6034944649a80b030b02503e680480c031400d101600c6440c42d842d200b100f070b940c81510b04c500c00315492007100e1760341c50750040c030034102d00a62009540600340010009405440f6055807001c903400f001c4180d44441d100340d18001841c00300c8000b0b0403c00300d001c0d90b0054410109602c1c9643e005500c4e4041444191541001001030900c603042c0062358040050007031039843d00c0c011080318800c02d0740400b00c0402c00002036a01c1d05071012454030340cbe5100e0002600040c0410003e50799032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 815859838 1250 815858588 815858597
    0x20304110d03051c0b0d060525020703020108090316030f1808060103060c110105010801060e0f040c1e0902030108010c020d05161113050406051005041404020409080f16050706 77
    0x48950342c060321900a103042a0400130f10b604184007610301540016100c00070040108803849000d00e800704c000c10058580030054240d482d01805810a0013103240319000050700180204da180d58011180540014280b0a03640014401c00b01011010307803054054500c41d80b03a0458100f010340000309000070410002c83c45c01c0c0c400724204202080850b809054903000f010100303015019601c140d036520070144030010190718042c00004e9818040d48100e00741c0d0b141d03150514140c1c80b110130882e000b01c801d83e00030f002c540c01580100300015012131151202602154442d1285a441c10070780200c0c0c00036405120705035180c0440702c40c0300707a050090036410388450404a00b03100c1085039844480a034210700400d0300c5135000394080165100b10712140c0c000450101400140351500c1c000000d0700e0143d50111400d02c2d1880046514a4240100d105d0305400112010b01136071203400300006005180b800780c886040401c1b002c0903a04e0810020030452200568a04507509140392152800c00181d02c04010803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 815861088 1250 815859838 815859859
    0x110406170603011d010c09090203060f01080405100c030e06010b0408030a0e0118120c2408040f0f05030c160b03011205012405030c0d0b0c0a090e040602030411 70
    0xa0303040341048210140d21140150310380d4030080031900601040046070038000d4164030321100000c054000d0031039900c803541d0700a40641da6844a1080c1d0005492007980400e0f41d07507060300c0c1c3d17502c151901c0364041d00881c1200d05400030700c220002103a1122196900003600c9154034503100c00e00b0002e0b01c2c0142841c840c502c1c900b41c5461a000e40b41e019480300c240400c04507400c400340983c4a10314072442c002651402c0d0140750340d40e00030982c2d0003403590012209800740c07810014603104000d030000c00c0c0e1000104e0b004c0701000406021148d0001c01001201c41003000300c103201c082100c102c01040b905108100445d691051040e00e986010880341c040c5032003c2e20000305008882009065034110740080c4481c4c000071207245000340c0940441e480100603429820b02c0321800d80d11543d1080308540d070603015200c124180105000b0240c52188000e040240f0400104000d0400312008012010352861306452950f00d41ca1031480200c1e098505843c0d1a0300032044c8000c1c408208944500154126003e0f1403c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 815862338 1250 815861088 815861099
    0xc0305060d050c10091a0415020c01050d1508010e06180304060c02060f120f07030b1c3003020703260403081803030c04090506030a0c050402090609040914011104 71
    0x2101540c0780894040c0e004ca10f25400351070301800b400300261400c40400d41c140c0034000a0303004a030304144516280b00f0640c8000c1080c450001c5600c003d03042040e90382c07510780f24010041c000a405400d0500101609500d0009040f00081c0703c2c504280d100e80f0301800380c50814048140303001c0011200401d40c2d410401040100c40d4015003507403019981039074140d803500080a0505854024a1104000c1811000030800c1c54660201c0c183d1140c1003d40b410042c00e881c4205108510036503e0740031150712040d45022011030104d44400d12304c44050488180c031f241070404005050101844000701003900480c42c4000c058000302c4111030705441492030303042c02d0420b05854140003000380c03014060042c04004100300c807043d01c2c5140e960101c00411242e881c100380f4818207042e402403103101c1c2414a080082401c038640400c40c2010141c10407552070206040c01d0810000f94040c005060380810100540300d1241c51324003860100324040c1c91071000c140a00840f02d800c0d00c11000f280d0084035001c0205000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 815863588 1250 815862338 815862343
    0xf08010203100f0807060f05090301180b0703022a12040e01030606050609090402010e120a1b06030b06040b090f0907030e1b0102030a050306041104081011160b0613020d0c0305060d05 80
    0x12103146d480d111700306031aa440207a55a00c01c1e13045494055092900e44400b003031406401d20b080b1841100861969503541c41308030100d000c0e84500fa812600d00710212000c03200242503200b141e0f40c0120a840018080342855546a400782d170140c06452000801002803141501ca44802081c0942da0b0b540780190b5040021451880100002d06019010940180c1910b85620701441c0c0800c500880c3d04c092107074200580d11541020031004440301c1c0990208045109015039031640038060040da00346070611a5032a40c1303070401c01c1119080b03000d0803c5860741e030f030324518054099440c1391800183c070360840881d9800e02041e50144482c401d020381c2d081d46540d034004101c400c05041840d0071a101d0311928001000303004844601281c9002c0410080340202011540c0c0c0482c040003e0100301d20128103a920440f405081c01201541805140813400710345500d248540c8140d000f00520540341c00328890000702d0700b080203075070071903135403141004120b9806100300760b004102100c42c0300880c00140d840380d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 815864838 1250 815863588 815863603
    0xf0506070c05040203130506010b0915121603090803152404051e060304060203060108070212040e0903090301150501020c0108130609020105070f060906051303140309070f08010203100f08 82
    0x34059903001001911400d4030007043c00f05107500c1f105031101940c4d100b014803041d8003d444001e1048440110309541d54054404070381003460454819503451341c2c0c102110b0142c4000764101c2041c07648070700200d00010401e10096115810760b800d1840003c1c4400140100100302074001c0e01c4082d1954103a10440f440d000698046490884554000805001c1200c005000880d023098101c0d00100501040201d1900074506c188820b030380340300482d40c604104a2360b990071800108415641088284908640d80c80c0b0950721074100c804503490001ca040109086602440c011840c003083d465042c42036690610500714404000d10704140756043c000d091a04500300ca5400612042e51540041c04590098007903c629a42125000b160441d65060003009003500000403034003e4900000039158446841a0180080c0c055072020316803560b40c4100c160583c4007821000c018480c4440c00102001c107220000040e0030383e5000503817a4140703695614047d074459001107010032492107080c49088800078010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 815866088 1250 815864838 815864849
    0x212010b0309120c06060f0d1119050306190c020c010519180e06130608060a150b0c011b090302130b0d300212160804050301020c070f0506070c 63
    0x45590b0385800502602d4040e4000480c01c24410208110001d800301203105485440250340c9000319104070020810030600c0101c00800300004a084074519041c03d036500340300000c10703c000311041900ca400003490104125558100d150207540c2040795005103020b00309441e105070000780294030100300040c116004e0602459a00300050020701081031240d9403610aa1552111482d01d00d030300c8401d055500b11088522030b0068990b9080603124020b03a03c5010120740124000c0c20b203640b174260242d0b000c3e1040c0c0a0b40896180c0196001c551084a10700402802c0405c4000041d85003440c030701d0321a254015076191041c480b40500400158458810410209a4000d000912103011034006070801403004006004c84407a9108100452100d4003010441d2006980e03007884904807030403c82c1d0300d08940c0e101c414210024070050096400900055040601c640d07082820640c8030800301c0d00326000001952900d50140c0e034100174a081405d851009014140c4070285403120a40391450224124883c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 815867338 1250 815866088 815866109
    0x30c091308072a080f12070204090507091d0c0a080601181b03020705100603020f040c020a0b070206010f1403070e0604180c1e1d0c120103060c0f03021201 68
    0x250710401191410305079846038883c458000403003104102c980f20541900400c1c085110344068854224000256003842c000b0000040e840c003959542400003500f0005c8086500c0d101d40709010682e901c85001d51700d480e14003d107020700c9200c1074030700461401c0306501c43c5900480780c40070148080800070403a181915a044400c603114965003c0e10401008108507403041000c9086030300780560b07810303002001003030b004200305c824080f00d00306000d04070b03141840000d5001c0f00000b04c0180c1030070640c01199540c42c550050300c205401c1900c540e00303d41c404035503000050708084010300148819407007001c00b42552140e005860200304020990f290a00e00071812401a00f500194a641e542c0d00194807250607110420002d0005203056a07003244240103040366107a8907400019507000251401080303030207480c0d40105464218440d40d0030002e024102d00c4d0b28840030002d401c49464003401282c0294404d0380c00003045c6032083c20091044601940502c2010b004100b441021040c0d000c440f4152071010340c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 815868588 1250 815867338 815867347
    0xb0609040203031b0309041103060901051003090219030c06051e031008030c010606030e2b0212040e0109050f040302151008010c020609070501091503180c080c030c091308 75
    0xd01d140110305404940070342c0885204d01d5548080701a21084106070760603c00c0032024501807100e40030444426030400000801040640380c51051403c1c0c0b50404e05000812450a0300812242d50441103003540d8542c42001c1001040591182c0c44000c1050f072426909251085201d201d0035245100b502d8174020001c000302d885400e041c00b2000007800581c04a035a20181104007070301a00652080001091600407902961000466031140a03103040140041c820007480100c041c0035030480e207510031803003849c203107001d104c41042c01000a4020040403000a6140220b060150380004207062055400c030b00900c000680c00013240300941416415a1109503621024a00c58020a51200d4519803e10010404880d000300301c09020301111400c1e1049251205d0064800c1d401e81d104d200e403003156210750759440d41d02c00d900034101500c15881040c07640401e625801017210503074202c9141c5403c21810030450389400c124401001406842648540c94601410100440d40c5000900356420018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 815869838 1250 815868588 815868593
    0x510051804060e0102040e180114060f220908120c070803160c020415170708120a0e041d190213020703050f1210060203070528050709021c02070b060904 67
    0x1015240a131604003684045c504d023030f4058140244824100005c0b951912101600b51000d0302400ea1045001900b102101503ca40902400e4914000c801e000c1052039650050349084038003542c4022406000f0071a03d41d80c40c2121010010005404220710200800c0628001014442600c0d03000060341e04031400602141e20179180d11440c2e58009500038508031240058100c0351260306d00b500e46800e0003030041d038412649030755a0302050142d41a9640120546013041225400900510080d481c194401845480109007035481c0440c00c0001c00c4042c0b485001e154904000d050344031000742400c00c10401c03545c0c010406160684014940158000580e1030038103001d02d00f1921a804a101800d1307231000e241500b032442c0503042c0e40148400c211901c000a03564400000c2c1d840050300f08001d010301141c4800c81600006560799240c010340c219004200c082202440518014810034101507543e0500c0001059a426502003015002d0b10512624011560b01e090607a4064400e44901c52035485070b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 815871088 1250 815869838 815869841
    0x22d060115020a0606270506060f090d240b04051509070c0c140306070809151003060c021b03160e061f050901020c0a060f2007090510051804060e01 65
    0x100f0050a228107041c4001080201204a8505810b1080300110182d20030440c035402d94400b6540d1651102043c0080c0100300c854a0090151001c000c2a00700e824a02d42d440c030b82440740104080e18400000301194a040740a40900b1006000c101c0d02006149400e2070b05058140c10000c04602820440000803510b60062000e003954035041000302c0f043d6035459404554000040300d20074000d000e0900400d840c1c901a842081c000d0110740301404126100707403407001d0901001807100703003c55089040080410a035107d120103801c03d0303034003070312629500c0010840507008a0301c85070b009074031412001e4100484086c504050300e040350401d0740d445d140c03540050349540b0032221414680c0788940800e90751541040040c00003500a03002c2c0e031113031a101420000c0703894462260402045610500002903441810001105045880c205070719618005405103046400d0b04506821640e0300180302c040000c0c403821900500c8111a80c2c1c0540c200303c0b10346400312402520017461140c507003202c12800c410030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 815872338 1250 815871088 815871103
    0x304060f05060d1202072d05090618060f040c08040c05031c1b08040f1401051303113007050301050405030406080705041508040b0f0106021c02010219022d06011502 72
    0x100d00c40c2070380402c0301a8550801501e0b41c442c00070344087c03400580381c100781400f1441201e001f0464401d031402c0f9000c036000c020009064951041344412240b480365681d20400c1e0400070b0356075860910389041d1814401c402c00c01c0c3c018a1090b805458440e03000e41c1030403894190718003e4a131610b0303072103c04100c00700a4902d180d001805220041004242c00c140600c0000840c0c03581d0501e14491400800103449034440c44d00c0035400e00e1403c80091001ca1404640540c000c0e40c0501589960440401401101122045006429002054415104101080036001600702200204024280f583c1c4265413480f9510811040c80f00c0c02c40010481c1380200141d400400b81045007c034031840800c802040e948040318101c0e400e00305c000100307203222040440b250588059400500d1888010600300501391860030000c2e003150740810151180300382d41410ba203201c4119800a0064140104008500e08607003035a040112000c024075001064001407814110342041018800030021031030101d040810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 815873588 1250 815872338 815872349
    0x224090f0420031608060f060315042a050f19020f0d0806091509240d111206041a0c12130501060906050f330304060f05060d120207 58
    0x101c4900950100e41010015445203541c4d0300340410241189005544051054810640041584820130300c54284030000b0350300700d0864220403008820500028007540c40038480d600a42c00c014581e460000414a50301296880c64200507007070101c40380b10542da40c054084403803040310300d4603a1446124028020202c8c036030510003e41e012507100200151200400381c03069409229254000341801c54040521612480010004806a20344002c82464060900c01041c41e041d110040050301e65104000c200038284200310811280d0001c000b0000c0103c400d082041c0560000e108010007c0c0c0205041c0210308001c00480c42c407500c406400c07840e5805051204414040310005101001c000c011a41081e80e108a0003841410380380d4103104140c8010348203194004042d54070071040c1d440c0402610280082c099254083d682c41c102d1500c000040181011100d140000140018056640100c400d140386100c001c0c821801c00c0c1c00443d5510700c49100c0500310190f60031513001c8140c400c3c04120300401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 815874838 1250 815873588 815873621
    0x11041203210204242f0c010801030308070f0201110c070509130803042d0b060a0915170a020312040611070302010c060902032b110d0905060c03040b1201030224090f04 73
    0x403800342e110604100304218880584500d00e0039003030a6102e2391a180c181c07070317040eaa030580545500c10705640d400c003244851030a41d5221008180c4141a44c005841e0003242c40c80101003407494402449001c1002901c80c00f540d0019a04000201e45d241040302c3d0480c0e4086411840036007900405e144400c202e03980380d03c0c010340942c080e40510266031050703400340400311100000f003981c40300e108040701c01000940f1803001100310204484c1c482c82c087c204040c00c155054400500c010b900007401c0400c05600c1443c25100482c050100325802440e21007062200d43c0140700250454002a05040346030344010001707600c50501c1011903c050060014003c0f42c000500400041e1142003002c10702e165198000048030402c000f007500c8000034412003401c420b41c071144440e0b0300317200a0220f131b0390160101d074005200400c400907070080403000529030100120f2912100d541140304110400c20100c600740310b90703013080507100005011607040b00d000703040c11a000480503880c4070108014180502001c071015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 815876088 1250 815874838 815874887
    0x8030c0906040e01061b0201020c010c021f111e150406090b09030d0e0c0d11011e1d03060709090f090b01031b15020706031104120321020424 62
    0x8a4112010138141e440310385420140e841d0354000b454040924010181c0103030300000d00c0c008154080c8900700c000342d0014004003000050041105c10b1015882021000529004030700800d0107414000d812055800c103000c03003528440c0c108090f940301d00d8a013510505d049204003090401030203034042c5160a134010740082441c90404421074803900003210802c5164105059041301c10b20104003d0303540503005003259481c0c4500c4c0c43e1a107001c1c1060010368180950841c190f0000d0041030585007410000359204500d1104642c1801116135800d01d180703002c2ea00a07402d005020390882111002e407038019000041001c406454a0058004c00c031010b0202e001145c004014452040c01c4000f030100440149820307903503140300c20a944801c0d0032880c001a00315190030b2060f2482794001d0060131005840240c1816140c800c4407070110452801240807960149400b40e06116207001c44170b100c1300a20b0114101840c0ca070050000303d442d04c414200f0221114a80000d441c040c040c010010091032030504041d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 815877338 1250 815876088 815876099
    0x3080313052e090512030c070c12020f0603040b070809030d06090617060c1605010f061806060201060501023004030b0415021e0a030e0610060e120a08030c090604 71
    0x200c2c02400307100411030040401090001d0843d004080a00342c2c0000100203202c44489100c0d0190409400041803040400c034410215601104c281c02130281d06240d0022003000d8810060000556681940240b605004000102e40001d100e164800b1042c2481ea40c66a510311b0440d065100c0d110703100800310310b03011001c01e01500d00c4d13001e40252408030024070401e0380d50b1410f403a503440382240c0c01401801308006650b680c0765001075111145204100101740621640319100584100741c1040c0254a8050b144d80100d4200d40a048001c00e4035000800020742881e0000391604a00b0481c90324000d042c0c2a001210309000759070302c00340b0545a0040d41c50b2030b16490032001c5440c0980381951845c90894040061b40528821a10080829100703c01248406000403c550304a2074100090568400c01500351641c00d00c58144031b04881000351041c80d047c01c0c0040c2c03500c074501c1c2c44540101d100f040e04194500d4000b503d0400103811010315a100c2e6200070b080c841900c140042c0c160089004100000c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 815878588 1250 815877338 815877373
    0xa1b0c020d0803150a05040905031e0408030706020306040506100f0f2601031502160b0402031c0e0102010e120405060c10061805090604111c0206120105010807020f03040308031305 79
    0x80b602164405d80d403654460402c000d036003119002030000e4004114800605101000c015180720003c81450708142e1380302c00807400d41d007004c141039400039000003c00c481442d207481100da01c40401c85200c59450305608008218213407100c9850705008100681c1c1001501407400440b280e420703490441c8400008640307000f030142080c4022035100000350541d80004075603009554950400c0308103100980306035110343c2c034000300146c401d03a00340c050b18400342e000c0003400641150880003626040c0e0603140300400242150b40f03d14014403140c03c8181c03151f032803e0304030301190100c0f901110b40545821505c0540c505281001041e4a10a403410b20000b49600d90900c82c5026640c841c1b1040080382d8a4020154a9a0044800401c080c070b414540316814a0081520407000348401040070750f44103540e0103c2c08031390140b20401010003020700100b2072981d100d20030943c80307a12440035052400c42c1d0000b003966802280401001c2d00c001000141c20400824440381c056030b04001111b444042032000c005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 815879838 1250 815878588 815878621
    0x230a021207051e2802121006050f0604060e210d0207080114090307021e28060c05030a05091519020115060906081e090f060a1b0c020d0803 61
    0xa001d0384032400b05140300c0c8012a0001c8042a1036140300c000c00480160b80340c100c036030610101e906c406400712004003c02d00f0801c811030510813040c005159800e02e81004400c3c4056048544640030030003060006e20b83c05101a408040107030781903101000041001414115210700c200103900c82d000d6510115136001030303800e0071030b02c055000708840841c5001c869a082c030704482c3e05540f03500c100031440050405102280d046041c4503d03500c9080005000942914216912107080c00c075215000441c50104418000007011030782849070000310181e465a80740e01070555144140030300401c4400d002c1e2078040c90303072105c82804400c4580d00c0009440840d61800356448040043d86032a0410310160000303c0900103440c003d45800c0585031400780100d0721a100101707202941907031031803841244904540078070b00a01441d006840c00c00c83c85801c240ca41003005100c60b180134141901681e104c840301c00204a1160325103000e240d210042e0001c5145000030241c0140381440000c100714010400b00c6499 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 815881088 1250 815879838 815879863
    0x516060903020a2d02010e0a0e0901060807170618070306050a1b0c020906101b061d06010b030c25060203061804080301151806030504020f01230a02120705 68
    0x706500341c1c4441c90202445004001001c0b024591301000c000342d0300600205560042c000c0c0394038034141d10703180501a80031080d90342880c140c0d183e81c02880400c02c1440040d001e8144020b140038011400c0c5005039450700041c2c1039464503040075426208448051080c00d014503003254003030080c2c0c1403081c0400000d040101c4141d04000d200e10300c0c40c034001e108440c02201250001d28080e010b8035451300b0071015a41c1500c105042c400d07485070312908180860912030b091402060700007010b240e07501c003c9030014240c00d070000c801d4001c0c200501c0003048503c16290041c1034440081c2d140d00320300400700c0007000501400d00e10301514a0b511010445203400840c4100c60170f440311800e009202c008414102d4007603400030440402800140500c000c119000715083c03126141c80d0000f6039071400740d0710105880d500071030300190f00c40040105508000c1246071109100f0b190a81441c00d00c1c44500c2144a07207801040038582d00005c10342d1800f4420094a25544c0c070031101d041e0383d50342071b1821139514510510b56 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 815882338 1250 815881088 815881103
    0x110429041e0e060f0603060d020306010308031608010b07060207020a050d0609200913051e010207050111090f0411040b1209070e1311060723011a010f0516060903020a 73
    0x85001140302010b54041c81c2e000e403d00034000c03032250400050740c04c0108041e411500041c101400f50b6802c1140b203008500980e040303075030790a24140804c42034070f0f01058601031085d60001005480c060700d003100e1115030003000040e1507000c680b0014441054a500c244d0b40303d04450000d41c00d1100c01c0c2d0001060768881c82640c1a200e5081084141e103a210007600d65000740201c001441d405010b180307c50100d40700d4401ea0b6041e940b44100c04003c0702010308000410703075007c1144d80802109104a2411070001203c180c1441c000ba0700151a20b0f0b80701501c00d020f2501e070702e4205200b040070000d54015000800c00e1030b864010004007421003020031503c041301403048410002d181e001000c0c009000b6110403a8248146425455030320358800086c0b032480e08404200f00c1c6074042444440562621000d4800b03000f00e24001581c0982034072400040c0003000d0604200071625681c00c0261311918200e981041911402100e03e18882c1c0280740703201511f41810302e14001c08140d400310b06004820b200d100c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 815883588 1250 815882338 815882399
    0x13090c11100507050a031109040204260c1003020a02070e0c0a1e050f0a1119050c0108070801090c02010905030d092904060207050a05070807081011042904 68
    0x45807055440541c1d0020104904200c050f00503880b81d04822484030640d1440d51400702c0c0c07100801d00726400ba6001e55000100344030aa40301008590480d00d034112004000c0036403801110004d40500c1c8440061811306078000361140c0140c0c024000400100108101054540380c080c103e040c0903800040e0700b4000446494480d20302040f048496021030101c0e0b40d43c142000100035500b0100e46c040058001807141c1d11001e003490301d5040140103c005940c4040290802680ca0301604d40140070400505001843e0108450668085031880c1182c2807411b0209507500580310590040542e0380c0e0242940c040040c0a6009210303a030405100c0c9841030b10b02150038403040000704608080baa484801c0c60007541e0100700403608980191001074094412340300e1038110742d44c5540c03901e252503001c501290031440e01044011000d215150380001d45c4501446465803112404095118500404d0030591030040900003003000d42c10700b18203c1c0500840207a8450312a900d40d450f00c0c100501c1d2101a800444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 815884838 1250 815883588 815883613
    0xc0d020102041a13090c0512060d0302060406051b04030501050f090615010302030703181b1d060907050417070807060f020a2a0b030604052a13090c11 66
    0x208580842d1440c0340c501420194080e4075801e15482200c40f0b01c0d40e030813843c0010500c100a84260f0009a0b099103c141e80d640c1e007038140d020240d800402151080c182210500d011940210f80160b00070b5104400080560342c40225000710300071620140003100c40820003100b0000f055004034003075582c40c1554001a511102801d6859004580a0321240c00b1800f0b1030035254043c1d000b41d0342141d80360401180700100321050365000c04003400309413502031814482041c10307015100c850018140000c0c58100d5130110140c200c5a1725005489240a0300303000300010440d61207131041c1c4001e04801c600103241c3d8103605910590300d07591402400700718043c0c10800500c86010703051181d4110595005445520500e07260000c0d10001020310341050800f031640280c81c071700c40840020141214899032030b20390a0210900085a034024440d440308400c2c0080d003100f00000314194140c0310000709945560781721300844021214210781c4034541c0309040079149114a9003141e054004042c0307020031100d2221408 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 815886088 1250 815884838 815884841
    0xc0a08071b050303040e04050309130b090105091003020d0c0e0f0702070e10060f030e010f090506011e12111f02190308070c080c070308120a0207030f200109080c0d0201 74
    0x140b1445625600422040284005400700907502901900035a41008290000300e00800031001aaa00460303991014180d1442c045402034090002550582c03841c1c540955810712a219030300020f44944080e440c0e042c104842171503a00090010004c0325901c03820000c010344000c0b203094610300b016014481000c81c019003040c900c01e00c5090350007041c03e00207141010542e284100212644205515022542480700090103010300c81800408001030000c03940c02c0140c00d12074180c002c1012076007600100100449885203c10580703401c00441d90b80c1107280d2a21407800004e003240705812a2042003107011942c0040010902001580c00f41d410070360741075035100d032550460040100840e0401c8042143c41d4490308040958612844505141048001c0070f00d14000207036008646c11600052110b01c0c2d00450746150750051080340c01075003003245590b4050f0803221340c0d4401c6001c1252203030b85451004180c4000140c80c04803c8000c00481c60a03003010701d02907001e001c4c44982031150000b08102503105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 815887338 1250 815886088 815886143
    0x2090a0c080406051e0106110712020f01050a0221030601031103060102060703051902070c0504110a0207050d03090b1605061f0e04050a14031903020c0c04110c0a0807 73
    0x11540e640c80650350380da4607040140300140c641c6048202c066001c06904005c9410315010742460341302c414030b07080d0810b50303240b410b1600e0f003111003801110034590006840ea1401a2000308007402d007141c0326000c0342012840c0c5501c0d603050583c82412040502e5200075400f0086003e180c00307a0301400300c2e1784150040f01881c402903c010340183c2c0800b0000302402c0c803d60010360012024213024242106140302801640c100c0842034640d20003002d0200910325146c0f040703110704216400300c14185807011078082d464940078854180600300a406001c03c140c840d038441c00240414100040c1c40340d4552211100a03160904200c03050712500d00410790100c10805035144503403005400e52202402d000e16400420b0740070304202c07010b1041481f107000050305900501d01000110f00190384940c0c95848190414410140d08800c1c10b1042042c020102001300341100e8581d000d840100d000d03000361000141c24070401180401c94000c0c400d1b0401080070381c1c0018101c00380610b0891010f44002e44400c1c101ea81e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 815888588 1250 815887338 815887361
    0x50309030a0f0b0c1809090c0301090b01150f02030a05251b05010e030703060b18090a0312050114010c050c060a020c1f091a040302090709080f070f1413061202090a 72
    0x3069170344c0b000c1601d07086240c01c5d4810007404c107130303401c0301d011001090a5500b2035504484030b84100d00140202228001110350b4140145800405540d0709800691a440341e440c0c1c2801b0031800007075202658030070700300c0319100b0501c22020b000502128200503820500c40c2c1c2d01a00c84152081000850707622950340d41c00907120041c0541181440c5d0307918140140b0300c200010381c00c142c40b810103c2c2949221400741d881980d02c400034060b8102940790007405450800207104c841490301d0014841d4007501c02104240e07a100b0300381103808002c281000342c5886c0c00c41e901e01c0d5005000041080368907501050002c002101910780480130318a0b6074030082e41406040404000400c408410000f5250345044101e1801c00440c09500d07107520781d00030030034018007110040086194203108200c0703404200702e420310358120540034101440c01c0c0f4040715400360b018854925071411203880003d5a0b5169001e4454901108100704042c1e60b442c807200703079010b00e108400d9100e650070400080404032680030702100e030340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 815889838 1250 815888588 815888617
    0x603160e0d0b09150c1b1609020a1202030c0304030f0e09280908030606090a1206090b0604020a021c0207180b0411040f0b0f0f0307020a02030f1513050309030a0f0b0c 73
    0x8a40c1d1005620f18801010524000d00c5034400650b1003a040c40b1f00000540920381e40135a03500c003924400780400d5a40250442c000e40f0403c10051410611015650031540c5807034480f00e81104d80c542101c1654045280c2c1e40d2010342a0f00b031001c092031021040101c1f00d40c40080010110792011044102c5030b00c41c2d03024152007010000a07401c3d1800c1c0c00180845100103040d03440395611407451604d103000302c0704c2c112074075a40c3e020f068083c09400c901c4070358402c81c200d030294038000c10158020f45076100c0c54443c80c0416075007541040d8507070080c0070120141a00106001060601c00804800740c2800b00503180128074041d0740c065503602c498100c0f41920030700040e5017080c62505032010466844034407034032498a402e01100c092800358400440c040d03407940d401010007514900400d800e1585001c880c43d26a4401210b0703030300001140134283d030311001008510342c10710410b040003810744c860b03c8100c551600032403041e1400c0201d0f0b22030300c0c0e40c0c1c14004d1548102076550f0100c0d030700071482800c0303140e555803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 815891088 1250 815889838 815889847
    0x5070507200a120501090c0b0c03070609060b0d1b0902070b07080702010908070b0711030405010c060b040906090b10080c01090902070309150c050c0405060603160e0d0b09150c 77
    0x100800c100500a50002e8880a501c0341d0701d055040c000c0e0140c00d41150340d65121607040d800e02c040e00a41c01c3c058002c0400503450a10140d43d2a43c0e41d11540310024115511102e02d8402d104244d8842200280c0141c00740c140840c061600e000821076001502e6100c40030b110b030102e10100c1c41d20035158a160302c1703008038031543c4400720166800c1c01c000f4625400c56488410010000ea652000303454141c0c462010b5081d6420183c00280440c0701d500440d100e6540705200030000f6aa020708400382440c2c201d00001100301401b404280600b8010f80017601c41410a81003d08001104030b40c3c0e8132540001042500c1c1582721002d46840e1016800520300148112100b480704101366401090300034802c0c100643c1081d59500d00740103c40c8200141800f1841d000d01c0c2c0d000b0703c84280603207912640704072000c03c031a03c0e01d00c0c0002c41c2408040c2c280c2c03610882c41130a0181e502d0148806130001000104142000603045c038154040c0041214090480c1c040d692641c0204d504201d40c43c0d0180140c00a40c6013403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 815892338 1250 815891088 815891123
    0xf05091f2f0c0d050d0b010c0503030705130503070803070b0702071a0d200c0d2c0a090207050604140d122c07080d08010609031e0203061905070507 65
    0x41004500c1c500034440c1003007081c51456102049055580b60351074a8140e140d416880c455022030380f20300c5002d81031010440078540020340c0401240c2c0c0c84110b5040003500c1e02074002c55800585450380191b90944039103000801c2104000026050f02403145900304204d076078200040762102c095101d140d04158004103011002e042c441c1c0a003054100c403c0001615401d9021542418100804044002400000cbc3c619540078280400d82c901e20ba64200404500b8401014680c00c1c2e0098000723003111803236540703503111a42e11604800001c0821a00541d00c0314468105243c480c402600d0403261806800500c2c4270841012444441020300740d01c03050b030045c0801c00b4040180c46c2010103c0d12907100441081d01020804d10110b64051045c1c004000007400c0414407460824044200303000d00c1180b800412100d64401e44280507240e0001180c428900d210b0780e51203040d01071038802035160150f501008405455108485c2c0c01c00035282040c002d60b04c841d0800e542c1c3e4811205c026000c4204659070959 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 815893588 1250 815892338 815892401
    0x12280b0402130905010903180906080312040f141b10081906260d0e0904030c050106031e0b06010e131505120d0807020313060e03010f05091f 62
    0x10b2a544401d01042200b001c1d41d03124215040120124080380c00404940c100075031566845025000400c01040200e040000c0240d0300d028114560012045150014080101001c070503001e841d800124581300c043d9403c0140d4070f50400c1c4090282c0c0b100d82d01c507181410300c0c1c02900700030070300410b8407041145d86a0070a0024201001e14034601040c2c0c941ea000030b0800b00e10074080421000e0302040514510403482c0042c1094540031541d42044a01d443d00401562440741c0b5981290340f505001d41c0704aa54545035015281c41d0348003405003514661602d0b02d62003407131a4501b0b5184200707400c00b807961b13501e80192650f81141400541012075900000e00074201c0e548514101a20443d000955564400004112402102207080d60307410820740f002e40d040e002014240c00003024006942403400541c001072440c2d5462049004000340401c01c80c4154801b036100481c0840b12100620052070420a840d07500c0c0410008901d2259100580c3c411001991080007881c40c1005030000d034124a0f150b1144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 815894838 1250 815893588 815893609
    0x60c03040e150f1f09150504081509280804060f110a050c1309120509180106082e27051b030c120405160509040c180b12280b0402 57
    0x10170f000c11400701040d080c03541d01c02d01065034816900c003661141000400d504010504132404c60180c50234080c40103401c030200301000d40950269400400c150740c0c200001c1f41241c034100162074481c0000b0701248280d4000b42c800f60b5a0003e842d03047c062481007091a0783d40407410302c0a0301e00d410851a0f8015031806103c41010300403040c1000c51102c4481d100d816075046045048804500c00060b40851414005c01d15040c19555440c0b5030307440d40c9021000b0b03280000c0104444410301202c044840074500050008500031800440000100d40319126074040400c87c181c00c0d100c0d513200482c200c03402400d6000c0d11703220fa00c0020185162941803e590012508042d0005807101d00a024000310442042c2e14907200d18041c00081c04401d6400d5110822402940c0081d4000c0d4550800c10000c500c0b4026080121420300250111140a000c44a00140320600302250301000542d550040b5100005880301803080300044143c604003078815255452080b00340040c2000d84480006015103491b14084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 815896088 1250 815894838 815894899
    0x6120d050309031b03070606080a0b0c0d1b08060102060a0c0c080c0a050d121a10081b070302060f0705070213020a170c03090c1504050f060c03040e150f 67
    0x100e06001151803211201d0600404544c2140d10109000007405440d002c0e1070000d2400c1c1c000f92040c0400e640701ca9140030802030000003a0400014006800300c0701342d21003002c2645e8160240d45481000800030242071040e558140140314030804910041214030030640501c4807600e440c0051856562500e0150704621500700c0a4059004041d0114205001c0280304050656940034904000e440d200100c690304504480d10101500e103000c8c00d6201c1c1035000c04030348103504051129684910800ea520102020819004480407900c0010580c002820074000d101c0f24808a559540d010002c903414000c2035000780d8046050740446403402d9030381e03000340020b800c1460f10343d40c2000c0c440e1111981c0c000660300003c507108000700700600c8050900c9000c0b800c4a00b15100000407540841c0c00085004030300911f803060000d1103411400342e0741c03482141c0c0c00c1300501c07040d02d44070b6607038000c10662100121102d40d01d9208203401e14500e0301e885400301030440001000d0a1641c62091002804c02101c030800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 815897338 1250 815896088 815896093
    0x306050a1703070605010b0a1101060f0e180f010905070806040b010b0d0608030f070b09010b090a0b060c0a03090807080609060f0a0f0f0204090c08010b0d0c1701080105070806120d050309 82
    0x1010f000c50f14501509004e40b001c440c900303540303009003e4010840742e0400301d1030070141d26112003402200c807505111000c940c01124072000b19101e16002400070904c2003900c507101c4c859179440c9804040103400641c496030180c019903038003980c1c0c0d580c0151200310407200148004039000060020420404c040c2858010740003000881d56140c0c05805c0c0380d644080759240d016100032640c2d030100728403003a9a0368845a5480240f16800004012419102e80070340500c000b543c643c9102001622445e0903030b0101c0310f050046a48800300c605000d011088a03004806a074090140b011607001d20005156024001800003891a0b690f200b0f0701502d60100500200241e03501d6808028002555004850044a0100005a54a01c0c0c195070714102c4680c42e1010041c001010010800d01070000140c5d0841d0b001c2c1e01020410161600044070315810950610000310041e40020440910541c40340d0b00c1003040e600c0b0251580c580b0010086240d070407060424180d40070314003070201c843c0b040002e550820944000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 815898588 1250 815897338 815897347
    0x6030412110601240f091413021b0708030703020a020d0606030510050906070e010c0b040c030c080c0a051206070309031b150609092a0504020c030909070306050a1703 73
    0x48481c1440702c20f07442102941001d1a1300386031255801421400e444c81c80c00c140c00e4055804601404059080c8540c92908803800c404040d5900d41c81100c004940d110401195616400d100b043e6561501107444603803407042e048013040c503100002c200d0311100e070150000c110581a0313900704401108200421110385031604000800103604000403184d4140c0588040740f13516220320064540100206400e0400040d0f000b00625640c0084050320b4031900070001d10301c42c0d51141020480618503510007448a40054000601d0000218004034980b031704030391100d0115900c008005050704d884140c880142c02410100e078802d030103580581d111500c80e040c19154a041c0035141d65040034511420768140721a000000c0011045200c0c0001600042c42c4c1013006a40c503807191000c841c00d0b0340341c203210105064608105044046910402004010f100355a42e042c0c2c1c005030b03a242d4000c1e161650040380004041070441d4001c0c02844180d400c00b038904850310389403520741c06c41c4c42218601000140801c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 815899838 1250 815898588 815898617
    0x603031c020409060306020a181d0a0b0603070918050402060f0903100e012a05073009030614160c061107060626150a0e1023040206030412 61
    0x504c0004600541005071611144840030b01b00c00b030f2080c0c22541e842404942885011a40e10445115404500e541c0307886603284180a0000c0c0038486000785d0021001c01004041750348424010195080e005902c2051218060400c0660f031064a009521080038480e140c5048032007806041c81c06801002c607a02d400e4002c00070402c80380802002200742e5101c0032040b4107072002035540040e18507518180e05030400e05a6000300f081c080c01000928518100c40c690310002441c444d0003506001283e4061104154042c000d0440700b0580f004981080c200302600301c0c0305074086011441020071001d400c09080c050070040b0f07088003400b007003119401d9407200c0100c44000d00c0c001500e541d500c80d00d00004d4207400c04c04c42500d40600c2003001e49d05010340c9551007100c0040820342c10040d40e07a109400c1ca50780c8402c03a400300038000b0707400c0c030f211544681e00c540c1c1e00c80d80d96a0019001840c44807000c2d8445c0307030603001c07140c8080c034101c0380030313400c42802c0010800040d42003814045140e440d01d0b01c401104001d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 815901088 1250 815899838 815899841
    0x40c24360e16020c061602150c0a110607050d110a0f0c0509091b01030b0d0212010b01230708130e0403030f11070b070e0310020a030603050c090603031c020409 70
    0x942022003101410810060b9255520b81c409001802d940000c001400d01d00c00080e9280c80742c4000340c19122085142081192074a554070520320780d1920b81c1e9512100601d00403a640e00000d541078902c07034408980e182140c1010030845203d01d0304000640945541c2e0034003610b07503013000804c010886c070070041500301149202e07a4403c0150300c00c0200000c464500002c10000c190054454a02d5801031400342c5003804136044209100da80030300f40424003002a80014010b00d054a0b00a5001420019036510040040d4040030101e0307800d0300d03120003082400e000e840a00c000100764410280301002140046002c1101034030f4681c041d480f48101098903240c03070b0111110140c0d021400729890b0b904641c840561340c020390781c0034182411058200492034951805200000d0a054288810f00030390642d151001d2280c1c8150314034000042d961614482d000500070708117031105a803035008401e80d000b80d529181808500440c0002c00550415a41100450b12903641d4031420111642c20000052102c03020b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 815902338 1250 815901088 815901197
    0x12090f1209180605030d03050112140109120c0210090b04030602160204110a0219080a1d0402210105040e030919080a032c060307110a0b040c24 63
    0x10b104046619854070091618000c8851030f51414103003044014064280c84813014107180350041e0354204560411100d0900409000f00041c28841d00000d908a2164002d100411070b00c4c030a4036043c90b010040e420890ba60f4507280106a83e6442c2040304001055280d0042c051b07202c14071501d5210100b065001608440030541d41500150012580c045995014485100d48641f103500d0f602000005650705c0c800382c0b08550804043c0540581d1462048505114060101d80e010344110364940c201d10b00c103a00440d582130000c044411460011886051501075064000c0500c0000c0d4208075806c420800380f4242030340d80040d43c0150f00c50001d0000e43c10443e66804501a443e411440c0410f9040010a69018403072a9032011410401c0850303900c40c0780850313a02040900d00524100c4205070302508041080700040c080094000c207020500113010614402c45031000061303440c0c41211501c0d0241906c043c40304a000c6203680704402044107050600001111b1251001c45404d00b00358880100c5084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 815903588 1250 815902338 815902379
    0x16031e05040b09010203040c0902030a0f0f27120f02030d0507080f013f0c0b03151f081e15011407050c0d05070b07080a12090f1209 58
    0x84a4003408207000203442c4240d00011071800130740c5980745c152120550929035204103201d10f0b80c0080091040c0d02c0580c4401c80400301c0d680b09000002e040380400000c0c3c00c071841e145d41d0314a1740030a44001c1102000c1000303021039101941d443e400c0c04401f000c2e0707022054015484c055000420103690f405c40c151045a205804075190340c925800c00041002440350140c0000b01c80c051034440018201d007407910144884514404010280301d505c481442c0120941c07000101403040076000421594581da02851180003050304900c01c20f02c02c2c0d010800210f0345a104407030104000c2c42c05002c014400d881480d8000c0340350250f4101810380000d41e2883c0e040c101d90120103010190b001403260340c0d00034402211913540400681c1442525222a9100c42c4003902c4a1f21541254440c501002000d0040340028841403003050349070115170a0003006980421905000034100ca003900f99904520b10840d4002030f0410035107504000c0d160344254506280400040071b000e4000390004040440e00d0070580500ca = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 815904838 1250 815903588 815903591
    0x100b0a06210b06190e090f190b0307090f050f06060304030f3c0201020c15040f02060a120509120304020111151501090806010b0a2303070e130e030316031e 68
    0x241c481c00080603032821014880c0300e80100018401080740e4260b805800c0300c215161112303606d4005c08000004c01c004010300340c05000356100003514881551001031a01147d4909124590b205101e03030350101c104841c020b52000050001c00d0101e40f2500c8040103400b61401d01c030911503c903042112034103400780515618032402c00301944440b00d120365064400381c0d881c0029410000100d0540c1d489407102020541d40c4e10070200010f0921241c40710f001c001c5070300074240513510101c0200003419020060540086242448081490182c0000781d41428405000c0a20700750303181c1703600450b00c00c2c0b2a0b601946091150b2200300f03413010310443c0c80c0c1c0c1c014001c441180b0780d500d20754400908402026441a002c039000360740108111642c080032034500f00410303d040b130083d2032040898403002043d02e10f03101d9841000700402c81c40c0d5030046420500e0110031200c100c1850040c42418060302e441948403a000d40003072002c14403600c0c144000d005414861704011070303c00344840200380c3d650622007100310707e00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 815906088 1250 815904838 815904877
    0x2010f300204080d0c02031e1906050708421806030c09090604020105130e0a05071101020c070b031509090604020906010c0b1b040512100b0a06210b06 66
    0x1400c1004104c1c400240c42c1041a00d10b10581c00080d00c4214107101030482e51802c540c83c1210243c24442000000c003a00d00300c4440ca4458204070b0b0080408a40303c0340071032101e40204034028107586000741e90100c070010b015400460f6010160035026681c1540902c60040704080801e5501e48140701c40008601180c0d1695140040c1014a80540f500344980200045418003111480c0801c866038099020300300141e55641c0c40201c080b0b012160392140a50000c60f2050041c07140c82e980059000c3c9040b51344019880310042544e030300300e10611601000540c271510081204085000155a02c481000d8040e2440319600021036150001240c000710250080020041146410800c07160468400c0c1b81002c0304404c0b5590380030030318402610b6100d1001070300a000034100311080489024010107420310044104540d9100d036900030020194002c0c6003071404240041c101640f0700822900a6540c02806904001d0a66450311181d0360a05419480300e4100d495529080e00400b04c2c02c240c608021810f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 815907338 1250 815906088 815906099
    0x9030c0f07150e010908101a2e1e0c0302070f0b09120c06040627180504022403190513020103090204110f0d0c090e06092a0d11030402010f300204 64
    0x400742403803e0b103205031707640c02d1285401ca80c4d082005040144400001408500ba01c6040e26a022085c1042b4406010180008401070b404104403038041d2281d0220313200e0030389414001c10107040600070201c1e800f00c140820b85041c60503a1103800e64140f440240d8020034141c0001c500c6551064229a002c01c02c0036603a03500001c5600c00e03000036285160050041c043c100f40d122002628142d0311107035015180d402140541d50340c41e40500c5035002586240316a8a551801d442154104441d01280b244c001100309030b04800d5409154484da040c4559404210600c3d801503005014440050340c00954070200703c0c3c0c0c002c00c1a0018505208001402621591850410415a071020440c1c81c20411644002c119051411480c0c0d41c2141c0c04903885840c036a45d203075008500c3c6441c41050400c5001c03807001c81407040302d0140100041c0d2403621040c490008000c05240035032000b03480c002d0024071004041d80300c4601c200b100c0640c100c1c83c1c0902c0c0d404800c10750451810070300c80e91040b003021680060104070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 815908588 1250 815907338 815907371
    0x131e0c05040609080f03091e03060f01060e0907081308070804080102070c0803040b0702060d0b101805030c06070303050403050d0903030b09330a08030309030c0f07150e01090810 78
    0x5011860007014117041d00c00e103003502c03402102d04040c0124191525070b2046c0c1c0030f8040d820308201029044541d00d00c2d08000d0f00002e00003e01c64000442d0702800c40007100d0a01071150b901c1080d00d0340340c26030240c03545011f0f8106009080d0050343e644800b4402e08001440341c1303000380020420100017503241c410341d084c0440c540909520490a0381e1040104014101501e0306489080d0340446105031034040306101c0d000641121010719501488401140111541001c0716080607500c2c041e400b082c00d6111402e0640d00d01f100b14101d42e12800c2400301c000028480e4020b02d600622034540103007014401c10820080e01d940d80070071000310340c0301e40341d0b4041820480b0303900e5031100c00c14000180c2e010f070100b017000c901402a130500307060440e074030003c844540720849080010310305a400c4036078070325104051035200d0b04030511241c010300481c0d8081c0c0c29450001032080503142c801b00c0e070039042c4003071000036203580030140a801d040c02441034001031060740c1403241c04445c141c10b18000ca02c40075041822503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 815909838 1250 815908588 815908607
    0x160e030f01091106040303021221090a03030612020a05060a0c0507030809030610150c03180e090111120705030406151512050c0418150b120f06131e0c050406 69
    0x2d0146130207000c1080420b0340003401010b07540d44110603503a200406400101507000c5c040101c2c5100e800324042c88411100012800001406a90b0410020b03031180b9810409151520019500009183c82407110f450300000400c0349142c2400c100c00c0c5540c143e80d030f0505000d095442661103110114016946050600a0503800b404400b891100c241c00c244600041184542c015000c00c00c0307495800b400c15010f100040d107008025031441e50340075601d4221210001c000c441d0b44045501740400340042030200030980d0403914048851207195a1070ba00f040700ca6400051040d19165150342042c640030720009a0345000e06000e03a60480c1c50094110040d201c00c89001c080c9071102d00c0c0500708174401d10f040e4166020b84228084689506200c4510b00000d40a003240520809101480001e0740602003c000e0001204100002e800c0d035036070092074200c1c030200325400341c1c0000b072a00f802070304002283c1c04515a10500d040700150f5091514507103040b6906c6120700c401084000405002c4140c0003110348 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 815911088 1250 815909838 815909873
    0x112031706011706030a08030112140c06030c0729091501150c06140c190504051c02010507050a0b01090e06190203071209030503012606160e030f0109 66
    0x800035400c0c000c1c0000c1c812200c5003d1405080203000204165640511200c2e03019600190b1064881d6184c03d10030079074010f0000200c91590310848400030408011607480e0071490010007140c1541d8400e10004050f80c030221048559030311985054130386031030403606042480c0c0c1041089035a440c120b111a858440d512401802c40d07040f1000400515900e0b80c1d100504000303502c0c0c0080146001c3c541040541401c00249401c1d04490b0704100d42507400c0d10290400035050f00d4443c491034414a400d030395501c210f005250b006035010703e070010f194003440111010240b06241462405246803515410091000b80864811101100420800469010b5006446142b4002d41a10300300405403000b40140d204641031426000300c0010315441c0201300804040e000d81c4000d0001c01e4181c94018469802401a0b41e031003042000c082c104030200c42215141c5806c10b50003000d0325154400c0190303846480c4c0785200c4c20042905041c0205032018030040c00411aa0800030900408a05c0c00c07401400c0c00b000380 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 815912338 1250 815911088 815911127
    0xe121c1b0b071d03010e120a030207050a050c0301060b0c070b07110303160204151202040f11030c0a0f0903120e0f0402040b180105090d0b061816120b060901080c12011203 75
    0x3003158128007c12201c805085514030b40e0396903034040500707030041d02071a07101514034040c0d00b1504d02400b50220390b20303a00c81d100310001c1242a403505540c45460140d81c00a5001c1d178084c05007031022001d0f500080078000e0103611109121030403800000d1440d480440071a12091041a484045060131b025043701c0065002048040340e0501804c200c0f61814204040c1c410358403071404810700c2285070f01401aa10074100690781c0c1e403030000f480081650008000380005035280c103100b5050352044200038142c940c0203031807056600403203c04445032001000d10503888100b400f46507030541e440e4030090005000201021340c980800b03d042100741540e04551a0611030208a155125034074040020388043d80402c20050075125032011070022460381c4180415031301214240800e20f4800007003c020680035980741010031082042210a540e1002c3e112030b00000140990503480d0701644225504c06149203486007012a2111500c10603102070748942c52400c0844210409d141d8000f8802014031040d490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 815913588 1250 815912338 815912351
    0xf1c0b0a061d01080c04030c032901030b010302040509150a0605040f02090f090a090605130b100501091701020d02070b04051e030307120213060e121c1b0b071d0301 72
    0x1841000e0142c01c1c070b25181084480304c005118001c220341a20041c42d000250300d0780079500c0e482c0600e400034000b245070010041c460302001541101480e135074140d84e40502a03541992030766092101500001d060b40003a805115501041120701e84e0349288509a1002c01107000c0785403d0601084408200d03256080600400040c0a42e40300c0c1e020981004009841d10b1005a070780b2085140148042c840040960b070406d8144520a0701c0901050300003806100398440d6030311084201001200c240c8601c502240c0d151008000800280602d40318098840001619200b044910041207078446c590444621912800707104c240403040000c041609a4019080558412404515502d020003400041004048440307a02101d50302c2d0180c0b0b0460054040e06440913485d400050100b141c00343c0d00c2030051300700441004400c0d00004030040b899a0581001c80706201840b402c8a900c0089003a0444003c40c11461000082c0c01c3d0202d144150025039601300d06e00501034140d903040c07042d10343c1c40e4400e078100351 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 815914838 1250 815913588 815913617
    0x30408030922050a20120a0507090f120308060303031311010306050415090c031e1104080303010e060405460c020615030a03080c0f1c0b0a06 62
    0xc072039011408444401101c100d01881489a01001800d600740b94140070520595000c25004640b21007118034520304400c8150600311101d0140c03c4062a8040c000f402050107031b045a0b02030398000300d941c038082600c25211001205010f4072640499401d50080c004030342417550241803190000011800b4501e0b50030280121042402c00000c040c081c06c40100328603040780e000368881c0700142005071040c0900c294841d0303000400b0800c0c0c0701e5841200d08040702888120310034800d0300000c44000c400107000091030604400201204032851184000420001c40d81c42d40400c0514003c240007421070400d86014014402610f00282c04038140852080080e4100c50500d8a880d000415800300458418401c2e00c040c81084c1406143c018000d24050b8000051640880c01a00c1110340950f24400c106021050543c7c0b5002510050700041c00100441c00440d6041c00600306001550081d07402c0a0240388100700d88404001001705850317a8080c40003c03030070610500402411642002600e910309503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 815916088 1250 815914838 815914843
    0x20d262206170c03070e04060602030c06101a03190e0f070b0f19020a080f0c010b1f1b0b0a09020907080412050a170906040c0f03020112090302010f0504030806040e030408 75
    0x20300243d40901c1c02000140109109400c542c481a000070700910109a0f070b9030b000794695010f00f4102029001d80f0700014488031407031003014200d0780e1190000c2d0016481108449040e0400703003590401907041040381c40e00c00120b0003074200042840d0042c01c0041010b102d024030b0314416a00c00c40e29140b007803042159051201d0b0a540c4021401da00403105800701c0310040f401d0004544c0010f1032200701003808400300c40b08a001e4894440c02600800240111030200f004e90303118640c800c0c640d0141d429075035030740e07510821829825685855810311070311015030b10450301060440300e40384215130b00e00c0c820007545803904034240c214030b840c2440d00d064201620340721481c0d00745201e8903040c4840041c1142c0b0403803085045604218886160f000a42462010b464840c0001c0d5016104461410320100309030300c6a04070b000c202c1340c0c140c5801e009003000415000280040e68016401c0d07541e5807401c903124403c0c50144520440c441e544405142c0b5140c010407084801c0b41c410329480c1d42c0240400d00000720b00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 815917338 1250 815916088 815916091
    0x5060f040216020a030b090d0309080901031512060203040215090a052b050606030609070602030711040f0507031e140117010e0d020703020f010c020d26220617 70
    0x2514050390b61510084104400900c2e06802908941c5118000050005003491a400784080c0401e6034400a82078400b1010360355042342c0070707200c3c110420120b030031507002c1c0e80000644140b00254941d0142d0b40c80211842c3c5813640002c4e201b16400008100462420140d1540404000400503050401860118502e1051802018040e00c130713030403034a180e84500c64401d1203582202c601590111141c1d00c1c00c9a115007003590603902900c071f102e000c24020321011802009850380360b8000c600349a1551101c00012905100d5190000e503208948030001d038090040c2e91081c045600c0104040c6450b4040200050441d420628110f02c0c01e9490080c85d1108200641100c6051740508000168054001e0060505c104291104c1c49000e0312510f00c42d4021801d0070440e4022901d400c001c920a000659806102420080d0f2240319061020001510144240074a05035241001510f9100100099140d030081114511250074501810b43e809400c10406014114901d407110032a28440000000e0b40ea0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 815918588 1250 815917338 815917369
    0x1c0305060a03031d1c05070305150c0d020d0902040e0d020c0f101112030711121c02030405100204060e0405010b09030a120302090405010b210601020d031d010504240506 74
    0x103540340c621100d030703500760381c00c031088210f017001c1d02e0445101c0c0340443c0d440b0b4051004454600484082107800d001c420180f501c00c01c031411546190100a5038400003d41c030103e02c0c01015603440b002400562610710600c80c035141101c00500100e05817010183c9011500c0106900c00c6200c000000e00c03580f90104488002125801e1001c882050b01d2040c1e4100480302701c01442100c03000c0104203046611220012a480046064070803040d1645525441407003101000d540900c401c00c0428008031a96005640c868007800599202c11081382415040e070f8401d40c000c000103130b11f8508030752241c585445054014290341843c64601803000303010a84440c0c0721400a000c0035448650041100c0c080d070104c03a940d101c0180200714940c2c480c40e0340d2009400504000e0100340b00e00d102d003500d101000d80882e0146a050b002800c06110f01c61048003d000d405a02031440c00c101c07280081e4100d0240119402a171140000e1690120f03551101c80710040010a00e4050500342414020030f0384070038401403032508 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 815919838 1250 815918588 815918627
    0xe0a050a1506050a0e150706020910051213030e0a030b100609080c090606070606080d1709070b0a091a0316091805060a121209050406080327031c0305060a0303 70
    0x50030340f0008405910413514070805000001c2c2141c100b000d189d0050004a004468044440c211514104e80e03501074602000c1d01d0595440124403a100c2c044284e02510b886450b00c07113045102500441c031540401d80c401c0356100a48014861700c1c00b45414444050421450103540c1e0619113881c90f42d03a2088410640d01800b031140224100d81c681e0412180f040780c01010501c0300c180c1d42c0c0c8100741c0e40c420384040640000c211241d030810840100002d64060303000000100f04180c10030800194650100d4505c200b88000c003080080c48000302804408514a00e6041179142d141c4040c0700034044807480a420704100c0c000800740110f10b102441860419100040041c00755240030104000182c0c030713000719400024100300d2404001a03c1200c50440c6056070301c4a404c1582c5400340000d461141c0034045480c0c200f80041c000002032002804007500c51400246003244503034010a04000e0207207009491540c00301103500b001e6425000350340d04103030700b80d64902c0954510b4400802c0804804070115210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 815921088 1250 815919838 815919857
    0x251d010b0c0c180601180e04121b050c10050301060504061107090f1a060408030703080423160b0f04180908040603062903070c05070e0a050a1506050a 66
    0x1d101009050b2203848060420701c82070020040641400c00100e80c1c460001c0c0264080319001300418a000b001c960380145140407036210f030750f280407001107080300030010460004c1c40c100707110305080134201c00305009001418842150200340100700700300142071024844200010884180d0013401c0710111180d07807820031602d4907584000c0e070515206911845c900c82c100015040036076003a510491024200080301c01c0003000f50014040701d4000c1e4403668407150018400800400c0c00784400d903a120b4422104c10311058420101485010004000c0701d50310740c041141030151103260308a820160050a0449081c42c0c0410316150445c0308a00034001d26a00b44000c00c40d8080540c0c0181407025071100b400d50703c403512224000c008280500c20b02e5800c0c8034400d10810b00c09100d101021507072210300d881500d076548200b020354420010113001c64481c03144030300004000c1e040b162020f02441d203411001c02c243c2000d40c21003040d2000c001c0407030421030501400700411900302c3d046400c900c8075400e1100d000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 815922338 1250 815921088 815921107
    0x30801050d0302070305070b0307021b10031a041103060315040b01061b0506070e0103060e0f0703090212030c16050f01090510030b0406090608070e0712050414251d010b 74
    0x405011742d0004009100d0001d022814148140207036110b02c0760b82d422154400588a406026004505012034008020703880950295205e0b401c401075010180d08c54455030300b41403020800316418400285a00034011060154500e402e00c80591410044c201c04441c1d801c00d0340f109401120103107d0042840407210076407040380d90f0082180c12280d00035059402a107444500600400000c40002e40002d14181011401108400116000d81c24103400782c0c0003966075a00a9005002c481c5069a02c80d140c1840a0740c1480100010f01c06001100f01418100c82010100080d1400320b070045c0c1c2c407070345605080074481d0740d2010021040701ca0807110901d03012603401c01500104405551b4940060078070f04041021480c2d600319008460b90601250030341d942e03030015148030080959039900040c0011100095030703640e0381c06c415000f0780689580c03491000c90a81c11850f00410006000d0500c0309126540b82c501d0702e070748039003006004052643e0380c50496540410880300c014090700c1150140414004034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815923588 1250 815922338 815922343
    0x110601060f03140709030b0a02040305100b011709100f14270f06040b0702060f010308130b03011e060f0e061305030a031e0906050901050309280b13030801050d0302 72
    0x110020102800d07081030400500c010a05ea080b07000a95005c1c0f002c5c00484e014000d140300311402c0703070380000107003c44104034001c2c0005070484a5045040004500d410307490940d03041010307030180d07100b000184202c41c1381c80c0d40c90342501c0e4585032811600c0e00d0240d40c01000510500001c2d031201d00303941e01d006410101e104078481c0a421a401d4291403060490351183e280c000148075000300d01500c8403407580e60390103d0072603442c24211164030309400300313800410009018134054004000d1007102148695110081c3c000d241e08264042c2130380340384401900741810b1281380108060916803a10160004900d10054071050415040902410002407034080012107499190080c6c44028250356a5114500b001007071006810840302d03940922234004c1d5001130240c03080200311121900d41d58200910240156050b03007004150741030724000c203080c400c91200c84041800b03c0030000a02c07074011044d1803c066025000050250715011080000400440e401c00c80707150444204554803003002500c1c0c90101e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 815924838 1250 815923588 815923601
    0x1104051803030c0918150d080d020d020702011101151406090406060203071406040b0c0a02160602100c082a0706020a050301091b0c060f110403080c0d110601060f03 72
    0x91503000c00b10610401400b0080106040c94040341d01038250002c2d241c1c4400c4401080e42d550310614540d0441658500f882841c92442c02e001d110400d08060454102070182d9003c10013240d091603000911500310f6070032041c038041290105008010000341350480c1c5003411164081c0c1c00308020301031102c3d41c40359a0301d03044400c0c0c0c00010b0001c0c4584e6079105c0010390313203800c21030301200c4141540300075280303040bc0002c289200c0d075082040140c041d110304030f1140c0c2c04e5000c107401c40b0460144403c0f4182148000700300700018969a8000e03d004200b0140420490311b858803154104251030003413011030011403c0400101c03e81600020444420595000c207504c5103800017854140040341100c01350380c218014504a560441091018981e008000c000b507605414080c030209508400540200f54581d20992003050b210100045d410f0b20407a941016801903403045400c03c400180101220314184000d00c1004014203280003032144140300c0a488a40500684d01006407807001c550200303101c0e0308644c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 815926088 1250 815924838 815924881
    0x1c170c0c010905030418110c0d030b060403050f10110a08010317190903050c01030e0303040b270106090c02032704141e061005121510050307030e0109110405 69
    0x36a56030769200c1c0f44006d11201c500d4842506450a4090368a085000045030507024516002e440750381580a0164000c0c1400c2279550f4021609020101c0001d60130054078a40c20b0800d0001c11207103280004810503186142c5c0381e0b0711100d20034400c0400207904100c0d5a810b4075408800c0c9a80c201160982550900071000351052140380c0c031850040a94001101c08140c034014403e0f9940100c4410064040c2c981c1c040fa59030340c542c010000900441d4941c0a642c0d04090700700480001d07103d070007280c00c002141c4004544030a941d0742c1ca0400035002c144c820b908541286001850400300700360148220740102d0b1072002981500410305194603070703d6502c0314100c1e004114000c0214200030584000e200d0b00248803040388d00300724003c15158a4942c082015941150340d589203800005200004076540c090403000d56840811000d40c000e54602081c034403c00d2103030303403042c0d124903141a00a0940c0c0c8444030018003a4900710001d0003141008244004c40ea00c00d0710301003216211800c1c83c42c1d1512000740c0c138 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 815927338 1250 815926088 815926093
    0x1b03080a0912350705090d02030d180f06020c1509090a02041e0f0b090d0b13020307061b083006040f060b0306090c0f0c1c170c0c010905 60
    0x40d00c0c1542c10060304221403c100c851400b0f9400c400d541007801090781c12281c0141914140020720041c0f080c401050700a02c0078020030b00e20140e82d40405d03d40041c203c50600460f400d6004118610000030682c0c009100b0a01d41202c40c514102001c4e440b0712866914601506410307140030840d2a0120840303281c0600644900034500d004c0345c0080081d0020b0041c80c0c04052500420314034014165001800d03504000c002c180018608890305d11306c2c1c3e00c00450250045012440040811440546240b03d0704001c2c001410f64001c900c1018208906504a00244100e01c5091905d0704e011400d01f02031250b111103116541d00c4c031510140034072000341225022210501058804800910420300d0213214281c500380300c401c60311008001515024022148070303070001d0002400e60728044250940081d0958082ea03d0203100781c80d202456030001c4280056a80140c0b16248000406100610f060301d0519050507d848104001540404042c4c082140c584011941900d03ca00a601082e8001d0b4050304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 815928588 1250 815927338 815927363
    0xb1305090721020a0b1810030b130615080405122b061403011118010302041e051c050d030905031603030e01050604020c0312041a010306090506071b03080a09 69
    0x9032981c07010710750b620490058a890400056150002055400b2000c0b0003102c28102c0380c1e60824000d08060000070b0341c00300740d12398911201c540c4465004006c000a03032100810014149802c00d80026620252501000200030410000c1000420b450b406000c00021b000d40c0c0e43d148880c509140764080070802d8004c81311045210440c0a190b21060032200020241740c3c1f0007400344201400c840080c008080242420042c045500041e403004482d441c2c2c05041c010301341070b15500f0320810341102c003c0c0505410b402d00028440c51401c00d591440100e01106880149079041e541c49807540405164001415102d000c07080070850180140c40180b41c000307010200c26040d07400d004019103100d60003c6501d51800d000310307070340742458001c884184003807400a40c0340505414220900d020010b00c140c1d14401c1d0300c54102180c511800e0705500860040c0300100d000d00050400b2400c08a02501c1e40c803d0108501241c05009001180d9036050f5806007018544c540d158101c2a01800035544014160949401e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 815929838 1250 815928588 815928629
    0x5030405030d0e15091c11071a071403090d080703110105070c0c081501060f02030d02190216050f0d140f010e060a060e0f0916060815040b13050907 65
    0x1340040c80d980c000e00c2c0320030190f00c03036050031503c50952010464210184640c0d004206d4007440100442000a100b2a1822907680c044c0e10340c40f14031301000300c403100000550842400071032091342c400c006807640914a0944d40d00b00040c9100888540101201e0001c103843c41410301500800b040e00380218003e00c002d10707000a00421003489030100f02d65006250340702003054a07000a04208000942e5003171466030f400c140c002d0310f4001041490004503c4200002200303200240040c06024a00841c4003405400011000c1c1c1440b40c4c145a84881d080d44180c01c019995842d5441c002c40c00341959400303003644039814034043d802d820506480c0c0b580300f000c0c804000408158001d0540301c0a120a0324100e88442000005807130301c6104840821702500b010601107000c000007590000c0b40c40c0c0481c0c0c1410780c00101422514401c1c1d010801288041d03042000718400d00c003804a190504075010448582c2d4000025045a14030b45629100750f601c80000704031000811828000d0851400d8005d084410304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 815931088 1250 815929838 815929843
    0xc0f0d0b18010c020a02030d1b08070c0f0501080601090308030a0f051302030c0603040c05100504030506070215130b0408070606120b06030c01080411240f03060a050d1205030405030d0e 81
    0xe003620401036180c05411429603201140c00b41c0305d40d500401904d40c0f40b24012088842e11a0451152442e1040400030000134945038000c101151060311150350944c40c01c183d4100501481d48281d040c007101008125081ea4030962030b1003070383d510039003e075229180d40100c080108068944400428a46414040042a02041c86409034800c0b001c0f6200c0003071070790a010450000b9240144600308029050101d45011000340812031007501d072407410266a40c45052a2540682d064009030700f0111154400c4030310010803a03844178a0840c8031407070ba00c0c1582c401d40f050600800190801c84041000010410986c020030024040104c0d0507448000ea400d0200c3d14a0090358a6442441001d070054425406109004e10071600806000f078003d038802c0c1881041d9074036004110002180300759420850700d11001411440303c111411948a1030204140101c210319900301621030050f144084d400124124610515180503203805c6880340c07524a880d1303143d070107008400f080302c0e42400240d200da242c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 815932338 1250 815931088 815931121
    0xd121407030c11040c08160c02090f06010806151c15180506010903231216110d0c120804080703030302121f090b030a06060602071d090c0f0d0b 63
    0x1009a5412621020704101c100c5000400c0303800455086c00000b2142c000141801c9411905820a6203603000103a000503c0800304444a0300e9000881c1c0601c0040d5a0290780d0a600000603900c6480b80d21028001552500a0001c1940d402c4041d2815501c0c41711150810340c80440148a040c3c00d5030303150b12080c11069541035144600c245483c0c00202550310500280302200e4001101c0b00b071200303c0030400604180d00b0fa1280c0914850300c60002412080310b0b004042066642110703841c0301c503c510308801003603020028144105d000c83c4155000c5902d0441007003c03604e8908208103d40745619010364240200c0d40030840d58090450000240b40d00b54000341099450f221950368a581c40605400d10096504181240e03144807030b000340316908607584454000c08004040301c2c2d414005a880c8400d99816420080068114050410006901ea030701c26040d100c1480201c4540c1c500aa1415130b954000000c0520a0b0341c407043d03901d800d45898031440a07440d048000400d0501e01a03100c9440c0085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 815933588 1250 815932338 815932343
    0x60a0e030d081e06011e0c0c0b0309011103060603070804020a0b0c0106060801050402073201110a030b2704030909020a2307022d060301180c030b0d121407030c 70
    0xc1c484540c121206914462600c1064140c43e0030803403040405859a04806c100406020302483e0102140403d00103510000107106200309030380c2d02d19250040e1400d4420b6841880b048403414414440039a541805495200c000c41c41e100c1c0856079140000b6001c0b900e80e902146211500051802601c1019000301d401c3e1002e07034480fa10207981c1c42003404101c0c0f0580002401030300304840e07a100c603825041036080d00c0304d8004402c1025001c1031400c45003141c5150b5072010f505040040e01c1c4d00b5030741c2c15011382c40a0303c108a800d00c030008880c50303001040030708141800c0d1029004070001010180248103030300140c0303900c280454070781200d1038015000329982c4084c140729829514480040490f03043c01c0703c503d15405407034400e849400f8115185181d001101172115021a520000303003a0301d03000041e40c0203040d590940b001f9061200f00b41c10448000050500815007001c403070009545448051003512640041c50410301651007004480e2102c406c88400705040000452000385580715200041860 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 815934838 1250 815933588 815933611
    0x81902060702010b09090618010b04020f0702090a0e2e0e06040c1703220b221d010e0915070f0311032203120603030c051b010509060a0e030d08 63
    0x2d120408008111170215894002503000d8800200040c429440c500040c10b5448000b243c816220800502030742c00001407110040d201154140c15803038002460307134009032203420400c0648a408116915240700040c00c0d0307813606440c8040f00c100703100304214141e4816550303402c10002541d680f1464503004252025215101d8100340410000312800c0050f40c07129443c0300039450312080d44801d10b003412a0340c00c0e5032421850010000380c0d200300d0384020241d094400c612030340e10500e04080070344c5180d20340d0004202502001d650b41c400507000019603055810317001c403a08580c0d488454440c601802c00c80403c0720311420000380110319810000b12415204140ca0500501c0c1c00030782980c10900040314011709040144103414210f80c10707181c446039464040d20317140c0003031070050395070100703032086c1d503004600141000e0082001d00071f09000c528407441c2c550868995202010700000d255026420640d48140d40000f041d0050328014545c111407583e000d02030380c07950115030401800c0350604a42c141c5550 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 815936088 1250 815934838 815934851
    0x203071514071a1509130201050c070e010f1512051f180c020f151801060602060114100e130f0e0609060906011d1009020c0106090606021f020708190206070201 70
    0x101c04e4281e10000d85001d4820b42203990f41c441103c406080041d82079040c42401c00a940342a50103008200c003420140300109029450035084501c00202548240c80000c00c01003182500c030342c0010b41c004a089041400724190b00c8403040c10800180b04444030702c0c20809100005140150380e11000d5111301d10301c004018030800c0440aa0325044002030413801c64209501c0d5402e440171010903560424900406594062041e10300142101c103141c109d400503070302020042014861040010071402c2003940c41c4003558000c044003170f056031054955144500c130706840c00641c1d07030f80e15031240c1c00a01d1085400d10243c0010704500b601c98400b40d42c401300d14020342c000614100350001d0000e040310f0806a61130290b8901c1d43c0f00300346101c4040c00c86000d610b001c0c0c0c0e00203000c0340d460014004d03c3d54030100000e00e031454810580116015a8040015034108616001d410305210481001c034280805001d81d4030030140c50b0406e2180320b100c811003450102030410491183d0700042380361040005030000c200d00c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 815937338 1250 815936088 815936101
    0xb100c021005090609060307050c030d050907050a0305030306010c1407030b0a060b07080a0c0f021f1101050705040504090203010b0a1d0708190902030a05102004030203071514071a 79
    0x240301d51a40190859410426205d071401c000004550000c41c0b03191450806001c60216401c41c3d03c0f10b0b8102c42c943c2e85038030521208120602c0b000008103c101c030f801640c103241d03583c2c0301d413240030091038075050044070460304007400b080c0841405110906002d54600030740300e1030303e9620100240c4400c2e44452400c1c401003043d24a5008480540380c100b0340c05401c4c02003d280c01c85210180c000c0448003d80942d201d8001601c503040d0107410f4204850354026241c01c081c0c0000d080103082e26007a02280c1c1040305000009400100311001d644c01510086051020f80c0003081c0134000e82c05050350000108000001c041c031000300394501001b0700d07000d486159141c621007264200700c00e8a4040c0030884080803041d1041455000801c4544042c065801007902d41d1541e40c240051900c00c0b00e51540c44203541c4410460000703c0d241008005600301c1d04040c03d41e0003090741c41c82c4600a4005402c161440000c00c10302602c42c410000311050449982c0d014a071400c0800c65408401174081c680301000403905 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 815938588 1250 815937338 815937347
    0x602120403110603040f0f0b0601030c0e0108011205120a031e0603170c01140718050405040b071110020f090405130b280908090102070e07080103150b100c0210 70
    0x44a0b00199004507084541081280d03d0f400a0401c0328241d01e4031070f4402c00120f5440402e05580c2c003420340c844c81d034904640050241c0703200d80e20000030403442c080300140356a08149464191401021017a01c01c3d9054500b99141c854804c0c100009074001044c19402c0c6a815040580242c1068954100b4505540c80c80d0040d034a460200400b40103100c0010304801c0c0c0c18134040e14041151500200b04400741d04102c9481030700a50f088000120a6950100c0c040b500c00703500c10060034151000c00641c039150711640d210580143c144170400040480c90004100100643c041d01d05020b00f0840d5121044da54a070300c01c0d80000302142c000d41c10100011000000343c0c080b020b400d904010802c10540e1021000903030300315012011800303d40360444400004c1094814140c0d250b224113000340e502d41242001925010441d030140422528200401000c9030340111b415045a5001550b005009415942d400c013510000b010290070200d914000c2e034916038403c000c02c840301e0094540a0b01d5091a200c102c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 815939838 1250 815938588 815938597
    0x60f03011b11070b18012706030b0a0f0308030606041e050301200a18180b1e061c0b10020d14130302010503090a0602120405070801141810020d06060212 67
    0x131440c2d001485644011851000d4100b000f01d41454107440d4000702d440030140c18198021000c5000b503080b641840040e4140c072075090310450071289024047e00d0854031601c1c4c40d509000c0141699000f10102d249a110082500c015010b00713001c450790f2005203280000070391840d10036a40301c4d6080000c51640384425000941d4518030392500d00385880c414090648040c600c4101c1500c0343d010080001803aa2440038256140e401e0882c804180041607404000a4000f4002650340c0e11201d2201c0d00c0d100d0386c0390300442e1040010301030f00391002000400311310010308a980700e09030407683d502c1080c08850f601150a0340d4120150716104020f0b01c00045014941c0281010340c00014010101840558020005140d10000c508119000d00b990341c1d48040998014100c1a00041540f00505c0300300202401003c015101c1c01000304403000c0c151600d08a240b4024100c2088081c182c2c4a407074080c40d086c0414104000203c0056548150701c1c00726000400c440d20804005005241a090651040b5401c03134 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 815941088 1250 815939838 815939849
    0x3030c1f02040501170403120c110c0406060801051c020a03121205010509060103150504020a0f17040b060f010e28060c050a031103070c0909030801090203100e060f03011b1107 77
    0x117a111100e2941400034808054020f4061055001c0280c0f41460a0300401e4250782c110364440e400000190510b903c0c121a901c0080d101e1070800e9001c0c0b1000f544111320710704603001241e507504101030100403503040c58056000a5000302045601000f402002c4c8060840c154081d82c035100c81c00700e0040c002048520070300500e544806c03d10040744280d8030a8114211024021b56040001c5a50b20002001c0364071001703400c0c011078210b0f29034404590300301d684501e0354040080e02c0841c0d843d187d40d0b81421100c001380954492104107404075450b074800c80101e40f00341c40242c50b0500050304111a0728201c07a40b006c41400d43c03580c0e2800030640b030344108000144258001c0040c0203a10f9140c2e0169030280c1c00309480d2126101c1449a070010908074841b0000400a50000103030351940d9041c002c2000d20142c1180091500400521019800211039a0f08580c2c96038149045520307603600094a580340802c140b6419030a00000601c61840300c0c00d021580030141c1c23106018284c00040703094031110184200b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 815942338 1250 815941088 815941097
    0x9020a0b030702030c0708060109050709082104120c080c0301110d020c1504030504090b040b130e030d1a0a0e0c040303081b030a050f07030615030906020903030c1f02040501 76
    0x400003485400060358004216005072818181c1070349542d45050026404a00990f00a0004001c114910f21a841c0c00007403500e0036410007030814840a5480c03140501c4003103d4161450300c0c241c0d60810b402a10098a041d24003040c40a0042c00d01c00c0f011301140c000d100b081e0280c0c0c00194520320381481017480c0da5004008450401c45a010000025000b01020301003c1c014541080704003100700030690b108a101e03841e03d41c1c881c0e0034451035030201c1b2130b044410390040d850305400c503a03d943e0b4224501500d0b284940b000c0341155444103154150f006203c01101d01754148a40d1f1405200b0000b41d030220500709946000020b66160b0005040c2d05040e903403404408001c10041c008a4842c1d025203510201c243d02003064400c00500c02d0905904c04c562084c69241e4600520160321701c01ca04440d0403020354902440114288030100d1600144904201c082c1685c1c1c4584504020064040d2080c40e100182602d44903450b0000042c1c0315641e00200704414003031452100301002d960b1003601c05594042e500d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 815943588 1250 815942338 815942359
    0x1502071e030f0203010608030a02060f070e0d0213060e010f06020f0607050412050102160c091802012c040207060207030f0519050904181407270c0c0f0b0106080a0902 73
    0x31001a9224051403e070f070103548644010483d0b1004000424580141e6401085e02e8905a004945088030242403581040410b4031644803654400360509038160b011144071404100d2140507030006c040c581c0c0000d0044080100000b1070b542040c3e05101107900c10b0302958954603000360301f2a15400212074a0000c181e0a00040c414004000e184030f002d03500c0350000501e040b0b000b03076014646030b040c9842116440104101404640c02d00c2c0154100742c540340e001068200701c0e590019110704081c500031644444800ca80c402040410b05a24401d0302002e80f045507600742900300b24000c2c1d070000c00290003107a0b01c807400c44030f1107200d401203c110441400c070840b454403010400319201d42c01030603d194001d80303417800c1000c86031200c42541105842030001d4a05809501380d9182001c60591150680040c02214445030b81c1c0010340c2c04602000a18000074000c1c3c005d10151440c04807a0006420783c0a868404000c02c1084030003079060f5039098803400800c3d03603441022002d4a05d45c5100030f4100800a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 815944838 1250 815943588 815943593
    0x150203040b0d0f3e040b090d0602030c040513020306181018020a02010501080d052b05091f0c081303020a0807051b0607080a031a060f040e090d02190201050d061502071e03 75
    0x1001f6004541001f40064090039454864005a8106980314002c00d200010100003502e402561081d0803480d010f030560031440c1c42c03c0052a20f42000e05e00350360f880901c4c4005070114845228440180000070041490004014405030081d040f140c040c10156191100214009100007816807075246039645103450007900d1300031100200b110440c0c0d66891495110703c003420f03400700c1c0211845003052500810941300ca501200c1c81c03079014141103031102c030710300360300242131581c408461035119000040c240d403038035801d140c01c900d08118100c014113444004180c940c10440301151002d105c2040d072a00d4248800302e6800c100c034500c07070100014002c0070100a1041158040d0300f10b080000710202c0e1100d100126040802c009500459000ba80b0b260006400c0c40481c1045d83c003690040520030080404454000c000b07075030307a40c4180910000011000030f41c411a8802c1d0304681d880040000140411940d0b00b60b000541c905000c903c1026020b0107c0c0455500025080c010340001866108074005107540c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 815946088 1250 815944838 815944859
    0x1020d020c06100f1221030b03100c091a07020d0b07020c0306070f0f09090609021c15062304030c061b05120c01090822150203040b0d0f3e04 62
    0x5c00494120110100031141d41020050f010040100c6450110314002032108241c20070403000b44a100344c91400c4604218560b21055001c1a92601d101c60809103070700301141d00300f03401203942c000d5124002080c810100800700316494020080d540072074044080400c02c15844020441c0c1c040000b0b1b80000c02142998800d00200142d29018180001e01c00c5d294261070054680d031350000d00403a40c00041144a60b00040c200c0c400c040d0141104001c2c0001741d0000d841404200d1150204200003400040a20400450800b0101d4002074080c0e50b0346e55203203841410041940308800218a0340d4240040500f48003000c0ca07601039001c0007030a6000b506054003581c40c0c103c0024950300d90342c0d504400300081c01610040880007a504207140000c2c56001003400b80c801c10303801101211401201c4600240d40020035241510f6181021503141c2d0302c900c4022004064104071100c00d0703802c00c0c0040030040e101003060b200c00c4030150703103c203c0c05c24104014200914038650000030088100001c01100300b8a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 815947338 1250 815946088 815946119
    0xb1905010f1d03070f180b0f010804080d18120813020111030904110c0708070803030c1b03070b090613020a0b07050f06070e1801081f0e01020d020c06100f 68
    0x40d0aa102e550310045002c0383c6000c140e40c000310204010032038240900740c0306c12580c018104500302c00307101d40154400462102c0381841d43ca641403102c0e15000c00c08014040381958481c0044803c00c0181e10704101266030b14000d52002903585450360004007c040740300e401d045101e40c4000c00341003859001940111040080c44090001500040c0100c0b4101c2d81c650080040c0c00380038408403525502044081c80c00c00c000d60384150703141c0e409440c042042c10008002d40f9840f1050400042d21340c1d0102c100100b076407002c0030b914603607404009882010094450411805103a5000444185507502c80e860070404140b25006503101c20754041c100440d410035401481c01c0c0b8820ba054803103941401c24801e00e852020342c0c2c030001040d0f0303001400e40c05041051401c00701c911201c032000c0c1c155151805664507080c204c0702c1e14038a503200180c2002c0f04003a540191100100c1c0000856031906041030801c000d42100e05080c0e400e00070000440c004000e10000c84054a84074000c403190107103020801442c003041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 815948588 1250 815947338 815947367
    0xf010804032c040c23040602070303120902100210060609120b18061e07021f180503032707031a13020a060e12070b0306010c03210b1905010f 62
    0x501c050642d01d5511180030300c8a070103d02c1e40b100c5e10303404041a628103c1c60050f040d010705103801440200719180d400a0918101c0f9098244625403400c0e8503c03560191a10740c00103034100b402c00c0d400e900c9035940060140c41c80b040070078040081d10745070ba03030466006609206400c007101184144c4070201d40900c542d1904006101c00107500041c10180050410000b1a42c0c43c03058034034111076440c00003066500c030380c3c4007a240c4003030040d00c00e00c100c0c0c03002c001c0d0401d01c1e1098115a0340405040011003100280d000d0b5410400f1282ca030b150440b8040d41c40301c2003100b0011009154904504180800a05101641e41c4054020303000b20681c0240001ca220040c0103000410072450481e0241e110f000e0018003a0a1680d203480c2c80000b59020b00c4489118421000010780c04602c0800120032644142e0390041003d283c41c40540a09003822200c0030b11860070f0151007500e60b10403e44404150307104403000c101c02d850340303051141e00c032a40601800d110321802e170114610362401500d00307225404200c100782 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 815949838 1250 815948588 815948657
    0x90f05010825120c1d220201020c12030319091a040807060614040c020f071401020a050f010906180c0e060402190e040605040603030509190e0709050f01080403 70
    0x169541a4600c0c901140001a0364000c0790328003c5c8116400c40e00343c01142c06480b807241c1241c0c10318440380d01c110442c0c1e064201e540001355039001c04580c401d0204440340030703004040c0e011803070300006015129401580c0c03412003200030070780d51100c0b030100d4080c0c19055900210b002c03640000400007212612802001114058401c10104001940e580320b400c000c0d02010341580302d004c0d00f01051104907010140b0860640d8080079065040781000601d05050350003010b56512001030b0080140d241143c0c0840c014030354080c0760004440720405500200c030321030042506020b1354420350141280e0f260b00c3c403000b07401c262900c8020710007203000e800240d81080b400b40c401490a85055200c001005641d04d03c4d500040d04145c040010340f03094000c80c405084112030801c0420b03d9640c028280d0b100d840000c0d03004103641d0725050302c00041200b1900c010510300c1d81c00c1c03100703141481d801420b2805074000c00c1d01c6450b4840e0b058905500c01c0420700c2c4120703410380b24000300489140142111130310032100d200014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 815951088 1250 815949838 815949913
    0x80d05071b0506070824010e03030d2a03020322170f030402090a050903160c0e011203020d050a09090207060b22050c030f0f040317010f090f050108 65
    0x4440c0c032140081e019000e0400340425090182c0014040d4002824660b0b00113108170340c0045a90a4030b211440114090078000c44821001020909501400281d4805907241941201030032101e11030010303200049900441c4240c004c020f06504900055a501c0601c903185070344404000000c0c0100480c05010746403044942c03008501840d080e90204a1941c030721000401400304508283c2066034001d5658117085c8070074602007162a41d0ba0007410604100041804142d1041c401c091401001405400c0e0040e420f960b103940711160001443c2904034014820003203c4c0315103c0c4180300380c4080308050f649400a180c40e080440d0083d412030324080d60b526586242058803607541821030080c80d411585245141529020220100c910040441c1181c03d020410444050402c07800682e02481c021003184072a01e603030030200d5102149080d01c1a11042c07540000c203a002c0601244822a0461542848511420010740003950310070308c10311382d15a0241d088010403084d0350420b030314114415040003149 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 815952338 1250 815951088 815951117
    0x612080714030705120415090803091c0236060a12050f0708060709080f03121918021f14031504060906051203040612021303080316020f0a080d0507 65
    0x242079501c0700300500034500040c10001c0505092000c0d141c52020b040540c2c03180d140a0300f40e902c9200b1010321512410110112042c103258055014240f150040d0140ca3b80124003d041907001448510041820079030314104c00e210b440150202d8820040941300700a03a504d88100d0000040344603000319081c0c01100c508c0c80c0b40a9041200c4402000e80c100186518200400003408540041d04100d805800000102d060000008104d561403820901c0203540c3e642c3e1100e0a01d980c010a03d801801c4900b4004a842a0010100a440494021114039111130b044407041c203808516a024000850004407031601c2e5000000003665100d217158136810000c0c0d03c0d010019081368032941080c900a5540d400501040c02c0008070781481d20790007002103180c64209a8081e28203660b18152035030494001a14103900f00a0041c81c000650b480790407142c40341007041c0286011a1141c03241d600510a5200d00c403218040000c005101582000d01c80b03241c031600f01d50040241000401a00078401400e0007641d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 815953588 1250 815952338 815952343
    0x70f020f040c0903030905010c031704021903050105040c17061306020c0717010608010b0a140d170c1507141305151207050a2007050406080f010612080714030705 71
    0x3150000c0c3d0381d55102c10300711315000d05103c0d40c5400213410004042c8004001941007205e0794148045240c03d000c440c5d80c3c901c0015218919030501c01803100d0542ca0000412034150070540c02584503140c41c0700d107251a600d039164190891424280e05500031030206507116013240b0749194042c001d003409440c040c102080d60349007140c181d200d150481d4090588800c504000e108400151030709800902c8110071810000b1a0342a1500030101504044440803085a0b2140c1540f07120030b604c011107083c000d07c40c2001c0420745c1c01c4075800e19542e0150313811440100c00b1041600e4420b61440c0c84940d0990158888500c241d000801080303440842420042003a0b039541e81ca02c03e0210844080540c0c0d4030b1062001d4040501c0580003000740503080c000e000c110b81c0c02605105405000403815410345142c641c0c003a2410364164031080d04a4900380020683c2034021039000f0b03600302d2400007030003680c0d0785621645c003408112a0141c0612028030000f4001007413141200380045046040703e040c403c20741c45090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 815954838 1250 815953588 815953601
    0x30c070c0305030318010f05060d031206180203190603020102071403030c030309060403120e100504080d090606171605060306010c060218090705090907050a02030705070e2a070f020f04 81
    0x95141070005c150700040300b4012000042141c203c24826400c014002c14202e4061402c007c00340500881200040645580120000c0002c400880090020000810000d60069481000700711070f14580f0018410385004036400c895044e030040038080e241410120002c0440038050394540400c015980c00754100304007440c050200080070340b03003d007044d04d4064040111101130104150600041602005002c5002d03188040500740129440e83d8504d4104005d01c1004004004145004810001c1c81540d0b880001a0b402c404c40b503a010f10b001e000441d580d074400f00c0c840d03055001403a02c148088c3c10a03c2c051070f00705506041c4401c03000710681c6d0b10340c240d81006603401c603045113500641c1c0c000c2c50010316003074101c1481d0804c0fa00d800d9480000c0f44264a004240b2814810006103010784c030744c401c00c12522502c2c1c010050f40c50311900c945c0c4802e03442206444440c0034501c2c4505125898401d00e10200c20014080d0035989090b6081d03454800342d03020050142d07400040c0032031116403a1076500401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 815956088 1250 815954838 815954851
    0xb03010b031f0b0403020913061823030f0c0102130902030a110301080a02091518010f080712120314010305010920060904050c0d0903050c0d0e0105030c070c03050303 73
    0x540341d1402c03048001050b40809510419003809410411540b9418801c603000e50380c0660380e40c0750913a902041c0703142d44803103210002d00c1c6900e41110720349035120f603c070202c03030052281010b206184510004407001e18065444007155400801c0540d100c5940107000304400c4208e5000581406a20810307c0110b421951100780020707000000c02c103460260384078400d0b51850784444d403070841d4189101c4070303503400c41800000d00400c1c52001144d6032969030501c040c1c82240041202461422041c100300d0700176004e20400d64845040003001c501c02c040420141c09440344041030102004258403a184c080940f10801402d041d03a940401003030b001582c1c079290285019000114068040f45010000320000d51804100c599400c021b00f1200d6403154215414410110b4001c512070300c3d606002d981074400d8014107201c040c6001020401c041d084400381c400a8089d0041d106180e64080302a249941906001400a6410400144c400c02003001803e40d2a0044400310f0902d5101e9a50714034560054420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 815957338 1250 815956088 815956109
    0xd141612020a06060911040e04020d1e11040e120304030302041203050901020f0a210e04020307020c03060c400602010f0617030301050d030521041109041203150b0301 73
    0xc00d043c020741c1d000324001000803007000c10100550710a00350f003d000714020411003151070000f080955a40703040c9500d800c1d4001c88612000c00208090078868003a0707100803108102da000c211085880c040c403500c1c0b2041c1110028186a25280842207000c3e40010401c4080c10f9081c08003080041c1c14140c0b40045511a0304c03031555400084001920380355040110500e40d0384946c0209000510009200818540308105803031071201190081d2140f02e43d00b400540c02c548080204901b0380d80c00212600c910030709500b03581c1e0503180d00490890318420702d0001d80f900c8507645132800348070114581c0c01c03002c4601c1c5005030014441621111612441070f038801401030303444031525440c0e8403041c881e0000400c101c0c0c130040640280310701781c07948a001c14842c4030711960380502c03400217150081013250440c005001c840e1084084079100045d0002c4280e40948182084814135030f07c5081001c4002e0103070350020b000103410148a0402c4014015200c10500303540580c500c0014544007070b0001e14080c0c120702c880e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 815958588 1250 815957338 815957353
    0x1050d0f030c3503091216081201050411070b040f0609022809020703120c0314011502060c070305030a0b1210020903190b0a0f02090603190507020d14161202 69
    0x10b0004405507683c580008101c81003007032044240e0002150381e030301e02096200f142c94021800601355120106007002d00002ea0000e8030030050180c40500303a05035001242c04200101284050028034016003a005043c8c0304ca041c08507021403410307180e00124610420020034060f460741e0118400c81c031600790f040501590340344149a100c03244082c09026243e201d90031820800c90f0f0720000c0007410f01300d5118425503554142e41c0380c5140700703402007207101d00d500200348455651003414400d07814041400400600411f0085076560002400300c03203a46405546660540d150707035503000c00800d445070780356a11401500a000445d01d0a01c001c0090030000c040040c1c41d03a008000b41400c2614400036500152490765400d000100d00e101c1c0240c020b01640700000b50000095480c400174491074000302c3d03200380302204000104100c5031381100c181c02095000e1225807110241071360b4404528603403001203800412142800310312480a0f2440d0f4446030300710131000109840301c84000c1d10766296080103800009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 815959838 1250 815958588 815958653
    0x30c0905061002060603032b020307021b0301150b0306030a15140f0402010f140c190510140a020a0c1b080d0c0305090609031f051b0301050d0f030c 65
    0x1544800802d035800602014509100069201d2144600424102d04492004010000814100303583c0c595950030455480c148200003a5403a0100d200c205450400c1d07a1034810300d402d060280c214180e600e00c0400f0b004604000310005141c1008185513098410511101d0105031484911000c025618100007900103000207007001c80d54004108181c00b0450506100040c1da2100c4840725a503428a041307451014140340c0f47c0c82c24403030b14103814114425484024000706455a10001562084c4101c038178090131000740005440c3c1c00140e10a17088603500c00103404400d0764004219400d030a142c080e50191040d6607865000c4154800301d04100803407842172000b2041088001140d40c200d04002000301c440d903500418503c900d08006008581c0403c0c00e00e004d880400c01482c040140c0301b004a503090a46008100401c4129003008001228110800c000600e20084a050700d201800990b88a60340352140322007009083d0044041180d505210804202603a03039000081041c031840c40391820955 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 815961088 1250 815959838 815959849
    0x12031d1513051f111c0206160f1409010302160c060801060216031b08010c2a0506012612070314120f09031e030406060b03090d05030907030c090506 65
    0x75009903000f4400c070305118007000c0403100d440840c43c459151845244410424107401c10886005c01004000d01a264940302c0d50042443d61041c800c0025521040100741412501041c1c01c000c420b011400007028101040c4146004050300c9e1810304015140000c0100c0700c610303c0600074416680da08640c4002d0041660207840503006141600c001c010307800c2c00d1808800b03503140a11005010480c181c0d000303e150344402005c90020100390300204500c442100c0d0240c074440d032840c8240300004142002103102d21031801c0080040383c108006000e10780c200284e031007070800203104188640081c50b0103a54081c6040241e60540d9403000c0e6071580750707411491b02a01000c1c9841c2d908181e40014007680e205190710b184407039440081003030740f40020345444007500d00754030a0107074489401002c60340840d150311558009600480c495141005207560702d03070007881d143c003040c2e501100c0d0b5004182c3c259819072080002d141c120039802c0959801c290741e680d4540801c1600e50102e914075450b1400c101d000c1ca0070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 815962338 1250 815961088 815961127
    0x303020a150207020114090f0d08030a1b17181609111e090111100b091b0901050c010e011e1a0616080705151008030412031d15 56
    0x112801e5043c500140d0001e40f120001910042c0702010114070132507903584221010070a494040c1421001e0486810024440c0c0d1085503840315460600509181088040100c003050655580d1020003d1504034040304035841d000c0c01c500b500100c014424080101b0a0101040e82d400100c41443c016190170443d02c1510340656000d4540c0000b44440c00401c09200e001001101c5200e10203551000780200580d941c0c000417140c01802e02c075034000b05090324401e901030561310108684c091890360303030840e00741342c5603a4400301969411000d01c00040554081c1c0003500010044a0010030401660b9400f68210f038842903110845941140310304107070309524424a141c030742d034020310008088042d20110700c561280c0a030614034681e400400c64107001c0210140c401669001c400e17620f00402003120780b40728400945070f003124010030000c0011a82d000008a50407102c0e0b10901c15080c000588060f81c0c0740444500c509211066002ca1108030703614041003640700340d042c0305a1070700c0d0b1070410b0352600c500300c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 815963588 1250 815962338 815962373
    0x90212032203051207080715200708091207030b04150b01020a020108010b0904180c0806070206101514120103150c0c0204091703090c0103151508041b0303020a 70
    0x240703040038400302c0d0010800c0c2810f40000518165a80c481d03207805009032180440251150000003821040d005003600107141d1344407055855010b070041154120058850380400a1405608002101c06c1e81846102e10940d04084030940750125500d80350034801040c03c590448448001c496465a03102480c130400104c060b00384014481d039201d540c0045d01c4164103001e40030308013101040200899640f6000320706080020150702c0b8008440385881e4098800502500249005200004040d1840050040e2054507022001001103240c05c94804d1a82c214508240411100880140c02c91880784001d0901200c900c9141d0384540c0755082100e01007a880e13440d4008a81440028820254049503030025250100c1d00080c1e0040c0782d00d0004051101104000b4031814003100f0000461000301d0b91001d14082030300e0511032030009009a041d01e051a005003903170305c0c1c1a505403288031841051b280d940070344541490040d00c00000c0e841401032040740c0c412001603015900120030400010f40c02400c101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 815964838 1250 815963588 815963647
    0x305070206010b0324040225110111070b03040501090210180602030327010207051906050c030610261314150103030518040c0c02030105100b18030109021203 69
    0x240f926441780c1e200140c1c1c0010104414541d40711000f692680d04039281600a60140032a103e102c03941c2c0c400c00d04001c10240d0304020118102380c4154010481440007111032005000b07903504086a007265504080d01c2030318199a140e521400613160601d0030b602c0c02409855140303060325007641001220030140c0101046400a00c14420240c203814294243c11b108040c851228040121213a030080c0a0b40714003a01c1e40c4502c0501e9654001c0350b0301c042d1100c42c081c40050080707030743e0b410ba4640e2038070060b1142c9800901c0c41001d90070052140b011504105982c501c42c1c1c02d68003144d80c20019802c816656a202540c0c0a0007580c1006000d000c240c0780f50700d0420181055a5034080c0b0820041414480901800b80000c1c03c03007014268440c00c42c2c56403c0061003000082850347c0020540c4c41c01c210200e0203980707040080745881160300035003803c80c1c00d10400c032450511000300c1c2644c42900c06940c00c0e015900c80e042d0000594940941c8120034103c000212f8560070022100c00c4184c100329030201248 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 815966088 1250 815964838 815964841
    0x2203151b0c0201020c0d03020a0b0a0b0111010c0801030b04110d060203071b0b0636040201030f1806110c0a0602091f0c0303110d15080c0a0501170405010e0a030305070206010b03 78
    0x140d030041780400588104850601d190703000341c00d00303070300380301c61101c0040c41c6111050811044510a45c07181303030900000e07a03078002e010805034a928202c801c004141ba01243c0d4240040000403400c000590780b00f4460002035440082001c04161200c02c0c2c1041121860780200400050759480158170000000e030745030603020456903481d011000034010300503600441d060400200c4006907040800c3d4900301d0920001e1035003840e00e54102401005450407800641084540d10505025014111581a6003c00180c3d0321042d6a00c2400134090f159094445000030b010032040c139a07050200750042801100d003d0b03a280700c0041003000c1010880703c08075004102c4000322846590145030381c106140c0c1801e00140707021100c1c07a1211140140502d0541d00f03400d003078600600760503031080407049074440c00807981080d640104128a2041a00480e40000c0114080d4109040003900d102e8005000d0350000030f0480d00c00910303c3c2000c0c9202c20070350100340ca400900c180594100300c038030700502c581208141075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 815967338 1250 815966088 815966093
    0x61909020d020f0d02060712080a140a0509070807030b0f0c1309020f040e0705130801020412060f090b040c1d16030207031107060903060501090504082203151b0c 71
    0x4075110070041e0003503c0c50a280c143c0f90b01c0b14104a880d05400605240d182c07100c1e440d1961022210f0182c01c0002108000401e410743c589026001008261080785025655510440f00040c50000d00100e05403042840004010a0612040010310f002d408542410300e0301c0c00310708445c842e002d8082e40c3e204600304221200900000014415985240301c050b0355031b00080d01a40c040c0c02160058620442c0020511402d5a0400d000300085400381e51700b00b6196543e580464200e004900c510440c0018034420600000d01c1c81d4001c1d050042940300001d0b50600c50f45070850030503022a42200c41400049061003102c908540001c0b00003504032100403140750000011b42071a40221544c0240754000c20031710300301401460400a0300d00110f00310b98445558000051012401d0310081d61401d203010b00100315003490b806424407450f040007020f4a01604080709a103051140955601481c40014020000031007010701c80e44a1103010a001c40e0003009104001038040304585020305002c408030b0348000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 815968588 1250 815967338 815967349
    0x702030a0f0804050907030603060c030603050601170a081801120606051606021b0606120c030303061908010c05092d060a0212031f080d021c0311070506190902 70
    0x14039651040d00382001d2480c40c030302518240915004664805804002c1001c02c55050303106100f101c2c01080b080c818412007a6003a01203070036a000144c282d800ca000140441040a0410b5021002131070440e00074008640b01e56190b90001e00203003d015031400040042d6691215a040c48210710440402c2010705d40302e0082c0c0b2324410400d01e80003141c00350034101c00f0721140f035058031510010701071420b40a400310302c5466140c14003101e485104052501900c0050840002d110341c106a0250082d8556258a0104803d058a448800301c242e26000404901e00b4000c1c0210103a00c0200d4540503142d2050408100b542272488680440c41d6102c1000e15030003c4c050070316400b20700c00555189a0303c1d0f0000e001203040140d61689420100400402e010810000703160f281d1007a00f44480044200c0d49503540541c82d502d82d1401c0038010707071002e0603140c0102c088d801d40130350850007410000741d2050480f0581c4055000301400303035000d4001800700030f03000048a0601004440303a80e010064804103500084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 815969838 1250 815968588 815968603
    0x1120b1e13080403060c0807090f060203030103110a15050304020414061e06040f0608091002090631150906090803250c0308030a0e0316030e1f03140c070203 69
    0x142031941441d54028841850b00f02e42c00795400100900c6440d11034040540355050a0350f03075000240307425074002505404181c03210290b6134950301441c0380d6441e54440582d58480540229401031000c03500060400c01304c00410150401a19410307220b140c0342c01008125000031141a45401c035601c2008a941e4035404c1c0711404001e0b4401c0300400c1d02d03002000c07481c5802181c0005941e1041c1031341c08102940c1018030a4892000346080340c0e81e01d03000c0307075102c0c00b030340955419170760050018441b5000313543d00303401c174484014904118030740c0e18252403074881080c01c91a800f1000c1c0c0c84e900c42d85881d0741c5501c44c2c1c00b440540b90900300000e105252001d05552881031041701c4421007078028000b1824480c034120f1042c0142c120b1800030b2220307140d04080560368010b5440800261070505c03200d92000000c4141c80c480b441c0c502440b0b203001c44c580c5064039a44100300045a00100341c00740240c401c14054022903900110340c2d40001c58070501104502051400340c51541116000d0049900507030300040c408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 815971088 1250 815969838 815969851
    0x1608060d020d031e03090c0503030a09230402120603010c02150a090311100605091e0429040804060e2d010c0f050d090509060d0816060501120b1e 64
    0x5500145142400c6856001c42582c003c000780b004106411105d6160f00010b030040d00611020351440c5d07449080560300d20a00c01c3c00700c013160b40c264041000c98112005031041c40700c441c448024000600001030100e90144114502c402c1da0ba2060182d07a040910032103052107a40d000924051064005400440344024030005c00d00791605000f4040601c1b610000003000c24031022122551220084100646280d00a1034040c400050004440b9041041410712815454001c07201c55103481d2500c185c124007849407041c900c441603180d0701d240326000f00002e214a008076160307500c8605200c0c00809452954130218815a03025405000807204000c8a0a010318034441c45496440c6000042c0e03452011244090b08031200c4020142c14004007040c1011641c0480c0c4d10340040c42d48450802651400a42e409500301158007a11000528840000c00f441d41c0c408000302103983c629505c003000d40313401342c01c07420b074000304100a001005605942c80d50402d403116810303003200d00304070407106000310014541d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 815972338 1250 815971088 815971099
    0x604050703060b01020a020a1d0c030c0d11040305150109060906080606040f0b06190215190b04020f0417120c03071113090602090a05030c0303180a17061608060d02 72
    0x952075a0303000b045103842ea10b82c0030f0041c0000c5989c54888103020b03281c00d0550038240d056400021000311400b811a407140b000d40500c2410308041184a00040140e1581904006030070400840032031001c018918005078020f404828a6040c114000155042540040b41c1c3c0c1d0304110051148840210f800d642c45041990001045001011303604007404132110f020782c100030001030000155858802000c03038189103070205c079095607580c4141c2c1c42d0400111500703d040c040c2400b04003030310316903500704032100e400040001d0308003100c040a02e03840758480d902085501112101004404c0020b000f990614065030f07028509180200e18550703240d01c00c20600030840b081008007a5044c0d40e82c04202d241000d0514000c004a40ca07920b09080290301ca60102d03841030b0300704080040c9500d80010501d0b081540940034508019007c400b00e00c040c007110b1002903000001c02004194441083c80098881c00345c0d000500d03141c242001c58031340c2c1c02410407156003007206060030040070340c0f10b41038902d0794268107480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 815973588 1250 815972338 815972351
    0xf0406080c151306080a06060807050406080a14010603020a030608121209010e01050c030a180c090c1e020c010f080411100e0405160f0507171b01111b060405070306 72
    0x205000034400c4158429680d142c1d400040342c213a60000c5907920079104090100300b05902d0b10025a02a141290b4070400603108000c203010b4240f007210044d030440910403020880c195020f10022485c5000d810417400a0b40c040303010856558140200030013011920054400b5140410300800c20b4800c65504000d00d000080208000034070960018402c848110700801607410080515240d50740700f0f981022440303041111b425210340c2c0d04201c0103049a4000b140c524102d240022410141c8410301a5400f400705160002e5100d041c103001c2131182d59401e60150140800c2400003500111a00d80d01400b008128001c000024199143c080f4000000302c0e0f1100700c1c20202802195005110380e2104c0d0418144810b100d10041036800c0c001070a0942c3c0c030380042f8800e06100440c0c20b4050701e080070341011111300360441c2d1a0441801442d03450102078441d20014072904941e03003503504002000c2c0800701c0005154030300780080400c003d0440403841c09070a46040039210556105e460340805002c1e1a940c1c40e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 815974838 1250 815973588 815973619
    0x1303020d03120207030305060a0815041101031107060f050c04060c080702280f0801140f0c070f050d020c100c03080604060f0b0904050c04080a0b060d080c0102090f0406080c 76
    0x5010121942c8004015566189140350080161005a4915000d81408600405c440c40c0c00b2420003c0c034224062403402d15600d0b92a1660f503d8010191541807594030010b608520104500421030740340680030202e041904416270000b1501c0c01059403641a00901060100d10b91000c1002c103820b4000e002d1a448840d2800000c445e508038180390003400350050b4040003100e20030725400e8216003914117034140d841e560ba1006801d0300c1900e020590610020400150400d160001d66604412000c4410342070204603a2001140e05c2160802d45080d840886241c400513410044c86900c0c01d0140c4102080b20a4040003801001140e80010180a1101c001601644607940110014034080c541510701960b585504166a8004060540214100400a84804d0107502282c0495001c400100a04c1e00980ca44070502800609695804800e00b500140443c007100060011406908001a66a410361040102d4035495009140c041c906201081045140100d500c0c0e4a115040d00ca46a1800d4180b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 815976088 1250 815974838 815974847
    0x302040b0309100605030115031704031703090610051008151003060303021006270f05011d0a05160e0414010303090501080c07020a05040c021009080a0f051303020d03 73
    0x203400c4a86900004000c108000000081c641001d00e1020340030000d00303440380140340c269400c01c10701e00981160040204009a812607100c98401140101c4900b010b40300c0d81c8107400c640c0d504000c03a80d00100881881900d020603c00b0b9a00070040114051442c0c1c80c10300440d00341e9040d44080d00500104d60006425920803807a601c180050040c440780030a060018007400600842c08280c0051080301a01042854103100715019118030f01d0201d01018881d0400460045c0042541101551a1118111080c2242c01030f940070b0500740b40c81c0c0d841d00180141e00000c1030f5005001c1410b82e8100405c5c0718094202810f070b80410000d5141c0b40040310320003c01300c0c0c041c2800160b221420402400004145980103448005607902642c90700c1498640c020080078074010504c010b544500c1549041200d407800790b110842000089c01a0b800c100d0301540103600f114040762080e00c6a4000241507109180d100c004460050101d003019400d02c3c4000107848400244da0000034010038010071001c0078180036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 815977338 1250 815976088 815976097
    0x9071e121b020d0f0e0609060c120f0d050718061d030f0145030c15050601080a0c0e240d060501020c09060f04050a0e070806060a0f050315070302 64
    0x1d40000090030004918000e59940070310030a0390000d540341800400c3c017132045c0165410308000600300350030a08580708004c05c542c8000c400300c1c142d20514580c00000c0410034080c00d91880160301c25904c44c0006422017007541d400422501c10810a05580240740114010600c29180c0c18a400e58002044140c0c5024500d214410395034075201b200d804000b0200b054000c990311403215000030481c0c660341f030001000a007944800c05021840030700c5104440c3c20304060280303520301a01e00307075500005d103449480710300c506004000d180310384500800c41c065821862003604111b2510040003201d10300203005284044801d6881d104c1c0c03440c6041003003030921003203081e0940c2078101a080e5980128100e41c00007802d4511a503409070140d12001000303803500212151042802401e1180c40c01c0820040000400e401845021250380d50002c1000c0c0da2010029031000e014a40c0050100b800d2510400458610380c0c0d0003072a401e414428244019140400d6100c42ca04c81c50902c103c0070f4540303400c10380c068001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 815978588 1250 815977338 815977361
    0xb09060d060504052404110904080a030506130617010605011d211c02060f19050405070305033010030f050705090c041814190b0604060503010509071e12 67
    0x101002da1159018071203003079016034030907060090300c1d6060b4820701230f0000c0f080302c0c0076000c4c002c10302848421a00940250307a1011340104414100b026400341c01e0101c446980207000007000707682c5803070391610003445088007400c0309013044002d0110b24001c0d41c0d02d02c00c03144801070154141103803940105c00e13040c1905840c00c0c800010350380c0c0305081d0018a0300d400d049506c840014419100465201465001000d0080c1814440b41448070f6281640034041d120240045072144540e440000101c5c0040c4060003d0481044070600c03280e040c0390034480754a92200e06c6003c002681d5042c007048100b0006001c0483c0d9220b550b041c000708050501d1400e0000b40e5001c5c1c1d4110200d4800c01030031489440040003942c8844045000c40fa840895140c120b48694041045541d49200032901540000000e40e80c0d6100000020424410032804110300d03030820741c08503011503400b100500051415507032203680983c9500e0459032052103902240652000e003900042480000f28107200007403000d802400d076154 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 815979838 1250 815978588 815978623
    0x50d0516090603050c1207171005010908030f0a1404171e0615300c0f18130206040305011805240a0507020309100c02040b09060d06050405 61
    0x9004001000c4180010089800194084102203049802031040c00d009003094041c1a082c0956200080c403000c40280214041c0f01c0482110714503458407907049481418241c0f8000c0c20039103000009401c4c02c000e03810045039508188050042e60440c032060300c500349002d00e0060506200301d0044242842075800c0745605a8254056560b1000300007840e0300c007520381c00c4c8109004181410902c1e110002550b82059810a40c0b2951600f40381480e00115061040c92403586031a1405040302c032100c0094001e0205900280c4465403103240188202040d143c00742d441e900e1300b00d0700069a84d90000000e00c2d10340140c1d640c5078010295101e2a0507100075550100c000c07c121403020a1345103100084003030440c1c0301e12502c13004901e8041c0804405117404031070302200c21280c861041400140100034010000c52006202c00b9a16603108141e0f0301e05021070f0749504c030721503035540148000d6542e10040c190184d003091092065a8441006070303034000d508040e0008207601c0d1403600034148070f6800488035180703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 815981088 1250 815979838 815979841
    0xf0f070803060907090302090a1116140601050102071d090a06020d0902090114060901082e23011e020a0c1d060f01050708130e0a0905010c0206090309010f050d05 71
    0x10820045001c2ca204850400740313680c40c40c404076504501c50000a40040112002c560084125086a04884c00c1c0c64911800d200a0750030b00d50600b10354003025540c1996940f031440700c07501c00340300e824050a4203202610701542803140400c0f4032810343d4512000310071041c0002d44040402d1003040d0105500000035983d6004007105040a048022001d91080c1d40303120000550369140c2d1064001c4c000f025140b6070810a1040040d41d6040000304031042d030f00e00c2002c45000d00800e4507a0240c1404104a86400f241d08081c10b9800c88010464420a000242d00020a4584e04000340260343c10402d503040d0b002500e05803040f0300707050f19500000d01800e006040803a440c20080c050b01c160100c00c25000856030b485508200040c3c15900ba42404a2410804100803a6040e0020165840c02190006526a4502c0e030038481c100c00710361b44500d10782d031100303840d00b00b00007030103408030744a00b620050499040c20a070b02ea890b4410441040d0510214503c62621079002c1c070203034ec0329885010410080d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 815982338 1250 815981088 815981093
    0x1505070f0f051e010e01090302060a180602070b010e10050a031104200316080415020c1207080d06080a151d0307050a02040c020607050301030809012708011505060f0f0f07 75
    0x144404040d94807225405c2c803031034a042c210144074484500750103900034210754850724aa40c2c01400c0003900c001440049107241000b040c83e0b40010903516102e400c4507002507240c164904403088000e402500f440d0708410f410840390303650000d24002e0b1394100030840e105801c42c2d00010010180002c4d550840c443e0702154036004501580030710f10900340803000000c220320402007124078100c09c03603004000020200700d069040c07206030b001e4900100103804480c030081c042c5409a081c1d0b00300080c111440038001802e211071051134002c800080440c000103080030b120700e9441d1076224625111044a85607a05600a46444030002e034030102fa005006a0f90768542605046440360a0b0034800e034007070b5080c2404842c555100181280c0b040e8095920f440c11a401c40d990035036140c0c0008980340c100040030a080100e4503004610001040c00718a800405a142c24299801d5900c589600310501183d07100400c41d5440c3e410844512104605030f80360f9500c5400d2400c03030240100010b040c001c04c07000c1075003004c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 815983588 1250 815982338 815982373
    0x1030f020f210a020102070611060c030c131221170a06050d0b1e06060403030f090b04121101020622061407050d14010b070803190e15011505070f0f05 66
    0xb01d43c0e00030383c25070b0703e07003521004152044503a0070a45000c55208030300040d02a40207001464008400c041c01526261400e03280c2c2e919112141c1011302ea07000d490800004000720310442c1102070f00b1052045045002d489005400c0c50914021030a5003a400c40c006003244031681d00241c00361400400c40c5880c124607003402440544101c410303500c0801c0e42a5001a110400d1040b188658402044149040d04558048a100c65075440d40b0b414017402810110700c8001d0000684040c02101c00038031684200d509002c4011031070762902c00d05642040d011b108414101100c12050219200c807024001d0300a884c120340140742224001c01c050034680b090001480d80320005040c0740c0d16418060111100c14494901c040d5000c1c86034840e040000c02004000803201d10280d540300d1401d5028030310107144081400140c561341d10060400340c2003407920f0701c40000006105070142000400c58143c40e01c0c03810018081e407240d00e50190041d04034400b13071001c025201007045400b41c0d000f070945803201c000805122 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 815984838 1250 815983588 815983603
    0x801090b0a03060c023306060705010609050703091101180b13090903180f0e040f083109020405132a021612021018050411091801030f020f21 62
    0x3200d02d444040002e220100e03000c41c2d00403480310003811006ca51a4542041401e030f10411040f1050354a0f211f000400c1c003540d114940c880c540c203440120b03007280d043c9413940d030130ba905091036410b00481511507143c60751211020300039145141c400b503079180da003c0480501020b4960240300d03401d05220020382010b40c0904200f22207810102c007541010744030280064600194001e0303011611089001030003007070f20010084005401211807900d007040d03107102c0c0807002605500ea04e1280b101d110001d0304850510521130010240284214101410500024010246c2e03c2c4110701e00380d1521300140c0091005000c010b00030160050240702c1c2c61003d000a034580c0182c154028012001890005143e920b0001c885840c59000301249080840e03504162451112007548280030005110046080d8559104000710303c20062510f6407038115002c10410320044032085444003200c1c9600400c00640e41c80700340380a4590464140111301680c00c04200340c15102c0c0b0103091450460316100c01c01600105540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 815986088 1250 815984838 815984863
    0x2030c1309200a021b1f0f020d11120c070803120406110c3c06010e0112020a0e07030f0204030f0302010f180215040b0c030a03060609060801090b0a03060c02 69
    0x5003010381c030790090b4a09005a0300a41d0240c0c104224441d4107003d03042d141c034415500103080100c14080ca0580003001b40001c0d00703110100340101c0680d41680e40400654030b2403c2146084960381c29080f4049480380003a4048800f103800210324451109000e00195000d81007201c205c0c0c0c0c07103103400700b070003012002d084c0c0f42524200e00d01116034202c1c5d56440219107041003000d004100241d01c0f4012030b03a0140160801c00a650798242041040f41c05006110806240f0701c4020071695042250440e0301d00410b034010a5000e007409450301c01612120141000c40f210795181d000c0654403100d0030303400ba241045400401c50310015000c0108000344150080c4907019074020013403181611022011030700040350f07a0080681b2489003800603d4441c0d032034208110722010b1581040d51780e41d0201c01c150000100e0324540d802c081600c14000d9070600c1443d008051030b01d81001c486140c84000ba0042006000381c603d03c0d0b403515014803064985562020056600200c2045200300640f002525a0848840f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 815987338 1250 815986088 815986121
    0xb060310240503160e130b161101140606031005060a05070b070914061b100603031e05040303030b01020a12081b090a1517100f0501050c0c0402030c1309 67
    0x2203020709000800c01c41c010300d184c0500601508251000314010710081040036403a018066003c005180407010b2401207401074808a0401003030000540340c2e2604140b215490307850250b8014042d06100a00e6070801c00982e9500d40e43d4980740d03503059803121540c010326000a000100f400c02c05612400500c8102d0040f032801c1c8107a2111981201c501e9860700c0703458100d8404182c10811460448010160703803440703504250b01c6a0031407106d54109002045848a038581c0c401e41041415003010031a14500180400101d03070743d490100c044c1050040b40030180c101940c5006040c4d46034020080c0382c5445800c02c05440d0144002c240c024036825003168040303c0e80c4e0004100440c41d0071864251101460000c01501c9040d08124545105040074980e44c4200f03d2280084c50600420202c964001c04020280c1001c02e404e01c020781a0f80d400c1544000e040200c200102d4481d500301161031109a0001c0701c01603501e8403190421240742c050740f2010034007804500700c0080c9807419075114000883d440c156 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 815988588 1250 815987338 815987411
    0x6060f111906270c03020109230f06090a0909050f06010e0f060d021305010320130f11030903120112020d0b060a051003050603010b0414130201050d06060305071206120b060310 77
    0x444440314050558082e040c0275441e1200000c0e0300c0c1890142800c40409003040d401d0030906000141c1600451303214200490741c424050b4184003003803240ca6112803482006041c1540f5003090351580078001880d901d10b45064102261880d0341c1e190070080070a80040000355011010850080108800c0c401125054010031903440405040c03c447d540300c44004090468095070740000401804185506042099031a104442d02d81c1c10640698099502c0c8002075031100c8a031a24001007500603000319402071a02000b100c0141c1e640407400002caa03214094003c82e071243c03404580802e03074642200b40d0050040098014540d41648494401d0034124020310103800c0f503209120484118886800ca08541ca8000413805002c000300d085055206140107481c203218010020103d85454104800080e02c032003c0c0000598096004014180c44400c00c0043e5440e1035410740010500810040c1036000309000500c9070b0b03800340050010808401400c0c08401c00c61340c40da150030390700082071180140c055803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 815989838 1250 815988588 815988599
    0xb0a0b030f060102010c03060518090316140f06101211060c100b100c032106090b1014161a0405010e160303090e0402060c0106060f111906270c03020109 67
    0xd030100709e400182c011a80100074100003400803200a118464520003040940c031105003100b5107281d46030040b500a1410010803040d01d0410442800155580e408001032103180d806810009040744c070003516804245c1898038040c50303840824003405a00000118043c01d0501012880390b1408078115001c1054408242c100300c510980d1800810000d4a07030700b000c0c0b000030b01804003088020f8a6120034a5080071984100c0d05544180c0c000342807042d10b464650946041001e80e542c980c4045003030407031003d1068a48403030103000311109000040204c0f201002880200e0451850030933181503159502e103071605100f03000c0c25400d49100c0051161941c1b080703252080040080a90b541640c40441007490701d0161000c2090103013043c1c0c0d05c41c3c4200300c0184080b10034400d4100500305078a40c081c0e02000300c1d101070024411014000301c3e0341c000c2c000321400c80901700440d03c0b1881d8401c0300014180c0e103035080502100e1102040034007404900c0d29034810b010382c040300401168402d0381e80091442d29070303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 815991088 1250 815989838 815989841
    0x3050108010c030218010507170304050d08010b070f060c03020f12101a040e10120c1a0c030f0708070f0f0b0c0c0a0f0201050c0115180203010e0a0b0a0b030f060102010c03 75
    0x4010400c0688410070ba449000d47c40381006055160241040303020014240c25100c003580d20503202150b2660040303810118031038020500900508201c1e51041c20404561544d804404401b40c0081003560b59620b4520307058089e070f058035603e0080221140d00e032405403880003c000800d4440034281c10680d0b02c0068407288071807a00b0205400040020304143c070b00343d181d0700786000251840c200d400e0f1400d80440e004070181924a9078030700413402c082000b49015128040c41481740c1c0c1519440004203d0b5410304480001140c40301000842c0c200e0f0350300c2c050f0800010364080c5400003000142064180c0b02072043c41514a602c090080e643e12030036481320020498944a100c0074a0825001031a4401c08103080f1100c6420700c3d030040c10540d10381018040342030f0171256882c41070402c9034181e56003440490f5005c0c80c3c28403058241201140b465050009101003880c00404030040c507512518090200d840e4610341030018012019143d450381451016a4043d20045841c24015880c048040d20f020380b0a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 815992338 1250 815991088 815991097
    0x106080a051203010b190e1203120903031b1818010602010b090f0705090d02090a090b1b030f100e070f080f040b01180902091023130e1c03050108010c0302 68
    0x5c00c98454602061600e41a401c110020404010721011301e90951482d00c0d010000c920000c00c11020b5603840d030303520929031a00030003d03040c3c2c0c5060b4024000c0002c00720b07007411941901404140055100ca8001c051503004208401020742c0102c81c2c1d481c082c160207030003902c0c14107032813484d0024010301c0c82902c04e011f03c01c0c104030740c0c10918000b08004142c00502403002420f41c41c401a012078907000e91900440d401c944203071601070b04d103540d07004144240000725030714503049110145000412806084c1e1611b090002418482b0001661404207007010740201034074005020303000b4442018902010050030f5906103000105c0840c82250006005d030390803403c05486180c0c424180c407071503402d00034488003403400101180d1407150f84922200141e82c400401d0b51082c1754822900200c541002c4d1250101400d452604046003a225012071650b43c0304507012140400001c4005072442c07400080616092960303000305e080c3e0008501c50381c5000c1e40b40d00400d050b40c0481c0001e2010003d004021000c9204c1e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 815993588 1250 815992338 815992349
    0xc17060604120302340501030b03070e0c120c0a0816020d1824110f1b0a090f0e0c0a030804050906030f030301090203090c0109080a060f020c0106080a05120301 70
    0x2004148545803200c2151880c0b10f0291044450301c034042c4480004042c03080303000d5003442d01003240e440302450220400d076001e01000e280600a0400c0c84021136603900642c0180e5a104d440324001a0140800005484000d45404598602c030b01b4910300d501d40a51000000d540018284400503450b142014200c0030900c001c0d034000d000c1c04c04040400c031581d080f82412400b24600a000025040e418011402c0b80880d4404090151103098503010342000110ba10116503900301e00418040341c40081400323421800308003480400240e01d04001a50864603400580c00c640c41c24031130301c0845581c0d0307000b200100174500807101c80c0780419007000468940c0c0d1000078004d100c108400d1003a0300b800101607411841c042e0445461814014411742181c109030010249140d01004115611800304401d4141210138200417000c3d905154003952540c0d03550b40082c0031162181700c401115100c65040301e03c5203415400802905484455540c2c644120010070385051041507040c09466800c1d03c12a8102c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 815994838 1250 815993588 815993599
    0x2301605041d0c0d020f0405040617030f161e0c0603060f14041b020d03061e12051c020706031401060f0c0312112503022805100c1706 59
    0x1c0490701402d85900700104400c0a00748140b14160907011203001a14a4541401d015a1681d041609001c02c42d1a281d00c281032841d50340803102c403444000301c11914074102020345184c0d02c190000360340b50800c4420900074403078640b4034682401002c2e8104040710081c41081140c40e91a550b480450a50752507004d05510685100c85c00c0060078810f62280704400f1000d040407800049e030a0900d4100c402440c07065015820441c40000c000d545481403001500741f00f11000f07845c030030160034402c0070312060140c42c101664105149050003810080c0c400d24100042e008420200030701e400a4490030544034ac4c070040703400c0070303014284041c2403c01241039820302d5a40005051349a01d08642c98003031700005038148203104048061f03800c22401848501c2001c005034590700d041c03c1c006400d40b801c84005003000420340c858108000ba0307008c140c3c1d002c200d4042e4034000480c004554400b40a8600c407000405030301c1400c580b040550001d803c075404c500c0039900e48a84500a0546c0d05002420856040f58040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 815996088 1250 815994838 815994869
    0xf021501090e0a0b010f051203180f061306030209100309050a03050a050d0c0207050f01020f1f0b090f060307050a06090510090803070c080c100c060230160504 70
    0x600807544a62902c0e0b000808546100045072a05581c1060a8000d03031034030783e040350041c049030403c00d000c14081303420400110318145802400c190b40c0d000030b0622501c01e07003a000c00714000c0c0d03682c0011348100e00c40e00c04043c1042955440040c00075405001654040c0c4402c08110a01c1402480b40c00c44558024000d400491169a0100c030380e503020200344018440b0a1240318400400b5204800a02043d0307001415524200000c0000d48080c0d07031040ea04540c040300350390028940100d40060200b000103402072076141c1002260001d00f01022145800c4000c0c03004102e050100b492079103010b80b4041e0306540c1599222814403040507141d02031640800c4100b6070401a0342080007030015124801e242c0b031000581c6860f00a0304540c855401650001c500d580184003190081c0710340868818100c80c603000402d00940098807420740d00c032014004c03650219a448003a00510310003030300c030801d405101e40c0803000d01c0b400c0c20f5035aa095800f1f0007400800c10a5007101c9004104072002c3c0d07a6500400d2040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 815997338 1250 815996088 815996099
    0x3010e0127080904091b090c12020406021902040e030f0301030611121501090510050c0610050a03080c07080a030804051908030c1308060c07050c0402071e03260103030f021501 77
    0x2500740b050040300c0d43d1b250a01c03003d41c41c071804034100028045081c408a0090036070300c002010400d514100001c3d4604c1004100042500003408c400ca03603201c800f00d0b144c4000d031400009c0c01881514401a214000069010410958000154141d07481401d0030403072710034842e01641c0180a015100c2c500d42c0a00c20201303031840070244041d07090100500d882030166441e03001107061311201c450004080303100800d08000c0414148030007940101d100e1070407211b0900d010300181391111144000341c81008006210348466409020000203050040c040b41c1c545050b51a00a001c1d103001ca4081d0307014000d0700c0c0524005040c024024800c1c2ea0426204d0381144c0f00e440b002c031000c0c2c1c006680c0117065101c0c00400610711606000f07a510078542d00f03007204d44074000f07400d0950420440c1c4929521840c0304026140003d488201070880c008420010301944090b07615007030b211640f080e6042c40d50842c01c18685403c2045181e2134a040c1c0b4800d0366044401889150240d9603040e12440401b00c1044071030041c0305 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 815998588 1250 815997338 815997341
    0xb090c070c080d11100e0717010207060203090f0d0c17180a030524010f0e0c13090b0a47072303041a0a0e03010e0127080904 55
    0x3124050140e02058559a0080520f000c07a14007010707010038121281002d400c44140301e0f550300303155614402d10a070300030300a006444c1da40d61700840d2a08011140750342130f41c100950507100d1b5540e11190031941c9003040b42d522561011240b11401c401c0c030681c0342c4500b1481c8190380d8109503942c402e80b0b0b00c00b0000c9105918049403c007030016803950850f0071200c1016a1100000e8008500440c09400391190711000540501e014060510344d012007070004010306442d94080408480c44480c1900707071030310ba1450890142c40f4184080b0802c2001882c08602c1540503800604004000c40e80030f020183c0d0380d6094451940030704c3e240004440c0b02000020b20341000444410040729111002c18060855040c802043c2c000d22820349440c400d104a491900d0261110b40084440c4400107608291400d42c042c4d640c3c0d00b01a002000c11540400d0207902c0f54056103001c01c0f9040024000e114000454201074002c0490b1088140c8400c02da40a40c0c083d00f03826115010fa65401880711031074001558240030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 815999838 1250 815998588 815998597
    0x1205070b0a1110050a1b1403071b05060604142203030f09030801030c0801020721091833090e0312240f061b0f0d05090102100b090c 58
    0x284a0b00420707107180010240300e0b500010036120000141c0c0d0070000c410b10101c1303c034006101140c1100320006d811407a003241031051400382400303826980f81e81e448400c40d4280900f80c0404010311a003031456003000004102d05220302c209681c2007000c0c6c060300340d02002e40b0500341d0300702c40036880d013000640d140f050000604128500a0402146803409806080110f500d501010340025240400610070082c9000c0e1443c001e00402000b582030895039203480604680107688924101c18601c03a42c40701a0055107000c000700010b070b002000c154921000300001c1e01d1441d0500802070060200d024080c0341c0034014070b90b22442e4840326010710303003080902c03801400f070110803400c07922040c4040242040e40c0904e030340c40b5403141c1090700b00d0340a0900e1211000012004658420b0012008180d46070b01c5000139510903040b841c1110742c0da0184201550705040c50515010024028800c2d64120f65402100a00c05400c0c00e0b422110004072512402c4211845405240d901000c00d40120301882c01210140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 816001088 1250 815999838 815999857
    0xf130b0402010c1e0303150605091314070f0e01030911120c0d05010207170304020609090a0209030105040302031e19081b0408150a021809070c0b04060905071205070b 73
    0x551555080e502c400d200320104d600b8a020f0121001650010154180243d8503140700c840120200582400c0b0b014045002c0d18031814080c0745d4030446000d4600203034026940070b10704100d02030741508080c6001050020036010190109a42203130314983c5510a00c20100100d420020340781541401c0f070100040416045400001c07445560b000780c0955850703200002c880c61246e0001640c0d0300040c54180546107280180345642d25051040001584130001201c10240c0221922403003903640d424030030000d0040c1844190150b29002c200010550008010044500f44460300b008030401c804841445101d0000c0250b02c003022500c0071000c1c1401420600e40001c2410f944040950303401c2030107c810b03002940000400c1e40070f25540760202c4641200960040c0a001d0107520b00405c0008a00303051040c1b0300340501179034030040081c10b1103204008181101c0d9201116004504103401c104010b0484114190341500500713000140e09000d5040352801658400080e2040702e00d40076603800c00303822006d0380 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 816002338 1250 816001088 816001097
    0x30f05160207180212010806010e070807050f09011b0c0f0b090d02130b03060f070f1b200a03150e1603060c120912020c010e0f060d0b060301030b040b0f130b040201 72
    0x1100c170b5841c80340d0016070190103140005c00c41585455100b0f0044400540740e0360600c018001401a05a4044201d95501e10000891551010a480100c8000c000880c10750398180100f0103090421084080389421101c0e1102d024402548502000c1503034800e6901840d0b200c040d141c00c0c1401424061840d00183c0d00310b21000a031040482c0119052a008031001d080109044040000c22500807548807a22509454403c4080c9400120a4a40090034034084c1c841140c00300d000c000794894403003141c002040540349106003541d9103041c0d002d00d2508142d887d030303c03800c08000c1c04d9245400200844060340005903503500070b20390b880c0e072801001245602010841c9650941841110a01443c0242072180080242c41001150000c0c104085115440d04210421145487d075555210301d40b01840c0781194032075610004158400001c24000191540058010000009000007080124800c901954204800396034181e125401100d044030014006e0b1414610070010030f821a00050388544107060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 816003588 1250 816002338 816002347
    0x409020a120b0109050709060507060f021b06060d240e030331080a0302250302060f011a0a080601180305010b030d02030f0a050903070306020a030f051602071802 71
    0x10030400308454104008003080d81c01c0303030420007441c01c040ca030041c00202c5040040341804840108445001d01c42e16041240220303020062218030342c01040c54040c8950219074036903001c2d441981a500c20209031603640104800036640742004480800801d80c04000d40c0f0440d8007080145850711020348070030000d165151407000316000c04000650241c800003968000e0240064050702004002d920b258807600301c014284030002d6942c806846410195040c05a00c0d9101e1600d43c500038480c0c0c19200c4c0e2440c0011000d101410340105200780104501a610016a0707210391090385038481120b04905442e5003009103c441070311a841c0c443c2c103d07805140c0340201d90505041803d480e10290015101030750354241e085501c4c541045003440c08241e500245050401d6071010b440c0c02c2c05040414824000005510407031390f9802d02c4058091030784403501315250301c05080000d005041c044123648107507141174003140c400d400640741e49803801d00c00e0340100b120714107180c2904180707511078002062080d028003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 816004838 1250 816003588 816003593
    0x6081009080d060303050d06050d020d06020903150406090c080601180207061113140d050a0b15090906100501110604120e030a080d140f011716080c01111f0b0409 71
    0x10f00c4004d50007542e62a46071148005002e007250020350115209200d074041c15401a141d003200002c00300d40090005071a40e00741e00100e4246070301b42c400843c2244069080104000311903010019240c024030b6095502500d503e51203980700c00c2070040c54a90f600c4c070358210503220041d80081200901c5510041413180c100890b80d41c0f580c00c60240c0b0320b403401001c036080c40b51858615040101c40710446402c0700540060300c0701500d840001e103000d003104020301c0009801c06a10040c0c4001920040c1003003101d842c204001685600c0240d6000070341d0344a48800186542c071401b003030010030b150b00000d0000d03525942d90b00261030148440031024400b141c0050801c41c0d03410303c0b40c000c04502500e8480e0751000c0c1109944101d9a010110254102c1c240b0309101c05006100006030648810780309094440752402140c40c0b418500c0c0101c0e030b009441e05070b00419121400b003949000200282c0383c0950780003a0015003074440b23901d2164041030b0700081003008102015600446104134024000248a00b281d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 816006088 1250 816004838 816004841
    0x40e03030a090606270b270606040b1b071a2d160501060509040c120311010f060602061b0a0c0f080a0c03080c09010207030803040303020d050114120106081009080d 72
    0x200c200c0c0592010303d2505c0e000d040490050149810341102c40780d10032000f10703c094071031410540c0d818140400780030018200352100c408590250807110b13155034441c101402c41000711608080380340014040d510303000800d000c2d91101c0300c1c0b001d0b041c0403081d400c0c001e4548035040c959521000c4400305c5045610081c50034854140100240e201d54043c41807003c1c09030400c282036801d168083d6002d2683c2000b0040401c211441034010340d141000115507d180d42e00303048030080c01e01c13214080c0c0c55127044e04003810b104c6a94440b108840c1540c080e20f030150707a52421841100b8040100c9503030443d0410032029214442d80044216910520000456a460707484e41c1e207281d000078021101007100418294241500103074204c0e0300170812103806140624640000b9100c64061200400d9070340f01001040405009030140c5140d4001d681c803c00407903a49820707072502080c0f40f80e440ca01840440111400300c450600400080c0c681c603200030b2000c5218035800310000c0292440c250b0781024240710440d002c0c07859 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 816007194 1106 816006088 816006119
    0x111603030509070b1809060607051b060d0204090f0509030406020d031a04090605060f030d270305100203150d030c0b04021c030518040e03030a090606 66
    0x204690a803909640350090b0f200d4041c0824100304035114a00d0305c9190101c00c8440c0c259589480040c00b000788100725000c0c11581141c810003443c1c15a45d5442c0c02207070005030015141c140f441182c01c040381c126030840180c440d01c4201d515401907075400b9070f5802c071903c00042e518061802c1c0c000796644a2420907841419100c0c600f2804415803458880c80c821000f80007031141c00c00c1c1d80340c01402080100d902600c10800c0003c00380c42c074200028690400ca10316140c0e28070009404540601c41030f01d48440d500f001c0c00c01d030004800204240310519030110541c10240c1c882c2001c00b035114541c1c1c1d002000c135005031001d51042d000310741c0c01500b000709549c00036112200c607211400411080e080c14084000b11071404c030a40400c16600c08010b122404100c0c0180d10349001e04010401920424194010070364020700c017007120b518141d805841020f100340b20004d0426a03501964030451003 = true := by decide +kernel

theorem cover : BRFrame.Cov 815827338 816007194 := by
  have h0 := BRFrame.cov_init 815827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 815827338 ≤ n) (h2 : n < 816007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
