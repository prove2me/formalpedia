-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1727
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:27:12.282712+00:00
-- url     : https://prove2.me/submissions/4e469fa5-d85c-4102-8c2e-9c2857d1e8a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 310431654 ≤ n < 310611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 310432904 1250 310431654 310431677
    0x92301051501080a0e070f0801050108120702030703290c0c011413080f1b0d0f030b01080c070c170a0c1a031f050a140907090509180109060f0903 64
    0x2404440c0765455a03001503c030074041200440150801d80320480043d081d2059250b5807030580026020903801400e00f0394481c001004234402c14010140c0c1600d440d170442c0d182613a1540042e8884d003c1d030000804c60541c4030107401c04035040418000d03102c040c000301c00d5140c9c10a201003120784c1e040310500d44076560805107030340340742584504498050328520400d010117000380d07034481c042e9410458008140c0c647c20300403101e06504525902c080500740102403c108c00004070f0081401510b03940d010f06040c1071001c4041580d03405443c240c0d20600725014a500d4803a1460000142c001c45c3d889604050203074042030680840c041030b420005841840100c0f01d4039038a0060b100000d00300c8a05a82c03055081c8001810301003002c10341d9010001d0742e00a00324140d00d900c0061060380d400d03003004001c2d1031414002c044504040e98615004503031800c0803818140342c040001c12426000b001642501c1420040d015907032004d400a948156200c503040c006e148260310024020008480e0a400194904209 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 310434154 1250 310432904 310432921
    0x70603050114190b0c0a0203010f0608061e010e070e030d08010504060f0b040302060309071a0901080c03090601030201050f0f030c0d050c1602060a0c050a051b040b030a0b040609230105 81
    0x20b41000c810f4804510140c0c0f030001d4549240d040681c8100040c0a070010071401a6000e119241c200443c011000a2003418424510700e0300034000d0440341010707417030050440806251044181101c3d03141d20814655a140f0008480e82008001c030141c00d449602ca80124054004241a060b6030080c0c03810081030f5541c800100340b2765031510030080c400800300024000340c1800001980d10a0001c4101c44600380d507070780901821009581040b0a40c40c0104010301c842d81d02100d50f40c0c11142403000c1609500f00880903540728801844028144030000589441000940003a40c41c0709400b07171340268903440d00c5910403015601c4821410441d41c9440e001175608200c540c150340807200d109550101c0c08600c0c2c2e0a00200c0e40c4603224007024003401104840c0041d4080150b034220502c02e802400520300e0568501c40f80b1925441c00c644202e0418111f1141c60b14002911900e40c0d0b08000001159125400e0403802031110341d8001c0c22203444501e1058001103c45242e00d4a03200410080000da506c0d802d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 310435404 1250 310434154 310434169
    0xa05010c020f01140a0206011a040e13030918020309070608042f0909010c110606060a120204050607050a140610120c0b0a03230405030a1101020c070603050114 70
    0x405010508035010000941440100400e28940c10f060500c1205201d9074941d00301d0b008901003100692040c0010f01c950b46821044c00e0503c05602c1146045c1403d100303c1d9802c05c5001007644203042d04c025418002c0c144079444d01030040440c00c0c9408c000c5032a010000001c0d50003150300d5941071044080c002412f6100380705062089800660118010503c015100940300c20300b40e4580d06c0c09500300000d85981c0c0d800c94241e000f004000300004a0360807000003d0031b200c045461a1685070005000c11640743c56240440700d45814601c1c0048030040e44d04442c0000b4041d079008950400d2010400310f080200c0011540051801811100e521282c00301b0010741d9131303a081f501c049070030b84502e00400c60403088000401e00584034004070540326494908800c03ca40000915034002070710340408042440c1c102064518038080d07100300c0411460192203d030303500c0c45400c1940d000c0003109003001032080002c0d03065403920325180d8183d454440d50384c03c000780900000e00800d40c84881d041d4041300286450303030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 310436654 1250 310435404 310435409
    0xe0103110d0501060b0a120f090b0106031112010f180b060901120b15190e1f110d022803120f09020a030507030302060c0a0219021521060a 61
    0x114000c40d052082405141500340c1411079440d900c42802007466420030010f0b041d0f840d65030751808040c4914001d50000d40342c207000703401d1101d4a001000c4000c00c54400b00ea41c10358400b070901041c41107080c56060550722881c1d0345143c0a500510020032000b10b4211070808a803400c5640d200c50054202071201200c4030604201e6004000700000742103075002c2d14102d10404236002000072503440031400309840003581c04100c200070303200003045024170a541c144407403115810300d0014a02d000b00004100030b100d42460080c140440d0802402885100f0401000d030204031a0944c0c003030050440020b551045001d640070343c16440303215098810020101d4100c01650107584510340d500c0d03102c1b61038004002c00442002c0d516210100400035881e107020303c0000714031030320080040c5840d6060080c1090809002000f0010081000c50240b550018040780045203114000300d80c1d410501c0020b03d01c0003a441c90400c5440f0108024500388100d84601c139080c000307803080843c0e55641001b017050641c00c50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 310437904 1250 310436654 310436663
    0x11410030209040201120e010c030606050a02100b04091203020a0e0f09040b040519080405030f012009060d0e0d080f190203060a050406240903150216080c0c03070e0103 74
    0x84000300054500610800d4000c0e0060404005040500141c0c005035800350440d0945a03442d408038203a103e60601c1800020060b81c90114248462103c0c002d480302c902409582c1d40940300c44040c43c095036241d00030780340240e205403400c10341881600c01401035003103c02d0030400303d950310a402441342481b0002c2c0c5a1000300034603441942d51035940d00d281640d400f41007a6420b200700000c55104c02c407007044100300207000701c0c0201d0f01c3c0c034070300010103150214400c400340059041654080703130002c0c402403050b4081040b481080e110b1a0700e10101e4524000c6641c0243c86078140b04120303042c000b01007202c13885000079507141d42c5181d43d18944030392015801daa0344401d1802840c005000c2c0a0a54090744c1c21034401400801d03025a00c0d030000d07040e40c40f2604107640130802c1c903071403207025511050200c0f292180f600b031020146113103890f03050301003601c0900d03180d2980d00090038861b0451306172070840209a2100d55251100c4200300059030b10000108502d000384281c14000c14260803841c000360480303034403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 310439154 1250 310437904 310437931
    0x90102030f04060c0c170706060b040b030112050a050106170c01110616021e01021b1b06030408120108100c031b0e01140406080f0c07020a06050310260114 68
    0x30b540d141001081c0b100218410445400a01703000240d00396240071880c0003046100c1e40303a5559007480d408440455010038103105080000f08a11504401070780c0c11680110070b0072120142c0c906140f400e1290f1104028059403030000007044a454080c0c036103034020613100c202d60f40c1c629014019143c2c00402c000945090340003130001091a0f24274005022440b005106031000d400c1d91420015450b22080c02e160300694002c40e40c2c011100c0345803081d841c00070010700201000445480d4403586c2d00d01508226004620001c0081d0901a0400440d5070548082c4c03003810345036a40d10030581d15000002c2d240c0d0106401c0180a0780d0441c4280506920840c400071a011176201c1a5070a4502030301c0b240055040c4915512903065034102c030070107080201201e446842180c9403404c4444c0300884014040b0008131b105001c045c0143c0c45600341003040c4e80780c03420940e90fa86c980c1c5400100d9000a80c0c40031070b1112136402c1100304407a800c11100c00c0090558028020340307101d258900b0040d18100c540801c010304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 310440404 1250 310439154 310439161
    0x20c09010e0a0905010e060727090504230c03010b2205150306070201140c0301030b270723040b0d0803060d0b13020a0603020301080c0d050c030105130b090102030f 72
    0x400006842c0c00401030000000c040c46140da5150968101d40300c4500581c101d00304205403d50002151000c11200d061805003061046c80b81d11034420b80c0b1701460100030760310f0002804101e0054100b8500c00302d8030950340110081110040d544280091805000354201800c1080505062080e039040709142110034490f004111307030520091074001c2461219916100420482d82c40c1886083e010307905950000c1004410b80c40441c49481001c0d05411421500700010004145c10068180e00107081e00302c4000101c2c4a41e28807420600c00420403252401804400101c1600f0040c40e00c24888481103000303031f8006800c08010031980b12500903a0071951307402e506800592120300444d488000101103030402d020986845604600864501410904840b45507065103001111800200b05620b02589035604043c80742e0f0f10b44030042c43d0140100e09003400700d801c00105100d1004e0854002c5d00800140c900700400110380c2d00a4401a030b10082120701207072100300180202c03807090002592544a64a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 310441654 1250 310440404 310440419
    0x3110307051b100207031106010e15010503060102120c03070c050901030f02151e09120622111005030106080a020406052a100507030e01140106141e071101020c0901 72
    0xd5a40182890701d000b02d081100c1e103d01140301800707660b401380d9a40060317030042541c032900d40032060300060b5500d0094010404641c400002c80400c948081c81e120b40c403519110b00503450501000c3c00b0010300c22001c40c240a02641c000003900c0e4050252100f2244581e0365410300c41c40b1130080c00054501c04444070554054108100346520003a10030700c01e035151420342c205c1513920038141415010340d004001021200b520b001d000440340768070b05002400c4a0b0400a981d544281605503140c01c4002402500c07609000070300201002c002809003841c0860112b080d80109280d00074000c040c0411300c0c003004a09025000d102750340544001d511014a4451005010107415010b0050a0f0314682c2c0b003900c0ba8a82101441507241140c801140880c40d414a10000707400d8500086141e02d0503854864450409030302e62070024115805030030180303510a840514618940b06a05000703401c0c0f030304001c41c481c0d0007940030000e10065000c2d800d42c18803501e000004980b00c00704e0000f0f080d8006c055600521642 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 310442904 1250 310441654 310441687
    0x20606211510230a150c110418110a0f0f23041805070b0711090901020702030d0e011b12030b0301021e0d0b060c07031e0b04050a030311030705 63
    0x3600301c1070500e52169200d105140410001d41a9038043e118002280c505040450071400a040398061804400055407802800c500019001908188214100f021107454560080b81c40058804909040014600b003615410742c07480e9403e4040d420100d000228000580108001d4402d010441980d0910707011419101d0011030400d242c9050214450149941d00e0348241d0340000074030840400b0008003802c105045c2503080d40000702d91103080064000003407520000c000442d1049400d01c01e81d07164402607070f00a018501c0c0007034141c451641d8941505400c1200c403c07001c4d2003607980211682003034402c40c400e2040c03024020610411241d4901400c0e0003030300108261400900014100310821000090b5000748980a0180b0140018003440c08032250259050b040c1d01a140149425a10f078030007a5112030511010300b5801c610490196080a4a5084c428440e04100001c02078140f60501548684513186c0480100b40751a09105906070408141c0f0321404a03500d5881c208052556214101c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 310444154 1250 310442904 310442911
    0xc12030118021e0309010f05060105130504020f1204080304050712080a030e0c090a0b1c0201020d0503040c091a030f571002060f010308071e030206062115 68
    0x1c2001d0303040c0b03490f4001122004d14840c50642e0004034a6118a80d0f9081c00c0310f6000d04181e041003410810781d803400400354030700821910306440050343d42d1454410310429001f0302488088006041c0140000d1207101c10282d40100c1c0034105481d901c41c0c0d10180710180701c011007030050402c04103001d40b1030885e020b9417064100d829040180c4a074002c3d40c0c400607000100499117100d600d0755602441120b070904424414070313000d42c0c0600403601243c0e90000713503640c00035503c05410050000005002c11000c0e00d4128001c0c000010240f01c81d0004025071041c1e405640c100f58000e1041c5820a20803003c0040c0641c40060b130101c50100f1a40c03c49514190960b2030070301103500303001d4400410261030f45081290050064104450304081c902e10801440920f950681c0c01158410414001c0e40820207207000c0c1100d500a01c45507403000c5500c0e000300d000e207413885c3d03081c620365200c01d8000c20300d03030080b450070720031642100c003640000250354200e13214040103404400700da40030a00c0a0712818650944540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 310445404 1250 310444154 310444177
    0x7090b090d050d02060907060e030a110d0501020f0306040b06070c060302090103240f0e040b010e04020f040e06010f050d0305030a020c160807030c06030507020a031416080c1203011802 81
    0x510360441c1c60b0240f50503003929400e401a80800c0412440440c280030003001303800c2501e850310784a2800ca00195031007810304006010702019401d803003180c0e642d2800d074086c42c0e54008020b5444025825980400c1d800456000e40200d0424480030032074645002218241039000403030003a81820110300b28000c0d00300a0280d0306060366030b62031003a0030310145240c81400541c1f07484e04800c2c5051a004100e0f54800c0e07404407416042c0d10051200103170a01d280e260641e10400613a419980c0c0d40d00000e0b51004018500c3d68101d4541002004225004141d4034140c505010a48024995400c24040d41c5c80b43c484024002900500204401c64003a4004207800002d440c1250801155484900e80000c1076903c100516172010104100300300790b24038036000611a43c20100725529000f10042d403100c01c40c020007002c00c602c600b030f500700d40d0444009451501c0540ba90503001002ca03480c202c0c071183e100c000a5800d44c4035070303c054140281d00b18102c0317058441d2b00c641907515856031441003000c0e402c10100e145 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 310446654 1250 310445404 310445419
    0x3031204060b0d0b090d0c05070e040c050d080c0105010b1905130506040e07031b0903020d020111010204060306080c0312040e0c120f04060b091623070c0608070807090b09 75
    0xc156640f81d0050014090003000540d101c0e081002c84030746000c40c1801e0000600451203810310200d0b10220703007207088549a1a10010340e0395140f03000c0d044000c0b2508441d90121f41131400710184417401000e80301c801c0e402c200070030659032510342c1d1202d07078000c840080c220210f003c44600b0203107120310081c1042c0390501d040b0343c20840c0c4840000d102d039081500a0590414103c041018207a030500429a11a05050303031000b40b00e0821400030240c402c2408043c0c0103000c54000d003401c5900c074030903201542c49800000c6441e075071601c0c0001c1c0a056a403080200b180704bc4601102a03203004202e400c2c60300c1124410924103450844801c0d1000801440110030140610011403901d02da0400e90384511004001c0c1401031410b8940780048074582c1c21803901445d01c19003040b0303da4101080c07188201c505070030503050008480c0740001c03001c4041d560319265040007181140410840000210680b800c0f5110081203a6542c07108075080d2108a8404002412150b410095881064010409010080d1071032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 310447904 1250 310446654 310446671
    0x80d030c020a02040e0f1002041a0906091f122f0706020304030201140109140a1113120b16020703030f260f1302060f0c1608160f03020303120406 64
    0x4017201d22501c6a0344007078019140081d999103003841503801d40e00101008505050900d400c44001080b4444601d0804000203034181080c2e8480094604200b03004000000605240484a10120b140d041110102c1c5010a105401030300e540180500100754103418000c05138004103108048108440c480c025a03410080703180400d001e400191f103c1c500980000c11030902d2404074180c0310905a202040c0c40d4500200040301d849a03840103508401c84c10170129541030a802d8000c0984516416203d51070290f41000502e103440c04079004c0b006004c1e00903003c1c6a55101100e8000d440302120110041e0007605040c000240a240105444c511b1480d06d0078030394401601081030030107220390b590071014021080202c50640b94482982c440c8407a10228803144840c2c1c08510f45003c0c901400031003a001040c03124000104024149402000d07400d50071441c1d65541d00303540c8480d0382c81d80598900881600100b03c101c1d02c02c280c6411254050010b600e050000d41c1c0d486040c40029108441042d152640d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 310449154 1250 310447904 310447909
    0xe2d03030a09050f010e030a0303091e060b04240303050c0307120333050d050f0303040f0b0609060a060804210207060206010801050c030612010605130b030610080d030c020a02 77
    0x40c00d1070940076110003650b1401c1a08100e04585406036680c10401400c1d00750416807000305090704019410709000c0780c00740b09481d1140c00399412021441e810072101002205200103500030038220001902d003081400301e240b40680d00c0e49009503404054507000101000040e00c160001c110a500d410280c900300f00e001ea130b0360144118456141030019843d101c480e01950138030b0164529007100c1c1d1500020780f40c0c800d14155a070756001d118040c0b0500461010344240034080c452040f1002008054a5503840c0a19000350440d15808003511030701010400100282003080c2a05d00440d4010400c041030b519003501180c0350400200225405550341109003007040c8005801e0500910f103401818201d030034140d0080c035140e03050744050103580c18038080c464000450001c0b81c0d082078050f81c110241c4500148685d000d0492039003c950404050f000e54401c0c85c1055202c1a1460360841c1908c0d02a04d985c580003124601d18000c44849070030580120304c21078000d521a1142c85000d0040d00c1e40007009400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 310450404 1250 310449154 310449157
    0x2010b06120f0f15060a090b0406020a031107050a150e0301090506341b08070804031101020d0e042f030a050c0313020409020a03080309070302010f0e2d0303 69
    0xa15818008070000d1100c105080c4110307550150720b08070180e5013854030540d0002102d0b00340e03c0c03c038060040082c098100354480c10b004005000b150465580c0c40d0340e00c0100039543d5510140650010302d0515015424200c0420050100d4800410001d074840c10a04d000280c00d5039100b410003401607240ca60071241d1400e002c0e03901c1d9a80500050300d46413800c840d45540910382186903454102d81c06644018035503e1900c03043d440b56480c600050041c02e4000480183e50f000c25011744032620118000080050030030003803040d84d220301805103404e215807005907601c0c0454070340c2d0000309040f085c45549a0074564810901011800c6c00a50440c20340800710440010520641003080400020001c404019024058100d20700c90a500e1840c50008038410010303c00f408024030903030310303403040034155524112404055900008595520f0502c0c80111350f45e4403071840100e02044005050300f07445406111480c0561402601d544e400514102014089800c0701341d0305000080080d00c4030003652000c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 310451654 1250 310450404 310450417
    0x60f120e0109021c0b0c070c0806010b040501020111030c340528080301031202030f0c0d02060708060a030204020313050d020f0c090124031b0e01030501090e07030b0702010b06 77
    0xc0005506082030041c0002041012015015181d800d4040400108046200c84c0c2c0001030045098480e480c5160407000b44160380c1c014140ca102d580b0000c40c0c03c0f54054000d100304c4100740c000f007110086604102030355000c2100c40e5049040203020090a88500c407090741800c00c90444081c100d50340d4250314290010409005460139403090200c840080e003110640c000745140c1403909000102150b9a031002488140801003400000f04540c0144a008000b40e54400101c40026503c5400d41318900381c4e07491002c40c000340107206903070200300240d015451035402041c01407e0203194900b9034080c40041e62002d071036501045075400c000760124109000c01e4681c2206503000d0040d01900d103800920303015401100c0342c0301e0115540100018020303100020380c500000c1540c003803402801d4400703a000f0b02d04c410200c0722080324010209421a40041c803918400c0e0240c90400041e62140044012600820382ca20780d1548043c1d010300c08200340782400b540c022850710010a03c420818046079481d007084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 310452904 1250 310451654 310451681
    0x6090b1303080f13031119110316210804120b090f01020f0904050a0b030a060f0e060c161523010602161412070b09010905150301060f12 60
    0x100c03480d00c01c255121000d070f40c01920f10044100c03182492105103001c814802c0c001428881c409114050039a800c0c002e0440b4640442c18110380d07a44103081c00c0481c2c0004100c0c003442401101244003c0007028020312081d0780c042c1685120444048a0301c0c00000700740c100568040000b8000001e80c6035041940500e154031810001040c1e00b820f07001c16250800003400007405034018801c10803040e50090580302611001c580120381501da0b507034413400a10808100641500807101088103101880d0020180303100c2c100c50400103c0001c0325000d848482c1070720104403510003042004024a1030203a002e0325280610120041a0750984040040351508180b913a501e0b0404580c90240c1045501003900510a0703001401200b650600503810041050059620328a00c08003100c0464490ba045180c0c0c10841c0021904059195022118245c01c80c81c102400940f440c0004200384c100362070010280b01c04400c0903070031642054019600b04401c100c020003041600ca182c400b4001c02401100d0180060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 310454154 1250 310452904 310452931
    0x40b09151c0b010906090c05030121060b0402030708161d1e060307090306061401050d05100504110306030d050403021f050d0207080a030b06040807050d0602130815060301091e06090b 80
    0x20030290406a507c05441d071024050103000410080078284058151460326000c1003039154600c0c0341600c010543c412034660402e10200402c15041c2e000940d007806a83c5845a080b0140c04070a01214402a01c3c44c4c01ca07052482c04a980b00c00b8240030b070303014014110103540342043d00b031344a000c41c4903030f001142c2140026008120400030f200040c0704481c09404202644440b407148400068441e20a24810302c0d00603548a0010302e074040b101e10707014041e040050040c0007a910040c0d0881c070300d4005031401d41c800d0080250744018580980201c41c100c1c0e074094512410b0301401c041d8450080404111030051080802030182c5000c124270091194034030500700c0e0b6032a1485180000c003154900c0284500580c4100414409a200043c20408440049903841410b80c4580b6006000e4000c1c0e80300b69207461250800420300e503902142c450840e00801e04d601c00142d840204140c01c0e1a11808040c00349013036240240110320f01e1100c1c50305c0041c000d44021444205640c0c403c2c180740e40444e82c840380780c41d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 310455404 1250 310454154 310454159
    0xb061305040515010b0a05030105010c05010b03010f2403050d08090a0f080c0c030106030c05061305180105120d0509011116030602030727050108130818040b09151c0b010906 76
    0x101000542e001d0091a2100d6092005c0c6c40c0010701540f0060085a040c0560b440015042002c250858031035180040c000744180d0040f09945809000401289003488455102900070104900140d01c116034101c4010100c4419500b000c1d103004501500c40646070241d0b45160b00820f0350f0442c0350610f14070071000141d440000504040c20305043c04200d80c440d904114081010030520301070001580c0c0201c2e4001d5480c0348036010700c4000c482550025400c00c01a29080106900314505213048500682d0458102c010710400315450f48050848500401d10510500101d54801c0d02d11460f011001002c136040482510b080030000d1300305500031180d0940004c2089141540706c10000c010102031030642e00c60304800b0080b42c04400080c02642e04008074100010710fa84102c0c00a500f190b40c20030ac050340d0361848142034011404e45018224020381c100f51003d000c074241720902900c24118844d5122015103c00c0410a951300c99407006000300f10944601310115440141303c41c000c001c04030740004c00c41d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 310456654 1250 310455404 310455433
    0x9050f0f13020a0302121f15050108040f1506080f0a050d2309040b120d03060b0c06070e040209130510050405160c170f0915160b0613050405 62
    0x10010407404912105185100042e00c803401c0e20015039904841400619500000c15031501c9021203061052175200b165803224950183e00050807100b041d10001210b5445000544007880306440c01890351048140b10008a0141c020145103c0150500400c14954650300649894840012505190031800356141000410021000050300c241030a0074449012040806200b10254880500841c0001d2450032903450b80d12401080710002d291003012421031f001c0d656640800d884c0c04010a1521a01007009104082179910017842c002c0108200d40e9285c0d03007190707400903d0f188035070403503000e000220b015a640c03682d40788102900000001d885c501007201c02031100090740400e00407458401032000303500200c103c4851003003050030300141d1500d140c80d10301c05501955221204581020030800e81c012192801003c201300200d0300402c0284036100c046149100f12030500080d4101c0c0c200c00d00c00070307254298680c1d1002d0001c02c6961320007050705018040d200f0480d0101e540c0e0300546c21924407203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 310457904 1250 310456654 310456681
    0x7060f230105010f110f030703200c060a1d09090102180f011e0c1a18070513181b0501080906010e18211b030702130902030709050f 58
    0x2060300441041103514000002c0c11040407003d543c0100091894610b01601042180540011118085035074540450400038078401d69502c1031041d0f420a40c1030361418442c00581d17414007210049ca010303d42482e04006940c0d81d40154007410101d800b501d4526250391f240d41100d48203141680000d607690310070185010003029542c091a1103449007456041c62a6482000300b441954483d800180842d103403001607881403460b0b10010a0390b8442a20341c020307500760b0083c10313010324200c0c8404034a510988074910b46540c803034002c05402c880302c3c01e000120680c99070030122125050700307413903030315048180c56401c101482c100c221340b0407403001882040f10f541d000300302c40c0d404035805004c2e10240d4104541c102801d0350140006200b03850b054000c4c0c1240c82c040c401c048001228a100c01c04010301007281c54441d8120b038211002032901492083c3d000c2030701008440209500030300010380b01a04d04606402400809010fa17014881c0310302c08140740c8101d20503140241100700daa03485a10b48400c0d01d4510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 310459154 1250 310457904 310457951
    0x6030c05010e061809092b080108031903051b0c010203040b0709030b0a09111e0111070e010b0d060e04200a03050d08071e1115010b030c070807060f 65
    0xc0c1d0010055000204c1300120440ca0a49084801320a00e4030340401c000d24000c18203c0103081056040c0b04004045c2200607400480705240e2201080703680d98230141505c80c02908080e90352816460090040140300364415a4815a081a03001e80c0c0d103601c140c40c0100b5003200d61808640c0e903002080c80180101c18520a40c811507a1419403010790a540d40d02104180c007070a80074615440e0511001041042c5144100c0b0a1000e4101a094480031060050181d0f9030942280440e01c02074400351249070100d80c140903908500c21111590f46014500e0000c0c1e80011000c2d280966100c10220356200c9481010340140e00540c3e440a000070f000b101000e604481030440c5106a0b0b10040801c0040c50201e1000603a60301810b020f551507541c3c510a03540c01000c43c900000541085122044150300509058600e40c2c03100100e501d000e10046079105000c0080c041d04000b520244009290b42e40440d0081c503441b40301e14107481c10881c481d45c1d5a81544c00303545210104a44416840004a0764008031008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 310460404 1250 310459154 310459159
    0x90203060d030f050d050f16110a0201080603031e03070206060a0f050906040608060a020a03140f010b0c011e050105030c030109020f04020d060503030703170907180903030b030106030c05010e 84
    0x558144500010a4402000401000d210310714040380f20040c050310590310007401d840010300403482c051181001842c021541071120620140040702910701c5418015144840707040180000c2030990010754801c08001c1000b84d2510040001d800e40d0b41034a8004041001c00386580ca03224280017201909046000305164018184040b080111309550300d0304208603081568040041e85844010601a00980d040004141305e20402c2c0403200c422030740240000540c541d000c1050802500d9500200942912021403410031031005200c032441d40001800300084000002403892407400d24420319854081610312100d5440004005c1420140040c1c0a4005c04030020030102056500186950b13402d0320015010702d5003c00c010403c19416030012025040041c00c6a443e8680d030b2071300a09030480e48000c002d121000e603011a460150016480c405d07a10000f0407800000d5842d450741004250111055082507202d00450000351002c0c407418000d9800307009107803851410032001501c0e2016210b0000d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 310461654 1250 310460404 310460407
    0x504050727021c0c0908010605060f0a0e0d060e1e160e060109050411030a2706090204020702191a0a0503011e030203031303051005041e0203160905040c0902 69
    0x41000d640a120224588103a00c0010303140d800e4440c0061401c0400740f07038090703202d180680c082081e5822410340341c00ca80c5a00001d0000c5605c42d0300788031780350145101e5900208818441c1c5040070b40501d00b04104060b02600b100300c0d1001380d8450406403041c0c2c188550281d0042c0d4508480300701e100e03142240040c200402080100114180d5890b050294803a20b041c825003a00461002e80c40342c111400106402030046c0000300b103000d040c40c0c060303100b601c0d2100716925007804960505640414514407101c1400c3d4402018000d80703403a070241400d41e0b01240d015508001120040c0d541d06030f081c0080d4403070551440c8182c200890034400c40044a002c65818206200c26058035a000702200c0c15200292500b8814529443d5440f94001c4141c100070341c50300010800b00103220300b0030030700360490380a80304840d60400741e403103100304650703040c1c034040c002d14500481c500c4034051048000182c079101400b00d4030a00c083c10014910f000c09a00400805500c403001e00003400304486440006d880c0b2003a045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 310462904 1250 310461654 310461689
    0x6030504120e1f030e0705120d0c03030b040c0201021c0510030314070606080a0516060903022e0c0209060301151703040b040609230603280f05040507 66
    0xc01100c128201a03010803860844010843c0c03602c3c100c00c09034408602507411074500c0b01d24044d02030040c8034220115440385c140b0004041c6030038403000f03030b039842d59101801c84002d41340b41c1141c042c00d00300e206038185a203d0f00240e4254983c1e11070324007046060b6000603103c40030210144801028190705100050400703080c042c401072110380a50441758076091a4003800d44410000310240160000540403500c1c110380002e100c10045038a01e00e0600c5401030301c455070402051440000385c113004410000b824804c09000500749408090451400c54a80c0ea60004030700c00f8860226094451080000e40d84003044000c50408020a541125084000340a45980f00b921040c01c420305129034091540f0307000888034041002d00444020300321403195117944d141c540720702800c80c044030b12400058552950421492515032101d80c1c0301c0f84030040403140f8645030502e0b00c6014031000582c000c01c5108444008528680603c1f40780c80c40c900020011459250904205c0d042c018160f0161181c1412007410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 310464154 1250 310462904 310462913
    0x5180d08030618010b1605100203100510090b0a030902030c041e06050d0819090306050f061002191b0509190b030f0312041e0302011401090209011b1a0f010f06030504 73
    0x2e84402190582c41c160510a06e03052043c0303071254259113250141d00c0003040c40b4454440000130011741d08255034101c52001c0c00c2804070b810329214441c0342c5412900780800145540b013500036034005030008048507089035202000400301c9054007007902409205c00c21001000c07006024800c01020121400c0808180f01c0c1c686c3d0038240709544480e14600010030540340f650380650410000b8507003040d010030481c548200300641d0f851003611141d00c141c440701c01c0b07035411300d100040007000c000000a030b40c9424240ba40c0c0382642036220200f1119684500000800c1c10b8440500384c07440340c0540000800c500c0d601d80e6210080b104514044c070301a4101c01c2d82c69010b51000411140740003050a2001015038032030600c1c3c244210060f0528503504004407110003419415000b00d4101188881490720300e907620310f01d5804030700c100701c5500d002c42c4441a610200541900c14002624000c40308607116240315190058995030840740303080990040001404038004ca0000e400c040d00c403604040040b81000c5c1c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 310465404 1250 310464154 310464157
    0xf1f050f0f01110706021b04061d060103331502060103030507150609020c0d030c201c0c0605130c090b010908030c010b01020f0a03090605180d08030618010b 69
    0x1003003801188041d01542007030740b14060074010f206400080c0e8050036201e95009440d0280980b00b020844d080b2051045039282a10403001298107000c4084022000058000d800180040902d414950f84400000c040c4030b1a496040d17404091406e90b0383d8452050313410401d2a065078208246254a00601c2c8201d036800280300381c15030742c241c1015500e5044919040e0103040900381c20240741424103c0020320b00345241c001c3d004030409203081d01d03040c21403d54203e088171b45981c06800051101030320350510003070190b4a00b56001e400c030705640c0c9102c60018490542e030302c1078907207800103214901d190040c082c1c984501a041040381d18040100311282c1c649003040302c028000c002c003050380c641c250322a40e03009064400091003a40f041d241c0314120201124000c0c030310844c2c0701d400360150500d0001440404652040503da00d1740310000c50300d00740141191190041c143c1050000d032092000c0b0704903620540391a9101d0322901d01c85075207240800c28420402c1c40c0c00c030034010755a10280188080c00c100b50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 310466654 1250 310465404 310465429
    0x90506070809210d0f0507091509050d0821011202010f0507020a0e0603010b090c030c07050717060103030f050c120306060405091006022404030c0c05090f1f05 70
    0x1d080200d9445110400d401c002c25629420905810710350100030303103411640a005070344201030040041e001d9031000309099070005c55800b00002c041076424400c20a0f00740307403405614802e18108000c00d4850380842c07a4500030940c10340d0402d001041d02580003004140c105107010001c3ca04000d254907010303181d1b400c02407151000303040c40034ae00030500113135100b2000c5c0c0d052079800400515060382d41708030400303059000350381c0300e4025400c06207080746a00386450700074025596a0740f41c07481c40d0f40e500b6405a1a80055200306c80318050100009006e40099110300e101d0568140500141d52442c58050031401003e0340031400c2c1300007408422400800414842c1000b00b0055a455680d50380b440090301911440e000580c1c000c482d1424401140c00780110b0030b0640f1a04d400b180e010b805005c9461030741580301c00c5100032803606070700003600213841080003080151190040000d103603104d83c00501140700807610f6006d003c1600e07003000313034410480c0c031040402c029504c2c000e0210b9081001007481d4000d1030307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 310467904 1250 310466654 310466657
    0x118050c101e080703060501020d1205040206040e044b15110c060a02030103022d060f070209180703230a050d090b03061c140d020d02060a09050607 65
    0x100100c400360740c01180910344084000809100c0311540c44805071086030192803190000b40350503000701d4607500000f80440c003411507494008800d403101e000000603050040c4126046541400002015500f4640384c038011449041004107284401c0561035826005443e09070086c103050300009201031407c1056012069466004440710185007020302c100314808000e040ca4501c1e100c6000100500600501210f0000170280d6110361240c3d0341500a9000030b01000c3d40c016000300164010100181c00002030788c0012070003080505074840003c240d90800c1008098030b12001600c1c2046240c5082181d40c002c1d104042c0c03444134448040c1442d680d004a01006098030900d006121082800b5804c2c4010000160102c0d0600350840c5401ea4489402090b1178020914814002c551418a00c0c252842a0400f0b44003144074203043c40501e64110340c0314402c2d0303401d060355034103c00c40d544140205116040c02c2d8000b02060050034900070700c1c149004054410051405060780001040441d156400c02e03141e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 310469154 1250 310467904 310467919
    0x3070e040507091e2414040602120d060b040e04110901081e1504030201060e131101141605010204080d020f06070c03120203010303030c030f020703021f020c0109080304050118050c 79
    0xfa00d42c500302885103402185400405c4d801c4002c1c0b290382a0300d10340c000f0b1308603610590307452844000b440160159005000140c0c124030b2490800100ba00301800381065a00404a11940c0c2c5054000c00c6500c48d0f08001e818070054002c000501110003101550b0040645141002c0e615080f011500c500c100310901403100103450040500c28410401031040ca043c0180359a154141854003034002e2101c0d21584485805010000c0c184407440c1030856002030300404603101041900c4011202c034000d00d00004d411120501902000100f142c02407451188036800060707a07a82841c6c1c0342442c0040800004003107501c4135000856140001c1030894101d56542880c08800d07520740303000d40d6204038281010b042c6610101c000010b00d9455004445030302125101002100581100c41c0140d1044101c040c015a01c00490380300340402d0f03041d10001740d0000f0840141011a80520396003504c2d0580303020341d030854003c4288010310500b03200c1d41d011050060b660044800660343d8440e00d400180c00c4072481a06c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 310470404 1250 310469154 310469189
    0x5011806080607021213030b130203010c02060c0702060a090b03070c030206090d050d0507030e0313030303060b1207080702250815060a0303030209010c0602071208010506030912090d051203070e04050709 89
    0x3080e050086c0659400700440507030b40b414241580d074242441000764030a600707000c1010011400072811901640701c003142507250007526000e1102c141d1041c0001c804000c00c8050009004042601642c060f10407a80c4500f180169424008c2c942200542422619000030710004c0c50542c01000300c0d80183c03822315002c2055070780d19105134000d200100e6014018000001c2207070250a89214040641c2e2013620108050f9844104d100118002c00c030b8001200042e04c40841d5505000b040703010381c0200b00703204407204092315554001d05004402000940c0009940041c030181006100380031112708950a01c464a241203c0000c5070070040e84005800d060340081c101d001c030792182c00000c520300d0b08814155039807040d83c0303014011002c1e00f100e00300c00100f00364004101458101c007141e010790320103401010340d5800c4410300c00c0641d00201c002580046907152000000300309200d8291106001c800880d10780c68840c1002d0042140444200e01c00e6162204009503035401081d843c1c140e41002c0400f451068 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 310471654 1250 310470404 310470427
    0x22090608030703231813050c04150822060902030d05040e09030313020d030e060304081b12040510091502030319060503030a08063010060317030601020709050118060806070212 77
    0x10804040041e407e0400007000b0145070490000d00807207041001c511100c10380074108403400b5200703503140b840c010f0401c4a610300300c0f0940814102424002d0100092403070b440c2d40064a051401c2d080d20000c01c1c5c0c0420100107240141048541c4500d03041c001d1851450b00d440c500d040d4150b0400300074443d03a010600c0405240c40f407002c030413001070f02400860b07403810682040c5415130040f0781041c0c4079a00e00c4552407003805011407503184010149034142e040c0307802e20301001403200003540e4400c00c0004c400800112060482e02c500080c407116000b840e0350b410304101c42c030041e1104818408050741045030801c01500c0000407100d010350355240280c22511101c3c00141c03840040300007184030302e100d4181001c03c0c40c00c0046031203c1c2d0b0205002c41341510b031020820010380d0340c103110181c04400c0171a0015010ba171100000c591015052055a20640d283c0b104e80044030b0007a00b00c608503100c801c1c0144040714003442560003030580b24004200510b0b00e41c00080d40c40ca0030440c0c0e000320030780c003003250303031418 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 310472904 1250 310471654 310471669
    0xe011a120a0605040509010c0917120304060605010305091f0c03020f07030f0e120a0f02010c0f032304031101030902010e0d1a010b07020105220906080307032318 71
    0x41200c10040c45142000c100140141029019491140d440c19000c100303069014402c2c6044207010703444050085141401d86281c1c4c00281e0604e5000b4001c100a0310841c10301e50005600c02c5100e1100091f10501741400181250300092480c2115405001c43c2c00120401446d05c95146031800c101003041c55600e00210060b01450308480380354075000c20628109504a5a0850300031010340c0d9036104031039000200b0000d080c8921a001c02500004450700200b140480f45403525801070514050000079551f44000e9070444620a400045801242e01d6500c201e90b044420303c140340c98110360a1a0441e15881108014244400d050581e19202c401c11a406401d070508a42401030034107401012a04024100300800b100b980c000008503c00466581c10440a8410b1181c06944242c2001a510340131040499043c03a90748206d0500940003805912038003483d4081c000c07840280d500c07200d091030040e14501c554110203086103070785407100403065085010750300d40c0e0303039945001500f4041090201c0d90f034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 310474154 1250 310472904 310472917
    0x40b0907030807111c0609050606030c0a090e0a1e03020d05120a0b010210020315040e0d0c08030a0f15060e0a0501140708070506010f05121203060f031603050c10090e011a 75
    0x80550486000d06002c06c950064207114010820b0710850341d1000c0c100341d1210482d90103164484130002d41804204082d502c4400c05c143e00c0360482d0703007460b901c0e02c0b691082d29148040c103052041048000302099814840c1c00c140c41040d0030000d0a02030700307006100404000904001020742c2c0c4032803040b03050b0302c20840c0300f080705a0f410b81190b607420310f000c1e00d40f9801e00d1815402d01480c2003415070040700800103880e034281d035903d6031090a005040d03541e000ca558009041e000c0303003a880780a80f01c0c80684601c00c40032a80750004800c000a850030902400140024540e039210f8089808108400d9030007400c4046d00f100c059464643e21091031400c0c034401d01031050f0180482c03150f000007240050b0840d40c44c80c01d036041140c901c0d541401540e0f00315034480c0c0b002d02c1030410000c06c1c00070030094104640025450750004040d18900d5080c2085648403d4140d4411b80f45a070000100200c282040014908501050710b00402094288a480c40e62644188140c5c0e002c541d03441c0b000e451110001e401d9505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 310475404 1250 310474154 310474189
    0xa0c18090f080c07060c211202122e1716030c0518041a10090203280605060702060a0201061e0305061e162303040b090703080711 57
    0x201e15024180301000b5004000c211035940302d80301020500f10700807922075005a81c01042d503154000650825001e04420078000c00a000c036051035940e2102d8280003a0041c0c0b654050001990f2030001e0694a020b1000c4090300701d1840c50700704440030742d81821388403400d54030f500301403001d250004c0640910304854520740c00e205110031680441040b4400b0aa0411160b04861100c000710309140c0e5021015000d440041c045590070548a040401c0f0b0402d0550158082510340d452a550b80c04484c1613910031520502542d4902440a800e564400c101520340d03180e44901300700b02400c06002c45d80350301c00c0c010041e02c00da03000310b000894a8401d400440140c10182407407803880c0400308e401d10304140740d030108039494081d280004036190184038a4441000c040c00c2101c109490f80c1c03040b911458612807a100812030320f0080b041306070540e000c001d00201404c2141903079a140034140410340c02000b419075503107600910810400b1401d0101982c003503c0d08242001c121040c04c80010301c080e0701107181c0c0314 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 310476654 1250 310475404 310475423
    0xf030e1203030906010b121f0e19050c0c030405010302030408070c15022a060c100e0a02030c0d0b0612010608010c080604140c032703180109080a0c1809 67
    0x654104010028600031030f001c0d01240d1003640c1b0340d6a841c1440c0070340c5c1c880c44101c8510314000790700300c5c0c1240ca100c004010101e4810581c00d03120309003483c00341000c4600312180819401c030f90103000d00c103120345a44602c007014402d0402111103134203502c9200f1840b440d0304060f00400800d086c800c49000701c55090381d021003c4d1103802d42c1c40d01120088403039a075102c1d0160092142421440300c0e052541101c02804003080841c1069500030420117411181d0789402500c07410400c400c503c10f040c0705800010169000800e03842015104052500c45d841c202c00340070385900f03c802d80024103c120050f81003103048403201200200a8000c500410150b441060340d5801d0244016038160402200c1c1d004040688061002c030417060700038800c2d58000e07184191407000402c001a03800b001e400c60120312140c0400c021544055440e0420314582160811a00e01d0b2031401c400356666030045014401020590003409404025803503800d901c84041c03140042990036258890b07400e24a65018801569018140c5c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 310477904 1250 310476654 310476679
    0x12021603030c0f0504080a0303020d09060504061a0102011e09030c120e0a05041e020a1107030c0e1f03200d030905120f0c0409020f030709020a140301120f030e 70
    0x10003628200480001080f8440507480c2d14501c00c1381103070f007074031580310040c8030f49080c0e90b0b001c0f0004d510807041000400c0ea11044000051445d00035680078038050341000c01c800388050100c140302c011000d015419a0b14000c00c120704c071100d03010700c1110703992051000503243e601401c0a0343d84482d004802084a00161165540705800817040d40c80c551041e21501c3c3c0140d250800d000c219108541c000907010b403001105464188260000e0a072400c1c6450440d84000301c51801514220300f03604111050b19007060140a541d1a4603812075118540b40820700c0592140e016011400e040707030102a01400c0b40074103601c65026901c442c1104200090141c05031080e80b401c00400001250041a00c500e46a000095000078009101c8c26654445000f5010380071800d400c01c0028104082d04030380108402d0040c2041d41d401f80000030040440c0500035031340b40b8101500800000d40301d50101d202007028401440000b010507402c80b1030a03032100c0b10b80c030b2402207030030141c403c0040e00c051143c2c08205602c15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 310479154 1250 310477904 310477907
    0x60b0f1009030b090c030313062006040b10051503040506070305060a120221060a0b10020c042004060c0506010f0e060904051002040b04090f0b0f150913090b0603070305060712021603 80
    0xaa600700c41743c65a802030f162b544c1d648451070300019943ca0a44691001c00480c020030005140d0342c0d0001554055024100c1e07580b000b0a401d4034091120070040b40d000f10420041c4281445050744c011040d00e0100070510306000041d01d003c1450007140d8800d092480200d0464441604010403501e0ba0365040c12840303403200740641d940908807410040d0a0501001c40f8039400c1181c1d060071801c0319500a8011528103034107200082120300c0d0140c1c1c0001e4490802c00d01c8008410003000074007420f54590140710a42d00300a4980403040e404040c1030b402c07145042221804265280ea040365080314804029203590a0180c0f40c201c0d029050000580b00140019030800100300602c22980c5000d018486100b80943d10710460b00010341007900056880c507041d22038070344010020542c841101c4418202a030000c003240000403909490407005a8404030f0703401380481852079960000b8120b0003040d115046d5030703440d510381001402c00c1040c840c10b0012100024510b8054032400000c00e6019110221a17080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 310480404 1250 310479154 310479187
    0x311011806052508060f060f040b0403030809030408070324052a132c070804020a08031e09030f0312150d03050f030c07020904060b0f1009030b090c0303 67
    0x201107400450444942003c1058140c40c0b8056154540350011155100c405002d01c044521403003950240d401c01c80c0c0319a591211000d403000d800510f100c02d80741e03030841c038004d400c40380064402032440d8000c0c082000084800603020041d6a4001e0f080580307800c040c3c404031158420340e40071f007070034038101010800c0c01030001a0b44d0144016405801c2190106815840300700e119480c0104440321610f4000d0100b5035440d000310250340002580f01c18100d41d5016046030101085e11060001280d5000788010741c90440c04d054058000c0d24051464444503104041c40040c44020a83d403005020403034001aa0341405041c05c1c40d48003105517591184101030030075451104684203244400b0800300a2464102000201c604642c1920303901e24159060110b42001d410080c88248228030410254006846030100c20b4082c41c49440c02003514400f031410440608032141d20300b030094120a00e0301c02041d84c003c85c158112500078095900700d40310070b902d090a100c07040440f03e4140c400014400a540001b06c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 310481654 1250 310480404 310480411
    0x2060904090b13170a1d010c080d0f0b0405150d02040216050c12120706051b0705010f05010501030c0e06030a090602070c06020d0203090d0b070e0a08010e070b03060d031101180605 79
    0x1560005201042042c0c2c4c0640c042c1c00183c1c030000d601c49800f6540a64062244521050141000e02c05010316681d1031545510442c0e09400c195210700700c4110032003003030003032a034110400c076170521135071504942d10807000e410000700030702c2200343e20031810654540354101c0300390030086c441d0902022464140160b03981b00080059000d1489205c040600042c04120a202c14a107580c00b1803400015803100e10107044013601c00d6000c1c00d00780e143d60700a880e0340c0005082c2144900c002142d1003d020110b613080701ea050340014181824641c204500343e0740030b0f290a40420381240c0250700c94440d644094010446007070b00801c4030340f0025901050111081d15901120902d42c202d0302c2580e070700c0d11b00320703200d000f0040729a41003005d0b552443c2c00645946003050b4801d480d8030741540c01881001c00a004a4031a502c5407007265900e0b0b400c0140c4c500b05120180240541050703091541c1815004900503007036130311018040200e924182e264000e030a40040c10500c030035101601c440c2c9403904102c00180b0b020b6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 310482904 1250 310481654 310481663
    0x90c09090c09050603060601050310051011061605030c0c0715031e0204270e060c13090504020f0123070c05090a181704080a050610051c02060904090b13 67
    0x741e000800d4103641c01150320030301029002d0401e94540700015030f4a500058911160503c01075404100c40d111803d0280c2a0380f03599441460103503000c403542c0d08024000c0d00d01d2403412042c1c20014076280d0030004980c3c2020040c4aa10359803c28110750310300b001800c0d005800281109507950b00030303960507005004065901144c55001e20f9030090008101d102d244030715808140d0320040031702c1c00c500080c884410010400e41c003044140c6a50801800d2a00480327040c00d50020104040900441c224400009005050720820241c1025000508a40001088541042018002d09054035554080b41c581c100c1d00501e115120803051a080009282c10b014240c00744401c0301c00a940714280d4058080d504441c03181e0b22880507065154001035000500ca0380140c00d208200010701c0c018100501b86000c2e001e280a08110304080b1070880c1c1e80c00895010600c03505000c15110584c01c040301d104028a6030403140345a9034280d90002ca400307002c42c480040c0004980340e042107080c1c840203030401c6e802c5104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 310484154 1250 310482904 310482923
    0x1012141801150e060105031302130504150606050d0c0315060509030606010c0308060904031b0609050c0306101e0513090c091b031e0510030308060a0b0d0f090c0909 72
    0x109600c2c0032600c1518410200203201440101c0c5076940204000c54109041001c0d0f4100d81c0726a4007c42e40c1000a442c60a0b036065171041000280010146d090019010140c4288403491a02e80c0040c030700c2c007802c1034030b1001e6035580e0b071025011070281d070162480c0041005100304c2582e403514007500343e420141d0100d019004820020712150f208041c2c80a9080d41f5480b9141941c8918042c80024040103004909001b00c02d60300d02984692a008118038034410078012500a99502c0c0c010b042000c0d031107895000350b2060040c064600750640558040e144a5000d80120030202400d591030140694426504900c0d44801481000d1068002d0b0060500480e0403521483c1d0b5103510b04c04480b002030440a442e403440d0740f44840140700350011340039420411258a02da4904501e95012200241c4602303444107050075080003050b030025107141c0d00500c03c9490301c3c0c0c02c524048552083d4412000071200c01603841c0f00003400d0340110340c0b0504850703400070740346074440e61100642e070020001080c3c140e03510040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 310485404 1250 310484154 310484171
    0x806280507120b030a050303100f0824092103070201051008100e0102090402030a06181104090e15161407050c06090a120804050f01030b1012141801 65
    0x58602419024030803603524000030502c14200240188503140b8401d525001d8a499000410020400385010701c007401f0fa403140c02882d042604a00755401d42c000308072504012821852080d003610542c1c08644e20070060300300e5907070300324005040c00408681e10350302c9044481040000d6108102662241c02d40ea0000c1000f82c0b210070700c000704c800103803140c0c20f0b40703500c58100e048000d0307030700c0d00000b0a500c21200050305007020040014141c1c0c008070f9000990315601d0400704003c502a20305905002241e010402c488000b60480d500184218041c1801a41d02c842d000f203100d9000704090301c40300300d440d034001141d03050001c002d600b03807035501408000103680686c0d06c48032040203004403001c05a20200618049000c58188081904501d1110b94005002080058024103043e4440b0107030344582d04440e030780d07414401000b04000304402564101482c0c000f0001113601c8186c1250756004e4681400303540c100598a585000e4490b800c2c86a0078490610180a24040000d031821000520322000b405202e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 310486654 1250 310485404 310485481
    0x10e030a120b0d1212060b1201050109120f0807060207300c1b1203030e120313020904060216030305160f0504090e07050402030103120314010b12060301060806 70
    0x1080800c110b507009038106100310009860102c03513504042d050500d828050046111402241c50982c481000040d00244030b445401c4c01e010300a001d01400d080c0381440d9800e14906581d104010000180080d10700c01041040c0702d1030301c0a4944090744010107558902e5245040e044202c0d1317041140348410901c5091102108205640322001110f6988030310201d03d003501d440c01c40c406403205001e4580b610400202e901d08030f1022906582c0e000e504d02085000c801714415241c03001201d0388141016041c0705000d0450741d90941c0842040e0102c030701f648135880d103042240c000d01c1480b03004100d0760300420402c800c142d05038114a01c074120441079200400e492002c01e854035944401004d000034800c001c240000c0d06250300450f840e061140441d444940c07202c002c20304030380c002c1c3c005031640355030790110304c5141c2d5244c0a445002e42e015407065005514200d045003a0740142143d07449080c00745000500c10391001d600034001007010004645143c20a51a141c014120344110744516821070850311001c2e1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 310487904 1250 310486654 310486661
    0x60506030f25050a0b0a080108190308041721061525020d20040c091412161701020306010918021c050610030603020906120f010e030a12 60
    0x901072203018220940034200c031100810442904a01c1148000201103803030740b1984220b030058500c1040d0ba95813056082c0d4041c0607618144c1c40024607510070840000d018a502c014000160f0b4035091110140e1a1031071306050000c210301c1c40086480740849d590450040302d000d5030f45c00003115151094141c458900740107020f50041c4a00b054030008100c05e0400c240a03150485655a12403000300640031654001b842075903425001f564003814042032010240140000041545800c842c100031500c0201005800e005961040e54000c00040c41b04800c1520781060254020b01150140c0c3c424001a000040c06440207000c1d042e120310080fa4021500c0301c05100301c9010340c00c16195025001d11340094080003050300b41c44802d60b0b5800f44980c0d1861100485220910540d10001140314940301003132040d41c01c044681103007090b0414800b000035032a00801c054202c00296049210007c001100d42d207030038032852a00410707603e4030030320252101c00440540b441300c0340c6603104110b1881e8050044280c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 310489154 1250 310487904 310487923
    0xa14042301060506180a03080c06010f0608040b0a02130914040309050a1805042405010302030c041109060d0e0708010b01031b0f0e1f02100e010c0903060e10051306050603 75
    0x110408206181d0350340c400d1740c1c4204091000030603038140c03507840f5a14080703603401080c03c04281d030307210384010300007450081d50450217440280707003680e174a03e41910341c00505900a40341c0c9003003682c0040c070300c01c0264120740414043c1006403c18407007c02c0d17017180c0c032441c078004503415000101110000700e200d241170f00d0140200d450720310403110210647d403210401084050011940c4840c0f02c40c1690001d48841c180303802c100e0b88100006055071440c01450b080500030800380f4031a030b2400200b040c13094244003d40710040019034001d502d94134030b000785038010101000d072010a40b041d00310014091405401240e50070381c1c01e0340c0600000c8201808020365840c9a41c884000c1004040cae81845144528010070600500400d014031704551048004460156421802c005030401028094404d02c580901c50100440740c1c001c101c0f40c0d2800000070305017421404014015900c440340000c142508100c42510003003004001c0080f0309111000301840440d01e4000c07a100e81c20003002401a181c0410345188 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 310490404 1250 310489154 310489159
    0xe01330b040b1804090c0e0f01050405071d0a03020a080601150c030c150b04050703020d1802010c0f050f011107050c0f220609321005090a140423010605 67
    0x18020316120101403004400010f03504140c3d61102807000c110301040c001c0003440d1407140b260031800c0500c0040d100150503000180224200810312608070380c00847c4030307a02d48031004c4c0c42803041402c000140ea0b44045a1000c4e40c082852000810350f00b001080c550f0403200004030764103076035548000542e9140c013048070103004030708915810004628031a0000086812102000070444e002c000002e04452007a10440300095000c119000540010f1003400d21021800400b503c404d81d0550009094103a148002006410044c101c181044001c004040c0540b500400070b014148400d0710000745170b0071200c410f491038403424050381d03907500740b0202890f000c200140020f5162080d40d08000c12210301c091058000c259541400078401100d031140e61410700031031034010301c1410101417460148419005100301c410709a000e122000160450400c1100c0003030b58411040e5507081c0c00340004000400e00c010119510008002c02c1200020f6a0b47d0301140810b10001902e01015007030b42268140e0081d10b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 310491654 1250 310490404 310490407
    0x70f09090b061c0204050a0504050114151c090308070c0b06010809122706030f0106030504032c131404020d020d020a0b030402030d0806030a060e01330b040b 69
    0x55a596000700e040000094070061800081e07020954407107100900407104154003140030b10051501018140c01014204c40911140d41004140340c83e0701c04140340507200d8440030480501c0c60365414245c0d0100302c1248905070b058095031100b03101820400400b140011091000a44610b020b10950018582c0021840c50350b6a2124015100d001c0d01a104203e5441040041c81060803400b0040841e5040780e90080e0303004080c1c42d80d485c0002c10b40302805200d81000e0040101158144c484681150400e180200f01600c450500f40c41c00030716418054426141d2500d900a0101100b80c60b43c1c079540c05032002000908000740c800c046a03d800d111103250042c240125001d40b90080c8038080c214001807a1402c03070941a40024644d14882d030240c40b03403580100801c010351505000070070034108542051410340c5000340000307844100e00c05004220950f00d0310025580701c805d50240c0400c02c3c801130341610100120314207020f183d00d4002406a03500f000b140c0070500c4180003099400707c03a040e40d07640303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 310492904 1250 310491654 310491659
    0x40b01111e0c101101110f0d020a0e0d080703080903090102071701020408061906080102070804030b15090a0906200909072d0e10080c211509070f09 65
    0x5040c218000c0419007080c451038001010a645620120031607a03141e0b202c4480c01055000ca030360940c0c0f0b43d030128402d0100180700c1c01c080c001c02241103800780d9816600c016600c1229103030684507118403020b801c0c1c1200460300c400c410007180c0801400428000e03200c42903c2d80c0d44200d116660f1040e00da0403401a0462001040541c41d01c41c1c034501c07103607003a2002506103071300d600840c3d10b4524200e400500b680c500403141c07090f17120140f24000c00388c4640d00007035207001e0641e2140c4c0c1c02c0e8400d81c0320040c0540075001c00a016103001c07004071910b05000030044c040d02e04140b0149000780024482c241ca6140c039012043c04485a101c40d07a105c0348180e4101030b0300b0f000e881d404120100e4002040e03041801402010140880c1d04481485112844500030030040c100f0320800400d0809404140c1d401500041090b01c079140c0c00484066200040c0c04d490340d07507000845200204d00d5040e405615608054800303120f424444100c0808100d5000c0d2401c0603190385000046031300c444003071030720b0001c108000d070b05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 310494154 1250 310492904 310492933
    0xb150a17030712080103170c06010506210f1f1d040302030c1519020a0915020a0803040605161b0b060a03050604120f1805060a0e061305040b0111 64
    0x280303002040d020041c1c9050100584429400000e01001c94001488010041c410064441304000001c0b9000103030900b021500c100c402d5032400e040c0643c620030030001c181d600380d4007142c44c40c030340c5c03413086401c5401c2c00e50070404005441d8031026900d14803c160740512040301c80000f80b8610303040700d544882c60103034484407030310320800350340d010304280c046010820a00620840401c580c1c0100018030038440c24030725002c8900411b098103c00e00007a220b00400c03485a01d10b0f4094118410b40308124040100c106401009030319280d5500c00c01082414080300f0032041c40500e40c442840b03000304001d456001c00a440c812500300c0c071070790f0b0503041303900c0444542404281d00b4481182c0c041005014241c642e5240d40380c0354604401241c089400845140c02c40c11400da008a00103202c07012420180d000309103012000c940e40103240a0b5a020b41004078220400074400c0310000c05856025115a581e100720b03481040d5800168081c030350013981040141c00c002d502c0380c600f881c1d4003e10103029202c1c01140460 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 310495404 1250 310494154 310494179
    0xb16140301052b39090902060f070f0b0c0c460c050105160f061103160207230d11120709060f1202090a06031b0303090509040305030c1b010c0c0b150a 66
    0x801fa604031105104003108041c0c0c6000401d02310b8052908035403121203610304901500c40c01011410305039001d112070500c25600142403504000000040c00d00716074800000042042d0000c4030710101070b241c02c0080100026a8070781a1001c0c0190311500c501034403203005403058469006003181d0346c8032050780c94011400f0740103150040391207080c02040d400a10301e07200345150400d541444404024940c2c082c929030301000484020200100c0c40b1a0b0300e10842c41d010814506086014007c80056136958200546075405081040009141c600c05040d00300c80380d03641e9100c0d03000b2040a140b80241c04220904444051001c40701c0041c84c0c3e5180c00b095500b48216181e016241c546556191003021000030020300b038910190742c4250b82c110f5024a10708004004104580c002400b800340d540a00020a0748101140da210314504c04090791100050301c030142c0c1125058980303080d5441d001041c0f01069000907449141d5005119000103a10740818480c40c2203c4074002d15030002030840200041c1d00c40c2c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 310496654 1250 310495404 310495421
    0x10801140121061a0f040b10030f0e0601060207060f110a06020f0705060c19050412060b010c0b010803030a051807050919090b16140301052b3909 64
    0x100149082e49079940384001d403240c1800e01c418400414428003078a043c850452035840c94110b40520030386201c64003240010074449446820940c940c030000005402c241c1100d480c3c652a04100c03101341d030395200e001751501d860b402011700045010800c0310b10395100d480003000c0d1241c5c1c440504240d2101c0d0f500c400095106c20030071210024248810408244103104441c4030302414480203965541c4402c450074541e10011801007030002c14003080c008440031074145a161130f403100002401c0514480141d40640ea00c12000340065001070002ca010304000c0003444c007400300c3c00d0091100b52295442215140c1070b8490501440c0d001b00e8041040c0d1608280300b07034200c448001d044030301980d40031451050350f58801c0c055502402843c284083c144502c20020000ca2192030544a240403403110701c0003510062045610a80c03043c600c2120303206a216040346800d208001c0ca0000c400940b502000c03c0340c5407c202114080c040e0f08001d80c0e0042c044e40815071800f0100c101a090381895010720040442c0b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 310497904 1250 310496654 310496699
    0xc06030c0504081c120c020109110604080a060504020415060c020102010c09080607030f180812010f051e030304211205040810050a0e070e09010c18060c1401051303080108011401 78
    0x151045e401c3c807404c1c0b048204c200110350001c100170341e042c140403c1140315101114010340303040000304001a40444d9035918268003030404103d60720703107000290192184040a40800150510001c0c80c95084450560000e1007a0000d11072000000781c01e03143e507881440344041940241c000200a188a640445180c0914a078001061000c0000142d05000514801c9828082c00241d00070141c8065410390b004040704200d0848490501c0089081418840c2100a849200d07028410f815642481920040c00720204d00f403071100a00036078000c5003042c115095507284401140c4603030041c414400c50381500e103210010900d0090340c01c3d0303c1e001880c005228a81d400d66442e00a080d81605101c201c00400c90340f00d00000900b0a2401e9500f1102207102da08141304c9506040c0d080c00c0003030080031080ba00c1500748038940ba48941071211206024160184255290200b0045400e21138203174020554000d5461110300c1c0c0c0c0390030041d8200c2c5d032035030800301c20003200c0350040010071006c44000c198101c44 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 310499154 1250 310497904 310497917
    0xb06010f030f1121100b0706091203051509060f0d030905060f030919020d0f061401090606090b0313020904050f0604030509040b241b03070c06030c0504081c 69
    0x4810780300b2180c0650b1840004000011403003d100c413284403000d03115124407401c40403801c0014074410fa155031441408505400400e01d5810b01500380d102880c3c0c2c0e5000050420304c001002002070040c04106d41c1c21410043d911141c500341e080c0314602d00d200d0000078224148181c5900c0c20002d4110051f98220200003690301c0c041110b885944c042c041c050b000e6200c01d81c4a0400e5040d1751304144010802c0e2403405181c904203400350ba00c5140746040d0302d400c417501034003801203801c222001c1e210707640d1442c1c60444031000000f13030100c0591220044071440ea442e5240c642c0c0394503910103903200c1a241400310318200050171f009031406603045600702c3d00c0b41e41159400d441800307606003441c0c0304490690110f4070200d149401414680a18984040100c07034400320b800c45000018404450280c030a6140040400c0300c0240c51010102c4846007241d007422207848040c40d1070032603c080c00034041e00300080c2c01c1c00c0150b08100d000d6025102501c1d1180040d120210040c24081c08a034100581d40007008403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 310500404 1250 310499154 310499171
    0x80402012f0a02010801050d08040e0406020408010e0703051605010905062104050a1e02010503070e0105090d05061609032d082a1b0f0a031202100b0d0b06010f03 71
    0x1107281800d4500504007a100c0d00550380005007a29070164041c0d40210912011040040c503e030f412602038803002140504140c60b1810064000d01541e04600c10541c0380c014428000a0b0000e40d41c0e084a1059088030880c110180800308190300301d20855010072032942c0c0900c00c5140c206c000d0b01603401c40c2d004d0f80ba03038411200c1c00d10600070b03030580f41038501ba00113039100824880100248010f141300584c0c0408440d229070700007000381c071000f000d00c010004444401800c82c1e00c1032013110a003c00040850101c80e0103418502d85a010503240b402c070030481c41c146600c1325405281c0c4078044a0b0811483d0003d591195251174003e040c180b501c07501e00c00e801c0c000100188426000c0c08407580f0291880310074615865816039800d0300001c0c003a80300e070702030521600c8080950013981d40550301503601c407500c00038110108800b00b81580005000032182d00c2040c44d80c0d50b000a04200d101843c06041c032a03c10844140190310031108030150100f035030390000591035401148910500700e440d14002070180c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 310501654 1250 310500404 310500467
    0x2c1005071401151514161109070302180a0b040308072a061b0c170f01020d1b230702120709020d0c0512040b0702100e0102041d0708040201 61
    0x7550700c0800340203410500010f0010080344d05020918040c0742c2000780820598103564000c03130041c840540c180000c0d1140b081c080012102080e101c00c400501030044034100000098040d40180c0c0c00c0741170f03c0591588c070001c1c62030325605500c00c950031034450b10324160860300c54078101da02601040d00c2d1104010103c2c00d0450711a100100d1004d000c2c0c80550300b0350f0a141d0010104400890880c0d26860035240e0100171078000900300f4100c1d43e10f2024030b804002141001c03820107840d4280c40d091548081060300e14280250000031840381941000c51100c00d150405607610b40c07401c03034404144c00d80c02c16501e00b40421a0020420540024800324081c80d403412a94680280c980010702c00c103170080b81d0786008040500600a045240d03080080c2030034001c0e4207005980070010409080e0003503810108400d40c0c0240030941024600380000e0050112f03448206020358080d1040d02c02c0021490039901404c0c0011801b1401540a40c2d075424280d15560011524000000e041c228802d03e094241c20384032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 310502904 1250 310501654 310501661
    0xc011e0c030b0f1203160309150521100b0f0406030501050a081f09080c0d1b0f0209060105160f050705041a09071103070605060f030a0f12031404032c1005071401 71
    0x1648a80c0d00e039080d00d270070f01c0b000c000d01c12070030007166041c07010510181d0500c60812940782c1c646012030080503615960040e442c500956680e01c030302102600090070300c48203100400104141c3d24952014880d42c0d0380c84003405210038940c850300105421402440202e007143e020302100d01c20811001040e440102d1b00c1740c0c0c513180d111400d030301c2c0c0c03e6000030100c40d181500f00211890590300355038940514034183c2c9800c07950050b5104000e04c00c07609000010103503800341d81074a02c00e01f41403964116000f410318140c87d41c404007540640300e521422100090a282034042d06502000f40040c04125015050a1100111001d0003d005002c1d840d510314030340c507600700060099103008110210741414140c0c24403103c0246180e40390300a030042904e07134012030760415406140c0c95000100001c400444070044000f003030403c602c000408900c400344014036500c070a00ba4403581d2200d4028402101e16400002081c410034801508412540703001000540180050300400e8020b103a040d00050f0545422800c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 310504154 1250 310502904 310502947
    0x3110603190b0123030702010e1b0f1c05030703030509030918060109080d0f0e0307150f0507170a0e0906031b06130801060f0e04031b080c011e0c030b0f1203 69
    0x42c1c0c135000c010010000d50900415558400320405007840c1e071156503103020580030a800d030a00a404544217040592240d189015100000304003081001d512841c00c02c0d202da000303113020b4001034205008034503c1c03036010003180c2003c000203002c2d0303030540e1164103400340091000b40b030705050268110001502c3c28081c80354443c0c400781540d400c5082d003261080580100b541c407003918000c1c0e101d00d000703000d44400c400100405400c0c5081c8004440c1984008640324403038180c008100310407590613400008400c1000d0004171815482e100d00d260551000d01c103166008681681d4107600c1a2090140405064140880d0b903101034003481c0782400041461035103840e80d600030a4180e42d43c40040256407140718400d000f9014280c3d02c90420704140e2030042820b8a0114080310800b410140401005843c1702140d090b03500c80d9000b40890964103500f00301c1404142004649075007080c050291507403181c4900380c00400014000302802c400c80050007810181c011002c0850700c000c200601c42542c01f6565080c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 310505404 1250 310504154 310504217
    0x10e040e060604110906041703040b2106091317070f0b1b07030f03050a020405130f1d070308090604030f0803040201021006051e0a090c03050103110603190b01 70
    0x2281c2040824881200d8265444c1019620180000042a0f4400c004c942c100e40c1194000c00c450708611414900f544116070003000d40d8070000440003d81041950070041012024481007142d540d00024490780e900100d4200e40752000e8000e02c0030001d01c1c050900403401441c4050b55040c554180c1d66048021180e0b0800d449070080c560030407840d1600611030781950190803401a08004c6a41d074083e000e444540340310b005041c1c940001070b4181101d40d05840040500505000c1d0701e00304c114801e0024404d040c1e007131070b4040c248400c0c001c911007000004a020291034009004240c69038803102c000e50441c48100398010310801c00000810002017035441d2150055003025507a0416200181c90070011140060115041c00010007a85e0b54000c1940442120014503259044a840c00180362540c1c94128101e52460590b212112a40c903900490681c1d20441009115042d4103040096a010440325036403007000d244600e9030002c500340c11002c00c128040c10a40c0c0406001c60752804284c011401881c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 310506654 1250 310505404 310505413
    0xf200604080601091b0210050402062a1e12090d0605010f1707061e0c0c06030b3a060f0507030f1a060d020c0c03030a27050904020906010e040e 63
    0x2005102e6845816054085c000c6421a03c103040d0b1030180d25540c259403444001681c5d140000c0035526102c3c00c40c2c030805842e100c00c2d0b990036800015907201030302c0030303c9100b10351041c520b0820131554140c040b207400c1e42c1140024689404020a100580c1d0700001040c1d82112100451000080c40ca01a0307902914a44641c6040c207414101400f8000c01a00000003050788030034803c00910740c01480c040c6501210140d64407030201072090a8451142020000f400050305450000d000c81d4581e010204031030044500f00841050102c0030a50818a000e44401141d0311452098210780b042890700a09440360002050300d8203074503010070881d50304440c0c000120ba11040f0b2400f124040d44644c01842c2c803223002074002851480c003c80c00500175920481c0c000742e0300003810b01c030603003003081800a1000000e080340c1d03503444c1c090b200a180c1c0801d9601440070408103000c14065000402440040e03500261411605a640d50204110300f0400341c0f0041c140091100c0c21030382c40c2c4403401981042c40305500280b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 310507904 1250 310506654 310506659
    0x708031308060703140c0a0302090d05010b01020709111204020a080d0e01110f06010e0628080d020f0d0f0c0609031805010f02103c06120f200604080601 67
    0xd800c02d500203200328100351404d0648000c3c40c0d01507440d07540101c1d140c069581c443c960642c00303600038420a030055510a03500502d140400c18150000342c41032800781c1c26514003a036211b440038165810b1010799403400d1000e0085200324a03a50b158654824002031051001541d6480d181e824400030704d04550000b00030034664080d55820900d104080351400d001008911070b50030b1002d45498040c004c0e20004003000c40800d1031541c0d84031102d11b0341c06c404a683d08081000380824402050b0078071400c3d03041d004909952400078000310f044912010308c40082c040e00d020044049814140c2222f81c1c50910903008075200104443e481307022003040c403a49421082a0003011441d480e4070680d48614100000b88011072480c0c3e0340440e1241c40643d1001000c00d91000807200403004051014010501000c6c00c103142c86e0003802d541c245041103d0b4030f00c00b040103c0e01e0708014100c04c0c100120182c540c04124940c540081e1140c0c40000d0b56a90003403a190702401e40710300048039076200da80100300942c002d0300103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 310509154 1250 310507904 310507919
    0x10c211b05030a031d0a02130b0301020408010b03010509060106080408030a02070830070903080c15070512150604061214090f060606120c1308030307030509060f0906011707080313 79
    0x60480c642445c0c09021403640110100035903480307401400a01400d0300c506810b1800f6130582129030003510040081d0340703c94030703202c03064028010100360508c00c3d82444003103030343c0010124505041c0c814903669580940c0e6030741ca51b040c039940b01a007100c1802d03070f081242c0e0000c142520702518442071130250078441400d4a0044014120403d111144488440340a01c0300c1150000a20000c1365484060b09840c0d520f461007807801c00d50b858480c0c65441000400b0031840660000040082580e03c043d8032103a9101c029909418000b9207080c103800170400c0009000300e500840d50050450108100403444412903016110101c00544110040d5801071601c102e6154041c00415406141038500b5810507008220b84544000050030000e005000062402d222482080500f009804602c049036503070708100e2001001040c04881215042c01098080b4420f01c51541d0b9050090070580001c0c0841d03400e145a0111406d07509420b600c0303510600d80e00190002003800500701030b211841009205600e807442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 310510404 1250 310509154 310509161
    0x4030e010207060503150123071403030105010e090c072117160c0c03051207060501082d0f0a060525090308090d1e020f010c211b05030a03 61
    0x400e055400080c0d05005940d440302c290395000c00c10180c0704001c50400d038010707600490380404400341076840604004c00001c1160080402c1d80c0300d4484062564020700c4440d80740c0c0030a000c0c0f240081d0100005000d24a00889a103401c818032180940c41e0001c2e603a207114400f60303803201401100e60407010b00b6003101d4010700c510a034007007003030b40020700b81c07600d42400c138060390501c80d01f1070038098501703000014408810041c2c400f956102040340c8148a000c1031040058002c590111003117801c143c004540c12001007600c40740410b40c0e214150a0703556459420044004802400605219600801030507075000c02005a0081c0540e80025060900b1098111805e1240d420a619807a8410f0368001c415071140a0804594100145035110740840c000100d5102c0f94250240140d007038008407640340800740e003c00301903600c2150070100f024030600054a150400c00c0010306180340796407202d25099958031551113485201e1900028090010010780544000050240c4040e80041000c00c0300039058030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 310511654 1250 310510404 310510427
    0x20d06090e0a14010c0c02090a140106020109121707121e02130f15081509150a050901060e04020d02091002030316140d020c01060317090301050f0609070c0510090b0403 74
    0x24020321085c502e503000502400da82d140028014082d82c0000b8450000301d13404000c1da0faa2a00c51a001c6503980d04c0001d0103400d511600b50307860f8029051860b41c0c18003600004114014050317000102d5a102041171303440c0114a400808003a071240e40000800010414a05a40303402a60041e00c54801c1150503007540c02c560020742070355141000a02c04526010106111004a803030000b0b07140e07960f449070705c2c50084201d03401600f00c242141440303000c00301c1100f0049242e0040c0c41d24881282c0c0c9504001d2112020307c914004203005440800c100d0130150000c1c0010040c41c0b90140c81c14100d10702040104000c204c601c40103810200c140200e004004e02c1c030403140c03002d42c688011000018501c081c00c907c2050354102003075500144401e0a01000e40108001b15000002c1041060503000f010302168060001e00313119500c0c01001031444020004428001c000181800c820359441c45070559a0710f00704101620907202d50000b003000d2203c0740c0244825980704484131450340c281b61401908400e0900d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 310512904 1250 310511654 310511693
    0x70e060313150f3c020c15180705011b0f0506040f1407050906040228180b07200607140c1804050d2604050303150d1104020d06090e0a 59
    0x107550b04070030309080c0c1c44042007031480314001380f41d411495881c00700284109030211500e4000d902040c6150340528400d01c2c401c0d0000c080840007a01c0010841d9220070140c010540854020701402041d440000594401148a0413013a080d101d07858036100d11b8504200d40031140030460070100f90800900404441100800da4000c09625040c440040c0b403400004101502403a40880c4c1e0b40401c045d0311030408161510902c102c103d40d9a0468000c184840388401858032840215001030300088240859200316042403c0520303a0401a01e2801a801c2c0b050303c0320b0b403000b07050280d840480d0406070040f51101c2c0440060202c2c01218041c0b240340c14102c0b40303101d10300c0301e00000c01021940100c0c1e80c880a01103490002e01c0000c0c107128a8208803030f41030054641c4a1040100002c00000000450041e80d068141307401c0e849a05c42000101d80c55484c0003859900c141d14001460705143d005810580404500805d0594407071144908507404000207007500c0c1d0109450ba0b083c0040c0425040306003140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 310514154 1250 310512904 310512941
    0x110c0601030c06022e0623100f051606111b120403031205040203010e1209040b120a060203150d030507020f042702032404030806030303070e060313150f 67
    0x3d4a02032050544c80e61340b103090380480c1da18a101c0c643c606512110240050b01095100d8411030101c2c0181d000080d4800390194185440307050380240134181c02d0303001d04014ac1c0c0b01441d040d0880308a01c0d01c01c01281c001c5a20710340710b80b020007a403100c03900600390114002c100001810450340304245041d801c242c0e07062244008003c140f001c83c2d0f0081c0c08054100301e0190105d01d41c4c0f140d10101c5d0040164401503151401400440310aa070503007001805000300460702440442c60800802c0301c1150500720060a40c0d104440700800185c568000d0b6074000c07039150b04200401c41c482c000c214607a104034002c60009030000303241c400b14a4100b071561300d02d0f0790030b83c0d00b04100058421a201004141d42280710300400055100c0119a000c210807005002e0001d280c61500c0d200b4104600600d2003964203c0100344403000194060134004107417441f8140594a003003500d01a00144840c82d88050810035800041d18401000304020a001c403203034116480001568108a041a404440100c0300010b4080507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 310515404 1250 310514154 310514173
    0x411072409050313140a06030b0a091a0a14010c26040626010303020c120705060f090a06030509060412111218010c0b0402040203060a030c0603050114060a020d1101110c0601030c0602 80
    0x640351b65210660300c8604000038801b01510010300311a080f42d110034078148c20086400c000d000c2c166080c01002c00203440580300c0c0c40e1a80b000c240c1050580c403500d400078540d01000008200c01004000c02008403a10242c943d8880c6d01d142c0b42c2503405600078101040640041d03100c40c1c1c06100020b004c01810381d41292042d410741d0b50003920b4000b035440c1c451150304c072850944080c480c140003c5005203001461a03a0300c0901028204407504000320943c03007144500400128107002c3c0c01010710420714580605842c0d51540d650b0b400317006c150412002000440c03160581c0d0608100861428000701002642c0c03641494441c03001107900980e40c070f40c100700c50141032030006564a0800703900540e04484c0941c89541315400304000d0601948040d2803404040b50004455406501c802d050f03484800017a419100c4000902c519071051480e07107801640b000c407000d09914405c10551001307400c07090010546844480c2d68105a4101c881402c44540010b00104100b086a43d4400c00620782070028007c04030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 310516654 1250 310515404 310515409
    0x1050108070c0b0714190201050903070c0306091e0318050316091d1e01140114010e0402090402040801050907050a0602060a0216140102030601030b041107240905031314 74
    0xb50055001400701584a011650481c01030000b4004204a0070b0225210303080f4000c0d00004110380d000300c00155203041d000c26040f5001104035441c05802000700c00c0558956500c0c1c0d030017400d81d00400c0e50498031803118480c540002510244225003e40d9600c000b5900231500403030031a5450344002e1007036001c0902c3e00500740745010204102e50030141e0000704001120600c40c4440c40c0508401241e00940380005288540c030140001003580401c02040041c0c03540c0c0701c1c58044202070141c2c40800b0a80300b10401b04e584513054007010040c0190015040007000408139069030882e170010f005a035100c00400c66240e00401c2004001d0100b101c1b107180e01d0340303095406911003d01401c0d11030080c0e000103401c0400012007100002003940007440300f250500b400c0e80d2a00030b40003641c849000a00700101002145441d025007070305a041ca0400ca0714141c070940c1e401a240c0000460281d604d050744050208a440314030030310300b41e64000d1b0091030351421245401c2040d24126085450301503020001000c10742c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 310517904 1250 310516654 310516667
    0x120f02031509090708030304030504080d051602040506130204141228050705130204151403011514072108041a190e030c010c050903100506060c0703060b090105010807 73
    0x4001682c0404058840c1c01c1c100381482025048849944000010300c000c144e8410002c10444459006031106140c011608490600c15001c104065103142d4000d480076150503030005420500c0101404060a070032a0400240d1b0007a40c0300078000e081072a40d901c1181401c0a843c1441105400603040f04101c0301c440450381000d007041070140584105901082010802c0410f0180030002c00c440c074400c0b8441c080401075841f600031440d400141c14841e042c602c3c05050300c640c21441c00c40701e0304d0035a82041007144148a5014000f0104000c0701138211590030032a0041c04514003644404414130b448030643d41e185107540440d00c0411481004002c0428000c002d60b601120100041607030725107500744a1400b40c50000e41442d4603516080448400c2400000202010a0454028051451800340036241030042d100016010303000004080c14511b03580e40101d41c052401030101e81030503c02c240d801c1c0791580680040700d001e031303444282c40031764075000d2440313401083c00f440c002c0c98924081c0c3c4000c015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 310519154 1250 310517904 310517941
    0x203250b0103260c01060311010f08010e070504210c05010c0b07080a0f020a0207150908120304030201060314010c0909060b1611031209040e0c0a140d080a120f0203 72
    0xc0d000c041c10541c6543d4124101002040402007a081e1603a0600000c6030003840c1c4c80c40101c075103000002c7c090703c0c69406010030315010191a01d50511503032030f00c4203448010390001c0041003003050411001c91540841580000c10403005500d0103601c007100d02c1c0071204090302d034000a040c019070542c1480000e03406025254490a1454440c3c401e481e9061031b40041d006001842c42001d001087d00c906080d80091180202c6e50001c090754600c02003504203032100c1c20365016621840d00104d842e0f208020b00640110b0f04184a8800011000c2e03480e01c420120a504520380441e5035141c0d240d04502340d90040c1e1450240201080030480b203403400b28032800700d120315031010440c124034200070410b0100200d0741442070302e4040e040d1903042c7c41007030241000750302c50b58185108030b140c5109400c500400044074104d075540900321074182d9091040342d0701403c0c200121340d41c0c060b840d10b18a00000e0340b0b84014040d9440740f41c6801c08880440b402550076141021640900300384184208010a403e50300b48154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 310520404 1250 310519154 310519163
    0x80601050f0d0f1a010e0702010609020310030b060d08030117160b090904060b0303030c09010816171801060e0a0f050c090f040b0307080609070e0103030e04021b0604030203250b0103 80
    0x108406141041c5829135215075607461401d0b0070000526900000266481001550700800001340c6826450040340415036403140204941001440000c20070395400d40c1056009060b1102c9604941d103603851640300b604072824061201600040c140707801c100640310295051814907800e800c0c461002514000e502d80c0d68440d800c46004039051100d01d90141d9503405000e030549940e41780000021005034040f01001c1c1c0041d124000103400b080282070041241036080d03a41c141c0c4800c480b4010080ba103800b42024030519104c17600e029403103000b40f050b00003c04030011002c01c10b2500011170012504810080b42c6182c1c00e000403c40e000c005c8204030381c0030090403142c003c603c03101900801d00621924850b290188507481000c035205e02c00007480f9209185032011203100603181c0d400309030102402c1c440100481c4900c402c01d05103141c0b80d0041d0842e0200301c5240515a100b243d150b0349045801e4500390056040002d8074580c92009003000d500269402c06980c211010301e640e000c48a0105200c00341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 310521654 1250 310520404 310520423
    0x3130e011827050c0a050f0f0d03140a09150305090d031e0501030503090a172121190c0914010306120309080114040f03031d0304030606080601050f0d 66
    0x114110540400a240e42d03000006995540e14245041a603c14420a01910411414500113030a1410302c50480c440c0d00c01418a41040d0502014880030503558003048051003100807000314003900801c060b00d49041d5566031071030000d150800441d02040744c40015400c260801c020403141540009003006404104e10300020710040d04500c65642c01c0c00c0c502400ba155050400002c1403181c000302070180060119821508070390303109070701108002e9403000003400390040260590b50864100e011100c004004a03560700e4000d42090721002d014212600c05c0115880009000c100c0444005041d043c1c00c400703400b00041481100090304241c0b062252009044c2d82c0c40c8243c089911175000307040144000c050704105140079203805807855106020b030082c0d40d0301e409110400c09076456051030049801107034205400000340c0b02200030f80170080f01d04040000466604503509800c100500085018030000100c0d03e045c56181400c10006034003c0d486820803440f19911640c1d08a01c03804800d60041d0750f213 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 310522904 1250 310521654 310521671
    0x50601031404140319120b04090b070305100302060a030504142d071508041a0106050702120a140a02030105240909120d060611010903050415140c03130e0118 69
    0x844ca98454021420b01c1e0985224071015a10780000501c00c0010f02400d0500513075900405110848001100141c4001d2060000c0350204d4041d90145c0d17040b048210204088503120703004100254410128800040e0b80c031403c1005000c010400c1d012400601c3c0c0151801003c8044500c0d101800d0b1070034400055403103420902c010004008007401401400c3c80c020380c1041c0301744003804a140c11030b810f8801c00c1d050043d04c600e01c02500071007030588a894403801d04012058086c040051070441c4100c40b0b40c40f846c1c05180c04924140444281208528000e00a204451050509640d4050041c0481080752502a080754660307440e54140004151019080d5a5924000c9443e18900144565604200080035403101600750402400e8a119449803035002c031245007002d007219400c0c100540041c0061105204044421002551034002ea1401d1010f424000300000300c1548088660781444c0d1000800f101801c0070301c00d0400060540907008c280f10b62501c07404000d00c468098a00030415070b40c1419 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 310524154 1250 310522904 310522943
    0x1061b051209130c09060906030e0d0e060702031c030b040902100c020a030b01121718010e03070e1f120f030c06140406140c04060e040c020c180604050601031404 71
    0x480c910303129980c10612001000d030130301800412040c0250000103283c2c1c1d80c04140280240120382c0315080103402031a5500146808486c096424504a6481013081200c3e13400f50703078200806003480b52528100b41c080e051070440030b022150315960241c000c5041080407805a80c2d151403440c1c0070784441c1401e1140c49907a10004140c080d0ba500000e000c03845510003c14040c0035003004140c8548111b2082c0142008150091b070305025800c1c10240044070022051115481500e40100c260000360403140601d4841c3ca209a002d0012203500540c00071421404101884c907212a80041921040310350b0485001e0f15101210500d000b8003409200d004000941009610b500c18074002d00d03081d4808400c1d00b018a41b07207010b0302030b03030b24040d01c200c3e40040446c0320501f032142102c0c200e035480d8030f400e1281c4001005010150920b80d0009043d4080c42e181640039840c0e642e20111020038500c070200c0540307040c40411007101d50282c00141014648404a400201d007a00d286030046d401c40900d03400303900310021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 310525404 1250 310524154 310524169
    0x203092b0b07080c0903190204061703030603100203040305030109110d0606080702070e010810110c06040807030315030b180a021518030c0102060103241401061b051209 74
    0x60101402980300303400040c0180381003154000c0ca182daa07088841d4680340312000701805151390341545030f085a803030404203c00d40c010305c1554034070160004ca07005031340e00070b80064500780c403a03428090382000080007185e18060200c3da8100c0c3e0140b40442c194201918001c00e07a00050103902000c668034203c0010402140054414102e8210002e0011580f00c410007440d00c50b050750104003502c1804070115959500d42c0100f410394080000800301d48074015a54270260070501644103540d00700f0440146c050360240700c0184168007851580d503843c199482c00a040703036108a10074131041c00142050001401c180d14498000390070201080460105441181c200300081c4002944801071240c4a03400780005800380020503021a518180c01400d4018961030f541c102e011036005070400303c0144005181d80d001900701d410354003c81c0343c6200c110041681103031000c0f41158000c41c01040100191a404001e8415400000046481003c0c0344c3c0c1d5055524140240400d00040011914010039200c410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 310526654 1250 310525404 310525459
    0x501050309070f1d100605191709070302090a050c090d0204020d05040303050105150403020d0803071103160b09010c020705040c05120c07120f05030105090402060904020c0c01120c020309 82
    0x20307801c00741503462034184c20028000501d140c0c440b031060000b40020a004e008041151401d0725081d1414a13480710780c2c1c0200c06070090100030f0140012050844010142c1c00c0346c801c15549004041c800d040d4010000071980c01808285030500300420002c503564010306495070f000003a40c4a0800c0f0050748001030183c05644c1c4884100c42c5480204800d02d50b05420907812508161aa66460740c103010021b541d83c0308600001c1d4100501c40503400c00160040b0055138001011b00c3d100810168a814550560340240c1d2140324a54001c085241448507840703006410281e0301c0020802d04080440c00303134603031050b4414588070b1559418188000350040003111042d90000c05401858035102c121f0382e100e40c109d4101550361280c0018407124541c0542c03004060040d04c1e44030141980e00e0541041004c08004000701d030002c00078030175081e00e40c6a600283c050100703602c02501c51403802c40c00050103a5084100200b0150420328412003090300441103e400e12000d84812111812164090400301c5000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 310527904 1250 310526654 310526669
    0xf060c0f14070302010908120f09030c090403020307120306061704050f0304081c0c08070f050304090c1205070203041214010209101823010f03110c1e0610050105030907 74
    0x1d01d4811400c58049510810790b4800d89800c0c0c140e0340c03144150341d907520140c41d4124031024200701030420560542e0207480e4a4500900301c40c01013003800e010518101c0180d07404c60244c0e1000c030f40321040022200c40038215004510302003080c1c9240c414020101e103001d000e8000098100000304003802001d001100d83c2c0034180c401c481e95540c0d100c810707542c0c603d80141c1d14107000c9141e4481c1104548208290b8450541200451b4102607542e120500d66402e0350b10112203d20041100061001c41c900407080c90003410340301c041512a940c50154103907980280a40c045400c00c10003840320000c1d14643c0c0720040d4108454030004442128030600a04c902401150300906140881000f203501c00c0b5803214158114582944490303560080040041d06400d81041103031007800d2040143d4440d40864554461500d00880c440620b041109042e6011a8206180f40c005c0c180102080d00b03021680c6103a1a5180010001454841150203208803a40145070410200102080b60700008014a20282204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 310529154 1250 310527904 310527923
    0x302130e18010e0f0c060a02010b151801030c1202130b07210302090a1a070f08032403060403270e01060e0319081605030301080a1a010f060c0f 63
    0x42403112000700d0912081d1a6091540042d01d800001c02e9440703031640404001e0103003180280c00c011854010b044030100b15940c4043c454101c0d43d0384607501c4d600302c03540300c0c1c4241d459440140580c09c04d01100c031054181824004d12800065022030310203c0e05005040050701c03415040010340210303903d41d22500f07841c0804290101448500c2c083c40380e018659600401186400b401c058069028510310303a0340c0000380560030000e1424240078280e1003100030801614004550f900c0c0702c5c041d4082942950400804000c00c80c04a0050003a11402010194402e00b03850800740001d5a9500083c0f004040100081880b41100c00c0388090501d100315203c000000b040d1210998a032010091107001d0024038040c80d1251103041c01300d160583c015007080d0a074542c05c8540c4032a80310343d104045d03d40c0c5584282040c400032640c01d01c081e602915a003130182ca481001810b0504040303401035180c11180241d0801002a000a1190441251200d090501083c0315504203061052890003000c1e140ca1078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 310530404 1250 310529154 310529161
    0x60f090103080a081f060c11030a0309050906152a06040b06040b01050301050607061e020d05090c01050c03041503140a0506030f01150b030901060305030a0203030109060b030f0402010302130e 84
    0x1c2d40d81c00b07042146290307504c48019664544000070f02c803900c540e103800c0c80c81140d02d0030f00c21907100389503610000d8050b111040c01c440c551804617182400817003042c0c0024100c5001407115290582203036070003d80865145407402440515040c452081c0c0c0d00e0747e650381c0e1200d45204021050b40e0440c207640140c0105480c003034039060401c120000411134120340324600e414030b280d8183d030140041d2810b9420141025041084594402e00140000005554404c00d060054440c4000d140020044658074120100c2d480c20203124a41c60400d103240c9083c1403120500c44040d8507140082a10304581e100c48100c0c42d00000c40c10700b50002c00e61901c004000d080301c2c004000c0004c03a59048a03024020540c21a03500b401e2204946088501c112541901c2080842c03080281c3e107008005590040141c90000600940c0c03655a03030f180d42d201842c15400b5030000300c010860003c40c0d200d55002001803103c494590300c0c007040c074015481c40050000303062550200d403010080001c00c0000d0050301489034039102c0b904 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 310531654 1250 310530404 310530413
    0x3050c041401030213082a010201061202090405010b0312120c07050c1c0605010b07051c0206011505190201200a090603050723220f0e25030f0e0a150203060f090103 72
    0x403a4645902e003071381d04e107e52001319441441804c046403010300c1c0da804010381030f0342040b0102e1005001503c40f90340701d0f1803002450b80c0c1032161054230884266080d9840700605540b030503070707500181349041000302480740101207000031500d45c0303030042d00301c3e1100d40b0507088110759441c1110580c009030505140c04004203090b5060401400302c6401b400440c0e0085070000e00d45181c4084102e05080141c1042004000390681142c010003810000d007003007400e141e000449204203030041c00d2040c0041c0c0d16000182e905203400e000084175240314440841c60000050760140050b00140720355010581c0c0e07400000e04092003403076458502c2901d194254482c0503c0a000400b0b43c110318040c002d082c11030750302c001c520503c070030503007040b03500140216052600e80382041d0208140100f05a180c10306504d0100c2c0c103982c41d101c80c41ea125209071030000350b9202e035401550031140c051410b200240d00c00c0303079504c001c01c04804403040301064017a409a81c0b5518140441c60a000340c0110303940080070180040f0800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 310532904 1250 310531654 310531693
    0x90c0d0e070f09051302040509070b03040c0501090e0408070b060d060c030c1b051b150c210a1704030e03150406050a0c0503040b0a151503050c04140103021308 70
    0x3100700580c251503490300c0b1404282120020b80c1e2554841c1c5d00200444010300f00344d08003e03071020741001a91103da40e40c83c22140315500444048804c9076104805214540c0c2001c00c1c8405005c030910010200e18041d900c8501070310a642e0040c2c6103065540004420341c1d560042200090741c00a4280014100408090302411030b41031000e0210f5120124540d100c52b40c05550b001c00da81080040031401c000503c61640360000d01d01d0706802160841c40281d0901540c0e0041281d440c2d0f410040500410840d40040a40051400003184440070824100f03003c1e401106c0d1408400c0d0110380d0546a16689002d6440401c104000341c0c040c0500c00700e0440c10400001d0541c40746014a0051181da40c840701c0c09412144000035400100703c013400841c01042800c44250342c807134040c40f00018501001b0b4081c841011456120640e172007a6280b0a00d2031030340c0740c0191500202c02480b810700303081c1004030f6001c01c075994000a9041650208189510806000581000340b400c4d0003a9000d1000780079405610 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 310534154 1250 310532904 310532909
    0x111e01051005120a060b15030f0403172e0302210c030703080a0f0504030b0a0207030e040b090105120a17040f0f050102060103030e040e06071e0c080702090c0d0e07 72
    0xa0061007103000505080c035403081009118010082c00b05040c076070b030302d03038000b0310b00041c4654000101070f1130342c400022404021801900c8801e9051090320f402d240050040082c074598800b045140301c2030000540070007401200c8258041d9068128030001c0950349c1d020201c903480658802082e1804508044007104044a10420394050340d1040c1455001d0507a18002e5210013004000c003044170815403441032100820131201440e00c60700d0160f498a9402ca1581d0965214000d10303400035804040503002221184190400d80d800d00c513400c00500042d1484030144510b901070a14103100c80d00d070300810b000c8002002d6001307030704880c80f943d01030044000382c0080c0540301480c4803802000c10071005d0040c6038400c5070016402051aa821980c040b0b0780d4600d10010300f50441d4440c19011103900050090910582d05640d41f10460b4034103205041803103140003102070520164100f201c0100783e60358200e03246141c054800c080d01da1502c020780c01061080803603140341c082c94011030034001700d00813541104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 310535404 1250 310534154 310534171
    0xb04060b03011103011502060408030c090a090e0318120705040b0f06030a0b0a080f0c011d091e0a180b060a030c0609080106061403060d0206090d14010f06060f111e0105 74
    0x654141b07102d0b0507a030340c0300107a038013401c7ca54091000941c0300e010b02c03005200c003d07005003442c8205a0b403400e0040035200c00e9000b40000f40c1021941881c052424510b446003000300f21560340e24040543c009680782c0203940212030058ad10341c661509241c940a0018004040140003240c3c1c0b81303400369120000b00007a1038220f119440b020300001b142ca6000031003000050b50300b030161080340300c50001542c2020518a250103459560307012419590382c2c080300f10344140002c61407056410700c0c6100303003482c8000c02440740004600d8040800b40000c480c1091010141c0c1c041441c0c4982d8807a071002980d40d110a41c0010304002101c2004204a035208849108a90340240244407580c0c640e141960301540040806c0f041c00f2080c0005202c2c5c1c90b000260035007190019110b146407a080303401240399694118800e03100000400b103684c01920b400d00c60000407000400c0204000f505001c40140b4850150030703c8000c0101c3c0c0a8110344001e0107100341088030b450303542c5094281015822aa020700011568001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 310536654 1250 310535404 310535429
    0x10f180915050904020901121b080c150a0c06020913020f0c060a02071205030402040e011a0112020702010903080f09040504110415050105040515040f060216120206070b04060b0301110301 82
    0x42d07142480d46506000b03e5009007060303201ea0806203404841c000e542810744807181c14145800300102c0d10601c8002401496000e401040414400d00031001c124000f050b92240040141841c03840e8043c0a802d209544002c2c0983d032581810005841c001d011850a04c00d6440001c0c03a04140d200c0d4002090500910b900360f030000c0c0e46030f0700190104e0042c100c001d031000c0054042801802c0c0700b07000641c0e21500c010000203006035500e109508603060000f4404480f074410704007403060741c1c1141c0d1401086003142d48c10751400d000ea40c002003181203180f100800a600101d4204010781d01c8000f9551910b801400410441c80d0505100c424841b4010a55010f07501d0046501803030700501052506440c0180c60700c610302441c140900100030a16031810740c01850a00c0301191006141c950100240202c1c0c2c010f041354803060200450f140110703404100c40e507e035071224000507200c01c811b075104103400c80a01d030741503075803810b096016042854425606500e080400c9105500c1030f40518142e400f84400300c0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 310537904 1250 310536654 310536659
    0xc0e10031802040903030e1e0c091603180f1b0e1006110a0f050a0203120a0804060c050409050708040506070504050328170406030b040204030f02010f180915 69
    0x1502107694030160841c01591003500718025060640050070400d10a00d0001a45413500040905280140b40303004280c041a0b0503504610500704006889404100d481c184c2034200900c0d41c1c40c5200d05c1c001d07044140350706c564003120b00c01c1c502a802d0040e141c01ca46440d1240f100da1402454800084007514588000d824011544242071780000d80309510302001c05075170318100001500c28801c200401e071032798440c0380344407000100c1503071100194604c01c03002040d800000d031042505100340032100c1d18015406108204859030301c1114541c000d030b00000d0008112801c0301c1c0807101071140d5049a14500d04110a000c580c82d070114a03144234030700507402d440c160b0b02c581c1d40c210f035035118510a02d41e140e80410040601100200c2040c500361000d115600c0d0fa070b60300c90740c0e48441d101c00c10040075074081020604000480e010f001d480c5882008840852a107811981c0310840960060006410000c0c44454100c10500403242550030308e00040702c0e40041e5035a8000340001d02415030300c5051900d80322000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 310539154 1250 310537904 310537907
    0x41d010605090609130b1903060e06040b010b0a05120f100608192f1909050d060e1203010f03030908030a0c1205070219030210021f0c0201020d0c0e10 66
    0x50b20040080204400c0c80d240301c0d94100580441c2084101090341da03a0000710400f90303240b1320400c07124502d1510306100300b4590b041c80e108039141c124501610b50000b80400000603907070700000d810b5421141e041619031016682c01c940a004070b1f0310116082d26068203000406e030400c45031a101c2c00440c2d02d152021078541408035403980050350302010790300c1003669007403984c44036030080300010040184043e07000c0250800d0380711030b8845003504040d100000440440301d00000040ca403081c0d140e42080420030b4588401315041d0040e9200251000d9030300c044483d142441407001c0c0070a030843c201866140c0d41c58400364182022540700c1100801d0b013100c0c0003d10504e020007902e621085ca0b031122041e16160707407280d49503228001402810407508000b2080140e440510646c2d0561041c0b400c00d00181c103500c140502d01c244d003880349056510040c440b08030082c024902500c10f50603ca004920b00c407403418142e0190103032003408101103003000c1d0003100781c590142110700c400d842114194801109000f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 310540404 1250 310539154 310539157
    0x1030605010e16020304050f01030f05010905071706090403030c1806050426030a0309020303130f050901091a06160c0305030d20040b1e070c15051c180206041d010605 73
    0xf14140940c2017030204204c145010352024501c1340040c1000f1070030424148030034084410903000101403660300c1c000d1000d46a408010190112070981507480349003445c0000a0313902400a000508240e183d903d490a680d21a100340f034110052002071315074040c0c4a45002e4640c0d001406960070844102000d040041c04441180441c45403100c0550b00d0a441900201e001c2c180300b940a9806220800210f80140c1d5070341e000400a10004070070490701810101001000320041e40235400050400c1050100c0c4c560300c950f1303101c0e54041240c000340c1d0342030010680318018007820406040509061340010034841c01000601820b1210001045103007c10b18041450464407140050581010301081c4020400d0100800c1503502c1940d01c80c014001c80749003200d1650254000700c4003505030920402002000c02d01d5109002201e0800c1405e000c401074444072140c08548080300159152031a90002041c0c03e0f07903114105801414081d515902c465104241c0081080c070800788050712400010910300c40c80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 310541654 1250 310540404 310540441
    0x9021801090c181502010e030a03230c09010c050c060c01090c170709050703150303020f0106050a14040207141c08010503060f01033009090506060c0a080c120301030605010e 76
    0x100d01c0300115003001001381d103640e40402010705540d030f594140b42d600740040015244600c80c176503000c81c00c80320085608541410b0b4030002488940c2040602000303d40d10400d44e1500c0c50f081ca84036081000b00d0403c646801349207403c2a4001c0740000d40f400050340d040d00000a000d00407090300058941d40c0d00b04000c1058980d940c0050313a00101028071440f550b0390012a000402880c0c08039035402050700d00c8071b24245950003200036a120781b1804134500d4083c0100230040100b01d840c184810b1400410007805c0540c0c04249204a0f17002400b90104250b441e003502200d0050000c0340e00447d001030120381c0e0446120700310804070794020000035040ca0300041003403162840c0041403d89910303654500790720b940903000c030900c1045207041034103082030340045a642c0006141d03150036221b4545440035007110301c0039007440c1c0140000c0005051000c000590000100e500c80300442d62003440e900b02e682000300024032202000c50010001042c840145c021506031000c00ba02d410490300d0701c0303002690450164 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 310542904 1250 310541654 310541687
    0x601050303041203030605030607050a080f0c0f09010309050102042d030312020a020a4e0e0102070b0c010204090c020109020a0302040c0e0d050f010b0a0803160609021801090c 77
    0x304800d00c4800f0400c0b000400c900c2c802d060100b41e150720380000a062a40484160700000d401142149d4030315444280c0030b4000041c01081403190504001e2406180b085003e82502e801002414040030b0f48203500c124003007504500215152601c60121000d000c12180c40c1001500010170298000070070b003007800c021254941c50740d02c0541901842c200280d008245040d06500a0348290380100301c0503401410b6070740310701e208102e044c440d840700b200300c0e000c0e103000d5481e849101c02d6a24500b4100000d034404a05080d08104902505120040780b0700441070b00080e6900001061444070040150050825101b424009000070070318110103d00325030003024042d500030440b000c10405810260700c016002e1000746400c007424403034a000b10300703148800b05086503150f01c11568280420f60a1051404200e030840d55449031528003d1025602c0c0140c00704180b9001020f12036200304005035101e9203401c1e5001d0030402c0754448100c4508410b480c02d2160300166420980c049800c07901c9203440e09604c9a10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 310544154 1250 310542904 310542907
    0x18021b0303090a020d1e1101030f090209010506030901021c020901020d030b060910020c030a05150705031015090f03030215010603181415131101170a1a040e100e0601050303 76
    0x95400304601101d5804c0107846d9207070140e22103824001503600540f9443d0151a807812103103402c80c00182140d403681c104c2c1c008240b6000e0302c84d006940344050541115411035030030761030340c544511035402446036451044d880414200c41c03000c8860503401801e40d48109130242d5007011382d00b100c00e03016034a808510348d80c440c108120000161070034800c0c40010a140c5d2044800302d00d01d40001c40d2904481c0345058850350b00054a103451085000440b5500c0306280c0740c4281582021010102d4103541d5004032516941da1008038410b113031052014100030040400c05030840e40c0c1d00d090103900c44000c0211343c2c0c00b4444c040c0022072054003d000b082c0d601d40c17044d2081203034482c0c240c94503032403200c0d4400030710340718029014183c045550b801134081c058100b41c4140c80340311400f03142240101c045048010305001079043c004030f404168814040d40800700d80300c00700303400300103041140d04d45d041c3c50107084d0300903d4458404048000003a030303051b00c0c1445480400060150442d00c0365070b18000d10485606510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 310545404 1250 310544154 310544173
    0x140607080109020c0705030d0e0319020306040f1e120806010315151202070501050906010815060907020a05010f0204051912030315120b060108060904030c0201050a0918021b030309 79
    0x185a80249050702c460015902030a4486d40002c0c03c150760000807000103031003884859070a103814444480b48038040c10148141c0306031a030200c0d440f00b20082c00604003255075141c4005100082d11814455200e02d440e1a04469051a119402c82d90f0080c0250003c0ca004001410701e5000748190704841c03041964904250346401601694104100420001c20910705549800001d29001422a40f03100d031002040a10b0000e28983c80e2007016031040030903901902132080782004650f20349030021703020360f410b40940d5204070050349401c480351030040030fa44c82c244190490010384d80c06001070b2041101d200828071150180702034140110b0245030079069030701401c0c9001a010342c6c0240c1041e95031624201c40300340d41d2810892000003118003501c20300aa4410404c0b41d44e4007102069010030216442003c1c0c0c1481e44009040884240c0300a050007000034060000700e0040c1071210007030a21400b0a514145901c80c0c2c880690001e00e04030002c50400c0681c0c84000345c0100642e4814800140103014010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 310546654 1250 310545404 310545419
    0x2150f0703020c0f0109023d0e100906080115050f030a09050709050a0606080108030a031d010c110606121903050909041a0105030c030307020f04150807031406070801 73
    0x88054241001d142d802c111210307901d1400d01c450900030b5600d0300001010344650050041c40c5203484020076400c4c47d1414400c0c81042c823030a464210501e074600c0044403426070441503411040d04550158844141e0820b050101c0c0e0080d00e42096442c66641c103401c690f030741c4040c4d00da40301400e481c1601041c424007840c012442e40b03001547e07012500f0385000c00c400f101130311003d0412482d038116002a0751641e04004c41110325000b42c000500c0c0d0361400403401d6240c16641a100d0082c040c01604041d241c1442c0600070b0001c54030811924410300081004503030010001c0c1c00b2a101c0614401d49018a0300040c11500d05810120b01011034a00902030f0061000f210100040000c0c400b10240a800c1c000100541c40700182a8840c44c0b1030092039004450541003280401c0d070591000784264007801c00074802e51004411343e1f44090b410781d806402c0250460000b005040f80c1d0000c4c200d6000042c00010311150002003900842c1d001e1614101030300381c0c3c04c640e00d858000448449011510f040d004201e0f09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 310547904 1250 310546654 310546681
    0x4060f052a06070206071805010305100905130209060303070b01031704090903030b01080612030f0f0408030a020102340209060d150605010311090a050d170403030c030f0215 76
    0x5030390700c00d015000d21500001d410480a0031070440c001944648100304419030100482e64005500c1d050140484201c0070741c01400100d54060b2604050312403010440d400790080884e0007502e84074070288200d2500080301401054014400c0e480340d01c401005c0388844c10048121208184c0184440d070540e0b0031510341d51040c400c43d054001d220030080000144002d01c42c41441c00c161b02c01e03580811418048800102842c001405043c841d030080c0c2400e6610250000445580d072414402c01c1d03845082e070202052081c01290310601d000d000000701400740710343c194010a6005140300400d038000c0d01c1003a40318519100300500503c413000d20b10b85030000d441c2a01c4044c0c0c0c0641e004104142a03038050351008400b00c0000c444030f4101d07403605000e10042d81c0500801041c22417044480d402d000210b000644000300c10300c540d174050312601c0803040500c000351099a800110b0036114607601da40e03c0c034008000340d11400054001400380c5d040ea45d030091000c240300b000040c3d003030807030170756034540d040d001850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 310549154 1250 310547904 310547917
    0x31a0f0d06050c0c0d0c0606080606010206150105070f0b01050a1e050103110c030d090c12051c020312150a17060a0f0225021503060d03050f0702040911031204060f05 73
    0xa43c1441003620080e803c124201c024025030303070703400000074491810340140c685035007210030290441d1003005000c0e42e00058065015403000425007607000100016074280c481c5d05030162150241d43d285000344040d04207071a040b900c0c107a6408103c182d50341140c90080c80c80ca801c00000c0360081c641040b02d984070f41c002d50809a034400c049860000303007126142c61540001320041e120381e21501c040d024800700c840b00c900106125404130015044698581ea107803801101e20a00c81954849a07034030543c803c00c1a40c1d51242205809116801c02c0c40b1840d0460714988080c510070400790790041403000e03000c02014540b030120720041580341c48000200004d480c4408640000300c6d0b09010b03024103100c03402c484101030f907010500c42d03005ca0450300511500051500e81010345000410610056442c5c04080c0410709070140750946c3c0300c2c0d0200001410343e00c80c1000c080d5200c0d06050658085c4031030102c0c8a0b00d10740044003240ca00300c4a052010a440c0164801c4402140c2c0142010a0007030195005144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 310550404 1250 310549154 310549171
    0x101521060b04031202060121261317010603030e0628090602010f050103020907080703090606090c110a0309090e03091201020304140105010e04140c040c031a0f0d0605 73
    0x18000d03103841c40d11441d9045a401030b00c1c4c101d2070250345542d0940611880f40075103400000d101c42c40e0750074440c560400c8059072000b49a2071204d0342c0004c04d03a005014030981219041d00350782c0d95607080c0d00c0c00000d580f041e000382e2580e45001e64080d40f00410511442e001c8030ba141d100e031142c1030301c2c510800469801001f20310394210700c4c4030f00000d8819207420b85076400200c0d03500d80c00015406d081c0001d00f1640303508000d083d001d142c40010700140c1d071000c0000e80d00140f9403401c0c102c0e03503540401c1180503010021000b480542800404105403d054005081c000900e60b83c010704410380404c440d80c1ca0080c240c1c0034000c43c02c900c0e0240541c024a0b0004c896200b00348040300d01c2d1005a10100d008016814000745080e58044240010010304c0200246100b0241c4002d200304e50416401c007200700340151009045142c001a2201c19032001e00c008105200b009008000c5514240c1c00a005403c0120b04a00d10141c424960303002481c10209001c400390010300051210b40c05ea40e01c103070007040041d2641a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 310551654 1250 310550404 310550411
    0x1103041707021e0f04060608070e04090c090b0d060507020a02180f070e0604180222061d040e01050906010612060605091912080d0b060408060a0f06080304080303101521 74
    0x1ca40395401914020640c23a07440b84a64900618000c1541024032103561085050460383c074041402c0452140581c0d04ae1200050180c1d504c1d00052120340002070014540e50820042102450300030880364081b40c000e858503807141075207400004004a046506c920180e000c8404200d80783d204040032400040045c10135458262200e2501000305002c0c03e594007101e400040d0f20a081c40c0356207108800203501c040d06000c040c1402e90103131400b54500c0144141e01100b9100240c1f44d504d50b080314201c03440d12030080100d405e05000c17051322013800b40901c50100e0b5070000e406a400e241485207508451030740d0354040c04c0410900420907030840e820f2052141d801403d00200715000b000c1c40003006144207081b0070382d40b00110a413200070384d800035024911480d41440100b0104401160300340e80004242d0001603000c01500101e40100b5498026605510000c0344c049122980040294069000070660684040d601e001010804080300300100016501e451000201200e0000320305102c4891000130 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 310552904 1250 310551654 310551679
    0xa21020d0e03060a0e0f030c06011a04050907050a090b0f431b0e07030e0604020d020103150803040b1c0e0a021512040c0608100f0b0d0b041103041707021e 68
    0x107186401002800ca609d070000d0307004000d05043d02101e511094502c448041c105071800d4002030300c50310700920309018020001449529684941203410240c031320902d00a894101c84562703168a42c012103a540d0080c450071200c1c1d002c100314401c3d000100c001c07240000c0d440e00e046c1d0480a1011a00060840d00910400c6141c1c02105072803004402400c41c2114608440c9000760004040e20415610560103800c440705020150303d4040144044913028240824040041c81d000c610202c1c43d54040c00e12404003003030115172808800c2c014429403c15202c8002c0308420601410102d4076500c00c03220359944a228800010705014480852031801c503d0740509200010b084c00f8102c140403030341182d460105800c24425541c00410881c0c1217042c0308007020300e403401e06001440d100840e004002600d5400700d102c0303d80018030b4014910f04c060113031060010b2a510102c500320340d0000e540c110346162440100500c2e000c1c1c0103040c1c403440d41d0010107144076821084055200b007200500413503001252641e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 310554154 1250 310552904 310552933
    0x80a0e0d050a1406011502072112030c20060423010c18060f30090b0a0b060a0e09040c05180a06050d030509120a21020d0e03060a0e 58
    0x3580c80721070068840c3d1404400c0071160900b0b1000507080302c556141c0381c50102a510b9400140c403030940c0c034003800e80c419180b03000129500401c11440001c08031340c81d00d10700218080d0305411206c015446611080380b00000d21842501c0e600c41c200d25400e256200b0000500401c01003c030761411a10783c01402c00481c041c117108542501c40b603c0d24000130a00d000d4000d114102250b90b98001000e01d03140c0200c80700c28000004140411964248806445200c038503003407090b880050100500184404001d10b50300707480d00005660044415485851134524816402d050410440b068402180d482c4c0031480140f1040000b444000b820595040c4407101003c1100c1d11401098a400c40035503d82c02000e2422030a80c100755242c03038018901418070f10030110300081d0044243c4003440e0049034802120409100c110b454850343c250013908081101d5550301108030003c40c8211464420345c01d85800d0701d402401943c88c1401a801070f0307015448000001e151000503845100c2d01c242141c243c501c0106c1a0f8032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 310555404 1250 310554154 310554163
    0x160203060a0501080615010c172208010606080108061308090a080307060b040608030702060711330f030a02030615030c0a0809070302010c03081902120103110409080a0e0d05 76
    0x71a20100d0b40c0e61001806a050b04000c1181e05c08100400702c1581c0701d0000000f042c460f0807074030051050303061000c206544190314045d1881c019800c41e4900810556a0301c155200c4903601c5410f001d54a80700300450358a1180002d0380c140d500c028001c1c90306845003070101500d08040a005e42c0c400c10b050140302c2499850242c404014030385000255100e800343d0601030101d4507000f1040c4d02c110b00e000070401016a0100544060701c0e0101c40250302c40f0000c2c104a82015010132500390700484007030b09078902096181400422044011151500118020210000d0702c102c108410f090001480090103560068004643c030950150840785611104c03a0b6280090304203848042d074800022512902641d40714074400e0344020440c00030485140355800181c01c6804060014040140e070000045601700d8054542d4129864890b08558812100415050606007030004a510440a01c840344140c94140940040141c00801b61460102000c0e016100114038840341a0081c00000380a27000c20001d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 310556654 1250 310555404 310555411
    0x102120105220524030a02011e050408120a02070803091309020402090d0309050f01020606090f10080a0c180b011413050411070c05060c1b01051b010b040501050105120a0216020306 79
    0x1c40503801c941000000100780410021320b0f90090b400b07005c0c40000340c3e0f400454100c407071008102d020300c0d1011504003200d007445250840401481010102c0303100000c004000d03c0308040581c00d4a0b1896116103041e6180c0c0b08801c1d405910015403005041103c155501505900784001c0c80145084003401c080361101072400406c3d008102c600780104881d0078030b03c040d45003900003440a07008610f03150b40000c01111780500040440c050440015a1891000c82202c0c09060840304460214490346080e1007070f07041a01604946540760040c41c483e0070414040d11004070416154803825100038101000b540d0040c1a0700c000342e00e02907a0001e8a900c0d9803080c6d01031140d1403000540d554400b0304001e482c80070940d10060141500700316107004003101107001c0008484480142680100c1c0c940100c406004618546450419500918000c00015030220a5102c0242e40a01035681c0e43c40064480b4000c00c140c1c5404c14183c04002582c4190941c024140c3c0008520350826016050300402e2800000303c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 310557904 1250 310556654 310556671
    0x1b23040e011a040b010302070807061503080c0f0d080112030c031b111801060903120c02041103090c01261003050d050a080a0b0f0d03020a0503270301021201052205 72
    0x1001c4080b040c2024050090804030a007000d51504600e56104d604620070800060105544ca030f0203030081c44140034010f401150000c0340d103903c414001d440c0c651114849000f81b4510302c24500003c0300180902c5849040390303041c5284c000320780440e0b102610025031880b8110100b01c11801646031480c8228002800d41e4014528120a0b448400074440f04541c0740c17040b42e810b5199100100520341c0d0141c0d810054941c4505c42682c903551680050b2030480c40001c3c020b603c0381c200410007140c2114240514814030004044554039001503005450000355007141c5103800102400c1255074540345203030301d030b0004015128041c5469403500c8150800714100c180d0b90005400151911425610011140d005040b41104001c5401d610000400411071012024014200d8821020a02d4000c0c002c51145580010640c1da89034000f0416058046501340b92552250005040004c0d5080c14420349108800407111805a64282010132840c0c8041ca20340542c01e01654000350b44045c142e000b81e501a000c2c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 310559154 1250 310557904 310557941
    0x6120209100f12020a140306040210030e070605030a050609010b19020f070e071815030504030224060112050606030a0b0a0308040608010504060b07030e150c030f071b23040e01 77
    0x281c410040c01200c15484584241d8400c00040603c7d503001c101103400c194100d44008400c0744081c02500030b000052604c051138000d081000807403c1e0400000e41c4194403288003003260b83d13142d80800c09210420301400c5800354040c0030092100e2019045e400200e100d0b0f004036000c100c210f580c598500a01500440c200808000a0003122030300f0410f030324181c00c04058404401420250010300141c0320f24640800c040c1c8070001310703003418000d109043c00560390020072140c205848000040074803080e5190ba000811800f51300f944d506403407088a0142400400440c0795807510301100015141c183c201075130180d40719a002002800110050004282589071700140d98907040070041143d10380d601014108400300502d80000b64420040796482c20304480080d288032401590b00000d0066102c1201c0c40e110005040d046020100080c01c08903110300008418140814210540c1801030b01c61060340140201174071070a0110004022401c0e48080c000140072081c610869080d100c0003902d54204456 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 310560404 1250 310559154 310559189
    0x4090b0414151303031416030213090e010c0207050d1109220b060108100503030a3e0d0e0a06080a02071509020102060a020f180307050402041d01050406120209100f 72
    0x1017500030003c0c42d064031618036031646001c00d02030403110420f01e820410141d00207017912602d2005190350018020440c0b04104805403e28418000c100440c0c4044c054030880000151034900341c517985c0200c6d0382c007040401907243c0e040c0a0014511700a4400080401201c0080306941c0070000001c034668043e1170b5604117410724000243c00994042c00e4201a440c615000380280e840010440b0350440c007514044803100303002d400044404040c6550264040c6c440715004c0004c4035400301b02c50094030300b0f40564507801504101138850248811206030402585c1d032042050a00a80c91640e2021030400b01500e02041030780c4040c0414a4211455003542d0383d800d581c03055503030402c02d4580c0403502c503000310b241200d880f9000d201d5008020184000c40e6210304112407988080c041e040c01410003030000c1d0344841e03d0b000350388402790111a0f00c04601c500200006800d00d02402108203c60030b51558801d200e94a0b024003581e024024942010038515902c0010301c8084000040c000b4694500703600480007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 310561654 1250 310560404 310560407
    0x170d050c1b0a1218080706020a0606090b0d030c0302190c080d08101e03140303190204050d0b071b0302060106021e0d0c03020703051204060e04090b0414151303 70
    0xd400c6a9458600d0b0310600c407490004100107280d94031500d0b1420440140d0442400c0c01c0400043d03500280c00500444c10001012500000daa50141b403040e0000c2c014541c8446010003140c0030040301d41c2c0d00c81c0d00c01c07604001090044d110705246034042d10580d13603a06401103521150480d42801241d20803040c00042010500c00e108a21840c0b60629001034242000d10465118690710300484440040d0101100c4c1c002407800e400c04011a804510703804042a070b28212502e90f0401c82e1101200c000980c040d50207083c00d0b100701c80540c1c030010800c1e00e44a0700c0fa1900c8000040042c082c8007844100c4a0342d08030031074002a8885190311a80c000e20b029810104000c3c2815440800d5080d2001030340c1030041c840f5000700c0c04045046092404020024950404900e040c10b0350f4005401d81c080d266465414a03c401c1c010000d40e0000e4959442100c8504140011921520b6018001d001b02d600810006a003a8480c4d0404410100489100890305d514007803c0100507161811700d0204001c0b13102c00c06 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 310562904 1250 310561654 310561687
    0xf190807020a020a050405070201021e030103300f0c1505010816031e030e06070303050402030c0108071b140f01050105090619060806030a1406060301110f0403170d050c 74
    0xe0020710162650b5030b1190302160a050032401658842d07070b2140c0c00500520710035030680e0740c180181030208240794118145c1d00019031003808155085d05102c0d80082c0c000002c8240c0314030245101d103c403540755424178000c07034616204102c1e070020010022506004903420b080c500110301070604000a555142152a91400812100c40074090111080810214007d042a40306101d420906621604010303e4103d407040b0039071444650080021071681e007859490f90250b07102d2403003034044550090f4030f40015681487c00700d0380800016650180c0700700a003038080480010f02e1080640944490305d4105880c10440e842c0303031500f8107030365540041045192110b050b5070094016111034159110302038a07000080104c1c09580c2c240504036010840315101000036a4003d60031842e00f140741e030110000f060b11070800355041807180d8241800c400701d10f81c1020869999180d018040c0e8a080c0c84e5983e800a40320400c0400c4086400910800103240300c1401001d03c40c9c88501c81c1c4940d95a034910020154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 310564154 1250 310562904 310562911
    0x803070f030e0c0105070c03020a03230a020904030c050f031c05061002070e07050405031c0f0305061e0a03120507050d020309180a0207050a061e051603110f1908 71
    0x7010304200009210190108152040a80038a052941c0389110b0808440c151526403009400480c0124000f0501c54140741d01d0031900c00d03460340e910098040f440c110b560350805c42c601a510032100e20204001901460343c1e519580d116030280d0344000a4410480d05507080304000c00140185202041d070b880d81140314159110004072190029100c5d0420000d5541c080c1d4000d0707018513903d00010500c09409034040e0b9008003001411165400c140001000c410300002c1280c070003040390f1122043d8030700d0190040c10300c41d5001600780803665040036500b5400405e0595096003004c03803642c021001c592a6080785281005e50b031030342640ea10325443c049181c10b086c1c401300000c42d00184102000c5903600f04503403c007000100410f14882c1c844ac0d910800038424050014100d100314a44030041105580000312902014001d000e100c026003901e0405444081b589503944150359640e00701500d00039484000c003104520642400c1802c000c1c1c11013040d03801248044d00e050b5800c14600d10003948108034076170 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 310565404 1250 310564154 310564157
    0x207090608070b040603050603190f11240a03090501020304110306010e0c0f0901050f120f1501020703021002011b12062117090a060e0a0b03090607030f180803070f 72
    0x10b040303160582120706401540124000c143d100d4000c80c403140e030100500c007081512208082e207a04428602602c2503c6401012100c180d41c0e51414109407410386c0c000407403d41204641200702c01102203900850b40401c051200b41503949500c180840c400f44003451003648134078054a000341c0242d0801d494000142d10803c8141802d90030401800b5400040e81c3c1005c80000640f500c8101450060710203000b84108078407070410215807105164031100c072150142c24018042c90706078407000c040e408401c1c0504042805030388800d10401c014280b4800301a0441000e100014251441c010580101d060718a4400c00040703420320041010811441003500612407071500058080d456284800e03607842c8000c0c094020740091140c47c10300c1c840102103d0340030740000c0c5504003a40c1c447c440a001400c8417450715001d034007042c0b40403661000110440780203141d04001090182e070b50001c100e0141c10000c081a400b182c407214413400d49822014416215442200341766100e1034000001040c0c40d803000c03002c1c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 310566654 1250 310565404 310565413
    0x1209070f0e09010b0303070507120c0302090a0f0c1b020919181223070213050106050408120f07140102090d030806010201140403050d0c1107120506090d05160f0b04030207090608 78
    0x4005000019144120340740300101c152b2948081c10200c401c0b40841d400a500810b10000b00703d14510070f0707404034a0044111200708141c0344401f000300c2d0070404080c014101200c01100080140c981b42841da1390209804065000e00d40360307100c1e41c40944401081084040411088200400ca00780e07110480350301483c60121014130044000c41541d11181c80088002c8d0000101401903481d410b2540c0030402c142c2006200b65651a00010010307401031064038880c0c00b50f866803944100400d003c071ba5680300c644a00c40c3c180000750300e90b40b03100d0307032200c1080003999400c00048040c2c2c0c40c0c2e401c82034030300f0b40651a146810b01d8500000781c25109912100d4000015000411000a80000036601003d021180000b000e0b010f120060b6141440b048424807640f241d4000001c40d02841500140490312850648107144ca070599555625040a031140020517001d100c13440a0341c02130805170108500460b1030341c2c3e1117601600c0f01c90500700162400e80058000d00c1c028880580349011705030040001e0030060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 310567904 1250 310566654 310566667
    0x30306060906050306130906023703020c0d0e0109090509100e06062b17040f0b0408060103030e0d02090709080601080708100c0c02091905100602031209070f0e09010b0303 75
    0x10441a515448940c0c02039407007d014080c0411a07060742d59103a1788100c0303a0f101c0d03d11203107610001089005141480b00b5440c100a540510174000c1e104041e420f440208403040e04008166420503a6280c00e504011180d480080d407140c450007414084e20841d800b5111030865941444240c48034900f00c600240d000c070003031200341d440d840320300300b011850580b43d8401d500c5050501c600e0349440c250b02400186245005c007a0580303c038001441281c0003480107070aa01d90f11195020507000f58070030032255400441c01000400d0060782600d04516005150781c0c14090f950307000856401050742c000f000103050100c103000148003002414003411440000380000f500d040384899844130107020303083c032003a1208080300d00280107070056014a503000305240341d54030708080c0a88100c8403a0044482041c1000082070000035844040c6040d1241c3d903028519241c60010172504885026100b484d05203c1d0040005101070410340c80c0d005400e4019181c5405d0402c02c036080e003036403500c0705040e11030740080048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 310569154 1250 310567904 310567909
    0xf0b0a14190f081b0f0108010e0603030415030203070e010305060f0112090206030c07050d03050601080a020a020f071d010b091c11060d05160809031c110403030306060906050306 78
    0x1a60801003045034010105900454500155840e0b548407803011034490102040110700840c01030112034401600014510446007002081400c5241c4d213404603d4420040c00040d5403c044150320102c050216407501e540d801e04040e20040030040340c40000c0d404801d00c854203a0060888242d01001d190a21030760802070009102c0594001e1390906210b22210301903016007498100c40307580b40e0000d100e00e4a80c07a0260310011158049401268240900301423020b45a000c1d105150044030103940c0d829056891020b45c0000354041c1131260300f58414056a030f0740034941000a100074045c038000e642c0d185803280042c6600b0940682004031407a4041c0003210407038856503a40c0411490041d42e002c010b0308141070171140c04003860f00c02038100c5000900103603140031a802c5940107070290960307801d905801303003812500c0480698908815030010004201101d080d180000c1c201c1e42c1c40d0a00013205285031046040039801580304401003a254001009829002585400200700e142401499032620307800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 310570404 1250 310569154 310569179
    0xa140d141018020c011104120212030c070e0406150f0504060b090f06132309060609010e01050904150f09053907020607050a050c061309051302030607030f0b0a 70
    0x400600707258081000c600000d0b00f5007045c06c241084048541c1d54940741c3c01d030031441da11544002da001ea9010f01d0312071247c0c40000f04a440408611014040b000d041c14042040c40d50098015941e00e502d8148101c5001c0c8142400c0d8014103051003d5680c480c900402e00081d03601503845011003481c2030183c01c120380c40c4d1615421003070f2000c40c4c0040c1d43c1d89080c10074110755595600302d041c2c5010ba805010111400356190701440c1142103c1d4412207503141d0003001090710607650440e0002c0c126500c2d41d01c1c2540128040c0100d0f180c01040480d0b28040d484000d02846110752014102030302d8008104107607203040c414075401140001c0001d144403408448110400717031121680d80c500b90314030722a28400e40071906441c690348c0d004010981d10328081c00d001d41c0d81d480000040d150f0f4000c0d0a04100c1600c0c08008640a1000e0480c1c0c4c10031140ca02008000181310050030f078020340380b18491302c10041e40c050103039131b12403030340c07034400191551001103c901119108241140206110081800758a0285d039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 310571654 1250 310570404 310570439
    0xe032d031305060703051902100f020702240d14041518260f090a0501020303130204090f060513060e0625030603080a020c03061b0f0a140d1410 63
    0x543d05a5280c0303403441c04a91512405400030f5401d1452100304035010b43c04a0315070005850b24100307000350702c406401d200c103d100b2030310025400300c0e0106111403140d25074110001000b10080e021420031816442c610240d881c2e80019040c5801c0f03440411040000f0042c0541100f5048001081042840c01241411110004010f810a044c015503c0e84001d04070001081760000d8050040e1036113004514400d5940014503d51320502d40050003141039440001524441c089441c40502001400e03000d00008120000307003603808140c08201c00b00410410700900f4004c140358102c411404000b03040c035004a5400d148184415000582844041ca1160071100206640c080c1041555040c1000685c020302c803503800140f0742030b00460720000035500441c0300400b0440907000c3d00c0a039514180e245224001c020303071040c4005414442d40c40f1924407840603081042807400d0002101102070520f10b65604401101c0369950f17224170401050303c1c1d60101d4250040202c440a0300002e04001d498503940070301c0c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 310572904 1250 310571654 310571659
    0x9061a0309030903070b04080105280b0d060908040512010e060a0b010c051e0f070f12020a09090b011802120403080c040f0305060708010b0a0206040b070e032d031305 73
    0xc00400d05503402030044903c03000d0020121686a035490120204540191241c000c180d440c0c40000b8007000407480358124190309044800c5031103a20b81e02104020b01d2400c0b51203802c550f07003281c42030001c0e0b11441040103480c003409000d84c44a00e014100041c8680800000040340d0414040c40508140043c001d83c00800d0603401041c001003082c0101c84040449101030094451040c50424588030716440e48807510755203090700c07000b88000c800c080d5901c0c900c6c0725a80c00d101d9401f40030003044014501d6503012030301c02000b900c6540d90f20a03960b015180090340903214211003400410031443c01c5070076201010280c81065081030385da40804c100b03a120081c070180500903d200001d504501580855002e00a103403011140a912410a00e80e0399800311845404a01500008a01c840107a4241c0340f407078415070700806d9035a0311a55908030240c00034260606001d0a02c0701143d4a0360280b00c510500c2484885501101500c1815441c0c1c503801d1341400780881d0020041c11600e442c44141c8801640e000b07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 310574154 1250 310572904 310572907
    0x114030403080a0f0c0c0c050a0b0f0c070e0901270f0f06061d1f080703080f09120109030f0e0d03030e102316080105010804140d020d0909061a 63
    0x100000f64019204544100102074a03151040380819000020900c007180154085801031f83c6820070b11400c4480c502800e11804024402c80520081100042c0350903109501075500d0607070354000342c0b00051000d881180c0c140c1d440e80b100c082041c0b51a0342c00404d1110340b42c9880024000c0f900c401e0342441c0c030004090110030404a420080c007440d9005140200f02c4103d405400031104101c024103408286c815080c1404800310b0040d428003190000021b0f101100040e10300640343d603880b602c107940100004200d92006016840e4195a090f4508900c46105c2c4000b140d21031591400030074041000b032845081c030885500c1da00fa2071700d07040d11625480740c1c1400e00040702c0003121a020b1402140e040c41da9189424003c8140d1101c00091803041d0440311003401105503252062480098541c080ca5440007681c020010041907208200c200e8100c0e011700e2402440b4600480928248041500c003d00076a1020180c0c18480f07a0240e4000010803002404200c02401d1072101d01c40003101c1003d0081c582e40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 310575404 1250 310574154 310574161
    0x60e060c0a150209031002070305120a0e16081606020304060c0303180807120c0f02010305042f120106080a0809011106070c120305060d03080901200315011403040308 73
    0x820005541682c0d08880000354031400402c4070300c069405015124041e0142401e8000d040300b441c000d886074564107448a60034020380c129500d86c121070061802c10810389a01c860f045800d020700000d0810044107111030007241c20f106409251a80780c0c0b11310f0b0100e0041640030413481e03601201b501d0a58909242a41e180f40c0141400c60140040040888403161000e11075820060300d07000500c03001c0d03c0754020f41c1e0050800c1e40c060304c010041d10006008003c440868100661184d80000d500c03501c91440c4800382d192034041310301400c052340e00f80d00d0003d9502400650621340a80e046c0b003080208802801100d0030240d4a030345906c102e2600070a00c11010403000b016a014441811880380c90303004842e65440c0050b0300600001101400340c500e40310300c0da500014a8403a015851003490081d060ba0310800ca00d03602292190401415143c2a5680389048240c00c203803010b61440038010400c4454a90074009600a084503401c50342c04e05010018021144804254060340d43c425010309010310030340d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 310576654 1250 310575404 310575427
    0x90429060f090a0f05010f0c0b041b1e0303020105060609060f1812010b040606031a10140c060f180d030f380a0609050603130209011d0a0204060e06 65
    0x104400b5035486074000b4030216642c0100b41c456000c94800f40c2c3d904082140c03103d41a40c003040001e501400c4400d030000041d0101d110709a0806810078104800040c0d2907807000e000004035404906030082e810b17034240030000d05609000302c40c0c1140040fa8050700d00b880c07140025902d442020010058480c02161103807403d0043e8034000001c00019185100c0c0070402c4a8043c0204162030106200324a0280003142c0148a8400c6035201c12100e6822400e058545c8200681c5603c030011800402840301050045004040c015000620760302c8002e2a003410804036a24180384001e01c60807000d4841825020035180c0020182301c1c0d40100c0c1030000741a54041494409040b40f201c1d111080c0034000f44200c040150175440845100821401110038801d0508100718400ba1b032042400003801c00740140040d00d07161000b542c11039000510615423302c00d0780803c0340030000342c0c441d03c58089d004070a8142c0f11000000154000846c010031441d2a041c40c4000d072513a90b040d9512406030700b021079041c0021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 310577904 1250 310576654 310576657
    0x90703020603040b07111603080c07050a0b070c050603070215070c020306010312030c1107050415031a070f030e120f0d050f06041815020f0f0f090429060f 68
    0x15500a40310554901c1c290510a404c0b800648800000824107101d9802d03c450102d124928901450704031401e091440d2078603145070308000d04a0b805802040c000260b41d586080ba0f000040c2140d10700d0359201c0e03105060203440c0c01c0391984414041d02c020030801c03250030350102d1064401c00b01350710705c40d40c45d444224044030346000240c0000e41620a0700008400d001e5450016103414038184d809201d2607100a000721004444040d26108035030000e482400503103002d0700000700c114011003111450681e02c0e26603101b42c10b5030901c86810b400c8143c00780000687e20034103010b00c080d0346050030711140c0301c140d649550b0f800c03c440300c0329401240481c00d80c1c080c00d4900c04035030054060380c505100030300300340061900aa40c195081c501c80d078034100610f401b0b4a05042c80001c01a0000f608200018004160b80c020354846608107588007020006a910004c6840280400026a0190399155003104040c041220526240b0303111520710506c010408140d20000d1082441060740c1c1e09484d04003482009003103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 310579154 1250 310577904 310577909
    0x40b0604090c2705130201020601060806030a050703080306090c03040b0402060f070b0f010f0911030a0c05040506040602240f070f09170307150e0a030f12050109050405101a01080907 80
    0x600002a042480d842070701e20b5486241100c3c1c1000f00b15903103410b000088000c0c11030034002c0c05a00044010045c003400740184991104025045d11440040c03a912541442190340048481801c080180003c0341080d81d089030b07005151a00c0b8604c4c3d414076448441d65040b00800007445000002200c80c900140e400a884003550f110400310303a24240f0003294404501c01340a13403005401d15250020344c00c40180540c2440c4404440d100340b440c0c60b614007000144c08040520018000104000290780d150007000348002c2100764041e009000d00040300600c4550702c00c4068500560001c240404103400340c425541218090909207a000e40b2180c050710000c000b6800408105265055044000d2021000742816807192000303c0580446107402401c8404005014a280c0c2c0854020300000e401075113840800c0100c0d00303104010b00380d08504030080e100c00360003a00f140e60700e50051200b007040400c8080002c10071074a090100795035071151604860410b0701c95074100031486c00420b007524410f1019101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 310580404 1250 310579154 310579169
    0xb090d02040207060209130209011b111002030c010c02340302030609030c1c0807051c05130302010c0201090521130305010b0913031b03021e0123040b0604090c 70
    0x4a8000c9130130200020b4003c0302c1c90324001e0001e0202d51150b25164403c60b87c1c602d605840300c0d5a030905955014125105080048410315000d10034040c0595940c401d42201e80d945600841e9a090b0001102e0309558510b25104159803225415802400a401004c401ca081d04008001c09582c1d04032890090392455101075014007131a0140483c5640201c000d1821200c541c04a40c19204041404c41d0010100340003100020f4400c0701050406204000621406075a141c03c40c4001c800100340b40200d40c0192403004a000000042208140d0207002c0ca4111085030300080000c0303225038031181e07100c1d10100841000f64128ac111780320090400c00c00c0d40c1d4440c0d00c03803412490036071f1039145c124003c07e0000000340c42508030030000341043c070401000a101e41d40c10f1391000100c0c0014211701d4401e10746a0812800e60103a110000d00302c01c00c1d1418813800d0f20b202000420764125403c441085c1d84421000c04041e487d001d000c200108a10700045d54101e2010b94001602426604001c0100800780e0030009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 310581654 1250 310580404 310580407
    0x40f0201180305120c0c0a2c0103050304090c200705010f0206150907020a0b090c190b041517040b0103020a080c010804080a03090804030b0108070b030106120507030b0a03030302130b04050a0b090d020402 89
    0x144958000e03810030b48c034042c1106144503424a03004412511242440000e00d1a40108024841d6003840d421101490005041501c110040c0c6c129401c003801e0002c40003030384c503800068204038640e84200041c3d01540c0c02d0003c0e122504100d20010b4410b003180003042d002d29802d13404200d4a510810620550035040400050380d41040300720941c0300c0e4000030b4035a10881000407804008c1c035000c140501124140c802142c5050310700b9180c8000082c4000750f0351b051020308035851000d160310840039449540305003911080d540c11407042040c600141c0e0011318403503103c840510307082c0e60407480461704590442c3e00d054a88085c840218040d01c00207a004040507408074001007000903641c00c0c4c0d8140d03411407050307440b01601c482c04000c95000900c200c40c0000c892008250340c4d412107511094121802d0b281c0451014450710108034195500c1c0d10032000a0350005861458284070348070f480107482e00ba11102d18052030080000c0d048100c0d80180c90050000040300e06855a802c010032152036400760055 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 310582904 1250 310581654 310581659
    0x301060f050a090606211d061e1005010503191806140613021809070c0303140408040b0a0302040f0b0702090a09200307050405040f0201180305120c0c0a 67
    0x80652441d01c502406401c0ca0100410009228040c071400e450003960f481d510644000048901000c9042c40400101e03076441005581c1000d001c0c10100c07241356036000f01118140103228040c05a50061601003004000c0140200e1608441c1481c04640c024a062501e030388908184408490080c1c425400742803074a100c144091440c000800d1290340205810031129440003401801d40c401116120f600020500284107540c2e600c0e8083c050240010701e02d003a604920b07a02084465000b600c041021400140d007032004c040d8103015640300300300340c28181c0d1910b0400ea82e461031180142c1c0115010004085000d81a091003581910010400c9412400545075924010320740341e840100183e006115a5001030300824580c0522034a10754840c1e5038000705c5400392458080c0f011040d41603581805440d00c00078007980c40c0c0c05030f1130103980100c0032020288010720001d0442e24010307252a00030300800380c08001181c00403581e200301e5a8611042c81d520300090400310b0401c0d40d09001b107a40f011086401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 310584154 1250 310582904 310582919
    0x1c0501021204030306050a0b0a0f0c06020705100506040e030f1603020f0a11090c130506160501110d05070f08040f0c120606030c080705060d0b03010908030a020a0806010305061815030106 82
    0x100200c45050300c452884030b4844942301d115100301c120310b00214050681004405101318202d030715942c0115401405e101c2c0740d175a418104100c00340c0c1711141a40300c81c14010300c0e01d4a1702c520b06659940100840c0361842801251840d405241000c03514411200014028180284010620f405911050352402c03a85c1c0c0c9800040704094403606400340c502040040c607404144000c0303035801c1007004d044031704440c907003c1003049590200300c0448240c6000b80c43c510003d4070034007484000e0380c0607425540e100c0256001003011039100034610030400840002ea102e5140d004443c590700941c1184503c44e04c1541800c0041600c0d146901000050720b0101504050018542c400c0c005c0d01e225858140712203544006031a40d41900c0c0c02080d03440030042150000100f480ea10185d20484042c0c00400d0b03564103a02e4003080340e001210260072680c0c0004655103440e038844005c56001d03100342010015410700201050701c07140c9128491000d081d034603000c2411400016002c22840e00000c0090140d2900c4a00307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 310585404 1250 310584154 310584161
    0xb04080406030f020901020c0d020111030a0306090f02120109090c030b0405100506010216050d151b0e0a061709010b060d06090b060903060708250804020108151c05010212040303 78
    0x74040020f190521401e034446140c0220f460100d4140c1c001d00303c98150504120040a0300341c012410b1094003074620006620a0010b0248003540e07440029500b85030543c01c2081c1e401c0401401c1c1244c0c41041000c0041501c031941906680f03032000009041c0b140c80c03030200449615500003410343c2d044d140c1040308011000400c4e1010608030381d0280b140e41c03100710040e40d071402d100300240c2c3d03a08842503080c0305904118200204040c0601c40000290790354420040454038010300c1441c143c40715078610f41180303030007032281000c03140c090740e0030a101e41c980a030091102d4406c81000403900810300209034046000d401035008080c2c0144256079445803442d0b50401007038a4851121090701384101607521349415421748000c07403009000f601c502e65a014084446940080c10148d03064070146404402e140c40700c0c402808142c250b12441c181c0d040900015201120042004600099000311000707151544010540d40b44028900011541c40c6813a00c80c1c06405074001c00c20081c1507001c01c2109140e031540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 310586654 1250 310585404 310585409
    0xd081b030103080a11060105060414010c17031e060906100215011e1d070804050a0c061d121507050d1a0f0d030203190512090d08011d0408090402070b040804 69
    0x4072031704006441d51610b0350700c501003442020790203601800b040100c200c0c0c0042c3d175940100140b400030b240091035038030090404103d82c4c0d00401d0310030103c07c102e4407191940411059a0200549680500d08100050791007200146958020030054108002a0340200201e43c2c01c5405900d40c42238941c0c50b150109402098031301181a0426020300006d80ba411003212440d1903181420150120f42c0d861205848106018104503018460351140c000030401c43c1085802425882d9078285134007141c111450015058444018030501240d450400c6441001405020701e041d104180d26155552110540d03007801901e0b0078000441c1019429428080c1e9240d86030203150040f1044880741e00c1741d000344501e200402d0030050140e802017002c220b00301c0300061914089440d40c1b5000345085907005104150880907a4003042540c854200403d5640e001061240900440303055045200100341c00b030314501c00080e10150208600242101d010303200e903012555887d03004807800010341003c0c50021243c3d407292 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 310587904 1250 310586654 310586657
    0x31212051312051e03060a08120a030c1e08270c13020906070b04022706030f03030705070b1f0b0a1713060b3f0f0d081b030103080a 58
    0xc032003202d0550081e4140c506003034140c080c2049400c21280303115a0b80d0b0000d0560742d40a800c2e0000012103000c02c00001c0c82c0800d14601668641d0403034075000d0f00f81c954030b402c2d80041c451650003503940c0090702d41c020700300c0074414a0042c1d0203494100200c0a9511494942280da83d08181c8905580704000340700f201c510b0003610321960941000700c40c04228051204080d900002c1001548040395106100300d400600003401014228901d400d03036941d040072100301c1c00f281e0b03c00004000392440d00b40514080c2401840c0a141b6610304914000e00d248610b80b0000d080c0d920038030101d841e9512141018ac0d1581414401c0c41380d140c3c6403100803566801c21641d840000e00c80c03041c408205032059500e00d0245010f02560305290405565807406010005400c60300040390112010a41400040020601505d680c0e40702000315040f02c140059034201d0075145599000d003940c1a29000c0c00a511441c2490519102106494a40390b4540c00401041c0d03035500e0740c101100110501007048000d00c50078526 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 310589154 1250 310587904 310587923
    0x21e090a05070509101103040f0e07030b0f0613030203070902040e09031305040f0b041401090606031104090b030709110a0e18070e04060f0f0501030b06130312120513 73
    0x214a400c40656074110b815200190f01481160300a0403c1005103000b10000e0a01c00d483c1110f1100071032450300306a124117034602e508030003005080c0d40d80c2c17440c87d002003942c901807040d80c07001004112404c04030700c0c400340502c00007c0e1f0082a9003408800a0103558010244c5690b541c1e6501e50030065041809108000040b000c04146e50080000031245204214442000590f00d49020040203080c000044000c1c2626090a0071042d5100d21403442d0030b608680f2207850701d50521440104a4840b60044011b00d45046111150074040c2070a4030122140d1080100313084a02102103818020554031040c000390070301011560702d83c2d9450203003011200903a070b50000c001170b01d010800d4000c0903400c0402004440c10200303810900c6060318070035200c400340000c158140e46110941c0c449665500869030000c80031818402913070701d4081c1e04540541181d5107820441e040d8048801e0344801d00c8001d00310080d121000c42070078001c400c540b401e1032400301d040180b0b16100403075400c480004101116007510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 310590404 1250 310589154 310589161
    0x2220e0604050607110604170f0720030706050301140a08060a02190912060f150f15050403051203040318030b100608070207050609040603080a02031e04050603060904060603021e09 79
    0x440c05e4010b9411122074010240341e2601e481e80306004216415404a80c082000600e500c4800100100010b5200700c01c1c00e6010408203034500301800110034281c0c4250040b0004100c00d5030300106030b034155492540c0b41c01042c0000b07400541014160b40c8411214021385082012a00b10b95001e09140030700b07130b03181955001d0300038021500100c850068490090320000480b01050541e030006281c41729152000801c0110081c4002c108612940300e860084192101445200d0b40c07500500060380ea9400e02038241811585c4890310342d44400c0d40400400e01c08800201031500c25031101069080b861000c460085c0c8a040c0a80b441c071048500081211002100040141c85168010b106144542c045c10100342440204075251b4003007160243d11030345800e40403010030194401440e0070a0b09400440ea00c00868605a4808081042d01601460180001c100039200c000c22a6401b070b00403508005559100e1030144010851504041d40041c10b9411411440c080e010600004240448085400c0d070f8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 310591654 1250 310590404 310590407
    0x140c2d0f0a080d0203041a0112050118020a0618050a32031b03120d0605190b04061407060c02010605040f0e0c060703020a140106140301090b010302220e0604050607 72
    0x10380c50072009014000400188150521507070103076800921410459840f18410940426400020b8010030200c001c55020391040000921420307034090b94003d03040c2034011440d00040d05074005071048000740610716240603901e4034280e10200c040d2030004d05504c3d10545401880d0201461041c000c00155508800e50100282c0d19620343c08242d0028014894083d00c0c038000104c6019100c40a60140700c0e2104036624111810302070042c001034914006071052509081104c0c0b6006412514641031a00780c0c180311500e0f210044400b90380860600740140e00c1d02144020880c071804601800b40c074902815402c843da41074101508682d0110b07401d00017401a0540c0d181201d9500b852015154001e103145038050512201070034900c1e00a005071400101a074a81e109081c886000b0300f9010b954840084c003001c0c0703000d2140044002d09500070041c18a040d070b43d031108640180006445048480700240c600d8804010500680703050768400d102514102c01c1860380c03030100740c1e0f0840d174502401d0300088406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 310592904 1250 310591654 310591663
    0x80c0118120c24060503011a090c0403050d0302160f0f0201030501050415030f0311030a0c0302191112071203030b151201030b07030204270e060601140c2d0f 69
    0x183d42000c8125100c22441e001c41001c443c104400701c1801e0707140d9a000400740e40c01c7c4159030200e1000d41d001414401c0e20020400c51060040948001e42c4091205001194001462201d2050f40d41401070307642d20300c15420030f0102c0e0104401040b10250060650030001000c500e103880b030303200b0f882c148241e980b50b500f00020b440c0000304000d4046210001000480c0d040071440103154003a0a0030070010680d065410304550080d8403507004240000450003c040d410040c0c020490034100c00a541038201d544c036100f80030301d10210325110340a159a8052021000c0c0320410042c45410811209413000389805000f44c42008401c17489880c040441507402020300303049440340d08441038140c00c07507070850350349401c1d1003000380500007096070900012807440078440000301124142142c00c0320030f501c00e483e21000d440403030340c1f00740c2e00350402c400340070007660402816250030b82503940103500c402d24800402d1038084a0140c1b03900c0b0388052100318a184400900d41c000c1c015201080e50f95844416003940d6a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 310594154 1250 310592904 310592927
    0x602070b0f071d06071b0f05060f070201180801020c0d0e03070503120a05070203030a09091a100c0203150109021c021303022b0b1f0b040b07080c011812 67
    0x114005501d0988102042c0f108010282d0000b45800e0070450a901c89a0840403140110590700c441c07090144010315252078507500401e0107c2d4998070b009003902181c0a24000c00c2002410301c29045034400d1051904942c000c041d00c110002191501c100058041e581d800e46681e450106000200c0103845003804111482a200050b00405210079400c2e445101584403c840c007041000c2408948010f076824002401d6109655039061003140c01d00d50840121102028424100301e03034422034034003a0b101d00c1c00e243c0440605040890b401c68503400402d05240707118103090541c544a0002050881e016030103001000755000e11040592a1342e170b0303520100d11546025107000006510204014a088803100804508514030391504421285003040ca426102c1c80480d05542d0210801c91000c031003084500752249210001c0c240503161030322207201c81c4214000c05801000002e507000611001d941281c040c261a90000c2050072005480c20302d003000415802c580020300c8001010315180300d903022015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 310595404 1250 310594154 310594157
    0x30b0105030f010e130507060c02150c0c01050c0f010f0e0d14091003020c0d030504110a0e0604020c030c0d050d050c0f03160306080d030207020405070c0f0609020f0901030602070b0f07 81
    0xd81d9080c5005444090f10040c0803842c02485c0d61540300c0003030360900180c4020102500e802080800ca841041850700314240c0030041c800e418411045060f41c00600e05d10180402e00341156251405103d8900704007401260300d000d0345c03d00c4810003102400d540900349400b8840169003600150781e4044500350301801424003100400d114045252508041108070790655080c0145840704483d0200e080810a2040d01c012030340d5001080180a00351072243c020034030441390440b1030b500346201c0445412004d00f480d80101d50200780c48a4801042084440180f0424101c88a42c038a8200c0101160b10154044a1203801c0c2008142c1d955441e13400d6403509031130401040e04607651007980860750017a01c0e003c20b0401da195100002c201c081440b08650310030403a40c0150341e502560041c8025110080c20400c100000c089443c070115001002036403c0f66032140c00440d560070340340002010840c8100c0c0d070745c5d4400c1100b40000300f004126401003001d54401c0c00d0010340c0e660b401c5407041071044103e86200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 310596654 1250 310595404 310595431
    0x1050f25090e07051309110f030411180916050f06220b0a03110909040305160c090903110f06070c0c08060c0a11010908120601110604080a030b010503 66
    0x6401082488551a50038030318001000c0395807281100e40190381518084003040f400100c280341c44c4c001c4181d0340d0280c01c02ca0310620840041401104480c495054440308201011002c00c04100c3c3c00519480b8800700103054148048041c0128045070700240c8200e081c40c460070210f0104001840e2090b0108c4400421100d907400c086e006202c00c0348e01c2076291160390181a60042100034208186001501400c0c2e1469259419240c0207011030340d030640717102805101840074007a55524505074a900c10b605103000380c0c480030b547c00910460000c04200601c004019180030a0100c0c0541c4055240c60180e03072188074040e039aa03021500c401481c2c0f4011990303001207000881190290011000d8144070b410500c1d100c03950784c100d4609050090328661080c000001395011560380c021000c0301c4c40c1104500801c51108940e5030001c1511414004002d20b00e04800000c1c0540e004110421141106038103640c02840c107032400c4032681c0d116017a4180440d180a00c01c9985500c60425240304035040b41414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 310597904 1250 310596654 310596691
    0x5090109181106070203010905011a03010203100b09060d06080a0b0114030604060c051204050307050f2b03060506120615040e06060d060803070516120206070b1f1701050f 75
    0xd841a4007410407243d00424200700410045e10b0034414070480500034000000d0040382c2d612501d40700024010050f11030703801401171100c2c05890b100610111521140000c0c0e54404990102c0c03132038090007e18540c46440c107800054101d80208031024050320800b0745155903030300e907a5400342c2c00b8101112103802d82d00410000300040e20fa82d0041d08661030b1810181d0034010441401008c080c0b08031421101d0750404140740c4200309041010403100c0c46540040c12a5010710b0694009180d00240c10441e21115104544440c0303000e07034420800f500b0007810303150380c80c41400003215003004180c85440c051401c9801a0512003541c82c01e65041d945600b02085503501d400c01085076139006460044402070b518180040e91440030401027000610510207407a842c096441a0302e2072005a510081141e400c9060300001651100110344c82e01d0780c810040d00d03071500c0700524580b0a04400f41038028000e44000f01050003c1074030003a06050030a1402841030342d98280101000c03801c180c5624000c1c08105a11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 310599154 1250 310597904 310597913
    0x50c0f1e010309110316180605010f080601050f0309010911010e010f03020309010209061603081b040504020307120f0227180403030207122d1409040608030406090509010918 76
    0x704082e0707014076601504c9084c0000002d00784201001100b07403203040d40004004108050303081a516588001d41040718a245c0350003c0e01c0c0200d0450750b0020404800000717251603020300141d401c0074003214150b585a18006d56642d00a0043c10015290405a80c160b2040e6620660309620301c203006944151001c081142d0a130040d400142030802655003d10a041d0507454260140040d540c0700c0b25081881d20746401e0103007140001622101c040085440d02d0203c1d0081641140c048074415100103a032035a590798100d17100c010400665000d6428028560b107010041d802500000c0c50001d43c07000984140c3c3c469144091071420f010f82c1040c14050054070850000004c1380c5d02500a007005032401c00300f41d07103410100d983d2100d1100032500744c0c050a1900303051540303c1060a411008035000c012551040900030b4140c195050014040004030038881d62925003000b0700925101c02103030f071940d44544000d440039255010703180c010f030701000000541c0c9049000d4103098810a00704031919906613240c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 310600404 1250 310599154 310599161
    0xb07080624160f020d050a0c0e09060c1c110418020903060a15030b011d07080403080412090b070501050109050c040b0f07240e0d050f030117120304050c0f1e0103 71
    0x1010b5400300803049040001da11144000c03071881d8880c1c1c000c7c01c2c140b0700614042443c826260000700c19503183d00c2c1008061100002c202c0c3d0006146983c0f2501d64001801b070000c6100d03500c21000308a810134114280078415000500256902102c0d14800c8503c000b9181049004000c20300d54542c0c84000800d9400d28654000c4102044003207840100030707100d444460200034282c1c000d0880d0b0340c00d407015044e800d0410001ca034010700341d032a01640e0b0b070800b500c00500d0101d01a0000e00040c1d041e10100b11b101c5e0040d510940181030440a140d01c690341801d125008000c2407152011079804c1c1070020710072501c0002140d0a41d88942000c1d0f04024858141401e0341d0440c150442d01f60301d43c4a164102d411001f000d080c3d0381066004040b0b4070120503038100c0c0c18152220040d00034000103008070041d150401041c0c13410b4481020749890405000d1041e645000c002e02e184003007159000043c0b2003400000704e426120504281d840001407425802444403545452954903210600c121007441903611980 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 310601654 1250 310600404 310600447
    0x1501050f040204080d02070303030606090803120c190809010c03060f0b0315090c071b0b040315060e04030216050901121b170102090a050d020a06050708070b07080624 73
    0x400c014103054541c00701c2880c1408005d105800b40c1d008690400401d03078140500380c054140307443c000b4941441d0204407a903c2c0980d490403030307a4805a00000e01c0600d900e40c1a20800707402d40d00302c40e02c034080e01d210203800300b03c1c1900c010266508011040c0c07403081c0230f8015242252080b05030312036001d00e4041e03a103002e42c0004e0031007003a00700e0018040c0d544e0b80d180c805041c06440c00f410550b5495040d4900365200071124620000105450f01003000025680c100b55801c80e45c105150707088441c00e80e000310b8000d117081c3d0000c044d132141030014042410f500003451701000d44c0701040000d9581d04d900c100401000309100f17011500d90880008400501c4101c80c401d40b1400095800318259219685503111001c0402c542d821a940401d418440c1d241100003007000b40f20a9403182103468850b0085074800c200c5024050034018001118801c0103164411112090707000f5604088908001d1001000001c0a51708184251450008084400780303d0507200011090000f20b64505045c44960b00d0a034501032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 310602904 1250 310601654 310601659
    0x60702030a140a0501050f06090708010f1e1509050901060305060d060c0c0c06030c021902030d050702030a060501090b01030e032a07120b0108060106180302040203060d060c0314091501050f 83
    0x303c480100142090286c10b003e120000034000c0706182010601c441203070300611800030002024010010102403961103001e030340b08000344101c225180301e054076080b04254403884600c4140d4600d6107110b136000200340b00740c5404540140051340d0b1500708606990341038860950042c2441d9003680083c040354886014000103003040e5a04407a07948030060305040c607078021004252188155010b4135170520005c1c03083c0c1d1003030032071601004490300800e0f0344424a03580e00d01403100024448065540401c0404800ba904c01000d021944c1c40e0b03200c0002400c400c1c60041e000c05d041050200b015103012003030359240c035070601d40000f1500d8104d2108600c0da885110b004464003458202107880f0184007091040540269010261035240c02c81441c41d00340d0580c01041000391414011605948455a180c01c803501114096101c0d220600012440040c0c208020580361070003030410029034060b00043c01404c039510720034800d0740e6a4429691a0040018660036008015005101034a4907001c40c0f440340401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 310604154 1250 310602904 310602913
    0x30809130f02181c05030702100e0a0902070b07030b06160309120516060e06030a050703062303120f1b0a02030723180106031a03010c0f030605060702030a14 69
    0x4098a03100b00c1c2d000702000d607031040325000b000780f29003032004000a8a20042600d001141010b071030b400c2d00c034010003c00a00c928900551540030512418220f2224540104451340650b5501c04e1000258002c1004443d4107404d180041c5100340240305d10001584080c0c145840e0018004001c40e001038014022018408000c40101c1e4005d00443c8402c24184100000c154000c03003020300c4407004149500850070480c02c2d00c104c0e080c989413070003625004080a2030105040d101c640042d03001c0c110b02e4111001e000714103514040042c00603405840441e4084d4103071503425102e1a403a2500303201300f8242107008034007088480303036014400c10301c1400d0450001c19154205d405a0009050840030f03400688074806900404070794400d0b40d91002c120140c11100201c0400070450078000c11501407040c1001d165aa0f0307015003526a100888080801000b40200480101074002038240004608003c0c0024a05200811071b814000112010b00307800400410034082e5580d43c02c2c0d42c40d090741902c1e5100b03014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 310605404 1250 310604154 310604171
    0x801060c060e030d090c08060601050910020a1509061d19020102101406090c1305090c0d0606050309010e010e060a020a090b03010b070b070206130b060604031a0103021903080913 78
    0x42880074103c1d044c1442e00101c0e030152142402c148841003600041c032150041410f20066030b800c9004c9900c00fa03410b40340c1e00c440041c08030080c1c0c02c00b5252003028007250100401024440140d51100040900c103840401003040c42580c0085100481e10740004a58000c500c1000c01040d0540104407251050ac1141c2628003000c40070400e94000c0c0010f988008445810b002051405405855004040c600805c5c14141d20b40f48103c401b104500c03489000716201c001190034501c1c1881100e4820103800000c0c043c860b41c07400020019802200c030029507500c0e0060b605002c08042c0100640464a40002c0546841d0002c0c514000c2d488a40301c034090005c40900001c449038584041d5000b88010b11405442c1c514138201920907030b00051040045410070380811030681c0650500e0740865403c13101d544116610640820050f00c0781d6000906540110608002408550f00362541601d01c25100c4000313007c0c150452101e2407a04c0c0c000100107150521500d4241d081400500e03002c8540e69201144142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 310606654 1250 310605404 310605431
    0x20619021e040b0a09210609080d0e0d0e030c090c0c0106150c0203010b090f1501031107060e0d0c120806011803150b09010602032205040c05030906070801060801060c06 74
    0x40c401d51014151000114030842a150894a032600070b0018a490b0b42512590542601b40c00c1c0d4901c10040195944007141d805010401090303c034680311000b01044490503c03165107664015a0b407100c8001640c00e00203032081d0501140103032248201404c88105600c60401040490f00200000c1c5020f40d078580d00021a000441c90b40c903680f088540f14616010140d0040c18256000c004803980506030350824800040c101c040e429500c500120020400e194103400101d0140040c0e40e00302c03003602404200078091000da580907100c00000345084520214150209036451941100c000d41890040b81407805564004c1c4101a40150145000340036103440e102d122030103140541081e03e0407541a041d844070a06a072140308001001150b40d24115858035000039624420b44d01005400026180000001d624822903000900f0f4000d03c2441603065594008101e6001111101060307c07400000c1100c0c0d501940c41103041c0c400035610001541c0c00e04d002690301140c19041210303420350350044c170410381 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 310607904 1250 310606654 310606657
    0x901091a0127031401060b0703050f030405070b04140102101103070c14060c0919031509030e03010f0b01170403020c0909031308160602010605030303131703041101080106020619021e 80
    0x8602c502c0740c10082c20fa0000c42c950850303191f9000244503500c10402400843d0300300003655001a02c4e804050b51740d55407403410f2403c00d0a9544035502c062004140401c941c0c3d030b0110407034081d260a03400c4402007001c00030b405094418800c4001072441c0c080012400c030038800c007245640d45001310780e103c2c105038010403100c0c6481d034102c4080c824100013250166141c41c0c4102140c08042c01e1200c54003800e070850311031411351061121005140765072280174500b014000d52864032070303d200030000c001014030391640d40080c00080061500041c0c1c0e0a40649425032400c0200d40602c1d01680103160103900602840401480944405502c0c071003408400c4c1c103003462207507102c05440307030b4809044002c040041c091402070f9550800d106590604a0a101d5a00c0010603aa400300640c50b43d007000300d4003801c00c0d200c001095219110b080c5000810002481070001c50490a24001e90341e07079900d40e9070b40d1000c03a03c54405841c41c44003012031100340640103541e078000d050140322020b04400c84201002400041e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 310609154 1250 310607904 310607909
    0x6160212060c0901031b120f0e01021204030201110f07020f010e040f0b030607031a09070e0a0b03151f0e0f0409030804050115120303020c16060e0901091a0127 70
    0x10002400c86090b5034180180441459100c0303410000b264011b601038010303101d05020805583d42c4403203154244030721f0f401095448005100855580c0808a5802c401101c00c0740c0540140d802c204204a0451412040350818000000b903182420041d03403c01094a000f1403866040202c8800d680010b81c2c2e492240f01070000030941c0009150440c04141410150b0040c622000d2510b0704044040d070301400c2840310b103c6401244c1d10300c002c0d43c5a40b4107a84811000c111940c103d021404003281c10420100118003514902e001d286200c0c04c50000c000c200804100540059400344800d280000e00810000300d0041000b01884000d4840708007080807202003400513070000719014240411b01400380702d032203941c840035403ca0009606007080c05c21400001040182050781c0060502c010390004d219040801164461500303225075a03610040c03080668407a143c1c8502010300000032017140c0b900c2180c00580d1052082106032803400c006450340c0600044c03480c4101d41c1240d10403101411700c0c0c1008003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 310610404 1250 310609154 310609171
    0xd020309010b1305190908191d041b08060d29060306130212011e0b120607020d031d0d020d0206010e10120311010914010c020c0616021206 61
    0x4640240b28100b0112036a90b9100d051001d103404c060141e0701d5407048007881441c1420b0401725248445203000d2010340304140b1000c0c126204041d036004410f0380b10403a4070b08110f51500c01000d41c55118200000c0329001080c14445070030104484464a008507000b035030104006118000f419559140c001242e07500c842e14003150344590b030304809495104c0208d0307504500260001e181350314000000d500300c08043e1101034800c2c2c0e800e80c00c0d140100400d4201c144295030355151070261514904050700680b061080017841851100c1008010b0f0400080c81031046001d50300034651080030600a8000300554a100081104803a6190f0b810140c2000134044040460b40100501c115440b4006d00f82041a0401d0307030308407405d40901c140ba403280d0440009541d600c07008400d580160345403c1da000d0407035100000301c0394200085001441952140c150f05100064020700c16002030050480e00c64401c8910640e0041091101c040055a041c200540040c40909110245421481c503c1c1c40d0074002c440821 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 310611510 1106 310610404 310610411
    0xc0519140106031b0504290420040f08030301060c080d060503061906090204081f090f06051f03080a360306060b090d030302090103020d02030901 64
    0x9814034060402040310903540d00d0b10107201c1d0381e241c681d911544c0c00d80d00c000074981014040c400700054940d9040d200981489988404480c1d5021340b00e4009a441e416200003491180158070f00381e6020080644880c03800749a040d04107210741003188c00d90000d10041041c03640001d02d010410f035000102544a6040a2542005000c10740c000d5038144a25070a218009143c80d80c1c0c20010b050450040c000d180e00d80e07020a00ba885544540303500c5601c1340a00c6800fa411800c0c1220f030000c1d001c2408284605151030345000c10701c180c2b0302560015642c13001e1000c1c440038200300310f90030005444601065407950301c80403000c1c000c081c0704c441809200d0b504014894210104418800b0322003100c1490000d040c1c0505010340c0542c041216094500038000c203c1d1001c51090301c9801e4802000c01c600b003403544e030342140070350420001d80781070680a03c0034640c0e07408103002861080c22880d0001 = true := by decide +kernel

theorem cover : BRFrame.Cov 310431654 310611510 := by
  have h0 := BRFrame.cov_init 310431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 310431654 ≤ n) (h2 : n < 310611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
