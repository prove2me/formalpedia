-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1854
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:54:55.470651+00:00
-- url     : https://prove2.me/submissions/4950edd4-977d-45e0-a6ba-8d2c03d2d821

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 333273381 ≤ n < 333453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 333274631 1250 333273381 333273401
    0x8010e0607090b0d0c0903060c020109030806040207020d021519031b0f0e040b04110d050f01091803120605060a020a05300c0f030309070905091222090c0201 69
    0x2000d4100070401c0588101c2c80c41c416104015103061030010b4a824000c001c00740a544001408201071000000c12000d1142140c998160380011480c1c9800703250040030704000078040391041e8130620485002d40c54003145c00b0304542c0d041e150724646203003c01c2260708074001d000e059a070b910301c221a007010143e450740004100500840c10310740d82c00c41c264026140f848003100320500040030070451051515058020b06142c14000c0c00000d6a10012098031902380d1015404144444d01d07039003408008540b0301c2650b0b00400d4414410855054002444901008000d034054108030441c100790f00004003d0384200010301c00100b0359503645900d030b50047d44680003d0001d0b100c41c000c05807039800c031110702c00c03848182410009108107102c000c0f800311080c5410801440040784600b43c0001b00300a030400007103010704e400100070284245060b8050303041c2c50005102c008990030100c01c883c0c440c8070725000e440c0d2000c1a41d034103c03440b5802c040d2600d10100c40794442c0c0003590a20358540a05501980301c2e03103446c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 333275881 1250 333274631 333274633
    0x618050d061d1c0203190503040f0204020a0309021306050306010e0903040e10170607080109020a09050301050f0906070c08120414070303080711190807020d0b040809010e03150f0c070c08010e 84
    0x2000301c030f441030703889010344a140c5000f000c4c00e001280820f44510002c0d07504c9481100d200c1094002600464201e80140303600341c011a540305105410351030215042c03201c030b42c003000d0103000481c00d000103e030b11488188552800b89600e5804101d8100c0c00307000b901d014040710941d04140e45020700d5041c2d405601840340c0d0882064403880741034851000b02e0035512900a9031030f0a1011703440d00030408001e5014040c41010001c0441000c200ba540c20b0041500618400e60601010b0138041c115a080041c081d10040902c035800f44240c001486090a4902032024441b203480c19a60f2410401c46071901c130500c0c00d00e2030140050200405400201c024011800c3d0366480ca80e80200d03643c01640d58030107105a01800d0700100340d00000960903001080100d1014141910407101d6558007143c1e80006e4170102c8954401160750011035038407094600440380700724020407040c14882c0000c0e030062806000c611000b81d2000000303032034081c50801c0322410b0354000c0910721074a41d80d181490082c51118441046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 333277131 1250 333275881 333275923
    0x1c080d1b0503071d010201090b09101b02190f1a10050a030302061b0c06010303020c0f0f180711120d0506090408030106030b240705070618050d061d 65
    0x500d034414820303a4440c40103511a0114041c111300d0b04d01004404c0815903045640b0750100c1000680a42c99127406683c1c1400141501401c29900c0e00950704101c0d100450400b0700e031045900b041d400140c1480c0008041041c507250203a80c1448016140c0380703080601106c00840a0865170426444034921402c0341d81c07580e034142c030f4403134080048000e024400500140d2200f400310b440c2c0c6c940e4580713503980c0d2000001e8113072800340020030b458108442680182e01617000303034140000d1400c020030b49000d02602211941803803003040d000102890050540c02095041c3c81c000150001d0040800c202007040c444111b809800036400c413034284d64804444038003103a0074000130a4560400d940c5403805540d101c41c1250950b030030110110010026a4000f9900c03a80e40b209070b180f00e041307190503440746070300461502d950786103142085032806003640e001504104072014601c800404101c0030703030140d4004640d00c1e0b0583c0c10f0f03030410740007802410400301c417081000e000c02c0544010015100c01d559007a14030f5016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 333278381 1250 333277131 333277181
    0x90903030609010f050d0602031801060b040303080a05070c0f1a01090902041104030b04020603150a061119020609040e01111602180603100c05070b0408090411040f051c080d 76
    0x84030381024805e40d41c0100d100c11940000a1031074020303640c002e99504500d55143d84041d20707982540c03001d5018500c0c2c40c40004041c024544e10151499000340c5076541031081c0e05010308010642e00281901400051038a4021000c01c0042c111705141000c044600250702e5031500e1598004185540d401c80c82140f4100b1960a0000c00740103540480341c21442c07442440c0e07219001d01c4101e030b000405540c018030201102c440e6582e5007004420140810b90f50302d820500742d10705180c2c945a0000d40c08015407001c440001c0059690303000b200ca82e07a1040c0c5000ca220310354081d2280c003500381c8a51100da00c0001061102c910210403101c03103a500e008680d002076544105900e11858007040d190710350160008842c40044075440d410803401a20340e0300c2e085250480740d841e41480c07180c00384c4049071070600000c0c00b49405d185c0342c083d10001081094921b03140030f140c003940042552851060901a040d01d01d694000c444030502c02020fa5600644a503580307650000040c0f0040c140c032000c0340600440c0da00c03240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 333279631 1250 333278381 333278399
    0x10060206060607110d05030c0a11040509060105040c020c060318061b03010e0402060f130f080c0102030706151e03060612020f04050405030c10050906011e06030e0a0209090303060901 80
    0x341c0030381c401401107450180140c0790340c403840d8043d00c1a0b41c0c212542004081c0019010070080445803940340281c0100b0b40e0925051082d0700d1050070305403055003060306000c2d403400003085060454204403400504ac5002280070380c146416580c1c06580f08001104100300c5100388400c40f202e00707110005480d21565511000054241e0041120308801820300040c0401001041c0c1b658005000800d51807e044c1170a4040c1d2040e44800a080038814030351008000208d80744010310f0261180320050811341c1102030000355240a0080003078807994450350b900010340c0704240d00c000a81404c504c104a00106900022501c0b40c90740700c00c0b0345d41c0b1301e003680004085101100140c0c0250f401032903d40c14550000801000d0017015005035034900003040082e14146007040040c90b070300000500402d507850180030b65820080e059010301440070070004100003c1c01125801d1f015116941030004452051140007858180320700d600a4205032401d040c401041b0001018620421033240d10303200c1a07803954440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 333280881 1250 333279631 333279643
    0x8041a011a090102010f02030403050c1513080706150303020d140414040f111b1c0813050f03040b190306080c060711040204032901030c0b0a110601090203100602 71
    0x12422104040c04014401c1e0303990340100700e41501440040707420420802c0c038108a9109540071000b00c3e00c00504118066810300c8503050251004542e80018039045c0c1e0510480110b420000b80564000a1030204121680e88200e499100c801041c10080e40c4900d0080e5440480d85800d00200744400d1081c01600080c2c412181552031000d5600c1075186804203001c0904010010741d1a4a42c9540c0084008501c2c0c4010700400300d00040442c003180d00350049182000704409041c087d1904003d04001c420350070596035a00035014009d9030b0340d004400c6c00c24505212501c0c00c1c3c203c245c00f00080c001604406000600045041c0111081d00c0d148801d2040d02100d1452152885580145454500c103140ca40081c044c180e00550308611400c000c0e9001070100e174820303002203565010722908428510383c0100315603540c034000d0440c10841d50450b200c1004a440038420281050070000d0f01f00b40c0644620403e40700c440d94171041b2041940c481e10100043d400448a0020f00e40c00182c0c0015658800640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 333282131 1250 333280881 333280889
    0x913140a29032d061006030f062d12030302120609040b07080705040503151509040f020d06182604230a0b0301060504030b01090501180c020c0301060608041a01 70
    0x30100107401054420b40f455100760b0507012a4086100f05501034400c0c03100e607108005102440c81154204074024044610781100001102d16040081c012040e01180061107035000b4250725000c070600800303000441020343c000040100410b00d0450805806402601d04804001c1044806540c2e040920041c03580440e4054080032080c00031a901d035000701c000a401070100d2518500e01070b10703400403c0c40c0440b1110106081c051807401c0000d000c92409035682c43c114102c0d20072109007015101d100b8824500c0d000644134011810354002008210360010034003141090f000c04004029007040141e2840503880e00450070b42c81c0741c4405030710383c8140442e019503810000640c90400401c9080950074108001c0540200e40710401081e24203e5001560003450250380d40b035a15403d40c60b02500044060340b113180d0447c20f000062002051203114081e010a40c04400141a003200c1800ca2405044008940d00f5521300a40841c40e594400d1101e071085d4000c641921050b8905800d50301c0341102445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 333283381 1250 333282131 333282133
    0x90a0c080a1d030a05070c0b0a1d1c06090605011e060c0f02210f0304050a060315210303051e04080d14070306060f140913140a2903 58
    0x100041800d02254000500d1aa841105201901256000030310f583c0c0b01d1040000828004201e2004011101d80e2103005030040d110458144116044040d00b011101018103200050424881c0d0301c0f51031b4070019200b030002e00c0c1c2d80d0041c11003142c2440c01c010905200305403600e0341407800224a96201c0340c0c400b41c0c03e0341504035190784140b030b000044030311441d03681d401c4a824604030400030142c0d440b0003240f4409144000a45581b0b90a81c00e02880c003000ca0f40c485c00b00e07400c1440204015528552001c0031160181408503a480503000300055825460b00b00001c1d0710f80e199401c1000d80c02c12210710030290b10035107040119850f1400e121604074000c02d1052418181c500004000651000103030a8085c6030140100701441ca103103020f10083c000b16468070010703075030303601c10040a9401106031140c00b400e81802c103441108584400c003688205100c1da4041e1000c0072852031014015400200034030880517513050310b401d100c540800504406410400540d10b180320030ba0681d0403580d1058940c000041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 333284631 1250 333283381 333283397
    0x3050a021606121e020c0303011e0e010306020a0309140601081501050607020d02150a08060f010302070312020a0c02030f0c01031506020c100323070801060e0102100209030f1605090a0c 81
    0xd80003c00352619502d51000030000c0000d0340c000000e82c0c000742840c1014031001d5a129810030b19130340003082140904245c2c00000d0281001a040228044ea0549402420142e6a20806101507014000070200281010300041010b44d12503408074606050b1005901aa0002d90040400700741a000078050990711510820907500145042010203914034401341c000c0f183c1480c00314030401c0d160010449000400d00407410401103281015092507030708000d007811820301c0c40d580c8004203042d01c0406910340041e0300040c05508680501c0b0a0140160700408450b0103c0e400c12009031078065071343c00306001c6410103c0e090000307104400e00c441964034a9005100d5050090104009000d1007904a002e260362500c4201400c00700159400c025000000120101e00b881440100340340e0050744400d04100c8120380350519aa07011590346a00040d112000d6158203000780000d0070003104400801541c86150340e0402130056110419046450854450b18180d0b5070140810948a0798080d03400018002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 333285881 1250 333284631 333284657
    0xa060603060c0f12051f0b0306013905030c1f050a09030c0314160302030a0239180907031403191b02040e0c0f04180b09010f02040303050a021606 64
    0x1340e4002548120417408030b0041e4141503600001404040e0860200304c00000208900b81d40c2060f60310f0302d843d480e0b05841344c80d06402c1607030080b4540c580034404d007101c202c1402036051140800a441c0c0600e017460035655a2000001d4407030101c12842c10a04509081c4030002d55840294403854201c0ca416495040b44800320b50f504880341598010b0503529400244510f8820b04100041c50900f18425001195a40e44444001e0710307066240080590403401c0020440103c15010031702c00040e40b60442296442440e400001c0440c9414100000c81011001c204030690740009403000489000b031110400c04d8220134003850320703440741e00c54190500040b00300c3c81c0403291148050040014032280d41c007912907106e41c00034041d21a03000e44c05079035074051020481a8a002010040d6030382c4c0403a02008820350131001e41c0003480240c01c01030728448081c0c0c0099000c1c403007901726612640704860210340e910f440e445d01501540205101d600103218500114440040300003c20081c1d40042c0c8512401c40b0390 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 333287131 1250 333285881 333285917
    0xb03040201050f340201031a150f07080d140a0c020d0e04021603021b0901120201030509030c0105041b06030c02060c1e030411040b1824030a060603060c0f 68
    0x4c495800c000c0309590a4461502d207440d1101014002c03020343d0901d83d820f815000040540e4151100210313540700301066102a603407501c02030324003445c1172400f03180c4a4481800c0c205050181000c060300c0300c00000b8500700058050341c01a00501c0038548081c410351984030b4a00102d0704a0500003000d684964502c000031800744509510007000104058540900d1104121046014a00803805030b0301c166000f0422540c01d502401542900740ca00009561400c0540715031300801c1036020341495a6280807601e0306005108460b02d00701d002c00203010b941040d00e00030310300504045914a21045425000c00c8651088c0a03d0b003800d82164000c04040d00c0784140b141c0e85038072150280c0c0d003c04005031298102031005015510490259140300c550800701010b11040d00d0b6100b1a4070710a100507030b6205420107100032003e81080c2413125a041a00d0044c600304810320800d0b0360387d40d0610481000c2c030300b007200540080040e80d11512080c4054591013800b62540c542d06003d100110310003070124141602c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 333288381 1250 333287131 333287137
    0x3030901200a03200a11071e0b030403091203120b010801081b060418020309010c020105040506131109010b07021305010503030f0711120f12070c0510030b12030c06010b03040201050f 80
    0x1041041e413850141c100d00b020501c0c1c0c491318038030000c10410f00300102c2d805021310000c40100a507a104012002100d00c509078032a02900803000d4070b5601001140a05201d10f01d001702038684a1003d0200700c942d42000782506c03403800410b032881414003540005a5116040250489080b54010220340920000c12141403240b00b0226420040038000000e24601400c910340327400142540040e500e050002d030480c25640315840c107106580c144030a0200240d030000394554010109c1d2040030340581d003450000e412a4014402c16800160000049603a03581e500003020310501c00c4400d01d01440c2000d10b01d00130748400340720342d9505410a01030110b140f821f0400402c6154458200704814200c10790004100300000b61280301994001c4d205842c24040400c005611418400455401c0400da50717540c1c2481207541c0150ba014401042200f91440e0080c1c0022503200700040c185031443c614240c07056503941141c03040702d5581c4216400001c004540707004032806260182d42d000d240103407120529066038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 333289631 1250 333288381 333288401
    0x15091e050606061c23010f031a0903090d030e040c170f090c0d0302030c070609030b2401030b0d020414060f040e10091b080607140901020a0308060a09050903030901200a03 75
    0x50602c102c02000020512402401f038540c0001b031809103401d40c01c1c0600014800c1c04101040b00b8241c00784100c0c040000203440d030801d0300b2110000c1828140c501120f940b80800007151f0801c0c103042e46503107541c1d00302e101040d00020407009032100d80d89000b62480b400c002540c0300140d580000c0b2800c4403900f003d0301d0301000f860007401182d2411400f24580751410341d2030f6014030001031a0403800e2081040b01482d403900032445004d6010350011405104c81000e1210804134107041d55504c00c4e11040c2c4808528079452a0010010002030500d0708504038503c40441e00ca5208241030b8810301e08628140c4510540c54136600014401d482c0684841401818040720540340058501c0200c00c00c08842d22100010303142d00c202034291402c0c5200007401105c3c004803030643d004010301c0440c41c01d036400508400d40d50b805140146103610b5600114803400180c0d00310b4002c090409007088084200000198010540d0f040200321110719400c00c0b8070125180d1420b542c5030001006001d8659200ba000350303c140e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 333290881 1250 333289631 333289661
    0x903170a090f050601080d0903050c0d02010903050f01090326060d06060b030a15060f05030601180909080705060604140f090c060c0a0b0702030307090315091e050606061c 75
    0x1181d002e071200840c032038507008111203641c0490014061140c00380070b19007440c01642001410242543c2d03942d5141c05101c44524064110540500256031052035410001c5801c41c060700c0c2d4078010240382c280604810003095021036440143e03410302c0c810002c0c41802c291b12100444030546c0f1880101300c000900c0c2402600d07565107170780002c02c08000007001180a900307175130000100103940001d0080f00d13070040d0b40103805002488030074125507900501100d6009000b441c090031040415424402841c285400c030710952858140024204043d0100a00f0084c0c00b0320300b00c3c1c1e61a80c6d48030402003a944140034903102c05403031801040ea400c0901c201c1641205c4540140e941c0d00301c440000c07800742d80098130306460381c0d0700c141c00380400d00c40c03d1f0801035000180c9201552443c41c040d40041e2000040384030050011180c2c5406620b0741c0d900c0d5001e881a282d00c500003042c4000c3c00c0300c8003105800200420b5545000e48400320b00c0c5071034800215a0b1443c1004445500d90784904560401483d59a03c92065 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 333292131 1250 333290881 333290891
    0x8100b040608040203030f040e0f010503030a05120601031b02030a080906060d0f050a0506101d160f0c08070305030f0f010f05010e0102010b0d140f0f0304052110020406120903170a 79
    0x10f00b051003008d8005440d005070428428642180d0030043c0c4c540690019001e6001088807040503940841243c0f11010649030000b103d844580049006080c005510352a80c00d401d41c00c0c0c11700580c080000d090180e45079446c0c1402c0c0d200c4404940e115142525095840848000704000085100c52001013590250080c5c40044c08140c41d81350800780e0450b000065110004814400560b001e002e0100c0d4400c1c182401300585091010384e0600821454244203100c045440b0320200c03445081d0881d4466841211251100003514002c2e1440d04180e4a00103c0041c6800041c12990391200c558100d440b030700a944281483c1c000151070301125001d54a04554a941040c4804e0315011808022240f091140c0c003901c0c00388440190901071201c01c02d00142c0c01860b008a0101e1002003030f1015960200d603c07041c8605098070141c0d00840800500c1c0c0c460088074900790051045601800032100300703481305103052030341250708022190407080007000f0580c590484865140a40300b03444e405071000000140e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 333293381 1250 333292131 333292147
    0x5090412170702010c030c050a0c170c121b0a0f02090c160c03050c1c0209060f090702011425030f0b04241a040b073008100b04060804020303 62
    0x20707100119404009030b9100d00d50038440f580c0c1441005e03115505840c00500781001c000d4000e1021010000282c00e60240742c1501c0b400705010412249070400f801d04460b00c03c650180d0000503504140241c0b09402541101c00742c85000210340440d8590b44094843c0361004a6400c0100702c44014060200d000001d001701c0510b6008101104c406038014664600401e15500d0310030f181c401005441030203200d40c0d1128182c401e0207002e0f06a4015411030745042950313609008504a00200500c0036804565201800f2182c0d4040d8000807540040040c060342d950380703a0700700b2000d541001100320514110150740305c01203403003a0310461441c0204440420034414010008095684503096440754040701007894442c1c0c00017a48080c000c002d0085603108402c001513600c0e58900071440b5080c444e030380000b0b003141009200078924051000b0f100900d0708500003129180030303418103202410302003450300001c24903040c12103400b00c085802064000d0318150416a04462407178010b4801c80e0107100500c8524 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 333294631 1250 333293381 333293417
    0x15180203130f110307151407060b041103090706030203010302010f0302090d2f030105010803040524030c070b0a0b0310111c02090a0b09090a051f0b09040b010905090412 74
    0x8400240504030f4040407140700300405040010951105191110031200340c000550004066004141140a100e44500c21401c121000d414120b20440e0b100346000c00d02500b252002010f98003403105103045450081e01e4204c1501284801c0c04068089810256480103191007600200300f0500007505035410514035a41d600c2d402c0e420740012944005000e0b00c1a40710380720000d070700800c1c1c01c01280240503a51515a0303e503124070880c01840e00070031110380640295510b140c4080300d041e010030304035980c80c6403000021605410180702182d0f110b0b4120041802c482c882d0040c480c10060003406005a1a581e481420041002139511042070b02c00340403a40011100c4031100400d80100400581d40300281000c114001090341c202540101060000000d0f0307803514070b6010f9100c129a800000d076074903501d81540002a40702c82515501c0c00042d0040340b441002000350001c40000d842c240103001c5010015991102d242c09151380021492000a0100c0c070003041c02054450a400c12141c6112801200d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 333295881 1250 333294631 333294653
    0xa020d03050315010206011203032013090c02031315121d19050604240e0f01060b090d02100e03100b090106080106051602042d1518020313 61
    0xd8011440210420505070300c4200c0084902100748045e001640c106040403000f01510b03074026003003655542140e02c0b4a81111144070300c10744000c078419198840061580c07118102405954821410102400c41c143d0001059410288030103100202140c00e11600c1891041c05280e003008000354407402c0d10302030500344070b1500352401800b4101c50307107003180903424a000d4140042a9048851040304400700d0404a030082c1c01941c08a840c19568580c1c01d42c00c4100606042c00c1b0078020b241201d90300d442a80020f03088250a2840b00a001440c4c0d1070560850601610a290707800ca00e0210381c00c401442c0c1315095802ca4059820008404140980424609500400c0100c0e0079641d9054a079590314049080fa40180b000c1e1401407599814200010414045c0140102100040a40f001c0466031190450307941c484805c801002d88403c2c01d03480480e10300b54403d92556851902c0b071041c00d404071861000050714035082d510310800d4601c420000095000400c039a810210005001001414008034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 333297131 1250 333295881 333295883
    0x90c03090b0c0406170604060f08010c02010c0f120f141e0c190309141b040e0c0337080405010e0409120c02030f030c0d091205070e04050a020d 63
    0x5804240e03240c07424407801c0151102d000c010040c0404c001e00c0da44900348018240e0340d031210b60b0341a103c060101c1d01510440d0050381c40e00c501181c01082e40034055020800d5421154000c0c0f1400f5100310060350490b0780e0814240c0050407032103200707190040f0343e040526a0f80e0b42080008110301c100010150042d026105a424640500c249001e4166000e030915048604d003941d4920f0110180059200b15003040e065030240342d00c60942d0b200b8454412900d514007007190741a00c0d100003070407074000c60040e000a0610f10071031078903010f6111301c180000d115004188c0a001804454000b800300b000282c441d94409240314041307400101c0302075510800d0b540c2540306030646510343c2d041a0000d0701840040070054003540c600000c070404101c0303103240d011910802d401d2010000116001203030500040a06014451200107140e030300e5031400090604001c1210fa4580c0c100546032178440009100204010301706500c02401406040301244400c1c0c0c01621031401c13901131080c1a800b20380b80c507030070802c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 333298381 1250 333297131 333297137
    0xf1106011d0906010b0d050a0e0607030204060f11030a11030c0102040609050405130f030f021e070f0e10090f060306050702150109060501170703091a0a1401080307110a090c 76
    0x3910814100d00e012100e600040030700054206981012180d0029015020b8064106d5480d4804030700101102d900c040c0700103244034196680352410344000340107544031703103e0f00c400500b40e2056180458030030544200d131a5440805103182c0000020b0849112410741003230061703808100201c414400d030901c010401401c0c40d49941d8582c91901e4100001c40758000c000c3c1c102e690602c62450000382d0030880004580d40e0508060000c01002c62040b4034014401019200d14030781111000b18001001498004072410290100c90090b103c80710440400310644a0010360005020309100e00b034400c4d0000654641d000c100019240e980340c50340c2080d40c0301a5040f0001d60001c403500c0f07a250502c415050b01500480909001e02850302000821410701d4290703601c40054003002040e000f0b4440e4120311901ca4000e03180c21014910810718a20000c0180c44601403140340130205900f06c40c001c802c1c64103c4034110702445c1000d481d40c90b565840d942c400c4081c2d44c00003070a07001046003021807240500d02282c0da5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 333299631 1250 333298381 333298409
    0x20102010608100e0c010c030512090316150506040b100e0f06030403080f06010201021806090a0b0307050c100b0d020d051204121509121407060f05060915060306010f110601 76
    0x51941e17092030f40181d032440c10003034100d8021002c240c01c58200d50030030b94084403043d004ea940c4c200050031401102d0140460341c2d00c00a140061060300d0006501d0080400c41c02c0205494100410044448100c907442c0c1040c0c9003802040e507a070154004040400d805014842035460840000e00c1a50086504401262404042c822908007200400d9402002030008510300106504c0036440820740340a09445400000348801441c0c43d10100e1200928842c03a40c02d032a0b051069000d04190018007250340c940c0704041c02020440c1190203098255030020704400c22407843e6809014449242800030b81c0c06200d441c0ba2580d110003542d0051000307140395035041c1002e40d01c034540b8096990809243c020060b040100302004251200b220207500304844c01d00c9038861002500216850088200152000b8a8607081c0010055641c010340d2058604444403250341c1c2c2c40c510030310807561a0124040e0044802e01c0000e0381540114840264145035061040403080751145c19880c02009070001c4030004641 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 333300881 1250 333299631 333299651
    0x5010603140108100b040b040207060c080f010f030602031e0405070602070801050c0406030c1202070c050a050405040c032d050304030203010e1f090602070501020d06050f0a0e1302010201060810 85
    0x41c4a90080c035588400301c4a4154900900340759900c1c0040d103030781c11069440881910316500d070b5000c603204510141c403c2d500c403011410507100400b220750380b92000c60481c2c000503155401c1d58a050f4182e2304844401a085070440d22076400a4100500f50550180041d0352481e01c01d503100d49543c4524440ea0080c0f42c141e0400c2d000a05252107984820354583c1002c040c4403222003010140c0d0150f8000c1d280000300e800c4024400c0320507080e204d4040490b02c2c400207040c010b0004905240c4103031a001d6035400c0780c15a941c0cac01d0104650045601800462040c0310034400a240b528000142c42600009c1d80400c0300d1004000c031b03084000e000200e030f131075000140c1042141001c0c00350701820b10b03807103018002848400e14009000c0817601c000c0d04100d55224098410003245a058640c16904500210748500700b030300c03811004042e130b4054035110710b04601403807a40d80780c180b80400c192340603d8a201d43d6625401d80031a8007640350ba00132030640d500d0310f10208603404100034030180b1100720b240202c0d00101c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 333302131 1250 333300881 333300887
    0x2130b0d1d0c030303011715070e04050610080f04140f0a050c09040b01120629010e0f01020a0303110702040e030a0e01022b0e13020c10060f290a03050106 68
    0x44181c10302010307045038003035045641d00401030302d04440131040301c02d4130210000f410034142403044103640040c50708001030001513503000d031100001803030a942c100b00365140c1c0820440b08804c089403a6000501c038800245401d03140144064120b0f100e1021b000d5400b004400c2e180c10440c000220f481940c1c0039540322801d01c0010001c051910304180e446c21518101901c3e030f00f03d4010140200015241c8880200c800c0010030384c02999030030102c05034000220180e2003603582c41c40c1d5030800e89001030f08284d4003c49521b8810f540c83c02d040b84c160000c10301500d03196416005460140c083c1d55081000388030350000f580702c80c0940d51807002e00c10003a6540e6040000042c100c140c049021504660000000b504041c0d00b4540542c0c0402e0b505400514035002d00b4001c844103c56041d8098000c0d2030910700780c00303421181e0050425088108252901078590f50340400813071b8554418820240000101040102028042101001c2092509a50b0407032440013404540e0300400c01c050000340d0350300040000c0da43c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 333303381 1250 333302131 333302171
    0x6050a0e060c161a1b0c03010207060504031e080a09020a1205070e0a0501210813030804062d14040306050f060907020c09070f1107090203010e0c0c1002130b0d 70
    0x54400d002005680b013401c5000306010301040f010b48100641d0038500d10f440300b080f6003421240010000d5582c0c60031303803900308040c140655080300401c9050782c1c1c40ad000c0b1308080101a0200712969083d1302c0d50b80c2c0b4180030003d44002031060783c2003001c1020104a140121185206042c084d80043c07510a00c0d04003d5425960010070740780160386000b005208100b039400740344001a03101c10300f400210307410381450390062107500c6858050003041c520010411600c0c1c00a0001c0342ca0036210803040150301c004001d2045000b100909038203411115000d200381c01494002c40b0314420410701c03402c198270b17035032a542154025645441e0b007000001c100b00d020710f00b0360301c0300354043d2051001d0310443d00040017040425030058003420600c10169680e203d420711420841100800b2503007251341c45656040c1c400300075402030090382071580040000410308902c1c10100c85c542c1d034400004140755001c0c1c040c5900290400c062600c0f0200c0c1130100010003c0d00a4090070180e201c90710b00003814100284181c185c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 333304631 1250 333303381 333303389
    0xc0d0f020706050d09082104150204141309050609010906061d0a0e0f03070f060f0e030403060e121903050f070e060318011404031404050a06050a0e060c16 68
    0x26110a20a101d02c5900c001034420300e90500c030000c220340308503181c25503840c000e01c074100141c644d107486c02c5088081c0d0826580e000b6130081181c00004000650b00800b40d1240e8003074542d0383d00c0241383d04206424255000c1c80c01e00581c0c0303000296003401e035965608010301030350700a00c160344804070041840860300c210b00041000c240300054100c901c0c00a600040380041111480c07580d074454a0300c81c10010f202d8400c800c000751050b65910001c0e807900080396007600718203841c11854090024807403041481040030366030b80000290f0901d4038642d45d26001e06899200012a80200103121007070b03040203c003400611101c0c0d908a20b028222940043c1241c40082451504180c606c051142c030307940101c4040080081030312095925507400010786003000301c0403125280e5600e401c285142c40710f09080c556010b107100b591590741d45408803003009818042c034060705038010402c1204102c3e0900030740c0140030203035083c142001458000400030303903560000700d1060920b030031511000716545884101032000d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 333305881 1250 333304631 333304633
    0x1050f0f070c0c0b030403020a080307021e010e0601050d03090503010606120c080c0306040c050f130314010e03030c0a1e230315060f1224010305091b0f04020c0d0f02 73
    0x10304030f0300c07015400c0070544520750360282e00101080601d4401c0c88401180d5400c50f01c20781c0d6031304200a0095a800041d41c080d010507800304c003183c58128041c05403010701c2d041540200600d03424001005100342c040d203000c5052210b501d80c0015240c0b0f0038091000201150744a0364141d0702d40803c12815200d40c00c076491704105c0103000f00848a01e21006407500003000743c8001500c113810140a403441e11070302c02480705144002c1003a02034000e03c21114029288940c07031041c1242100c02525081e500400707409030f0207400901c0061001001c03000136002110440c5003508030350100350305941c80e0301c0c081040035000230380b210303804040d041d0400c144da980c2103030780340e81280b552400e40e0548034010305c08210148142e000040404100c0500000d9030034042d040c0380c241c1403906100c1c00e8519003a04048500b0350303500c14901402c001e5030181c0301c0c00348a061010080c10f11a0070703400400d84400706940d141e030340c80040d18034069090749403840030b802e01e0415040205800c00003140003402c1002007824180071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 333307131 1250 333305881 333305897
    0xc03030b09100b09180f0901060b0304120c02060d1409070f030302070b0705071502010c0e0a0605070609021c0609020f0a080318031c0e0109050108100608040f0501050f0f07 76
    0x102e03250b80e030040d50031514121001d9459521800005581c130000d1100c14210301000014402100320403900c140c040c01882000b040a2680d030744008599000868000c3c1c40303044080341c42d00c00c941c0124800d17480c05200800040ca052201d507055811155008008044540c1c50010000c07620020408007000d0409480e02c108464a9698002e558204038007a9200b0820081060000c10208000708406406c50b040001c001903002d03403009008140c0c60200c880041d884091031209424115104000e44a1a9039903a103001c50075210b101c086c0c00c40c000200c1c0c20400f030003c007468040340810070510043c402d03180425403014900402540c5200a0121881480e6402041003201c00c000102c991604148034080c0c1d1298403400064280000c2121400d034400640820b0003006a00c020030704009202621504ca4440d209d50044031a00d0040343d00814000700140d06101032401000d260354410301c5110840c158a00590355103094600c240d800b074003101d00101c10300c0b140052005045503c00e04920340036074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 333308381 1250 333307131 333307141
    0x20306060403030c2102030c0105010605030705070f05210408011103090307141c05040e09070609170a15050402030717070e0402030c100f02010b0303041a0a110604030c03030b09 78
    0x3428840c5200007018480c0c2402d4820400510040d1800750b8100540c804a00e9048003c0207500c980c0514020481c81d403038900085026070050040d28003e41c150381e681402c0c41d51319900d0058490300c451094031507201d40047d0341a030203105900700032564109010b090b01d941c90000c000d401d6a01c24a032101010809008206508000006603604182c0102c00c080075203071900740380c0c0d0911070409045046194100301c0e014690303811600400455a2440c10411039a5502902c0703030f15a0024024180001c0d030701c210820100b20f0181641102a0144003500d8001000e80e842c000d201c11461034800e141900d4400304401d5160032b200300d400901026482131800320503500e016848811500840b0011014203003c1819905c04100c451b0401c90054000312b000d40d2154005024000001c60841c0158200aa204550708020040c0e804844010f4041c0b5030340345a10000a0103030704400c9803501008102c40d0f015100031400c10880d80290b00940f5102e1420034542001015503003495120384c05002c1e1341051007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 333309631 1250 333308381 333308389
    0x50309161e0905090318060408030d0203040b0a0506010c060e03040e010306062909061303021008060a0b0a021f0e0304030c082a010305040302190c08240708060613080d030b04020306 80
    0x140790121a5281e1324414486d000000e29a008035004002c05100103c0d113444860307900d500541c0071300d0060441201658410418a054900880318240000c01c90301600b03002a095801074040444004244c0e41069102c407810039102109038029a002911002c1c02c0199035509005051100001280071f41c6c1c2a0550501d0b200c06c0c440c041d1580d000d801c00250410094040c0c21100010b95802460312680343d4107000024000c28040d113a403071140000742d5000403107414841c00c0710791208098014140ca0354907020142076000b2400403ca10040d00d43c202e518002d1410700090024510801c0021a0030341030000091402002c4041180061209085072000d42070720002c80e000c5100034039012509544a00e4100d003020100400d010103029203202403010841424240b0059031071310403c691015061160800301e07940824000307003540c01c09201040c8840d1051446c00e81c000006402c40e03160201c40110541c1100c400c0e80460102c1d08940d5102c1c2c5004e6041c0144680c40804450560450030200300203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 333310881 1250 333309631 333309637
    0x6090706050a12110d0606020d14090301090b0405030a0806030313121104150513020f0406080907081b040e0d0210180b01090204051002030a0807050309161e09050903 73
    0x100c4107000c808190880c00310f210b001d83c0c4100d0150140c091240c0d25001000a2440d003001d060019000d007040c00116400703200142610281225551341c0c07843c928561009070a940c08001c88030380554841d040f41012a00c514600d90095200b40d00840d5180f02c2c1c14002850110f0151896110360400c000707105000c80d080550b801902d003a00444042144580b81080d01040c0c440c504c550031504102605100035842c00c03102c4100d030b0341924220700000001e070081c0c040340b10b443c0e4034005c0b0034414803040c03010318440c403505507024202c1e008031800075843d00c20240c074107600017240864020740304200300000e082a000c0c2450014584c0c0003459810114000691140fa50004d14040780c0d84c1c43d035404001d4206400089040c5410000e140d4165031101018006540701d4020f990280e10402d02100a0900c004103d42000c00140d48100068a40c0d80c1e0403a40c950003c2c040341140c0c82000040440400b0300c441050003000c220f40304071444815400800c580241c00c2d840000725a15180400208070800700403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 333312131 1250 333310881 333310889
    0xd08100308030403080903120c0d0b060310150210020c0d0f05130911041805090c180f06010c0209150a050303040602061b040e04050c0109170309040f0e011806050702060907 76
    0x785d040d5548440c0074500e940102c003200b0085512420500921b81d0501c0700414006000c0581400721000d0035041c40020300c4281c42400c509a64984208840241f00c2c1000c68102c9152040d1002c0750354402032403044e60460b140358982c075007141d41e103850309a40103200e408180c522401c09a040461001c810080700105128002c0801d84940c000542100e0860403507010742034843d40e0481035090880c0c02c50042004541c00302080c403130381e04070105514061446524943c0910064500b5543e003480410540a002e0301d45c038180000081d035840160b540d480041d205e00300c03030022640000034010401c08111aa50320582c0a034000f0442030140759404103000d035001150394003070b032068043e520311207803203200303552103000750030524402e0104100c004075029072120b07806d0365030040d241e4031080c0785101c104000e811418203a204021001c0d5900380380e0002d2801c0c11442d0000501c0348002045142560000c02102e140002807509400801a00b0310031103800000ca84018456843c0c86e004003641c0750144d002e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 333313381 1250 333312131 333312137
    0x60f0601091703180103090c03030c02010c0807050109060b040b03031b030d0203040c082a131b2708070b030406060918020102010f0e0606011d040207050d08100308030403 75
    0x100190980e4001c0039088018000c2041c08540c03a0602d400850b16074111080182030080000514900f961081c001c0d40111034001001e00940c51031079500755052008030b030003281403014607560030001c41c0d00d500140050340d001c0c01c00072600841070720300b1108480e0a400c91300d20980c270f0300340c0d40b12054500000b62841c0c1c00400e410070f202585007401d41482d5002c0d00001914560001080004001e901403511084403c3c120480d40d422070701c0d62580e010000e0312029441d403a11001034460751850311050072490301754070801c0000d01d018510003c80300a84992415408a4142c0d210010050341840d09520382c1071740d542c503c51041d0b00782009984c03520007034070802851a001001150520019502032002405400410071070080030fa0700f04400582d080d48203a0141d40703410070901c812120f40c0182c0d00c0700c0021002905455035664010754003001d000d42039420140700c51031042004d4807a44014611a4040e1008010846150300b0003400201c3c010041c00403d001c0300f00410000780300c20192900654981 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 333314631 1250 333313381 333313411
    0x110d080a0e03090306070509090106020604030f051b0703050c0316050f0105030619060207030201080f0f061302480d1b0219030303051509150402120c0d050a0b0306 72
    0x1000d41d2441c0510011103901d4010074051051b0399400c0710080c8454503040c3d49585c420780e0303240d0040c6d0f1241401c035406000b080c0881322001030540300d8002440b4541a526001c400c107a051301602c1c0c070b49072841c0c00454044c2c3c04000001d40071719040040f1441030741450030080402d0304113004a0b810a02d02c5001030b0600001001040c40c07903a4110340c010501d42041040b0307405665620009580740d40510050380852401c0001c07600014084013402d200d0404c6000c00703115034a81405104d074040b0b0001e1041034480d400e201000148110b00420001c00c000c0c0322120301200090510a10515050020719081140820b1980700514000c00c4003501000c044c1810038003c49511882c07407200001c1100250b10441c01c0b00407000704081d104819064070700980d0b01f004107540310000070071604444003c0c65400442d800c00030b511941212442d0a0505003d1310150806054404100100c1d20580c2c00f004812070107e48840b130f401c1d003485426803252004405008075841c500220b41c0303500c005845004806424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 333315881 1250 333314631 333314651
    0x81306022a0f010609022d071a010609120f031404050301060b18060408070b090a03060f0218060301050d0f05030f0f03070e06070803070315050a060f1101062106060e040f03110d080a 80
    0x1040a923502075800c03180a000192002c04d90100c1303180c0901030580410380d4800c020903131860311205881070b254015200e0905c003406807030541d24640455218031060804100c046480d032400c2c043c41c3c004001020050380c80d612040e0750703116015828080d281c060002400100144e880004e5100112242040007942e9684480041070005107180c001402e0a828802e480003c2201c0340c0c014182c0d403603012800d0130440714040c10480c50748800c0c480c00307501504558181c0f020641c2c08003410784680c405c030112860170070008031039170743c981000040310744040700031017004a8241c00c200d482050f980c00303c403903502d00020382d5140089804058180c404040e1348404901c510000c10500f9009801c0040880b0030241d40c418006002c000d031100c085002a50b15001843d03200014055403041c0c903420f00140000d481504101030303c1c0490200184c0da100d40390300f40000c042100f1540680110300502d0404501c07651030401500e9038840c1c1c511441c11390711030480718014070f030301031161500401e00d4000820341c00300d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 333317131 1250 333315881 333315967
    0x150e0918061f05100e130b100f020a140a120305070801090504030203130b041d09071e0324060e0f071b0501020d0203060f01081306022a0f01060902 65
    0x1164000307642019041c50221035070341d0810a01c01c0780c2801118400101b03c04411070138207984140c00c0480e00141c49074840c2411500072450150003c8461040300e40c100c01e03580354025142042c590311825a0003240004040c00084c880305004040340741000d0110f424049001440380c20148912100326a903903010908141c0f003441111985000300d00c1104015031690040c100681c054807030b030318022010000d40100416140d080790300c584090005409128a064116075215070010790302d0548500300007021001880742c0c4602e541e40e2a9075117121150003481030a25049946a4100284c0d01c44d80104003c110b02c4101d010a03400740940c03070403120380d101d19a2414414103510000400c59400850fa140e0898200c2c0c0c042c610604080b2410001c40b21181c0065035052000c1d661480340599100740800400c07010303001407072401f03034440480744110301c0c08010401441002413010440c0e0810542030542e0b050901030000980030003241181f40040032070360601c00d002e8a11005000e000104d02035486019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 333318381 1250 333317131 333317191
    0x120103033005010f080a02030c04090611131a0301030f111201060e042a030f0f08030703020a030e011a0d080903030a0c12030c0c0219150e091806 64
    0x740c030507026481d440e05124100042e18007402600507214001d07400240410001500c041c5542c0c019010344000d00740181800050084030000faa1200c3e11956451080307a82c80c1300074a040300402c240f5030803460402131081044440e0041c00707000400c0920050000c56500c908111030603a004a10201c40c10301400407600400840880c40c6884d460070400003070306203524034064401c9100d1030b40703420f5400340058550700e500e01060b20b48510032142c100034400602d034900c2c0d220b4058080d100010f40710b0541c0e980d1080c1c07a070040b22403074000b80c0c02040c619400341d00342c001c042d042100c8000a008184240c5401109942c0311282c60303201d10b4008003004207204c90401180c008820203020327242da694000e0740141046001080403038040391619a0a203055200703105035610100c03a079807080301075080c54080108a9100300114001041c2030300d8002003c496101200d142803000d9110800f13040304030800c21001c01c000603c1300007004040400e021940c0000300391035074041085030490700303180307000c501340c400c0c6034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 333319631 1250 333318381 333318437
    0x402030601110d09170706022109030a150510060210110c0a050703031202030903070f02040f2a0801031101080717041506080c030c0405060319060e01060b12010303 72
    0x20003442c0b02c07a450301d5444000c98081e180b22035040f0650140601720aa0f54008070320503400140c1108a9104600848405481e1042001c0b610303541041000c40000f414482c0c07091085030441c4007003a0b101000310450046a601441126228107194944440039464601800320700d070b103d80e62750407001c03d683c0341007080d600503000d110121a48007074513140640d5610300501042d0081801014140510f5125000701c0348201407150146007011031942d210100383c0104007040341e1007500c82956a0b00c2c0d0034a072007121240385001d15400450901d416400d41c40741200c0b0402d4080005c0c1c40c0041c000f14400080301d43c2c05600c00e103070040090340e4007102100c0035201c0c200d041560b1040b0b20244420301c9000c1940c07034043c400b002c0040204035542c202640e84c5440b000461034242e0020000b0f140306150603401907922560181c02d4031191500d10030001400b02220308100c807800e640b040c0708007004070240b1a100241c001c2c01461483c20b840034a208030040e00510000f0200500740c401c0d5902860315211030810742d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 333320881 1250 333319631 333319633
    0x105040305071502012a050f04091506230906130f1403071401020c0d0606090c03090b060f090f0405070312080603060c030c070b060409080c06070e0618040203060111 73
    0x2564030340500e01483c00b01c401c1400c1c019803d160220200034040321803450107650070052480008a030300d4040d076840d0444800210b19035810f2000080c4c5041500a11881c0c40400515491981c20081c0181154550038954044107800c01c114504010710141140c100c400c00300c9581d500e40c00b20840c0c140301d0242d40d070040c0381040d0810f10b00107801003000c02c4142d075002049085d80c071340070b44480804400f07103c810000b82c0161f000c00c0783d940440c10100c0800030514042ca1000c5256511051100d090350000c0000800003581e8292510600100c11407440e0424412038105010400300b00019040410142c900480140b02e6400306040203400c10041008650181c00100e0440c030744031020f080d032081103030454024042d20001030b241011000c1201d22880c114880241410600d440d10031940740014902030b00155694000d10100315090003803c04003400000030700b680e183c0004020304081041040c1805400c040c00040744803030100514462101e0241c078011303266500d140040f28030300b030003908019103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 333322131 1250 333320881 333320893
    0xa0507050f0d1805030303100e0a1d071a09210106030c09050109050601080910150513020307020d020a02010c030804050a0c17121602090408040b0d021b0316030302090105040305 78
    0x509400400303d5220341c2e801d011203020103544800b4940c803840100c07040c041501d14000c0070b0007242c03c0480b907140c000a49120000b0a400381c0000030500b4041c00e9956996035200602c10030919051800c0a2460b00e1115203203414008280c010803010301108010301c0d14410000710f504181d01007540a42c00441e0001d0002d400140c2d9458203000914080c01010700701400c010010b0072a5024144107800707060f1040081180d4498891000010008104104d003190b802400018103a82c9103003c1c0030032841c2c0e0400c0144e50741003030308003e0f2902e05824010000d542010400c900940c2c0c0205002e8280c980604100c912642d840c5809400c000503a40001d00da003c02c81d80203d0318030324000320f4400da00b07100c9040f41e001c0705542c886a00e090062102c0540f0b007115200d200001070a08403081038120788580c002f03a08142e00d90b00704402036044a64222086075000c6070b00c4020f030605101401200303854001841c50442d6225051042c64a80500681456000100708650303910070001c40c2d0040d60420142d070342c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 333323381 1250 333322131 333322153
    0x1209031f0f0608010e070924081c020d2304091508061b030c0a2003031609051311041a0c0105010506030115030902031207060b09010603110a0507050f 66
    0x34071140c0320035520280352840203c0d40510500c80c079100324000d04000e0520500d00310302d041c06801c441304c1c0107400036a0319031344c40c69a4402180d030002528082001c0c150b05002c08622094002c4030b00649000c66020b0001240c11036004070101007101c51844085020000d2000a4a418490b65120b00e010b103113000964072004690034001c106485a12003035440545540f0b40301d4820406840854860041c10004116100680c50080006071007034100540070100c1c014244100100c09503a1507000d070000020450400c144586036655402ca50414990441c1000f0128441c0e807603180d42c2008050751a68410440d120020984000b00b40c10f480007100700413903426421158110001c3c5880c20743c203020011400707140c1141070304d0683e92100c00400e410040500128083c100845050b6094000d158050445081e61402003070040e001750008950b10b80090240011101e05034411400c05150040c4450717242c500f40101c0d100740c0420314200303032180c034242400d40c1010495a8213841903c2202c0201e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 333324631 1250 333323381 333323443
    0x1a0601080f25272d050405070503010315050c070f0501060b030a0608060109061a1c1404030206060f0f2b0b01080d0504030b041211060114040f020c120903 68
    0x2201c0a4095070f1446075900040c02008040506000f44040b165039510000c0e40e0110701000944a450382c042c00e200300ca969480828100d4100740c1d600000200e00000500500c400034451a440341d1310004104294a0000e5904010b400f4290004001c1d01d400100c0c00c00744030003504008050b00b141800d040c0c1d28140256420002e00851046511074004c4400008603c44c00303101d02c00480e0b400a60401d294001c2051014440d40b04241c403d515220710800c9140051246c41080d00c80100c50900701048d080c10f00b8081e142590003006070344155080b401d4400f5503140c500c0301079103001c3c045d41e602440b00e2140ca0a00b980b08601c45840e84100401c51200b014404461092812640c001d0207171801d1514035101100c0318030890101405e241c40d45c81c00300d8002440640c0d800d24100151810000c00d0833070610312400c0c0721017a4071140710b04a0300c040850756440c01d8400e1201d48800f00c001180741c022280c040d56100c004441c0e01e51100d01012400c00540c1e1000d0064515902c410740400351032004d007030000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 333325881 1250 333324631 333324647
    0x30b0d021203090111011413081603030603020a0923090304031401090605062d0103020403021009050301052d0402030f0a05010e06010b030403210b04020a020a1a0601080f25 76
    0x41130002d40c480071400382841c03040c407540111400507007241c00c041d543d240d2002c41841880c0c0741101d00450400603100c00981d00803405005601c259800708082d4234500420850500bda0409150307145050b821041e40c000040400003c2c1e442004514007030380d504014507045000710362000d0481001d400b1134540110040d0300c03016986200f4642004661107600500c60004a1904501104008a802d010020314000032800c5c20390f20502d40949401d03129404909800001040b03c404200410703003e000350300d42801400e40c820129071040812869140c0790141d61890480c0030399003403a80c40086410741d1401e001d4031b01d5282c1110222413400d141880d040d03009002e40d10716170f003140c06000008200c981043c0101c031700070342d0140c0da00c1c4444281c68001c246010800b99580c8051650381c200105c0315181c50001d001d48591640182100c03425030704003035050302e65a454545e2100c031000100542c0d680c200300c500340c05c1340340d0b1050001103944490700c040715007078041190001803074044c4140014903440303401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 333327131 1250 333325881 333325897
    0x50705030a0b180a1e1e061508030c1002131a070302010e0c0109331110020a0f230708030601110d0207060c021302030702010204080d0906050901030b0d021203 70
    0x104604821052000a485902c19540146007620845200c02d100e03580c4a184050640a0b01d1105154106d4030302c000315070056040215010798440010880194490920100070f1090300d01861402000003003c50702d03000c1007400740040c0341c0c2c00708030500d10328080c160102c0680321211805c00b00c0702c110f20000c4030329044420300318010f46c03c00f10503480d408004103000c2740217481a1680340c00c03181811116264080030300e50344c4031144061031072854010340010070164000c540c0e84510540c020010f40d610300313004c1d1500601500e5070041020103a120b50100c403100080e41145000a0406070f0302d5102c81c282003601084c1c40700444085072134801e0100d95002140591000d803182a040d101c8000e070903403034800d82403216001da0443e40081001c540142c4590058a200510001c0c5140180700722400320b8006540000040c5c1d070228040c42424401c0100450245d0217040c8410705518049004045110701e0300c407281010b032614136211582c0c4034840c0074145981e001700000e011a1a5480366035698024040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 333328381 1250 333327131 333327151
    0x4051003050709021602120a0501090606060f08091b01110f030405091f0b090d020604172a0103020a12050f0f13050a0b150901060503010305060f010b090d050705030a0b 74
    0x6030016030710700f00d8401c0700e03c4203070007011510040340c0c1602000b80900704040320755294000e6a01ea0070018000b0321841c00a50701c11903002800d142014001422a08542136890038401c41c2d505008150308001401d10b4401441582d0a880103400740040310100e00015060f0581c0c490308403035a40008010016001780c0b00240c03042009070340e4100e0322800e100010306002d0b840c401c0034081032107940083d80080054500c05030940001509641c0460040e611030b0740b088407103101c0e0a01c0340303c2039441400b0100c0d0b10400ea813801c2c240758814034105070114810f412601d040c5507000944082c0b9901440c541004031611507030410091408c1d20141c012842c04403000b0203484c4095000820390000781000003040358200d00208480d24003656000c07401c00d0060018001414002c0040540b07503954690030740079004564907030b07803a9451442c1092070840b0250040210300030b01d100620900c48114151084d8620459030506111b0050500e181031503800d40246802d4051610440309010705000c240340111032804d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 333329631 1250 333328381 333328393
    0x4120e18010614040506070f0501240f08060903030a0507020c090103060b150a090e0a061e03060c080411091f060903030e10140309010204150c050105090c0a0501030f02090405100305 80
    0x102c42c01e0f200340700760b000d0203901201c144000b0010543c2c181014400034401d10000403501c0040c82c0d1110071010003210000d5600e20501c0c10311842c05d90074032140003846144d004001d58100001896228007004045103a80e507a100c0001c1c84040c420009a803060001070299071995840f0305048014141d6900c0d894000c285185403040d80b03586410480b03441201300d60715805818101043c044032048007800407001c02d5240c0c2000b2550303004c20452900d80e82184031501042500d51700e0904142c0b050400c215013480707401000c01c40801d440b403500d842164001c54140d1a107654441c0c400400010b848030901a00c508030101160994126401c03005880c02038954a2442e401001080300700f03403c1c8004480082c5920300f505005032a01400303140c0103004003001604094481d1400c544028610701131200142070681003d007807100030300c14a900026890007501100324500045099951544103207070405580300c0c80f88000101583c1071b6190490010000c7c44941002c2c000409450880c0c042551280640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 333330881 1250 333329631 333329657
    0x40203040c081905030d0e01150f38030a0906052701061d0712090305272d0409081b0304060210090614041b0807050904120e180106 58
    0x9403081d08041c0d0b030220045140c14912032001b00906440c0034040c0f90b81d0740301d090400c460302150340d29070051f0402d1540c40c40301500e0102e401020b81311000f94180c90782d04117850204000003038480e0041c00260141c00d1542c1c0d448162594000b03284181c0064000ca2074041401500140e10285058601107a4092031070402d889500a0880315a84109071070903058418440d19007440001c060761100e85414492601d00481240c40b0940301c070392208030005240015030341c100c078181880c1c1b05450042d03684c0b03008619609001190b0840101480d04140318840540154418140880d80c914000302a1003800b070840306103410a2240c003d40183c848004800c1561260341c000001030b0780403690b0b6130f80101000c613245003241c00100074180e07040da58151100f80c0d1901c0304e210b00d1201d9000e0751141c03105941040e840058055000300c0b40e0092030745500f003a2002c00055842605880e00030350400c21400001d01503003026180502c40b01001c640045041c0b1349441416011840a4102c44e583d840d820040e000c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 333332131 1250 333330881 333330913
    0xf120307090b13050d02150c16150c0f140607020303010504050109090b06090c1b0c0301050a05162106150e03030a050703210c080405010506040902100f030e06100f12020a1e0302040203040c08 84
    0x342b882c60005413200341e02404103003079a100c182c0701c030b0050444030400304045200342e00b0b0007402c813103540159200000410190401e0301c80c243c014110b040c4100701500c090703500c84d2018071020307000522540c0a44085900320054904880c00030400b105081031100080e80c04176251007059402621a5280c08005101c08080e8000c10b84100350050031000c9201c246581076404002c40d1600201c400b144c00d440c09182d007040c0c403424024203584024030072181c0d40c440c8010200e030f4030f1050f014000c9d003090210401c0c241d0414190b660590703260805600220510034101012901c0300c003059045414009581007e5401c180040c1c0202d008800070322403542d889c000d000c2a03640d5601d0003034004151841d0710140c0d40c42441c28403082c01d5180780c0881c404080d103a8003131801000395903580c4a5070300810b003045544c8013814580300030004590340301500001e540010b0940d462a100b82c50304c04140d880c42c518041c850781914000b55500130000c644a080a00340000184018040c00c04c0500c83d5801003222152 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 333333381 1250 333332131 333332159
    0xd0e01060f060e0f06030612030702040204170c041514122d06010f09020c0c09042301110403080703090b0d0f050114031b030f120307090b13050d02150c16 68
    0x40041c1c05d040c0343d40c0b00c40c02400f00031010070910b1011804180200b20040e51240000c1c8000c0c0204287c005131201600489400c00701d020010300c1c031842c41c0c480c5a621f078100079240d5074200d81e803407100401c224282c100400c0d50744142226401081c09250000207942040d528032420403185260350484c04000c06101d90780c0c4450a0044c4041803803000400c001c1c1c000c0b16001003124a211105030303403840c02003201180d6501c000b62011220008083c2c1690350007444900074542e0144154024400030400718540c803e24859030102600e00c5800059040626000b456035200420640301e09907503850014955000030420904c10b0340d81705041500002e0704042c1d07400051030032a4000c0c0503241c1400d010b614074202c0480140081e4040c05120704d4503403002c1007031203807540c8008441c100940d07a250401b4011321400c8c03d9040b80c01511401d008226520a0b844050802e854041d42c20703030041c18031400041c0c01010f114004007614030001405080460002c03410012180d8030700e000c450003030346420301249410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 333334631 1250 333333381 333333409
    0xb12010e011a030115090504090506042108040f05010e030f0c100605010806010c0c080102210105040606080a051f150909020307050f1e070308011e0308030a020d0e01060f060e 77
    0x40c06000502c03110b031141c113682d104d01010703082c4000c01b2666400460141c1d069050281c8554000104000c1440764071049074058259800d00d50600c0c020300c0340050a1610041c01c00703000507124954078410440258031189003240300f0030880b501d40d007091011101503406280ca1100900484607000b080c0c11060041070705861050b104d0007001d0760340900450782c11814030401e440604004000113080c0000303100909140c030700e1402804100b034902e010284089c006074003141c0640c1c41c0c4074040114503030000306290082d046540102d465210701e03200c043c44100031300115080304c41040002688a2031840014040710683c0c41c0d01d01c940c0c0d914900300049000403108440801e404210413540c0c80300ba08000c041840900701450380c0ca0190a901012030f0f088407504a0200b0543c400500032208070300c0f5919101d03415451802a0b072401c581c2c80512600000c0d00703032030fa550380104241c0580760841d00600c0312002c1e0f903c02004000d40d40c1c2174903044008039200c1c4001040700b012182c50a42080b81b0091001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 333335881 1250 333334631 333334679
    0x1605040b0409020a0909110904061203092d0e010306240b0a020f0a06050609180c01052503020304210c060c02150403060f0c0215060405060a0b12010e01 67
    0x64030b019042000303507200012080801c404014045181c40d03541c490000310300c212204140d160141c41d005d010448ea640d800241215126a90303103030000b58001d03440001d84001c405a084086200d41035192144100c42012810703035007500000c14502a4041494126800344005111a00c2c00a95001c002c3c1404400d2100d000002242401b2416815004000180c5603104960b00c280741403848900307240c441d0780202ca4042d120130a001503490420302d402e07080285d4003c014440a000c900036070f5600c40b0300c100103060001c0410f8128103481c2804078441c065900d81c803070700700e084440e00d402500c940c070600568407400c80801c0d0621500c806007010603a41075201c1c0c2d80f1020942001000e503581400300c0b10899001456500a4000780400c501920003540300d1180410302d0004100c5840c00e03a100d0701d9070b8100315400f80948030b1600744481041c0f50800c40654002806880701008600d0309901a0404a403c5100095065044111101442c100c515240c12a002e42c1d032506000d180b00040141e0340010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 333337131 1250 333335881 333335887
    0x602070818010c05121c02031302120d0522090c0309031b050703151d0106030b010b03040822050d0c05030706050f0a1d100e040506040e0307030c02060c06010e1605040b 74
    0x30404040b0051a0361b003200044141c42503103903203108069a000319898407080262003102c90460a02c450015801903054000d020402d0f0803d034000c1050140800c5000030403031402c03441442c030350240a40c10151000c140284040c1c50031020160250140c800110002020b44606180b56a83c02d03a00194290b8450058040146583c5a03a1007002104207207125450340c80c0a0407440c0c1a4a1040d03280071280380002050b850314600f07006260b00700581c40401500300800420000030086801c80f007002d00ca44050010900019030300c902650516080720341c0002d0042001010300582c060035900302d03002102111a0641c468804885500034079041ca032000c50b041c046044814042c4140c0044850060344180c1c101008200059002c55044881d0f00803070049001000107080078000d05038004000d80b0140550100200030302d58170300c05e031403001e01007102c0c2072650f80865440008492844400b2011a061075071510401043d103c81503420a14031102e00c0902e4502d00d008006030790440301c4c40081d19007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 333338381 1250 333337131 333337153
    0x6020a0b250809070e1e07091203050711040f1a0d02010206060907180b19030603080a1b0c0e06091b0904050402061b0304060207092f04030602070818010c05 69
    0x2d00303504040c1640c0480c3c052240701003456480301501c148502005010400c10382c0900c00148801c25001d004041008403201c820b002e02084081400d00042d8180351555541d540c504200d00c004032503e04586c0d000b4204450a95900401c8d00f0104800030b00c01c1041c0b80400080040048102c0c80c004000e01581100c0c002459903d440c0c01050341c82a0340b802c1c240d440c1101c0408000750250107030040400c01034086080302c2e4080b20501c070220104458101008500c0c1140c0b502101401101d10040c200482070b081800c1c10a9004400c0704429031190541c0d005544a05140e24001c0003242c01c14082c8140900040440044000807071844c1243c491880c0703003480035014071024003802841a40c0004040100c5250600b0384005078520281d40401780da102c504101000742043d400f6800300e600c0314200140d00071a000318201810484600c9581810581401c2c826160a4007031544090010b51010176034005020442e0000c1000719040004a40f426885c400151140b040509000c1e1042c2d00080c4040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 333339631 1250 333338381 333338387
    0x1814060105090a0305060f0a05010e060109090e120c2503480f0b09010909020a03061203020102030405070902210c0c1917040608070819050106020a0b25 67
    0x30121809010030b0380ea2a10394a500d0718051b416981c029035071022004000706003500f440b4a0303015048803050b0041e035040c4000004c090107214000d419506643c2c03108004a13801c00c0003051800c012a07501241c55002c10b185142e11000195002c41e1001c0d01340810640001000c0c07040c9007540c2d4441e8030301e00700ba0500122503243c607181020700508000c80c10300030031041c14000c500d4102c0c4000005c00e08282d50401124156076510790340200c02c0800e041c020740c2c580741c0c0c01c004001c080c0c92400000685402c02250201d003e4502540011850000c00d803a12007407541c1900114480e0b0b001d402104c80d2150740b80180c008910a0044940d801c3c4e00103012a01e81c515880c800719000301186403a207041130705c1181c03038030300340310f00320000da000c0c040803808441c200014001c0d54030207844100515401d0500e400e1024000150041440d0108400140000e1034070b40c8002c3c00701042946458100500e40c0c40d10400395603010480800d46068180c4000160f50b80b985014060110190100c41e14008009030015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 333340881 1250 333339631 333339637
    0x1d161a0d0f090b150f030309031e2e0c1b060e070f08030d0605060a0c0f0c09020a0f03150b0d0b040e010207080717030601020a080c160806011814060105 67
    0xa403201c6444012542c0441c40420109000303ea010b88885022440c1e081003299182e14520090302030f800030321035004140d802107550210074071941c1000080120728400c00d800d02c0c2943c1c00c4001209207503404442c0c80e4407031040703052912940310810824001c601c0000c0e0f5105642c0380182c01440011210600041c82c6500304090582c0c0305000c4407031103512050404c84150813074002560540c00812860f031004e40d903000e041c00414064598074500020450002d21036914841c0182c081c1c41480444004c21100e141e07158000c0c40310301000c640301c03034041600921003030b280b6440d10002824224004000240c001c1018112406c0c2075800b464003a080c803540e8007814100400c59801680e8003c501c001100038001007180343c0c402c2402c143d99101030b10b00307508140200502802d0b4284148100807099030001052440701ea04440da0945038616000410703d01940703c640d0030001400f03440000f4000e10700152043c140c407551010301c1590211204088112908481c000f00380d5000500814141e500031402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 333342131 1250 333340881 333340901
    0x20f07050a0501032d020d060909020901170a050a0b310b0c041a090a0605030f1302040902060d0617010e030f0a140f0a23071101031d161a0d 62
    0x8145c2c41350301c01d1180320b117541011a191030b81c1d0342c00142c0450080014800d00c8c1c050004100104111655500400d5034284140500301e440c0f40c2d00385400e146540200301c613140840d84101103500b503040d03034a01800c0d4810207644111072202d01c04900300320300070640102c04112a04260484080100f503c5440002e400074100308101e5108000201c5c0d810048104c040790b600c2484105d0703558070850028080c06440c0c075809002080350a20038040764007403162560390028248100448240c2c02c81c00050010040564025800070b070014003c2c44400858004008645500c042008021380b10a0001e0917a4074025440d81c0b0f42d0410844d46103003401e184003034260200c03289454000f240c0140b21621165010030030b5503541d100f0210301c40c00c410340d0195080b8400a45194101003191003491084428000c00c81d00604079203079106000c0301344c0d129a000d0340300c0740b00640d004020800039084413500d60944400c0b113080000b0742c41c8046211194aaa4244815a295466881c099030501d1090007082803400d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 333343381 1250 333342131 333342161
    0x6080a030e0f06070b091009150207110d0f060f0509070909140f0f16050d200a090204180207021c0503072f090c0d020f04091803020f07050a050103 65
    0x700c101481c0c4816000c4c28030644214502c0103103040c5112054901024010b0000e01d141c101251000020b109192403814030b0700941c400741e26030185142015540e1001141e0700d4002030300d022041c045c48034082c450303098180944410000070008072042c2c020390358100c1d203405159003d01010800040303d40d011084040c0a1002200c4007401c200c8032600744403044820304c2103a032000c004960303400020b2200f0402d025000700c0f001070045c5060049840f135207440e0130107000002000d146840b9404204003242c0300d60700040080741100c0d150b0015400079045070041e0b02518100f0f100c90b010300344403031084403140d6400414050240c114414403003951605040111003502051000d140010055180310419040c0000b000c1540a40201c0560729520804e500c140309417140000e00c6045882c00d01200c0c00c1c00d11012000d691400380c00d5403440944034540c0002040342c90000b42c8401406980b80c240080380c13007a42070300c141030700c4882219650300e5907001e000e0744524101c104021541c02980300400b40d00c011a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 333344631 1250 333343381 333343399
    0x504140f09070504061403100b03070509040c02031908130b190e1b04021801030c03021e040e090f030301051e0409050f072111040e061e0a06080a030e 66
    0xc046101040240e03840b0010580c007007014012540c0101c9400700c02103003065594190718180300080c60394403840c07084101c6004008085056140304500301d441505c1e0203032042c4030104443c5802940c039032001280b801518261b0340c0380100d85100b507070310900840300811155404030460b217400d802104098903450034820300201300c0d107010141d4040c4071416041c0c54064400403003000720b002040d09002c64858811441002244810201d040320814006801e10700083c6140d0101c2c0180c00a109401c1d40c440b92009404840040260660050040d520303000185921a103502040507618a05525422711a40050006010a040c0640c0428030380040e0202c000c50340183d40c1c08a82100c01d500fa040d00c1c59080404000c4104c101003152000a00d00b050018001c0300e2038a54220a04078081c8005008441040030092199269000700001008038010345200d03090807130f1481440e540101c1c41c6001c841c082c42c0091400e00452041e00d04881c081c001070400c90000c1c1d5022120040c190050303030b500c20804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 333345881 1250 333344631 333344659
    0x161205060f0a030b070e04020c03030a090c0f180f09020d32030705060601020613080f12010f1d0708010b1b060903120f010303020703030809010e0a030e0907030c050414 74
    0x204061801140100c29031a0f031401c0c4030301c0003003110381c0b0b01b440540035070300401040d89140030000c1140c0d031049605c3c40c0003d510300c2c00c0c549003031100c00d030b9800105400003a9402042c61940f0000d038010b00714600d0803c21034044210b042006460005402950144460740240b0105022050380000300c1c1c29210304500c810400078100001501415006805500124489082042c20000c00c0d40211b001d0000344030600c0c04a481202310107603000300400c051004940070010107800c10594001c00c000d902e840d2010741e120038054480404520070000981032480d019921100fa54103901d0064001d5502e8050980c208511449140d020f40300b541780381100c400f10301011400a0041d12f002c0c003c090007540d9a05141c507059a464400503001c000c0b1001603074010000683c000503030b0340840354941428000c513038449007894014a6462110113043c055024200308255010035404e4080b60106c403031100725261030710b0031400c071114110024003081c0704100070300007070343c510f00d041180d0600104a6813480c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 333347131 1250 333345881 333345889
    0xd03050f062d0a09020d050f0c040605070218070206070f140405010302030c0909150109090b060a03091506030807141f0b060d02160c30020d02030a0c0608161205060f 73
    0xd95101c1341c0855400719903050f0b0315070b041c01a1385d00075910303040e801079506000e4009012842240f2403002030001c001001011074803a0903080848440c0309000700b40c0c5160094010f51241d404030f07807140028144100858019010740c1c801003184c0754a250759418036081c140154000e52001d41001c030820400c0c400b954056030780b10349552050459094910800341d40030009080c400158111143e00c03800c0061241680d10354005840381d0903258540415045000d051035035034400c0310a00d009034141442404001d01501f4002402e106204000c24850964106601920b55012900703481e40212241c0c1144400042d60700898425540280980e2400d100d0451f00f0049911441d60000b60101d480c00100a10007031208500051015100c2d401d1140700d07600c4481d4020036031010440b1a61180310100040d0f4079411500141c03e50b0140441300c2814890a0140b4044110f10a0100180d00100020264940a0b039000b008100907202c503040070840291010140074014031454019668242c1d024113551 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 333348381 1250 333347131 333347149
    0x4120c060c0e0a05060a05090f011103030a0911010512070804050f030a090306060902070b041401060b2a16030212011b0c06050f011211150c0d03050f062d 68
    0x6442d140c20406440d4082400321008140d03012602c01c5030140804010300c2d4000741110200c020441d0412005030303e00c0b006803100fa507060065401ca110201c2000341c01111548000d5400d401014800c800110900c0119000c0c8640840d50207001c00d101c000c81c1081e40a81c1c5102e420074856800c0d2081001712640f00e624582007005400c0c0005c2c09450100140261403240b0320149c16908415441d1402c40d07200c400c8640c00240c802400c2c0810303000b0000000c0c0007940803102130030ba82050744e80d5550412884400c111001a582e08100303142c0131020309440740005003208001200140032081c5442e5408200c0480079001c442c600307a54a40320ba00d10124000182d019181c6c0294403480740c1c400ca607080c00811104010000580c3c2404003006104400c02207a0342d4103000d50101c2c80c924500290400b10300c0180d41905d01014120380441c00716811200410f4045074600c5036a01085140d90f01d42d48400c41e50b005944042e00400160721002c41d5090704800503080c1c1c41d51100701c96250301e1035408208440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 333349631 1250 333348381 333348401
    0x904030c080a2012030106080403020f10060501120902010f03090809120703050d020f0a080a1e03050105030c0405130308100b040806040b0a0506030c010f092402071d04120c06 77
    0x240001d00c8020410803e894890542080c6000a00c207484241020814900c410b000390014480d0900029040610800c40c0441f07800b04c81d0140c0d5032411004400c80003030000f0f030003224041f802d5410107e2820354540f04081101e5016075924044150b0b11400780d0003440c007404e003940c8120081146a00039220080079101d050448401040c2c07040c55070500c103050a608080040854100e000700140442000503c00200f80d0003006947c0d50351001002079031207c12500340c0c2c81d0b068450700081c0000da0b8041e80858101d8000703809844c80c0c80303039010400044900496a500c110024084600c000c2403040801039400740f40c80002c2410030303850745601d07a80e942081d80f02d00c180e940160204130401661504c810741000fa40719042c400c5007440340001e40c840c0c0841c450035040050104240e1503451045000300e0003011660003081d418481004d1154810703043c80c1d04d52005d48140f680c0002c00381e4070381907010303034a000001000029813910340c3d81c00754001e4034400520401140303103100f101040d01ca00c03542e001e203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 333350881 1250 333349631 333349637
    0x3080f0705160f0302130e0610091a01090e130203190c050418060e030d0c050702090601091215020d020d0c0206060105041203110a0501090515010902031003020904030c080a 76
    0x1240c20385401c51600125140d0190344082c40e801c00c0000e521404003010699a0449403821391100450f0400000d0001c40e0503c01c2078130030042032100540004404500b610708400042c020f900c1032400c0c0c010b40e0340101c0a6140000c1354201d00700503842c0d690f090950000101d084008000d0310a800003490007400003d4256500390045c00d50041000c1c401283c0001c080c260707000e01542d1801021000007045d004006003940b80c03541c1c0121840780f0140119506400f280d00100110202c000300204a40c1040904a000c1c00170840814115030044800408885256038000e4010006644604c0d041944d0b190b00d1803195000d2220603141403490014042d6110354000005103482a44d1009141006c01351071607050143c20001400b603a0020121941101d4040c1040032000400c2d00e112403500c200800301800035460074444400f0800040b0780c4500c2c0d01002030f6034003070794ad0701c0b585498101d100940300d41d00201203803081000142002042c00341e1140c003900381803084e154191120070596000f00b201d4400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 333352131 1250 333350881 333350887
    0xd0914040905480108150307030605090c01021b06030c07150603061e0501060807110a0f080a02070b0906070b09030714070f080a02030714131e06091401030b1003080f 73
    0xc0083c403400b003101c4031101c03030b2414000c095000001802030f0034050400e250000c0382d6900b076401034404002003070040d5030101081002e45001e0945941b9158236100c0c1c0750040c00b580c44042070220801e6540c21414800401592441c1c60b00308480d4250b81c4860350444601440880c844d1004c1c003288282d00c01140117000c01f0402c6c5494441c60f1021400900e2816105481c203001884003d81c05000315521820500300303e00030511580ca145d250280c3e0410051485c400700124200300a6880d02601221003180c01301d800160701d03a84410518004d1144c003680103001400f03900d0105000d00d03010380e005900002541c3c07600100d600c03001a5105030030560380003a0300001003004985920305c44940140381c0c0101500d60443c05500103a1100c0700c0380314500400080140102c0300c1d554202610903040030b20001003244490200c41000001d040b03240318540f440c40c00c1000103d888680c014603003920f0044d000e19860784c0c21a41c0d000400c80c0040d151403203c110082e00400001c40d8100103004103645203103011340f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 333353381 1250 333352131 333352213
    0x2010c05010507050d270201030e2107020109060c03050901050724060314010c050d231501030515100f03060f06030204080618060c0d0b0418050d0914040905 69
    0x401e91745401100504101c5000c1c0e4811850b001501c0d42003007507030912700841e444e0441448645024034810305a140705040a07490030b00840110020041c03d0310070b0301c071000c04507982d070410307140500341c000050301183c010803401e960366218030000d219540c80b4007a40c0074010740700010301851000416400300126a01c200a1080c031244681e034210740c1c11903800911140454500041c058003806d09962074194031280055039a00c554800680c41d0b03544c0c20700f1a4800d140048000d000a045000d800780070a280601041510300d450480d0341740104042e04840d40c54102000c120f0b200c0d070446000c1020950b4915022a48500000c5003400401c0103a40150302c40b81005c1a06050140280c50030704910441d600340c20307150f1804103009a208507050483c1c0d0b01e0b83d000d03802c0580a49001030300305070f1103868034201e0205000126a80d01d5840c1c042d0044489d030003c02d08055031000240e01030000310010658000c8024035041d0000c2d90194440c40c1039403003c50807520500138024800042480107654a04008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 333354631 1250 333353381 333353407
    0x1107060c02280c0b09010f030e0304050907080a060f1a1b0304260309030d080c09190305060f040323271002120f03070e0a06030c0f0905100c02010c0501050705 70
    0xc03010300b49400d03e44d860f00103140c0c0080c0550159000708014151038a0040e101d51006006a070018036001c2c1c480c504ca403804c01c00c0203240c1c1500311819402a4601100420040c440300070380c0c8140c1d0981502002c2001e410400f42c0f089400c0071003400000c041e40314014906032011700240c030007090300d40501d90b41386000701e000c020a1805400075820a030b00c244150000c0d65400200e00c1c840705c040c0d052054041d01c600c1482ca0503480b88500b019000f01c2c0303004190404d001500030300c0c01140d006200361604c03521958a81c41800ba41900e0140005100c03c001d210354442c8880101941c14084c00002c5c508072000210b2400d00d4400940307580081c0381c1d000c005466060035101c16080403401d00c003400094503000c03406c0c10782d406115001c580e0001c000c0001480035014026070100040c0040c001428681e48880c01400380c0203000d014000218030301038841c0d10a001e5012041034910041c040440e4000d1968200c9808c04031000a81c1000f910f822030310b000ca442031081c240103500ea0ba59440c0c0d5022510b40708 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 333355881 1250 333354631 333354653
    0xe060a061715041e0c05013203070201061206020306040c0c0308011505091c060b040902090a020d18030801080d080411011421040b09011107060c0228 66
    0xc0d000006490060030060000481c2d510034070b8070315112001d000d44036400d08807944014410b103030481d40074102c1c1070010b02c680da080200844809036540107004405407110890016020750810055603181d0010301030301d611002a5600201c0c41c07000150b0203039620080c0e40c2c040144041035a655a00105100c00da0909004180f030030800c0b810004640e685603503008010103070521500c0e040c0c00004100400700d91140044070820a070040a86050310368030102e2221070141c100c000c41d002d82ca441d400140c5400c040c0140740600350020000f0307045588000d807980195025080364003103190b403403403090a50368590844400c114080d0380c0e20074856060101282c90320b04815034840034404070108101c0000d4598541e510040002e2a00707002020381c03890622040c0c020118020f80c0341c115140c00d00d044c04d03e1581d035940f08900801400c0703c1501c035412550300321070080d01500da001c0c02c10007100020880a80140e100b2010301d1040b0348006010828160410a113840305450108200300d180303003407080441403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 333357131 1250 333355881 333355889
    0xf09030305010e160804080703140714012703030e0a0c030f03080c03150f0d05102004080604021c0b070e100905090621061f060f020606060702040905010e060a06 71
    0x40c001020304494806805d0313840040006000130030000f603140c02c1500c240800f28040025110850304c6d40d03101d1500c00d00c1800710b00c0241c0241c3d0b1a060445260b200e200b20500d00454814000d404081525101100644007005600045104820128000a40100b1038000039802180001080311182c500202a10000340464000c08424020320207105544071104501d03520031a40710780d20074004008140c100b4240c00c405409405990f002000140c1c154104103021030181d6580103070441e41103026003880c000c4d03010705540c42d800340c000a00141070a9201c80294021402c1d072610b185410390f900c0c4040030b001c40c1c0002c005540c04686040c1c80c10600b05049403840306040c8641c0c0d1a09000114403d294000c007050320540d0175242036000142200d448048400041d001d0f00d501d46001c0040c600d004101c880c0c100150551382d200010b90700c0c8140b46014101203503034060030054460000b0010241c0040f0401d13a8041c4d551030b1001c0020f1801d00c240392410302907402421003403401003c0e82c400c4600741c0e84 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 333358381 1250 333357131 333357151
    0x501021215090f100b0a02010e060c0c07080303091e0a05010903020307020108070305040f020f0402120901060e0105010f02060f04080412050d09050607020f0402030405210301050a0f0605090d060f09030305010e 92
    0x10038001e00c030805844c21025244920700150315541a800e0480c05402500c0700300c40c150180500740300303801080380c005000000d0008111880140c0d101d0245540f840116454100780e0055070710070b80f4101c404248141c56881540031100302500d01d80f40c060840d014004210003603840090441c0440d6003006071a40d01515a04042000e49003e80b1424502c1140f048024030031b6244d890704200e60ba03500c0c3e0503036515000354620006d65141ca203028900800e064019580600c904100010740da42c8203294211040714540d02419150710755041a00170071300080c204440702502480082000080401c502c400f09005000400c1c8035580d00d540544803900c560003140c09000100034400258031402c1c0404002c2c90141c900598a46e69410b0071400c040b0350300c1a02040a88401c5141c1c03a5121440c0a50f040c0c8000f25009050755940d0450402481014495000854800d01c8044c3d0341e0701e082003170300d0340c6280a030f0b802041010300d000814040fa05241c1c0b00b00c010035514001032116845941249500c000001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 333359631 1250 333358381 333358411
    0x8030a0215060915010e0a0b04090905010f050c160201021504050c01120605010504050f040b0d0b0a0f020909130204090803010f06020f0105070806130609020f07030e0a0302100309050102121509 85
    0x14000d100b1389195040540c10702000c0c200751246505e49100010042c01068401c6456546480d80000500380c181c40980d00c0e5820308504003405d01c200c5c8512800b0320450141c0900c0e2010041c0000701d01c074110079007a4154020014445c0481c0d90dc10155440b0310b02c103070042d010680808001400710000020079040c070601c0c1403000d111598100c0119015107604813842040c01038401d000130050300a01e00c2075034005c03658407002c40401c241100002d000344000306003805100c1c001d0000d80200d0280302940b65021600c140402c0d8140003410903284081d0007c4c0c03010802a0040e03c81c2d894580c805e90042c4040850402d08001c1030f6414400303d40858410402071041d803d00600080c080d603400b030305441c8601c001c0e08007101c15a0b0140c0c0001e005192400095444881002c942d0301d6540110500b580030451401c240c502a140001183c070640341e0082010b0380402d940e910031401414500d4003100c00399420000d40801e102c005062500c04d20503969500050085c1c0024006008030241c01141c0441501c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 333360881 1250 333359631 333359641
    0x1e0d05130506100503070612150f081e07060503180106031218030b01050405060a090c030f0b06120115022b17100b070c030f0f12020d0c0b1008030a02150609 69
    0x2145080480300c3c1498a50300107000000706400812840e1031030b84107004841c0c000202d649002000c1c1042f1400078003510910091a502c0c4100c100960642000300e40015405100d898000d038081d503040320304600701078018142040e03140d0071100140c0050721203003038001c4030314240c40d40302c01e1407020304004141c00044289160786408000006016481c07049071a0b10008001d6169249120300400d0100c90a1000301c4680d480923005004e260440203009085c20b0240b091070915204840d61100c1640c40071030168604600c85d81c4102500e80700d1011809543e400e0240c004a003c03041d40d02e9482511680700000600360090040b49003410708801c2845c0190421100c05400c00303010301220704441c3e5041d5266180e20300b055586013541c100a00c000c2ca07001d0103d0501c040c0080d680142445001d020105551411099903500590b030a5207000825130109030b40001d0281c505a5040440000d6130a100e945800c507041c115000705000b100141d100c607040b2030080c80c1e80c042964000b039043c0e550500078246 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 333362131 1250 333360881 333360883
    0x60609030a11030309030a080d051803030a0903050f0409061e050a030f03051207050319020c0a0602070c03050f0d02100b090c070c1809050c03010c051e0d05130506100503 75
    0x6040c802402c010300040d0ba40c075540c3c0701841164031030791008047d501c2c3c4509034940302626400040b102d550b41c2c2d14110014100d92201d1070307910007500d0700300001e5055541d141480300181c40c440000b1001c0240500007814440c03100c40180014281c8241c001c610142002400303003820880d405d0302002c0311750310081042103807244504202920380044828400305800e040c1511580308100c02d00c10501c2c88541088542030b40800503500804400300c0c001c0300086000545400e900032041052040d800a001e404000786250f401010384911070300d0f201e401c8907540c1d100c50b418106000310f6040300c0e409c800e1070060442c0e4140064041c044040ea81000082ca6410100d018404000c1c40c040700c240001070038906000b1001c0741c0700010420800c0754400d001851241c0da000d080102c904450611960302005c0d1140341c103001e94841c00443e59625800e01c07201c06c1d2a900000907180400840c1d00c1c080002c03400000d401d0003802d20981d14241c0720000c600301450301031b140801c020300c074925183e001cae5014005560 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 333363381 1250 333362131 333362143
    0x3011104050d14030c0a03080405150121020111030d091a040b06011b0606060e15090303070809011803060b0f010201090b06100e030609010c02010b0d1e030302161a06060903 76
    0x600020200015007054203c0c500d1440b070100805c0b04c600c00c05524a042691200b00544514446d00950300d8a0f2020302040501e030740c1c2030040142d404030000d59050f110498408800001d40145080b44c114108d0822490550f80000f031032045143c1c5524213607040c400000304100745022070404003140d03440c250300c91512404010300054100002010059004128000b840144d80c0d0085020072515545080240120042442007401940600a9039490300c0700f940c01c1e20003904014014504c1c1090351340d210700882c0c0c403469102d4140328890308541e6464142c40031080c06188140d600148406000c001c01200008080c83c1ca811a03060858140020702c42c1009190410f10998118084003043c80c000c0d01d041c0c2d69540342c150540304100800a2444054100781c43e00201034000b0800c044031081446100e048070361000d05500d6043c40226240c103c0d0324500c0001c030f4028a001400c00705924924040c3d82c00c8114117503050807410301050300c010488141075801c100215051031802d00c200c2c0200c0c2d02c0380 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 333364631 1250 333363381 333363383
    0x5131d0312040209040f1a0405010b0a0602070e04030203040b0d060801060b0405010f120b060a0c0b16051c110c0c12030a0c06050603190323090114090a2303011104050d 74
    0xc9884020400b001200c003d042d07005a80925031442d4807108003a00c402c607c0040318280c61942c00e082004040c0d00f00144ca5100f9129a0390140510909113140c2c0400f082b0f000e0000c03011848208800180842c1c0d04000e003c02450340c55000c24000d01d81800c49080d00e500350000741d40c0c000200403c2006a801a010104440540c104010741034400800580100524500d19420050008400d29501c0d0f116546c884054454035180200b500d44190404204503d00e4258000c100c00300000010f4000061640355003403441040451441c61808180100c0e420580401505038440d540003074852418018003081121003400460600761005030040c007507554031002401c040d5460021032a40c0e00c090040c001c4e83c800919032030301c17607580710b1a0042511000c21602030b003030400c00b0340e072241c0b85182108031004400c05031750703110248000421001c0d0076032002d851650f12018400c0002840a44655030054100c2440c01802140110600b41400d6528900c007034050a8170401c0240419500c08000420b05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 333365881 1250 333364631 333364639
    0xc0506030f0a0915050c0901030515101b17030103060f05100603090302280b010602070303021b0d170301090e030c031608040306050a060f080c0102100b0a05131d03120402 75
    0x2810b03540c04e0064200c1601c0000350185420301c2c04016540400100810b600c54080e030b000c000c10368443c4240c41d80f00a020300c0e0903a0012300241c410700000d110b103000c030310840311082616068100c40d9030fa0680d80f1f0301205121442c0d40c40480108140800c0f0710460302c1c5c02c98610024401440e2100d4440d030607000e030340940400c2c99942c12468050510811890010081d0009440000d0000606001c601d81c1000000c5403001c20060010070b500b407020444808996154000700403050000341c0d801030303100c0440021508840c0442c103103400704080030204064007101d401415503a5041039096016540d030381246521540c4100030010000d8400821102503180d041207010b000c604907c0e10b42c200e840760342e002500342c41c184018803c2c40f45a40d804681115100200880c80035550906c080d00c44103a4619503016800c410200032082c0016048034484103c001c1c03c00c2d06550f2a200002c0c440c04000c41c0341d40801c2d80d01c080c0141900408051042441d420900850030102c086001602d1014018002801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 333367131 1250 333365881 333365891
    0x504060f0e0606030c221802041d030a080c12070305060112090b0408030406062c0726070905030a051c0206061f090504020a0807090603050c0403020904020d1407030c0506030f0a 78
    0x142220240115038840c800b030824840c0c4056507607250b01d803000c5407c081e4450381c546150b544940310300101600002d00c00d0006035042220118003925040d6000f442c0080c1160104076010f4058603a1000520901094030005060700f44000010700a083d5954907030b0720240382c5491200480d501051050b40294425829940c0780e5580c60500080c08040e80315907140e02940e400c2d20f05868049101c5a900070311050048213a41c0c448004650300700341d030131015914140046002d20544001d40005030b0064190034441402aa030718080303031034035004031420344442e0440c42e00d8ac8501000481c160008903c4d0344001c10311802c0c08000035030300b500a042218440070011003030076555409404020002d000003030086440f042d0026000d0070400085808a0001e0880000030400070b000c0c2c4034450054404d64401414141140d092280c0a64054402da07803041e25000340c00006403414640aa045500d0009010400e18616101c201030a40760400d0340701d14002e00070000c035050840c5130298846d10010000c28 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 333368381 1250 333367131 333367159
    0x70b040501180507090e1501030204020c07080d11071212121104300c18150815160e0d15090303060620100207020604090504060f0e0606030c 62
    0x401041c2502c01c642107100d84403055018407402290341011035081c40024403407040101a050b40f100e24003030b83c0c01220a6110014009800c02e81d003c0c01002400c10115030040e601c4065581c6024024800c0c01c0026152400d618540d001c00d000d0040107103032170140d00340200919680d040245900c44806020007000420f500d81031180c5401c00c003a000c1d445014581d440341c0b9100b5203962a02c4000c5212841c00780c00580800c26244945402d1149402030702c00c506160400c01802003c0d4101100b1001c07141d11001402d201000c480d0382d4a004040c040002d01c3c00880000b011111a00024140406404403035a4011050740140d0049200e010482c1e035074903800030070b01e0f260040e103041d91091154a03150142010425401d5030161055031643e803580e071590680d41010801c085441242c3c034a5075008101044508038550700941049440100000c1c200b80e114908481180c1e42201c0c29141d1035221038049081d40140c0c40340081464501010b8062441c00c000400d84d90402010400d000b4194210005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 333369631 1250 333368381 333368383
    0x3061326040e16080f0601050307030e030c03041706131106070602160204061203090b130b0a0201051614090111120a08010810020c100c12060b0a09080c0105070b0405 73
    0x440440389000920785031612006402d402490440d44085140340004001c00d885000e84c107031510500100e10908070507694000115a00d400203400c0c48141621202c941401101c2803000c0c0031301e038940500540d110f61a0a50803880b020003000c18000a03040382082c4500c40c140169440c419580005648890034003c001148452140d070070003401140c8007080541e54201c04049806255008903006c2c0300d2039440710780c0441c41502d0200005c01060a20800700700d800d0700d1001400091045160000065540c2c5c00c1c030790b401e0780c807040c21400141d558000308419807401010281d200312051505446888800c00302c55002e00c40c009002c0e05212803403582a80d0540100550740ca005071745111540c540e0368851010346500030030f02905085005019080c1003001e030610940b262030500000810041c000040701c44001d281e00e91404080000e0402e44c0b48c04d003605c60051038014118044401e54440e13072001c0c024000305003a00940b030150895400c1c00500d80c0e01006a824054010944e60802c0e21070b03140a0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 333370881 1250 333369631 333369683
    0x618050106032a0504270e010e1b0f09130303060b07082b0f02120603060402010e120a0b040305042102010f0516020307170f07030c06080603101118030613 68
    0x821030030000d101c046c0c1220009000c80c03d000340150700042c0702e10f0801d0358a03a82030b2a401196083d4030b5019141e003c07016001004044140301000d0300f044200c00d2890007240701910221010060414121a540100359051150710000c0000c1410241490590781d200031040c03081400b080143c1c4400a89074103205803032080800b524045c0132042014010145000b0065000300c91082c0402490a0018940c0d040110b03c0e24401c660503035544840300e5182040210f50240300c2d100c024207118841c2e008000030242c0b04018051800b9460300c989883c81d0842a2101c1964445000e0641414104400050341c114072521030090f458103180340c887e0594030043d42e05c0da10400d00654944109400060000d00c10b41d403c0302d0307001410003500d01110004000301d0780d500d481d1200900b10b00d0f4481d001c1142c10300c42c051803900014010b041c0d840384d00503550314100f0341302e020390b26208968000030300117004014001e8a001d0104141d018202c0d0385480303100405013411171003015105a61800c03408800e00c00d1418030b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 333372131 1250 333370881 333370889
    0x4090f0f0905100b2416080a08010e070f020a0b090c0301020d0204050405061f120e060a0b1207030302100e190303020306011202040b27040618050106032a0504 70
    0x20030540180b4200a07948004542c1c2d0600038510302159603030780e81001d130200460000780e20401c1203207401c0f40381000501d90080601d003071030f40344580300d1000140824000b003565400b16966040154108071341d4030110310005e041039040c88012680b40b4101f0b0740100d0302030f041036041202c11080d9921442580d00f4074400c41b0309654554070000e0305a000204a50180041d20420340e030400003541c40400b03021048100d60500c044400008c5c0c2c0012100b449a480382d120341c04942d2001c90449084822545028402d9401c014110340704d80c200d080c242008410949440700340c00003080707070a286460180d103031100d03400d203002c2c002e4590b9070300100a5070400200ba03103088182c600003a94542f83c20010000d41040e0764550008a0b0301c03048001039001802a50300391080c45c02c03068a0120030501d90080c905010507a082c00c2d01c07845d40740c64844d039118403a41e0001d014504c9010700001c507218010b802c0307800580000c81490700c2d1002e804400440030200d29091840105000c0f8452080c070740035105d0780070b40e0380 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 333373381 1250 333372131 333372161
    0xe0a08070801050a0501050a05030307080a0c0b010e060f0102060c220b120a050c180f0a03020619120c0c1403070c06030e0f0703031215050d0303020304140f0304090f 73
    0x3000061414055000510030028240b0070030071a602c0e1810410444401d100e03007030b807541c0288811004174080c0001007068201300c4c24520071452450369050703a00c0100768885a40c0303058880c204480c90a11800c4810800801d10107400149400c94003020b65018002c40e60000101e80100c01e43e408aa04081d500504410784085442c1c240c519801d541d450403c8542c0c0c1201401c04c4086004606071800781c9445c95210541c1c1c8000301c1d01081404a60300f0f000d001954001c1d58408000096101e00c8000c240d401d09107031060306000f81c180c00c05481500540d105e01902440c09200728411a8094111700c0051f0b0300c04000c51325500e601b45151320354007400a020709602d00e03d079400165140c056003c0402e0340c51071000e03210b452010751111074403401c0b03501c0060045070482078008000d600660111804c48528a0001c661680310700220344e40e0380d25900d00305d001c29400030038070041c4403e0b440d05038040d0104a0050105840441308103403240691310a40260603201c451142c40c3e04580e400203022010400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 333374631 1250 333373381 333373393
    0xf09080d0e0a050f030a02480d05030c0d140901270609050108090a03020607050d1104030f0c050a03121b020d150507110604021e090a060510030207120e0a08 69
    0x100c1e0039034032580b28010a502510452242c00000c402c05805012304c4000782400d482c1c1a8800b2000c14803101800700340d03100076081a0342d00710031652032000110b002800341005548410b98002200d2501c80d004600d034080c0b205001c03450b1200100d071350485040040a2805d0300030741004690440d100341c5040403081c501c4088400c04140f269000928004882c4242d840c18a0307a1030b60800d150301c400d041d0001800507000f017000150b556016a0051511400355540016582d0740d100c0162003c1d0003a42044901ca01a0f010030300c2403103040700403480035000440b40740000c0da10b11b5481090000b80d94000c0000d000d0072100c0500c5080c881d448504075181c000e042440455614078008484820904040403290301e00b00c0402c400c07511030900c99556888000017489103032126000c024a2180c0e02410700012003241d00d0003d40b40d1a40310049000b07012000000c90014100010003021080002c0304804241c4144000c0c4042803900c0c003194408030361814144513640041c8040307103844c0e6458000341500c1c4116 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 333375881 1250 333374631 333374653
    0xf030a0f11130212310510060602010216030c020a0b0403030c051002032403032101181109040b0310020a050901030605030609060f1504050a020903010f09080d0e0a05 73
    0x10403000c42641c00111100d5101c6911807114400702c1c096006030500394050200094034400c004c0035070b01c81003800382120040d4003500c560200c0c6502034482c0100d0f140e82101d0244100304880d4003404002d0440c0e80001c0d0700b820f240b00c211040901518801504010b416100d420942d121050240041e10454a103181d80315103034100581290603107101210709209520500e030140082e84203030b034002d100340800311910000701d10342c1c1351060a10911540e450b01040100d41c0003020b84c28240d00003048410306d040c40310761408034034208003000d454081d050281041d0201e03c0362903004040780e11441041720005150b103903002c0828a040381200181221a1001850640e201d0304817010740304c000c070242c0c2e003880015124002d2503140c50007901c0720311541c0c0c44040455009020703000400d0384010700a400c20948030b904c2d400902600c4050b1100300203154001350b03950079410280200c0c11081c1507103405100c5c2c19103641c0c2d50020ba2007100c05413800c1c59501c83c0c0c81c107110b03541400800c40158001d01251801c44103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 333377131 1250 333375881 333375893
    0x1153c1211090708150d15020301080c030d03020406020715050d050108060a0b04061818050d0512241302120a02130807080a0201050a0c12090608010515090f030a0f 72
    0x101c900e0040c401d4070307030000003802c0a2140780100c3c401e0042d4100284202111400e001c15034403150780844041c00c200c440c0641e000e106102450080040c94001c002103083d941c140760800b07003031800e5401094010031041c0701d240d0f000690300b4210750200b003004186105003007040742c41c1d020700280304c2801c41c2850000200641d0001d18903000d07103050b4030100001c0711800300708421191248103610001c2800340f090003600d02c1d42d5214000801705000104040c44440c3c0d40d0742d0401003640c640201260011074408582506a55016805182d01040c140050b0034406140e41e01d003145100c66103c1c1118107080c1ca1284415010381d070702c0c058641455906810003c9a240280d00400d41030b41c1c4412002c03170002490003002400381d089505e000050301e030440c03c5400460f05980010f03d031030144070891030303a171000038a9910903105050550383c501104504250004090040c1a0b110b10310902d21408020716401000b0201c0d0b84c80c0c0c2048506031807040d0b00e000420304100c001040501400202c9a900c01400741d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 333378381 1250 333377131 333377153
    0x6172a06280212090d1b080d0203040305060c0a08040f051c020304031e020a0909050c10030525050a1101061502070e06091509040c05040e01153c12 65
    0x2100c1c0e0240c50303070b010300c80f000700b10603008113401d55a11a4110b2010000316a070a42000507a07107007080c480d280d89450300100c40c602185c20000e0303c016400002c040081c000d00380280341e0040c4511208071b151081c81d4030021f003150400340000d0b024a41c1076401c0c0c4100103082000c840002025454a4200341c912480a501c980162005460754403902110349810101d207a420f01d5000e60080c6245460b904001955004113080b071030440743d03442618022071455a42c611500c0185d28513607404590351804a6001400f51603000407030014ac03096190040090303802a0940d502860285440600d1450ba00c0043d40908034552041c15806135241c004a0200e0303010650707900b42d0f644a0520407480e12240c092200a550443e0314150740001c4045181040c5050401e01d9007043c002c110070b04115440342c0005013109e140c60400003081e0354591050100903048101d180c0100343d2240d00b8201d04081c1c1d000c41102844d00c0303012071300c20700e045186480d0a1700c10380001030207000d0b0b40703550304c0c00e1020903c1c014412103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 333379631 1250 333378381 333378457
    0x9050d090f0b2503030e01150306180209011703070204090c050a080609030703032409050a06060305130609020d0f08270a0b0c071806172a06 62
    0x1c41410021800401c080c0c1101c0504004070f1107040924209610100e401041d608101e003055210624001882c5003400340c00c0554021112a04045156103071900c01c03240460040e9448681301c00c1c2d12000350b9241400319044818103040720350700040301010315041d0720900c04003d42c0189080307014014840304801c40c0090341d1042e10b144100c580c40d20300ca10b594043c202c903581c401c2d502c100500c41c0005d01c6074106d4010b0040818890101c061501915618514a500810350042e694400c0152100b12402054018159818100420b0030103681c1c4940003d000743d40900071b6602c51001ca404c5480320000186144d402200000900400e480c00b220581d00585c103c82e1006c040e4180e0400c49200b544107202000c000809400c1c40f1440c0400c0c0b080c094020b00078042c00c500070b2a01c001912089407580f021030151190380021414209007420086614075107502e03106520a0340c202055250828010504841d0782c4040300e1203000f4403000554a102c0d0042040340070310741c402201d0010030307901c802c42654 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 333380881 1250 333379631 333379649
    0x1409060405010c110705010f030905060f0601031b08010b0306150703032c031204060b19031b05090c07150c020c0102010b2706030102042403060504060b09060d09050d09 74
    0x1481105400311990161100c1350115908142020000c1e1f60040c0d0901940103080d040224034168143c84050410900b16424040382650004010240d0780c1841045109041d070402c00c45000c0404000401c0038905000d411414000000494240e07540e10b000c0c007181c800400410359403200b0324580140507082039442c1621030346070000d204e030070b2400c000156003aa00d2040021800c2110a168050280704007030020399082e6910303180f40a80b502c0b15034868440025070031803c40920b24503c0c100008074413084000e994141c8511044c07103155141521184c04ca94800c0307a040c0c468040382403c980c1d89400c0c024442c0d45501e081004000c50b50049100e0401132800d80003088191001c0d810722810007211020003d204032000003e001811501b0001604910040c00050810b5142c0c1964081d020f01c00721a00215159482d140540356814040c003005000203803802e011803442c1400d04102809404c00441c0304180102d43c03c800c43d00103901406941d81c012084400403441240e0241412a45001e110b0207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 333382131 1250 333380881 333380891
    0x806160e0a0311040b0d020406080c0306090d1e02010b030106030b06120d080610020c13061505040506040b0c030d0f05090f0a02030303070f0c14070e090d0905090703140906040501 79
    0x9281812074402101c1e00040c1050072075030b18008001c0282240f5031100c0d402030f40928444090380b5140b042002030082c05000b080c034561544e0030545056001010002d1035403000c01082c0c10b13203500c018201691614090b2500844494440990241420101058140d031800310000701f40134403034401900421040e9240c1194100384082c4a444010300d403505400720781c11101050349070400d54899500d0340c5151058400c400e1f2104000386070408404900440d441e03c442082c05240246901241904000d04040f8030b41490100030035454081c5110b00b280d00400803424006668050040754030f05004038208000801d802203201000349001c0d01c0c408080d100d001d0200c00300d00c0000480d5101c00d07030001c00440c04d5590f1408112455000740e203c0d00100902c00090000141440c280c0c05c4000030341c08040d0180500b000ba0102038104024071400140e03004110004119030410b5400c82510820b942000142d61009025400340084038030010a803005602003004682000c50031b1307070060384134070f0017404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 333383381 1250 333382131 333382157
    0xa0b010e04051b1c1404061404050606041104050607050d030c0203070c091512050a060c0926010b0a0f08250b1809040b070807030614090c04080616 65
    0x12202c007241c0a8815802c18400c6190b00715640c005080401c400c40a030038401c048921424050f40e141241e110b40e0018001c0a1104000d440e000b283d4201c6070600706140301e0301e46030715030540d100000b800e110300032a07a91980c4514102403004950262030301800c000d5a403001860002d030748074114584a00020703e002d12204209201004642c1c01a81140a4a20060901d010703500142082c0700d4a4800d034091000009c0c0310002e00035501d407004d01640140101071036074208181900c910f41207500801039150024403882528214008552000c0c01c024005050340040c61801420b01d0542941d10001d00e0f80c0000f05800d680c0500000c0d201c0010030f4a00200403141d14100c407018803181141c140c01510700600504a4010140c2440e1950180b0103048400c10404075200751025507056520130361710010410b0f6642c20994058000140e89007c01640d440d1184415440d2a10fa076014410381003500401c502d00703181000d4402070458001940e0b601d0404040d100c12004403e0f420700045007032401005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 333384631 1250 333383381 333383389
    0x6030c09030f03111b03070b0c10050c031e041a04020111032a01061202130f0f0c03140402030304050d03090306050f220206090d060243020319080c060a0b010e 70
    0x2140c5d560081c000f4445241011042c1480303400c07020402c0c0c590304c0386515002c2d0786240c90140b503004608000400307540e81010085000480e0310703144245010200c0e042800001040c071080d032020511180c044140c107445610040702c94054100b0030100c9817201048140f0f114180c5080d04041c800d01c610042d104d0001410418240c400d80e00c121140c0050100c0048050b0500c0c103503a01181c4488880054050034152003081152400340c443c108840d50b6031010312900e90103200b960300c8210b601c801d101c1c142c40c0907800a5500d104070b0259600441e05901c0f200109401011004040c40e0f101506002c145400802002b6081d01243e00405203111b42c030038030160040d01030100c003440c5d4004d00f100c0d240c0010401400000d024441d02100c0780740c0e0030040922100f02d841d10100303203000c120700d4802c0820300c2000d4a48840c0c07100340d404e600031190b00340030400580d8002140704d4a019050300400b2583c9072801e0052050042c84122001405034a00700142d100803584a201c40d540300740c1728200380c400718000b40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 333385881 1250 333384631 333384673
    0x1517252709211409041d0102030408070317040c0b0d02070506041506050603040b070f120c030e01051b03181507030c080a02030114011d1518100906030c09030f0311 72
    0x20a0f2003608101312140350500d07410030300541c1e1500407005003d00c5011051400c83e4000c5800780c1e0071810200e5100205584000c0030280e14212244618a03030a10fa100c07066000050301c41c0354403243c00003e0f82501810942c056504d0342d604041070300d0b4036280c5800e1440f074280384100880c06087c9020408281881c1c142e051364000c50b00086503100959605c4000d5460903034503480740d001e00a00b0824500c80c041c0354003a5103202c42040d40d01083c1c490314101d1050035504003400d103049203a100950303031401c00704034000c2d20b40c003411816442242c0307160040e19608201c0043d01c0c40e00ea80800c9004c0000294040e0080c1407070403400d5036000078a0b40c80c410280c040340400c0c09078203030704420314140003050f6100d000e03420500c1d400320151a006c1400000014500c01607181c42c50306070800411000100d850420704804c0342c40082d150f00c0d5224545020081010082e401010141640c40032a034014510800354207001c1c685c800d219070006030003400c0c0075003641540c500c240010310580f400512101d402a00c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 333387131 1250 333385881 333385907
    0x5160602100b01030b0a290f07171e041a03272a01080a0603110904030507050d12050a06050a1404151725270921 50
    0xd4540c1c907103241c00d81d80c003800c81c5481d103d0400d6100c4c0c03145507465480d602210000c2c21003000a80c00c0f150340e4084150108414005c0b4005900140034802080340c0d29000c649140340d00a051440c1e0202d0f400308840c01d406000050300b58404903640d0b1100c15203441e40240266030000c000d040001c1e03280d066249591004580b600101211041d40d982200f07984d080079514964814281c854240c0c10a86c00154011803010902e0391040d01c810380401560044401500417010b40030074494541940c50323114114030401c1d00c2c00c0c003411040c40060f042c03620a40603190000c0c2e0240568686490400c401004011500d80302c4612501e4440400c40e685030030302c40c6604566001d0100201e0500d41900300990005280d0142e8115445510100f0f081600c443c00802030003802c0c4007000c1d6032952001d0705240400491061004043c284801318401c180c41c0b03001c0c012075101ca0320120391040c90a001c55840c101101e003222065042c03446042c00c107c51300c1080103200c0d00301c015401028000b41401c854603003020803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 333388381 1250 333387131 333387133
    0x608090d0c02040b03031c1d0601050a0e2d010e1f09050c070c0e0f090f060114010912060c080c070209010902220f0612020c101a06040b040305160602 66
    0x11841c01420203401002c035825000b401d0f04e042c01c2054144034050000c0b000c43c181c00a640d00e0407840e0116001504524110341d08006200560402011404418160040d44d05080214001820050700380340404036040440f01d241001780e0904d04240d013400c0c0c0a008010702e0b00f800500007103003440ca20315a403480051200c203c2280c3c41c580340303101d8001e040242407080440010450b04001c10899807210300100110003c0484600d0240e0b260744403e0400342550b483c540014001e5aa06600050224103688481c000381d601c5e01140001a00c40b8400d980c4407405d40740104484509000382c0e5444500800500c0d120305a1907692511084d42c2c0c0d101c1c0c0e0000952020038030300103000511941e070203441e04411000300c085100e12121900382116a00f0340c402410f2080b201c00c10701440d90b2090698000e0984c04200f5414412000300180c0c45134400f080e050205680c5111080507030341e2805036494424005017085079203948030009403046900500060b1058421700901ca08481c0e03142d4281d00845150358 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 333389631 1250 333388381 333388397
    0x60f010608130f060b0a1202100c122f060711191e060905030301031103010207120e01030f1508120429040312120e060105062b05010f0608090d 63
    0x2548880d140014603000341c41c82540d070500c0a419071561b40001011300308044c4000c1c058811481000310046002040804001000b880b503070001d151050b0b6105805c40e01e040c4031106103d0ba00022414094188814444506040c5140040b90010410303600400c01c42d030710340f0308411300c18840682e2144c070280ea2400d440307600a6108085552500e00090740d400341441c0c1e03003640007181c641c1025184a0300003521a41c00002c010801c03c15103800f07504851809800941c1000c1c41626000302200d00ea0a0781d0f404c0c441c8541c00402580c1c400d600130012007a051104028400038000000d0100300103010700403451117681100400040f205040d40d00312500310181d488840540010030403107240c5054070600540090102000113100114840240c00c40b99031034900304203101c010b5406440034000d88070081d802c800c0c014440c1c3e440b0340d821161000180151400e8070041d04600150409400001154252810001040800c07030a0f0b483c100f1594103640c0c3e00020307140e0905d45034071a00c0b030348501004203000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 333390881 1250 333389631 333389633
    0x5011a012102040f1d0709030510020f070209100f0b13050d0206120702010504030905060909010306050c09120304030b09160303030b0a0308070c0302211009021f02060f01060813 78
    0x1940702640016050710150a0a5484a6020151085802602c1c0b81d40750702043c900f20201c40c2038103e5010102d0710b4190b0b2031602e903407500d03502c9004001781200d1090b000a8641c942d071000700d0448070b903142c1c043c1c0803050615004444584c83d480d513000307021403114007010004903035440e10180c9004206001141003c24a047d0400168851640c02280c210006006420301e01c80984c80003032103080d81e40c0002c01d161405150060001034290003030b13486482e046c0030102c1c0783c0e00c40c1c01281d8150380d0300c0320b800921610b980107044514025000034075884000183c0180520130301101800440c1d00c03e00718124540c86064240e82c80ea4000c106528a8094580007040071074400e4201c400354071405060310140c03030348903183d205003688012025070784002680c50801c1142002e07280b400405132500030b0164212004070406894506142607103180d151602882d4007559900188800956108001404100d0390440042c0d224001120040d030347c40050800050070b01e0042e2a114402c02100000000146d56 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 333392131 1250 333390881 333390917
    0x105031807030803090106090c0f02030910111b1306060c08070204062303070f0f0b031f0e09250303110f030a03090605090a0803061e061605011a01 65
    0x31260301a0040c414900c000011401c0c0c0742c01180564025400030410904158030102500d0f501e00b850b104005a00e000352595545c040159540803030300b240c0768004444041000c840410402c84c8042d1107001d02035215840b5000e811b290051043e080d1408a004000d06000100b128200d00c100d8011581e0b0450074000189468010a40217100070000541e4580726080e0310a200c000480c0350114a6050f800f0410500d02044a40f0007004a80703031030002d1a0a003034540b540d071202485840b05245001c4046048007184001c298941007210385030610031a80c410204491643c1a9181030241c0030b0080684100318551030001e400310010558641c1c050314540d01103910f5104410340c15076034002d8041c4807107030442c00d10041c0b4a81100e46c1c0d01182d60000e504100301200e1001d4242c440e59804454004002200710080e0fa601c080115460150041d81c880b650324004031000c51181d10540000d60741541c0c045050200c003115000c1d60003000051103d507d01c060304991003003910301195007149084c581d030312 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 333393381 1250 333392131 333392161
    0x1b080a0b1803040f060806101d0102032104020a0b0304080a0c03021005011403010c020c0a0501050c12161a06180a06030236040f060b0105120a050405010b030c010503 73
    0x20740340404500a03410201000d0454000c2d8008881c00e0021070410045664481075058200f50300b110501c41d503030041c82c005400c58507103802010003200c1c03045081803207030700a009a03190780054034141501e82880d842c04050903501228124071540c0c2294010075024645401d403842039a0103080e462404039854016916007450350021000c504c00c2c6107844140c1603c9005181c000c2c52080c9103182015001c80c201800e446180d020901103600c4008140c01c142d5039060078004071242030070301542c1c4140841521782001c0003190644c01d001c8000a07880d40c4d1a80482c03400c03503468015441006540e8400040003910102565820b070301501202c0c1058084000c840c80c181c0007001c100d00014800e82d2a07000c0f40b80341c0c006621010100400c0c124050351441c041c0c0d548605104203014002c3d85145c5039844030140780c804507014110542c0e4100011190340128102e6508045103d5450654a440d035990740103000c08503402c4406509103092000c0600300050030180c82c00058541504540d138595050760004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 333394631 1250 333393381 333393391
    0xf050d080709082d010e0c040e0c090f13050609030a02010609090209040204050907050d0f0c090b0108071809050109020c070603180b04110402030c0a0f090b04090c0201090503040801091b080a0b 85
    0xb1304401d82e04001c28000344240c0080c001c1d82d01c00f0b0580c0300c2e0030b01d0822007211000035804086410121a440103640c42448103903014691340015103031902c400c450000720b48501c400082140c4651020b0040c40e020000140c41007508a03402488626100e1018100ba40c05c980d400030b4000c1c00000203c2d0041c40c0c960030085d48003804504032074400b42c2e00d50000d184501c2002c000d0341d40003103501c482c40c140b045803103a80700980721000c1d00f13101000c0c041c00000c050000041040c030030003542d0f509984082071100f40501c02445010003d102d1035840301400b00003940640109401f40c815200002800d03406406581e0080640860000c000c1c007041c0c403102d01c0b0803c020300c1220f03541058400e008860f80c85201a5025418501240341c40d60f2a00344040c040084044002042c010301d80703001c0105640784030489d030507200c0d5241c01080f98209070f00c06074090020120000d0290002250118041c00158446c0d46020b00450310180306458205000a8008150280c4c5080d5008035079a440444e401c5104142c0003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 333395881 1250 333394631 333394693
    0xc11040c021516030b040b01140f090a0312031508120d0e0102040b0426100b0f0d0516090608100b01021005090c0103060b120103031b0f050d08070908 66
    0x108541d07480300042810110b07264100d4480f607925407905240d00d842100203001c2c0a450400028400a002134562120002540031540d00000c6a0b103040300f030403090750500c038009000c5107211a01c038600b4030031030500003010702d001a1401034000d260300141601307801201c040c440580b4540000307030b485a445034820158146031645405040e450304000744001e00003855046121070b00c0d98281003c4008454405010240030080c211140c0e1081c000032982500d040c0c5c1c201400210342c03c00001184406d4a040405940304d030440c0065014030002013500c0403018000030190349203586941030007003100d845015024a030b5005a4400c40d070304510b03a004a5105405004941003044603080030701c15502e08503001002c80c2c1050040000b2540c05000e90740291502d000328a0038800d1050640c58884014400902089840d928204070b1240022840703400d66008403c8611000c03d500b02107648440100510000850b084002000c2d28400d180c100305485403070024156041e00e603408629016000e001700d00034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 333397131 1250 333395881 333395893
    0x102240a151202030c01090803040b030a06180e0606030f071505040e15010e04230408040801090309150503070f050a0210062306090a0605030a0905160f05010c11040c02 74
    0x41c0e41116001d0100818029250340d00c24010b41c810300d0704040c10760602c2c81c1400a10302051010b92404402ea400fa120b0405581c1e072299680c000100c007600141d03100c044000500b8488000708601500211500303012582118502d4407001c0c24956a40003654462005400c02e00041c042c11f95203c03080c802d0700c3c28618145003041d840f050780e510300032000c0c4c4d12401001c4c0d20240e0034480356002900b80d12600c01c1101c1c1000303203803503a00488071040000c0c0b0104541c4108a80040c0800036901c0a80780905802402003021081c3d5240c040e01d04810b03801000e0300b5001d0b080d0041c03502c42c412000c0320310540007903407040010745ca2440f003660785800007031020007035001e81c503840c0e5040410341c40b0354030040c05c0c1c051580b11624401514a050310005400c107d02541c01000701c8000303925542c01402c00c981d098038040380d8030360340c9000f42001007108420042041c0241c034804901d0242007401003003038401c843c0d50004d1b1740e5510001956550301c1c00d82e0043c1941d0110a4011a501c1d00e035000c1034203031030360b4016503d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 333398381 1250 333397131 333397151
    0xe181c05070c051f1101051312120204060504080c060901050a1101140c0703110106260a080408070608091534030501060f020f07030209040804090509070e060102240a 73
    0x2c5040c80341c82d00c403440c1c0c21860729500b00d50100400e01c0c145d0319080200240d04041601d041c0308108a0702c06401c0218950400255511a0702e15240c0c0050350042151502d4844100034203545c0320b4801c4107590f100c1c0065803011450400111030368000140c481ca842c00540c12020f8500540016011200b5581c8800c030450034481c0c2171226200d00c414441c1c1031358400c03807450050040c0121440c4100c80380c0c9090000d000b61035400154080045074099400b90030780c1d04901e403510300981440700510881d40450001202c01d000141d0708103441140e00c40e404556554206e40d6501d02810010400e68810b900208201901c0c840c10b40d50514840c1139845a48403062203032022100262201000003942c03036004002055100344001c0405078984040c05038180103440f41a501d40d1640000703445000d101c8040b0b410000c405003114003c1a401006100d540b81001c21140c840b22180700320111985410001056503102088000355201c00c4a05c0030240308010340d440c4218100203120100855540500c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 333399631 1250 333398381 333398389
    0x3010b0315120d02060613090c09021305040f020a030c05130b160b18060c130306020c030c0d031415130c051b01090c0905040b01230a0e181c05070c05 66
    0x222000070f40e4004164605000c01407061190b0350302c0c508400c140c984400c042c0040c10704080e00044400c050350240c1c6403c0c01800b54000c112541c1d22a51380185440101c1100124a802400c080d00040d1000c22040c3c110000079141ca200d161500c918ac07080c1d1140c00d0120040d02006090b45003410007040e640c0d0b4605e0340e0340c01034280c0107940c452541700095140e2014042c00b0005980e000d801040041e0804c13280c041e0620040005000c01051107401040d00c002c500d40404c1600c0101c50075008480b010130007010b0190040100c1c1c0c05000b40b81c1611000200d030000740c20300c050b0700b070b01d0050566a11300c1c900441520041182c12003450404c0420090002941002c2402c541180b1604000143c041d00074500000b020405034440d5894600788810440446c04440b40d050441d02c2e0800e8070506c1117411110030071310084609056610080320b0501150701c001c19000309201e216004080001d140001c00c00b55603400c08a644141042e091802c040c403074034230600242402500c60340a81d4080c684400c001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 333400881 1250 333399631 333399643
    0xc050709020f030f01091803080a0e16090b01020613060b03070302190806090d050702090c040b0301030b0601180b0405101101020c0a05060c0903070303140c1605031203010b031512 79
    0x40001e0040120a100001400d140304c2401414445010401c44442072002c1010007d00040138040c0070100001444e81c0305a600100c01d510011419502c60b0202445104020203031402004481490035944110550000444901500001005103200c103c1507488070050b0803800030300d0f40c16000d40c0c14004010b031a40041c00440144132048038060750305100d001072803c08001c10344c00c51035002d501e9107203209030040119070030b240e01034034100d0942d40d074005c2800103485260b2180794090000800002402a208545401003100f681c0d0040848040c102c0950707147d0542c00346141058041004004a01e400700300038085104a0924180040c050101142280c1202e004d00c820350300440340100c10044203201d5150720044e02d0030990704040148010030759583c1540801014010500c203020368071901c003025100c0c1c030075044c0126011084030f05c102070140f54240c810715002c0d21460659031501c00288003660b040e500200d441034210355440c90740305100c54103984016000021843d081079080d00078800b03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 333402131 1250 333400881 333400897
    0x1002010e0d05190206010f050603060a0e09030909090c090a0b0409080c010501050f191217031f0506120c0919090b1912060b030c0a08160e09030a0c05070902 69
    0x9103c0d02c1e01c00b044001520804107074100b0085410810041c007800211110b110b040d10f030f05440e840c1d2203955940100b249202150040c00420701643d0401c151100c0010051140c00300603a801c1c58103032105400c403a580c07600440b0240c0d00c9a8446c00250a500c410343c0301e411801c2c1c00610120f00300e000f507100c3d40501c0d8819540420700e139445e40b00520a03400c0140685a40b50004c0d01c03000a80c410400251036422818064480d22030045071680c0c05014400414000107103042850651701d041001c8260880403100070481040c0b840c0204c005290314008050300c1021015041d0b281c802d5a4902002e482039221042c00c651050074984002083c0308001002c40103440320200002e070b207049410421400c10840280000522007101c81800410544504200c8255001e00089450f01224001a090102d80e1195580064000b04001040680003880003410030520700003010303403501c0340c440100700d080c116650007603a8410081011400d00c00c07041505058050401d4641043c0c58058007003e0340e1005c04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 333403381 1250 333402131 333402137
    0x60812090f010815060f18101709031c02070303060b0a0207120227010e1f050f0d0b07030b15340b0f01060f030615030b060c06070203030415060b091002010e0d 70
    0x34030740070740086000d941c1c0b0401c7c604445031214020103032802002048146001c000003050140410300c40c0d0f03020001d803003e02c0012070014a100d040c3c00040c1d0000e4021540c15000213081c42da0000d41402c0e40780c1240ca420b10150301901d034150070039000c04d40c00c03108404102c0c0c200c0e6002c0c04003000540a400c0b40754502035641402c00055243c0701c103010103c0d2020303012040c1d0305041b02c03081320140039440d01d2208a420039521800c500b543d800000d40b001d89a004080c2030705071803004114a85500d580170b800f411000f103480c3c0c0703003450703400c0d0520740a8021800c400000040318016410030404007030340b5003a510107008250304000919550070014841c00d90300320440004000061203010307041444904681e403e0b1404115017031070302d56503405594490341e004041c90b65601c8408400c1c0c4408085548141070081180c980707041030800296030b40c5c0f04650599181090a018800c5203000d80a1002103410020701281001040b400308502810409400c0c000d6650302c6021056480090141030b8407a2410341f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 333404631 1250 333403381 333403387
    0xd1d010c02060106080c030c030103120e040f0203101a0313050a0f051c1e050d090218072007032d0b0f0109060807031103030418060812090f010815060f 67
    0x44c4005c0c0c100751020b8a409480d80c5c050042242a000410036241100c0d0898013281840c1142582a02c405112030201038102e802c1115413000140707160006d40c041e01e41c00d041080801e40c2c51940000000712201141c3e44808204041104d51b109107140440003402102560000000341c0e440904031780d0045000c0365283c000c04100d0919000780448401c1c0c0c0760460034050385000041d82038034085d80311164090f05009010458140c403403801c1e0300c222a00d40d03001d031482c0c80480021440c120910f00844084002690194552284a640490541d181003442d00244034040c1165156004042e4010803404600d4020890b40c07404007000003144802b50003484000d801e0305001c0b80f1a01c01d110160040842c0718203003c410030401c200042e42074112030700035105140038480480000d0861065a01c481074040c4504001c0301e0034411a8003c4045904542c00c4442e40c50340d014a0410030700440c4065136000030b4020005026501030301c0050342c080152140821040c07010b00c0042c41c0341e00115034403a000c44001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 333405881 1250 333404631 333404639
    0xf040f03061406040b420306120106030c030b130c06030b10090f0b1c0203010b04090c090e1305070b03090a02040e01140415020c10021804060501050d1d010c020601 72
    0x101c10050b00303c1000d40302400601050404a80c0102801c0e03203440e96121b05002214000300e4441c01307420f40c001541e04000c88040c90784001c032015002592110b11805c031102d02c80762004014820b2030201c0c0c4e8804d0800780020300d584c03203003200e01c00300501890a07800302c000002c0c00100690048000b40403e40c40c00a4131441180038015082d003400c00c4c62041c00006079052002c002c218400f02e040391444401159101c0311030744484001d038040d01190300307000d0020001003201030b4414050b00c00e07103044000c100030b4450b20440403905640f41e0305c2080121060380c0e02181c110001400000c2050b4081e00c21601a40d6907105180115803040751030302003503081001d2280444c50b15010b070002c1c10b82c4d008020300142d5401040240c8020015000800d0300d9001c1402e55840411a01684d4030403001c2001d45000a46620b07001000c0d41c004282040d003900031040e2040e140c64548904015500107030f440d5030801da00344000c500201200c4450b021180301d031072008101180e003401401c00042c00ca0780506000c0d490 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 333407131 1250 333405881 333405911
    0x5030604053013060318020901090c02010b04050103060518120405010806120708160902030c0a080907030b0c1b010e06062206030f0b01050109031709011709011b020703050705060f040f0306 83
    0x4088440400b1001e806d100101603520381411a0564030383c2c58000403404020b0809a0060075507908003038105050000000a20800d48d020a00c1a074591840c030409055031401d06486a5100046241d559000c2c0f00a220a5208001301303a4011301c05056800480715a0300b0141c90f05080e5404090ba640c46600115803004601180c400209412003096046082552812105004007019a82002480c030001030111008000703d8004681040c00400d0900f0012040c404640c0300c2c810100100369680c4071a403a502051080d02d14140524002e001c641d10381c42c007084040b07190007008860005c44800300e6920a6041e128076001180f0030904504010054038000d811110147c0c0000c4c1400b5224400b007000c0b4051044009400d600c9031380030b50381d4411000041ea100c540840940c81640c408108000240205500840718000f01c05c0070400100c8524070100ea4842e124000102283c0020074100894140800030300964140c4094060500c0c1d140c09440d105140598400d550140e1100c08083d2201a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 333408381 1250 333407131 333407141
    0x605101e05030307060209060909090318010e030a0b10082b030213030303110d0603050f010b12070e182a09040b0103020d30030501050306040530130603 67
    0x8800c011032120714103000681c49000b103520140030346800280c100001d546e24030484d42d540f02c0040401c00903080c030259159594001100001c4580b5801d54002e090351700481c66001c4c500b01c028010415900941d680041180016009620360b06c00c40f840440c0788070060011002140d065002c41e01c2d0701c08403105295141d61001c40c0da0081c9441080001c5102c40843c0076042501d4240c02c0c08143c282000d180c0011620070892400b0300c13149400800720401001042c03a10169800400902820004034100f06000307500f056040060751288004003c0184000313441a0700080030511911080a001001420412a940300c1e50600b0010920b821003900c148005d80c40c5840b064491140d00d260955800604007011300002c2d10031030b00401c0f00810400c036400d10341984215141392501440d04152600c07481154102c017000800d003001e00100e11828001a00d92013560080010a81041114402812100b500043ea00322903506601241c0d0f80c030f900002800e103000109444003c00b03103400e0000b0103c2d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 333409631 1250 333408381 333408419
    0x80d0b090a0e030a0810030b0a0209040b18071419050c06100510050d29030c0d0816030c0503040e04060c020604020102070902030718180b150d18060510 67
    0x40c1c0b6000e080620300c0000800d40e41000c80a0030701c07612035154000000001034040d40001c01c11280340c0108162825190050608020203803014030141c3c4c200b00c108507036107101412400d1102d0a1070009410148140000c2d59500c02d000c05040c90a010400c0d125007000e5083d2620380842e400141d164406042003001b02d9221144511005509080c280041c03140d0382c003403020318204480401d83c114842c0c41a400300c0c0300900e0755040d010520301c000d0800e0038bd495202030034910070300812031206210700b410714144003500c2d8014021840d1000440724804210442d0806404000004078007100158080000308043c0507075401c0c407822460103140280984100c114003a085401c80002e010044c1d0700050300d00c080d0f0f1001100541c9030391394040c0c00c41e035444a54803581010f00c3d0a0304002400203c0150303078807408100032000d20610b14084103000420700c47c1d0048503011481041424044030207a40712040090349614a1881c07030a158507440103507101a11107010001d001c4200700120b00080490852070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 333410881 1250 333409631 333409651
    0x1b0f0d0608060f040309030f0303060e07030902030f03040509060d11090a050a0f090b0a110c1218090f04200d060515090106051804090c120501050c04050f1c080d0b09 73
    0xa413500350340040c4100980e200003020403802c20140020103020f41c01c14009001c070303541c0f0304e20203140a000040141c00c400000340d010f40034141096407401d80120448040d1000504824100c0e00c44400f03100c40d510700881d00b9104a000392001c01c0c0742d0fa83c0c0c02c600b00c0c02408008000724980c20310720702c0c041c1150210f0300105180d500c5c00c0744a40008140d6032400c1c0d07000f540c001000601c09280d602c1c2a00c1c03440b5040c00302d184e90142e0960045010482c201501c3d007804445803090001c2c85000c1407010039a42511500f0070048008001400210592440840b4200c0741061a02000400c004100a4207403031904440540d00c40f0104030200c1d4003c1c8400b40d03001c000312002d81c44c40d45045000f42082c0309a03140b0300d861111207068424180c0302e0350000c80700190311502e2508400c0d0b17500c0ca08445082c0d030a004648950070880881c848815220968096030b200511517605c2c011001c00300100070b05800780003501003411882e03400120f5001e0014100e046214140440c04040340000c02501c0d4030020180203070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 333412131 1250 333410881 333410911
    0xb0a030609020909040602030405012d0f0b01050322061e0c02010605220603020303130f080714040c0c02090103111003180b090a21030b060a081b0f0d060806 69
    0x42d50f13541c0c1c41483e4100d0b40050300107035a034985003441809400c0d900c000001c1018007491512041c8018011600300403a01441005010f10699801007030f81c002122040c0005e01c00c0c404190421262031440035031401b9908040300d800910303902c00c0706840d0481140503004824201160240c1c41c00e0148200c640c03030500c020000d2500b003000240c640300038440b800f4110350521380c8010801c88503a00050186400604a03920350464201d0245118510301800d00c185560703410005050302c0004904090725240401c000a2403c114148001000750343c84540810400040010142c3c43d2401400d001e140948250303c0c48004803801d00000080c5c100f009030030146051041e450400e01050207240c9160b011294100301d480d00c15415181000000c0043e184040d45107401440c41501d0b644031110040548040c400010f2354410403950703000300d07008080468880e00000751880100390310840e05100d0517000504110b4205502c00c030725040412071561643e62200240032a4804001096105242c2041411 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 333413381 1250 333412131 333412147
    0x804110f030a0b0c0d0e03250b0a091e030314010501051812010b0612060901060906020307111f0201200f0d0c050909040609121d1201150b0a03060902 66
    0xb03602d0307103007000190103035a040d804100c0e4040c00340d04413031443c3c0d80d55000f0b005083c1d10380d5100b070701d9601011202001a0b0440d00112402800008610743c00e170300104d1407070300c0b43d4850115401500d010101261103011100f50111401e140b1f0b410001c10034060380d4000782000c1d00365486810b110042e0805410b02c00144940104110a9087c09514001c203403505240c8144012046015002d070340000795116102081d100401002d4100b6144038081c1114005226640d0301230030388205d5503500641c0300582041042c50042800120544880c03800907142071020100b110a10a4141d120400f0000603512080d51010540780c0703d0381030600c610408220b914180754466102c405100300c0d101c0d03240980c1ca4640c44444180194251400800081d090904503d814a4400010f1000140c1210009031150101d1225031040f585107000d281a492940d1820140c48200080c200080f003030700941e992074a008040314000110f0f41d0004240c144822a20384a100d0030240039514150040000c441c41807083c03078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 333414631 1250 333413381 333413383
    0xf110a09020309121e04120b0c09060901030207050f070b0705060906060a05011214040c0518060105030127020c0d08160801060c03110f1c030e06180304150804110f03 73
    0x600d144000013880d59580c3c2810346107455148450407200c5028400700d07000401946c0d0303012100c0105e01c1081da4410b16664241d0800d40d9005a142d8903810600c240820051540254003d05419015804403200f000301120490b1510400d90040c1c0c0107400701080007002c0101c10000240c002d40c43d4400350082d0b250240104030048103500c603660401080f0490340c004100c40381d200c41e1100c61207100302c1c5072600e803070700340302c4600c144611a0398001e010800308210504c001c0c6518600504059490030314503481d00001c142c014046006402844040c2c14004d040c81071a407004004100264000d044020144240a442103100400c503944480045203810f00f1290700c00c3c6902d0559005041020704d0440c00e050440b0220300e81c0002e50914491550551082c2c4400a049014104500d2106200403c04402201a904c2030b0302d20b81c1c4186d005c240841c000c20102c00d0500445110141183e04095489002045820040e03540305d011903032607010b003c24001c01c49440203102c001500c20800c4000c00c1d001117 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 333415881 1250 333414631 333414643
    0xf09070507080d090515090307110613120b010f0f0f060311190c0c09090f20090f0601080105060705060a1d010903030b120c030a0f0602070f110a09020309 68
    0x1010030450000345a034100105101907458400d4040f070b080042410340d02d0300f155a8440728034420000001000011002000081180c074103a50103448095000182002d20806400c00c5441600c20218544040f448084009200782e2417401210922219490001682c08014150300705078402da41c454402d0102034107031104081141d200340340005a100071003107a80745d20300880452840c0c070f00c002a261441d80c1e901105c202501401162107030329107541e904150080b100040001040140c001100307001080f01842c210b62030f44d22000310084008004000115460000c4420900110104040c8005c0c0d5900c000300b2400b4101c01c0d52290314010310b0381c50301e0380e440d0001807011300d07815212248100c00d500045103039400b41c1d801c000240700b64403091030050043d103820036000e40503000d0b40404000711340e0005203950300010080d000c0d0891460689800420354403200058400300d80800c00c05c40026418100303491310750b005d103540400a031441020030003070007400e502c2034003198010300a1162460001c180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 333417131 1250 333415881 333415891
    0x4090b0a080a0809031207060c08010b16020609040f0501030503030103110102010504030512180102030a0b0301051b030103032d09150c02010207060f02100203160906020607020c062a0d09050f09 85
    0x2071613880d07011a6000a20b04180700503c1c0400d14408100702003000000e0300200600e80b02500c800c03215a0300c0381c6148005000394800c403403e8204900e96400542014802010b81d14400b400c0030402d050440204000c0d07a6003a442140c3d00e9100000420510401c0144464544c00901c02802507050a4038010002e010384041420340503810300228002c12185c0b4000840c03002c0083c000d42d2a841c20700710304001042d1100070795000354205000102c2c0c440c0c01c07030103004070030f001c3e03282060440e400c545007262008042d0355040048080c3d210001c0800030494035800c2c2565455540d50403090030400c186401071010480c030414401070f407411500603a00800c40c88265212032601c10140f01044000328580f40301c040f00504800d00c00002c1c845454940c4940044a01c455101d020341d20f83d40c2c4404a96460b41128100011f03048600200200e24001d030003000924801c02032008034102c1511100030301040c00c045050380b0b40c031400c000f074000b80e00260b01d88003c060445555401c0e01c084004203119045c0180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 333418381 1250 333417131 333417143
    0xb0105031b120a0c110a0807060b031009060c1b110f13020d0c020f0f072102030102180a14010c0204180c140a510504090b0a080a 57
    0x1440e00d072003011000030740e00c016424001e1a2154101240d0b024020300440d51202d00040720040f400c1c18422000481800a55010a007146400c0035511910b005103c204c11040d4075000d0b04031445901805070281c07201441c09a80002a4032840c0707030707001c0c0601071100c21807122031510180740000305141c0d80020424100070354040d00e510b001c0100040c802c040500c030719030b6444d10203c0d030300d840c8080d903900c40031407900e45030200e5501c0c1c2c500b510415500c01c00c00311390709015440782c074040c0322160564035008440c00d5035180600b682200c0ea80003c6c00e83e0400c02c8d0349405010314842e03c0081e85421900300008100710f80306000320b8016080000d10240c4004406801a0b172034001c0402040ca0903118034002a0f081440b00048580320444a807010360400003ca02c40c0b283c10401149001504485903c002c0704030f008403a0083e01843e003440c80b8442c90f80d00138a510b18026640400c0c00c0318880307403d00111070b5a2425500c90604000c0c0045440b42c4c1400390043e070003030400703201c0500000380506031190060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 333419631 1250 333418381 333418411
    0x3181523180a05041d07051906030c05040906060f080c1c1a040e070303170f0711010e010c020d02100b03030717070204020a050703030f0504050d1805030102031f08010b010503 77
    0x1e00412400d0100e0f0b030005400515124000c08140c0f0194008000102000161b80116030344a04100341210807411515a05e10a01400c01406001e5486413061800d1403d20341d040c1551010518121003090b848400810f1115005540e0294880703111680400940005400d16120415010400c240003982d03018180e5582480205080190407081d0240300040050051641000305c4540b504103502c4100c0200e0300d1005004c0961095020fa541b16540400f910340701036880300c600701c540c8511080e00301115580d500c2504902c8400307000d48104180c21350018141e0700d0110b4802450000901041c42403103240040c004000e80d00030041301c0c0d0b0b09421001540060707a108030203030054459080c0007940035100180c410a01d80d0410040d000d403d0190310100062440c00d4200d84c00d4900c2203074020a607030841c40040031100d000d8141c5283c40a80303840c41602054a4030080783c2268810f031842d0a01d4107044204071306089000d178075000a000796600a2002e824020300180003808003605c9111455501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 333420881 1250 333419631 333419677
    0x1a01061b0302070b09280302090f06150315040515030c0102030408031917040609110f010c020909010e0a0503030619140616020607150f06031e03181523 67
    0x8681c0143c20101d0030f441d8581180119403000c0e684400a07c800c074000e24038100000d040300102e01815110786006070a54070780013032003810768803980c2c07008041d001da64519407090040d5480d18031800d40b180c9518400310120035055410185450300c1d00404504541c000c00041c01812808429a03090005044284c000340e04819408c0e034042283d181d0191040207464108414041c0b0340c0c00034410b942c0106120f817000310716a4180560110a0480030340800e266070051401400d0059040e580158207000015641500b16180c0e400c100c4807181c10b60f00d50340040240700c1103103001408840c10122482480c100c0914000440005180d00100c961050340045031180a27240b060042581c9258000d203c07940d0350096182004004162203014400c152500c1d040c403840c016030384500c5050360b401041c0380076203a13000318282d07030742e201301040490402036642d14500c1d0510701d00003a0300103024200b003119540000b484008100e8800070189042c65100d100c3e4a00c01c2d9102c4030115070154649120b0302018900c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 333422131 1250 333420881 333420889
    0x41202010507052406010f1b211d0405091c0c1208071103031e0901020405030d020a03020613420603020109050d11120a1a01061b0302070b09 62
    0x2804401900b03a0042c0c80c401241841244d60751100d1604803d00391441e0b03100d410044030310325403107180f0101160110310075248002c040300700e0040b202d00c00c06460600b080a6546c2c01000e000c0342c0c1c620804180c1401440c900704042c6400c94001003402d40703081006192101e80142d0316000d80913034022010362403080310344083c0f03c1c103090006240c00440281d1140c05c0c8100c0100020400c448001c00103544030030004072110044100d81c092480341c00b0001c006e1a2041c40465401d00140c45034605650800000a0b035071401c0c070035805040125005001c0d00406130502908000b4001c00d0484051030b44142c0100042903400746100d00303900e841c100382c11610710302a000002d0125001c000c0e49440c1d02c2103013030110007250f044001942e00c00c0c0c0c4e441d555180d469090181c02099001e00615115542094000c2c070b0034629205d0f00254100e40464600c0c000741d0f1520301c1c0740c8201100504521045000502002c0c0e0001441100151070b2011000d02800944000b0f480300d115004401140500044078036492b0342d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 333423381 1250 333422131 333422137
    0x3030b03061e07080405101d060406020702130203010506030c0703030216050601090c14090402340209011205060a0e07030203030301090510300c091e0e01110412020105 74
    0x240a8222401810100011000801920356010205071510700043c00701c1d1040d81c4e40303070103940d000e4001c02d11850012100809083c590340c440281450098209500741800c002d998006c03409103c0040c2c1c1c80d0018010302c8600f5900c005000001801000100b04503104c1104803644150f400c1501c036264401c501c3d04801a11848524080a02d0b4600081e000e1000c0440d6084c1250812502002882d04101041d103140c6401070720503520aa0a0080787c84d18100b6400030000d03d0482420000c0340b2013901c0c1002040744000c0411488695039004180071410300103c0310340940200c01040f0000566542e8150b500d800003850003903e103886010070251400100000c070061030303006059903220740c0c43e1551003000b0310307086810501188142d4030004c4c00d042c245610081c403000000c0e40c4410080104460090400c000401f00c548141c1312000180d0340525100d02c445400084500380c100384100d02020055589020921001d41d14000e004115080503104550480340c5d5410640300ca02d40724001030350f540c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 333424631 1250 333423381 333423401
    0x1a070b0a0b030a03110f0109111c150204060f0806100c021504090f2a2d02030a020c040b0d110d05031308210301140a360203040b04030c0303 62
    0x300c0f840081000701504003030381c5046604424111000c20410f0000740703090780e50074203010b845144c00058038030141c03c001c0d9602c0450b86480d80c4441c0c00a900da51041000c100040003550040c0e40444d0078800a13500240d07000445c10f440c40c00410070300303241e800145056284800369080c01300d13100c800c0045403a803004107401201a01002900d030359039003034018080c02c0c441e1654030b540c40c5054106410408101b0303101c0c0403000200001500d012022000b40d442c000702502c00c0d070040804600c2c03418103a103481070018030004ca41c1c0c0990303202c465002d4064601014002c001d0301c918107101312034840341c50301e040c05180c042d00326840302c00d92800382c40454600804450050000d020000b85a4a001d090a0790241251050070842d00c600b106445d0500002240342d1680418140400040100c05030803c01e2014881000300000080340e55030a021410084c1d40c0142c4000c5011840c0c102201540003110036400d5030121415491403400381e0f0389204481c8000c0c0000e00340300340700f4004014148241c3c0304000301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 333425881 1250 333424631 333424633
    0x90106090203130326131104050c0706140f0c0703050f040e0907062109060e15010906050d0f0b0702030d0501030506010e1e04110612010902030609011a070b0a0b03 72
    0x180c10303d5100c0380008040ca46042e8041081010801140038040400b0798004038181480307a410b80703840c0311340078a400e6680740c241c52800e04d2000041d00e95603180700d8113006a94903400305644d18628502081a45d0883c564151600c0700304003042164007014466580c40010200b585036a0420703490242e03034a0041c03a00501d100000460049070000100142d140103070b042c14200c2d0320342c640d00d2000b00c0381e9402e4070408403412504d802545107401d01c40d4022541d40c0b48100c801155200d00c0c404076074944113802d0600c80c0c00003c018010000c40d06c0c00d110ba017015290a0f196000e0350b0010352034040000b400301d00020300600140e400251140c1c400e00548261131343c8110240003d584d241401070356094280580c5100580c0b00d404185501c9896104210151802ca88165503655503100c01981d0020300e0354079604984100300d841001028208030602900f440300c00140c9904244e414050f407608146c001c1c50760481d034010a001035103003003425921300b2907101a00a1003035446401c5c10000d0300d249500300c3e0b05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333427131 1250 333425881 333425887
    0xf08060310060f06021204081f06090e0c040f0b01050301030206030c09101116050f040903050f0f03010f050307061403100f0801091109060a060c02030c060a17060303071a0901060902 80
    0x68031416100c070300f15074441c0d080743c071b29030b801d840c0c078541600c0343d442044501c0c0e0041e006968002e52049a8a60b102d248900001e582561402c81400f03480700c000b0680482d800030361114106181500c60344014071102d007410400c105044001030300394030041c040030b48a1340b000300004070001c072000304403802840003805400071100c0303052014091940705a914121740c0140070900940304d140700d030400111640100b110381c2011041c0180710050240040039420094104440e80c548040c80e0010008100189449a52985000c402d000b04010b1034000601c03a800082c030800c0f4003079000b01c003007002d240c00866440d547e0720307450004182900103900c2414203450b1400700141c0e0130010b5001c00300d84e44c01108034000d000c0000e006c1191403038040710303905e031300081d021400d200ea03a22400306070007540d1006d421100041e801000095490b040410520009401d00100114104607803071903e801031420b40045081001075640e0080e209115030210100c81c7d41d000004810003800d402200050101580441d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 333428381 1250 333427131 333427139
    0x10f0e0c1605030a1106131202010e03270603010b0f0c1f020316030e071e030b040f03090602031303023006090705030c0307030b133e010f0806031006 66
    0x10f01e07074004101c00000300b41e80d512110076440c0301050b0980f16000c0140900c440001c2541c0310380c1801c100a0040342103640c0c40307032a1918008108024580d02250088041c0d4009a0080001e903d0b201c1c1042140945003c1c0010840101141d003500d40c180e40300001c00342c80312000380106251551030340503003c0d1480990b02101502120b58019805203c401d43e450103052203903941030701a51002e030f00501c1c030381d8809641040028040320030b4154040c603040b25820101c0c1d0f02e40b038034003a07000d003074400f600c1104004040c0c0080503040302400c80103250038000355040c088480e480d01c49507451840701a016500900c600969034021100d01c801421401d10712840203121545030301c2c0e507600c049903070038100c4c070998802044502d40052446803085005000b4400355047d036903021010300029010f141c0060f8804051400647c0d009452103011015085401520100c00000088100c04420402c440150b248104500d41d0f4042800c441128950505007255240c85020a01d404441e440041403507140078000b007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 333429631 1250 333428381 333428383
    0x60906051e0d0f05070b120f04030206010501120e0f0d02010b03070b250506090a2306041106090d1a0705160201081801020d05060a0b030106050d0b010e060a0e120303010f0e0c1605 79
    0x2070124804203050490340c8c1c400909100036425a00a005030b48002e004121948c400e01c010900c88404c3e03038002c030b000d0520150451a14031a0409002243c000d00b00340d44000340e0901c114405c1c1d0108174001e2003000e10340100364845101301000b0b4110403401c2c0d5401d48280c0d82c102c2c59548240e80c400c0c210b03501803601c80da8158aa081028088445203d200c1c8402e4003800003040e6144c80540b81d40190071303242c6481e65951070522486c030310303a038100d942445040210b694210654a030580100d07003030005080070240e0075050100c02013000082c0f280c14082e40500e5801118503000003036082c00e00c1c0495841e0000390807404070342d2804103002580005001d10600d180350300207900402040d40e241d404282c841610b8445804240103800001e031003032001c0480b13002d55130016040500181440050b410001d03011407101d0340f003600d08034081203500d0f04010a508182c00018000300c20030740a103081d0b5062907072044140b5024462600381010200c08030700c40d89103180c11104515078801c82d00145d5a50303483c1103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 333430881 1250 333429631 333429637
    0x31803031101050601030c020d1209050609070807080102031003080a0c02121501080a05030306100905100e010f0c03080a1509181707020904150f0e01060906051e0d0f05070b 76
    0x41c600e508002c080340d0194000e0142e9810203140ba0003401c101c0c4503000040381d0300c45030540c207140469200d1603d240440c1003488220f001c1c0b40d82c170014060541c20a580c10b442c0001e035900c44a05a8410020000c041c850102c8450940c5d5000c140705580b1408050115458890030501070b50120b02e070076080e818101d000584a83e503100503002c024060baa5808503a0702c61082076070140c0141c00c20000254140761145141044603507500f00901c1003504c8002040440c1080305000010440078180003d0075070b00b2040d241042103540ca44058908015a8020400030b000b414210340d10780c4034076403e0b06035460030466002405040008000c01e40c198541d502040c0c02c031060584010701c003004084441c0000d00101e0303030095000b400385001e90315140e44030300540610004078403486540d4440c11000400700d00441d854451b103080041134a608011061040b039a842c2e10403481040000c00d41d0445a10901307811900342401c5170b0f54500b0980c0c41c1001d000c0e0507440c0350002c1490080c4c3c540403034070f1080013001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 333432131 1250 333430881 333430907
    0x60213150e0f150c0f1c031103060d0611070503180f1206041127010e07031e20041203091505030417131202190b1603180303 55
    0xe4074509207189401d0280442c01d1001d4590800e550044641107855010024015844080c04540c0202484d48540d810403100c11000071200d003180c41c26041666060080e80d01c02865003a1052440c00d06074005a03c0d178507180340c001c102540f030701c507210220713a150f10039164110342207410343e179032039900d0f010350200b1100c01200302c3e2144060f042440400e0600004031f5040b00c4000b8003d014030340305d60b02c80103141a218101540d002c807070a05c44040d5001d40c51000c9080b901303d003600c0700341d035410405100001c150040081d401c0500e442d51443d841820072425402150041200252020b03842c04840229541c04100301c01071500090002401c5107132030f4002240364000d644040da080e40b1083e420301c2d230311001c10510000440c28170103d03000c5403007500b03030f10a4101d00d000c0d42481c00c0d000b00010500c203001070f80300e0030038040d19000050540c1040311900c05180710b20091045402e01b01454441d5501401c1c9180c200c94501c02c20341020980160660135185031001d000d44899942c0c5c1c60000c10540c07000035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 333433381 1250 333432131 333432137
    0x40b0301030c0b04030c12051f020304120f0c0b190203180706021b0120010c03061802041511070b19030b041505040e010207020d060c0f1b03030906021315 68
    0x743c400e40c81007a14180c95029000d0003540340341011441945040300d100784c40c1401980c00c0c40404511a0f0785c0c1103994401e500c405a01c0b442e00d41402d920703c0c0b41c680107940c00d00c240c02e122414080e601c08120100c0c0c1d54411284050354480750307590004580f1000d01c120300355100109100042c5100810044a442c80c4400ca032000354a1700c00490300d6448803081d80d81d0b40181004a0281d56014101d141c032201c030b507031114009982682c41010f080d0380f40d44110402280e03641308240034030038400c510130003211000241985464a01006c2c00422540c0e000d4810400c5907120340d0b404002d03000c1c050784000301080c840c0d0310f485041400e444041071402202d100046842c0c0341d144919401c1a0207003644020820103130081c582e140105003c081c0c01440101c02079558200324000041e5505c000e41e8042901818000540e00342c500400341c6004c170990010f400340301d03045801c1103800d0858007900e00d8850b414030300801d200d038a5183c681d004c2d00400381071801c4650180c2007c181420f1080e040d10000c080c40d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 333434631 1250 333433381 333433403
    0x20f0309060612210f16080301080111070c050409020d062316090e07030b0409060b0906091b0706020702031903030f02042405070203070308090406061707031a06040b030103 76
    0x21060641c1c4a80781082d201d914035880405034890407605014100100b030f036a03000b40c54080800361031a81506d0151081340c00d41c1c00440140a850740c248a180d00c01c0102e42c41103807030412241c032142c101c02e41a00c10340d4441e40d19100c00c5401c5468a000c0c0703a4000390300c080e040c8a0340c1c011010001e01009120000c1c0d90310580c200014004151070902240c0a0a0544a00a40d0350501c80c55204510005054038103040c0c0f22034918220382c459101744000640202c0340003840364001000c001d03400c00c02405042c42064a441401041c100c8001485503d03c0d05240ca1542c0310320310726002003e405100f0010350325000b40200304403503141d5031404620044c4265000c00101941404800490056008042c00864000c91612800b1f4029105c41749003200c07803c045040845130b500280c6485002d8004440004021038008094100b9000e040090956820860403c4007200000005d54800620b080d04154441c1e03250314648410400e40154104050314003983c440e100c003030b041816407081c48100d07138080d080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 333435881 1250 333434631 333434659
    0xa14070f051207121103041203020c0406081f09061d060f0a0501120201052809080c010c030c0308040f05010c0f020f01180f0606050a0303030b1e060418020f03090606 73
    0x100304954109610041813070b489a0748080454121090451006403031208100205001c000020503010640c030030360003459004401802d0105880069000300c080d80c0c41400a0144220500c103641003442d22242d00050100107405c050016215901c0c4c8800380001414001c4241c2a010035898071501640709900c4041c4c03103145c04641111004d02c034940c80000343c0f0b4801d0780198402d9008080029214004030325010424086030709400c69a01548085454140104034900060003400e0115500f42030001c804c00c90341c2c50180c5110182c8100500704205031000400f00019000394021568101d00208407845e03c40c94040d042c2e102045503040580301f0030b07901000c1d280050049100c002101d400d0244803048503601c141c400800800c00b1a074458071307140c001c0350700e03180e0100380b000441c040c0d0740c085101031140b07081c00303000060601d0b60401210a40d100701d500d030712207504540803510460f81e10220740c0e1029208100038040c0e11410215208000107004e80c0c0c40c400a09036000b0700003218100d9680f482 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 333437131 1250 333435881 333435913
    0x3050c09090c061608030906100b1305121f060f050418031803060504050616030218010f02030903010501030c0312410d0501091a03070302060a14070f05 67
    0x40320080200d9000c2c007140d80c15414100090036a0345061008400c80042643d00c4085580044681451070b40c040420401d584541202c5a8004c1200c1440d441c41c00e070207051441840491070094034090000a91031100d1b21204000c190100ca003101960b600d0703d4652800741c009840648220294604048400b003040c5c0303000d20603850f08480e400a210244402d0340c0d42500c211501c40015180982d200341c1c004082406400b800303201e20321603001740442d850b2940c0441d440034111044117042500c10f114180f5188042c8202c920400400d080c594803506035194103e14503c100c2034410303015401d0000010810150039070b80c8d41520712034440b004a1080c200011101400d0f69907028903419805c0e2201c0ba080e10f094100f5210180203030755404002c403001c9000f26110750007c240205c9503507480b001040010018403402c0c03604122106070100500211000070342d1500c03113010280c0300d21800034141c11024004c41c80e042c10b0980034140ca6440b0403ca0400300d111200128040d901801000b1035480c0c4030705 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 333438381 1250 333437131 333437149
    0xb09011d03041d06040e06151e010f1103190c110103020901050a030b0604030206042403060f0329010305031305010305010617100819030201060803030105031510031b03050c 76
    0xc1c21505820703d09000212120040140a054002d6680c2080c41051642800305501c02c561061140b10801c1700ca80910040c8841034601e160401c28010420201ea070b0701200441307501c1e08a15001086c41c4011080f2070951103620403580903180303440504292280c001c80c0c02c6400d18011080c1d41c410740c0007500150140e1003034122150000e4005c202038258039000394043c08a90b28050150b074201600ca60110790164020f40103400c4200072480c144021000840301c3e44801030b4580f40c140101ea151080c604e84070300362400014001a44103070305140c00c1d601481d072140740c1d02e0001f1000345107581d41c1c2040b544a900003506404110b091480105003540240a1035040303480e180d41c0c0c039582c6125541c40d0302800170080c2401891a4991000044440040140c603010201000d00001d8481641c81d0107030842c2c040c0d500c00802c540041c40100801e6901150021404d003800007003041a594191140051001c5508018050544911410070501800304d1350815284690102d03202da407a680304102c4880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 333439631 1250 333438381 333438389
    0x207170c0c010905270a0f1a0f040606020d03020c030c0105040305120130021807050310050315060f01091a07120503090705061c1103070807080405030307080c04030b09011d0304 78
    0x80065000f170500681102c04c080c0c0d001d0312050300003980c4d08040e0002e0381a62900e070007a0902c0c0c40030103040481468800303000442120111030401800703161a102948a4500c2c2c1032850526034003158452800e0701c02e00480d56221038004c001c20241c68a4038020780540c2040440c0c2105c81d20150004c80c8581c1c030301d400d0a1404481801d1100c40a101018071804015030785c3c0102e802c503400356000e0852191861071507000e4030300e64541988a24014601c08001046a40b040d8480d030310040b8035844e030610940510b50031203000c0c0e941d06041e64a4000580d09046030b544a000d802600c0c026040c5c8100070301004c3d081d44c0384120090407500c1703401c2c6c40072a0a40401e6511036015040590100014642480108403020046045000b032040040e00d000031a1101c80c4003940f00070001003002a240e40c070511187d802071442c2014141340c1005d40b151b6917280401800f500c03d0003043e4001c02d1080e501c501c141e400031a84081e0a1605142c4020201d0203400f282e951003801101410758100c80c58004020394003030b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 333440881 1250 333439631 333439669
    0x1211060702060f0709031b051f050d0203060607080c0c01031506020309190b13030506090703030503041202010b041e0b060306220e03130f050406050907030207170c0c010905 76
    0xb51601c100c10f001e15440648064103002c0344e00400400103401c003112185c0444030b085100d444e03e14040c00d2240e624588010242004031090b445503402d90001c051321411014250016103070703511480864507078842c802016184800c003003202107403400d0004907d200d00c00c0c20381e414001c4078452800290f8407a050b00900000da042489615168140040b0f070107944003258000110b000d5072081c03c000c1d140e00c0b0503c2e03d414480c12480a2040c003004000c1942c200050ba0005c00559103161001840b6000180004080740040b0040030b44041c401d400283c01840b000f0801c003c22062032800503c1d02000398084011981498090129440c2c11404e0724400c01001c0c01c6001c00306030079140011981508503030b03101c0855030f500c481c1043e03c000704007070503102504c5107044400b941060440005400b0503808948070b02e04287d800c0c0002d89400c0111a0481c9090038056194030240c0f07400c2000080c946004140040c02042158410750001188900990b080e285c5003000d42d01e410038420381c108454200100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 333442131 1250 333440881 333440893
    0x201050406050c0a06180314090102030306011103360312030a181703190e03090d051e0706110307051504031e0203091f171003020d1211060702 63
    0x41c0350b000e200140f10310000d030002d450703001440c1d603546070466a80d162440c0980d051000320800705070b00b00800b00c2c1d81d000c09070307403440c00c260038480001c0d505e210007004581004482c1600420400d010415601004005010f2481d0200b98104d007401003600b08a14103000c88030100340000780d00340898280c040b113022030100362540d43c4406c565000303403240c81003640e0f400c00c1000d000400708140c4403041c003641f1030400b00541c0e40d00305030032000f0040c41c400c0c4990740386500c0c1c03a030300d412101000804c46484103402d4072480032035100c0d410301c0782c2400c00d038140000c0c041d2200ca149441c0140003190b200f040c1c40d5203440d880044049000303656541e008011006041da8000c0d04101904040c0e000c050b98400d100703241c001485240f8564400d0640000d0f1140805640301050314102481c1c28041c514100394a48a0904000d00c0c0e0a0000e02d41d5014130b1404400c0c503043d00104048a480c806d07050055a0050820b503249003140c03610403403007100d070034180c000555100c08040c0c94144c04220203015400903801424 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 333443381 1250 333442131 333442139
    0x60338450f0106030218030a06090201230a03231519060903060b1c060b030d080f04110f06040b03091006034d01020606040c050417030408010e0a110d02010504 70
    0x4001d510440b06c0e040c100362041088003a641d002c0040c603141500c118008603100083e0300c00036020304e4043c8120244031040343c0e48030010184520681c0c0d5000500d15010903000e0040030b11030310100c04c0c0100450541082c104000c850910240040d00c20345060704c1c41c45440003058070090300000c1c917003e100c00241d8465410404203100c0d401c001039002c0014001c40150740d800301c01c4102c00b42e82800460788207884040b00c0e02d030b61034188901400140c041c10401042d29040420204603a0300800060172050200f0b111269074552940300104818090a000d40c0d030354591200340754030742045075845098400c08249803000300d10341c001c103400c90798403c444030340c221283d860403104c00100c00c0d0045100c6030f10215000391030080958144041c0000f01c1c1c200c5004007514002410150005d00c19402241007a42009050354080c0031030b4111607200c80c035061200303181d601c0c01d402c600c240ea01044156092160300445414003241000a5610520718403944c4101c400520001c691100341c06408103000b403000300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 333444631 1250 333443381 333443387
    0x608060a0b090f0a0f031203060b2710050d05011203050910030f020412060b030c0907030b030c03030307030608060a0605010e010f0324060338450f0106 67
    0xc800740000030311000306408084003090485469034051280d1317445004003042800040305200601100a28043c00018101141c0072107520450007a21610700e82d00311301c54020860040700b0b000c1d254009200182016010300c004000d03410001900b0201e41c035020000a0319040d108418400b170340d16449541c10900baa01c00c00c0741c020340021054040c50303110040d81e6940d64261005102801f50368040d075000c018141082400c8444c82900940070781d0000c8506030a0740e54a40610b07600c0b11452030045084411940841c1c24080d090000581600c07011091208468058210343c0c1a111a001210701d2540e42c003403584181c54080c400c01e80030644500030b094455103d501090a04512070038042902ca10b2001e41460b1030340c0e0000e020544040070131003401820f030b05019100905e079581e2484050940400f0f00d0900300351054001c1e101c1c1000107008107107103440b0b0840d070050344416010f0100c211103444086880c603090314070601403039030741c0c0c02c21960080da08803043c540510910724915102c4d0782004c03016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 333445881 1250 333444631 333444637
    0x9010f022d0304090501060f080a1e051b160311030f07030f0908030a2c0901090b030a0b150306060901140d060f110d1409030a0e0d02040c05130608060a0b 68
    0x800014041080041303460000d5024170f6009203010f5135001d8865032210310041202401404000e00c56007810407045080e00480c0d03070115a024402c0300040c60b925000c045031030703821009401c50b41c4481d001ca00c1c11941c9050202032380041303000741c54170f25221400b419840d0b00c0784a84040c6541e1004180040f60210f8440cac031a00310582700c2e0307060070040f40e42c40f14051881c5421146c804000500c44c03c142c0d5a08040a00340c590b8224407000c2d83c03000e031048a0b400250131800501941d0a031300d51b5159240400c0c2d4040001c00d01003500815240b109050440d00c08900408104c0800d000f0300c0382e070011942c41c0c02c0110625040724030075861542c1907596142003100060303100005441c866250344102550305403070f20404841c00350604641b6a29490080d81000383d5121154100e1000c44110800400381804070440da8803000a15040f09000600c0e0001540400307800c202035005031500d61000341e156001001071110340c40600302000125030301d040451780c1400c00c950380707a00040c245504016202ea01c00103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 333447131 1250 333445881 333445963
    0x5100521010e0f13080301080a05010b091018410f150d080d0f150609050d0c080a0b09010e0a0203281502130f0f0e04050a05010606020309010f02 64
    0x1c070304044d0542d500c5590709600283c100d81d0041d00b010202204000e001d02c0780103c0b041c02540d000072989030010140c010500e080c071515486a055140b803800c082c503a81e1040380840d501a8481c03500d8409a44901d8081001c480f01d4900308503480c801c10ba145004641180c840d810340480303030145944903020170311455001c1c504950000b6040489100091804000e001e94405d034a500180f440c43c111404000d503005116a41e4010060f40411302006900580c9182a00c100303a40c51b01400107a1700c1d180c1003140c1030b070380210183e02415085000700515034102a0151140000038801501c0d042861521038181c03050007549540941109501e0f14801a0960340c0d03c0746502c0f802050b443c1c0c0d92101844544d641c0406600243d002818404a03610400c082d00503017034400c06010401d0400b1600c0f00d045d40c85004030445200350800150030001c0421262102c01da0180081c000e8690b5030750b0207540c0340c01070701440e4003041ea514100c2625920018200c162000c80e11905071401e446800003e44072400140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 333448381 1250 333447131 333447151
    0xa0b0c010e010c02060a061403060c09131406010329120a1a040b0c0403080a120e160f05030102090607120e030706050a02011b08160905100521010e0f 66
    0x201c1c0300c042a03420301c15108002507640140c1618641240c44500701d84403074106118041400095180540b0000b40090b440032001120302c0d95003a0381000a01300e0010b03154080f1480d803c00002401041070300c28480e0151401382c03024400c8040e4400c600003880101c0340500300071008004941c2052804420902c400c40c800e4040e58100d00c01c91f2541caa090172042140d456101300c0000f4401041100003039a45d001c0413036125207003498155170303414440b88103540c2c00354108103510f16a8190b140c8140d109101d483c1c4030800303d6a00c0c0840307140e1400001054401d2151215041c40d0004180c10180203d610622000b48a18500800c681d03e51480400c0e0817280b408020b5492002501c179102048000040c001c680caa264a800281c0002030a491001c0540c4a6500201810f4010560452082c54101c070042da01d1082540c400c207422642084568445076201c00031030031044800d0303003200041a840d0350002d00240b440ca0381c410440c02c440c0c3c003807280c00f101d00c1c22000003e201388150498143c000305a04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 333449631 1250 333448381 333448391
    0x70305090d081c06031502030705030f1f0e090f010e150a0b090108070905100302090402010e0114040b090310050c030f040c090504060209100e0102120d11030103050f0610050a0b0c01 80
    0x5041c0d2201e0f00020104070b820196600c8051043c801040b60340741c50440b040c801540345241031440240f041c000a4041d036200905000030071083c2e2000e0850315091400a2030259549994090b441c100602c2641d2160b124003035040015400300041c0104900740003000000d2464000b008509000032a000308065030351981c50b41050072503038511000900801106004041140c00c090480c421582d02500c0c0140215015a041005072204045103922a4090a152041c0c180a10050340c10820105c3e407003510120024000c10064105409000c2c905016030403540701c29014107541046440540308800c140509000080542603000030150380f29100c2c015410780c4564410f12001500d41c191001c0340c4050f004a20501c1d1410703e15411180640340e450403180701c0d0744120000c0d40b1140c190a2420958000041901078240d00d604150040380e5508521544c03582d59042698940c82d4011800360b40d030056034049945403110142ea44180c40303000b8070418000340f0700044982650311180320130519540710 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 333450881 1250 333449631 333449647
    0x915020c03010f06050a0e040b0103060b011107241110090503070b0f0f0915060112150314250b0a030b040f0509070b070f1103010b190f0506070305090d08 68
    0xf03004080c041403d2190200c0d10a0401e02006404e00440d000043d0788a441e07410030001c55070401c04981120b030803607800a80328030400012119048441c0f4584040d103d54840010301c0011051003425580101e41454222280404219850b50070313246030b54043d60018560342036412007507200307100c0309200e07000f00e07031501802c1d030340b00ca00030b100032240c00c0111190750040000810b900c6000590010050000d03110215501461120fa0f140c041c14641c100075903010100c641d0300440d803007181c20100c01d0541620150f5030b854064080c1120120354021405038042c202070507000390808050b5501091518864a410400500d0b5582c01101102080503100c0c2c1805c11305448911038182c11515804c004140c515000c1101480e294042d0722120004408111040102e405510142d200e0303030f40180707603554070501140001c0c050180d0001c15984042c0340c000c50b40076007a181d4600c2080300e05412200003090740d1031040086c60302440e503000c2e010480411031131606142191020403100e00c20703038000b4184108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 333452131 1250 333450881 333450883
    0x50906040e270102130927060e01090807120c170a030f1b03060e07051e070210080703060e071b06110313031e09030807080c01020d0207061b0915020c03 67
    0x1030042c0355511a54009176a4010620145260020b410306100c180003401200c0a0130491081e01484c4110030f01d00d4185641c00c000e099001038000e20700b07100080c86507152505284c07030103500140c81110b200314051800c6042c80d01986113026129001032a000c004100d0216918656010421800816565801c0204092071512510704500c200c05048040c8090104018007103510642100d048031800344d00300007004d5408400c0702c031003000758058225282240d2485051502468200a6120940000c1e0f03016640e0702070042803040c540c50340c00784805c1d95203100d550000c0e1826150140028070f0a190004800d40705030301991503601c1054009002070003c804035030103402c259002005400c0c0d5000e02e1051680c41003242541420510000b039400321b101030082c1a5084a100040041a01240103000d00c5140019542c1014202000795690313094000c20000035800080201d880c2d41c90280d80700d04c1c1200b80204a400030456482d450b202a05004d0000f15144c40c0880c0d400840c0709203a90002e168074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 333453237 1106 333452131 333452191
    0x6010308031915060f080f0c03070f0e09010305030301050111010203012303150c07060f020705250803070f03020c2d010521100501050906040e 63
    0xc0d140482c00a0f0a20010340c1c441c1d07440880c2d0004065402940010f40304005944100c0c2695484807200c440c02400d0b6010301001006200141b4824081c520015100c007060034005150014180000c402440c26042100d035a0000301c0104403e5070401e02030008610b500c07000b035003590b0510032508402c200f03030409100f44034001c00440c0010344003481000144220806540507074034000300700c20280d501c12041121f21514009002213400501c0c401e8800c22076000c6d014091610f4080655801807000c6049601031034142a00062600c00030001017800a00c1244180c032000c104d03013400307414035442d4001c1d81e00030072002007003820003c010022845090000182c0e0b08011071031200480380f17401880c4200302400c10021954803901e6008100700d209090a1001c2c0c1403454441d001101d050048904c01c0e6040b84c02800b0500501000d81d1030158401032540c0e6602542084003110f8103504 = true := by decide +kernel

theorem cover : BRFrame.Cov 333273381 333453237 := by
  have h0 := BRFrame.cov_init 333273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 333273381 ≤ n) (h2 : n < 333453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
