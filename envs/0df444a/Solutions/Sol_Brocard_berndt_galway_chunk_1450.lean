-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1450
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:02:43.905616+00:00
-- url     : https://prove2.me/submissions/7a2a0b1d-71c8-4903-874b-a3a70ef75ba1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 260611510 ≤ n < 260791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 260612760 1250 260611510 260611529
    0xc0a03021608192a17191b020108060f03010905120c100603020d030804110301020a0c02120109081e0702030a06090c0e1006030203060d0515090d0e13050702100204 72
    0x5600000610710045001d031120030500210b080fa0311403500313405070350310352010040d40d0f010b051010394102039182007122070704918101400030342020032101111070280f0030005565606403003820031903524410360700c1750b20280c040342e01100090480d28022440040b120350203000442d68400558650f441d20001ca541300510410125401d16442c00c100100c450300b03c954141408402e155801281c0d03490303003c0c0700c05401c200900002030300b0711401c90071200b10403402034003c55031640048001802c01d8481c1100300c0c40751001084001200d50140941402c1907040f440c441d1419880f0b0038003006204084848030015001800013001607501808454122401014082280701c441e2a000c814040641c11041256640c0828400000751550001d000e480c003505005070f59407500e10009040c2c4c40c4441005006208400c0f0450b01c0300c02d19141c19000d40b0110049801d00243c048054a41045e18a2401c0c1c100180e6031503400741d00015001a038220600b4019240c0300107c542d100000d980c0550041d0080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 260614010 1250 260612760 260612767
    0xa03060b01030e03070c09180c030c031202010509060703021c050a0f050115120902150703020706030501062d17040f0b0c0909040204110409020414040c0e06030c0a03021608 76
    0x10758150044468044241c0040c52824240360b13180b081c1c018260181614180d035403141c0040c03003c0d911280f40101508420090745440eaa0324004001034100c0c003046940048082905140c14014000c00380104030101c003520ba180d8481108600075000880413080a55800300c41001c0442e8903c074040c000c40b010b4101180b07014844200384203484d01a44030840031842c0c00064105517502c0b059500440003200004200c01940307000203048400c038045550b07a24440090f40500f05600000d0701802c8400988041c0030503039031070109591400e000c803501501203411000c3c120280e0081c0c5072050080301582008c10f003041c4211070011841a0861b01280c000104c03c0e55001440201410a9448441c284030949005184004107842c900d014000038000c0741c0b503041101c009943d42c1c2c1a2805024404402c54a981e906c405020313103150190740c0c05009070304d405d19185486100d60f5500d03060440140c03102e40346803900256800c0b0343e03000e222039904260b400c0c05052038200312080840342e0a400351140586 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 260615260 1250 260614010 260614031
    0x150a1b0206040501140c1b03070c091b030b030705060c010e0703030512150a0b0d0f020c0d17010b0a120f020a05180109080601060e1c120f0203040803040e0903090a0306 74
    0x3c41d8a0040000d00c20100f0004121178801446d00b2500d45580200440d80e04940301a6228554003640c00024151440241e000c506e00c28164001d28420140e01c041c08035560900340300b43d04984e000c102d290f4040d001b40b038052000d800c1110042030398550321000061640e043c00220b5060041c01d400c00ca001490000e81d132070380c80038014180b0303030002119003004490a4203600002c070256681d1103683c09604010482440383e40180d4000c0d82288072440b415036603003040b203101c19110180c800d5180041510304a00028506c81c459912303040e242022121446d00080550a403135803209001c071000000e40345c41254000c01624005480c0700000c3d9241c00d038882d40e020600c0c030350314004203280394100086800c00700320b5240009006130450b07045062501c00c24500c000401c0c10114000d003520150030225091008010381011003030300d1030040d0b0b621920b0b00c0ca00d98000301d84074440e82c800c000550340300b8401808446400340c1480d03000018041120b28200030743c1c001c52000240d031350007540e480395075001000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 260616510 1250 260615260 260615263
    0x2030a021b01080106110c0405100801110711012a0506040308010801020a0917010b061603030501061106060103150801050a0608060105010318060902180108030702041d150a1b02060405 81
    0x70110720180924511a0603020008050481c144180c0080100e803001c2c3c00311545083c030220706800c50160050001d031400280306c4c030742e44115208107400c45d80303480705400401843c0e00a0392903da03441784903080301c42c802c0d20044592442001c122903400009246850f0104103020398442054802c101030540752134142000b920242d0140c0c0200b4869004202441c001c9078440c40e0131040c0c0314000f540c10201d03680407440310300400c10424030725004400000c05101c7d0910766610f0344805442590241b11903a00c2300d00071100c2c285441ca0f519010f034041c0700031030800c1d800b942014100051240740c1014107a51070804509451085d12400c0426030748a00c00d0001503c18450380703000d00f600303090034030404012400300c24540803d180040d0880d995544d9200856881d000c0340b07600c03501e5070050001603503180d548098481c0d00c0404102d01c81c42c5000d64800c1e02070071880c10020b1400401c00646880302010f24501030038000204490400f6a4480c581594580c000c4116100c1841580c002d2059140c24030b00507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 260617760 1250 260616510 260616523
    0x90103030c031d061e040b040306020904050a09030c060b01030f0f1406030606150f07080427110f0a110105100611010911011206030b070f030f0504170a120c02030a02 73
    0xa4410820300620f40d040e601c3d010115400035440c1e40c1c1c10005400700b16032800e91802182c01c07038122000c00140000c10b010300d540150440b240112420000c45d00c620b0100d80c1100d062020084c0820300c0120100007080d1294810003000e0410305010840722901c403021401c4924500588120179035a080469101e0151300b0015800707181130340245018285000000c0c03418240b04491005034900140500a00300f210040c0c4080507801ba0090b52a0b03505da1041003011000c8603101484c071208185041d10075062800303804100050380c00d80501c2c000a80c034150200d42e01c148400000d110020282001031308c001d00c00c0074865001955541811030400c00d005042d0110401c05c3c02d03007a810304943c00003085000180303900307800013420143c9660055031001401742586a20241024090008002d01c0300d4108242d0030081e1082d0364104200e5280c0c1039001c2c01c0b902d040e00c001c0c1903440ca038415441e20b403000c8401030100d029913041c013540c40c1592000c1e04090391621180c40005030404500f2100c03650701000315 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 260619010 1250 260617760 260617787
    0xf27010e01021303060c03060b1b150f0417130515070b0406020a09050f061207090909050106090c0f020c10350603071a0306130c080610021b040203060f090103030c03 73
    0x7407110501e27282500c0014090802c01c800000f0b403100400c09038207810400c41c1c5800d602254603900c6440e220468040f003c80403201a0f40200c1d200d54086c1c0407200c290104d98000501120029105003080e040c40101c140a4a403580d11281c108484e6001c070702c014034240d01c13461150502680da1600b64200604800709544a903004450b4510280309541d41c507030a60384891841a00400b02d5541e00340110f429031850b60007101c805141000c02428050107400c4442501c400342c0c0140107540800d0812038521007000000801604022010055864a9021203855448514110041071048481e0061030091f2082c005008550080800765039403840068550140f800ca01501d841850a04080c8003000090072a94035200c0000c000350b03095a80441038040400798041c108846112800d010700040c000b5118584182c405650880345c00e840021050500105109448050380c2e140c010300c0040d400150403503030703c40541d440800300c649072201e5160003507010307a907400c503200b80ca4140500b2482c1403800307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 260620260 1250 260619010 260619017
    0xa050c01110d170604270c0b070b16050c070e010509060d0f081e041203080a050702120c010609150303080f04030516150e150f27010e01021303060c 65
    0x480c808801e801c0f1044500b4940110b06940c0c0302d43c2e40000181c0200080b221000c110044000c69805482d880c070303140710341d0912030100c0b84ea045071245003014076405081002800ca503008000901c168030944494100c4a48500300303103041620080c005401d00d54150042c1c903041c00c1010040100c3d150040c00d03d81c2040081c4c801c0c072981a40e0341c03640d500340d6100c18000b8044c0f038000100b0003161548103040180a11405c1c200948890300c0d02007116130070341c40c15415000a100340f0041404403000740b02c1d90380034055a8000b0301111004210001040e0001c8032610642c3d541c45400007460031a5004040f04150b586200c1850729046203030103000d04030058101c5454681c07000c200000a9000f0045a40004100d000000a00918034003407400c5030b00d400000000c81d06002034043c01140004400c800ca0003401d840f00801e541d040c69250809600700c8680302e20100c0119036078980c1c50300c4260404034650140c008100240113800b06400da0788045088031313070525209401c00500c10f807841504040e010718034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 260621510 1250 260620260 260620273
    0x20a030210060f060c030504051e040b2209020616030806010906030e070509280501330e120d020c0f01080402180c0c010e06070237140a050c0111 64
    0x4400501021083c0602ca0a005c0e044548005040c0030344182d900400006000302c450341d01800ca0a41c110350804503a038003039030503d20f100009240c0f10450248480744c541480684c40c00500c1254042d1007500e90903a00301070200a070740f407000100014188054025200d03040e1904000000406844581d840841098070b00184604881004685082228411243c403507080c0c66905200c010b10b14441860340443c00c11481c0420300d88030700e802003812101e600c59051181e801c40c9070484024414010742944000c400d00d4007941d414010078400c2812000035003009800a141c0030401d141100340d141580160303122901482452400e07084c04007580d0401e18142c0c1807800d165000c00c108078251520144052008070024414200c9003003961a0802290020312000600803889600c40c00290b900700014003030744c10001004e0b804181e014110b08400d400d050980035801c0d10502d40e05011000403100e009200141820982040000203003542c01480a07000d416000c3c00007508544d891030b07047c1c0c0d0a80050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 260622760 1250 260621510 260621519
    0x3090506030c03010608190905010b240319140708090d0507150b150a0c0c0b0702011d0103061502060a141b0d020705070b121e040809010903050706020a03021006 71
    0x1001541d0468041d42007104a50b00c0d800300a400307c0705107807841c0245514003401c4034203000f1705400c0400d241200f0b035400c0036480c140701030044100c0301051031840c042d5410004910b03001940551000d0055200710002001c2e5200102d0500c0f8940907140c00c400101d01605101c0448002c2c0b0103507043d02c243d801e0681c03030b0680c16540e03a01c3c4a00c01015880c50076036960201101034407088004c2040c030005900a581e56004128080c000240801080c0d0340100040400300d00ca508010881d01001e4058442c01011881a210140742042d030b0404141095114940000c1c003080c03c2e4055034034000d054024043c9460a2850b40c01218a000781500b400e403601418420400445031a580305042c040e00d815585441103d1800081d00c1a0380c0010074601c188180018541d0015002d030a0704000504000b84540320740036000c00c99180007900005440c08240401c1c00664604000c0c1a202010705007082c40035602d45440b4106044d592008000d42c0201000f0310030158103105100304601110340400c03209050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 260624010 1250 260622760 260622781
    0x9060302070210110f0319030b0a0803161401021602030c01080114060a1e0e030f071406030402030f0f0102090a090614150c062409070c021909090605040309050603 72
    0x2a8490828031560813040a08141c091040314400c04203141244d58900400d10000d17000c14400d12007200281c90054092000d00e0319052003030488048100039810140005008000306120038001c540764042d00d411010401420300282c0301c0c021405100022103c03980c0140350502000070030031410000c031040180105641c00c400303865445000e951107626555500d9055414440c0514280310200030704108000c215440805410300e914150184c4150035480703011507a44605034043c0400d080980c10306401d09061000c00f95a03c0340c002400c07a080100b1741d01c5458117100240004a402da5000a105802402c140d08010020480c507501001054030f0b180e00e10304c018482e0340d400c620a403540d54080311070300c05d0401950100d8403ca000d9038a24200017a2401a1221504a03003213501c4c4081c1c608560707807400c50141441401580c480ca0a202010383c2040080280060300140c50702c82e214010851a1040c0716102509208440000f16401c190030013410b030000300d50060744506000c004000800c0e40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 260625260 1250 260624010 260624029
    0x40b0d0602030705070633080c090709030f0501050109051806060904020301060f1e240311160b06180c072012030706050c0a092102041407090603020702 67
    0x10080030068407078841d403104131081c2c4501480500940d00701851030180b864211800d0141c0c00451580c004160030000400309031948a00c070b5410650014640c010207810b00715035036a800383c142d150810b20355072280c0d1101ca00c5807070384005640c541c3d90b400051043c1109407203140d4110340e850018611444400014640c1d503000201198020600c241c080f800710f403001d4102c072010302804080241419203926401c0c495154904420402d400c03c52030018401c0082c000581c118a140c200d15100c07142c6581c8260007a10400c46d6043c0c14200400c808500301801d04011401c0c144201d03241c14003400c100040144600d41e0401c1451445803510a10880c008648119420743d90300514008110401428041440f0f14040b01c01d600020b8035407038401132900120041c07807403078480c030420060782c3c84685075090b690040941d070501160440106100540d10346258010111070b4031104002e0164a41c04501503560400c822610620103d09000444da040306c0b044000c1c00e201d260031803c0c03443e280c0004145c0c41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 260626510 1250 260625260 260625263
    0x270b07060b15030c03150103060f030308180610030203070b03060604180603120e1206061c060e010c03020a09120c03120509120304060e0a1203030209190906090506040b0d 75
    0x180d8580040c180740c0c4641071000e04241c82a8142034691820101c2c142041e44100c604821612070949420211760003841110b054801251075450900c0c11130340c090b95003040141031145c0103c425810031020250801038148910074400e107da80c0d02c0d1462040c10b1500d8416000800d03220b50920405c18292120030589007185d030311744504d0703003032929003848a00240041d40020700b00309086919444c1715900503854245408042d208200404115841c1f99241c100c259802079008075072075851007282c41080d034030b103000d1406642e0025541f02070039499800c4a90805000b00400d8000c1661030384c094100341303460b0061284003107484516850350364483c905a0603010041c0340b446910203001c4a01d2140098a440000c054010012141c140214a07500d400900c2240001601d81ca1005403038180151183e0454402922420488009640640294001d0080303541c00a9040740040844211080303160010b20642c1000a03085040c200b14200341d6000400950040341845000040f686a04c184194400d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 260627760 1250 260626510 260626523
    0x307060c050d030507140408010c09080d0e0906010314010305060f1b0f0a0e0d11040b10120c0c0803040c030303050a050610030506010201020912010614030d020318030a0b07270b07 79
    0x80d61030b2101a104070f0010700c8a000d1100000c50082350f1a0015070003c0010001915840503d50365841c10542d0f4000b20400c00000039245150072084d4184414041d4010605040101e4900800d80701900c0e50f507001d0313000b0360321640208244861401d0b001211600300d07181c80003000745902e606041401c40c0c814076803a020700060005004507100d10403211028213035001400054000014100000d40c62404100d070303803240f45414114212031808680310102d000c66500da91240a40808120000b0521a4500e0040c401c88544003000140c0740d400443c0702d10311554000525604500b030007030031104000c000103103141c075001c1402141d0351813400142c0e1844c040d01e00400c4503951000101c2c060b0041c100007603040800e00601200c00d800641018007501c0c0003a1290610009001c105a074070610f00b020400035810030400081c500040800110020350b0280c00c8030303a01c0071155030b1605600021a0580c001900000407100c1c0903054800030008280510035000c0f5030b6044c4042c5440d00c0c400d090004250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 260629010 1250 260627760 260627771
    0x6160624240c061b0306050303130b090609120610050301060e04081b06090c150412170415110105150109290a0305010501200c01030e0102120108010b0307060c050d03 73
    0x25110701d0002c003050b80e201d5402c3c411008950500d80910815004540c082070800001040f1801c0000603118030040c141901c2c50000e04d0542c1d0390070240d00409180d600a0420882101035403102d041071070365640010020031991415008800000c0c11a80115200b03904000301004180101083c26401c0398005982e50340e42d440f140c0084651040f226000c5c5d070503001301000c016001102290000c604a400d0303894400364060705a01100900c52805603070881140700b0f00e0880415510540680741d0813418001500e1b144d124400c16454646a00c072079000a08002c0380d8030a201001c0c041d403500003143c4001000000c1000300064500d00b02c0e80a901c3d1b000d041c406420605145205844000e0141d2415455072191101d0006001d08803d00800d07000c2140080d50701c8503182140c6c6008030310304001c40681880e00c0000b0044001d03040b42c02044140d0364090008000d10030315a940340307000f001070704000241e404120f070902d41014103e910802c00d00041c4d15024010901c0130402c0d00360700c11940b80000e42c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 260630260 1250 260629010 260629079
    0xc040302010c11130c081009151203090b121005010804020d150b060f07050f030c030a0509060715060303020c03010b0102100917030c041802070201050a0e06160624 72
    0x40300810006a0004c2c107041944440d40140c0090b00180141e24403e050003000d6150300780307d810346560916040240280034404c205005500c04440b61641c440e10f400d0a58682d1200c0c02661500f00c100040c1081030840c06101a2102c58600310008203020300b03003217a01e45001e4000482091944e00c020b0070700c80b02c0c241480200056075104824880005040c103850b40c1c034080b001700107a0000c480c2220f481c8150500350f101c1603000016201c2d2909a100158a81080c07032030211119080420360030340260b41444000c0010b4030315019032810b814030800c0082e00341c1c40d40c20003c4ca00141610221b02a901d03003d012002a68041948502211449000b2030f00da111031800701d01c0d00d01142c0035000d2200c408424041008180d00050040301d1440c001c1e01c406280346410a0101d02c0f4902c802800308204000080740a030189064440c900c1005001504040e0094030074500e507200d120048a402e95260381c0058800508407070314031032008800b455401507003840c031501d0341c0800032801507000000c001951507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 260631510 1250 260630260 260630269
    0xf170a0b03010b04110c010f050f1911030717151e0307050303030412030507080705030f061201110406140301030c050d141c0f110c0103020703090b031e0c040302010c11 74
    0x70701c940c0d0084c2c81082000700d088044c0c10103401000d0360405a50a09210b42c4141d0791034003509004004410907020151507124140100081088030988129207600d64102d500c0c0e481c501841c410350391602e86000e8001c0c40300b0601c10307411000300183c0d40748840d011083c400e915901d2141038464400b0105620100b28a00080d2501c0080d510542d03042c44000100301c100018a404144a101d440c1c90620154450710b009460f000340403600040055401d20001e505082100c20240d081032000d401610b9540650f1110b43c01d440c80342642c0d01c000300001404204c41540541860036003052803040e54250350569498070040480c0c4c0c810b16101c4c0d018440480c05100c2c9003813503c0000c1e001c0c074040320846880012107041509140e08001c0100d039012000024040c0510321681408889001030f2144c409080015002034010385d00c10707002c0082d42000400c1c8520440025402045031610180d160140d8108000b00d22000405c1c01d00c4e841000d110400041c1d0f000036296240607801000d103602040700d0070119 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 260632760 1250 260631510 260631521
    0x30201060f06031409060402012a120302180402071a0408040b04140909010504121407050a111507121202160f051902090f060d1a01060f170a0b0301 65
    0x20418141c0e80ca60015a040d0036030302018050314076441454480d03582c40c002e2170301c2e06000c54001c4d000c5081002903840c00c04528202c548a0300100b01488078220094943c407001d803003d0b642c00b1000c264005849119070203800d10500900100310703420b40c5003803065500c41400c2e0342000d00c440b00540031100807608000f21034058802418840050030b44440c0d03640c1740b4048106e011f444841c001c4034440c010a003041418012148915001448060a902ca5101c112032024034a01c03082d80900041c01004000b03a41403201d14005030089280d010701d8103408c020458045c2d002007042c516428108108000500004071401104109060003204d82100c044c4a4011b44240c9003a000ca003014000b5213810085111903090007540101c08032403441265280d1000080301900004c3d610070a03200000342d10269a40c80c0390741c044005821f1519451113560742ca01072428140c10068101d09000050040350740c4440341160426040c50034040700700320081000745011016100301c0000d512101c417484251400d4000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 260634010 1250 260632760 260632769
    0x50d0204020a1b05070906060305061f050f1b060106020a02130b01020304050d080c37081201060906080609100e18060115090b0a090b030414070b120702011a01050703020106 76
    0x183c070400b81c52498800e4070760f1034a000d41003906103481c8001c030b5400d1091207024400c00001d805003103030036040308121000c0f034071010381d42003001002c0000c03444d00280c49000d40f201104030012010341c6a02010140d0070241c0582150085601c980c0305c690259031915882e0300b484060107070004514280e200102e007944655001f094012080b0000d8604103c0004010b01964901300280e421000b07078020404100e91909507140004642141c00c7c0c0d80d03202020f01c1c0c17440054403d0044a01d0040e05481150000209034403000228a00d14800c20200350002115980884100c41111803450004139401070348501340550505041d5210026070021014040e07a060f40b5003450460b2200d40e541c0c1c1c56150901c203103140300c600054580000117181c06541080d00c2400d940b688800c80c0c518140150010241c100a00a4942c07074144550001d40c0030f403e20031074025050343c41840d076071070510301d0103580c807030300090302000840e031610411080e100c0d203d904480402000340780195031000b0340c0c03c00728050000c5412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 260635260 1250 260634010 260634047
    0xa0c0b040f050d0f020c10030f05010305010501031e0503070b1503010f0c0306230f01090b0d0914060601140901090b031303030c08040c0b0d09080a0f0e0a050d0204020a 74
    0x610051210092007090003078400c40850302140d00c2518201c031031403540c07400c20303001d80e000c81c0c105034603850910702d0b03c90036408070b01d00090724043e28840302040d42e40a9006440340d941da28010f06c140804800d08568010004000301e6000c080e6942c0e01b0b0f80c9118400f0040c0013258503c0218556101149a20260b84030003402801500e864000c00c1000b00b11441c1c508001ca072800c02d00003003072141c450103000f40e8074602c0440300f070003042c00c03050049000b48590300e54100f00f0441404102d50044801800d030b4003c6000c00060071140a1916035002d90342216040b0f510f60105040020585e88a4501d1411012030440e42e500c582d030840050b0b84a0540703400030402e03514048200000c0b1550340c0d10301d402c080d0003542c06110001e203000c011703208140d007550094007600c007282c41031080f034620341c008050701800000b00103045002a01e6501464000c2c40201001407103990719032071340d1079010f00e0a02222000f01c400c482075514103400181000302c03500c030007401147c0116400030340e0340c0107200c001ca030320320b500d41c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 260636510 1250 260635260 260635283
    0xc07110111010f1b0903030203071119060e0301060501090503061513020a030902180c0409051017010506040506030613020103050915010620010b010c03030b0f0a0902070c080319050a0c 81
    0x10380401414a000d000100f0308452644d452030340c0d00c20030101040780d41580107141b80034540d40310008581c000030758103504080d4007161100d2215560700d130740c801003107036550310501d011550040509440e40c46e44a6410007041c030b00c0601c003960340810356a411081903444031005030f200d480858400d81e113070300c190801d00d4030100d5a81c06090f059000012118400c82e1341e81d2081c80e00c0b441307150640304251150b0210440501061021a00592004ea0490214900009910b68960403840b0010847c014920265141ca0920403a82403034040c0d50f80041e003c0b4081e104511f00401e1000040180843c060b0400d0b0725080401c0c5214000d02006090110080428206617110400a0f040c01504d1455106100000500300c3d080030045c070490269420594801e00c55403a0798400310090524003a041e03503c1034111040724066502e82e071040780103206e1100b025844e04228200580744440582c09500c603900100210140ba07104083c03040411481400d1058490b50a60400c03142c540621380c00400d01121f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 260637760 1250 260636510 260636531
    0x411042f0c0c09130b090c0d081b0d0203090f0118080d110c010206071202120a0509010c020c0906010c0510062304140a1a0d060c030e060c0711011101 66
    0x4000810050781600c1c2194240b0044205110003c802101e000c100340800780304590000c0d0f11000d02d10b4104a503001118021400e410004040111103c021910b041d400291002510400219403124000c554007038142e060721484044c0d101d200703d4840b10f200d540c1c00d15261074141e00800007007203440300b100d02d405500c94817080840d0396140306403990000303ea0011403640300000001040510904180e02414150301c070301c20145c8418101c0c0b400c5c640407940901c82421207400d101e07111841181400b9020800c0d0808200f007034215800c15001d041150411a0400c0d40c0303440752140306030040001c0c80c01000a5000b41805403c10103080380400e815800d004001640000c036a2420108844851000c00513010725001c0004a400c80070403686140c09080c0040c0507142c8988c805c054500d15003480b07010784c60444000403005060043c2c11103019030781e5100c000b4507680c54424445c1d401d0a0000604087c106031408030894002c1010045c0381c20b01d00d49149840d030748100000e400110081c0c0c000e10800902c0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 260639010 1250 260637760 260637851
    0x315060a090212091915020a03090f03031505030d0203030c0d140406020702040605060405090703090606080f0708011a031c02101e0b0609060f091f051803010203041104 74
    0xa41e5050610312640d09000c05e86072242012403032442c2e22803406000d0741042101c82002e5001043c05009150341c51003843c0c0420b0481c5021140684079540c0015080060075006080360031940000c2d00039403183c0b0025600c02c2e000400c40f90408040303440c0315281d2421580403405080460010069510408180401c101d06500500390141c1708403010300c407440d1a6003e02500740139138464181c2c0034000c0c20104101c0790003a400242039601400d004102d01d6203841c5407620300319400d907000c50740f82d00481c802c002031030084c8109449902c00c0d880c04811100d00500280c3e6603040209164410b1246c00020030441e4001c2000b030604407103466041c4268a2280041310000451000643c8600d04114112440c1d00d040800c48610001c002e0125081c010b107101005035a030450045103808c0038011481c40500414181500100212507592a6886011011901d248100c841c11f95010f40e005005100016294084800c028482650001103018141001641c400c0c0e000d2030801002060101c14075031902c0c0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 260640260 1250 260639010 260639047
    0x1507050706080a090c23220f050105010c0228060309021c0c0b0c0a0203190201090f050105090607050c0d060f0b090c031f08010507020c0405150315060a0902 69
    0xe0325201c5501650324114200c0a403000c1d948000c5c50107842c2501800102c110240c0c211020043e10000d12441c01d602011030b50580d028262014241014082482c00000b1070282000034200c020060015515100002e000c9100c0703030000910405030f64040c032083c1c010200040e1040c00f880503040f5041030340c41902900402060b4000e1703004520034100703030307201e000180076000313019078850304071f0010034981106c0c4103094001d2400103009006032030210b409664104214801c000402e038884031460402d00c005001205c55500002200d080c59800700b01c241e80040c01e903444c42c0350903031f55107544550f28507202d800e1030464002564002c1070300c198041401656400f680a803146000d0030000b1440e00b408100b03031080200c4102428038004c00001c0d17042100311200e00c11189100721200c11007500ea0f4116030a6a800726810001a8043d10700b013030300752801c3d01525401504c107002c0b0f6082c51400001213501c40c0c0300f4401c52617421b0001d4000c507140d5242c400d241c41c0100a1610115118940003606c881d070300f0b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 260641510 1250 260640260 260640269
    0x50112020a091e02210408030a0b12150703021b060a0e03040810020c01060810020c060105100203030a0506011b26030606041a040f090e0d020c0604060e15070507 71
    0x494528046600c9200f84120140d81c0203080701081810380100030080690b102e1844a110342c404440711040f41c0011005690080b803140d92210785919090b00b8800440d074118200da4864282500182c2480c0004658280040c40e107207a9012141d49100b03094029120b413940c015460700a4000c107031060b000214129006006503282445000310601c010b654a00403800340030010f4100034130008400100c0d9000340100400071700085482c41e03440001d90700b850f4415041c0b011150300003507901a1644c0501c10b00740034200464030681604140c2000a560b0300004004c042400e680724040343d00350b030158541d0441e1103120031040c558210709260100000050200c81040d100c0d00c21005c907011001101501d11541c3c1c081c0000d41010701d407040d141000c1240b1002610b0710403080001081288081d60b90b00081c100300d80000c9503441b44640854540712500502c142150808006e2100c80e03078622048804a4109241400d00007804a00041200c1d040108241090341e002450804101010a8100c102c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 260642760 1250 260641510 260641519
    0xa0e010c09080d05131502031306051303260f09090a050411010f17040c0305060f0106120c1418030d020724030e1209030d0311191205011202 62
    0x1105082090751910814007952060342c00906222200910800c05040080610341e1400b40d5a40d50303501c4625080c0d010710920005800016003550400107641c1e0005c001e000f075280240c40c006003686c04001080c401e010040030228000400041c1c0452000300800049201400d01d070b0f00c6040e440c00c0c1c0b9190b40304190150113180448002075207400780d0301c96280700d41d8100f00084c440180c0640110b800365009000c0700b040c40f48182c0001407e030354001010b8815481100181851815070030411324103034008241c10f07a010030b15001403051130f52101e80f490390b2501c4104040342d1100441d03002e4600130048140c10800d030394081503020b03c0d02001081c0c40342d001d106400303968200a03005012a111025405039080707042405810542c3c0002c042d812000c00e44c07007441c0010300c0d0307003103901c1301810040c41c0b00c18231415207404580c00105260a0100a010a2003070504010000121700d03182c071540100000d004030a82800d1070500070078064140c040c0000e0340451700f044150b07100c03107510fa00d003802240f00380e024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 260644010 1250 260642760 260642771
    0x3050702102f0a080310081b010923060f0405090f0a0605030a03350f0a0606050421030e130203040b0a0b1305090c030a051e0106060c060c0504030b0a0e01 68
    0x940008015842c2140e07400c001810203030725283c035608800d03800582112980b064012001501200900c883c0003a00325401d01c80c40e04014041c0010001c888030f40002c0c0c416145524058100000c1040c11806464140d901d20b403142da0b050130700112070146910064000f90000c080000218800485610415200790b0801c50749032030784141566480041c1005020034044120104460080d42c0c0141c2e045000c0d01c6001000e841440610424070015a444003440480310706102030484607028803000383c101c0e8070301542002d1805c810745c400501150120700b0b14250525041e030a1512403d000b081c2a1805016800c00e8144c003e0b4060095100311030584041c550440485c103107069038014000d40c0d4400504009078004203850010040102400361601b83c401c08800b41079584003408542101400740b4090500e0400c07088440c0e2490b0320303114500410340d1400a05003d182e400140c40305156411190028178100654800d65072071007680c00203414000f0b00020414001115004100b0020140009126 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 260645260 1250 260644010 260644067
    0x10c0201020a0504030602030408070807080d0e060705090112200705010b041a04050601020a02092a0910120b040f05090d09182c0a030807110c010c0305070210 70
    0x8034010b0201c40c0340015410002000892015006150000e0095036940d180801700d41c0e07101030319400100e0440e040b49020600c5498400c3c184680302c11061540e001d082c251611500080861203070801c81414032007851603040d030840250b40010403880200c0c0b03145038590701c4c800500525030030682c4121071791344c2090482e50301c0c0d04103800742c150300341414480340b9050905003040202503d001000c4134110b108454500f03026980e03114000d40244100c2c00041401c4401c500700383c034611140005e08040304410080c1103419100c403102c03864152414645400040d60814102d4090800c803840a54000d0030607101c919210044d50207903004040e800100c0300c0340790318a2019100c008030b1788100303844a858200441e03d5809907400c500e43c0044441c410401030b200050080c2c4102041c003013840000d0f030200264004140d00085620707008001814011110106100e4256807941101410386c1000049815181010301590030340d01d40940c01003a10101510014006240b00d41440c00d013112190304668202 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 260646510 1250 260645260 260645263
    0x70806180706050f180d0605090c0a26120f0a080109180b0c07060908120112111009080a11090a0e060a0b0604080a03030b011206051c020310060611010c02 68
    0x704840c410f4a500d0f0405001c0440c611681d048811003880d504034001e40305440750b03681107003030340120b01c11807000486003009603c01d450401e1f41c40702d09001b03865074102031000c0e280e0b0b15490740b03030b150740040074091100d040d8010904054401c3c05014032041c0101c0d40007031000c0c50314040c094010300307592501016a40da00f042c7c0d041e201e10048420781d00341d4080201002c645260340c00c0da0700941960580e03142500c82c1e55107908861507004107a0341c54901013540d0114124a1060131700500c2c500a90100050142d2100030480c070306600024031801c05600c0e9200400e0080c2010f00c000c00f016000d4a6000c0d007030742450700002115580051084220a000927a072156a10854821380e008070020542550f500403010000c0000039017141e48103d040c000058680710070054180e8180c402c1c0c0d0041484800740d030000d4542c0d401c00c0441c000300340c10004180160345803004922601040941c42d40d00c840d407a4004203040200e405040006d850502c600450041e812445405480060740c0003045001d14200c01203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 260647760 1250 260646510 260646523
    0x70318030f030c030e0a0b1206180a020304020a030f050f120a020a1b03020402070309090612081819080123010f0605031909030c1a061003091407080618 67
    0x1054140189818000b00b4810703280407088601c40c2c24465403124030200081c034000c290780c1c810003500c000068002c951178003040d0000d40240e81a00c81c2030070784003041044000c403d4000d011940b403980c00b0000505555500151074015038014040440f04052802c049440d1a044080080d1502c280b01a0240010b80b4074100e408146896010300341004a40d640c040101d2024030b403200d4006007541300400541d84510042040781d1084d1105c607981843e2a00400a41d10140d00082e1583d0321040d08030003180d8084106c8604001c000203080714268013900181c5056005d42c035410003400c2030500850345010540c040b007500040e159003c030311070f0640103003444002c109008601454013803090070000700e800703070028540203800d10090390100d9141d03000d01401c84003404c0c01680080d62144014080c4401d050584c0300c8690342507881e01d0300b86040004030304410460352801c810181e4032400301007070092075130303612202c03a1221059400c580ea540c5009680c1d0413040d00c0e900300c1040700350341d035201806e00020340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 260649010 1250 260647760 260647763
    0x9060b0c1501060503060d0302121b2a0f240a02101e0507090305010903050405010806060702151305060705070306050609040b06010c0212030c1b0303040803030a090f080a0507031803 80
    0x44d1495030f81c504c02804140e010740c420481c103503c20300c4900300462329090b0290117640d0306500f500600f00c0d110100989400f049201d442c2e41e0f04484103d68031120000b103540310814000340e6040ea00c646880300441d41c2c20404840e50000c444044016040729517016004110090340c1d9070860b03e42d0001e80c00884115441c420840046c074044518140b00110b464007d183e1024103070415407195940c90315a80d00356484200c04400098001406000e151703084007403581c12200981c3c400d8140041d5a01280b04084d000300040003094002c0707003080d00e03040001d242002502d4007400c41034603522a80f61041c0d90f0002800211219800d040000342c050524003c4c0620030390f00320480340042e4481600656803e0580c88003a60418502e800c000c40c1c01d5410402400c8482c1c0304002030008417812052410035605d03040126100380c00130001004203040010589401c64001e101c0003940c0350051034880340f26030301443c0080c55200003059180b642c0b500725015148281c040d45880210400c01c614140d5a425203020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 260650260 1250 260649010 260649017
    0x3180609010b041a0f040c02010e030c0d02060705030f1f0f0602030d1a03062a04030b040b0105040c12021b060408070b0a1404030c050f190c09020c06160909060b0c150106 75
    0x2400c10140303407c1d00b101c5200c48035030000084400304010020304680c099010010960711065160080d2641040b4007070b423106091030a94150700300b844024601c0d180141c01c0340070401c01452040e036401e0f0f16a0b4032800401401001c10b490640d1900040c0d2281c002020040c11107240c10411204502c550708d00c0080c01038020702400349a60f4400300144030401e10980e4407064041141030000d080908001400075601416103031805241602e0301005025050304564020b07800c0c02500e6400c1038104a0103a426207030040c0140c0c85061400800b04a2500c0780c80c5047c5030320484040c082800258001819404d02407030690350f00d5502d80c034503002030380d2601b0842c400c2c4d009140002004a44940320305c2c91500c2c490425074003560041201e06160516442c00d480d400b280f06102c08040020100c50b1a00411007280b040d070529514104060303c07684024203e1326080e0404030310007041849405514044d0429090420019441d04400122600110b0760b85103a4480c08200052031115850424103c0e8035554 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 260651510 1250 260650260 260650279
    0xe060d140f0919030302070b100302101d0f0111060c04050310020c100b120717011a0f01050a0228060b030f0c1306080105010b0306040c18060503180609010b041a 71
    0x26002d502d60f02d0101001c1e0209a0b080c0107850002d41a150750900a105420750340100a00f5801000f0360001a041c1c00d0050100507210000d49442c0240c400795003000031584502e40800c81001a140d900700090001c440d4001c840400c54540300000c0900103070340d403c0e002c40b2150000c4041c41b1040340314031070303c00802e584040008042c4c0c015a40104040c903401400b2404092009a0010b01d800f820741c01c0114001074170940303107440d400248206507080e10041c01e40d895035554000800c10141c1020141810003600050103501b0701c2c000c00c00741c80f181d02d41381441c400c001800300f85450b000c0403680313086035403d04059128400f03240014003203178001302080140c5051090307075081080c544000148a180c1580729500022402001c0c420107000303258003070741d85a5918240e0204801c89200345151010300201c14171522881120100c03c1c015561241013040e40da8440e1130554860001c05540c00d222449010100508030506400205c450f580c10b58081c03102e10404216100a4120310440c241c1001c0100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 260652760 1250 260651510 260651533
    0x3070c050d0c091e0f0b0306130f0807020d0803011512020f0904051f140a0803030c04090906181a09030405010f1b0b040c182a0e060d140f09 62
    0x592050f410302007402c0004c0100518003002500b5151328101100c82e1964442c01c0c012a1709081c0030866000324000d00c401c141264a6580d0f40107120004005000500702003400021500c41d05825081960008446034803903950f013000e01301540701c1842013400648255920140a5400c1c02a100100011500142000003070303020302006100040806036454044c5281021060180588201a0840b1441c15214000f00c00c1030081e402d0b10b6a012001592007001008801105c140948041e10040e00d004505030f107241c103251000c2c00e020710303074210107a00e0306145908100c203a09540b01e032840c0014241425568407144607460b8003070b80c4101c5000c42c9424100d440d140d4812654062941d8000803c1c8810415a45841000c1b2208990440b6940d0b00004181308034800c5002c071304c00c8081d10035802c1c0400c40c1442901d00ca0640805502540520040c95a0f98014017401201d81c14807009005180c81e2004140140040c00c24815844002c042c0100071030440344103006218403d00510f402003181c00b0700e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 260654010 1250 260652760 260652779
    0x10f061d040b190b0903070b070201090b16020402041401020f0a03091518080102090312190507020402090d050606120a0807030f170103030e090708060a050907050706090503070c050d0c 81
    0x41c02840c550000200d480c005043c01c00800403406804c0302000c40380ca401c1c494040c103140c1240380d001000c00d007006110110050381e1040e070110588040f003950a0315001030540c5030b211040003840007507009001042c08a5200d603a15102d0180c42426821100580355501405840f015070f41805230001c2c885000034815111100c501601c181c40e545003e08009101c09580042e41c00036802c0807400380d400103180d040501d0200040215000134604880c45c01e4051241000c1071a00035110005122020031a501595201c0e4107880c030484014000411140441c54850b03101c007001c6810a11903035038200c20008410000500c0f0842c268880080c61400c000d80d1400d545007414800420100024426001d0b40541b20745a090300031486922000c903a00405c000f002030140d0300401b44801c100c80801045480d50f14400e044003250815030342c40c411502e6030130049402d4030039101c0c080e0805c2c2c20150420100035000005040981c02401c07858112511501001034001c082c0002030000c803903c40c014001d6104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 260655260 1250 260654010 260654021
    0x14010c030605040e070621050108011401050307060906031a12010b13060e040f060e0f070603050f1303031d07030b0405010b03120a18180912050a0203040308030c0d14010f061d04 78
    0x16003407c80111881010020703801d80d00300742c1000400c1d9448484e002200d40324884690f001d054100c0c05083c090f800c180300180b074062144951410140c03154a0380c00182e0005003840c100303800141181c1d240c0074068408074080e15407810411700500020100d15200b48452050100791a0296014100c03070320759445020b400c02a160066826a58900c90345194400800002c191114001c000e030500c18a0040050101c13200180740401c1c040c03040f41042400c6a418080501e0554182000a90b001e560007200c8141d004100110005200d022004428030440c201c0346031040748036400910400190106140d220418000034240d0a402030203200111401105206400c0c604d8040720385a4070b9440b402404011101c08018900d9980d41c00288140180e12043c060f2040160030120316121030138900965038072451002501c03101002c00401e2504040500300c40036000314200500c00b20300c0c2e06040e0740407900c082c800c6080c001c0200c000010002d02031060302d80100d821100140b07004c040082800040c11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 260656510 1250 260655260 260655287
    0xa090209040b0a0e091c091707030b0a020c190b071110020a050304060c0e010816050c030a020d0f02010b06030610020a06140a0b090c0a051614010c030605040e0706 72
    0x180c84600c0340c049900d41440900080001400c588990304146400743d04060b4000586d500301071080c0030f801d0150b5009040c405c101d17038080c11040718482d0011002410403840b80c0000300038140742828000041e92a030040c0c10541c3e00f81041e07510329103114101d8000f00c5003c55008103c043d0700d00000d0b48980c05070340342011202020707040e01e24a241c20040442281e11840d00b04000c180040240704c14451a031180c20034100c4d85d81401d281040348140040c0c921071000341200c52104c2c0c060000070300e441c4507005507988642107a04881d00d03242d083d1000f13503e48240d030031a0800501c0c403100910400748140241001e420010f0708181c41d60f212002032010101a00e0107500a41c45110800000500c207403203050320340c4507020942c250b00d0034044000c5050300e604c505030324170034024141030001e169801c008803441c01c2d4032414080d41d0f4644544a0a036007900c40a0042c20021584105110000c819004018034062682e800c1101b66160020001141e46043e403103403031503210043c00e000341d42c0500c0c076a90700d50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 260657760 1250 260656510 260656519
    0x10504080616030e16030b0612010911090c2b110d06080c06180d020109030f0602030106030c080103050c04090c050d0c050f0411120c1209010212070e0a090209 70
    0x2a19032101901d070501c1540c041603041210740180501c01c2c0d062241c1c2c411030101e40c001c1c0280c5030072504481c0e0030103903601000e0500b101210102e0219503e40181c0c0c01000c0c0d204009003c151524104080c0c0c0314801604680164280c030005014a4821811508820b10390940c0d08403883c4605405d4500146041c012054a40d0341c2d541404140c146c3c1001d492451150708010960504041030360341400c1036030110342d004010034000480c1c440c2e08505404400c000070b54501c0303c5240607000490b003403a070a6102504003076500c0c0d102e2080c0551500250f060790341548052040c051081411201d141e400d100c00740c125004040960b94502c0d0075081815064040e030180d4000c107440303000080d2240340c980400c4032541f0120408103c2d504004845100b01201200c2c1000450600c03c16070b62184242040c81c904481e9910014182c40702d4001596103600c3e01f00100720303142c90242c00c0326000b584425000c20a080c810800035180e0341c440e00f0081b642d807801a04201190785400c03000d40194000d0702c3d006901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 260659010 1250 260657760 260657767
    0x901020409020d0f15050a0303230c160602190209070e06160501150b04050607050f12090103050f010b0a18030f050a0c141809030705100b0a0608010315020304020105 73
    0x1c000d01c5001802c440305241c200021251800c11540c0120b807107250300c48006038200d5130f0070056651065030301001c0382d4160802c07040221401d036400318111000302e80c0100521010a80e1050035000141c10000d10050000c800602a00ea820990791940a01a4800c00c018040030102c014281400d02980085241c00d0158802d08800001030310354000742c05048140d4008a80d075010f00200b40111001046e408240c40355140c00c013078003000180b01d103000c0c03140542c2000420208001e004c04c01c01444210040550b0701d9460480c5000d141a8802021503000a06110209a51010303081525041350b094502103480c0600c02d51041d25061310711000340040245e48240000030400030621068420310440c050102c074030892811b10040c4205401c06070464107107084006054032100c5029208191155904c4015034441c00b243c3c0c650712640d44010700324010020300040c503600c5608840d0114100b156030590540d1a0041210043c10903c409030040340c2c941d0704421140c00d00d5005581081c010f140a526 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 260660260 1250 260659010 260659019
    0x3091406070611070b011e06080f06100507150b040507031404120e03060108071a0f0720130b0109090903021c0c0b07020c04110708031b04090905031b0a0f080309010204 74
    0x105d4030001d85c0090080c2c1d61190304030002c2680b00300e4031b601504480c1072100c810b0074024030010960750000c0c00c0502607007075210034000307041c080d00a40306441da1040440c4210ba1301c00d060200541b032844402c50090341401c0100d0f00880c02030044803100480040745410b15a00d94031002d031020020600e003003d20203d0540404540c505101e141c4c06810554020491240740000280c02c84003005100c03032654109001e02072100c0802c0d000c9548480d08000050104034916042c8816613003c2c46a00c0e501c05a4060000915071080d04203480501c42622584c03440c40e5100c0c0b0300c01c241c1b036080720001d0050b0080016541190b10281040c060b156042c54241c036805144e40e203034184c0d007030207654010141e40010300c0c114662419004024201c60325450303442c1808601d03034800c0d01c280005821110320040740511b1600c94428402500e004001c19042403041444e2030500545950044030280c6040c43c0c003103002d42400800092000d24aa400008065060080d445195541d04043c0921280e0b540810000a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 260661510 1250 260660260 260660273
    0x1207031209170d1409010504021c0302011103041103070803090f04050a0b06070c0e100303080f09010b040f02040302040f060b04170309040f051504050708010b13050402040f030309140607061107 85
    0xb0200f6000c2c02c0010700031894502480d520789004106442c9a07050008010050701d450344454030170982d07102c2c25000418645003c0c0e024000624040c3c40e41c51011003017106201501e0341d100c4010209406443ca2591201c540d2600c07440b56564038ce41007100071110380428200350784482c0d80140f08400003d0042e454800050403648071b00825100110ba807242442058440b0301c909402c44075009004d0301952441c0c3d4090a1000c0080c80b242c2043c14510010700140310a4102c1d09281000800400ca40d950300c02c034180c02504980000d07402680b80000c011080c1195201c0c84040d075949451040c2401e142c4144031000c0c100b2101d6801060200380141181c603141c49c001d0b40c0480c00b0840000c5000d1400c8200c0101124a068601d842181044140180745070401d01440c10340300203200c042d5841c400400008110b00302c030345c41643c10030b1001038000342110b08540440107603480b0384d95005580e0703920b089a00400d40310310310840c0d00c20420881d042c00680240c0c06042e5030040b040038a402d000c0c40f40c0310316 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 260662760 1250 260661510 260661517
    0xc051002130e0f010e0c0a110601091505040e070306020c12130303030c030203040b04020918030c16051813060b100210050907060816020114010f050102120703120917 73
    0xa0403000034150140240301c002501c55611910100710206158034120080fa8170340d40c0640240b0045100283e4a2121072007602d042030503250300703c111030b142d503520500940102010300d0414020045510003140c1807a1a002d91031203a2030000017000d00301e0551710380c14001d40c4008014019441617078107202038505860007404080c4a81b00c0400b070701524504000c0e007610541c0460800301441081040000366049010f030b6003154054410001a03521105040c91901c80d002000540788030108808011010001c0d9010000f010030415911345603590003805442004180315200d0070320040700141e043c615a03030314403042601820010914a00c4d402c046907401103c900d1070700068006c103007120760002503401210b800c1024030740203022040c03911400030b01901000c3c2c01014002d0902040c402403901c00d401641c01c3c0025420b202c000303540d5400858007080114810107015000d42c224208115800c04241e4244680580319114403140d826455001407180850498064a01003000706202242c503018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 260664010 1250 260662760 260662777
    0x7030b01091a1612122a02072112020c060d0e03040b0a0c060b091611030d1d0f01020304120f1709010b090f0106020705090c0405031507030c03060501050a0c051002 72
    0x134070b550b40022640104800d03800e4064406641c10642c10054901d445c000c40f0007805070801c110900c01340c00032800c0b410210b03140d00c40840b040e0340b8400100c142a0354908503003114403c102000da052050a4180e84a002c15242958031410a10110f00e880f40c07150061011f41240310180c0c0d1a10340c65080c5210b1036040000084005510622100200a401c1c45500c4400901300c907100c940f03191210000801000d48139002c010081002c140b07108440d801c100f6580303010715402050240298811880104500d030301c14030345042c451805103070710802041c400c490095401060b070086030b00d00810181c480340519101074081003d0342c1c00a5801d80c000115150046c1c00e00000030680059642c104001c011020b0700c103d024030400001000341e07a80015044e801c4810035a82861140d071003102403500c03400743d030f40007613014041d0000800811303010305d1500784540d1300c40e1800c1104c15580b00c000c40c2107804c140076850110307174200440100b160180310300510891080c8111101c80c0f05d1001c14a0aa8000340d0780d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 260665260 1250 260664010 260664023
    0x1317030403031407020c0a0b07060237030207030e090612070305010506011103040806010e0c070b0109141e01031403250507060221180d110907030b01091a16 69
    0x60b02e2110000c000015070413450030b100800340b51103045d00203401030b00c5a2065000014001070440100603498044d20418220314410b145034542049481040305040800d100310248915142c043c158044e1090f00e036030380c4d015521000ca031040c3e03000b03000c0c604d1000b88c0951752100342c291110740480010850180618810000400c5500b01807002600f4524012051007084c3c00c180002c0c003010400060b03550456007498818a02cad501d400c01002e00d54490030a0240c0008861b50000c900c210041d00006400011005454070a0b581d5070840030028010f11041e500c107100210041000c0340341554447d5181c5060000c0c4c07464006400111000788441c04d032452510010b80e1700c20000e001041c031195004000a001070803a0001c04500d0b401040704004480c8070342c603004100f440742035006000b181280c4030007801c41680c22910b41040c10206405907419032050b2003000c0051728051107409566155403068603800e2180b8102400003c0102c42c422010690344001c1c0002c10480c4240c0400d08000c0d402003a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 260666510 1250 260665260 260665271
    0x10215150d1202070302100e0105030c250308060306010e011202090a0221011409010f17100c02031b0d09051201020c0d080103030201050a0506130b0a050402180a1a03131703040303 79
    0x4144910704501c59041814082106010008c598120f0f01b2241c0c440d80b001c516507641d10040c9105c8448140940e400c05070842a00310507000c154001d80407c0c013800044080340e401343c1e03944c41c0003107103c0d00c00d0150992983e00e94400c00f005082c046041c40e00800300c0100541086514030100f00c40c1d1550980c100c03900144c4000400000000c02810003400d501521017036019810400c40b00e030307243e82038454080d4255961404014503803040c4440c85401ba1514810301003a001040001e60307a41004009840d541140c007841501e01d8000542864012401d0b26840403042c588801c2050b043e801d56803c04955408204800c6025011710600f608000192141501e55056081c000c2c02c5031001441d2a04891402052240c02d175240c00b44101508680840411010001c0002c5602032145500076900140040703070080d000c44421002d400f0b00c10007500c0b5044000e64481d91512080340c0c280c05000c4c42c22081020030702d00703039196095001ea18042c40c0c0d180180a00031420f20703020b42c030455042d03000a80c0d88 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 260667760 1250 260666510 260666513
    0x30124021e100f090519050705130615110c010e040f060605030130020f0d0501060f150914010503061507051509010b030d120f0908070b06010215150d12020703 70
    0x1d00c03511040083c881c20400c07064441d5501da5a0342c042980040340c2011b008501e417030811004105400c068980601750056420300c82158101405860203a094032224003005411101d228000900700020824001c101c44100740d401980c4052540900d0740d003013911640320140c0b0b80c2050150344010034965070382503520b602d842c07031000004801c0010a0903940c00702407903134039407590f9005400c0c0c419011113062000a1701c560002e5415600312100078101c3d404d03e600018101105111034080b1403c0048071411400740d100100e403003450038000c003a82458014100103080d4821005143d001c54090001021600f01c3c0fa03014240c0d41100d503040310140c0c4902d80e1071035400183c1c4440d40c2c000d40c83c200240070300030f62500040d4441307582e01a000e0400441c0344004404080c2904544c50034004500100300c110403506080c0019440b81c201034900e0302c610340115075203510004103298480c0c106179281a00da2105141c0c00014100c06079030b50b900922101002c80803804420176101c601e10030350000c2a003280746 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 260669010 1250 260667760 260667793
    0x1e0503121210080703060f1404060b130c170703061805040201030b09070c020d03022802090f01050102071a0906030c220b0a08040215040608040b0606030124021e 71
    0x10324040209042d10410000e1460000d40351054992000000c110101c6140e007140051100d06400354030b044800303003440244002580000e100314010394021252502404420040c4d0344e00036403160019803820b0074a1440c1c0d940300701640d000002c41c03802050a5075600c4840c940142d80c4042c2c414203a81e188180000c541c3c040c030840820030801d0704c507401c035854500c2c0080c0c10210755510190103105032402c1101058428082c0a0b41c4800a020a0054900108020740b119041070740c124043c006401c0400e0ba84440d202405040b598140c0c000d1407900c2c1481c61603146240f1030714001a26034000e0086500d103030b441e00041e500c680b0240d40c1c92502c030045a0b100d200034500001242000c402c884809010844c050f01c201da020340c000b401c1c0080644c80b10b01c0410340f040c410003005000000003060100b409030388202c409000314000d0095420946561003000081e01c400c0c07003041c2e000c00440e840070202180a0006104070b41042c0107881c09040c00d0130301665982e80c02c40b40c3d0020750304030744003010700c0202 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 260670260 1250 260669010 260669047
    0x204020f03101d06060d1515020f070e1b040f0b0319050103030e04020714030d1b03060e01170c091602100203040206070f050723011d0a1e050312 64
    0x101a00380503240500c3c003422040700d20002e84941d020b81000030f038100fa10f1080340c0203140c80c2c1e01880c152110444e9968152401c01210a0300034005018880c10b0039200079000a41c0b0099507040440114152100120101d04401c0c0c000c0007d0440001d010000380c0b0006040c20070000d214440700703030341d41c1e149c40b030703040c4251000c0c0d03c20b69280b081c42d000041c80480e50002c4200c80c41c0302c060704c0041e540c60540c10691480e062003415900c0d544000114500e034162180c01034022042607001035110300908403025415210f15011f1081030810b91702c01000b61244030b030034840c4070008039425111170020311804a070003100102e900074441ca110740d482d4414180d040000030224002403600b12f04604299002030301c0c070310480c1030107410320314003400d0101481804c2c44020000c000c0040b010360546d803142c02d0a003114034414407050110703140c0c940c04222010b422032a01d8251000070300d54018241813420008014031541c0302902403145440c808622514100300018a06042204260315807840740240c001088 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 260671510 1250 260670260 260670269
    0x11010f1e03052d0f2205210304030e061809040c0f0902090604030212030c0303130b060a03030f080702210c01180816061401091508010e070e040507030204020f0310 72
    0xf0a42d10000e0042030942e20301d90860b0407800100d04a495060328843c40a81049040e41c645680784110000c00400244107541d05100034552120140c248001009900045501402258603400e1f039020f20f107800030040c4030151001c0b401c040960808804101000000c07070341218800310540d01808045114104600140080401945003e0039a0042003440c0175500c0004d0041c6010402031410150500a0b82c3c810481c00080b681c4900e080081d4402d000321500b03003510050301d076201094440c1864640042541e0300354807420b0022903001411603c1100040c02a011805841c00400c07582c07200f01c01c0411900140521213031240b81d2480040d084404d50800c44500603284c0070700b440050701d0801070714820390207a5000b80c2841e0403030608030064603c21040b24010700b0018000302d038001c01544a404401c52842c0c1d1010b10341d03124402d4034204c0390005085001c40e80403a00410060000350710301d80e03120380700b80240c82d08550740744d01040981e00080081b10181e00007204020700b9800704480b0f14000c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 260672760 1250 260671510 260671561
    0x90609010b03070608060301090b07020d030e0303070507030804112808010504032102040503030d020703030507210c11010906060509070203030402011e0e0307090f1811010f1e0305 79
    0x110000000c1e5a64200307105490034842c9a45c002042da5800794000303030800b5003040342c4100c50324040c2e600075203e420000c001400300f4540785800b000f550f000000c0d81d1207840b2a448061901400740c8064611200081c4100c410414207800710034651504049949100e45200d003540c480c00c044d8040f80d510701ca40da0015901c9a00d09000c000c0425488030751150040d513001900300c1e101c81a031034280060f1041d90007054047c480001c4811070364119134020900ba5000b540d00700b0003500e420030104d54040708240c0030580500d400040c280d019503a41d020113110300725410041c256040d03200b0b849007594179840c415250503540d40010000d90034081c8031240d2186540c40514590f00c1c155001815a413000c9186080020f42c084480c6000c5e40a003241601c9040010221007020b5a01ca280f00003a02000c01c20743c402a06208007003d0441051154440340d6a003e501c418100000e07000440d40ba00420300f1103403c100038003d24a2285d600400404410310302c5a9004c41c940ca000e0400001e01c0c4030090000811 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 260674010 1250 260672760 260672771
    0xd08100b0c030403020603060a090e03031017120a09050d0807020f0d08250b090a140a1e0201140c16060e0607230f0609010e010603020a03030e010309170309060901 72
    0xc1c041d0200486007034940c112401c50300e030f444800219a01c840342c0d17000300314001c4c0b030100c2c0d122200707030008091407147d00100800e2030720580720091a0b5003400d6020f01d02800358051400b2583d1411201d001d440010010b260582c0c1d42c0e50f64200203024500200070548a13140c1c0007400106500b05408113194082064030382002030b0380390750b40c0c07110503118610a48030f00d080741203548041040c6111101d2081e80d00007035a02400d0502586040c0c031340800c44812201290710784800032600d0030100d00714a140b604005c0c01d0141e258404500600505c0c40d880403810010500c80700800c0703034001000740010b210240c0003081d001a0181304514070000a401040c18410100501809591190300b141c4003142e120035a080c000d0449051480381c0c0030741500c0c0d8401030191421050301d008001880c00d205000c1d030700003808094a07480903d400c079400742c00003030f41000d441d440c14000310f0301642c0659000c2c04103140008000d4921303113420108000c0b013006010111800814030004510820038590003002d81d02c000c01a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 260675260 1250 260674010 260674027
    0x2706060807050702030a15051006020601060c0803220309080f0c1509041b0309051b06041e09060308030103330b010e030d11070b040308030c1b0d08100b 67
    0x1a0364000c080703400304140043c5003011514148500c4214a0384240005038148a450310070740541000c0720140e280c4586000d000132054400540d5a040b80d041392240f100361501500c850035194070043c408402c0d51301e02004480381c00f09840e006041c8500070380c0c5640c80c107410041d4090a0000300e5814090a521071440d00c00c5681c0c03034054054406031580300342c5e036440c07035980d02181c050001016080d0200c0c0a0b8a181885c403905a001511082c0c4120150381d400c0441410340510580c11a00b840d03042007040c00240420101d6421040102c510383c3c66501d0501d685040d4042a41c090340c108a80951011004100300a100800614451640b9960142c2031245821002a801021000e04541501c4010100d201d034001c0800341c048000c054140e6042504002300034040c40b00d0629440c900d8811000002a20600c04050b9410307a80d00c505e4084c074545903452108005d400a10041d00c00900030212882610f5003040068254082500d40403414a07180d585211007a070141d01810700c4d603400308000d26 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 260676510 1250 260675260 260675267
    0x2603030f01050103090201230c1612060518030c0307030905090601170705070b101d07020712031e1809021804090813080309030622020f03010f06270606 67
    0x20705641007803034005081c8241c0d00048882c080003c1850b14004200300818000d580d40000078400741180c8011541207010340310031b0110500561258507040704440d0440701c001901500650b8000415403c1c009252004016540c1154010038030035180341d000181810070180c118140d20001c00003240c85141c10f15190340040d160002c0399900026000c0b03118000340141d40148155555182c106200a82d1880c088216418000803030191141820007400d000a8400ca01052140301d5805507025218081c58501a0240140040d40c114103219491001c0e1401403070b1801614921200ca80c0d9552081145100258a4010982010301114010841d2543c8080c4a5060016000054a0000d605a400e080882c698024440e000c1c04070441136078000b80000d000030103806150720403004d0380c2c0e40780c5954140c402050071921601068902c807030409405480c0c4041602120303a4060004600c07103442407034120480b001c2c1c0d0480c42c040c0c5840300d182c0c80c40480f400410a42900c6100c1d08000301401c00401070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 260677760 1250 260676510 260676541
    0xa020112020f0403080424090b18060a0201051b13032301091401060b09090705070f0c06020d120501030503220f090f050907050f0d0615260303 63
    0x641840015900d00d840c1105075030488410301da440060945964880c0351500b01944507214600308060310707254446100c02c10f24016050701625850f0021941c2c9000b12030031850308181c0c984162240849581c5809407500b5008100040e550760000400b490103844802c9002c0e400d2081c104192401c3c05000d20a1401d00442000d40303400c4194000c8140800d000390085c00d480f031212412550030070300100c040040c9030400301c402440c0000240001d513107418a40a80707000c0d29446543c80b81200004c0b40300e5134012002021282d0255a40d48813011042d03c4100b00c244e0990300c03070001079111b01040c840840e8800100107102007100d805100700e5145071140c03035a9014a9080707a4a441c144005504d56070141c150b40300003440c002e04110300d90b03941d412240008280d902c11150704141044000b03010322801103040d0042d110000c140e105108183d600b40440b4481200c4121082c0303a0761070075034800d11503049403c07004100384c694840701407540c95148044030541c20280b450607402801801410303081d04214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 260679010 1250 260677760 260677763
    0x5131104020c010b13050f1b07020111160b1e07211e02011a120d03150b13091104140907120c09140d05071404151d06040b030a 56
    0x142c0c07100c2402d0452401490150034240e440150815415100411a0040342c401c050041820415585040e08001442084481100041c008001200c0107601401c104062400150221086403510b01030787d651a01d4180c000810741d8a000c80c5043c20b43c500c00e241c000d04090360100450400e8040c0e501d031900c2c40e002200800c1030603081c030352811107503114281d0100400e08903950740724401548140a8001d142500b00c181080c60500c100c0e02c00c6040c0045d0380f05031144481c000386141b09900400f01c005124480d0681c01041e1401c10000d929403003200503101e0403591220381060300c1c0c07400c2600400c4903c00c0c9801481441d06000c00c010045c0b01080343c046c00c41040d05c2c450155554804200c070803420f039480761f815007031500800050280c0d10481e00310542d8007507402204034802a500f004951048110b000f082c5500c0b6540030300c0328807160100c07a41070450182010812141e507103204e03a40101c907500300c4201c0d24136414494500d94007810000d5040300c0b0a6904100e03a80395503002c6a12110743c60710 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 260680260 1250 260679010 260679019
    0x9050915060d1113020903060c07060c0f02060f071103340f0308150607060c08060909031803030c250905150405130615030c150219030201020d020403030c0204051311 73
    0xb018075082144d601251704410000b01544c0c414170f8648043d9215030000c04065a9a516181d61010407501903817403040500c215030018900c2d41c0c0e03505081e1035000ca0003050581000f144411001c40300104001501840b060a20021040014a0305400d1450a50311801a6010904008e01c003c980124040c6002e5030f01032520704a40d0751840c410b00c0041040c12040c0345c2048000ac0c0500510100b1b5000310703d80360b02c558403826192100c000308266480d05444260350742c4c20410000b00c280500404850350034102a081d02d0528250b48203031806c09400060071484140b002c00d0201483d140b160703e9502400851608000d94107110b81039000c2c1658020146015075668004109004190300ba900311469111105010120850184001e030703a42c1c61004a6980514032408078100314210083c1460780c3c4113900a2150140d2180800040b20901c00c050781595801c002d030719030b0000c0354001030015600907258002e1104140c4180070403550001c1c41920419860090300340043c0020340703000031040d411a03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 260681510 1250 260680260 260680279
    0x160b0f060a030b1e040b01031a090303011520070e0c07050307150b030105010303021c020303240a080322060f080c0f2a01050603060103031202070c09050915060d11 72
    0xc1314000100f10202c603030025860142000200b1490303425042c140d07845030740305e5544000c07038002d410802441926422950f41003030005112244600d9070610b1048010310b86500a15600003e0342c804000e4102d071081c0d141c12a2005102e0f0110401c2010b030451a158019486c1403095141ea64403805000402000600708100d072090b0180683c10036a00004001e00030001c5507907038503010b582c0700e541c03050180d104140f04025403015800403061720320540340003501c42d2141d00701d01c0b0302100c10b0581000042d4031482d01040407071050400c10160248400703003642d4445200c10f40110005880c0c444e4011810044091860b85001c2e43c41642c03184c108002400e925114400048601c03070364080c10615a600088000c4122400882e441a40d202004190000c00881c0c40d0a018152070310f0003400003401055440b929a016805d0f5940240380690040254201c0203445100e81800d82c0e0b8103880340e0040b5400a458500800c180307041d00d642000048407014103641d440d5444d0800e8040b04403040348a443c280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 260682760 1250 260681510 260681521
    0x3010f0b0a0504051201140709030b060402070311030301081f061d0601120c0207030b100308041401020a06140402010f021b040b030a06020403150b0604050d0620160b0f060a030b 78
    0x42e016a0090240107120994039404a4070042c000c040021541145503400780118103264000e113149401d882d00500001c81c0b17580c904082c040a5070115408800708400e072600c0140c280d400b400550301800d5104003800140459041c12804459880404a2007919141c4200b04080c8552200b1814001c0c0c44042c00d00c50f0340d1100141c54102e4074542d074018090a01162100345540070070510705603440355003418660303241c0280c0102c02202c00d0000a00c06801000706100052a8181c071840c080c005104561208842da502c0e1410344800d0032240e4a80d48180d820301c0110340e001100c81e100c0058074030041c03105110b041420042c2c0014200000c3c0120b80c0c402825040e0384003030002800c0786800250542d5180c0c0d03289014017030801020420a06546001101601c81c64250300300c1d0100c5070000c029a1a00d181e076103483e0002d0540140f44500849a004912030f284441000fa01c0035140c9103450b10404070460410110a840c001c00c00070105540e5001c2020607594220102e0980f038011940c800c00b50780e213 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 260684010 1250 260682760 260682767
    0x30c0d0f0203160902091e09010303050706020f0a0503010806090c090112060f0c0f090602010b06030f15040903020f0d0212031605040f0f0f14010c1502040e18010b0603010f0b0a 78
    0x41c03603144901c3d800544400700e860036460300102040b000954022400e0049404903030389080c0701e41403480c0e0010010380100003182c4914050619140240030052802e00140345e414a03d90180c507003030b00400c00c003000401c03c07074106010f15680040b443c4c0140110705c840c130000408404c014000c8181c0c199054458105202c0554040c10380018410000c03c517040c910000540503490a25160380002d2102402061891040c02011041c50001e040360f810f5072214041300416400051000b007034a42501451b0f103080c2c3c0c0f03a008810580c2c0c069000b6040d040d41c134040710fa0902440c03000d4682035610070b4000115201505003203039804071518141c401407840d00c0404554030b02c602e038882c0f0703041c0e0031420012a102c0c01c0401c80b0412501c02402c1c602d0310076940d0030011095a00c490b1030b40e0100340f20180100200301e86903000c04885040c000014505503c44080e4020b160702642c0d1001c0c061248200c41108640c24440d072403038a501120302505640c5040b0b0515052189800b030507803207400c08210071015900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 260685260 1250 260684010 260684023
    0xa05040f0e010203130c120302070902090d0503070b0109182d0209150102011506020c0d060e1b030c15180a0e090303100501050301060509011409060c0307060b030c0d0f0203 76
    0x1081002990313070b42001c00c40c103420526011307010b46d08840310301d07400103150450700c4800c1c46455254015000180c94a03c0860080d0071071018150044c4030248a0400550107000800d0301d13a01c184246d1160703504050f80f50703003207800e040a21103030b12041c804081d0218460060395082c1894041e100c080072040d801c07503880c42d05c880c1e890094000c82d01e1010301c120500ca0619100205100b81e000700304840c00e80340e80390707607c6c0d20310310132032015803c420141d48084c180600440e5005000c1c50010441c00c00070300d40c1c9440c01200100c0c40910070b0143c002c1c2916071900f405094404101143c0c004500c8a42c0006403050744581c12409581d05007440481040da1900004080201110340022a00e4503100103070503241d500c1143c082c001e079166003001052942c020401d80e4183d031050354840f81407083c4c1000540c0c410202645074070685030309000c030102542d20400100702d00c0c5a24006940c80e078200340380241c299200280958844d42008046a0103500d0700422000c29070b821981c00901c402050008c00d06203036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 260686510 1250 260685260 260685281
    0xa0e0c1e12030712120209010915110609010204060216060f120905030a08060315010303080c0f09041b09060314060405040201050d1401080c010503041203051f031506090b0a05040f 79
    0x104298007485540c04404d451081c407a00c039400d1182c0ca20605000700c3c8149012a03010562044041c400300280e100344c0c910462050810440350b40c000a0114079010007103c0f41512613400040900401e0707414041e1080701c50904e035080385120304001002c1d01b24092800e000040212101c802045496981c11004074290004e068030340e00c03a526040202942405c40344117009109101500c0c100010100d0328904032500741d9501c10320340c2c6511182d105182c0c49401a17041e442001c0c0b05d0340034030340d5452241020498041407500d605c1804084003400d005060350040b401d0500d046079090520203100079140d8040d00880e000201541e13540b0040e203045c02290114941c091528901000311400c06ca052070603a560b10046614440140e0011070702413208407401481ca1581d07800601d1014041d400c619040300f03102c40ca2800c1c101d031507101402c80150542c001d03690300706081380d4642c299081c0d110700400381c02020000d12108002c40301080c02d0701514480d5078007503a40d80c0045040c0f998103600100d50340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 260687760 1250 260686510 260686513
    0xf0303130821011d06030a03030203090f060c04030309080d051c020f0a030906060902161401060b0a1701241206050604081005160912020a050901030302060a0e0c1e12 73
    0xc01d04980b00440301109010744545407820150030610b01340c280e0401481510000c00504107110641e408402940014000d80291310507a0455100700c1414404207120b6010031103083d86131459400d000700b50706442d80c880102c83d0041740140708140d900c502210840040e405c1d0011846610703d21800080c03280f911300e03daa00001256100c0500e170300d40c12007003009001d2881400301c40d4442d05120200e01c80c085038041000d038030700644000500040c0c07000e8007013001c840c000101941c0c0c85c00c2c04852540201421400100044c20110b992060751804502410502002000c02c401042c0140b1540201220704400d00420921606442c156900030360702130400501001e03203659a40150b02e540390f00c040042d101c0d003424540020660011a4603a40300580517030f5500203140d283c40444c00c6c1d500c5000ca0180d0300400c001c1c801140135116890414001e621a40c0181003034603000018004864040d0b840010a4002c03000c070001c181d6840c140321107400c00c02d040c641d09643c5000001110000e14101940c4076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 260689010 1250 260687760 260687797
    0x20a03060f0510091e051807080a0506010911160c0801060602030c010605040c08040206070602040e0403080108160b0307200109030302090a06080c300a06050a080f03031308 76
    0x6441c800d0304580c0c060741c540854641c0182d26850400141d584406002a07101100c082d1500c2013940c0c1d03080325821074480c43c0b1203002103103459002405d0800641040f0300c00d5005c1140d40c810090b08101c49030041c42624801c0119490503090440b036481010210442035400d2840d041c1030008025202c401030659400070044699108006503c0b9005140c03a01c0381946044000038090400c0d0059241c16046980c0c0d8000d19550750b42000f0003600031070805d44e884c40c0c1c00e00012544030313850003071180141d0080d1220081d5603d0a5280e91400100644600030b440d02403d081000c410600d05072600041a81000b007a0b2100400c002d02c02a1800c0d00c01c0307801503082603051800c2c10340660007401e010009484080303810752160000c1da007900094030400e110050400564040c281e10b0200b100004801400200451001e50a01442480300755803240f0510f03a180d40402c014034200180e80000c241c600d028200100c2c080701610307101c4c000100611080c0d00d020b40d10900300910101210020641440d03038054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 260690260 1250 260689010 260689031
    0x903020f0d0e010f03140115020325060b012606190b0a021603170304060207080d0605120c0a09270302060604061d0406090c120b090d08130f020a0306 66
    0x10314490310002ca4041040d42c5101c02800e8400c2c09810a810030220040e0140e9284c41f00032001c4105c40c001301401c500040c4240d00140320404000d00340d0203d0041e000e042ea401a00b03141d0201c4551040140c14050f9182e110842c40da260036030001d600944060155442ea0340001081000411032010340c446200001d012800080c118090302031140c05508540c00da0310402903034081c4600c0c0e804043c05040d05440036001554402006590061186001600702000380d03481e80040c0d000368904244440d00c4100c02e0000e420003105031000c031400d010080006c105001c0c00700d090341565024401364247c88109035040b0041c000042600080306200000c51f8184509009464400554146218600342072000944020191140d22500c02243e0710750420303101d07070b84c502000301027a510854002c254a0030021307206000c108000140707801400c07500e4031868a00720007030a020401d051407041c07058010a01c41c1e86620084900c81007544540000900c0c0c5071400050251162648001c00d0941050050705 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 260691510 1250 260690260 260690267
    0xc08011103190c0203030f0702010204050406060c0212011116020303040317120f010303050a0509040605040e0136170c03070f051603170901030213080a02180105090a0903020f0d 78
    0x14481c149942c24078554030010064481951041100b001c016401403000c04c3c603422001c11a41d40111075800010b00e0a0b503107901141c1030300d00c1c942c00040407840c5402d002003541424800000c401720310350300030071601110200040c6640940d0341181001407030344d08131030110b4408208450140d40c10080084400744c4c031440029060740404c01040304005140041115090162203440c141e940c5912a84d04148240104a655401c5030030700e41e902588403000040d05444a2060403140205c881c00411500141d00703082c2c075200004220200040e12040303800c0c003a003800000054070300d40c1c0040c07421a11075440b146801d103070013584032000c05800009031010820228041001c50184980240c4101e0000c44004a90140040c0301c040c103100302c0700e00d04011074803000b401844205814180107040c103104a050004c005559001030f4001c2e40858282410b42c038007241d9031030510000620710030103503041002056001e0405050140981d4880a410041500a00c0451545030340300302190301150703805d84010f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 260692760 1250 260691510 260691517
    0x30e0a0905010314030901080601111e030d11040b07030e0d080c150708070801060e06070b01170606060a050a2307050c090702030c0c19150203090a0b041805040c080111 74
    0x100c4510000000012602138040240c80030b1600c1615075120aa0b200401902c0401d00601340c2d008600a211140489100510149010384000401951181512102c450458100300d17002003c0754014401040b01000c10300446401070350529204002d01030400200311440c3c2034140050907980007103410384180c0d00004200d010808525440915500d0304801035555200a880241c0046e400b40018800310340580a03200c60100e000e04024076199164441c0550070100b070b04101700a80c2d0780601135010850070041c0c1500004200e88092a20b071200314080e1591280500c241d0901c41001d607104101030f80824004002000c04551030307510040c03494601c5c0c650061580b02403185035880c0200700c10340c0c4000151440c00c142100102080d401101c100001401240900c019215102c180421948410788610108402540080da04d4011b54420020b81207a9034004140c8160188070402445240c03640040e20640c214000090070b846030304203c45141c41d1a00310380d45560030404a20888050407009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 260694010 1250 260692760 260692763
    0x30c0a2c0103050a0204050108040f142a010503070207230a06050a020601060809070603050402031204120317041101110c10020d030605040212010608180d050415031401060309030e0a09050103 84
    0x8220796500c400041041b4051030088500040c040400280000d20701d40000ca40305003d1b60701c2d180c90b1900c0c031409034039020902820046507040d03d0318030481807011003001a0345044c00d0070070301c0c154900004000d6446045216142010700451004410041940004840d01070060700c0050040d403a540c001d403903503002400b048014851040000f030514400c0c0b260300c0c080d8140c0405892883c0c50f040c03080300900005407040c1e9150040e01483c031000030b0480700900042c02e150914102c0707034020342030141014011001442c20b036000e1004020010302c40c1e240030405071009017040784010607400b00c228540005116450707080340204003914151600000c8003144031015a07401d00c042c684642c00c0c0000d074001c8031414144101c400340140050b601804030307282d0003082907600e151040748075041d0501e81000b207032031800841e0001074140800048100c0460710080e2a0400b48582c00c4000c103d902a840c0511507841010741e00c00c030550415200b202800520300c802040c40d0400394a034030300301c00140000e110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 260695260 1250 260694010 260694017
    0x31804060e3d06031b2c010e06160c06080405030405150c0604030815010903020306040f03050c010501150e1905060901050d110406030b15071b0306091a0105040908030c0a2c01 77
    0x200017101849611200c00da03c101d0300c441c035420b40d40d00c0721010070612815000d074103000d5020001d032000d484680161a417071028160150a80107513080c070505980454114208100c000800c10004c607000104840032240c00b9143c140500070404203440c100e020b4251400d0b42d602400c0709102c20b051f88100b0700c6015410907002107100c4a81c4c5001550311021a1000035010b420103800540814a40c248500c00c503402814218a01600e01080741e00310b4109800005d415880c001594000c203501022070750b1480b009943c680f08182c080301c20848004030307520646224840004099503180d102e4000c0d1108040c0c40c050500c007103848241c0520040c3c0150150b00c00280c60170b100c0780c11600d4101c0c0900006d48c6278060907803420400361184c1139140c4449800c0090b00f44a10340000c0040c1e541e200300341d40079020306d4240b41040c0041100040181c1c060780301781e20440c2019251404600e000003141e811170075800361142c0d10b40e02c030b8500b42d6425558580c03d02140c0c02c003050f40150b26030078900310060b0700400d0f42c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 260696510 1250 260695260 260695301
    0xb09010302091c051204030b0c180d060e2107060506040b040623032b0c0f03020309010914130510050d05030c01230106050c0708031804060e3d0603 65
    0xb411005c17401903210190001000d840803078120213446009042d24012a021001c5010a4601140c40b03403005010807551240e640e9454a03d803902401410101c100942e40903112100400c0034004d9801905801350403607a40e0804980255201d601147c208a40503209009440d1303240400e40e54180d082607070040790f065039480014603160104802c035546d02890b400184035180d50b2420003520650b0300c1c40000b07200b003044401004c144424003100c0103d1080e402541d40780543c0000600034005907100444030036090464286a90710801c40310800b000340a00001c450f641d003518800c599800340c1c416034002c1c00c125109000c0c4038001c002003240d005610000d10a51150722240d070030500141807080003a1005200511007144940e00805030944e4501c204e6000e103881d024240d08581c01101e00f0b6941071410400c00c40e0382d04140c098000100540d1030000c500e85003040c00030102040301d070189007040c01c4180e00300c96030f48070581aa00581001c0000011306c90b8176004003800510711b80e08140308608850 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 260697760 1250 260696510 260696533
    0x1906080c03160c0c090f021b0c06030106140f1b0609030304030e100522060e030307150b120303010e04020103060e07020706031d010515040b06040b03010b09010302091c05 75
    0x820480703000d14a0406404298010741c401100c0c42c60f41481c0c21500e0000100000400c404280594081000e510b03400598400184001d1800581d20b40100142c54100f003041000b142c0d1010140c3c4c0c1103500c0c030b0404014801541015000c5403041040242500401217041e10751100c1e02d24034201c03646e103203008440b45900c4070030340543e0307a0000310f60040000314002030b500c5107400d1100d1a40034003030040c10400e0510180781010815900d1405004862071b840007000c01110758010382a0440b020244c001c0c40c038052168603030751621003074800e0f00035289803100b54001c440c1e05c070a20300c0589007039010107403a165611180c000010650aa4050b40020709009010507052100025540141d0642d0001c007003142c6442d1054003d8185036026080c600c903c4841d0012031807007806407601c160843c049080720a81d03400200411541c03c206403e005440510060001007261412079040d078451003442c94556461000423806845040000f9410009111021842d0710b2414040512184140709492024444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 260699010 1250 260697760 260697781
    0x50312031501050d090203011407021e060f040c0b0c064503090a080604060c080601021209030723040c08070509130e030307080106090504060f14040b190608 69
    0x5640320a8841c62410200d151580144024032010301c01c040049402c1d94a900081d003100c00720008240480d03001020000b0a80d8140242d22161881112300d4030449130400c0015581e20300205150392a80381440850240052071200c2c01c010000c01201c540d039014084c802c41c3c1c50350002d4a05c0c056260034009407101c1100c951502d149089054000c2c0e840c0615a14003003a580c005203405400c4030b0004000d03079111502c0390141c11002d07240d44e400522079400c091a01e05c3c200d51a6040031301c06c0150290500220780e80c04104000c0b0090441201501c03140f05d18000707400c1602c5980406580c0204141c1c003202c003455801543e03840343f0704880c10081000c06000a071482e2104540850000b0401c0080721003600e040104102c9104804a0004514001e804d1407899548203440b600003244000e00104201c9610112160180c641520240107581c5008801e03c0454441c1c001c86100651203050380303420b41c85603808080320b040014203003038032466500d20680f082c460500480c000101150000340240343c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 260700260 1250 260699010 260699017
    0x13060e0609060904020706061802040512030a2016270509250b03090a0506100b0706020a050c0d030c1d06090d15050403020c04140403200304080a0c050312 68
    0x1000c1c20251803e485502000001e40c401581259820365840000c1034620000c0c04c9400c1051000d500141d641c1d05000421240440c212000100780c4e000304680380280b031707000e507141d407580c02107494a00d14100c11407141800c00394104c1118120003d41c0e0300000701c2c40030310002865108001451409400000c030608003c1c0c4108840801207580826002e402c40c44c0307190481d1001d2070b00c20740c440140c0c640b40d0305698119802a218000c00c1e6001410f000c0c203200050000c2504130280004014000346002c03045020782c010080081c14071075000ca02040c1c918010b10459211014250a5600c4405032070700140051018540c1c02c40040c584180c50011a5041c01c0702c3c00c2122001807006040000740420000c2e05105e2200454083c4844008604091440d00a01d40110310a4000d0901e003800c1c0303c280011920304030058003540420303030240000b198100403140c0282c80b8401d40480c0b50044c01c138201e0300d1441561300ca01c6c1e1900c1448030300c0041c07003600240d04003942c0d0100c0994440c4006103ca02c00c02d0b01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 260701510 1250 260700260 260700277
    0x2282006070f0e030c120c0111070e150f0405040f050f160918020901060e03190b0a0b0a12060203040c05010207050a0b070510090f05012d0905100213060e06 69
    0x652842c0c01c903a00074003d6000a01d2610300030308468860610002040c0020648011407400b0b52064031848030940e00010071500e10a40c090041410f240340922140e03840034054070280c12140c09940d040c0c0709488484500c040104041c00c20301c0a4109880c0ca610030002061040d03801c0d000d4084c035103071182804603212240140b11564000d4442c18104203030010b1080d41d800150b500c00d02c2121200507101c1030080c500030b00302a184c0d039921000040615082080c180c14480e003000420741e0400006603642010f40d0480d0f081c1d070001031484640310100703200d41d031140c12a8080002103180d01080094540080d846188101c1500505980d00e07001642d80d00054000d19074410183c003001d20000c007000019000f100d00600c22120b40d04421404101110400d08040d02e4403030342c0806050500009024860750400060351900c1b801d040c1c1c148101286d10f250500d07488284c0c85204034400c9c00320410802d1905414518119510380c0306410040120038544107038030114040224840440ca8240192010b40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 260702760 1250 260701510 260701517
    0x40204080706081305010c050c0d050703210b0a090c110609031611040c0c0204180804050616080a050306031203090a0809010c050703060203010501141305040228200607 74
    0x142e0800c9800d441030b041c010951401c006500c010040850300034004d0741c64a0711a5103c0c1c60390f41ea65859541d0900d80c10050700d40a11100b04540e000003030b4005204454240c0d100d14030481d0056843c50380002d0801506401d900c01c550480205082e4034641c095500746505807a202d400c1441d038260320351200000c40c0c441c061500705100485540a45000c01d40c1c1080c4a0028600d00042c0707840080c0880310b0940041000845500681045081903c24090043c1c40b082d10700320f404a1507600d607540e900c15401064080c61010a03000b0541c0302d4450052003055010b6071070303a1241a0598010417540003100e10903c644940701c45289103001e00011640900c0021000c0d241441c000e40b2080c401c4d90020f0410f60402c0513055550020900600070034001e5803152501590301e506d89800144520811407080400800402c00c01c0c00704031714514050b048a40540780542c507000100c0762100300c0541060580501e45080c2c0300c641c86c0c0766100c41030349581130b452807240035030381003e041e004d80c2e40ba011180400030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 260704010 1250 260702760 260702773
    0x3032a02030709110c010501060e0a08031606020c0106030503040902070515010308030402010503040201170703050411030136170304060c1e201005160c1502030a06050901061d04020408 81
    0x1401810b4000d01034403c5a141348030b2400513285801400c43c2ca099110b8000503d1100b01881c1615000c4402d00c006c2480000540c100100403803003075004025004010701450b0700042c260440802034200100441d00070041d030b40c44a6a070030700000654040d5004640c01d005280038140400e43c520700c128140d030740229503a81940d0359a401510250300107007007a070521422464081c04102e410b0780203845a40c0c145c0c1c1c0400c441c100b52501c59085ca18048199110742d040c4001018140c03d03102c1c0144000700080b00600e03c105032040f9550b01d8850b82000a00b003001c009080034070617100500118090742c49040201720400031090210303201c03001c814800c0b0000642e040b0100c803040c4140483d0460036001c41155101d140082c0c00b0074039002c0d1800c0b859840c07580795030400414648038650070038106450300f40650800d86070b85e02c1d550001000c100d01885541d0201c00f1032001e20b0300e40d0020700138003130117800d02080d03585031074028089005041e11049403000024441e1503a08140c0280c07000c48242c40b0003800d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 260705260 1250 260704010 260704019
    0x41b0e0703090501020f0a030207030206070e031f1b0c0c080114010b0309011103160917070e09010204050a0e0a0b0d020f060d020d020a1701060311090f120703032a020307 75
    0xd800c82c0c50054035203640074015188907541e2880109201105610010799030b4425250281c10035030010500c1043c002040070860326620301045108034134a007c1c1405000200b184543d0000f0170070350301001d0400810382a81001e40ba0480c10050705103010348401c0c5a410781e6503910500340c6248201c080c0b00342c5814401040540e02c0140503540002e0b2500002c1500c50050040341410741045070303034400c0300312810140d030881c82c0c10640781300c0030b008482d1403100286000740c02c03195900c820744207d010288011000030074010707081d815500a441d00500d1411941d0381c43c0c0a00c80c0a0030181d40d41c10501d403400c003000145140c010301c40c8800e00e6004c0c0c00b01d00c0000340c440030071981d13070025210034401607003c1207210064503242c070041c514050305407070784803816124403002c88a50b04144c000c1e905140c5070421050703d121500042d500c5014046900005038a4000f022074141d50b41034a0300c54480c41f40707500200400d41c01140c000c4903100c10585200c44540e400e050001c614821b1712003c4d4040c1c120003000d00c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 260706510 1250 260705260 260705267
    0x40c1a0d0b0d020d03031a0402040506160512120123151303062a0804080409180f0605090c030a03080118021e0301090f0204080d082d041b0e07 63
    0xa035007400a105070031a1460f0780101d9180d400002d4100c0000e95504190a098a083e0008428801b819034045042c43e0411010402c24442c202c4042e4107200d1119241080140400811840d00c0e03086da42507445601c0c0624100c1180c10070300a00240c1070300e54001d5032003440b6840068070300c0713a002040000740e2080302d50181c0107036100d986891580d1030340400c04400300b05540030329002003c4664000c83c60f2100f6410343c0a110310b0b4441403030108551542400042401d281c240c5003a6544400c002a8007118011000144c501c0000c004112030305080003101801160f5011900c5005a003042da1407a440c0302003010f0701c070001c00000a01003010701c8014001c0301c4104610580c81014103400500d4540000741803903414001d03882d074400c004000401403201c1030113401440c204848486047d8141400c0405043c0c0701e04501c1201010055080c0c0003a40701581300500b01003800c68414942c480111701c520560207104219000c2d40c1e80e0b288120240b12505986146004444d4250320007441c5859401c0200d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 260707760 1250 260706510 260706521
    0x50910050711120403110603010513020901120f090203012007110402160c18051b070f140a02031606050906181003091103070f05011206080105070206040c1a0d 70
    0x10041941081a02e0032410441d00500c031003180e002689032032a40c640070403c84c5020100f40d002d40707001d01c010442510f8082003000ca10f0034000c0b002d80c5036100c010040b210400c0c0c0da80001c011505058400b2110081da0780400c0d031240c0250000d01194803002c01d42d4074036a8450f204849800010440000414000020042c0737100e00104050b1602500804030400c440c003412007a41e11414040341004520019400f00701c45d000402805d00c50b605c2c00d40402102240d151118410450f4002020001c00020151400006174064656500038880c01e5400d03544094804049000b4072800d01e42c1680200200410300450700c6554a280c130781100c1200340600c54010340c010030180748080341d0142840d500d00701d003000c20300d109a40001e65650305042142d03881840c024003a0103078201c4da02c00d200c1c24200c2d00360305069607000c0c06d024108003503861142009003a40d6010000551070582888927841d804200d050045004102e00009a5100c40e03407144d00f42580890f412038800c0c2005008529803503178000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 260709010 1250 260707760 260707771
    0xc0606030615100e0306010306050f0109062102010201020702091602011a09010504111b211c021303060501030807050609061303200d030b1c0503120402030a3305091005 74
    0x84c0410150a010903c2d0060070781044034003035121130821a51011909505004001a04060142c14070f80516070001140109141b81120f8106400360107690007501215881c5902401000c3c04d03103424020a80d4024854056800550070041c1c11203e18a000340350f170341103100040a00c90544d10340401c010003003200b0601c00d041404140b041d03100c4034a045507a408000d5900340a401a401d0100007114044501c00d840c4011110038040c03210b0307107140180ca04d205100750316001a5103041480066403010600c0d400144181d0801c0000f004204107500507000d868815001c40b4038035201e40b00c0145c2c03120720449402da1405410901c0d0360110348554422640749511040100c1020280d18080781811102001100425110641c035a480c1c01c00d00741048082000a1a40c00f441100f80da583d6142d1244034506484603ca40c008241595030600c03500c2080399226000320061903001e505600801e080103800368040c0c112420342c42680b0050300505108000d044094029190381118038001014058032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 260710260 1250 260709010 260709017
    0x20f0d050901140a0905150408030a0e0102040b04080a050706230f2a0610150c051203010e10090c08010b1605070b0c0f070b0f0703020c040c050c060603061510 70
    0x40d0081c030b074402c4070720f0b160003400e80000110f0010300604215152082c41c945190a01640b01c2c10003000c00c11a4080d070b0382060f80c40c6004699810301c110308a01901a580100c2d019880025001a0584000800d50b200512a100f0303101515503030842551001c100c420100c454060b8900f00b00d00c008040d030018031144070040c203540e052070f135054003004804c25580341060203071038035070390414808404218807503004080c4904115628244684600348480908220050280d5102110304001e420320502e0540b0108000700b81d102d607551261811020020759400070141c10082c40440c401419005e1025000110f4540e14034a03488d0038200c0350207a100f003420030420fa01017041400001c60510030480141148a14241c0b56060074190078107004926502d140b0035485040200080c04190058407180100400710546440340c5050aa04002416003110343c0a441e000440300c1071a0031002078449220b01c0000c40717001c0d42e100402d00d55902001d5512080155054005003001d140061040020355413038034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 260711510 1250 260710260 260710271
    0x23030a08090a201c151a04050405150705070f110d0c030302210702100e01050706021215060a08060f06070501060305011d070b0904050c0f030702010c0909020f0d050901 74
    0x112410020b80c0803021a01000801c2281e0f14000e28101c140c0700604922145401d04101117031352840c4001c3d11a00640d440d0546031117404c040c2c000511401e0400c1800a0014000b929161414548403e01e0440038030303010a40700c0105482c58424010f50300403640c069001100c9603c0c81c0c0b01c20b0100d501c0860200d03408865145154006111604100c3c000c612940051030b2a445506041288103030064281196540911100001d6a03c0d429882d4890015080c802c04042d403d000480300c62041c0540a407000b400051401d4441c2e00c284c1c0705500c034158144120509a002d081004014855041c950001490344d1021480500d800d80744c80d1107804000708220b181400550703c103825284594000d444503551081c0c602214669245060000c0c01a140501526800d140a8a07104d000f0140da40380141d54400000d00e1030001d0104a034540c03404007208035102e141900c2d009010f440e051140e4000034000c402c0004000184d0300a40d1010284502818180050030581400505000340009615074a61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 260712760 1250 260711510 260711513
    0x81f060902071401110906191701030f020a0b0a08180709060b030f09010b030a0b0406141317090a0315020d0501061e020c0907120603020909070323030a08090a 70
    0x51008040c4240304401403450788000000184c00c440210744a18001d160822031481165a180111401c042911030f00c0102d4a04035036089032003801c403d059030a0b0000b420004010f000d030a07500e00d0f10040c401c9810a61030341d00c42d91503440d0303402009c3c05000841d4004001c500001400d00807071840c800003004580080d0b68802c104d40658a5a0740018410800041031009000d8104c180a42c4600800001d1141c1c43daa0004a5583c0c0c15030307103019000d07010480100d002c1140a802c5082a1400207a0454040c1001004100148020441180c03480e175800c121a48040342d010540380c95200007070145800da0702e90380392000b08003081c000c8004000d40c00c10a52311103050600c603060180001756074030140d0320003205d8409104080e0900d5182558403802140c0c1322a5644000c0c1540140107241c55036840c111985a41301403d2640c00017036010119400b00720388504001f0307240301240d00800e1003142d02003440d0030711008850480c44030300080d00204640414580a400032582000540c8110f8112500d60f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 260714010 1250 260712760 260712779
    0x1905010612060f03050303010312090306020d02030106020d09050312070309030b012403050603071a070b0403050c011a0604060507031206060c0c051801210206030a0b1009081f06 78
    0x2600322501007040c40c058118816114070501024201c1030445080c91401d41c0ca0701682d0b0700051100900488a91800102d664070507071180004507402242507441d0b1032505001c83c0a50004d005100c010702c10a016406003034031900e501c0044502c082c3c050311607002229000b0700b15500400302907080c00b030b00c4c40e400000162031a190034003c1060850700385620484c01064a0b1180902c0000c030101420704003444005c1e038000c50705c20112a020008264240510a94a041c03030083e132101405d0140000100414150031100030594190180c00030044c400e0900f0b0300e01d40c0e213652300b611540c2083c0180002c0c4005800f44008258142c005d0810304d215240280c01042603030080d030030401c00111140390b134004120a40e011140502812103643c03240b0072030b500303401119417014440c080403000f0494a07440d480c24880c0501c1c1e01c183c1c01074030b03480d900e04d8104040f01c05000b0040d031550044071142003290003240f0400c840016228100050028004400000009410803540c45000f0a42c0c0f20310002e601c10b44d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 260715260 1250 260714010 260714021
    0x609131e0b160e09070807050a03111206090a110d11220303031a0d030c080f301608220f1104181b380f03070819 50
    0xb4440b200c0084003003604005000b481c1640f0312074041d00c0d1a000348140690440d400507441081c5292054440c402800101c003d07183c5007a40e000a00700001e50344e00d014901c4210103201d06810f0310840d4507511100200800ca4841400000c1d10000a00c03013601040e4003504141d12107140400c000e400d00560f0480c00c5464801ca00905644c8c42e106030b810410590540104647c040d002d461013640000c032240426480e109118009007040b040300d0490080025110607200001c105c01e10903916283c0b070104248041c010344000c40071100500c5501d210b602c50900b000380c41080c0381c00b4940035150036101c0541d4640800303048101c0c3c8e540c0b40000201d0800920346001c03002c9001b0360880c6046805404d1410415141c90340c02c0380603d080074a42012038528054440a640d8085040c2000c1c8103852020340720300c00c0541000b42964a1547c0000050707104000c070200141c1581003d110060140e840f03c0024451610000c07800c40e810300000f20460b0103070b503509910040c0310f8103500c0502c070000440001c482 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 260716510 1250 260715260 260715271
    0x4090b07020a050114070806060a091e05010212070206071b030204050a0c081b090d0302010f0608010606080c03040f120e090705030a1404020a090b03030d0f140609131e0b 75
    0x780a40e203814240882406205c50040e18500b220243d410112002020741c0001084180070308000110385100078841c40800d0010800003201088206207102121060070385440b03414014882c00c640242d0444050342210030080d402005185400c00703a0340c0d08502140030880c405034268136900300201603100c901500b072064806980c00505116450030282c81c2c0031014240e5030441ca02c0d481c21660400e03c0c1d20849881c0c10007104c0f8803801841c1482c0c200d0250014180c20000c0c00d003040c500080401d01504200280ca0050315180100d503100c881c1c0e0441408202d50150a030420010140089180396100f0911403c2c01c4c5001e030b01500054001c02c4e420302e425527491000500000c10018100114440c80303001010300031403c0607a0403d40c0002c0c98404250060300c0001d03964050070802039504008960303040080050a01030303130715900030110062552101c00003440c030154000038000d20740036021b0751207802040040909482d258607556950316000d0f80c020510060009607001150340400c01d203210b00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 260717760 1250 260716510 260716513
    0xa050f03030604050c12150d1b06321606091410090201080a0f0b030709020c0d0302071a040312020f040f0909030207060807180b030a05010b0903030906030604090b0702 74
    0x2410b21800340412a400100391041032202401500c221480d00344110340c001d1152100c1c101900740d40b01c000b1328080c2d12007400030300500d0310380000451855520045022540f407510f0398201d051103240f0402d800d2034007020f181018000f00311003469080303626024101c0103e003003480811500d01c0703944110440e01c1e1007a082d500f150324500e0400009004108a0761400c0e103203030007480b1018007a80040c21126000c0c1c400111241c03030710a40e00a4201c2035004855117400181218a240d03136540725580254008181c0c4002d13400340c0081105214028001c03541c2e0568405c5640075243d169191030114a000540124104100400203541c521080d001401c011700c0180002c940e12807034800d10314000c1c0c040d580902c0005042186500200381c0200e401400c0701c510381080720840d6a4a002210491b0070404207080f42241454041480e1031074001a40c801c0f8200e4000b0819642c9072918954035003c0e40c2d006035030542c820402030700a400c007035003e1500204040c1010a01c40fa0b6959071502c0154116a01b6005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 260719010 1250 260717760 260717767
    0x604081315020c15090105040e0916030b04060b0306040b01050103090309080d032a0e061b1204031103070e070f020f0a0305120a0203010b070209040219030c080c010212030105120a050f03 82
    0xa80c80c0410000b10700e071081301c1383e07113240800700c0b03001a1082c041d6102d00c04508441e000020300644050041c40010101464201078181d207900d07001c1070708441134a09940f001d10b480a421101d00700003510340d00450300001134000030380c64140110081e0191a00880030812031034000108540304000101080700961404100c044440294040100d01500032000c0c11030310b2000c050f40d40d9080f0721200900c20007036402e03d580360041303450304401e8200010000c20b0b9100748181c640000010300d001c1e005586c410307105408031489590400d07a581409000f85003c001e615004955814060003c200c0da13040140151024802200096030a2403c440d5040d4041400001e580300b80181c3d40c01455440302d4508021401c5504008020910780035024000f4041e580f480701040c20355641c03100030707070300030401c0c0c200b9007403c030303180d252010320250a4400d004880c0319030b07402c0e1800e640c00070580e400c000e01d03000c241364156840e00c0c041008564001d108500c4e903000c3c0f2240000800c10900940920703100c084001c540c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 260720260 1250 260719010 260719033
    0x14010c1a060315061c020a0f0b091003020c1f0b12030d110a0f080c040b0d1a04090807020f06040515040e01050a15120f0f06090507090305060408131502 67
    0x1449080c00c95020065003400420160b0360360f4200206003090b1701e11041030710011500c04150000c6607900948004604c6101c001445880e040c0140b800040a90b031010790b460001009034168064a00d844e4515003110f180c0041c00340d003040700348000c02480c1d44081219840400440e002403180a8450856080080e04000b0032895001e0110b90b1484580c02600d0190303010801400400e803503102c00100720310301c004207610318000300c20385e8040e1464218903540c44c004640c500d80240380175072000f0308114030b505500c50319242611456540b1a089803546141050540c2049800b1154113100395100c0003d000100c1c5944865034103510f52100701c102c1996950500102c00703070b4000140d00c101c4c0300f1280e070038052220b255001d8a008000d41c544c104036500c00c1e00c04014101034142e00003a504403510303081c42124680410340210707086491091040156440d120344c100c5030181303180070290403540028041000a1518001010144500129814019220100100b5001031108080300580c400c18500c903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 260721510 1250 260720260 260720263
    0x1210f0f0e01150303020601060305091c120e120403080c100908070627230f03070219030b0609090a0203030403060e0d2f01020d0c2102040303050414010c1a0603 71
    0x1000106140e0010003d545503550003562a178050007031f20209a00e0741e001ca14500c100708032001d020b114000710b0004110710120000c0c030012031143c549071014140440f400340c642011452200701c013030102c2c0b11490701c0d003541c65140d49603103e00d80e81c10003031044203c0c00a6a000398490300c4a030314401c00d20b25640340d29608014081e1000710107400c606101aa190200e400303128040380004540c01907982d2154240480c140500c8585078292010718000ca01002c1d04016010008041891007255860342c0460301c030310320880282071030100800300101000421000d1505203c2260700c40881422240e201d80940e02081c25504a54011101e1a03100e5004511000051281003a902e20303914090f100aa0142254550440001521000c100b101e440c0f510b00300d8820f4040f1108040351407010f1103148280343c4001c00c0b0045600d1030415800420118094120781341c001c0f14101c2e601941c6071030a1600b08002d400300000001c4806051203030728914403000980300c01603441000040e40040751039191510134903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 260722760 1250 260721510 260721521
    0x906050417090d060507022b0906021c0507080715050126060106110f1501050a06050403080d020307050d0e0a03030515010c080a21050603070506030601210f0f0e01 72
    0x301c400c1c030062003045602d44410380071002c995013040300417405490780841681401402910708180c98449130b440c0e4031000c0e104043c0c00484495a5500203a555200022621030754410443d00311044440340600945102c0d402400c1c0942c0545011071600100e9510b456001c8001001ca290b419200d4004000030402644910b98484a051200c03082c00501036906446001c1409600144200c40c5a087c588944c10403c507108980b0341412217503400305100c91f03069043c130244516403140c4c0e803001e07000c81e46a2245007940c04690b48102100e043c12414582c0a0203500010000002c00c1414004403000c80e41d035015040c41c8480708030140000b032605040c0141501c0005003940d40c21214510810003e990000300650070907040546980c0352407a00c00d080f140254803070350707134641c000c090307181c041c40b000596001c3d500803c02102150507580e614814002d40d03000440d0703a140410600b40e00d04500d04100c5010f2803401c4101ca1001900b8001c1a0810003102c0f0421075203181155903048410004c0303401d100c4d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 260724010 1250 260722760 260722793
    0x1e01060603290d051e0105040c0f030f2013020316050405030c12151e010504050f070c0303060b0d06060908031204080d060e0705030f0f060f010e030705030109060504 73
    0x5240001410806000090412480c898043c40108180800b845001d0040540b041c12060002c11850811600341d0b002e444156001e41d9074800300d401c00260148461480070480e0361101181001c05180c1d00c1e02c0020030a20340386000303a21400c1e582c00758251340b50b190303d81003542c6107800142c0fa42880d0645082d20901113100703005200b01040140a03603500002c4080740c264046480900c01841078202070304000381030314001d498592120500c800c40300080191001e070010781081c1802680d13214200416078005803003d10b4041c00210220b0030321807041c0c00300703404507010b0704001c5000f030781d0340e14442c0c5147d02000c0c030244207596501c0c0030f02c4180e81c0149400c0003840004000c608200c1d00d581c2d00c02e00e003070003c0c20007810f504000a8603c4401c2140e003127a030051000040c80c0e805480c04c0e490113480e40e07000301d80c0050318107414000100d01c0d0301100c0c040c80c010b21003e41051040501c1e0001940c1d0210b603088020b43c5442085400200740da0f00740030f11034900784075000102c1c4908261400d4480c0410a070312 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 260725260 1250 260724010 260724041
    0x10b04060302010516030302040b04260114010e041b030302030406020f030c0601050d020a030b040b010501080703020c1222090209011715090c0f0a0e100c03140304051e01060603 78
    0x41007015070780c4001070780e46043c03452031450440c074203e00c0d098000f4801c56010030600304021500040300d041d5903014400e00118a20a402182c030006c200318226594803407078056201c042001800207103803408101e94070900c507083c041c0244021012a540c20800c950040700140d10000b014000d1903418031046070700c20801c100441c1130100c0d00111032b0310303413205000d80c13402401c00d10740d0a010356903181c24400096030400801d860906150815080081c001d004142c040358140c07011071000b5101e031080340c00031804400503245201103015044503aa002d00c0307a00c00401081d9120200d0065000140380c01409101c80040c1e80704007038400501260761f11195054806900e1040005001c1080c5d100080e1010481e00d402c541d5030360a00b814124040c4102000c0c151070042203071030380c40e80c100e00c0c2164903040c1180c24100c9000d411600b10342920054200030000342d010001944103135035000145810034850402e540c0c240e0410a40d40b101404038480105140c0c0d1a8003080101980501c03078603400410420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 260726510 1250 260725260 260725271
    0x5121c020a02011d010309020607080702010201110306030604030f0201390315060c06140f31110a09140115050301050a270c050c010b060309120a020a08030103060e010b04 75
    0xc0010700f212400c0303038040c0c1c19045212048095a0302c07d52200318020350040085488541c181800d05c0e098101c044100d01561900d0344084207030f5005025139208100c02001850980c0d119902101c0840b00c0c3e0700d90100795900c80c800c0038110701c011080407011080c02242000d60b68601c144c000c943d440000340f44c01c2030501e064140440b20106140200513140c1e0380c20a085c0103041450420028022180701030070100002c020f0101854004c1c001074012000222003048644111611102c0801c103500f20450720004000d076580050195000d441202500508591540e41d8440140301512908144030301d0291000303005001c205444925000340034401c3c41d00341c0c21503040001280080c0528010b000541d54558454004034440c080c4e904072441c1d0a483c140700b000760411002d080c5401c03101c605100c41d4200b40110119040500a40f031003450b07084003e06010075074402242440c3d11409400e000c41c0200e0500e41c000c02c9030100154001c502c80e02000a03000c1c42488110708540ea04006140f0807030502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 260727760 1250 260726510 260726513
    0x11805160503040212030403021008090607110712060603060501060503061c0302060f0c130608060a0503150615040825150c03080c13120201080f010b03150a05121c020a 74
    0x21007520341c444d03410703160160340c120544650b40c41c601659000941c8559050094070040d43e0007140d6900401005080383d0786605e03502002d440000c043d0103900d220742e02c44101040900d0000741160b200f50b000ea000002c03015120380700d100940781300360407641c0401d03000401d0060340d0400c4594003c0e550142060aa8544684d98000352290006000824840c941c2e6001c1964004407070103d070143c00158030400c20340c03a52100c020f0680b89007202c0843c401c00d4000c40001d06410049052920004942d0022100382c1c1e80c0740800c0712404100c0c80c2c00b05c00001c184008207140c1d2003001803202803070a0300890802c2015502156000c021035401854140100d8118550042c0d00000711000c09039040c09c049110ba641d0b40f813840d142e405522030456004500351000250399a080b501d00d98a80e0013a0f8075030084da40e400a0302071500200303108140600c0d400b00006a440f00c203032002e82d520010002c0030f05000581e2800002d043c40031039011807601d81c2000c0b4030310b585c002c407428052000700d119002030465034589 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 260729010 1250 260727760 260727767
    0x9091208130c150318050105070207081b10110a0c050a050a030308070f2c03010c09060507110d02060f03151c030318080c030703110115060c05010b0901180516 70
    0x340e115070b42d403200e11003d0140030540240c10480e40011000e000000300c41003810001c3c00782034191001d0000d401252000700d0078210110b104400b00c0c101ca0b009000c01c00c07000d0140840c080141c1c4183c020401c8084142c0c002e12001d0040c0c0780300078060140c18107101e04004c20040c103042c040e40b1151242508200800000e50080c01d03040c1d100c20242803100c1e00c4451010250b4101c920400e8000b9203007828041c4005a002d4041d502a0522003a402003101010340b2100f0b990150490181a0119009100301c1c4002801012000440c43c1e000e00011500d41b00d81e80421130b550028081050b10600100820400500315101d80051100880700202e010004110003814a074100170041c040503181d107c40400350b04071080404025510140145e81c071240440001d0b120b4100a40c203c1c0004c0e208490800751060500400d00b040324100610400725140c03850503111007201420481e0195240c90780d0400c6aa90000402d000b041c1c641c8000e680034807040b01c0002200c0c0002e1811600420b82c0080c5641c2551 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 260730260 1250 260729010 260729033
    0x1213050a0c0611161806090e07030308060418020d050a051b120106050a0b0705030c100b01090603050105012c0d06061403011e020708120a02090901080a170d060909120813 75
    0x100c0c04801040da5085030040043c01c0147c001404607805d040da03903420307988009541e80480e802640c03020070300d0700c0354400c00c000d44211a80910700c03c4d42803070729a0301525040e4840c00c00a440f0380d084502040044e600c217410304003103c261203036012603c941c0c100981400041d259072074211364000c201f5642480c000031500031140c00307820507180c0003103003400400600300100d071040800e032011101d1060310100d0303800c0944900421240001d185001c001070050290180d1810381e641612010030201f98828000c84000d1614030a0480d0070b880041000b25864210343c006510f40200404501c0360b050090000010048008241c02680b41c04542c0c1c0b0300030340120849038440040c403405030b40c5551074102b060182c044ca410640b0149079220030b00030348039041d80c02000341358025140d4500c0307a030707a0300d00b0251510b24120001c1c014140180c10110b02850b444009c01a1002c002e200250181d190400581114500301d81281c403000e500090b040100e806c00141648814200b02170001101550f030703414000c04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 260731510 1250 260730260 260730269
    0x5130e0d0f05130b04090b090f06010804020f1f020708030c030f0a020111030a052403031207180905090f070602070e0c070f050a0b06151213050a0c061116 68
    0x303441c00301da00300d40c840d200302c40e442010340b03010360010b64039919030400c558014070528035a145490744610407401c000c41c450384a501c0041c2c01b88100d65440e00103440181004104981c00b1510724502d00441e07a03088040302408950f211010200141d03080042c2c6040420740040b8450384c01031210701102d0070000100c90905c0c2da014616074561180e902c0503401341c41c0f9001050520071000c010040e03148003aa100c0c9108850b019002e102400740e200307094604590440c7c1161b0150010060901c069009610481e001046072600e00d502d00c0c55050008002c0006810014400b03849006000c0c16400410212031480c50f1302014222251400384065a902801d1013880c401c14005000205070b890030310300360350681c1d400c04114070b5404c1d12071910545882201a0847d900764200000c6900c03400c10500346d4040b402102e003528a4602c600c080c5030200003004100745940e420103428400002d0041c0580e820031813083c80312203005410108c01902d401031210324800701da0f0240a0340700040710014003090481c3c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 260732760 1250 260731510 260731517
    0x609070510180e0115140406090b030613110d0b09010e18010f020703030c080a050c0d0e030405030f030a1d0607110409020d150c03021201051216080705130e0d 70
    0x4440450640490036551115001c000d10200005c2c04807126100012802d1081e40c441c0341c90800c0039400a400d000f180200c5000035482c500512444e2110030046803c00d5006111400a11000b8400c00c00d640d501d00e0000d0101002286031003005c03080e80101080c9001c00c560107450703036050264084024a000303158421005465904c03698214082d8001c0380c6001504009650b00d15880c280a40500541884007000541000c00145840c2061151038050706802003068505200f50092102506107403050f68010b010400c000a6160b500b008020555a60325002e181c46200c0c1c143c0180c10101014407109250b20301561401c02c1d0fa41c0d4804903100e00c0d0340140d031890070414001c0401d00400340c500c002508044c01d0840c2206220403070262003154048a0000d00600c940000c01b02c0c142d010795100d1420003644070740180142e2a008a422488071f40c1403048a0542d200010000c08408890b80402480d0b0071160081c409800c00d03204003d8408010b040074848020f1101615a54110704007102080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 260734010 1250 260732760 260732777
    0x8040305040801112709040206090a0f1d070807020c040c090b03040609052e0209010507020a0b070209011d13020f03071409330d02040906090201020609070510 70
    0x201401901510301400c0c50350700030000200301112810b01c540c04481d184014144049092010040b003840758425030b079001c5c006a0540e00c90794203102c400c1e042209480d03030003100d42c9000700701c0c44810340d1320b5030050041c02c2c045c3e1421008805403154090000d4910010442c10b0001c000149400069100240000f5907000800024404044918003a40e0700010010710002043c003050102a8010703440c01b50064080e2515181c808068403200040003030050304600107000041e0f44507003164040c212805042c100149440440d40c0003403014000d6401080c5181030220b000c1c8154180075400c035014000b00003190916076200707052050003810081101c3c4002d40440c1c060030441d2603481c001c3c0a0340d0009000c07242d803a515154290006201c480c42c11380611442400a005003407003041c144010070310741c004011031450160304d016403005820011904a21900e62820050300d640c401d841d62580213130000600d4801e03900c0024203007500a00b407041160701c8203030240001c4d690641c0c5554052298107020300c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 260735260 1250 260734010 260734013
    0x609050907080a0f050705121f0b030406150305030d0b06040302010c15060305031b0111090612100503190b0f0903270603010602010903140406090b0a0c0f1506091b0804 74
    0x103410004e02c07961035141001d050040d01c5810002505050062013440102e0b0303554515810406800f410300349015600c551001c01c41c8043c40d0000f142c00038080da1010860031140d890300c0c1c031940042ea03c100c510750300000c0d42c81c0f8003004a10035502c6841003100c40c079292605e1134000070080058104040c0010fa060030b40200b0718121680070350001c40e4040c05032510380c118281d00f003000e03240000c6e0307410b215420003021001412000341190703400e5030000d01145c103203051117410395403141d4000c4c2880c4d0202c25002000c20300f680c08004284e492406000501031307248032464403823103440300a04000e900076201800e01190a038040309131003002802801180802091100602c402c104242095400c01800400850303811340c190400c0031401c0c0280c4448010003038800d04200144101d118000002d0001281030040410f0030004141c058014030f440001d211081d182c184c0030000c9400129401d1034952400481500c02d802910003d0916801c10004042c245400007444906000d6900030010650700280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 260736510 1250 260735260 260735281
    0x103020a0c0506010b09030c0102030415080714030405060106171006030f090f050c01090506031009050c0705100c080901020703050d0510030507060206010305010b0d1e0227010906060905090708 85
    0x89040d90420b08440d502d596544414580d40d01800640340030f80179402200c0b0b0554000800c58044a940e0141d8907088000600304071107403000a88094104600303464807400c241c141a0246020b94040d00103020f483d45040406842c11010543d4445946161410000d501402d040f05204071565402d020482912a0106c1c0d801130403462002031214401418810500100180c014020102a2110380c4069152010000c050100b1070b250035030342084120610130340245800c4141c0042c40051900d0401c00c1e5581e030281004004c2c61648000c55440c01c038000d9041d030181d07801e9001301a0800861030100c0940f8020074034411181ea1110705078450000c142c4090105500000031504542960512074503044003c0d103a003401e00c810b490a600348030003807020f45005010f024283d81c1c810600c05107601c0d000d03000743d013029000d282070340e000702d1a401d8503450011040300801801c003655407414441d130501081e00112105074001c1c4e01080300c10b402c00e11071741c0c075982c50b42a00411582000112641c0302a40340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 260737760 1250 260736510 260736527
    0x1b0c0a061e020c060403030e04060605160f11040207060c03050c040501050a031509060803070303230105130b04020a18090504121404030606060c03110d12021308070e0103141b0103020a 81
    0x340c0e0031000006000003450703404180200c00c2d008c1207405011503aa90300007180c00d03004400300c8000005a41d05a000003580c2c0c40a24103003103200b00005055000000300203812a002240191882a102d0210307005056042c031a40350b018015207034050030b182c18480020000e018031203194003410b81d680140f00200b440340080c500103207101c080501031240c03a21182c64503904091002ca01007030814203088840c680b40c8100c00c6201c1d60600e203030112686840100145814511a00c080c10380d940c0d00d043d105502c460000b4504050700e900c540402c0c019451a1458804a039070100f600140742000740070010300c0824240342c072075980703150101403004140341a42e85403280d40d000800c80e528045000445a4010b20b2500740c0c60300988402681d0300625440c55100c0c0002d26001c40018000000e400b003180762036024002001c21103030080758107a15508428540905904048801b40d803040c010410002000300402a80c000d60000e0520703050b0a510400030741a00032300140c18107401095648510f032040114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 260739010 1250 260737760 260737783
    0x105220303030618020901021b01030f1a030c040504020604050409080d020a36061808030c100e07210201030905010212041506050a291b0c0a061e02 65
    0x1050010355240360103801004944500210f100501c1000301120ba42882542c2c10321106030042c140b0341e01100302d46c0c10b00c800c030800b44906140c0d5605103111140c600703105000114076041e01d14040050490201850704401c0200144a05e050008200040e29504c080e02c1c100c8200b44c802051001a900d0081d5041c020035101c0e0320024404541080110b600007458251314140d0542c40180d4006230500780503081c0541841544070801d03501c1041030321301c1113040c0c1d0b10014090401c016100c0c0c550641e1400c66004d440c80421a901c0562a0a00f1120710b1086251040c00080140f644901d4124000e1070700e14025103032982d220440c99484250790094000b003880e550700030000c41d070b07550310a15080600d070070941d4140c402204e1102c480c8a10041ca00c64142a1075000700501ea100380791104284c0411001c24031019a6503212003441c2141003d0350140c05040070200020030100010b01c0702c60b240500c10250203102e809070300c804000054100001301b2901420b140602d02c001c10050003070740307000050b045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 260740260 1250 260739010 260739067
    0x6050d0207020a030f0507050901170a03080a060f060e13020301080a12051603080708010b0301140d05120c0a060510030809040b03010605030f0c030f0607050306011115070309060e06070e0105 84
    0x8070700d806c00c5070100f52001590f02c22a5950a10790f20740000006c2000030902882d010303800740c20074001003800761658592100c0341c80e81c0450203d44032885500005110740c40640860307660103140b051443c0c84012840104d0404a00f14110f600d000b607101d0781c580380540054000880006070b44003043c03143d0300b114015400c1005003034005601c1e10340200101e00854807100080c01c0e0000204046196600f268120b94605803009107c101c040204801401c0c0000e040f100d13841072a40540e6040d150302c018100d0892041c0140030310580034184281a500000d20001d000e000300d400c10301c006854201039035070501064030005051107007000440c0c010299900015414419036540c0101750600007030842c42100f098003070740c0e82c13071610a10312555640203440007008504103200103045544214400d21151a107242212000b90314500702030300c01203098480600103500c40d4500d4040c090382d0b00580c8043d40340c500043c103061900707420040000880da50a42c0c10030000054280c1d20542c1c41c0174603a540d400303111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 260741510 1250 260740260 260740283
    0xd0305070605010e0a0b03010c080106030e07050405011d0a020f0d0c051b010204090f050f07050901051216030612020d0b0c04051305040201020609071508040606090e0c0102070503030406050d0207020a03 89
    0x820404031300c00c03c44000d00c1007402c050501c9050709040c083c00503006040d8070b030185030364200716047d8003400c00d0341a40c3d1315520070910005482d56a50007410300031b05c1d00e41e480d405440382e400400000410018900c00e22a8010440201200180800c680d00c6d4640d106000400200c9120200d841d4440c1c030789c81d10403056222510801c45c103c19401402111070f000d804021001e5488070020580328102d5130000e41513003c00c00928118081e00080410902c1450000e141c00c0c81c3c2d819000c2090400e5607440c0c80302344545180c0c2001c980620600015006c290400e018610390340e40043c4805001c108010807040c00320010419120015082c1ca001d400001c2692039080400009000100400c440a80c0140f143c0c00c0400d80000b40804c0507803e440503e00b21070300750071080c101500c1103840a00100d03219a070355031000600203030074812036540c0d81c50b440140c0003e640f84400245054240d0b005103110b904104020051540c00c40e0884480302c2036120b01503141d29290000680082e125130010742001d4406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 260742760 1250 260741510 260741519
    0x15050105030408250f20010e03031602060f0c010501031e050c040c02101425020607111c02030d1d0705010c082a0609010506150702040e0706030c020601080c030c0d030507060501 78
    0xb0f1b580300c0e0400d07003501c10039040d401090b001124403204803454560541c04c10011080740c04002410040254009003e807403030a080d41c15480020740c0098440992a50365134014020084a900308402c1104010b1018407a5501b946400351501800b4902c60711680d40c400401c59014020301c0079155201e0008410441010128480c04c0389140440341c0c2000e40c0c0c0e00400030410401e5003020900c5030b45030755004007075555a03041c05550175210301255802c2c0344642c0e40c0454580d81d004001240548849d4041c54595004494001c20344021980f054100d0a1444c1d0601c42c042001500d40308984092a11105044241c1840b004600c140c10400c4d02d04a9036144240c019403410111004503001d6400702d911695a640701c0f40d080301c0041c3c4a407540000d8250100c440d4125800c05018070700e000400008480c0b2094901d60724002281e4009030100391111254094035406012040c018403d50300901711010203d000280c551031401d0349a4880d5000340e078804145480342054468140c1e20620810103035868 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 260744010 1250 260742760 260742773
    0x2030a0203071e0902040b1c02090d030e1008250302040803030106090612020705070504110903151014090c07030519020312060301180b07111015050105030408250f 72
    0x102601c1100d4562140f000181142c51072003220110b6101c80c90301420f0500340d400310075804600b80c45100c0351a070280070071082a5145e07850247c0300d9110b07840791078400c3e01c19401e10811600c41c000060902c541d0604102d16201405003400c0304400d00301d01014402c4407140160020f0040b90001d080600c0f000c4000701d03100350041d00f194148c90450b12104026240d5420002c01c2c0e11139118010540e03001544208003600381a00300d12040e100d203071022400c1503881d41c0440e00c1c10080741c5040d002c000d10701c2d05000004001060640280c5803080e114140166520040b0324800340242509840a100190240a0600c65001c0d0b5010b4180c014075116007071001c800c0250b498102c5060381c0c0b90501507001041040c078051050070403403c010003024108546a80303034151a100300420b041c003071260300c640d030b5510030300d081c401014000e0440800180703c12000e6140c0c4506002c1c1d400c0241070081c20814400881c0c1c1c03410a07244021008459100303cbd401c00402c008070403140704002010700f40c40d00c0445007040035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 260745260 1250 260744010 260744039
    0x703030e0d1e0b090625110609010906061d0121020306010608190203061f030f14010905010503010c02060c160212100e0303070e040b0303090d0804060e060910030902030a020307 78
    0x20800d10a4949944d0300d83c0351a01340584401c030f01000c107440880411500c0510014002400e400c00241c7c1000d42c14050b41807100c2180c4074062070350b5039000c00c0c0c01c00801c2c2c401c440c060510340342170201041014815843c805410301600c0e000d90441d0341c4070580005500d40c800f00b403070b42c0a41030303130000d5a4a020141c003503c0141c1c2d401d400589141200711700b403030451003504c0c402c1500030050344c68442150a0400384510313011400f42095124004468590828040c94140e050900c0303014060358900810b500440340e040e00302d144030784d0500440c20a495800038001d500315081111996403241b9064a5000004500d040250080c2c4c90000304802c084c400316044a030940c05000c240003500785a90001c2d100d100071500c140110b04a9815003030340741020707402541c245d14080c5c1107a16202507072000440d0401e01c050f040307490718000542840503d910020480384c105041d0303407990400304a07000040700441c80110120401d03030754020306400e5660400030710300040d17005015602c1c070325294480d5150307098 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 260746510 1250 260745260 260745263
    0x1e070513090c0b040f140612010b030405150903040501021b090103020105131503020702010201150501140c011811030d0e0604030206090f04150816150e03030f0d020301090501090e0703030e0d1e 85
    0x80030103040f055003400d600712341040c480c446580125a00701000c9038010f40002c0d00c103a520740300b1280d6100d1025801100c09001c0e10500d4000c1d034442d8904070009151544002e5010b0000e0710001d501c0425071509502030781582e50900708a45c4901514483c564161000d030f1255000c0c004045d098120389402d94002c0001a000380d000748815240c080114003a080244125070001d1400c101c09002140e65401030711040045a0002c5103804000441c2096190f640c0829600203488020079055440c080000156009003030402d0341c0d2644900000541e0341c00307a480081c1c0600000075603e04107503118a41034a4101c0700070020403012404410707000c4003e40f5400364513400e10503400e88001200d0120300100803a078840100300c4019200c0801100d503a0070072956560144000c0c00a2a8020302c00e01c05015061845a030042c4c5941c5403000f81400e070f500687c00100041c0c906441505400d42c042802c00a41e9010304040701181110301c041035460340701d120301400f00740c1e10940310214815803080298216 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 260747760 1250 260746510 260746529
    0x203060109050d0b0117030702031b100206240f0603130b01050d1e03170a09110a03080703140d1a0301062c06030a0f051e070513090c0b040f 62
    0xd50b12503092000c0c800c125000036290384000360040001034010f404000780540e10078103a0b0f045c200242d0100c2d150040e4426104150505485c05045c0e50504804000e502500c91004040d20b06000002c03548105007a1820030807500040b618070107544419041c0d40780c07110040c000a40d246425078840d80d00d000b20041c1101d41c0c0c0d00e240c00021703d502d40002c0420005030480d80e00c0401e06e401003031060702c03106252000c5051000030807007104030b00c1c3c8891445105845000c008a8141d03003511740060110f98009a4600c1802034074014008103190409442e101541428003000d180507942001c4454003980f10206007850820714240d030200d014a031401d0f000001038009220740358560005001d039021201d20024a00c91814420072519040c40880b03410000103001d4030800011604c8500c0400000a03080d00c0c158400e8814440015948000400f54a892005000035038209800540c051078103d510846c00d6440300e00300e0051046200b4034034000c0c4003414019070382d00c0e600c08086e00c3c0940c1038422140c00c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 260749010 1250 260747760 260747777
    0xf060305060406090c090b1e0406050304050d020d080105310605031207081204030509101106060a03082a1c0f0504030c05010c060f151511060f180a0602030601 70
    0x80d4900f85c0039004101038946c444903803040c10400714003803503040000c041444000c140208004140300320700070405802c41e692001e6480c07415060940c07804a0032411344c005c40d4000c6c00c681b10626844901c070790540b101203604c0710403000210180c0890000044400c00c80003406d40c19a055402207034400c40854000358107039001004104001d108600072503a0141000b04100701494542d02c0720425103900c1803290601c0390a204100c0d0100c0c011030a040000c0700401c0d042c1003403006411003040482c1d84480110343c2c0700e150500f96a0780703110034010101d40e2042951420410001e140034031440f141040c0b00b140485107a9000403100113607481c4026118400318201501e01b0900500c103404880a603500050301041541c0b900d0011603405003400400c0d070f4600c0c1e60740c1030b101c04038800380194480e6880500002c101e00303050620944a2426000824042c007890b103808610618002c138540307a00c607001c0720280c00c05070703a104481e8560700c00c006000c2c82240203000100041241941c09107000d83c100380e0314204c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 260750260 1250 260749010 260749019
    0x507120e0105150d1e030305040b06061806130e04050601030b10030507120804120b0f07030c0c17070807060c1d03152a0711060307090611070f060305060406 69
    0x8840080d01d02407030040c022400c41103d410186000d2110324824480d00c0a01c40c0e248408502211380410708400003030304c64040c40244400f5406076500b115040383c00c1880c08440100c40919941d5400203140034000201d20b0041a041f801c0000c0d004020b80b0340070164525013803810540300c2c00d09020444646080c1d101044002d40010055001d880c0e0090080000c00c4c03c0042c10780d0465502501200d4194081101058031401c0210001a26126810f0320005c1d04207c0800205041c0041c464000c152810034000c00955100c641c80c240660000d0102580d0051950b01341020b09c1119005880b2840001d42203040040d550300049940206035100707a02c0110444400c01295000c1d661994158080050000da8a011105040d0009a1240b441c89011342041c824038003082090401c11703a2860200f02e020034440c3c03150b040d0a1040302100c660340303145401d030b02c0903100006c140603001c01c01c4004c00354200303000020011507001d06503d507000541c09950f000014003502040747e4150140742807410008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 260751510 1250 260750260 260750263
    0x30720120f0f0118060504050319170615090d17030702030c010c080705191107230603040f12120204090506031006031e2103060f0f050f150d0507120e 66
    0x1210001c5124040030384c2500c0e2034000c1c00c005030080e1403900007048030709540c6001c100400d010440c141c5555001c4282d144009200600052207240100c0404070066000523060048031415030f0110385500b8828000e040c03100d200092103036001d495000000900620396000409441d01c645c000c0002d00000000c1502161907000c1600c215000c07070024042d144419080640030344901100d483c00040e505030010b40c0a2900c42d607644031088018000610785050f40d410b13450f150300e1450540d0810b1960a0594076140c2d0306824030005081541c60012112500c0c0c41400342c06040081030100350340303480d150711075403008100907101c0c07510a2161003000c003100200381c09407100f00c0f078105500b500081500400640c44a01c5010201c0300090400c0034214001d09140384405080f81c2594002003d42c00d05081054ac0002a0003a010b05046400204115901d140000d503240c101612101074008a500401d5000e0140115004089061104000300c09a00102084021050302c000380040c0010950305d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 260752760 1250 260751510 260751521
    0x1506050405030a0f020103090b0f010f0602011104051933030c08010e150306010b090f01050c0d0c1401091a07090501200a1703010302010f050408030720120f0f01 71
    0x10740d0540c1120424a0202d07200801c1983c0b800e0042c180424101126582d008507030344101c621700381024042c8010f2052503c0c06200201511050008004d2002101607071080d44c05107102c0c80b84914044403034194141e901c5ca0a0300014502c0080705002001c011410108051601082c0f83c4a072000160031b4004900c40d0261020161080d00da00c070b5035908008210303100950050628001c10241c01c810351250314100320302ea00030082c05140c0307078851202d08100680d0041d0700174280d0401a052040203241480850400c2c40c0540324103000311001094030304440f86c070710240c4440c0da195282041000c24040c1c4180c43c074500001100300d06000b0b0707541401c25591250f0038040d0358001a00c0300021031032a206d026001d6219130346e010884880051990724179075121100d4150040c08040407004200f1941c0200d40303c8084000c074107007103082c141083c8a1ba42c0d24003404074040d00d0035400781e1a002185000030f035405003c80d0041c0020444005511400d072360b4102d20101600c1d944103000b4012012070061040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 260754010 1250 260752760 260752769
    0x1a040e0c0322052109090619170a020a0801051005091311060c0d090317030705030a150b0409020a0e0402131503150e061e030c0607080904020a0315060504 68
    0x54820b407085148880800503841c1e0300311810700c5080401c460384440b05403000640c40d808440740303644005c518144070300424003400481c0140e0b0303080318022901e2a000b041d4000d03100104204009034030718554444c98203601c1171010703402c14440345012410740b0b010741100d84184201000c2134200343e40d48051102c0c00030700319203d80c0284080c1214200141c019044401c00c19401000203080440c90f2500360f0038001d007034075158003190002c0010020410f403c643d0440200c2c05501c1c5c1070035031829650143c441d06c00100303895402941c0d9803c096060320b6926051010b4460808050b031a80d40700c051150003944415045c502041c40c503e44c1480a2409008a85076280c2600b40d0240d95440c4c110038882c0340c20742da0500410706803a0b902851030281d040d2400c000a01841d5007071803407801d100040c844100746500d00c10078030360b240914400260b1000250b040070028140e0b51b041e0380310b0003410207540601031020312590207030000400902c4168140c0110301c3d40752010b41715000d5680c1e145001e8566114a204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 260755260 1250 260754010 260754031
    0x60305060a080c04020901020709051314010510261002040f17030702060a050c06070906030506010e030d12090c0e010f05030d080408030a06180903180f0e0901061a040e0c03 76
    0x43c80d410904058010700b11844c4180120742d031080d264950310742a0744c01181e0400300c0602481803002440500e0b061003045c500400c00822150608456075500c0300040d0051204000400c1440d02c2d40e11500b00707030107c201c0807410594524081200004010390b010784900d0000130032007100403a40f48004070090796003401c1b1030003c501d411034550901400d0780041490394107002c5d00344a601e4a440301408003a00c10251a5220b441c643d043c11005421a2070180c8014108508081c10303038100d440005866900f4045402e00355204a0201c08840180500c80001808409412000240c0d04c0c50b000ca680c2c1a5840c4018410f0440e07125003d160751003a24612907000034200c0b40100d0301046612005540044807400040340064640005048100410140104680c4e842221b8014185d10956517031040e20b120103203070340701460068102110780050062100581d00c1c0d1000c50300c8a0000d46c032102c01040d0f0403103072040300c000860001600741c1207803144881c045181c80026418511010480b407141c4065407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 260756510 1250 260755260 260755273
    0x20c15010617010e070c150902040c170403110c06070b1803070804060c02031204080c04050609131707020904050717030307090915050901230a140108090c19060305060a08 75
    0x30402c14008800703401c41c0e042c0700c0b0b044040c0c80880c01e60547c00c40d49032000c05000ca190308a0348140000c07124288551000c0144030300c1d2031a0f0b00d03084040425049038152401031014502c0100003414440d01c0c01c00b0940c008000284082000070410300280f007082c0c043c035101a581c50700e210440d181d106003a001001d80d24100000e1203080d000b0382c0d64404407400501118810350403510007000075480750300445010780c040300e80040e80346000d0013460360080c026615041c040c100440f00301640c00602c074000304180d00d58071035003440d40100401e9443c8036800400c1c0d000c4074106410100d80f5503070b02d030040401024901704990b1091200004903802500f0581c0c642e5003543c0b820242c40d000780711101105480c00c1c1816800103095440410f80780c043c10005a440070800035001c1c0340d00488542c2c0c65941e00984100708100156242001c45d2100401300707007401c800569801000e03a060000300d00c1c240d036000c0241d030035001d034404440301c0e04403d54001d600c080109840e61310802280b45018490f00c01554000d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 260757760 1250 260756510 260756519
    0x516080c090a030b04140109140c100207051c080301141c020108070c0201020a05010c0302040801060807140d150c02031b010e0a150b0a15090f0e0a02130306020c1501061701 76
    0x40d481a0b171081c010a08030031881e481c40e56450a64215002c143c0b24500d01484801d0380c000184503840342c4080480c0c841079032020340c0310069150031203072040c203201e0b10902c42c02c0e120b00f00420401c07030005503026008595030342e103e04131440f44140c0000f60500801c84200e0341c80000708030284407240305405854240003603550541c1114120b0a94004904601a00c58a00c0024509002d80320341c1d000c8680300561218240f540f81d80c01c58565074082511540043c20802580c0c41c404040c4141c80c0050f502005c0d800c1080c1000c00007151615080070740a40b41100055070700d68048050415280012103082c1c12901c0c1c800300900341c844d0502c2c1111203811a42a1000150a0703400c0400d0400a445020070320008590001c0c2010507242e00014081440340d805054142e848400700c5d01404001022009480c101841014204c50041040380301640c00209440c040c00400c149400071503000e541996942001a80d0640b54400386074a44200c541ea0000420ba0700d01408407055618140c2d641c0000c1c41c1c0c42c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 260759010 1250 260757760 260757773
    0x803040f030509190e0916170304080f24070806130e010908030a0c050c0a08070c05040216020f03010b060a1209050f0d090b07030c08030403020106090516080c090a03 73
    0x10309030201c051003820050444503488480c41401004607003181c000724246000d858007a0540001e0415a46e1340146400f489402c2490308010141c500035003030401c015608840141c40d6101d981c0043c1902c0c4264550607401b4075000030384003035a100d00045c80c42c0081c100107411840d144141d89500100d50382d540000d0880c1440c0f40c05030081140408007083c07903440248210b00710b0b400154207480268000041100c403020034050001202c0040c0341c114a451558012103880740741300c400050800d603000552000b401a6070340b800c0e0281600500455941100042c1050020303c9410704902030000d0001100701d0303160611542e4500c44014000c40d140c0400b180040701c0300382508810300c15a0741c0c2c07402c40801040080003161907011480004242407030524201030411090799000580d04c0034108510320019a1245640c0c11059000b980941c40b1748030307840d0681c0902466000f001e0f58a240400b00011640380d14566101c0500607268020340d83c44005840d0207510845103102d400828401c0c007000000c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 260760260 1250 260759010 260759033
    0x816080706300e070302030c030c0315130501020d0e010b010804120c02030a060e0105070801090c090501050d0b1203090406051c110d170a1706030607050a0e0607050a0501050c0403080304 82
    0x14110b41800582014481c10495040e903ca0000c0b9510030700040c030450404100d503103c0a00301f00d00412a4410140001c1c5c1d13a00c2c0c107051840c1c002a440310100d00c41e03070594165441c400ea03210009540b03441495006800030207525040344410f41c203000b01501d02e0f500406506004a0f000f4540d5000079007084000d0742e0428917028100e800d4405e50303030018081011481030f90102c3d030b40030002280c9800e007210000c00900060300900e00c22807030000c0c40c4407101e4100e42d207001101c02c2820000d446805e40c0d1551002406d4040401c4d0300410005100d00403500040000c0070800c00132901004440d0316101484042007003204201901034490710200c000c42e441c1300c0d1142c070b504401480300c2030740b60003036444408641c03c8401c18840c0d840007144261034580c01007401c0d0040162644c030315000d0b242c40400250b6812014006c007080c04000650300000c90700c40d1281543e0300d403010700101e50780c1c0a103291059450100c8002a5410352030000440c0360f1507040d10807a012607800c0101a070554039943c903180014403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 260761510 1250 260760260 260760317
    0x402070b06011d04021303030305013002270109060b040e0c0d240807090203130f020103110f030f1303120b01050d050109020307120b01050d0b0d020a0816080706 71
    0x800583c0c04503456650f400109605c2d010140c4180d81c1d00d1640c81c2c0581540c1060f04403500314581c403045403203444080001071404c46406160940e401c003150001c20781100c0701c89151007000c001c07080b0942481c00c020000cd41207900c0c5100c10410700d0341c0c5030007249981c020360203007082590750100801c0c0107a100c900604007401800e0400203c07401c0304207100b40795050306d01744411002d01c400d5007080050340c184000c0c0c0c01400b040d0019481d40c540352901d030300300f400341c408020986240d20709100f003564401c0c0c0c40428030202c0072a8042c3c0e140065881105660811105852501982c0f800640b042102c4405c25042a9140e12020340744a0035080140c0039101414031241040418064011083d400c2e02400d07000780f9081000594070f00b00f06100400b0095040540325600c0c0c249030030b80d0441e9130300c04100d030340d00c0441850000300031800d0800a11101050800658465564800482c04030300210b05180045c03900d01c1036228140d43d03911056141c984520030040130906401c4d000038502070783c01002c080742 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 260762760 1250 260761510 260761547
    0x6050c03040807240207030b0a090501060506032e060507020105180307090c02011a0a14040b10020114130f0b2203020c03010b01030608030f07021903061a0402070b0601 74
    0x5900c2c2c00d0b205103403000a90000000265180f07140003129590707284122400ea040c800381c50300f0303400d58032000300d80180500000074190b950b0b06600c043c04420341c0010043d0500412141e90380c14102000c00f41959181c0d01c0304a0301c003114101d50560b0302c03041080001c4074000d41707a540c00d141283d001560143c010745010501c42805103400c41050b502400000c015245070301c8005118002c26074000d003151050700c070440d8241c030114191f64199403402083c01c1140c005407007020030180c0440200740604803d100310340c1c0000e01748442034030701501034011100200006081210795500c0c60f070045e204415019016142e070f400056840b02258003204070747c2c2e0007911540c00d0101202e00d0003495102452441c016001a04110b042a2580c0303130a028861102200b46410300a1a00304511181c49200700622000303052400104801152079030441e01d400c031600b500201c00b001f40c1c0c1e828100c010308100c501c400e035080d031948403070042454148250b0320040d41008800080e80d4501005640c0400496255820b9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 260764010 1250 260762760 260762767
    0x503100b0d0b090a03030501080d0818030706020304081909060f0302031b120a0501060504081f111306080a1103150a050a2706030f0b0c0f1b1b0a06050c03 68
    0x441c15880700140181d0750300e0300801c49140301742030060445006812280c5290054225102030380da1000040360044442e1424814002c045280280303544580e42c002091640080100814001800060030607100c0c0c048032078003c4480c0180842d03680d160340c062403021030949131281d51458402d60186510001440440202050803c80d805203a0047c4ca061850f80b5440410030092071818040c0c0c2d4010481405e0103414203007404a4680c41745079548024900e405030303152031450b010781c680046004c0c0100c82581955041e0b01e01e01562942d038140900000700e000c600204038840c05a118944241420200d858210b84170840c008402285154446900c06002540422103946603041000180a00e00802801004401c40c10b401802d07a07440100c5a80d24005080020407051038458030295800072044115075100c0d0950111400341d0480c80c2c107184400b09411614001c4c15101d47d4118040100320b41e01c061480d1401c1804c0c014285003290800040041044041d00070030140000f031906605407800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 260765260 1250 260764010 260764013
    0x17060a0b16021201110a1d060307120b27150907030c0224040b07020a06090c0303022505010c021c030c0b0108010903140304150e0309190503100b0d 65
    0x4180d00304064070302269a48030910411460055110010940e08200a00c404010480c52600c24000c035401d0b035041c0a0340e080c900b030300d454a00384a0f03450340c200205800e880781008100200003621100b007030540c0c10f1609600d540b407032502e24644070340171050210003a440150b40c40c50740d0000300082c107a0ba10703a40341d01c90741e20fa003561074400703c0b88500840d50300001c92a048000082c580460012084103007084060100894200c2c000d459a1003600100d02d00055207548400324038103005c110002c0c05003490403241004200c20104002c040324001e0b42203c110700c8559400640c80c1c0020a500c040c01d450801d02001154050a902c1d00098001011009060b101840981c990344004400300c002481180c008006c01c0447c011040c09400c00e00e000700303c4a049640c1c041d010441d01c3c0c03590700030b00c28040005400c0002d10302c4d81007040c80c190703d01030000f00005500700da5250410303143c0c03d1145012800311284402451103980459500900400601d0710450044008103a110301d0107400c50f01d101750000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 260766510 1250 260765260 260765279
    0xd02010314010303050d1103090325050d0f030e010c12050a140a02040f15020604020f132d020c07050d06200a0e0103090f14070812040807080304050117060a 69
    0x6008502070f8446564492509040b1821501091118407c6038070502c20b0140d0741c200001919441805451080c7d01e15407c03100098000c001800300903d94030030700307540f070400c5540800584051a070944050100b015070030a0b043400d07031302410704140c0060104104450040b01c26000740c0e4110780f18000024450103444c6820000c0c0c01d04480000d01c9980018080141e98459003602c0d009102c4c1d02071401e0f04400d000c40003501d07110f010300b001c0c0c840d0790208000025503a81004005569550002c01c1008200101d60b403100c91905040100c5281e84911034698022903030b00031101040c00c00400b80c01d1440c01c1034200100491051415600c4d2596641528031043d2404440c0b010180c03268010364459078000c20003411030302400504c078105801c3c402080c00041207011900c02d1070751320861841c1d043c0c404083c03031458511268407102c01c91150031054140b41060b4001801503910340c0c02900c1404d62905400c1e0f940c3c1c441c0c1d10580340051020095040c10020300e0441c16001080180100129a0782c0d80005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 260767760 1250 260766510 260766551
    0x40c1107090912020a15020310181d0c0a271404110406050d02040203091002181f05040b030403020102070807030801170a02100f0c0c140315060f0d020103 68
    0x8074201da9100402018488508202d81090042d4030040148103051303656007055900c19050781c00310b0741e00400814400d5840d409000c024088480e904240310500783e900784081c00f04840d260881d12409000590907010100704885142d80160090714014070b4069000c841a12090300d03054108040380c44a139049003c4e000d002c092802c402e00042090a042c2400c00c1d0200c804a07600d485030780340030700802203070b200d0201d200303050741c0c040303400680300d507910004070703060480e1800000340080c070001d00c02d5490388030104001d5001c1c0050754040b8030041503010780381011810403032140108000307120400c081c1e040302000359413040c480d2002608006c5a5070382d40d001504910012400f01d0014070041c403190b2115040d24520400400040154a03200d401007168030b04009040d81c01c001150030101302a602400c2c603039010303540c004003120951b035481c2d00d03030f8074a01d00b40c07000719102c1d00520010440301c01c0004d05841c003449004100e40700d509503200030041d000782c501108a041c561140721000603251075032240d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 260769010 1250 260767760 260767769
    0x5250e0f0901060908071401090b030a24090f090b04060b060708030f01090b041a010e04060503061305250e06130f09020112060f0506030a0e071d060409050c040c1107 73
    0x2001c0740c0905000c05c4605100c099000051891510341c10071200da80d0180c81c034000c0724180801c1580e86e48984000c40042c0841c0d20191074000902c0140c044a600d2365400c507002c48941202c01c00180d14030b50a07035401c0e1a0f200d480504940b9181c404900803550701d07071105c118524000d01c82c500d811065503071848250002c49038a1b4580c490b0a004100000303190280780341604040b103041042d02581c072860040007107440c3e6840d0410a903401041d0321a1501d52140700030b040020226031135450107242d402511411403800301c0c1c05000ea0030108176061094542c2440009502c180030f0030150070511448568000148880d83c001105000d00d8550402840340c0c54007141c4003040859821400d000141103480d103405040ba01d9407800804102c401c503d42031450644a003100c2c11540c81c1c840d10070072400b42c00a0030483d40e0078000c02c00c00241500340c00034001a5543d440e225071280303075100740802c000c840d82160003903c2d03038000d0f0a41c0314244c0b5103980010845040741c248910103a0110307180c0792600101713030131 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 260770260 1250 260769010 260769017
    0x306051008070f08070507060b130e0606030c06070209070f020a0b0f100e0712020c01060302060c030301060315050904140a050123090607051e04091103010905250e0f090106 76
    0x10302c42210352180c2c1160502d0040d0501c0703145418000001415403199050203803071166a204030070a2541e800e0003900d0f40c0994200d0500208020800d005c1e21240260303180b501c24031440080382d4560030001d00b903610082e001082648507070384000e801d40d031514441002e442140200f104850015402180440c01000c3d4404203c125241c0072070911085e107a035401c158002c503240010090380c2e030350002641003003101002d405078035507030380e68aa140540150780000f5407200021602c11040c210010185048520700c0d90240300c3e00f00e14000c40c4c4d55201e400e0007402e0300600d000001401198000d075091020303d141d002110003000072510b46508540d08142000d41520202110689204514031101d8100041901405040c20140c0300540300e0b104180c540d02c0c012141030b1680801c080f8240a881c01030a015101740221031128048410303640c024001c00d02c9262070720001c6440000c0b448007030412800150310356009410640e00c01d980c1945c2c40d8416903030028101204080c50384030030100074001c0440c0e03103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 260771510 1250 260770260 260770277
    0x10641131206022a060105210601090e06070306030203210d0504050304090e011407080c0705060709031505070f081008010906050f130305040303050d0b0d150e03040308040e0703060510 81
    0x2080b40e81300e00500084a01d650700d50644842c980d0a01140060440d0b404455a80d03001c04028460002c1130035a20052045018450000818000c1a00b052802c81d1003042030b150165184101a0115040d0b400f01a4055200350100811030806644030b8042d0342800710b181c2d0030304002141d110241c64045800311250f400c0071904100a4203203000e00c00c5a04810030003844261011001951040002007145080004040c0410080152070080380c04164104050718124613041c080903000000070300c800c452a51000700801d65600c2e43d4480e0b50b0285002d80d40300c6100759061102102e003550050114035007640003941c0010034503024852680030301d1065a01203002d00d40b410103420710f0300740281240160301c40c0d481820002035000c8215010799505007007941c0c50300c44d6428000014501e0000c01c40e00985641035a034140901001074101d4100b28a2040c4810b00c40d0b1242c09031603029078031004200d04801d010500110380c004455542c0070718035140000309550394400080c6400301e2501d80e6400706000b031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 260772760 1250 260771510 260771527
    0xf0816030506150d2909060f0103090c03050d080117100e010216051e0a0201050a0c030201060f030b1008010e030403020609060f0a1d010507030c03030504051501064113120602 77
    0x281071005501c0302c0c404030281740c0c00d20480468202e40d001824103200703500401039416180c1c001c3d40100011a0010031130046c1580b20310302103030358000340101040030404107030000035540c011061050745211440c3c0030b05502002254080e0140003000e0941d80311b55000e0040c418000043d03060844018002d03401007020000d15082401c501f4241d048402c041d4010340a0b80c400b60360444101c5164000c14076100000e8503482c10100c0c01000140c10204c0300d80c01c103800000a100c40f500c060750252403400d003205d0301c1e280d03141d01d05400c9411350802c800b040d030018002040940b60240103054200c1016101c285881e00c4e668010180380d00a043c0800400e144400d1001c08503144001381203140800e0904501d07040c1329440c094000703c0c00074401801c250300e13400081c04104081c0205c80074960072100c03824036542c480341d010700451800752004580003541005c8198200c9000349180c401d40300c81c914002d202c6041803501415503c100c1c00000900f82c030708000035464902100c5405201e018403030060b20741220 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 260774010 1250 260772760 260772791
    0x15051e01090b090721020301030803150301060305120a0909020f0a090b03010612020309150403051809010e0c0a090f090906050105090708241f0f0816030506150d 71
    0x1a04003010301803401c120002c00c3d860b848a4150000c0f40c0b801c0000d11708041360102115061800303c02002c0301c3c00070000000f0840484e0241d400b92502078036148500c200340b41414200e681c0c03444003170300700e80c0962100701c0045080001000c0c5803c5ea803074081401500c481c0303900141e03032121007200d011820015000c00810340c070210b02e10203091155544c0d4a15450102c00604103074000f8084c1d00702640c0080814059907080080600640706144502c206281c54200540503030040c001c002051001c4150a41036840d00310700840c180c039081003020540ea100c0c42c410b00e550350003d4141d00c00340864104081950b0510101c0ca00042024050200d000d12191805000b515010790160380036078204020701503000d4109484551042110305011601d29010003180003561682080c5600884050110003007460f1030100c0010104c865121075004489490044403944001c0700c5605500311105c141d4105107100b42c104641102d40100385038445140d1107130660143c2d0200440c0c0310042d581d070b031603d10140324 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 260775260 1250 260774010 260774071
    0x9030d05091615120c0c0f03090501090510020a1707020a0308090301110406050a030e0102190903060e0703050303181c08040c0f081207062717180d1505 67
    0x883e10302c104052442030000742482d100c3c4d2256102c050344416141070510b1284008a9600d500144032000001840c24050541c1c03100d03020f0a40001c0c0300c20004074440c20a80004840800ca0f903006100c00b008545440070201d0030380e0a40c28070301c0d03401c1007100003584e5002d02480c060740c051805960781c1e00ea50000c16085880d84048184e107030341c0602082203019003200c1035404c9000340707040c08030784009a648034900a10600d034110809400081c04096a56071204403503054902c1074808001100e92040c00c00c1e51004140301c010400d40c41000010908514448803000c038003210000c0313132120714150340e8091803204240700744000290305404100c01c0c00140d542c514001c005190890702140d042428050b1a6007002500c80d40b280000100102044540c4d4441c0080442c048402c00340c0794a2100c004070310b0b0302240c1c0c05032810080200d40e2800482c0000485030031407030012a218180c40da040602c40c21003a400029558102c1c2294004102402801200e00c905128034500c100d80b41413601d502070011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 260776510 1250 260775260 260775269
    0xf0c070816060e0f010306090e010f0e03031302060c0109120c0221060c13050a060c0c080607081303260703150305070e180f07050108060108040506010302060309030d050916 76
    0x100400040203043c1e0002c2122090441c20f8030044880b884910060780a0842c90f40040607451800c401c9106000e810340c047c0d5803c0c00c051400703000b2200320141c0140d6a0000751024031400419003080801890882d005080300d882240002c501c00e600c90719400c145101384204c40020443c400154011454070003840301b22081d032200c400c840242203c42183e917401005258104000700000c07846207403100440d0b01300007450001e0400b180c850712040c1c020003944020b10300f00da100c000710001048a08000c18114410b40090b5212001c503070740d260705604d141c42810415000e011307490b0035030070b440300c1da2083c0400e2100b040b030099080c03400c200400404803801d030110102e141045417000e000064020500700100c0c2d03840e102040440e1209407030501c00c40d0002e04004240c0c030030304258034820140410100c0445409880b90481030360303604010748000c0001c8800808a40010006000600d421009076070000e6054040340d003001a00c0080c2c070120740b42980c0c50380ca00d50120340504180050790301c0210180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 260777760 1250 260776510 260776543
    0x4020a080103060c020a060912020706080708041b15030e0c030111030408250303051b07110d030504051504030c060e10031a06071101080a0209130f020f0c0708 70
    0x140820003810a001070100a158944403806655468030800c80007544035006081003211180e98503140c640810510100c40240c068408009070b818043e100e035910902150301e4072501950f6903a9005e80c566541126001c420003c0100421002c403500704000c0d04c88103549001505034107080019150581c0c10f00c0c5548281e040c002210b00c07525071542600c0e001a07125040070b84580d07140310241c105400415121a0070754070b06109406055050700418041c03010341d591f0710f551200c0103005400d540304041c800303455028010345201d40350501503150a107040c000d1610b1410b00b520741d00020304040c102c0c110f41345802408a418030500c21500140340c0105a6414000801e052800128004041d001000400e040d9101014803600748a510500603204005003042da50741014901320b8040400002118001802140000c2450030184221418058001c1030300744503c214a03420303000b03015014026240e8a40a1041c017408140410107400e0b00490f41016261503800c0c1500b09240000d09e03680ca4254 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 260779010 1250 260777760 260777767
    0x191202040e0706020c01050c0309040207082511280f0509060420070c030213050106020f0a0201140c1f05060102281e150c0210050103050d0c050a0c06021b0402 70
    0x106400050074605017000303080c65510303030441141b42421809800c01e465007050000030201c0030405d002c40104601c5080103101554065800070040c10000c15020007446000322007003128403890401d076070041c0040107001d03000024880d02c400e802403603100d0b400b501c41103000040034842d0349440c6500c2640f11605442c00c000c8215942c0d8003d0400031012180003140c0c200061b00700600c0481c9071110007031600500004140c40404040c14000e0000744a90b10050003007001c081d03d007003000300f154004550140c1d00e94000c20080814252154400103041c480da1280d6802c0b40820075400803c0310f61503041240004042c5041e1001a06114540ca01400c5407205e074064206080600c402c8040009c0c0c0080c4100886005007081031000b040302e20340a0300340140c040083c031000c6d0541d040030305500c0c0954241d481c01c038641013180040c1c075802c0c000100700e03400010b078446480c0c2c031540200100500840480c5c5280805072200350348008944c00c0340740103801a214050318404809130352030442405881c01c41c603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 260780260 1250 260779010 260779019
    0x9080d1a0f01050a0203040317070b0c031905101a130f0b12060d0605100f090e06040b040309050604090516170f0a020408070603020405040f0e0d0e191202040e07 71
    0x1d00107412400241408008125441594420001c0e076014607444908201c0301404202c0082c116080081c08503800d101c02d1700001c0101e1010300a690081501e90048441943c00065901c0500070040408001300c45608000170071030700800012180440082c074895540780030404a0b44000100d402c02d0542c2c03403000000300b2501310f01e2411600340354200306449515840790b0002810445240030054070b12428841400f00640b01700404e40e0898a803090000741c0b03190340d0718807078013598015000059076070003403400103000c40c000c035244a50140c42450980111a12480054010341185c2c0001034000c0d607a500300101a95038468490100046003480c40907003c07510390016a101e0003d1140c9200c001010104020080d680c0544010740912030951311100c0e180c180c010000d41040c81414807860801141050103d500c0c0f2685465600342c1014012a4400306001c1e1900ea06440380f0303e8004aa9400182109174600300c000f0140c220141000250303c03241c0100810703030701d1080e07440c251500044410803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 260781510 1250 260780260 260780269
    0x30d03090203061303021009060f0b010e011d060909090d02061f0b1318020c1902090c16050102120402180c03011518031112071409061309080d1a 64
    0x240d00034a5510801a4140c0c240345c22030508800020500c43c403424400400c04002da983c0101c25084210401040a91502c00044400c0100903100500ac90300310910b207160380d580d01504c1c410303100014103a54a1f1185041c080782c198403048a0f002025003140e100803440980c18096103411003841052825810304544807005004074034402c5120401002880051100900c00100014480403410040c0d590b00744c0c03140b202a503c076414010882c000d84a004142c0c8403280401c8442e00d402a0202c221596181e01d01c4c3c24a5203c401c59421a181300e00403207000503000d00007001d00c2c0c0000e4036500e1203814280f0510040c500c2080c0b91184041c813500820101d5008001a01e0448040c100e080710100c011400c01e450901c104660524040171008021092100c1c00403c44607052050b41c1d1b48140c030402c0f4002c940c4560960280b40e02410004400020920340b9a14541c0c00c00002030a0701016101d4200c080122494032404603254400402c4041e002120391041e4441070b82e0005400300544240390008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 260782760 1250 260781510 260781523
    0x2030411040506031608010c11071203081f08100b0f090f072105090d05120f070905101e050c0c15040e010e1f08100506040e0714030d03090203 63
    0xe8000c50303450002801c280e0301006103080350340d40841c00300200798942c402c19019240384035046001c10a1150b0380c03603a192000800d00304448071084040c1002640e664201c43e0100003400001481c2c4295810b0b464000e8072880c0c800c0240288401050f80b41e81220191080d02c0300007100c0d40c46021641c1100e083c68981c41c00d031960016003210024280e550314501594440550000324800007102181c50303086c40c01a61000e4094690f510807a5504410000d08903058454240c0171601c0a40c182c0100d6107000070110a0342c3c114a8504191444584030b001241a645440d40c45100003a50b194240c402c00800d40c0484000800038940b55103040100c69180d590380383c0e03144007031780510860700c14031000180b50400d4501030100d8070581c5c00c255030b50350a01d280e11081a5040c50203890405014410181004444d000b00c0f43c40f0b002070510030241960841c001d000c000c098503002925104035890448082c0b0565024081c0f206503440d03030103045410701d492301c4c0b505038021090610b070545203809a500010350 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 260784010 1250 260782760 260782793
    0x10e0d0914090403080a05040203250f0506040b180d06020c03031e0603070e0a02090d0308040c080a1a090a0803010b040314010605011e1704030c0201020607021b0f0d0f0c0513020304 80
    0x1007565111880400e00c0e0082f00a02c800c80309580e41c1d004480100844010b00440e806203540c46c0b00c240d11281003194620983c40f031401d4410b003c00c0b85500040d8815208010740c40000c2c0002000f03901d90311400e0590380003001040d200c0c0c00010820034400759229411200741c3c006584040981381420109079980a5402503001070959040082c81c0340003980c044540b5160043e0800c0c4850b0403502e0040e0828000703035000c549031210703100041180c200008100f118140c00c0040d90320303521851a01001c520320003408180300d6014155a00c000301d05000001c3d80200840c01c5210756681c6103040010b1800c504880180c0c40fa4140b240401541c0c0e40890410030340c821444100c070b038082c07000f4000d84601c0c0b0380c0c40b12500e140320740600704421304d0b40000030858183d000717030252511551107607000ca07110402c80055030719550002c03100585508101c0030245c0c2440029000320110b101684800c0c01076886280200c0e030380c1000c044280640e0528000384441120b90100c2582142466907400d551113618222 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 260785260 1250 260784010 260784031
    0xb07120c02100b030a08070c03020111010b0a090b03190305030a0b0409021e12060a020d0c0c0c03030809070305010e0a05070605040b090f0a09140a0b2e02010e0d091409040308 77
    0x104035900313079400c0c4869034106501070295943c0e0000c5c0c0ca0001c0c020a40780c0b1003039000c5488c0d00003030080b0b140107002d41050264014150800c080c103102d007100040c00a1a0b00580522036000c1d200780c0b002d01182940d142c0390003034035510380740d24105800170151501d010301b5500450808800ca8010380b1617540c012400c40401c28290404040140880d05480303a00c5c42000080c81060207200002c001130340208501070a84000b80825100e105090366100e85680780207007c04100042003001c41d00c1038031000c0d0040b880d001034038580c03556526103909549503064060020340185154108100b42002910001c0c5180d04041d1305280c5480702003806401040308041c0260440070945d200c550b1980c6004c40a0503c000701000550000901c5407020082200c0304a4a00c0c0b070811300d24003916180700107500ca1303043c80e00e14a44801da55400140a9081d42d8481800e541d00c99035031945040c070070702042805040c03907655802d00c240f0b0007140b01d0f60030103031005007030050304580c00784008284d10407d82540700c2c1c00e840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 260786510 1250 260785260 260785271
    0x91303080415020708040b0705060105060316030c020c040f0605030f0601081209010c020402190909180816050d020604052a061305031605041b020c090a11070b07120c0210 75
    0x100d41c50040c0c0302c0c3c180024441840010007003000c9900e40050103445022703001b1100281c1e265400d02c4910322050780e09004446042e03c81c281c0c1c1600c05d400115401d1203500c144d4020190240c0070a06842181c0800002d2944a65050000d81000c00051a00c000014001d00c201d500d40150f59071a80d403600640e280d1184001101c1c03a03903901510800d0302d8264083d108540c3c1d03407082c901051000c451000c1400014101c0c12001800d1500d0740209070142c406c030182411100c40c1940c0d20903561340100c011251442401d030f030b0340c400710301c0a00070b0707240d0120141c02901843c546890b11031b080c100329804072801c0b03644075a0500300c45c0b80c004034001030603141640c900d681c4100c0c00040c410754010b65440a64103210b50001c400c221a03c0e89411000c860040c3d609010381c1d2882003036a107003181d94a4500340143d0144541c444540741114019800003044040040c0c0082902d01c0b407a1242c0c0542c0b801d40740c12140c5403e03ca1710716807068141e44809620102042001140c1000070b4840200000d8050250b0b1642d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 260787760 1250 260786510 260786543
    0x10503070804030212070309170705010509130605031519050411011b0c0f0801181e1a09060f0108010912080901060503030c0c0424150e060c0601050913030804 70
    0x30049551210507071105c0e15244d8499182c010072030b00050160042e24074003801340841c80e5000003004420741c0c005071145410300c4541c1060000e0a18080c1c41406410b03200d150000d0345480074084448241c403e208408080c1c600704414070105120f102d407203e0300501c2c0108005c081841c1034203000740d4400034a04100c61004000b50368490781914100600f500c03050b030740c00103a04420b000c140011600014001c0c40f250034111a00c83c4003040f40d40340946078450f6104a085603200071650044076511030b440c2d680c4e550700c03031942a0191600c200c45010640e8003ca051280345916000082d00500c020002030044451a540c1c8402100c0395404010602150401041248000b0341010000e410b001d000c880d1903c040300800340d5202107004215000390b18006900389012404c4959122422107603808900d09450700d01c881c594013010524400800030429561991691800000d2080554103030017002e595051000b0482c0c4280c0c042d200044e8001d0608520000031381000500d94415041091489040d070701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 260789010 1250 260787760 260787763
    0x40b06150703030b180a090b130803060402030601180b0a080f06061204110d0804090c110319030906060b0903010510120305090f0a03030c0c09020421020d0816060e0c0105030708040302 81
    0x11720442050007802085400c440c958010000c99018141079000f54071054003981800d42c41a401400800b020030000310242007940041d43c2040c010325000c265051910303a2520361501d240c00c1000400d00000e42d4000007030b40041501d411105009500d0740c103051038000103005100f42442c8948183d00e0300001001c0c130203051104409184080d094465501036890400c05940c0315020b864804c52800c0f40340e42c0c0e014801c3c8001040e003130748480250b241c01c458961541c410181d00018004240c0c440d207000001402c00c2c06040014014024104d41702c400c80303802c060940350010050b000d2540040400c010403007541c520040c0075509070901c0b40d501d01c044d80118009203d0300304290b42050200d0000030405a000381886103103405480c69456461b203900c3c40300c041e88502d1042c0b0864041e0b11501c00450410396408821040c4000c1043c02c020f200c5648036082c40e0011041c941c500c8e40728200c404203005460055900b0540f0308400340c0341c0e2270402000a48175001c040c22500030007424200113004c0600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 260790260 1250 260789010 260789029
    0x4060f03060b0d0e010f050f0105010c0606080d0e0f090c04120501020d0203040b0906070903111003020903070602030a02071413021b0102180a1509090b19030506040b06150703030b 79
    0x101d829859034441d48051541c000c4c3c603d0340c4c00c100c42ca600e04915410400245e1040c1c5000d410011fa858041c0d910b020300440b4004c3d21484243c0e012507680070005800e520400040d00040c0492301d4144082804604222205840a224600500c01e610821100c980c0700b40c222421364114120304010301826003001402070048501c0500320910003c240014080c1d28002248614003940c2107601580d20648100c814104030312006000d22485001e104d5285845a026450804907280042c10200c2141c000391400308036a22480168000141c0a02c59680c184244405003144ad85004c031750f0303a00300000c0340b00c0c04102464058000c0d40030a84824245941100b4405010715000a64882d0b04001c2440c0f5158a5854041d20454a00310001841c0b000303829040050071044e01d82c1c820fa68a001005c001601a4071030440e401100642031940c03019404101d44080c40c010302c020701051419143c85141c2e510301a000511415000103081030076100c50341100d102d01e038035240108203402054003081c007464 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 260791366 1106 260790260 260790269
    0x307060605040633051908040204150b180301090b04060501050405010e150d11060c070e011e171905150601050f0a031107020a06170705090604060f0306 67
    0x100384440c00131041d10203040c9a860042e4601d2150490f50a014182020030081002d0001350308182c802c1440b007400009091a045090020803601405500034040d1010b0081100340c860ba2420f4014032055031307006102c158942454541f1a000d00310074001c0078022485c00000040410301740e5007003400785100034402c8136000b1401d000d2001c0d10015180580314a40311202c81103c6840e200e0044c0b068001e03010180114600b0000c0018044006a208200c11411400c51003080060b4551003812150030080104029075110b10039802c0c500601c400340e40c0c10384461103280c240000400e20b800c20486903a00b1003840e507541001520035000e000da243c500310500b400380803ca40d0080e03012054103a11b19116504003d1a540041c8c88007000360032420003e0403c045803985226009910750700b010280c107080d42044484000300326640628441c034010092034146121605000354000070103003 = true := by decide +kernel

theorem cover : BRFrame.Cov 260611510 260791366 := by
  have h0 := BRFrame.cov_init 260611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 260611510 ≤ n) (h2 : n < 260791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
