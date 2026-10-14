-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2897
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:41.297368+00:00
-- url     : https://prove2.me/submissions/dfb4e0fe-1820-49ae-a6fb-b8a8aad42935

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 520863309 ≤ n < 521043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 520864559 1250 520863309 520863331
    0xb160e01180f030803100e04031e0306050603090a1106041202040905011401030f0501050c0702130b030a0c08150a020f030c0703230406030c0c050601050609032b12061d 74
    0x648420b08104840d6140d4030031a4500408810712030130094801400010740400e52035690b035071800c0e403402042c419040f9450540180440c01c844c031118800d130041c4c0060710016003681c0e501d00f052200156140b8103030390140c4103010a00c48101641c0342c22400c5808441c0c0c03000000110a006808100040140c240d0440b41e940d80c0e450181d609405042880380294000d074101c441d008000e081c482d0a4402c0140a070341461000c20851300140c0d6011040121270b40b4207035002508520280220b86410101070015041c2c80e1541e500080c0c9170070000d2400740f41102c002340c40c1525120a0000c400340d001c0c0c00040c103085242800060000c00a45005d0440103000780382103110302544d0701e01688001c4070318062003ca00c000040c00d000c4145c26000320030204001e46010442980d05449403a120b04060044910446c0d00003059003181d902000070796044424104400312280d07050320900454282e182100c0c2c0840d80d00c0d248035400315110b104903c22203000585400c1d2052081d540400800c4e00140018050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 520865809 1250 520864559 520864607
    0xa09020f130807080708070e0406090812040b0a0b06040509070e13020a030501030b15030c0111030c01020d1407110c0904031101020a031e0605060403081b060f040b160e01 75
    0x400c80a0100304001c2002d80007a02e4043d003400d0125007810104d070000d41e01ea6010b4101006000404040558000d0300007a000924503142c2c82d01d0803043c400c180044152440e4042031109000f805407403136000d10704680d000c000c804c4000051220340c0c080c2e482041e40c0101d4503000242600c2c054041c0c4a401030000300081800082c4428190481e08202043c0340000e40d1400140100041540c107903820409006984404404510000740c1d60140d12746540d0410082d0200381149007020004d4035031000c0c0c0d03c0025500c545416001c14003c042d00058200061903030000301d2019401102ca01c446001201f01500c40d50780600107211413a00d000d042102000390b113441010540c00d00b88050840651550b40104140340440314001c01045045c4200b15468034003c0c0400c019920841140c6c110780e03100700c10325114400c0c102c00820070301400b01e01600c0f500071003041100000c4100c1e0030038429407242032071290a8031494491a06160344c0303031081d400304081c07160030215503000d0941407615614480d00c0600d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 520867059 1250 520865809 520865827
    0xa060509070809010f020705030702220204080a0b1b0a031104030606081006050a0819020a0e040503030117070e040308090f0319020118020a0b25030e01031a0a09020f 73
    0x3403510101c44560015002600b80f0104003c28000d908003814002e2040d4106911070320380f55101d11911000a2041400a19006065213007049882d140c40403220215200c65a6502c0d0075211204c0c0d0108903516134854000034002025040000070031071203400075074200300c00c460054000340070b290a1200038070814400040001c4c0b0600032103029044800142100c05129125842a04e41603000207124803011101800154400602040400501c0b07036094100b00076400440c01c00d40c115044005141036040c100414030a001000750304a500588507190a8519204031545811180c01a00c16615000f80032901207407040c12816006205642501c2001c0c0042c4032182c6981d10400d480a05291401c01c0400d01c0c90302032007003c0d0403140342d003070a80c001150b55000444400143c0614070054402090350344207022409030f0140720854061444611800302d08010744003c107290b500318001382c01c00b1742c00e144000c80807010918080000e014003101505048044001e504144c410a162038414068560 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 520868309 1250 520867059 520867069
    0x10212010b130503100e15061e060904061d010e040c050909010b0904030216050108010f0b030c0c060108030306040b03031606050c250203010e06190b0d0f0c0533030a0605 75
    0x56012105a0001200c058a0300c40324140241044008850600b250420400742c527a245040d03900d500420350300f000540103c2c0098034500030b640700150800e140803404543e07000c619022030304101d1501000c91150307907540001c0000c500c0071900207080e4103085604005034180645000c3d00070842c58000b003041741c0602c0100f40110001c540070b80040c1e010140b4001c8446240101d040506020b02c0c0481c002c1d81000d039045111402c92007603081d0f1000c000f000a4440c418601030300c001281b508241c0310b1341e5070343e021542e0340c0e9041034400034420351503d00c440031540b4000044030044c44201d42914100442d0f9100c202c000c0c03e0040c401c9a840800b0420140315441008511042c2c0054010841c03000c0f9942c010305003119091482034071141d100006200341144609902249680000e10204000190b1000f04243e80381c1108014031a5841920380340410149500402c01d0b01d8050341c01e09030f03210118409000032844907101c40b00c0c802d20302c20304c440c0d15030100c1e0003940d2000619402189003a80ea401180c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 520869559 1250 520868309 520868323
    0x2061201050f01030b1c080f040f18060e073002030103060b0d02012a080301080d03111801030e01020c15040c0f15120608010f0914010212010b130503 66
    0x2100860020014880340c540520058100781c0700386020007107542d240d004141042c480c81545802c0703000c0d841c45881004203003011a004030750429403007900c41d40d69290068044812303000740071720300071450307061400042148180e808903154480403154a403180c00058030580504014080c045103642903815101801502c105240c0079a920016903079031460030075200325400303c258a4440d186540382c1601507030b40401089160702030b00110802601c8a2800560600c41c0030364010900540840002007a010104140c1500025a1800d000b1200c400ba130076144c600c903003c003603850400145207840d41035120b0392000302103c460f500014a4480410035141c40d100e00c0c0600e00c03d80240d114100003c11100d8800900100701000821410b14180140580301d02c9202080301c04121030480e091500080d15046070004202c010000c11040c58440c4d5200094101c4403800d80d002c106041d0030385144203052088950f205418100030b0307460307428800c0003445580041e204824a030700051001c04d0656080c8221 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 520870809 1250 520869559 520869577
    0xd020d03050f09030405090a021303030906020d0f0503070f03020f0f071401050f0c07060b10020610240507020a0305010c080115020f12130f17060606270604030206 72
    0x10021150010001019581c006050a4428118909000402038000b003030302c041c0c0d24101c819190b40da0326040d02400034000d200200d010100b03150000001c4c9500552980280c0700c15a094076041343c0d020078103450800720300760320400240f001c00002d10001c1c42055440d402c141180350252030f1048611442c580c540054040d802240b400050003405c100d80c07440d1051070300002300024040c6250188446081d04c0e40103041030540c07200054240100000c0741c0c002003d041004003e130b21a001003060003507442004a0700d40c0844184101c0114070080d00a01070800214440ba01c06da090b01d0741a000c50301600015000c980140c065140400029000c0c040c1c4512022507036a411030a41c5805280c0340709c0317607000c40400155041403030000c07154800410750300c0684c100320144581d6105a4421100541500e92004a202c0c0c600340f00420340e00c80c080c6107030071482202c5044038410703220441044101c0c40344210315031031100140202165403589003460541c071b490040185040a65030740110b00c481d4003a10750 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 520872059 1250 520870809 520870813
    0xf130504060c0e270c09060304030903030e01110604140109200109091a012d0e03060f2208121305010e03031b031b07050a0c050613140a080d02 63
    0x90b1140c0d198841115403107410b0480300012200c0703514103d004030102c140140c1070b80b840c0000002c2d1038941200203d41c0c01590180c0640d64a103450f007002483c008140c04101c00080c0445000b034003962148a904100d444002c002e07001c0c949440d51001942d00852a103424295210b05104010940c441600e40a203940104c82082840060380010501c0c45c01c1d0300180800e070725196924403001c0015a01e1a802d0030282800d412142500c0c0007440b1302d00c0ba03210602070303e0400d14105110194440301da40e07608041541100c8258451040f12121904120380c488000038280e01c00c081003400d02c9044402990068088501c1c14903c0c0309541000c00080340d48804601400d640b4a042280900c41e4009024442d4003541c00d40c20a03469120f8940e1005504100c07540c4044042085c0701c0e16900c2c9482041040d41c00349681d00181d1420039110540b611083e9000400c4460015030303420104101c03030300c590b0190000d242c42410b0983c402d0100d185403102c0c80d008a0406c0300441d240d0340400c14241400041c0d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 520873309 1250 520872059 520872071
    0xe030f030a02160801020406050d021305030d09140907050901050f070210080702100b03120913060e0619030201120e0c09190e0304030206070b040512070c1a0304050c0f13050406 78
    0x488003500f0320503521144050388100000c0141a5201050340c1c1803250556002d0baa62440ca001c8501505080c1c11aa81c14012a413040480300d41000c28041142d00180c1d002201080960400581490443d078040c00306c0d00800008a0b99841100100740c01101a00854100707102c9802051b003a02441f0500004030340c0400a100d403264040040c50340300b51240006000d02552032000c01d444a82c044c030101b50714140440d02d02003c4d92402e00783e040c040540401045420f5550b00c0c4071055034020f8032900d01802211345c42c542d520f05d41c81c1102058070380603100c000d072054031418a50010200720b074030002e060203500c1d500200b60307548900140c002d08520b10000c43c00712940f03815104840e0102d5404c142340d84200402c0006031640d5080e01c0c0c40075000000c1d0695541c1d942407650500900d00501c514010001820004000400c0810810b03251400c440b54061005000c04030524401682c02901540c880344d40540d952420b800300802039000a042d00c480008000c042600340c41064604454082e2566 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 520874559 1250 520873309 520873333
    0x908010e0303012d0314210910110304050f0d15090b060a08060f0a060812130e04111002030903030d0203160c030c060f111c060603110a0e030f030a02 66
    0x480318001304403804650001d04201348071500d481e910b44001030258841802d00030403108180410208207020b0b01e4400b0071518a1102d6214a80c400b654103031080b513012260590300c1e88a03c004010201c034000081d85030900f0601000640300540700000d178001d88032101e410009800a01d6a842d0700750060004c00e49466602e0700e0090080d0080505008141700e0804112030100000d006801030030352400d0700007a850728224200509102d4105000510031500500e9011008400912000c10701603645410380340c80304141c40c02c00100751070182140b10b020b01c4030704103072800b10a100030501450040301e103440c1c000c10209085030820151100940d40c08810860914100041985000c140340b8085140740300d550740c0984100c03c8008040c01c080da41e5001c441503688154884400507004400190301d801d440d03020805809210001d141141f42040800144a402030041840521100c04418105101c0031011605004d20841156051141580c0285c1e0075005000511042039654098002a0852 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 520875809 1250 520874559 520874579
    0xa0f180501020921070302040f061703040e01090b0d1203090c170601080c0303070b090703171801141603030609050405060915040c0614133c050108070908010e030301 73
    0x100e880210361205500c20305130210001c2814000e40350304079000a0039a003124411002803074580c00c01c61903483d032a442180107038030000181048038400f0701c0d007107021b81c2c840949200f07403144d09d125250049500d2600d200056803261111594107002e00d0009024003a03600d4074110040a44c0c01015525400c0c0d003050903582061140a01400d4030300000c101d150b42d501c000c43c0c0e69115407103000c0c0c005000800480e01c0e50006001182c01150480c6400b1101150b040c494103159024040c00c890703240c2d05541c031041c6940580050483c80c0480c0c81410b081c41c04401d0000ba240500081c1141016914200072403011021310a0500950141d0700401e094540060607600e00289074506040041c6220200070005290560b100141e81e1540f40c940c00c0d54100c02154400c0d80540c1c11442c00c0381c034410750007040d6400007020507900303814078200c240200c1e0080c055041c4003c441c40307108160b1141d40902070050b540140180d541000701d070700e002000a69208001421a00b61350741d010520b800c008010080c0e83c80c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 520877059 1250 520875809 520875829
    0x6030b040e010209090609100312031d0606010905040c05160606060f09030b0105043909060e0607080912030403060c1701080606460e040305030a0f1805010209 70
    0x1940700071440c0c50000d00000383c000c10001e000510030a5038a0000707541c2024610220011a804951135090f160000b0b0090041d0240100c0c480030f0740c2d03880c0004084000005100360154106841d05c814060801e010701026002a83c4000b060060801107650702c104901d0011440e24040d0300e00203030080c1007000c002c000f112101556010803901c034403b030022510702460070341187c40480300083e091280900c0110000301b5280c00300c0e44504a503900c5d01c41c00c50080c40c41c01c08c2008690f0388108058848109170f400400c080840754012005100c0000000c450a005003c4203400404c000c1c178160b00700030b1861947e1710541044030700a440e142030000880e00803c00c0c00c1208542d04201c841c641c10030300180d41d1071500400c0103214101c0b4002172480d60032509103588094a00c2c4081c0e44808001c001c1d44404846540c401441c80740b40c04070300080c3c00300703804101802164551b50721071a6881d0342d25440050000041d00c030b01055501c0c1c2142510b00e10380d0400c00ca4251145001603111000c1c01c003000b0703031115 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 520878309 1250 520877059 520877081
    0x20c0a141b06181c060906050a0216060e1c05070b0901020a0e0607021909020c0c030307020a032d0b010608070e310c03140a0b0102071202060d0606030b04 68
    0xd9807203840c000c0c1c1d540d2805546081800141c0740e10503600f103000141d110035858070343d81201c4226030500c0040c05029080304d100d80e030240409210945550001030f04138450461180c018292103c071020001c1e0490b08200e07482042c51307040311070800f43c20400d00307210600400064046a400070b034003420041084291507001c9440d600031400c06001e03c201401007940400104e00c40d084c0050814215aa10360301f6802d8004038030714072a50961140d020b01d00039031000107440e5003482401d071808080d1600104640b0102c2d405484001e0b82071a5503200c03002c50001018544448a80008903100d6a1030400c03004081405503459103115490040c01410701c01000c0c2103030f01009801c1c41d031844a500d03100c00580e240003d0006c40000d1115240d40801c401c0602c4080c0003810f03040c41c0e000034155525802000d034101e181501525541c485031141e01c2203800c00204540507811560081180707611700c1940c2c075001c0d40003502061401d8603060007602101d00300d0f0881400300303a0700c0c001d404041c1414416981024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 520879559 1250 520878309 520878343
    0x204080d0c05060907080c13021b03040501020708070b070602090117041a071106160c08070b0402150c0703060c120c200d050d09111807031503021e04020c0a14 70
    0x5e400c065043e6100c080d0741031914082c15101400390807a5119074111811071098000b5250702084001d08107031654002e100d00c0703005200f1aa004142a44081900b1086412480ea02c0e403a00c3d40715a242400f0350814281c4a0510140e04013580005d04c140185501c207600c561044038448003210b0200b00340100140c100800c001e502180c600c42c001c1b00086441c0c0000d03c11645414280c220b5508550303040c80004020119200443e00c4400c008100f00f405000318030844460f1002c00a01c50301c4200ea0150b00f140403401d0307111900030808140c0551011040c0221171403c8120382190511243c00e03110000f41200004081c0c01e4010102d41c0c41c030f1103a500100070034020b4101244001c1c002000c0340260010104002d036900e07482c00400405085e86844000041c002160960424107031240701c500407a00c1c41c0c040703400d00480c941c1016400e8080c105a0fa070080c080e0079100c866a00c010b400704c41c420183c0703820907420801c0c3e6140520030004075084a00c00d0001143c1903103202115810402d852000307451314 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 520880809 1250 520879559 520879573
    0xa1115010302090f0a23010e0a09120e0109050a080f06011a0d051503010c02061f0338090f010e0303010806072601090207020414070206010611010204080d0c050609 72
    0x681e0354080c540e030004504c561214040d210000c89600034040c503d0380221070305503011a41c410390a190540c03030407a0b41c21444a11b940d0b60b84d402400c15180e5011009014210201e03400d18a54060046c48248032418540407140359200c00201d002129590080103907507110466880e045681041802c3c05446a450200065292103041c00c00b00d00880050b0038800d0b45600025a1a10052107800c4030040b000700244800442184065200c217400d50345444541c107000d10202402c0002100361048a51116014100060001560021598000d041d050200394a216000001501c0c80428012a411005400c1d10010011041d084840b00d840c5c81960340c0051004204a03e00442c095600803600c2c1400c02000781040c020124100c1071a82d5200030035224400070500305a1a0301521005100b41d404012690046180c140c1c03802e0b0881c0c0c0300300181d0050006001c550b102c0d0000c20400d40c0c8400000d03042c540c130b030382c030170350a1040342062031000426003801c52045c000f00b00081608000402c02903d49 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 520882059 1250 520880809 520880813
    0x100801180c0b0c0109050105040c0e0c0403170f0c0a083c0309030c0a030f080702060405070b13050a1401030501050a08031801050d05040b0103051015140a08030a11150103 75
    0x980703401407094071180000840e4281c0da00740c0a410088901d54000c000704043e180900c0e150700e000e80c46010f03000c4941c00040000b01e062001c0011501640e410088044022260414007519a482010045581002481202c14121081000664662180400766160040400c031824200e400d021140c001c60501f840840c00c40e4507a1071210301038407a00740b0840e43c80d542c0090b11480c600c81c091900c0d070244144100401171540c0000b0240806e1011b1fa90306100c0d44079104100d945141c1a9805406508441c2e41040001365020090040e04003200d89070141d10755610014464080725400003110359a04100c00c0155139061140d42d015203011550170080710305004039156207000e480c0b400c001030600541c0105103a8020010785422080d041c506119501d040d02e041c3c2c01e01d200a1008403078511a44507600a445800d00840704141c0304030003940da8042c58182014411503104a4403604065100360128202905000411002e580b40d1680030090714215002031411b90005031b131041c0c1c00b1603a801480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 520883309 1250 520882059 520882073
    0x201060303050708070f0b0a05011406120f04151a040b040e030a0f050f190f0f0c08070812070807140a0e060d1e0b0f0901050a121a10080118 62
    0x10000f03030014a81341e219412441c03c8a22005545c0004e45120307d04000c000f0105116040b4034183c840e040b0b04150200c003107000740f00c07850181d03010581c9146d001c0030001e00e03c3d1140b403200c3e55105001e000c2c03201c007000d0450200c1d02200d011010300c80034805083c00d1040b00f414240a0320750700010a0341c04120340c40c600e0101503202e0144866201c00c010000034110555881103054480f01d0000c0c3e2402c554480340c1c004854000000050883d000c1456898030b2144070740101740e05504040d03075440c1d07407040c500b0666645042d68402c0300129602d007000d000101d50300d080702d240144500000e444950aa06040c00702510303c401803100c900640108111002ca00f6501c130000300c80b208425a91079803075000790030201c80908000141c4030140100d070600903c46002c203400400301c4000669041c1c0106c5025014041c2d00c0d030090003030681011046000304900b241d4070715a48400381c0207171044820551540b561410f4100285c581e00280c440c5c0c0f11041c04044028810f440c801c410103062240003214035621a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 520884559 1250 520883309 520883317
    0x1d01050f0a030f06121e2001030f0c110f01050411090a0e0f0c01030b060301052b050a080304020a090c09060f0522030605010608091b0a050925020106030305 69
    0x212000340c0070a010040c140240c000580d0300004210038002c00d5141c604640034480890710548010984543c072980070100e80b4a52001c6031b8000c4445c0c100c4050300c60100b0310381c9050f4440d01e0304040d03440000120406c824030449010440aa5a080c0e0b0311081200403417401000b802c90b00c030742c0c4c0d00d44070500c00000c0103880741484802095403071a41590b03a081d544001041132540b98940b50007016615081090042400c800268090700e0801010f28800c041c07100c035000034082c43d90480803400c40310b086401d03a0074520640300c0d4402d2081c45a0340e400d5171410304201280c030040720204000300500c011480d00e880904040c00e42c8400803c0181d4145000410303881203072040720240b2000e441404000e0780f0840480d42d14800000d501c201c00c0f0050b00e46980c0c0030402d4803003611001c0c0f0344400429860300c5586d0f018000c00102005024800003064241d20061500c00650360181020000150a840380c0c02c1075480741000c03218081c2d010401e01406128070000c14800360469141503010310010f5044404c1c2c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 520885809 1250 520884559 520884577
    0x140711030d1416030905060c010501050a080c0a05060906250201021002070209070c02130c12060503010203010e010b1c0f05040b0f2a0d0204031b0605090f040c090306021305011d0105 80
    0x83e03510811141000d450303444103600090380001000407600c00980c41500402d0407100141c40e020030890ba103d00081d00c0d542191039080e072203107030a08100058900302d4003801178090700804151402e0184404031000c280a80c090015840d00d24016106540c2c05100c0400941c115007015458450150300095034840002d00c40001e204a0b4440c06040d901c42c2d00f88402030080c1d0782800c003d4540c68140241c03055261059800302c15045c0680420241818025030b412911220341c440102c0c0d0038016014926040840b0305144802d09041c4000c205034240204040e0603070040c000078007428142042180d00740010052480c2111110901248040303140c41e02c3d6480000440031380703180078035042064140c400c0a8030402002d0001c507000c400c0c000c006000c00d541c0b5200207410800d1a030348486c10703a10307401045892540501c0e0341c1d40e00051810f1540005115080760300e840600c10b030302d0780c0d1030804a8102038140035031002003c0e070910055801c001c1d2003030390b0303842c0f0103103e020488514002801445040d0035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 520887059 1250 520885809 520885837
    0x1809060b03180c030f01090b0603030a200a05010203010905041a0105030d12022107020706170a02090118240201021608070203120a02061e040201020d0f140711030d14 73
    0x8401e1940c1c0007404a0b10400780c004003905c03640725014410034087d1141543c00d403103a001c0c00002c110540303800404c8907110011343d04e511411200c941000460714014421170015801040d00c41c0c00050000c1c03006502030703c10750384001603600303041c2040302600561290113003031000342c0401409170b0780e800500405090030702d150052803c0344002c40c1384082c4c01941c00500c00e01145892100c1d04038072440d0018441e1f016507003220f821075500d050132500d16001a100d0705110740314401080e99407282d90010420020103040c01d80080f4070348a0003140301e407200d030322a20342c8910050300704501d07000d00d04866001e10701a100a50800c4000110780d0104404a04018100d00001503c130301151009d200c1c4003608141100300039221444200080e4913400c00300e5500c02c102ca0400400007210600c000031074022a01a0300804096018000998105440008100a118070100b5800048480320001e00c0541e10509044070b01c015100207061030812818507440c01d01c20038140d00d5294900c00c100380c0f4000501240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 520888309 1250 520887059 520887091
    0x210061e0b0307050c030c030403051515010e0a0e2401030603050c0f03120301060f091d04020904060e0703030513081f0203060123031015120510151809060b03 70
    0x40c0c405105d0420300712002d01020400e101002c102201400489014200751015000990b801800b00300c0704640d6400d4200920005080d594490003c550420754080c0331800d0040e12203410300d030456401c45095240c80407030422403454402541c00380707224410a00b020700031181103a42d03103915800400c800501880020421070843e980802042d40c070025000720842e500e50310798500414071081051214003040200000064041d52840040c22699080c81003184d90380300e91b400c2241c002c6014000707540310794a914400e5403031a004d000080085200303443d107941c2d5100d80103400d480795000740d0004100da0482c5c3c00c04441c6050040742d000c0010040000160750703585107001a40c21400e070320a00707007954010009041f040d030820001540100303034001031044c05540d92011044080d840040c40c000040d01d1440c078007204200c6411150b0006088850003510741c0c1c8421402170300750b018402a900050160a8280010020f000750300d0182000b5074042c04510b040298112661102400d003550700c0700184 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 520889559 1250 520888309 520888321
    0xe010509030c09040c06030e0d0c062f09041a09010303050f0c06181902100315330201050408040302090618040503030a11090306070c0c150210061e0b03 67
    0x11144000450b00104002c106003801c1c14100350366a154043c4802080ca031042c1d0404c0c0c000000f0f4008440302030380c0d444d668040b18542e10701000d808030341c03600240100140a080341955848540e4404114031019460302d9007042c008200c10750301600b000c41010600b042d0640416241c0f14240c9054a805007003542d40c0d07282c01d04400301e19208240c80c10f1000c0c0180d60034020f98600c2c4400308000c0001001c102c5100d9518160030102c030303000c1c03070700000d51280c2180c00c03103400309000e86c02c0b806484003103640000d00c940d664500025840101407998800407a030b085440201750450f00b4001680240740b008000d0b82c1b4250340d803030f20325100e2800081c1c418581c1c40300003003541d6100c016400d04a501e0103c407058500b000d19001d942c0303800c26107e01610700d040036411100900c03540250360042400400a00d0703281c407410030a4a100c00035400a0b211903486000100702a103d40c065502e802c16030f54000e100382e10000c0121002ca81058004c26000001c00644500f0300403030f400c41600740c03258032070241d43c7c6c0e8480c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 520890809 1250 520889559 520889563
    0x10020703060c08180d08220203010509100606021629270118170c060c0f010c050418050907090c0215011a1b0a0c080d09080d0e01050903 60
    0x256000070312042c180440c80940e075500c0a406401910341c100720040714502d01c10081c2d114050340640d03200107000c5000103595042e600c40f00c0000040b4460300c08640d200c540e00424203484044540514540c804040c104074000c0c3c600c41c0038018141c0d88054540078200380c440c42a061640e2091002946d07801060b400c40354194a4019171003400c0e0140d055940804180c001a400103000c0c01004c8180c0044034203040c1c2d4002c0b025803121901c0f041c01c0d100c0c00da0501242c80c0c100b52901ea40005c841c402c04202d401241c031044010100e1814400c0200000120722000c00c2c25258180ca248040180a110800480046003d81c1e08032042c1e400000c40c03a82e850354007080c0307803921542c012101c1605100c0003042c4a900030458590440c5803044c1c98801c1d80e00c4400500c02d280803d4040c81d480b031400c1080e01c111942d0071402c20340704031526040d54111055074450300040b03501500315907150b0304903c100620494002c240c82004040351009004050b98000f8060011245a40c10605008000070400196582 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 520892059 1250 520890809 520890823
    0x203030405040c1e030c051e190513050d080307050c1f02070b01050a0308070f05010f0f020c0d080c25020d060b030f0f0714060904090501290f1002 65
    0x202500803c01024083c2c2c004202c0c0e640c452041204082141d82000128403e0050210605868541a14001540d1540854481c94000001340c2c42000e014000c11504500d402c80c806203503a0b5170b9541c4526049003080442541940114840d1908c030710072000290010b8150386e48807501c0d00301a5190701e01d042c800c81c2401d2026004030b5100340c441c0541c0c0b25001d600c0c1c6c060183d0307a018101c85109a038992003400520415800003402c1c130041840201c0c0050180010180032620074000810304010000c0140242d0f40d0101001e485142c0120302c104c8190410032011139000b0b440c0c509201d00d42051188030f6041e00c2070a00c00110203a5450701c601030700c145403105a450a601034400d201505e8203080c20402002c040840d54402d01904046141040c0c0004102c0c0c01134292101403e441490003e80c40c0f56040300314505074100c441130011031050f030303103900c5441c908901402c000b00d00b145541900e9440300d580c1440325899541c51880c003030040d40381c41240319524502507a400a04050f660350907407074918 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 520893309 1250 520892059 520892069
    0x3090a050604061a040b031c090801060603091a1b0904020c1207030306061707050915070f020a0504140a050402041e1a0109030308150f03010e0c120c13020702030304 73
    0x100c1c10040c4401c1268692001c1028000c0000440c4013021820800c026518500c16880e4540c1c1302207041003c98402500031032560680d81400e403c0d103075407008500c1c259480f0354000c2d00403c0d0386d801010306000742d1030304c141e10301c6404035440306070362400f505407040151a01d65000c0b400d0707001148401c550f031901e6045a5810380c2007006c84142c000c4800400d8000d44c44590300701c0c0003030300705040003a1050103241c01c8524040681259030650343c9010044500341c000c0908250f0101148010b00343d10000b4000803c03031640200c07040c05003000c150051006809440d48510300642c82d05925120304142408043d80086900c900420313240c42c0d42c000203000c0e110f0240500300b603002809107004809040d5100392503007042c4001c103800d000702420054404c0c80841c84050f01290352000000c2c134042110302d200d8040c140c01011001340c203880002103030841e00e030140c501001d5031040745460001d103041c03a180041c8900c030000800401003c1b001041111115120391003400ea0049001c04c21581c091040e40c4c00b900c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 520894559 1250 520893309 520893313
    0xc2c121204140109080d0f0318030f0314090c360f0109090f032001020a020f060a0605010e0904260d0b01091512020706020a030e1209010c030503090a05 67
    0x44a88406840980e100b8401c911948280c09405002c075401480c1c04401c1710313841c1000e40003c070a13007801510110800c400290416540f210704081005100144c805801d02a503612000030f01920302c0581100c602c100c1020b01810709000308000401c0004001544910a84100944110001c8200030810141404072008400c07054544510700144c07001070702c1016080b01c07051650f6038900803602111003d100c0a858101201c01d1040401e0041c02d11408158201c1c59030f2101140d034101e1103007240c00039010f660042c1c01400382800700b002c0802c0559003060941c802001800c0c5860000703000c611050340c409008006c0c050000b0b003400502e02444030004003c40f04c5041e828401551030480780c7c08500144c0038140b40c10307884800395105070700550540c0c5d4008962040d1038200d0800340c50f0a07081c0c801c40d0703040f59020030200c40094540d00161170300701010f4178041104c0b08601c0909040c802c514207903456441080c070001d64640e0f44006a54401901803c21036644d8035041c01950416400d058058014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 520895809 1250 520894559 520894573
    0x1e031b060b360408160303061712120c0423010f0e03060a02030621070509070c12081b0a09170c0a0512010b0d12030c2c12 54
    0x120000e034124203051681114611840d0310407242c5807481d401c1d80c2e5034401142c00902032400500100c044a250814050086a414034074444000508a084030408800203a142da1040000c0050401c40e92200102900a0b0003849c0a8003000303409405400c0705440e0b41050701c004a0490f41140d4202c0c0d0103803250901b0103000c1d0403000c030b90000340011104083d0004150b200f012403441d200e0380c1d1a100c001c070001c001d4051601c403280e8000c00b94101034542c90707000c1c0c3c20039001031501d04195407008841754984058003183d0b140c41c0c1085001000101000c082c0800d030b40a00c0d00080002c1ca10300c6034010300d814084400d883e000e44103500980031030101c1306400400075260004580120302c01c411604055042c940d00b0010828440d00c540c0c000c03052941004000900340550729201401c82c54645241b000012000700307000010f089003011001c241c952040c140c01c5078604643c580544002000c0c01d04008480e44074880d8007a026100e62404c15810321646101d83c8000e541b4802c00080d40f08200b0211041c2c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 520897059 1250 520895809 520895813
    0x5120a0627081201050405090a03032d061a090303040303030c0210140a0c0302192613030f020601031707030210020301140112110304030c0f0204020a0c060c03091e031b 74
    0x11992141607000f2044980d1000041c2900e8103014a034410050b540180820410a94007500940f040101034080500150000144620b5441d04070f0180c04002c0008160b0034641100800f440100401d07180381c00204114500c90307038400108503400c51b681490000394034100c1c00340403803c100001043e043e11a09015500461500c841e400030301404008004202d5164802c80c154100d10a184c0c83e10270100b02c85400140580c01200008944540f00c106401002c0c9140c10307050708010100c620707005054440000d03009055114000001c0900140004e01c40c40d410b40d180d0090943c6007500713032494000001810f900b014400c0c031858040d480c0e440300644d26543c41e44e010307242e044c8007035100c04c2c0003454858182039505d0560240c03074408110b07442c400e45552141e4800700d0300d20380c1d4400180c803c00544d05091005032528070061818880c01e40e40e42030710705075038a0410700b543c0200260328100b5080186800200301d0080c01020300c002e142040c220051418a030660318060040fa40b4a1910a4001400e003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 520898309 1250 520897059 520897073
    0xc080d0c111009090b040615110712051504030216080c03120f0f031f080d12020702090106050d0603020301060b0a020f0d05040614040b0a031505120a0627 68
    0x508288500d9048004003a00414070500b40d8202242c100040c6020700200b0030b088550b071004080d000058404203031070344c0301e12102c0b00c19013080034440002140100048802d440500c6400042c0410300030031400700aa640340c150383d91600e640010042086000401c00b0140200101580600500310246416a84d03520741520f0301803040b4038a00034000d444000c0344218158040320701d03160058100a003003030300c1a80400c10f26000141034030400c0005032246002030081140c0c850007012804010031000900c10001060f410020b0500d0144034014018030340180e540e96900c40c1907403180c0c9080c03030300e41850b5425000507003026031001c2d401d0f501e80480451b0410340134000740f4042c0c0e900c1d02150381c07084240c1c10080d907030040d0140c80700000d1300500c018020240318552401c113641d07480381a9800d01c3d865100d141d5182d8000488100480e0ba1081842020310140f4001d400420040320601844500c0d00545520b4980001c40200b501366507184d150020083c00104800c2c90380600001500c1190078035002c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 520899559 1250 520898309 520898327
    0xd050403060257060a0c0c0506090f011515030b0f1c0b1006090b0313060203011716050a0905100f0e0406180804060f0905040c02010c080c07080708070c080d 69
    0x70043c0c4010f070420b00300d21100c1c4840040000308180c0286440da507400071a500a00310b004901c4204019828107070042102005007034000c400741c2c00035145120200007480d0850710148290841040c1110b010003000807210045000e030155400c0205090820340c00040d050a0340303160080c0c1c010b051070030003595030600c02d0b4100280b612402040125444924175030b803141e03034280302e25000070347c9002c014041c44010364051504580c02d1800c2c0b1070b03400306658900d016078000b44c00c4265220034841682111140030004528a02c0305249035114650a190101d00442040e000e200e225070340312400301c2e0072120004441001009200c000b509029110022404001801daa050b00e00c0b60030b003450385850203260b005038448998003550403440c1c0f0385032038000e840d20740325500d4030820321007000400680360720f85001d0b43e40c1980c01d0394000030380050f035034070068034000016200ca0302d40c01c020f00244000400d140300700d40c3da064008800300c7d1075500d40c0c40c245d00c1d6405541c00c0110f0300d01441c50040c120ec0e421405070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 520900809 1250 520899559 520899667
    0x6190e09242b02190b090d11090103200a18150302031009140105070c0f08090a06050405100801050a1403030c01110706050106050307080a0513080316110d0504030602 73
    0x6032100c0d003200313071642414482600495401007410015007205141003400c020039544540461a440034500c5d0004140c1364003644107171b58405010a02c00812080c5412140b8949811510001e003541845001c0b401602204112044c0d1136941250b000880581c00383e038002154001c0440300c0702503410007034401504556408940b5811000c008401c034180600505201c0da440c1e90783c50410a0741038840407a070982a035820303150344004220510040d1034650084016117034a444090303036640742409110b1100c80e840c2c2101c1c100310f4200014083c1c0d039a0b03480c51004a91442404142001c800c400081c110b20071841c41140760f61a01070860300ba099008082c00b50780c0e004200c200050703070780c0360400d840303500c0304483c0900003440003c0019201c84843d17000c50740000d00d054000441311015030f24111168000d9400d0403004084e0040c1006051b070290715101d02d0a15a0050720201110391000791090089010050105402040660b1442c90308030600380f180c03000c07030500c269450686070244d0510a01c0400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 520902059 1250 520900809 520900819
    0x150909051507091d0406092001080c07021e150d05011401170612070f1212020705060a0c080f0f09041103071b05070506190e09242b02 59
    0x1408503070140404034101c4560000804c00030f058a0614000c29400034422030f07800c4d0b900d005200100d02500e04498004110104c0c207180d001c07001c0d0001d0b01c080c0c001014200d82030410000440103031150480b40039010f44544c0c450040180c0d4400068a07240e07172002c0103404400100c1d08642d8985960480d038125511502c07040700ca150680c004590020a00d40000502c00d404004a1203e0400841000880b0700c0b0301d05031841c050b01c3c2d00c44504000c0c01c940c00070840201d001505018002c5441d0b18180003d500e0004103541071030600414010300600030580244840111003a040c8503a410840e400c281d808400b15035903001003075021000d50004850180a1447c000050840040b407a00311780c059810707600d4103500c2903894a506602483c0404080b506e40c0035802001840d82c40b100f0103000d212054012a02076003240070b01c0100302c245140b400600c40c101100901c011583d46160001001a02140ca83d03844090364020540149150480c6503841d4a110114260003000101ca000d06074800c4030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 520903309 1250 520902059 520902061
    0x60f0106081308120a0902130204060305010806090715271508060a05040e01020403020603100e0705070807030e012105100509040507050d15020708090f040c02060a1509090515 77
    0x224500716140c4000181504410080c0c49070480080c101180d001d05d2220700401e40180c0c1d9404070301c4044d10080d04051294010400780811501030003110302410002004000d6807404c0036402c0d9413400d441c1302e00d00400781d40c014125429882124a0700a840600010840031182da000540c0c00c91094410042002007c000d0302580d01c1c828011107002d144001d1007070f18000e0800c0c0400000303203140ea8444030151341c00c000001c0180c55900c007a501c80c0b14014450b42900d0315013200184403d1005289008110040107050000341e0380200b60b814841d058904002d4580c82d6000603039507141d01a00c02d420a07102c89040080080d00e40c0c000610521802240c1312100c1c7e42c61040c8000071001b59030052091308040350901290030502c0302131042070b0003030714030603000c02c00c0f03812002c00c9a00011050b50011000078090101d802e04014104000c7d000784c030b0801920455001c02515018040c000340490f60300d403070035010b240c40075a81c0070707000d444410740400c4408a10310302142d844908240c01310400003010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 520904559 1250 520903309 520903321
    0x5070f0e13050601180e010e0609010b06031009050a0204090e010902030d111011040e150102060f0609060d140d0509090c0304080d1515020312150f09060d05060f010608 74
    0x410024001c9602ca8001c0c030b02c0d41d003070200c0d803034a20034000301400303901d0b56405640317001550074000e01905450007000381c25036081c802d00c420700f5100360100e1740340200001c02c02d012080804c00e9100048074080c5000090507101d088060011b442190704c80c40c1d81e00d00b1300b5203441c0c9103641075000104151080301200c0c0304c0c000c007a41c1580c454144d111996056001004c015a080c0c80540101182c0c1c1030b4040840d00c0c00361a0364090190f240181c0b041c500340d50b000710488409580412034031340c00c003030a0343c0aa05989005c40000304c030f00c0d000900c46070280d2034007420002000314404603c0313a295912800c0d0b0f0300c80c040f00c0c44001c00343d4010450a070300c205440300102d800c600c18001140c0c0140e800214540c034003a8008400c00241c4165408240a21011000040e1208012080e003038055070581c051a9030b0300e011502c02541640c0a07002c0c2c00d07403841c0f60741c8198140e40c40d8136042c021344030309481602140d40c40500040c07460b410100041c3c80c50040300108080040b07106484d6050341c01030780f2200c090307803184 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 520905809 1250 520904559 520904581
    0xa060f06020a060b03010207020a081011190e040f0f230c0322020a0603020a0e0306070519050d020f070c12080a030b2202090a0b0c060705070f05070f0e 67
    0x94850180940c10a03026040810a903400006868101030000340c507159951b400b042d40031181d6801a052a08000c48041e9141100e00032240e00740281d4070414101a0484d482d20740d48a00039800300184802c0140c0121140c440f074100301610600c03034904201d0b841c06003184401507c0c44000e6140e404c01004002c0b103003050314404007802180c0000342c4605603555441c82d286401c2001c1c00b511118404a041400140d880740e0409000c0e120a030b50160300c910f03143d407019180444c0816920b200f07130800400c0110055220080c1c0e036000a90300000a41000401e6041c0d40d18414401e1451100b40001490202e40d104e440081c001c140c4110441d00c0382659554110082d449101c80042c504082088020002d03803098203d240f80f00c0c00144034880c111590b000d0f000c5515903030f5118904035500450400c8840c9010282d0000074205008440c0ca030441214005841e0603000f004134050140204440050001c09401d181d14958000c0032564113684528100f132100035640b02d503a03442100c4200141800c914 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 520907059 1250 520905809 520905839
    0x10f20011d060f010302120a050d0309020f0d02010c02090c090301020c0a0215040e160909090f050609030f030a2d090c0f05031b04110a18060314070305060114120a06 73
    0x2540003003000f1a403c5a00300280001e504003001c64501c141c4c3d6100000c50010311070104100444d0310001601401d900c140310120501c44006482000c12581d2030015036000568510665412122065150360b5443d54414070300440d12001d81561001c1010a0382510008480c502d03180212500f1300e55030301c0b0050759007051080c0d001d0402e640c110940031a244442c0a002642683c009042c0b50581c0b076212000c0c807048130581c42c07003944c4071411007171000f09210060103182c0e0401202005103103404c00c10040418580b02c068100b00300c0350360342c10181d1800035040a4503680c1032522030344c004020034029088005840650416501707030012550010341c0c546000c00150444001074080c03d40e942a803134146003421490792003250002d49a41ca00440400404014182c0e002c040c0c98603442c42c0c4c5ea1102000c1007505a40010061520f40410340c420042c00754051644540781d450085019a00c02d0012100241001c510a0740c00c9000b02d095800c0420a07010a0b20a990481041004a40d141000050058 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 520908309 1250 520907059 520907071
    0x6080303010b07030f020307120512070302040602150a060806090706090527040f020a12060608011529030403031406031606050a050c0303100e070e0f010f20011d06 72
    0x420009040000d000c1c80e10b0b4451031945d401901c0c101001511820918500c200611001400010b1050401c2150501c12600010b40d4602141001e044c0a00a541d8410301c88000100ea20784c50b00040c0c90350a290410320182a075442602c4d22800c040d01216940d0210b4080d44010607100b001c0800d1a0500650860343c0401d0700d100001d10142525400701c1070b05c4003070416034505031207244080150321070404200c0100702a0288a01c4080142005001c03519141c004507400d07410040301c1401081c41004078411394a4880b940580000703441e0640d0a81121743e299a541003001008000a1540540c0800c8650030602c5a4200d0380e5150000c144c0c50740c4130000f00d00807100d03102c0003e000741481880034000b6075043e400d16a192011080d203a40c910b0b00f007221a041700c400c3c5d03004244940d00003181d40ca03400c61428181840394074010b07400914404040201c031410801c944281e48542c601c1070410010a42c0e4001100c0d010070990306481c1c0c040c1101c036400444408500c0c040f408458800a5501c0c4034030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 520909559 1250 520908309 520908329
    0x50703050d09061b02040221390315060706050c0306040e0307020d080922050901060509041104020d02160302010603140325050304030b010806070e04141906270608030301 75
    0x81304507400c00c0000c0d044040e0510f4000620380c0030313040d0545004807941c0909004161403980d05d007180710b15102040304840c0d41c04040001d66409000d50030440590b50404541c10070000800d0f60100864082d02480d036000e050241002e0900c4030039121400114003070341c42580d0900424814400956072842810002500246d180c2483c20200b0001c0016201c800030081203c0b0403001103a11854811090150100e580da5481b020300201060910605004200503900441a03191a03129241c010a840c04442e0040341c00003203622001c00b01d641100c0102c0850701c1c0c80c904070300c1c05080c0280205000d020481343e42070b0803005c002c0c40c40030020948030071131142e00c03203082e150340b10032400c042c20021000c049920348024000032000070030102d001406020204024440b5240004006010318050490680201d1410140301542c00395402c3c07055100100c8120103444038044072035a001801a54004d00c0180d146038422074003504444031040c86c036410340e01d0602129444164071501c03480284282c00b600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 520910809 1250 520909559 520909607
    0x90105010507030e0103050645160806150708030717130204180f350301050d14010e070306140906130f1b031202070609050f030a050703050d0906 64
    0x6610a8201690280b0080c01c84218000004048113030542149070411200980b15081c2c5401c004c000010308827400c512080242074244880c450450b01d80b070510200c01c018840000a60380c0e00c500f0764a0800046040100765070791481e0520301e00740d400945020000514030810070200c03e07120191b00d0701840c1241c1c403045170700007282e013004024031818560381901a8114800d001060032038000c0d18086026803d151804040004507042090302d0740076002d260125a00c40040452011040d030b4159407056071045000e00303503810420241408810114030300d43c20402500c0d00c140020501c1c10841c3c4c884c441c184419051141e2620424104072500c05560303000f54001002c0d41440c600c040302d0b0300c0c05401440c025080f81e4507614030700300003070440c06807000d00c921b010000c00072a8580410249030500c080c1800a0501d840103190100ca0305c1f80600c5042555810b0086990601021245503070103022200902e41c0c900d4825180c0070040d1012000c610745100000f40b40d40500101d00d4441c403900448842c6c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 520912059 1250 520910809 520910837
    0x705071a1b07020f060705010603140a0507090b01030e011b031401050d03200f07050a050103020c070e1503030310050f15030c18121006061106060618031b09010501050703 75
    0x380b80c1020b98207907407150085280041a8076400001d00e4094082c40000ca000d50850420b80405100c0701c0342d0340c074640d0003e4003903c04914040341e04400d841f0440408075070307641510012005007a00300c0d20210103501e0a081c0402c040084038500b20780554a444c2807016031070035804a00160400d200302c5030402c0003a6040340019114204005011664140d41c5140640c0d6100d0305d4030b42800548609100e501020b0b0620092528080790b20052000340f030294501000c1c0c007003168640005100e082102e210a80200380140c141200420a07804060304403500c4e4a4030781c44403044407143e807041c0b034007400b0926084003190602c044501c80d110f0f14402c2691654403407900b400ea09501200130f000541001540c030820b6070381d070250486c40711098800109130481c01008101c007152602d51007602409101c5d00803124105012402030392050013140d00b00d458045014001d50580c80300b844071589801001904601c907100c110380d20360079203001d840c00742d660380e00c8000541d11441480b03009004280640c1e2410f030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 520913309 1250 520912059 520912111
    0xe0109031706031f0b090109090210030c0207080d03060509071e0c0c050607060b0102010c0f20010e070e07020d03020906030c07020a030b0108010f1401050906060304060b06030705071a 81
    0x60410009000c58003186400c0410a01100c2d13003a030041040758681c54045002e1528441c0c15016014040d800c000c03420181e400a118514a4441001856281c040400d070701c40c001c0c0024001003089606950003022a500024000e0080b401030074410042507002c00c400750f04c52101100250015060280c41c142d0182c1c0582d641072000704220b501d20868440447c2c10703250f802c041e0041340c3c81920701081d0204010006801d4810058800b410031491604100219a1021032880140c8030384e00460741343c607200c00c2c000c0d02600d5040202f00f503074401d1000018405140c01922881402070350700f038030b060600c44242141a44a0110940d6101d6418000b29000202e50707030041c02003520040503a00030341e607070740e0703030441242c009902ca81c1d420303552a40300c0304414416004010000590085d110600c0d810311000529011015280900a81c8013100003410044d0952029070040780003803165850f4540080010072a522049040300e5034070803005003e41040c00c420300540105140c040303541d07818a00382980b00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 520914559 1250 520913309 520913311
    0x60c030417030a090804060c03030b010e10051b010c08091204150807021c0f1b0c0605030903160b1806071d010909060308090f0a0806130c03020603070804060e01090317 74
    0x344e03500c0d803c0ca40083d03880d000810050003d03172203110901009003005801c0b1191070752814140000402402a1581c400c0c041660041b4241001516510f146e0105924803850207440e0800f503281071100c8041e02d8200791401e105940e4402210640150314521200e01c1c01079114130301140560911300c0840c140a01d1200364480814030490700010325034a100751104001140c3c0c2030105404c8216400c000f07601a44041403000c2104200441082c5aa104400300c07420340f0410041100110204044400500c00c82e16100d40362100c0e0400c507031041c02d00781d030382c040300380d440a03c40710000507158214200030400034400d060742e4844502e074102c0078040e0280f100d800742e8141e040100d04c0070701240c0d0386000d22801c80550302a001c0c241d212003100d0240101c0c0100c0f51520703407050908100170091100c000a0640c0e02440030b40c2c0c03070090b00c0c226190100340f50500c2c0d00000c1d8492400b10800c404958030201c501c1c452030150340144013844145502e10300b00c803040e142c00b900080c1e854084908901c11300000d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 520915809 1250 520914559 520914571
    0x5010615110c09040f02040c0e01030b030106050105070b0703090203070e010e0f130f150204090501080c090103050a1407050904060e010c03180201050c0c0418150b0d11040b090a0e060c03041703 85
    0x80e4403c181d58000707000c41d06034015030f40200b01103c11827101035900d841030b604a850168001c0010341d027400000707030403406080d500404e49400381001410040c480d0b001a200c4580c06812501000c0d2141c68002085009002d854a0b0b03c1005002907940078a07211128080c131210701c00a03800c5103454445040381002e444082c1e03011210350b0034406844160741b00403c0100254000040c2950612018500b0704a50081e5188181450340062020030001309061030344a40c0280e05003104400745504a04000307156006540c01102801003000340320403500045c440c40041002000342c000d60010640894910300e204000380340c0100c2ca10001540a10020a02c100030b81088984c0e5250640000d01039640c800358101c0300d5070058003881c04005a8a059282c9444000d0090159201e544085604003000c0500500240c00c02d2480c1e0445c1e840b190f00000d01010003500020807407401c41810000f40500c001d07030071440e00c50907000442e41858202940c0c05254030080020001c941009040d003513800291035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 520917059 1250 520915809 520915823
    0x6022212031d06070204091a070c15020c2d03070b0f0901050c0901051b010e2109030c0d02010509030706031d0615010e0117093708030c090d05010615110c0904 70
    0x1c048c107130300c0b02100000d1090351181d913100114006464913105140c907010644041900501c400202030700041500c0140c0c0800b00944c025000082d440f109510385490040800ca020009496051003480d544584c45450a0020b9a00980b143c1f4041401c0359021100483c40600078850030f03d01e584901e000344203d1401030501501e42c0c41c10140d8908442c6400301c00c0c0300ca503000d40507130724000e0711004d94100d44005001105040003882804a0340715840a135482e44140701c5100031500b168026000c0d41d000d400003404984000384c440d6809401441140040d54416034402e40c20131000c2400640c1501c50301d4103a050038038040b0340800650302050003c1580741408840407041009800c0580c0c03152154038804000c103008850340300303e00d0310200184580e40e5203040280c900000648944101d04400d58050a1b540c3e0781d964803186040c2d28010a0040c03035000b132012501005005054109800740c48038101c90040d94150b1003010744403140450f860204940280c911081d03103142407800103a0280c09002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 520918309 1250 520917059 520917083
    0x406050a0807032a030807031e1d0a27060806190501050d030215180d02030d050109050126101103070f0503070c06022212031d0607020409 61
    0x34092800a400408055106040410034011020b80c0c1c400082030704455501030000b1443c201c40c103008240030107803880710700140d440e0401d4800d40c0400e82441c0d070008001c1c50340c0c019420080200150040b141c4090209044010b1076240613510402151086285405c50300300e441142c0a0800800e4030100076140c1c1d8480c00104040c042c484d80380b00700740130070050b80b510002c804040101c5030181c000c0c40c050502c0c1107d01c03000940000341a181c0f491150458006030755010404c0c1c00c0b10396410801840f500800c110000499000000f500c1a01924081400141e8079440034000f1a0024403540108640c02000491940040800a100e10800c1c0043c4c81d01d40d44c4202501c0c09403203413a40c0c18810582c0000c10003101650246014010043c6440d2071403440c2009180104611081040034006580c0012540445090b2030300c03c550f20382140903407198403070365051000340c9400711721400d8001c04c100b044132014051082803040a08075005020505105d03e81e0240070083c40ca01c01c1c102e4003205c00359 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 520919559 1250 520918309 520918319
    0x6060509090d1403100506030907050a080c01020105010e090a020111120403150e010c0509060c0109051005010e0109020f0a030b0105070f0b06030f0109110f0a0f09020a0906050903060c090406 84
    0x380380d244034500e800000e0504480080c8003e008a81140c980488454188140310110160750400e004030b50048416540f2307600c41e00c0b4041d052a2007544495480401241c0c001440b40f00400c42940e9074000760001c0100344c3c0c1c2d480d030880a641c41110a00712641014010100545c06010910100344800c0c0031100e040411400c081440d500a030000d9400d000203900704120091280103841d40319080c28001c0c00035080714403015103140680c1007690312800340070850701d45680007503104501140c1c102c2c0450b60240a101d1006000b400c4c28000c09000c07884210012550241781d000302c03242c191640e03e180b40b81102c2080e04500922000100c9810030404000d842c01190700d170903602040e18011403000c210346c207060041618050f940500d25410b64140320b0b0b1180032840044c0780c480d21003c1915201c100d00b44c001d00082c9071100540026220099030301c0045214a07442e40075040e2880e05849440060b500c424068070603001c0c58914541c50340c4550005440d24400c207010f0070040d00058000f14001c0d44030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 520920809 1250 520919559 520919569
    0x2010810090c120e0a0b0105010302030c0d02030c0a0f0212040501030507121b0815060f0a090806040501060e010b04030b0a0b0613180f02040305060117100507020114010806070516060605 82
    0x310b400005208501c0003044042c00d40708070250030b01d06500815140d0011350700c2920303040052246606040e80400040c031242c0090088038140203041da030455903883c01c00260750050b01320351200307070004054050a44075540001510824602c8441800f401d1500d81001140a01001040a801c07c4115444140408024060010100d04030031640c0c0c009a052500204201401040f0389401130030345440414503200e50b02281c8842000c80304c85a0b54071100e610070b6461441682c004242ea2003107800304003e00c04194040800e4404810030504181d0761a2504040c9004a000141800e1800c2000c1050a540c5610400c102d0390003501c0d81d400c0840c030b40003c0f15400c201d54888410606004c403a07480c503942c1c13480f074004022a034540460030542103889196548605000d42024070800301030520b51200100704511081072000003d0081d442d00302c0d4028007a0001d060009081c40056001080740c000100c1c5840c400d12140c0c4e2040c2c1040c4140c610302c2a2090244e40036100e885c0d4035030b4003040316100c1e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 520922059 1250 520920809 520920821
    0xa02090702150a0b01051c0204081f0c050913050601030b0303220b070317040309180c1b05060a09020d1a25080402131b09210c030201081009 62
    0x1039034001d03041c1c00019102c1d184412000828440c1501d02c0c101640f40260b03000f0741aa502c10b0a01c91004114608411a0000922840d00701c10014450801c040e80b0f05043e482000a107090003000c01e00c40b059441c10250b449008420a03290b004a60a047c4001d10090ba07004076440a81454049500c441c408042400d540c082402d15142a008041e0800d413420f0144c179410040003140c40462030301c0345039203009001044100c5440040040031000c90141441040e913280503110303c480d18420302444468040051541c07243c0c1402084003013001010801c80e5040740781c004c0f5040b802400480e40c50159010040c100c84101b00e80c01180c0d04181e0f40800d8100354001c86030f8a903d0405c16207401d06400c64401e001200058080b40c580380c0000d1041300e607011951580059040d150381180711500328503e0050100780c2150281300038001100d00da980d80c0075030b2190485002c031924240044400010b242e00300c0040750301070305100b10b440080005511400b000c036030000d440e51030014042d45504a00d4150341d9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 520923309 1250 520922059 520922071
    0x209220c08030c01060807050303120c040902040b090a0509281d070e06030604050307061a030a12030c05040f170c030706030e060c03220c080d02100b1804140a0209 72
    0x11001c503070b0903c00c2030244201c001812406000303041d55403400000075528459010301121595a4070040317000c54a103c82a0350240000480654a640d01d420860102d0342140c09036510607015208006042d040120010b030181c140c0c1d140d0801520010980c8205400e010111048400d5840c4400c00c0c007141e0f51246090808800c0014101d40703441c20300c0080b44e412010388414420b411100c00d0000154002048440c225813000c408110b059403230301d09500c1c503940304003019014061004910100031aa00f10350130325050b280c40420208900c41e4003100c0600941c02016a0030050703190510040c1e04102c10072920b000c20104032414003a8001c042400c100c2d081d4800d00100ba214107100c1903112043c031001c1c1d8031201c211001411403402d0910f850340d800041c00a07202c28419000039909000e140c030b01510103800c0c800115400e28640d100000c0d9101010000c40e4803092401e1405410751400810000c10000300b0182000b594031039031100340d40d1100300d00072100540f01c0c1c200070200503281e00d61510f100f80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 520924559 1250 520923309 520923313
    0xf05040b1201050a0b0a0210050402010e150a0807030203010f120204020d090f030905060909070809150c0a09080706080f0c070c240305040b1b0705072408040209220c08 74
    0xb5240c40203018038078429405c024001740040c408441074030b6000075810090382c150300020425886500050302d88030b403c80ca0031504115001d801d4440c9005081c014100110581e481c88004d0ba02d00e00c0c2201240028000d02800285440e410031602070251800c80b581070008000501d0400d048450804072101d01c0403c50702045007aa120080c180c02400c1c01d0028001690740620782000312000480802008181409101090740420161002000000070b01364860119460508103074444840c66040752491800103502068007040009000c285207003201d52036102c0301445e85810b84036400b480002400c18189031020711911001c1a0007051100081004121410301d12050034003040140e10054100020315091a042c400000e00301160541d02030080b10b1180410740244000441520030003001820030b00c02c102001c244c0080d04080300c0c4240c100b00c5d8014002034401c0000365100b800c00c0701d029501030711000014040f050344102c1c5000078803250400030f031454480da0b0342d01e10030051600103200035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 520925809 1250 520924559 520924561
    0x9020a020a0b0703050609061302093003040518130503070b0f060f0a03110f03060f060a0f030809010513120b011a1c020706140408070203121206010f05040b12 70
    0x2c442440e4410790040454a01171006241c40004601e840c0009404c40380503c0c03003084d20359100c1509038103481816000815243c4078201c5000c01000010380e40720040f0249100d1051920401c1d000000c980c110764020340b10b000e041c0b200380f54069045400900c18800b01550520380000560b044c40100f0100c0e2140000200034281414070052980c4014141d90003401e840580e08101c0d40d440c50010300b02c030342c002c40840b41c0311420340118019851174500c464041c4a1a0103200c0741c607002580640c0316601c20380306a1a481d40c1c40c1080c0360901343c944006020301342c007041421919480390f8014032602049980b400000e07a500c1c2015113044030100c078160742ca8903040c0300522107035050b1189c81411001e5894054244140c00d14444001d400c5082801038440e400600c0204000c604c3c0c000c0e8000741d1030f60b41e2080061a050900040c0da600c0440202d01c01c0c0194000041d40b08a0002a900385074a860071000b9039070307100d00c01034540080c00c0e01c2001c1440400c1c0700c00140300725a03070028282880202c07480415 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 520927059 1250 520925809 520925813
    0x20324070201060608040515070e130b0411090a1e030f05010516140a0c15110a020105060307060c0b040309080f01292b150e100515150409020a020a 65
    0x2101c0c07050700700001704004501070002040000940070000c02c2c41114840b065181d248003940c0460884201e150082c04008244510050f254813041c1c215409560034062070712807000c42c101611410400341c1d070000305900144a51011515400f502d02440c18198101507100e480b200f6226100400c100c40c1c5039161001c00501c040b40440c242500c0b00182000b001c00c0c860311034024401c0c040c01c9407007810401c01c0307070140c024084400761440b68030400c1040ac008210150b02064030b264800742c8950092340c00e02000c01e2a07400c0c0080c035401181c0041d030f40d940c021445a942c2030199240988143c0400a08442c0420440020701821181080d043e00008209c440b500c0040c036106c5950000120062414052541030f0b00c5005402c00c0480b03100303000110b05502c400858200250101c8098200c015102502d07000198544c003c1302c210011804840010130225144000d65404071070140141c0c50100507000c4906000e050755922461801800c0c0c2425141c5841b10200c1c1c200d04400c01c01a8440c403440e400b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 520928309 1250 520927059 520927061
    0x403030e0601060504141c03030606090b07050a0204020f09031b030c031b04180b10030c171c0c0b16230405060f0c06070801030c06090302010e0d020324070201 70
    0xa1003150540181c0040d625080014015002c0d5102d082e440c0609810006441c0e590000c0c084400c0c5502c0c401c008003003045090040051500327010b070101103905000003181000410f000e4854090b409001841d00e16615800d000280d0084402080c2c1a481400a02d056940a221503000002034807154402003002c0c00416160014000e050350094000000c0c03e000c10b24034101d000540e241c00d0300d01145010303c00d40d9080d000c0340c0100c0701904148880c030070f120a409070100108100c03030042c5944c820481d128060609051900b062084641d842020144c9402031300c1a03403c10010000d003040d2000a07a60303200c411006004582c2e81c14001c507150b505d61a0182c0203094058041c41c40c5880241581d50000701c89858070490150522524010032000302c00d00700c3c4402c0360400b001140581c1e00500341500040c048600a0000f280c84106003031000c030303005103d0401e0b42c0c03c60750169034174031404243d10188026031740c08500c2030340c0500a00700d40c100c41d244e800c81054200750300100702c0103045c034000d03034028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 520929559 1250 520928309 520928321
    0x81209060a180b0c0424020d050906070605071e05371404210c090e0c04180602120403030501082b0e040e0a020a0b07030827010f05040303 61
    0x2506152410708030040e82c00d14510903190041e4052543c600c0c6440d001002080760003503902c40314180c0602c0d420740141e01290341d00c001c0400813036002c9804944d0080030030f5800b8003900084603040038050280c2c0011a046030442604140c2c070b810814550b80800d82888156000c01030b0b4040401ea00150340c030660021040b6008081d03100323580e050b0003070700031900d150a40c04499098104100035031100d660400100700456009000d02c0440b50310011170702521134824004040b0698120389188030028807604140104050000030901070000300c19500c2c00c20000700240013005e0030000e618007601001504910040c080903100c103201285034a0603140060984005801040c00358200700c020f88241031070684c052001c2c000400100c00900320711501280d400e5108903e0301d52141c00c01c002035484100120b01050788a0007503404152031526088049924072803030100400042400703000540a04244800268092000c042944a5002d120a260035280d51141d0703c5882c9a0360703001d202c10141c15200709 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 520930809 1250 520929559 520929571
    0xa051b010c210e030406120b04090b0115030603030f1808030a0c1709010504030605060d17040924091d0a080d050105010804050a0b0a06080303011e060206010f150c08120906 76
    0x1840794080c81d035a1280c8034065882138500344071000c1102c00790344e00032344c1265015907806001040811141d0400800b501c00c07c0c4034182100341038000713880406201e40508002d407901170312515886548e040084546c0d2003920f4500342115490070b40031410360401c0c0003d214140c3d00340c0e12101e03045654103011030014240c1d0340c50040da0000b0070241c0104e0740c000c002d5408407600980001079940d0b998001c00c0c5180700110000b88281c15552280c2c00354128200503009440a80000b004881d00b0350f0001e0303010202986101d200443c00900401403400250440342040000121b0040d858551119031403038541002c008a80105000c41c64400ca04c07414492240100001d01e40907025051a4a40c152500c2c142c038409002c5207070322000513a465100d80c1080c00103082e003400f165681d6035110703400c082e232a0f5824450150519103003000140140300046180c165603401907a58100b03031802c105807c90700d00100013070301480f00e1950401c0103e41c4007409400010708551200d80340b40b4016900a0030710a0040c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 520932059 1250 520930809 520930811
    0xf03010b04240c06020702040905060405070806150d0f14030a0801031a1509090c0a030b061c081b070b030c180a231f09080601060c03050a051b010c21 66
    0x10b859441c96200f4001c2140c50380141006031384540b20300200780904040100a0003922402060008101001501030112011042070742d4598490590500d0000030342c82803141e000c01030b59505030114051400c407010061203611400d54902c6150000c5003103811a03482a00132a18001c01003081c00400d030076040c8415814540d407402454904000500350b42104003a81c01125403000160300404104170800108100501358580d445d43e0b446c01d5400700800703c0d480740c00b9607108500f9914009403c2160810b0f01c2d44940e104d420810511942c0300900c89a140c0c500f0300c0c0c8140000001e0072030007640254042c21a144405903149680300103541e4103410398400c00e00408649500300840400c0055200ea202650500703c4440d071880e800059400340003030314101c0200d0a8800b04440d954200f0001c104454005064035401d0f030b681c000c1a038000002c090060089001000360010301481807000303004100f480e0300b0403c0c15404601405085902e20aa10004558181034001c0005d6580030f40c85040030340490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 520933309 1250 520932059 520932119
    0x2304030e0102030a080a0207030c05011b030e01020711011d150918090304061803021c0209090f0d05070318080607030e0c13050402030a0614040b0a05040c03030f050f03010b04 77
    0x90300170290034000b00046802d031360100b1028109440b849c48840290340100c02405000300001041d414160817801e101c020900d03020b4500116403040c02a184556009415000800b080000540e030808011104414121400c2403e816541c2d84a404d5150420321104c8180c9508640040c0083c11312803026850a0030701650400c441c16030000101c9099031541c0c54810240161f07654240c03109907664000952002c00000003030b94412003e0881c1220038000c03208600c0780d8890300c850301e813070310f0805108921b43d41194402010081c0594003c1046034072030314002c2241d40070181c01002180a83d0040036054200d03000344801160701d40034aa00d80d4403c207000d40740c030801641c0050384412000c01031000305920f40c00040c082d03550602c06c1155840c0c002c003050000301d420b11042c54040b102100c0072140e00341c4840100f9031495052280c1d903c121b41c49550780302d03858256101500c50386018000c602c20000c0421502d02d050b081000078500070301c0200c0e03030561601d052142081070704130714040c07036071028490380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 520934559 1250 520933309 520933327
    0xd0306051201150b160506010801051b130b0702060f03041103070f0609030210031b02030a080c07030813020a0b1303021c1a0c161b0501110c12012304030e010203 71
    0xe4251084808141c0805e95603080d01c0c1c2c40c40c0c603a155081015046008182c000549a04103400072807207030035014000001c0c503031140209821070040c4010000180007000c010300050141200034080707140001c0550f0b05100c1b0038000340000d940200d4046808114002d01084030341410845c0c5400f403d5024006580f2030305107180145540c0240c400680f2078800034101e030034400d0080c3e005200006030351001441114010401940c2d03684412a041d00050007003002400d0f1030400030503150603070342c940c0e41e6241d1506c510403080e8200c0e1400388142da1210142c40001008401c58000300551f54028540e4010320746140100071508000040b2414150680c01c402e05c00551000031504000c00c2c020481c2c4803d4540344003200a07030041b110500d444d0010a82400d0a104450003244d240c0b0000407070360406540c48100450f0045000b640794900d030391140055181c9880d12403135081c01041d80000018140a5070703014520507040000410492104060510082c1540056428180b0070280003c40c9041051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 520935809 1250 520934559 520934591
    0x901080102090d030c02041d0703030f08060f012006010f090e0102040b0306090702070815010e0604060b0a0c02010c06140f07180512100606030b1e0307090b060c0d0306051201 77
    0x9140020104400c0d480c0e421700719a40c942c0412491230058200d0190b8806408940e1354400090006401007156003a196000301c0c407801c4001e2150740040e140c0134803081520010b4502c108928018904401c8000c040075a028081003040e00a1a035074038182c03034092402140764202c1c0c040c2102c040c92640104802d0214840650449030403107400d50340182c075a56005400c038100070b03403074200c2c0314580101880c140c54886604021410385641441511280d114003007004221107040c8902c00b0468010701c0307000d5140c2d0082d0034000c01c090060400c1e0001c0005681c91100300c030b040b4850060b541c0700400a2000340498182d074142d00561703070304015010320b482c425501c400300ca442c03160a11611b50501e540c03421081c248100c0c4500b1460080c140407181c2c403041d000c4c0c060a107001e402805807440410b5141d5040c2d0038146101c080f0006000351903040c7c00c0107020f0015085940310b00c0d800250400a504100c6810850124000b04a0b640010070742c1c2424104504030144040c0a200c681c109800c81001c4042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 520937059 1250 520935809 520935829
    0x6150309060c0f0d0e03030f06030c0d080f0405040203010f080105010e1e0c0d020c0f010506190e06030304030f1a1e07030c11030705160803030f07110316060902090108010209 77
    0xb201c0d07069842d034540c610341e142d1030300c10441404c941908044948010351000000765005400d89008076640342c3e00c04052581d1403410f41440e507880207800e10b50030040b415941c001c1124504c101c002500e05500c52010400383d80c82030f444400c1c0a03c107410700304400ca03420700c43e0501420120303000c160f0900f0640181910721404107030b1140c3c4c808a4501165580049104030f034400c0103842c80641d1646440711080382c64115600c04554154205030003d6202d180200c1500c4410350140350407011103050803504403c40300f00400baa034062008210100202e8440602811102d105001e01c8030141034030300409040d41805440d103030401c034400142a2200314080305290344071905180015940c0a000700c02c81c3d490644024400e842d0000150b000180100854081440316108140c210700650b210f2455940f40310441d206100a9075032000300d4030031849900580840d0840c4004c81c0d04022182100807407400382c271001101c0c1c56030340324500821400e21300c40076401040c002000311b00700f561042c0402c4010007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 520938309 1250 520937059 520937071
    0x120c0509010507060e07030f060203040c1a0d2003101401050a0e04050a09061a011b03021c02071802180f0a0504090311030a091701063b070203030615030906 69
    0x1440360841748410804004081c015900030020b0001c40000303040803c002e40c0251002e0b00c00300030006010960002e00c0c040d0700c007482c15009050349802d0710301c0840740003030214843c0744044e045120044440c0916030307400303140206124000180e289181107112410141d43c4880c0906000041c040c002030560003249015100a0958011500b0782c0c80b030800800910550038010b0000346085c0702d030910440b00d07080d212402e03603085e25450380b21a1991007600f4030a004280042c0180e00042c60311400b060f4002161a034a0401d0044800c1d0310b440d046143c84c00070440444804544d4040385c010b14445080400103040b90056410030780d480c0c05000400c00c5519280183c5021b1511010b0203010544031301d04603410344203c8402d403522030784056001442a600c1c1d20600312241c45100491890007010320454084070044002940b8004125041820b0024580800d0701060f07101603444081100d1418190f1007054140c0c0a10303030f28540036040111407074140c05041c0c0048801d104100384490005030707841e0091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 520939559 1250 520938309 520938311
    0x240f06030c010f111218040923100216030f0807020a11010e0d1b0b031e0712090507081e0c090c07330b060d050901020415120c050901050706 62
    0x21001401a40e0303d11383c000925501d0b120340360807407544e0520031014000c0d0030402002c010742844c0c020100005d0b11194a0f001c0c10381100200c441d8002d0b00714081000c1c2d0500100d00343d40d0803944041c000822038000070b46003c0d4801740e60340d1210070158448098800060b090514814508100e907009542c3c400700756000708035250b6062241066801620540e500d4240241b14803011111441c01a582101c500410500507082902c0440d0030f072040c00949214a100e4040480c4071010f680a24060110260070f041c00d20600001034548105070703000e08141c150041700181140c42c9005803140c0761070701901100705403100041c20b00c0306030040424007000402003140c040c0290380b1240103020291040100c001e1042040f000320152604018600004152101c00e40790b0b000c16070a28010141c41d8400f002c02d40c890b1007040400800c034995840590000a040001420583c80e4402068004200100003000c1210b031042c0d041d0320107540c0100180d1031646d103042401d00b6012000a843d500901c40300070210707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 520940809 1250 520939559 520939577
    0x601030504061104030819030e0a080d060b0c160503010b0a231f0216031518150e0f0703020307060503130615170708061302060903240f06030c01 64
    0x8050243c0041d43d1200103020f045548995a01e820303065607025805803103854005094074107013a8024480c03c00300e020010080d00c68034056940d00301c02c5510291780e40c45015640c04010401107440c1c0003500150207e08002c04c001e4110401405102c80c00b0741c1300c984a60304102c0301645030380300e182080d000c4071054241c0b41d05480d4107507489458290045851500003400d0512aa030f41c020049407020b030b40c00c3d0703902591035203000c688041c1c0c1d600c1c44500001c0c08982c8152007403142c02e1000d44c0005104a81c4c4003c0e00528002a40d0303120030860350380006486aa20f45e040408842010310524410702c45445c01021071614680c0880d485500030700c039a0091050200000c0c2d03204017403e00d09140c50ba805481003010402e0202c510540190b280610141075a2080100c946803000007542416201c0c403d0041005646130701ca1244085d0712003100b01d81181c802e1000580640f010400b90503d1038000d020000d00000c61521089141e400030301c40c0350014051800c1c064952404284542150360078a001c03050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 520942059 1250 520940809 520940813
    0x30706051b0111030f04030914010206042409051c0c0215250605160f020c040209360c0a050403030f0e1807140c0601090c030e0a080405030c1203030601030504 70
    0x41149803010743ca1808004204005158042145031240c0e209459020420703407901c101031000089024041d0160340070a021402189050345401c1034202010b1200319082145840c10044e80c06a60040320254441031002030b0f0101408201038289141e881d155000701c03400d40000d400714402c050308001c00c1400240036200401c0e052400c80e4003103a01401c04103884002c0c900400105400c4520126001d01c00e075007907040c184203400801e00a1034960050003154800b40800009600c4982040e9104c49012101d0260501d0350381c030010800c0800d0000300c0700800c803d070b0401100e003004021040c03607041080484d01c000e800c00296030580e0740521701440d0000c600302e426941f030b40c100e9204039485a0601c040c058000e990b840c40b284284002e544403441d44840c07111858150090041d044180d4101c04014441c00c0302c99401070a0a00c240d103408509070341c089001604110301040140e40ca01030004060026007000c0103c3c0304a43d0040c0c40f03003912018454a03817922170001800c0681050348403008541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 520943309 1250 520942059 520942061
    0xc05060913050a151e1401050a14040f09060905010b0a1b03050d05010b03160f0905060f0f0c070303020c06040f050d050106090c050a0e0a030302030f0c10050408040311030706051b01 80
    0x80080d5006481e14013961181101c040b0380c00c2120300041042a04030020407455014a510740c00c90310180c5a49040500e40341056650031030103000300c9104c3e0801e0000044010385801c0881c0201030441c80040e0b62810041d01209842c1e0507003020402c1c8004015420301e5036440507142c88041000501000c410020b172804880c03910030070152510039410100003044211190000710300603030044040040b050030750001a2001d22172243c603600483d0741c50b5020805800c240c40140104907511003000d10304200603070071005a4005c00010100c66210030014401c240c0c0410401c03842000454206060600c0c0ca134a0580442803801140c0c014400c1701036140401000350420800341c84036800900040019110060641d08138140c0000000c610074202a8581040c00000084e02c1e05903019501c1d007c969040d005284e0b03c101d58402242c880e01107081c3c0d52058920825000301c0c40740904503952461401c00074002d5404007030051080c1c01038030040005c281c10604403402a4402134503405c0072a00075808038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 520944559 1250 520943309 520943321
    0xb0a090602040e1501112e0c0804022706040903051b0c01120203101403030c0f030a030516020d0e15030f01290901080a09050a050a0c05060913050a 65
    0x20440c500209010841c25801040140301e140c8900f02e401d07007681040c00440301a25003001003480e6411031008a440300d8034403201c04aa060144803260114561034040324225819503170b03402c0025191a050000710310f441c4081400039001c0440000c0e014602d18620741c910500648100e200e29134031200c038410940110305071788a03521084480e01d04010001d8207180c03584003906032980081e41083c64004124690b1094a00801c4e541900c1c40d115400e0051000400546107012035040c401488400d0785110304201859071071003034101654460058850190030b0741c40c060405581c0e2000341e99141c034071913400109104611514908241c14042040106d880d546d1805460500c0b40000070800c03032071009050040d41207581108600602a1440d03140314560780002690700ea01400802405000d503200e0070303c058006428207800912510b4560f541d40c0750110032101200c0e10740250494070300b07002c407802d0900d0040800780e8100e881d19000c000040c0e00680042400c1c0380046c1c0e1500400d500c104e49034405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 520945809 1250 520944559 520944563
    0x1103040c12151b020609070b0d11091f030b01030204050d0b0c0c15090c09040b040b061906031a040b1018080303070519021203010b1605060a0906050907050604030b0a09 74
    0x80200b41180d005141c03e110345512002e01500c0b030440410024480040d501c0c2c00c440701c040075941400603603804080504000c0601e290100c905102c044480d940d03084000d5889003d0501a50380300640d02009029a105420b60030305151060000700100d44514802c40d602c10340c0304181c80c0c46c2d680c03240000c8515004d0b401640003580724141d0500700a0300e00d00d45070760040c440c0d0001c45422001e89020081014400c480041090380700e00701080001b80c8035448960010401000da000310107401c0c2140c1ca02026583c055000039841d011086190303d4001c1526400040540703090045501076070126107440e05894511003000810010b401c03c0d42070039048280580060025607032b4030f081814000300150030410b030700203005402440c151041400000c089a41001c030350070f40c6055a00e403801c6400d16401c1342e201c1800b114a40501400040c2050041910560382d2803800a451011400c214045940042c142c0000b070380040e00c00d1040d596202e003610200c90788800e0115095461200700f40c0907051801e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 520947059 1250 520945809 520945811
    0x309021e03100c03140603030f0f070303060302090f010920040b090103060816180209130902060d050a02041403150a0b0118080106090e0102090d06181e0302011103040c1215 76
    0x10b901811645508644c0c906819994410f05d261103510805850307100300c00721407000e801c080100c00328410415018100d214043d00f00065500e580c4d4001c0b4440040c00c07200328118915140052052003100d124941009500800c3d07441c0460400c50085080c0c42039010701603072041d0125810346181e110390080d4001e80f44510680b41302c0000b6140c000c00c81900342c082e145d01014408503c0740d8411303492094400252000302034510f881c1281c07041800a102c10401641c0000c410412400e84d05458041c460040f002210010fa40301d141c804081c09107c1b407000090b2181e08107030803040c1c0c8500782900369900016080b20010348100c000c00140c40040c4558095580d652604400003034181d0194013000843d1500001800503d40080d40c0600701c2c40707031040999201850403080404900c183e0700000b0302c510341400229482c0142d4590040d0944107500e180a65000c8a800e80c08159080c060380c0404028141042d086041682d40c048120790207024004803601040b6008040c050500800b480c1001c40c614 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 520948309 1250 520947059 520947071
    0x513060314060f07020a03080f0604091208010302030c0a1d0903090a121a010b0304170f040305031c020304031209170c0a122105091c02030406020106060309021e0310 73
    0x420140c9900c811510f0301824502440041c14803800030074a03618040e410f58510000742d03141b4000e0080310102929a81d08159140600c50002c1d00c45200088450270584a140c010741c0745104241c070340f0f01011204ca000d44680720341040b03404282c510414070000443c15460071a0303102d910f220b145000e2140003035030111030002c00180c80705207420100a480d0140901c0001802c01d5030118500c80303001e110b06d03901c4110410004000c00c10b1070700203040704061045410b14245031410380c0d0071030b600260001d0f43c00340c20020b0f001c1100840c010401d02c110100f60b9042d800c601e4142c03000360130035440d8041c0181c0ccc1d644510a45040044416901d4139082c95455980e0b1a564207484050751414010411201078516843c001c071060300030301d1861080c02c038a1040b440480443c00740d100103050b0280000605204404466002100d040c1480003200100c1d401181c90b94606000203003034403110350002090604d8000c0c1c08000d601c0700f80500b0103100192111102c070051080109140c000f21000138042140303801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 520949559 1250 520948309 520948343
    0x15050409110a03080d0e0102070c030602030603160b040509101514090607110319110103150f0801020a020706080403020d05031515040503010606050903031912110a090602030a0905130603 82
    0x40c0103414485c051703803030400c0b86030700200c1014200e00c90041c002d0519810600100001850b50b0021a80b015014090314a83c16600703803003004040260300042a030b140040340c1440b0b00c2c180f0b4030240794040c1d901003152584920b070480c08140340d0545909042086041c03000f01410703000060031035290000c0502a1640c40f86a070038442c01316034003191407a1180c05607100c040090480d40c6584144e60ba0444125980444940d0040d07009008218120400c0040a040000c80181d06031b0508010300403d030000da03403041105d200a04094035a00f00400f8482a0400d02003c25400102150f03c41041d0400d00d0340c0b9241c01c881642030f000080100c070760112640803405031024400000c0d10483d503080d0000e0240703544509060f62031340201a82150154003e01240c6411480046003030b003899003508003a8100f0042e12111400c1c0d680fa562000c801e100009944104c0950102415004100d544065824503280c080010107000c80c81c49018458a140c1c002c00410310229441000210382c80104040510081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 520950809 1250 520949559 520949573
    0x8090a080a030209040c0c020f04020c010609050405010903030b09010b16170d0c020105071403040b0a090b15030c100507110a170601050f060408190615260115050409110a03 76
    0x184031140510f04040c06c0840c49800749040055040c1d000300b00b20710707030110082807100940201d80c10070385943d00c1d1b480000c2e0b060664402c0c00d0285005030008aa580907504003c1c081c0c0b902c0030129401172805500420540c0828415540080c02104100d640303203003541020a061641204040102640080c119081e2410b039481060003c3d0742c0c0d00244070032b903144c101c242c80d40d4040e5521103075200820400907000810b148944c0380d005506003c0040d40301c680e5292a41c10a02c02c607144162106058102d089602e0100f090842140c0100c1e084241c0c818110b0b0010a540030303010000305508101c4580c15519035892034018003409041c4448204d5001120545070b850320284501802820351580c110003e007041c4003114143c5482600030200200c03c1b03410342105401c148070946072276560b40841c440c103103040500a4024011101485001711040070308070020b00000320542041e80c50085800b00c100704c050300c0b040446100303c400246051042c103080e2180700c40001c3d590f91128804001104001c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 520952059 1250 520950809 520950817
    0x50d050108060915070903080702120a140c0319021c0519060e0d02120d020906031504142403100501090606090807120609061409062d040308090a080a0302 68
    0x30075001ca8801c213442c0c5500440382d11050b258035000030b04491060000c138410b4001003112510140501c82c00d5001205168149140f0350411a11003105500c4c91203203c404000c5d00440640850182101c20080341100fa007411002400134015803080040d52141480b42909001990308941034580c0b0b240e400b02c4040e81008883e40445900d460a0240c608007540015034512405890b0028845095022030001c095006480c850910540030050a00c494991101850003207100c0c030407114401442200300015122512407140c90407410000300320102030140741c0e0401c10510040254030414082012034102440032010b4005035080030700001d114402c550003101162603a07030712240c01c3c07500c807030015450b40401c5c4140c402e0840f02c183c025002c584c1c2548000d8085110314000140101e07810010205088112072200080e0008030812140134040f000421058040700d81071459001c00c12148005110b018002608000741d00000520108040011101c15500480e000f03860b5020110001d0181d0700c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 520953309 1250 520952059 520952071
    0xb030307050109080a1d10030504050f0a05070603061d04020f0112050c03060414040302030307030b2704030306060c170d1116020f0a06020c040c0917061029030403050d05010806 78
    0xb14039120700c4086e0940140d000100e10002d04a030041800401c00b140035100180041c0d82c28003c0509506040e001000b0b0000c24910075000340a54038030703201002d0100c2320503074000307401c0c150069141e40090048460b10b5a12541c1182c180d115016242d00403104002c14201c00c5661034901801d0100e000215009107200d0803046030280805070102889000e24001543c0040251b0300900200c2d082c54020380295550031030280081401144400300421144164411425404d405505010501d40d2601413107029010ba8105000443e41c0c1da81c4018010f840c00f10780c6441d041000c030300d41ca8102401e422808100303903a020025200e03850104c1c0760b40600400a0101d10804100c03004980d00e0a201c1d13003407c100d41458000d041e01d141d429003400080c111907482c030f00c20888541c40100e4101810585000010b81c804010000da10b4490240640e1346119007080301100c110903950700315075640a280020130030ac24007400d0340301e40310361a007039400d030185418040c58603080c06c0002c50104400945144520 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 520954559 1250 520953309 520953317
    0x703120e011d1011030a050a0b0d06090b0f010803071106040905100914100611120d06060207141c0f0804031a0a0c141b01020409050709060207060905040b030307050109080a 76
    0x250142c0d222008403420070900c00c9094501748005902e407091548420741c0000d400101080710040140042c10f14400e0f8003003120100e9485c1258018414140309950b406012a000026035505008210b0303541d025080000341081103070035107080c881c2c0742d00c4c098500903d4411401d0010b410020800a408101c6000d0348035100c0c80d00b0120301c5031401100589005046002e0b000340700781d0400754112030070900c00c1101e162500c90100b51102c40c0c081c04008150036000c2c0c210004540d8281000241400c44036070000c2d081e00744841000000d0b80e110720803400690301d64404044101414a0034501c2c0d1507540030058140b90001c9070003c18003141d0342c0080030a03024034209114507520120701000301c42000d001c600006800d0001c009181c40020001c0014807220f000004501568607801426603100d5084404003503280c42c10300c21805d0b004a05034000d04914006014402c3c02d1203030040000d0124403595203e507071103940b5034120703460500c00c41e242d00340c001000b840b402140381020035160f031000e04810009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 520955809 1250 520954559 520954573
    0x40902132c07030c050306040f2003060a120206041707150f030507030203100b0a03110316020d14091306030204020307170a02070b0f090f060f0105040609110703120e011d 75
    0x28510034444c507038030030034640c44007030944c0c4400c010700000b0304000301c0b0381401690301c03c00204640c01041403951140300c034440c20780d52480c0c0350081c0401c01079141d0250641c100018151001030340c40005850503944a001c054064244c8080140d1400e142a842800c03c14a410004455181e000c1e003010030340352a944081c0801e07101d00400710102c2c0f000300c1361710350384651040c03040c05140c0c00c0e00014011001140740124000070b41e0640415682c0c41510020801c0e00100080c2107030a030180140c000c00445800c0c002c0c00c00c00d800d0707034091b41c0e44515a000b5104100c2c480b034612601c1c6482e03101d8009507401810854503032815a001410b100d00369010124003a180400042e110b20281c0200c607003d03503210b940c00c1080d480703000300b4290040003d001e4160740c3c02540c01081d89080e04204c207a11400580b841c40e81d155140906000031950250414407081e03080c460540d081e0b21600048460056140ca03040000030f145000e000f00401c100c40442c0ca481d42008840851480c0404018038080c0c0c140c000c0c0d5210b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 520957059 1250 520955809 520955821
    0x50109061a0f0a23040e0606270f040e060a0f1104121b08030a080a1b0c08040504090c060e0301060608060d02221a040b0d080310030602070807111203040902132c 71
    0x590103044280107402d40710340c903031041030042761096402151000d060300c4c40903c40e0000060075101c03044c003040715035407040082141c1ca1103680200d003507503490a0300400c0040001044814a4405d5001d00c000e01203032940b5030003c002d0001042030b2041e20446ca4a0030043d2101c2c56291242e010b4003200d00080d42c0b4101041d1900c030075108096420001614001d00760101100607598101d41c03001c25a11803000b0302c0001150784860040c4007490740320f0880041541c0c00d01c1030140244e00d04288d0140207130325000040c80203a401c000308a030000001c07664122054890310018a4072034210403040308401400880e2910521140c1083e04c06a804c606d1045074101448144812a840300201c1e13a4010000e20b450360101d03001d407009541210380301d42e4149106440c3c0d20f8010590f400858211001d13000000c440040c0031112800b80c0c0041300c2280c050a03200d61702c405d2295240501c3c0210301c001c03a80041c10060070040c12001c20000d000444220f41e090b042c80c6032201d01000401001a042031484c000100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 520958309 1250 520957059 520957069
    0xf01090b0a0609150c0c08030c120f0304030309060f090c080c0114121305010c0f12020a080109020f0403021801150f0206160905090406050109061a0f0a23040e06 71
    0x1520103e65403208090f1901d00283d906014142d02e820920819000100216541d00103032406000010300071552580003001d52458030b02c0d500c03a1306080b80400d20012800d0044501101d8002da018540420301c0c440c0c0d0f00302103000741104140d014220b0b1800c07106504001e00ca2a0800494000c0419100c80c0d00d14840151503841a10070b00c1800c40300c0800034484040c0a500d840c07030f0031814098500e1030151955903890b0840b0380614948000c01d01034005018520307440b00540039680c4160781c8c02c0d41000d1044802501d50321041c003920035465008149a4622001c5100b503500854004198009500300000c2580140000707005143e0001d2030122103d405500401d500251114950f0040c4815610340c07078900302981d1282020003c000c04980002000d6640a64442c0228000c11001405514060203001200c92991090907000c654245030780c043c0d10b042090300d1003101c000f5045550707403044d202d0480700004d60144068450890b0044091020140c0010300107813407015480300c0c1c044d2124401c203e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 520959559 1250 520958309 520958329
    0xd0f1b0c0206160c0b0a1107050f30070603020408010507080906040b10030803070201020910080108121608030f0a06080705130c030e0d121503111e04050f01090b 71
    0x19400403400c000f16050441c010340c02060b014094400310103815229021980c56602140f00304000400d072094604551a00740603000081c0011112184d442141c14041504066104194400d465000e04442c0c048820341e00102c0d13501d1108001d4440f04c03619904082e00a40050080405940c030f8a00041c2c41c1c08d0043c0c26060182070100010f00c2c140ea074aa455031203003e001040f54082c41100fa00004c0002c4290001e1801442503800140e141c030080c03c24000110041900d43c1c0400440f400104841c0c034003c9080081d1900c4030038000d0342c80041c503119118070500c4c44001890b1100c000300704501c06007480310030303802582e00c51401d10032103698403e215030b81c04050050591100021001905058140e4026103404050382404960305003442c0c54035013407201744c0d189080421180c180d603203000c10aa1244c0105042051102c424041c155104c801300070f20991f12850040b1f08154048440e0540b8084001c540480100305011515011492181000c5d0a100d040b0a80b81840e050f01203606c0c02140f10303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 520960809 1250 520959559 520959563
    0xf03161a0f1204030302090a1502060915010b0c1912120207020906061b1b01090603270203070918150c080f13080d0603031e020c090c0d0f1b0c 63
    0x1402d201460b20400d1140710054030460901d41c0c2000703140610345503e40b8280081ca0b4002c0c5220083e03410380030203418000000c00c00000c0b40c000c0c41d800d9405c03c40c1c0701081c60646215030415a00c3d0101c0702c042a10380920901c0288000241101c810100186045090b2100d041d071303921080d10510309040c900582c01070140081d400004100011240d042a202800d42c070300301000130f50a50740035103020741d060449500001c80c024404610386106940c100a000c4001d000b20310f4108200c62070501a0382a451030340c0500c0c1180340c201400312056640421111026010803a42002161843c442010582c040701c10111040c00c125001000042c031a48540c1000c1195034440300507968442052828003000140942e0304581d1040698021401c91009011042075403100050140d045050185c01c02464000307030304131a8074038501b01001c0359009c1550a90102c09a1307045455482e550b4203003071035009a2090310380551400c0c60700c0c03000e1521500551403e9008001c100ca8858414030308441900340c140d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 520962059 1250 520960809 520960837
    0x616050415030b0114030a0c270b0a17010e010906050a1d0622050f0f01030c0b0304080f030c09040f020a0914030a0f030c0501050603060402011d0f03161a 68
    0x400c59115010390421000703c041490407081000600703004002c0c5800540f80c0740001c0b680ca4410f0905c031904403121104514440c0c40c810b041801c5d0b58101c1408104038060300c0031446000c5031860251303008070303201070509104000301506907846988178603208100b40704660b49681080e10008070780c02c04942c1c420548018007002b10088030420b40200102e04050703c03054004010048100c1444820000600c54000d00b16010403141800b005a804288001c3d001960800c00c000c010000036101c5040e4208840c94080083d0f1030f990b590802c9011402201c030400c9451f1000020000100000d00007014918012902080030303010b1049100120b0160b000c8400200c0e10040c2c0502401420209100c101e00c0002c08582c0d005480b5591402891402c9130100e002c1901c0c00b040c101000303400e009543d8043c030140d00419817440d140e000208484004000704112001c06c00c9110066220b40650a05c1060003600b25811700c81c07511170300003400b580c030320034112140751048181c40c040356800c013200c5000902c018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 520963309 1250 520962059 520962089
    0x2071a0405062d12011a16050304050a24090b090105091203040306140c091f1b2105091813150207170c071505070c0806160504 56
    0x3050004030341c00b09941c4800c440031043c014031078403094070742207034403001c803c8183d034640d0134007086a02c250300103070040129180c00510200032070911400392102e030780c000301c0c0000801810b1709203071341188200e4001303e0f0400d204420108003114420590b40c100c0a404445a109000d010001c884d810740500034210304603820803c101c05503100d44080c00107004001c00c03103141940b54400c000c1c650b5120394002c440c0c05407950039000e2144007400040d17510010402c121071070407001000050403c0d0160341010950441240c001d945584a40e00110840008429011a500c107e0500e404100841d035030b9410100d0300284030401c02d500c203078213990305d00034064080308922550340a1201c5003d40109103203040c4c04601600004560039001409010003840001a906c2180e030030150350160103000c400c10041010850a03c0310900040d00d00111005100410380480c1031f000111101e01c98810087c040c502c4220340460090004220607010364900c00c066003d003c802c000648290045100d5121544480c00f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 520964559 1250 520963309 520963319
    0x11106042103021c0606090503031c050c0903010c020a05010b0d030c060507020c0904030e180105011209020a081621080414131802040b01031109120102250302071a04 73
    0x1c0303050802440103007009030918030b060003c21540f690103072040440701d031950300c104581d98000702d450002c2d00c1c081c0c018620b4141e003000140300009102032a03511340c640d25000942410303c2030055440d8540001e00900a50000c0b20009680d0301e41c451085c1c8040d441c00800c4501c500c1c01441e809043c070760503118a48034203990f0311a0001842d0041c207034815405003980400455550034000c80c8500e119403200a50003505400b401140341c240b25481c880c8510b41c400502c456078102401a84840b04a5800b1880c2c508a02c0852001c18417588260010301c240b01e01c2c1701c030b030980e18003059007650001650745054142c01020900c001240c41c030040d010b00f00800c024401112220191000c016002d007441c03600c0b081100900044a5407820201c8041c5910461001103140500601e030203148246800e000b030a00600c48170503a84110451244121841d42c10303030144d05c4080d0159402011070352170805030107410302158520005500701c200c005001e1401c01103801501042d000080c40140d11849003824141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 520965809 1250 520964559 520964603
    0xb0315012a170408120d021b0a0501060902090607020607150f0209040e2107110604060801031e05071422020c1009110d02030c030d02010209030705010e0303070f0f15090201110604 79
    0x80b091b000c43c46400308900c10014051800030244501140d004103200c0019050060855601750030403501c65004021091542e900c54003130710b9641d501160070669500251801c0803055002e0710320170000da0300b81326114108102aa02404011000744c0d424403640a050220b251125040c000194044c0680e8401110504126000d807030402d10440000e6009041c440000301160007560200300014030751001481000400310aa052140e100d0910510241c41980c4070768542c88140541c0e58006240d0351422110342e61f0040103440c440c810300ca180b41040c21207807220042d602c902c2d41601e1520601b1001c1e0180d03145442107000f4203421496001d600e48007503040040c84030000c0c1041c0d0781131040c070480542d1aa000e220016102200741c0005030344246403801d050814150342d11140c1480418102407142e44c8002c8200c507182588243c03400c0e80e0003036518085510480c0d2780b90207492194451582081c0c2c2110382c5c40801458000d0320ba0009003e0ba01c9011640c558040390000d00010b0152078078581e00d115 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 520967059 1250 520965809 520965817
    0xc021011070b0304150b0d11062506021b06010f0302040b0406090c030501030b07110a11190603020a1404152f0115050a0b0315012a17040812 62
    0x60381068800940e9145101d41080e00180e401740d402c15000e0454880c05421440380c0c1ca0a80301c10b4940c0b50001c20350303484410350b1000b120402c0b400b5103070000358551881c0c01c1983c040c0c0c2854014011407204006030401d00000e4100350000c001d1078248840c682d120300c0001038068100e0f0074a00218180b10300315401d220260074104003480d00aa294540428031007120701070f03100b003045150b0b00050903624500b06242c0c180c80c064188002c0c40707a010002440000d01103403540049411500350304c20466100302045400113002d640100c1641501c201042c500d5043d0028100740c8000e546507043c1c51071480d1a81030502ca14030814034441c50311903030184c00e0344c0240746060804c0303002240000c4009851642c1170200c01f01861003440c070b1355288404448410f82042407409404183e0340340300310504010404259100280c61040340e40f5121400c240b56a12800072000030400d0103240300e0015030310943e4205007035441d440c00c6032986400520b10402520312011b82d0221762000e0300600c01e08041e400c1048031988 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 520968309 1250 520967059 520967087
    0x60a0509043e0a0e0415030206040e240a0e0916091d0a32030d05070e030a02090a090c030c0608091e0a021c0506180d0c0210 55
    0x6225080154095084894088010103014a904200301041500606040c10700d000807001c01003031010348283da61041041d42945019540018240202c00101ca0705804a500080d03100c100046c000c1603c05807060010301504c020400489850010701450820101185801d50414003201c01040369609079510290002a40416107003224591220300304000750b140c1040d0105910b940b0a6804d0b541d16030b02d851040c00a500250200c42d000b13070345d0440e54000c84009a04a1500550075810401c1c1c205907010300d03a180c00303003166030394200c108090000c0c2104498003404904200002034031030030049848034015500a0461300316690303840c0317400000c04008070241c9651008100c08000190302907440c03c0900032a4403890054504004031a24040b44a030740c52002e000c400f080c10520707810000f00c1520540c3c0c100c07102840000c1c1c1c8611441e4044424001404502c47c100c28032110141100355000c00c0d10310b100c1078a04100c481c200c2610592003200d8025040080704907140c041a00c148840c2c481d4007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 520969559 1250 520968309 520968311
    0x70224091203190c020d0f050301050a12050708160504110a0f030c0e04060914060d1106090114030a052703160c0b13050117010506030a0c020f120405040f020405060a050904 76
    0x4912a50f0b00c1040340c20054412026a100c0c0c264041c2d031a070440516100070380d1781e20700b0368910b604050202d5014800361003102c110300f07040f4503020b00700b140500101c000b9000040c205c404008180240407407005851141034002ca1405040c8060100c440301221690b01c030b03d031030302072030300082c05000c5008084044410040000703401c40e0103510390320350103418014041c41001107894014451452080240680064030804003c00b20100182d0b107030149403901d550803203d01c5d45271880300c00182d502d098000c10303844010400000308141e054503644418040c4110003d098200140490b00408444000100e4001c581c01444064490040216803052041c494038000411a5441520f1019034102c1300ca44248582e1480041c011075030f0004451114410000080c2c03247d51609002c05c41510000c1d040c85c00440c1c030340344400b1216008008103a600d0080c03400312025152001c402c1003158200780121442941010348401169001c0e000355025104010060740c80c0083d50a800e50b401d90104261036002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 520970809 1250 520969559 520969591
    0x90c0a020604021e030a0309080105060a0f0308090a0e1305060601021f18080406021b0d0b0c07030e120c03121206090702010e010c03020306100c030e12070806070224091203 76
    0x117032018059044410f2081d210340c04014140320b860350945500801d80790141d0b128a200b000403103058043c000031683c010f04d480c0d9031016074001040c0180816048690440700080030710443c501c0c00f500070210a0b00540c02e841103600c0d440c0c01280c45140f1441e000018201d445100ca581c4100b943c0800301c0c0c88054808020540000c6d9200c84468200c1d904c038401680104112401a4000c4d40041920b18012200d0f040c25110030b965048a0b80f07006000d00c1c0d0003510205c2d0090400d8081d4034080003540700100908020581441020341c2c80c03070f20950441c068080c038201c80c0e41d07501d82ca20130f458020b20360101d4420242d44020a00c904d410008007904110342d2100540c5510017001e105034045003036581d4025a032840d00006200301c40c1052640074040101a21200c00800e51040014810010460301500741c8008403550624284d0309801102c0c0074003554050002c0e00c0d80000d900d1100c9260100c0c115030b400318203c00c1d01802c0d901225006500e0700640b282d00301c0051924029580900311506003022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 520972059 1250 520970809 520970869
    0x4110c06130203060106020c0a17010b0a0f0503070512060a050403050f04030c0e060d1a090c0a080106090b0306090601090b01030e0d0206010302190b070f05120f09090c0a02060402 79
    0x150820540c0c0c1c1081e15a088001038080d03040c04d000b01800b4107407500040000c41a52004624220010303c01d10400034070406185e00040e02c02c0d00241c5031a1402040304507515202c051010381c900f194469184244100d000000d42d5051828641c056003c0010207002141d0300c3c040780070044c000042c4102c0400c5401c010340600141e00304040d03c0514014501c111059041c45403411031040301410f8103106890303d50840d00013903003a0b54006580c60070142480070719103030001d40ca8079011054006c00d42c003440010011400307940541c004402c940d5030502c00e11074a925a800d15440e854180c4203406140c004400500c50f126280d003041144c043d043c90300207070040d840720f0020306280420504900582000c0010429440c14070100c400440d41400400411481c081e580e2100e8401c0040c02040f800724050f00c0300501c0418810010001c481d881150350f5050740d82c0c00c03000264401c29501303108041e400d01189852168500b510404461a0000c01946c2c58580810100c004000403011710950306c0e60701802 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 520973309 1250 520972059 520972063
    0xa05060301091b05070b0a0b0f10020622030f14040522050705090102280c08160b0f030a0914100906051b0412030e04180b07080f0604110c 61
    0x100a02c12981e0003d0001c031038240c0010125610b41c03045040000071700118000ca42c038000a10341224107010001516075035000401c84072000e01c2901680300d1501e510921601d82c0216a01c1d110341242c81d960000200c1c1600c2041e02d54a4264015000803d640f564600082c064459075004080c04404e00d820035a8500000740f0f1642c85510506050702480d1240c001c0e6400d80c05140d420000c00c0c1407280c00d1049140000395035829580d1441d00f4003440b4000702c07400d8401c030104004010380222524040035224507005580c2c0101c41c01071800c4154114002910004c080d00b0303103405a0109040c20703d147ca030524403102034181c1d0501687c0d06c09101000d0401008108001d6423880d4441c03001040010302411700f6403c82d00000c1c1150020450707a00ba0f03800842d21602114165101801904080f40150808560900703030204403d80040c54840300080300c105500480303c40601c02c2c0a044095524403204680b081c0003690050400650f020100b8030301c0c9401d03002804240c1281409a00301914074038507038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 520974559 1250 520973309 520973311
    0x1e0a090f03030608010c0306180c050705010603030c1703040305091302090d060b040605120c0108091c0c12030e0a23031809100317030a180501050a05160c110a050603 73
    0x240440da031450100513805085c043d048001c6001e04003041040c1c03070500d1103d21400c80080441d003940d07541c2c0800d1603040c0640700b95031701a0f8000000704505512464040c01001d0b039100203440b2010305100c200c0890101c8421a845070354159109400c111103982403080b200d09800c44112125024822419940c0302c1451100c151801000041540c5111200340310494465410544c0680b0045d000c880300c0d03c5000a091015002c207191403240c0780d8401c10310b68140199184ea03500720b159141c1441d55400d40c00344511541a009040c441b5a0101d000801d6085508103240c5e00b8290308000712520100b00e10301200d06c200c40003c05020442c0c2c00140800d81554031207640100746d0080c0500007034150805401ca16401030400000d9110f039810368842100502424541500c038079800400984d601035940c1206c1e002409484031300ca000e51b018640b0700c0c040d0a00f280c2e4120045c6c5000d0016070242007440f0607000c4d1951940714000a10b195031105224907040e02c2c0340035004085201c0010341601e03610019 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 520975809 1250 520974559 520974563
    0x209040c08030a121a0a05090a11030103060f0f021218030c0304090603060c0201050903040b07060902100c050f0106062312160f02030703090e1b0a11151e0a090f 71
    0x30110b452508030700c4821a16a2000d0483d400317131005d10690b843c1c44030308940003071300c20444007201c0036076514090002074071308480c025040040201c000401c10071581c000c40c03d071174802c0d401444110000c601200403030043d020940c030403051081c00300d40d48100388030016040500110990b0700d4030903074401081c51a80a03500c000700680d0340754010800c0c06240c2c03044c208410503a200900c2a0305000001c26541d00075400b4031404000f00180784c1d01046101d602c041c1c095507018000c0d140d0101c0580c1d0140c160050203406440313601030024241034211061080e407056a03110b469512052034140400c0d02880c1001107500c101d10010000079030704440122419215011440303030380405600c2c1703a400503c002c170240ca451041d03500500100000a070024005420303078800040d142110340e19070007a441050403204041c00d5044000030340c01e00c4164805114003200840350101c0e0f81080f1403001505c3c4043c02240c0841d1281003103c40a0010210000c41e19007081811078045480c8041d501c428106612198003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 520977059 1250 520975809 520975817
    0xe1b03090c10200303040b190e060c070605061504120c080604050313060206010b0307050f12190e1f230a02030f0106030b010e10090317030114030a030c0209040c08030a 74
    0x403003040d011910900700024103c01e4059403d40c102a0f1310850016006809051156681c603503a80c1c1d102d04c40e42c040781040d0b002004036a42400c202c1074002840e400108152051820100041c490b402c00c074501800280c0b043c0f20b0380303140502d003482c0001012860138046410064503440010030000c02c0000034000d90145010b5030b550030501e00807841d02e011b1940003500359000301c3c00410070803840d00256544403d050518999404e2956005c0b03000344030300c900c0700c09809030403020b00c01030911011459041c408030389030030007001d04d440c0c594076a00c0380e8194030350000f8400e02c20207010480064008168121811000d11100c0e00ca98621144010307003203075090201c0d54003104102d00f004ea2041c15600604850070108402c09040f80002c19036100c918480340508005110790401e244540038138030045800c051103200c800030049140c0040d600a02c40e024004c0242190400c03a4a008104418120340c1030700d64081140700fa03402e120081400034004e8070840d2003d600091240411b2005004942895031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 520978309 1250 520977059 520977077
    0x1903120e030d0e250b1e0d060929040e0f06040b0403021005010305101e0204060903060c020d08160c0819110c01020a11030102090406060c06060e1b03090c10 69
    0x1444c54562080002480c13080e440c0071000241c1c40507600441a202e6001c84140d441103c98401d0201814040644054440000b00c1d404105410740c010170640d0782d03110b0705100e00c240c01511303916011503240c3e840036001c40d65903811800e4036240d400b11508500d000b0681d10f00190010300e00e81441d03411034094418005501c104020558180b01402688203440701c100419415602c91650b03134091190006003644c1e481c00e00b20300301c00e801211120740c441555025541c55442c2d81d80181801014401101c50606045c0c1d120286400480e9000f94081d90313a403100c809a0304d28218030061801100c2202c01d21030858210310125401307000400a000c44241c51036507440101200412001135510214882d8201209a581c5617030301080701c4141d01d8100c40d08101f0180ca00300040e0085c8194014103034803900d045000505103800c50483c0510754040d800c1040069512102d40c030300c0840c2120141214440c0440104442d4210b401540c0c101460008441010850380007050f25124003904840c08034141e40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 520979559 1250 520978309 520978331
    0x50603070e120a052401051e010f030b10051b0318010c0305090924041b11010b1309030801080313050603090a020405010f080d141912022106031903120e030d 69
    0x201c17400b80180f500340c4110b40d080100d202100f00e40c4903402920790411007058420b41007140b10350044c401503d00246141e0004403001c00c0500254001e001070b180305504500340900a22010065607485e0103015501c2c400e001c0424011242d20320034a80440074000240b2220903c0e0b00d620356028440d000b40e10400c548003103548080e0614210064038680300e03d0401c086003011544500081c0041c100605000c5601e440d19081c190150400340003c60700030f800d90401c3c0e2001c071201e82208000700c1c000d85629102c2d9885540181e128401e201e03419070880140c020400150404070300442c0d003d442901581c980750050790000782541c9080c0c0c00701c1d01c41005100f05001400080c0400400c541a074284180b620708144c03946a0303a030003170b1013000040d1044940b40d00310341e40c05101d50990f072905290045551741800894490305d080d0069100b20140455800a4094200010350390b18000c0c21140d005650703407650340e04581540c1e40070202c07490039444490308004150f0420180c191030300d1001011503080f40c1c031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 520980809 1250 520979559 520979623
    0x8031204110d030e091018050709060f020d050703030b2d0301020702011e03020702030609010c0e01080106201e06041a040b0a02031b160309050603070e120a05 70
    0x1072903020b125402a42000b400aa0054030101c00141d0549a0038003654a0344003140019845900010146404440e00c0942c030380b65501180c0714030083c0c0c40d40130300c9a41f20142141d550320300e0301c0000003682c001403200c69181d010710003502105100c0e01e800304030080c03d0301c04601e003c51049005003a000d100b2020241d104014151010702c544250000c42c100107440c0c00080c0400c19640510006203c4120b030f1498091098046030f110799000b40032a4040e0524039650303030081511450b000009403c2440c908410341c071403080b15048070034a070340310105a40c080041c0e052100502c03a4811491241041d4210b14501d5542003100b0246200080c029a1819090161103080f14403084603406145004110000d00e02c002c020b50040088840140c49543d0511202e501103603a0354254262200842c08e008940c2040491044c01c0344240d507039008065941d0b0500000e404140c60326004188180d42c030381100c1c10001c44520040812404445180b000c9441c2d0301e007008014101412282c84444100a2141c91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 520982059 1250 520980809 520980833
    0x3012c01060e1b07061410080c06030705090613171005010506070503040e09071a0903010b010807021b0f0d0b071404030314032503271110020708031204 67
    0x84402d801c910b61402c0c040c1e8550001191001c0c01c9040d001203021400c1c00340ba03038010110f5540110102449041c400c501100864035480b590345588160510001c00781082c0090700e004003110b0f102c69080110300300c10020310b5040307042c01d9542840c40c01c900007001d6031411901001d040c41e00d005013000b28160001c40060740c00503080740d40a80020041040007030400002c40b0300b110302d510941113454460f84286401c001d15079100e12082e14544000d04c003000d007000010965031808500070040b0205070401076581c0c0700d044845178007580040400308001d00174040c8141c0716500c005e0201c07000100c40c1c40018541c0c15801350540d241c40800c6c003084003c940040c100d10714036451901c010304240c40c60f1f41c010a544031000100398082404004102c0103a81c8480c00b00720460b90310420f208082d04040e004004100b04095001d00c11041501c101c4804400308070441083c3c1c115840b070541c040c400051200c00c2e80220001011807140d84c4001401a0041c4060304c00000c0b82072600b41c160034203040c102802c0007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 520983309 1250 520982059 520982069
    0x30a0b0a0b0910030504081614011e0f0b090a05070e0904050c01090501080405030a1d120a0b01050a3b07090303080a020c150603010b0402040b131a040605070203012c0106 75
    0x124185c2804085a024403d0310041c00900320641ca40c440c20f4a00b0b190490920220402d5640c01c060508034001c1c0030065a4984a9210030100086403407078032080f055907444500390340c2003000c090104099114030380010364080740e5820054035642e42c210128100080485083e95590001800d480076903a100c0302c1c1e20020802403038103413406e0605407192616441402c0440c01481385008800031640c0d460b501190454000030038036503120050941144d21007200382000c480ca4200d80c1d002040d2480c002206005617209124494909160391291585408000c610f441f400c80d0f100d05084240e05c051400d0512410b819561800c54030305e5807074040c0c003000c006010754002034010300c02c3d0302c010000015504408085141520295120200424010b21a00420300d811500005000c03815002040084c8251041da0040003030f500d0b510528030001c5092245d0700031140e0310400042044601c00c40c00303002628002000051401d10107850b403100150551005800720341441414030078910203200d9100109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 520984559 1250 520983309 520983311
    0xd0203190b181302060c0615011e0e04020d110c070b032202011709160801060602070b07080f160510060303211401080325080906030a0b0a0b091003 65
    0x2044000007901c0080800320b5840c20902e120006252200301e8810a24000d80150102e80c0c0c2e0007614014a03280c040850322000348842e041910350362944a0060040c1846204002061128410004840c03401c852030986621a03000d0202c0003508a241c4180c001c5080300c0000c07c0e54516151000a080c8802d0350f00c101c0380c0c004180100311118011004419260024120032100a00148016110310301c4100e9041803e4404008101541c880000d010314071640500701e109889a9800d003040c00d885240c007402c0d00580241c0800c2091807948005007222900c6427643e1401e24906040310300d4150048200450601040f444400505c54180512514840b00c208244a95030454801805a0031139000403248024400c000480b071041c683e01c6a40103017100d095010155a580c41d50701c0e47c0340c0050112208160a02000100030840c0c00b1101103480d5020740c490381880c1c0d42c1c8003004010b81005203801902c03519000103004540c0d4402d50b910141100b10b80542d10f80308208180301280e482c01500304189 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 520985809 1250 520984559 520984571
    0x130b010902091e0111010504080315090910020c030f0a0314220201050f090a0e0f0105011115190e061803040311040e1e0307030f050f0307230d020319 66
    0x41d8543c4145a034010070081c480800001403180125258914400b003114654a008140810025035a0046000742c01816292821310480c40800800c05030560750340d100c66005488c1103484031040c2c0c0182c00c4044158094a04110b0400115480c6a01c020740110000b80e5440c40301c41d01400c3d4081d06500b21403002d44008a01015204000d00c6004c2180003078144800407991031000c8140c0000c44039180740140820061554400503c3d200c1801902d0207a104e51064002103942c0d4030440303049145100710030003881100e0174a40f00040c0280040c3c082310340e80201010101c10241580141081000e0550042102d4507102c01c0d19014640c0552800c0c4554104020400220703d596003801d5000c201201c00254038140300000d0ae140c030700b008418020300311800d016010646008000303405050f0080e1112025104010720490f024420000d01202c903020078004541d000c3c1c4030705070410030030309440150708480c04450f000e405203420000301d860069400104029060510004003c1c043d05401014401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 520987059 1250 520985809 520985827
    0x3070807080a0b100c02061e09090714070f150c02060a1508030703261303030b0910030f0203010603080d09030e0901050a060c0812150f031609090c08010203130b010902 74
    0x40700304d2500c620041010720074001d8155602c80045071019021801000120301c6042141c0041c0e170050030f0104d201c0c8294400044203e8050079803400400641401e541c030f17090060744d4000721903000c0310003961803294401603241e03108217611440101800c190010811480d14000300002c2da448101c050103001078038003040218a00010540f100070303905040c50b585810b10225541c0344501400c01e82031650b0405000d0040d8074000c040e021074040c0c066a0180050070391481071003190007051b107042c4406d10a13460200003041340604c08106050cc024004a100c1e907407a00c5010040e00426100904555a10006800c0523044100720700e54001c01c0d45c020149602d000300003a62001c5500c220414441e82c51460310030040c445040300e503290389611016000c1d00300850111020300701d0846d103600401c07041c449690359142c006034107030307a00c4401c5210620340c0d0300b04451080601802c40c07045580112046010400902c2030000d94401c00d00408004141c01040c1098404100183e0258510901c10001052 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 520988309 1250 520987059 520987069
    0x6240801092a0503072601030b0a09060f0501080c01090b04050f03030d020301090f06080f0604030f1106040f0b16050403080a1e08100611030d05100b03070807080a0b 73
    0xc1114448000064074040220401d5041040b110310403149101114942e90301680042c00b45000304910b9407004000c101503000e010912600068040d8a84141d500400c00540030624959102050040c0400c001000f507845030240c485259560711520b440c0c40041c400000100440030360141c0901c0c1c025546417611135000c1c81b0344514050107003c0c1c008000000c4103610104101c0300c0c8002454001c55480da980d19a4800401c04158116955401c000d0002800c04002450800c1c2d0010310018041039280c90703400340c0f00007413140102d20170b210403400500c07020038027844050301c2140558000c1d25070130707454503100c44540d00003429607514000d0501c41d000c209604c0416a0b0035241d20080060380c03000640415602c40501200b0258500440111a5000d50384101d501c1d000d1006104450645030b2a5801074540002010100d480c079030091100b414003032181d07042207810448101100d00720703e8495440309101c0e801121101d01188003001800070159010341c289902c4407844c0303c01c104807980307000011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 520989559 1250 520988309 520988311
    0x260f03060915030a0305040e2d060a090204090504050c010f08010303050705100c020a051b0d080d0e0706050c06070c080706091505070306060305091603080d110d062408 74
    0x1401401e40c0e00008001c10307040c511a040c100402401c66013400c1c06072500400b42e900c180160b0845c0c00144000c507850350700c6050201d06061003201c0d0314182804001483c610074400034407a543c00301c90703a000012240c82c544018009003280c84004165454103080c44c40c80c003810b240c1c400341003201e0301c5001d4200360703070141e17030786041d603515150556540d07d035818598074040380b09408004d55440e102241c89101e030002184003143c0d2190f1f0980314400c441c0c2a1a418800c211200c0e650041d1014030840006403258009140440341c9040024170b000741a0382e0707280f070716086400082c046517001408012a280c10001c1c26800303800307850b040310354180503900d02040c1e004084e0003d0207241c8400c9500200304150503900401e1000310303010449464900c0c401000380955229a40101e4500f0002c149401000b01c0c21001e01c2d0728440710004130f10718590396254594014850140c829542d101c0200c60919181d006050203800d41c1400b1030755504060540c00e681d200580440d044034058004a4140c9810a0b038007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 520990809 1250 520989559 520989571
    0x3090d030e0307141f050901030f0f06030b01051e0616020105090411042d17030d0906090c091a06090a05030a060603050106170a11011704260f03 64
    0x90010854903140540701810410900350380360203032810124107000c642e4900c03190711104a50922906134500000c14824811a6006000030b90410641031b40e0350103038210071950380401c080002e55114945010084400c3c40d0421202c036800d4030010410343c6001f9032103403580a00140c4030302000902d40300040c503c0c89142403200e102e8000c0b02420056a002c0c4040e1105000c2c0900706100400345054801c04a60041c05101c011b5201040000900d18440b00c01c01000d604505e0005002e50411948440e91801c154503001a8801080803400c00140c90003400722851281c1c101250781007681c13900101c5000c55400200c000340c50b00c0c0d03040400381288825510640703815200d095072403025a02150f078002c020f4100329014031a140d54a810081c030f03980f00d0421680124020056a610307296041c008001003003d5090b82d0f80000c041e58003094401c440079403264014108449800200203e5100001c81150240d5546411500350b40109500c0070140840e410523500c100e00c0d042c0c10f892a004103000103004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 520992059 1250 520990809 520990819
    0x30f101d060409020409140f0c0f12010e0f03040810050402240c0a2406060807030f15060e0117010b0f0c0703240b01083d060201090c170309 62
    0x3081c0300e03032196070100b1000c3e5000340040c40a03460385e04241400c40c8412110b5034640c4074070404030340c005001240b11100e900c801000c0c8402c018a00003080030b800c00001c04c0820300d540c0c0b03c1c625001102c04000d0060f1600a0780042c580b128a0005464280724042c440c90700d00780c0c140004c000c0181d03101c5440030f83c2020200c00b80b4014481c1c0c1f2040010500071160600304038451401c00300240480030401ea00c0c0209400d03014021000312004000c155000e030b2080c04003041258010030000d902940040c1505c0024141c001440d0407009503400310188181c0c4014007041703014620301e1213540e10120f440c1e10f4034525076400020303516084011240e031144115a00545c8800318100b041c004082c40645d0045400802e8502002740c0400781c51500c41e180310130b40251030701d0514000d409500400006124521074176017840941030900090040c1d07280b41301070b11203590b6420304022040755401c40c1507010384a150b00015550703e4a00d0140c1414400350440040f400d5020305140c1c14503c00400c46000b00e0003522 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 520993309 1250 520992059 520992061
    0x30c1209051c0e04050109020909180f06010f091b02030d0e070803030114030f1c0804031b06020a02100629070f06020a09120309060806030a021203030f101d 69
    0x24900d0a091a0b103946903900c02110509041090303000f802942003120441d01006181d03a501c0c950812071083c80d48403500905600009054000d00c1e0b49a06420346c101c005642c282070381c0d40b50b0241450b80c00d8000704c1304030042c10f10038040c0c000c02d442191819442991840d0240661500180d82ca00034003103410b01740c685038000c0c01c90352041841030400401240003201c3e101d50311000e40310000c01c00c00491600a00c00c1c40c401948080000945003811744100320400c2102d00e0440d011070700e00b00024030650902404503594442c40003078a210100d0765009440042c3c40d42c3c2080b900906060008070312481d40c3d07003050350503c400148446036002c0d440304045507140c42c0c0c8001428403c280145100549800fa04000c0c1d401440002d03001442c0641040c1d90720003a503900c1d174001410800d02c0321750103400941821818042d10b40940f040a8100380000c0c226016403031964000b030b082518400c000641901b01105022440c540c25504540003d608410320002c1410440305240c0f22045601c800543c2c59108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 520994559 1250 520993309 520993313
    0x2031507032a031103160311070503070b150307080c1e031605041104060e1002010f0e030415090312120f0e06150f181f0303021c030c1209 61
    0x15000240e80012052807010300010080c4110b040c070b60b00442100440c3c2081c2008070f6400018080f01c1c030407841700584008414840030204c004049180040c184103c04001c1c0300c022620420240c40081d00c41e032024180b0b0318007200e02c5402c56005401c00ca0180d80403000502400c4404509034400900c107503000ca517108041029903001401202c9200d4060040c00001621030b0140702c0c7c1401a1041590f050100d62200c145d82e80b09071290b4410000024050188401ca80c075214440d4610f406144c0f001040e1413103811803040881c2d88803640880f8507400002d082040891034a40031340c01700c0c1c4e1424124021495a19044990001d20501008000341117001029020065000940728400c155003040342c05034020501350380300801c1d103c07802031200400d102031492a080d03059680e02d82c40a0002040100c004000b0302c0c2d800c5002d0050703c102da40004411549041e61426440194040e0340145007031501290f0405a020720402e10004050501c0f6000c107156070010409804008000c1002821000328 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 520995809 1250 520994559 520994561
    0x5060a14030613090507032109060c02030c06130306051003050d180e070f120b0a0504020913050a0204181103061002100609050907060306030507030b060a030b270a0203150703 77
    0x202c5041c6140345007135500001e0000c00640d25007624031424040001d2031034140000d158040b041801d00000d082c19500f400641d00ca0740350909011310280464007107050020000d1000d400c10340101590b0300d440c10703081007030000a001b21908840c000d17480c1700c2d0741415904c2e015110041c8080110900100c0c8100307400052241c1c0c0170720018072500005c1e50f42814114401001081c2c80c6120100080d901c03c40c0324400c2201d40b0601940c8000140080c038a54549003d00001e03400003104207a00004200421034101500e004003481945a0080142d85500300901e5403105001710042c414420318002c04179580c01c090004482d0020030413550100b102800301000c070300d040349041402c910070b030800c080050f4801e000d0b04003900602503201550b10346034865204904803140341c0310280c80d907401a60104040707403140400d580c10041c081c180c071160300c3e00c0ba1101c001101c003d1741c0c00e03200745c1d2031154031150803c110907411908081d0007001c0c103480c2c00e107500041d6448880b014180055042e90000c204100d0103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 520997059 1250 520995809 520995829
    0x503060a090203010303020d081e180c0901030632061e060d050601090812270607050c0a0b0415211406030f03031b030903160b1005060a140306 63
    0x80c401d015942e0b580c583c64000c3d2150402c0c00d92a002c00d80c5d640c0450b00150704000d070308108030013807044040e140e5919404801e00e030520001138141070007801815240350b216082e01a018500426010920301c0a6001c88041d070441005070f540040020903c8642d5124440e20b13503500306c801103410081030a0301c0c05030b1000030f00030a036042e6841136000500700329020305900324911900c000d80310724944503504d01c0381c20b494050190340d464499108001400a030059510f004903503003070449581e183c20341980049801c80e808a80181c1e5143e00c4002024610314202c00d0020140c00d0f61040d00b030030586891030b04200c3d0100030080740c0a005080366010703003980c044c0d441200c0a8088542c10300440501c000d00c840d800308103540c050b000c3d006104100551440000450b07000740718400110045025014482c2000d800181c95116140010048a0182040208011825402041d039508a0b0a0280303001c0e007401580c2e8403903401100203008000030b80303803c030351420920707030f128080e0b03541c3c84c0e41306c00000c1c4e81c00034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 520998309 1250 520997059 520997069
    0x10912051f091101020601060c060f09170304050d0f0e10021005100501030f02090d030f021204150f02010c080105060702010905060a111614100c230111090607030503060a 75
    0x7128070101c81d9861025080b8948503805442d114500710864401203803108401d0203581c010611043e040c400158241e4081001205640c0300061441242e60340c10760350081c0c4c0d100540d01c2c41408000d0009000c414801603e40603200d040c09409172181690103800c1192405403203210304240b09401864500a01c2807405010040d0b8041084c0d15240401000180403801180d0019240c101c450420681e03510840720051002802511010340c2caa50440c2e11040001a401c2180907080a280c0b0701c0e0340b42c001030030150611000104011100c2e550081a0040c18500c40d030440e81080d405807086034004448078103542081e5a0039907036090380c1c0016182c1c0b0103e6408145c0040c000642c0503001d0b5403041c0c40c01e0341003081c40c098039144881c0c4200302c105d90b950b90240155040c1a0100840c04c0d1070860700c07a05d15103089090402407000103841b05009180640328038182031020f4040d24203049020b11480c1110004c000340b06051035441008110305000b4040000c086c000008007290169441c42c0682c00100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 520999559 1250 520998309 520998343
    0x20010c090302120c030f0d090b07110d0804030b1e060303031e060f1c0201020106171002160602130302090601090f050609030727050c03010b07020907030608070e2401091205 76
    0x240b60414107070b88800d00b14900c7c000500400c4040b818840c3d10707088030300c070036004001d070f240440d140e80c20401085803c0340120f42212003008000300103201c14042510803804800300601030400d600041680c02c5005080702d10030342082003000142c0310303446000440e482002d103802103d962050082404030882100b082e61055555441c03485825490361001d1656200f1f9009001c00b41d615001083c1c201488000041c15030800e60441403035002d154060240b01b5050140c02644c0c01007a00c4400c201c1e48862003000703050781800e4051040d41080b648440d0000d9080c030701610b0440c03070724005160820b004d01802d44529000202d21229640800c40388002d0031f151442e80500c84010240c0c2485c406081211545040c02c040004104603815010f4030b049a00341d50100e40750481703541c04c00141c41401805d5800f41540c41c040820340d81c4d4200320b407a0103480c19135070040c441d00f401c400e11900a29503a003a03400d4884030035410059030b607210000504880f10347e02c1c01d03d908c0d90145007650806c1e83d081c82c00b1083c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 521000809 1250 520999559 520999573
    0xf09210d1a060c06240a0905071418030111211e090d030f02070b0105060901181203030b0d0c12060f0c050403030f0809060c0c0f010204030320010c090302120c03 71
    0x422404901c0c10b0141c0011540d100d1000b210130003490360500c0500b8003076400031550408200030500c941106500c40b00505d0074140d40d03292800cae8400160411110103210703d240403010005c6090034404c1040300350880e103c1e01d0a000811190110410700c9418940816219001050720b040b9540c450301f9042d2440c0101c681e05107030a00c0c0165848409480d00030000b810000300c0300c45242e0900c02c5404060b0005407091203072b82400700740301840d4000c0c003120f4100306000d013400d00c9142a429034a00688040d0f5842d60744a2071a080c02001da511b02340d4211310810030800130b1030010340c0160b91007003100c01107100d0003100e10703050034144002c103100701c481c02a0030300f444d01000c02c40380c0c002c000304256803203a281d550f001840d50b001111300e01c00450300d01c2d02542c0041c010031036014552014019041d001400c9501000d10303491a03600b0798110764011400301d0001d0384c060041c00e0107040c03198a50100b0320003c1055825110000700591102e100c003038000e042085240c812044207000409003000080c00720f07184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 521002059 1250 521000809 521000827
    0x110a08090d05040501050a210c0f0215060a030204110c03040f030c080607230c030408060a0b0d0506040201140c0a2102010b0904061505090f09210d1a06 67
    0x560421034030210a402480c54030707118240035006031400d80e6010303035406081c6069040141c1e481c0ca030580303840700d044110948407810702d502030007241c1a0302e0075030380c0c0c40488c82000503010340b810800a084071180100c4a00f0801291940401542102e40440300403071480d5402450452522032060400b5150100060200d504060b80116904403485021441d5065503551040d58940b00c06907810000103a45071442c0c58080d648c0071003800c24501420200d847c01daa0711f10220f00d1a0b00c1540110345907000401003122004441c800c868441d4000e40c0c00034031103813035590303031720713104c40300100001d040c000f102c5c090800c81c0c220b107010345100300a084112070a50520b42403c140c603010030f0117105540b030b111204d0004010301c10302926005d4400901500000d45983d500c40000d4000c44000751055080010009070603074070711052138061400c41c02080039504107100b01e141006038200c07105000641034803000790b84915038801c42e032149900702d80c00280c4280d00117203144a4881190041e88c4002c0c04250600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 521003309 1250 521002059 521002067
    0x1b080301060905040b09061210140f1003051009110a0303051b01020406020a020d050102120f1602010c0509040b03100509011e0501120f14010603060218090f0118110a 73
    0xc141e64980e1906004035a84a0402041d140861160368001c0b9240011071010f08044110200b180184000d0f5002200d5070400700d8115062004090102444241030002c0c0d1030000c10541e410024001c18010700c10708586400f0340c2c40b030310090546031b035680d40c0481d41c05105980ca0008c0150000510500180e0394909004040c0e421a1001440120080c4c6041c01c0800051007201c04071050303078010b40040d442030b40801c401c15048146c1a00d040d5000c21500200200280e015885a01320003840b8400e4248400441194101903000c0300a41e07241c00c2c80110f01d07541000988540010403240811010050300c0461700f014240d1014176030340c6d03040005101c00c3e0070040d000011000310300c03802032414810400c28403050701c40a1051004000c00c603030300c40c00494a49580048018001c80c181d142c4091115040c0d821944603900584030140c0c0811106005001c007080400c08000842d8042094100b91481c0c0d103405406100c2c04a6a2000041e044461b08049e0002280111150b00e181d444100c03040c0090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 521004559 1250 521003309 521003311
    0x10c030e1b1c02030c2e050418020c030702030a03210510060e060408070e06010f030b1509030c15041a04082a06070c140a0810020a1b0803 61
    0x106140541d841081c0105100c21600280400003045a03894210030100c21003040e1844809070f07094001e40f00d0b490100e4039a00400ca9420f44101ca07007480102800c000d880182d4001003450301044000c2008010300400c03444500200701d8207010060382d841c0100c2c0f04c0307841c62007030105c000d4150040740307464000e054002000449070344030800f042c0040c01d1841482e030100c5108a0300309881e90507200050000610900b400781c032551000e42454640354403140380500d0284e05903c51010340d240d01c4104030403564043c0310f6107c1c205190605014100380c02c0c00189110790008404c0004c100046040300555404100f400e03607682001d0100020003003806845281d552240c01a00c030383c088203800304080e46043d071085078210351555018000380d1201888445d800800e00304080030005041c2c000114a41d80c00c001010503912940307024a0291034042007455440c840c2d10b160b0303c10000380d5020065130401203100c0b2000e01c45200010b0741e840030080f0a070340e10030240000ea12840600c80740b0301c0411003114015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 521005809 1250 521004559 521004581
    0x40e070c05150a0615270e04083004020d030210020a080a11040f0905060f09010605031504050603030d0905031303030f0206060a0b091e040e0a031b02010f1b05010c03 73
    0x9101885d03d42e403200071901a01803d800004140450700e59242d0140e151000d484640a8489a5129940c800680341620180d40a4078101c0001a11030319800c4c4a00a000c00d039482e03c1c2440c1050960002d50440090000704081e009400980e01e05c2d003010701c28031242c4402c801e444411034035183e007802d0040c0070140071151009030f589042c0043e40746400041c196001c0715885000717091040c1c04d0402034000317080042c0c041508150b40c101034850070354030a035a460282c4034560700c0c10307224034041c0025580810b0f0a00c0e013a001d0303450300c0e050002589010007120421100050003003045d807100d00d803003031440c411598040c0e505160450080100740d40b0007242e0383c50f079000e0750840300c141c0c540d24200b20b103ea03070f5403240440307940003002072072824100a9040b2014812001500100503841e0003c201030700c030025100400354011040e03000405801c03c001509180d1001105a0700c180d1960010b005402c04181c41418084110301d40110b880340c50302c203aa202da510038000d10100c0d0b80b6500c050302800050002d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 521007059 1250 521005809 521005811
    0x50a061409151903052a100c0605040b0717160e01200609120f0a140c1006090f0b03060703022209050708070e0307031502070605010e150102060903040e070c05150a 72
    0x11030312094401c040441c03440d1382e01196490f41001c04000c00001100c3c050320751050107088d40782c15020510900c902071042d4040e2122141c5842c04e294000c0c141004c090600421049910034441e9512010a51640c501c5007401d08010510b03420005a83d0b00c004005968201006141c01200c2c0c0500425401d008102101c1190320240c0080b03c2a482406481c4004070480d40502503031060703600c5246404c0480102c40c00551510591000650401d40c1031000e052115880303400811a0f480c9034814480400c04000d0708010140d4400001780d145c4201030404400c040d00454001c03960182002102140480c0c40207020006a03260400000b60204668040100c0e00342c3c00005c102c107010b00f00b4006081001030140c049a801c503600c04103584402d8008040b120790030f120042c0094060310440340600b003e15000c00b0f00d840c0c03174401c010100d5030218010b41150044018040007140c00400d0703805842c03201100e41c102d42c5e41c0e640202c03564803599001800030310641d54021034415070a0354680c003800381241c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 521008309 1250 521007059 521007073
    0x30c0703122307211d060412060b120f0c031902060a0c140109050a020f0a06090e070e06120a0506060319050a021318050a06140915190305 61
    0x426691410403000c95080740003440210040040104028480e80344140030060000d21030f01e2400c4c40c0d51088220400104444018640089a00d03500044129401301c5249141c241004a0110190500c14004010b1912041c528609603204410407110172011003c4400c00302035442c80c42e5603500f1000c0d049001e400354a41c11945008060341c0304065903000b0380644d15002c102c0c2c508075200d6040c04401d49000c04a003410507090a0300303000f9017040502030401800c9600d51401088441210900018824018a501084615002000c1808849048404c450f0310360701c1800c2514492411a0010741c044030001d000d0704049074400481c0e01402c90388404011950743c0b03038280035440c132043d5403c1402e206040c1100d16803090541041c8d90040c40c481e80541850124405c201c400f80c06a0000790a0b18030703059143c098804940310700380d4803941c041d030248a036030301e4451141c04452044035268040c0315804001254007076500d1001c2039061010300901c0002c04d03500c8801d114507003030703000858680c0110f503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 521009559 1250 521008309 521008343
    0x906081b07050d080a0c0504030b10030203011508070b030106020a02010f050706050a020d0e01050f1501090f0303021e0106060914041d03190e0612040c0e010b0a031b080a050c0c030c0703 82
    0x3104a031006c01032034442a01c0c0608540301c81c0030030340008003800500d595051000c00180c8007801206803201883c10907038a902c4c02c4c1455a400e00c0038680007000580b030207100401c905940001d99545964083c02d11780a021015101100c580c0b00d1400094650303400c00e01401299400ca03030080000300c480c1c0d0400c222041a1448a40c243c86003aa0036000000220020a4101c444294031501402050404240d2240d03560011a04114240d2003500560881e050f00c036148005254451460b80300c0380000c200d8142007203c05050710780c0f00e001f0040d5400b03510508002c030f612564459a010107201034010380d042c3c5800d2699541f039012204400c461600d10070074070f500c64000c07104080d01f004000c06013420140c00d04201e103805000200300390b07841c040b00d420000c0d000305070b80445400780c501c0c0c0d0700c01390b44c40049401c05030a40c0c2e52600710b070556103c0100d02041041d0700c2514207402c9503441e42e0200381521880c025070030500410f412480c6038040000c4109644030000381c1d10089070310540d40c480490b0174031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 521010809 1250 521009559 521009561
    0xa17010b03013024050108030909090a17031e150f0409020618030319020a05010c0f0f1d1e041a030607031e1406010905100906081b07050d080a 63
    0x808100c0f10510242c8001000140300c82a14403009003001040c144107040c01c01301e44055803007e9100700003c0c0c1001074820640d013801941c0d40d91007401c00c0001d012a03102e5070b807400c00d4100c8010040e61204004000b00b5401c3c0d03240c2e00400700b041d024800c0040b03e1704004204031480200042c40501c150076194051000c0d06007802044d1241e6002480c050600d85000541030741d1000300b158042d07040c00100b0008256030900305049882400070345c010b1203514468030b415401c4403080c100f160240300302c0400700890241e001251580c15022490072401b00240881201c0b000f082c0ca5241641c0100c0415071541a40401402001580021981440111011f040048120070480311a54064220300d002920b814025040400303140f5030701d2400442a0000381c81101102c400e80c6c40c2440e1110385c2c3d814003059603031140451000d07000444600066484c50040980a0f910300e100c1c503407e000c6040000359503d44032141003980031044801d80c95444105241c925140c2c0c41520000c0301007011003007c00d80500300c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 521012059 1250 521010809 521010869
    0x100206060a061e0c05010908070f15020304150209041103010b0d0b0a080304050d08091306060314091c0c02100e03070b0c0604060b042c0127080a17010b0301 69
    0x50390407004001c001d140f40c115450215400141c030b5541d02c1f043d124002030a0b002c01040890b0094807121515009403074050381e040c208000d40c650040c014410701c40070441c0b540141ca27000c0c903103490041c0d0324242003000ca005011a01c40b2041d1424012000140311000640100400c04100360108585401c54080094241d080d020b0186964024802440f207070034401c0450b66001c0c0180034803401c02002c28009941d411000c01030f100d80c180c45a008001454150207400b03083c40e0f080200300110300c0c110034903d590303400340c84840c0c2d10601a440b030081d581e03018900300d0400d00c0d000340c078003c0c1020301040d0140c244800b91003198068464090009000e1040034140d80200d446400070740f0b8540c9840c1c60360800b512a10380381c1c1354010398400301c813070080d40110040c61074800015520f104120f00564a14210341510704101440003642149003841c0304070b81000d201040c0d00204454072022120400c4442a101c1050032161084050010680b4020907015504903003048001401e882250140b030004a01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 521013309 1250 521012059 521012087
    0x21216051903230105040317150d110a05060708040e1b0d020f04080307030e0109060e0a1203110f010509100608100903030b0a090506040b06070302060c0c010902100206060a06 77
    0x9842106000041e0341c4035000007000203600c41e0f0064140240300c6182100c0d4180c0b81200440c00c9041c0785038624040740c0300e00342c0c0091000c4c0c0d05000c608200002c2060b0555901c401840342006c0440e040007941c0d8030100ca0094080a01005d440305c4c0e0038030f0102120742c05401100942c0b81404001580079a41e00b1a9040c800380b0803c180d030401d582091601d010390030080c00040c0e1110306010119400d8003c00140a83c14000d40d5000d4001c44100005031101c90290040420404050000e001c152900d42e403500c1250704210148040d0b1031142400c941000840f02c1d076071018024140a010300c5441500110301410710f1009950450021180c030740107c8885218950154004120100c000921030380034a00860103400d010070b8406943c00043d420900640201c8a41b41d0ba030400c0c00418102441102038198040c1c03034440c9400c0782510007075600c00c3c0c000c001c1000c110740001c03071035075940c0290061020f807036000c2c00c826185800c540c400303500c43c00c0482e06180107030b41c40000002c00600c80e00c844106a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 521014559 1250 521013309 521013349
    0x42702040621080a090e07121103070c0b0415090c090605091006260108031b0c1f030b040c12141b0c0f0d0e10031e0e010902121605 58
    0x406556070f00c0b0b50039040401100d09000c005034000a6a5694681e00d510422852381c4102c205403c40808100f154203031440c050305841c0900c10803031348513049020903900c950000440d040b10303503c0d0b00d041c100c070003428003038214140d050010032810000c5400800302545d60640040c0421a12641881100310301128044d003012032021041061030301079040d9030278000400508403d56000c240881120400c20307400040c0b07a078000030b0103640340d00f0b02481c3c1c40c00e0010010045d2640303aa0300300006007007040c82140203240080300ea90300118540281c0c018203410300c015000b03011503081e011015103045001002442d0741c1e0300b0810706a013107544140c03556110320350480003481c1da000720800080c0079070007051210710075205008000c0fa0403d010005424441c8a5580f14850000a03c0c140b011101036000710005050600780c050450210144017080208dc50000020b840c4902401c070034058880118003035000582c4400c0e03411b0984010446c4040307800100c01c0c9901d0103544105100310001001d035107404403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 521015809 1250 521014559 521014619
    0x2070303020d02010506130e0a14070801200703080c13080303040b0606070f080c030c030408010e1e1b0109030b13030306050307051f020a02120304080d0822020427020406 75
    0x141c859101149442084044801c127203400d94502060a180e07541000c4c2d030340d1140c00308103c450000d0164000c084402072813524403440120f02032010b4054050700605006003100040c030781c2d0310030301c080d280c2d921400c80010850030368a040ca26269401030b02c041c0e401d0068000007641780c1c2400421039158076400105000c2052543d00e880c0565080043d018801e400104034900215034200041c2c0058a4043c00002d00d82c03120114007464000b002d030b007c0c3e18800c4401d000d10083c800110380c4030700024801807101118603100700104c1b41d07040540c000078141c06400051266094440035000c1e01c1501c00d4070300304101c42d01c40c4101642c070880303881185d60003403104850b0000340981c030003008448e51241c0100c4403003100d20750001d003600841407401401ca070b00204d01000904400c102d81d18240d00035090169a81c01c240d070076146800b84080700c40a0070545000c44070b0440d1550341c050f1200490261840780481c04502925404404910003613100c0e030b0614001240c0d100d403040c0040581039010301b0300028 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 521017059 1250 521015809 521015839
    0x1209060f08100506040f171f0b13050c0306100318080f040305030301060c060c0f0806280f0501020709060503072709030804030807080609060618030d02070303020d02010506 76
    0x301d400000d00188488104000c0001c030703500d81601400c090180648226009804c0010482c540740a010306526180d100303a0f20003070422004000d0844500c004200440e4444804000c210f231000780e4014040541d00d00b004020713040721110040d6001d080201c0e48402a9141030604034203035000c0303141000c20f0041465049001881034001415111720800d00d850500f55aa2240e03070858200b6400040814051140001004600d119491000c803250604c00040e5504440040200d0001811680254032020b1805010880ca1421b4081e031803102140302101c50b02d03145c0c01200c2c05180e21415001d80b00d0b2900202d1540140d01030070040d03e00c00350040107442e01c2c0c52810484200d01609281e165a02d01109022143c01e6000c0d2541e04c0340a612110a83d08051800a12901004000740c0c100701180782442000e548160f141a00444101c6a10361a0003023528104181420040c0a55042c41216000c0a00076008500001140d009809460400c12500b50690a1b58012900c19600c540d00f5601241 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 521018309 1250 521017059 521017067
    0x21070b282f070302100305040308130b0109020a02150115020c0a08100902130c020109030801050d051b061b0d1107240e04020a0914061c090318060305041209060f 71
    0x100700700c485421078588680d281c01040c6910702c02e000c0040060b449100300014590400030301e60300b00d20300024002d418032040d01c80100c18201030140021041d00020342c00780c114401c002072052441c1d0010072009a5079207000d00c02c039070321040c00850090b002d01c0c2c01c400100c1c41c22103088800c56840c032000d404504d80c1d003034185004002500d0708903404440b1255240700034402d440340407070104640e0000960001d49040241c1041016800240b00c0c60800b036902c000250003140c840c440b407540c205d0100e601128140014803500500658042c20880703c98070104403140042d4000084000e07032a404801d000001a140c1c41e4007042c090750703172840c40079401001001d580b041d00f5129205189007002421160340001410390703202810100005008160078007a0b07080c010030f1014289811610607181c80c891008881c4060750a40c0039000480d44c0b03c0c0e1180a043c002c0f00c150020344840c5c036001e4038203612101c0140061070309581c01d4920050340c5c0c0251140c203014186a405850460319042411650304204031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 521019559 1250 521018309 521018387
    0x1021215060c0a0303061a040302061c020910120e0105131704170102030601030e0706140904141e010609030c05090709090e030d0f0b21070b28 63
    0x341d0488020010b56018a00900020b140d040c425038010840b070703180624554a0310002601d00c1e814260802c400c1005927548800c40380c5001c0c1d041c4160000c400d440c03064500a01030b03109001d030091052020943c0c541d500000c6082c24804d00b4600704120384070304405600725142103c005802402c01d03140708003c00c50480400d1014075142e202980341c1621220a00040c01c00034058419581d004800d20580350780601070305280040c00d500411500c0d191640041425103090460072000900140b90019900c45030421f455840418614070400d0410700000031441200502207803030984420000303d00280b10f501c2940407690012214082d40c0e06140420007204c81c042d10f14824040c0c406000250500389001e01503007405410081c6885400301c0d42c2410070340f00042d211740340a80c030701000b42982e65038040b80c2d44d0540381c03101110740e84403444240040c035180541c0c00050524001150f501080790403000e200d04d544400c0a03001c004d8455600c000e0340d0f07a02c04084200078511100e4101d90380c4200307004200c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 521020809 1250 521019559 521019601
    0x21c050c0f1c0612230c151303030503040b0109090807080a020109060615020d090b04060e010c0b010b03161b0602130f09050124270e090c090603010212 67
    0x12001c011030b10b40070400c40340c169100354804560201608140003401030b1000007144403c0200c0d80c0484403440054071354801d002c005201e03080d83c0b040d50040484850598202135400d828080d6000d85a06010300f0300c0c0c004940483d00b002e1541e0020a44140c507000c1e80f40107941c401242400c0202d165115622600a440300104540da602ca07000f0104103e8020756004201002e1000a030140b1000d0003401d000b508000c000070700001d10760030000803965070121411100546812020b035201c0c000100d81040030210050554070001c8004180313804960000c44c06518825519100c1a959140c25a200e00c42c046070348501c3c0c050781d901c45006c41c0d030f41d4004000000ca02c56004001303d4903a2940c40c05034959402c403501043d0f4420050107529070308401c031108a013100c21a801900c1c00024000d1804540e2300161901002a00040b41e0003200c2281040c0504055180503c1d24039000070415529050201454400d04021002c07401c2400d0610031a00d0b8146000858035160307540c410400d00b400d000c8415 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 521022059 1250 521020809 521020837
    0xe091218120102071110020312040803040507030b070806030c040b01050307080406060b0a0c0b07081b0a1b0303020a080f070e04020715020a110606030303160f020a080d021c050c0f 79
    0x2040390501c1c0207100424041d845203101e0007007040b082c801e00244285048122055510402c0483c45240b1b0304002e032584203502131103a0345d0301d94451600a0404c0c110740d0005045d010004240040541c004001d82c0c460081a01100d0748050781c1c004010550b480c02d1121404550708102080c807141c412200903078400e0041c0004900b40340d582946143c0f6501c11941140094507a5802c3c40811100503003281e040560b03440e00c04120708000280001189070b00d080c0700e4072002c0c00580c0720f4210740142c2d021201d00e041c410200720b19100ca0704002d000707540705562503400941880006401510701c000620300030841e0780d440e000042e4007001400025401200c040c2d40311601000c117940f003c11180010400c480740ba55914288920300103441e460050003604030341c840d420a00c10880d460030100704000c2c60002da460090300444070b2460690074501c6c1d50703902502141e00011001c000720060740040c00c01124451401203107000c8258075a0850700d043c0c0d4403c9041d8400c0101400001c1c81c480a004502107203e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 521023309 1250 521022059 521022079
    0xe09040609080c0a1104052e031e050f071401030c120c0c02091e060d020f0a240804150b210d081501120e12130e091218 53
    0x10b61807001e400580305031603c0d42c040c289110400241c000320109400094805004a0810344000144060031000031008514107501c1d54652180c0000d03800c0086030480b04a01d00c0d02c03400003200e0101039801c1c9040e41c0b1403182d021080d000001c000b886c102106c1708450030990a20450b00110041d00c400c01c1c2081c10482c06ca0b841015200e268481c1021103015078451016251051040c0840501c00400e02d03141414074131525542020814002a400720044400d0400b41e40f4510001d01d2080b100da1a0701c1e00045510b002040301041c0b604034250107904543c0f800100380481c0011544108102e500500000b1041d500a042a0032504244501c40c001020f618039910f0540d080003401c0340e000100b81d1a41d0110703035200da80c01d8002e0102500b140358000300c8030842c014000080d2400503c1d07421070300843d540d10b9181004043c00d021150f040f04da101d040d42d54405981d560101103031000d009801c642c400140200b801c840000880800640041c10b5450400a15410385100070a4981e142500910940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 521024559 1250 521023309 521023313
    0x907140d0213051005030103081806041734090905011404061e181101020f0d0305180703031205150a060215060108060a05041a090f07120c0e09040609 66
    0x4000b030502c1d4155403020301680351401c0b0801294104100c1483c0034440200018000705076030004642c0d801441003d000c0c07401000e6800700d07000344500d0340305006694a0036403107403880700007007114a264071500501d5941090504819081140400031140c01c4181d5850200040d400603000701c01014010360001500100411507a0000c90040300c0480d0250383e260000c840700c04059840503400c84088504200c00d282c0804c1000e100d072081000903103800d8410000c0940341e842048400c40204a441c203482e44400c0140018000e0a010f440c0c42050113558650182c02c128002061002c40790550342e0b4181030025450241c0040001a00d0100005210a00c0c0320440c2c40d904105001000513500030600032074600700e080034000c070203426641041071100074000a6a51804400c0c00c1d2401194000f5050300612070403034072400d4504580d80c0154640c0d0400c00ea0380004154188110300e95200e01c1000310701c07403603003504071040d4050310f401240000d4201c82d100e08240740c0c420760043c410400002e4100040d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 521025809 1250 521024559 521024561
    0x7050f0a1a0c0d05031303051605030f0c06090303090a0f0c15090608061009060f09030b0406060314010b01021e0c040e061503030c070b091f03020304200907140d 71
    0xa0100d401d0310800149140c800c0700708101841c1524000e20b4002d046041c000280310506204c0c42c0c0140800c2800315038030b448820000d848000055200003240e50f64108082d05107111b8022402d60303d0f19010b000b000404807000482128424485840948040283d41d82c41c0040440050410b48500d02c0043c40402e407540c0a21403841010745130789070200220301d032040040001d0700c0100214000c0c1d1900c0c40104240340c00c0080c3d8002c0e0351207418952075859045404403039010540e030002d40f841d482401400284141c030783c4004142d90050b4018442085240012801e0318807080c18140141d108528a0121902101994807aa1102001d8034800b6000100040545400381c000c40e02d150800e1044c0022000505500c919000f0141c002d18209000b004040361980824842c072010f01c2c81c00610807909a5514444444111511a0f032110029951000500a40044a00305c903000d2003015100f0801c094172241c582c580b030000b04440440c0d40c44000481d0003114403850341034804028030002d0701c0d51b004d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 521027059 1250 521025809 521025839
    0x40803210108010902010c030503090c040513050f12040b0d020405030a140f0f07150e0a03050d030c080603060a0902030c030106030b0f06060a0f180b0406031e05070207050f0a 77
    0x2040300c4480351050a032000020381030180c0c422525a850310b00c3c03500050b60001c001c02030041c1c050134000d440f40e840c09501400c000d40a101d0543c050300e800308000f2a00078003c80c0c1611240103004807110304189010080d1380320075410440700c110f2000e2100304042c50300b20300106422207a445002d41419900e80103e031074075030004c03021100118035100c101c04000042000c04001d420480040c0310f00c80580c04643e854038011300400f8000c04882100e02e80c058040c01100c0000030000e030680c2119541e90a1441c0c4030400210f400c4000f90500300503100507407041450500901c0004c010701015118a00d00c5001030180d000d003241c241c0a4000000c040395000c0c45a907005500a4080c440c00d031800740f054400d40e980007042e5620540f4103101c0c00f40c0c00780c0c0c4a002001003a015040621b191401c2d908540c14a4107180c0c01141e102c0d00000e8007040003540354002c1c00207804500100c03c0c1282d24405800240e8008030351040040e40180700c200043c2c80e0200241e1103004c409406c5504c40c076201c0e6014600c84d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 521028309 1250 521027059 521027077
    0xb0a0902070b160516020a080f0303090105060619050c1005011205120a020a0f0804030b0103030504080c120c0114070807050a1203140606030406021209070f050604140d0503040803 79
    0x5808a102010b00c180c00121562107403004032641d141e18010355014109000d00294a1001300c039400c064811034849500b010090489201290801b80b0140d4400e03540f640103c911201c25400e14000c60324504101068034102503042800250070310a070a01180c0700e0304902e00b290384a100740304104810b11514850a4080d05441c1e0442d80b00e500c4604181e0702d05024458400c600d40004c2103000d08907940410f03451a81c039400a5818001c90700c44c28560b416000c6c44d040030340403240c21000001019000b800800481e142041622144d074035080030040301d8181c107031943e0401e4002405156443d80b1070714550450428150115003014810f440d500ca49170030020701100c85034850349284043c4003614100c2c1240e91a28502407111200040720000d800c103004d40034501804010010070104402601524118446501341a107a860300c000c4041d40c54440c1c0c030030b9009040c0107060100342420900c084800b55107a890080e54223000c0d91307040c003101d0503402005031402c1c0001e01c40840e40c0f02c2d06000600241d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 521029559 1250 521028309 521028311
    0x312060f06090806010b190c050f01050117150106080603071a0403030e060310030633030209090111192714090403020d0c0c0503070f0305070b0a080a0b040b0a09 71
    0x2420901e002d007001c2125048001c06600500c010001d80d46241c080f103100c092000c0480303e07010344420007595040c00e081e03402005070203039070070b015945001588014101c40901c418048030384400141c890b2180100000051841c056500510100e400b582c00242c121074050103c070006a540c600c804c4080f00c1041505c0401c001c005020014154803214650315100226040c61031400c0648400c2e04c44043c1d84030007055291100070f0b41003805c21115100c00003c5010541e82e504651042c4881e42050341400300300c4c0701c1d144102c00300d42403840c1417142c0482c03204214030b0a86407071400d060000116135480d6a000400c0080c10103040750105004185101d0a50748110b80b14090401e4602d03100030078840059402101f1039000c0001082e400a80c5c0110030045040825860540c1d041800d2280002d41101e509480340c0400018640d01c0c1d1214141103a000d03000703039005543c403284940b50318414011030400080c502e8020640e4140180c1c84030031042c000500010b400d404420200d0340380032607640003441c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 521030809 1250 521029559 521029589
    0x2109020f0d080d0605040e0307030c020d150b130b01020d08060a03140d020105090312010b030a09050607050a031b0f0f020a121d01030e03030c0d06030f06230603030702040207031206 80
    0x1003d40380941005454104c0d001c1c403412240c0c0b044141da074003503031344054100205414141c0541d11354070401c410440e0010302100c0e64018295400e8040e0640e81100790007155440701d804c071100e99034441c4600c0400141c0c0a46a1404191003c0f0b03811000607003120b510200c290800070014481c0520080d030080c03840f018240c240c1c07048001031308541c2c0c000d00c440700701e0f00308111101e4070404480d40541560f81011540b0b4803a122810290001c142c2d1201c000d0242c411032040c0f2241980100180c036039525190303800d02030000030388880302c030720089240d00d5000b01702070300c2c1090b400c03d005041101005070288111501403082d038a4186040c42544101400300e010701481036440703c000c1c1c080c281c40e10020b003000e1140b0460480415501e101c0101820a2130b20081102c145980c0d860308940d006641004040c000010a428010700405040d007401c00340085807400144030301800300c1a43c4c030920340180030358146041e980030b00c03010354040c2c02c1c1103040007002d01038034070b018440344501c034041c112141043ea52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 521032059 1250 521030809 521030827
    0x3020705120604171c020c0102190509031006050a05010305060607050d0f0f032a05070b010b2d04090207060b0909102d0c140a05090307062109020f0d08 67
    0x2a00031010013074444e03a030401c2002e10200e50b080d9000e08401d07000700e0040c4c3c0c7c0c00c140d00c070381e50090085829407643c0f00d403071200829015074004060842e60000300c085d0b0b03080d030b9000c030207800c1189e115209094016440e400c04002e6580241d009030352050003d00240c1c98134899948590a0402c1000c800010805100914600a1380180c8541003025103050030809400610110b4068207007601c8404a10b911280c6070120040c410f20640e1025135100c40c00c002c0a5031a458880d00d20741004060000714402c400b00c010307050002d40e16502e4043c0442204c140b82c00d0400d0403000196001d084143e0b0707981c1d122520560f0f01d881e10802503100700105009032607801441c1024805940e1559221181e00c6007e0300640806080c4502c07120807010351100016684010000541c0c2820b00c1c500300900c22040420440180c2c1e422030001c1c889040301318241c402180d01e0f26010354034005044440c04401030089016000301320340758048640700303000030300c40b81c000740714131000a03160750b591441210704182c08100c60346c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 521033309 1250 521032059 521032073
    0x41e14011508060f1212031605070c0e0c0403080c0606091f0b070c09021303213e010b090f090a030810050405010306020901020c03121603020705120604 67
    0x2000d0500c980d00c1c00420701412000805200d03018021a00c940c1460098420a42c0d0380c00800c64085200d4050383d0746c5c4250340c0034864440c0c20440345620070802c001244a201e80c0700d1380071505801d0348800c0024519091403041200e03200c0c001d001d000010820440031000c55050b0014000034550180109002d252002c14081100340103407068104058143d0889000025000c0d84025140c031000305035222149810510020802503202c080114400034010416005442c01082170340d0245400c0c5d4106050414000410011220803000103070054102018904401c00d41e60041001071078484400045044041804c0c0700c00b074103542042e9560041c803856400c000303500d154030160841800c123061030040311081d202c5400107001020400380e1300025000803040e4220001401c4040c10422456840e46800c000070b5126000c05400340c42003085d445854500010f0454428485420319030402070030882400b81c00e000f4a80850540c010324201107010b403a02c000403084881e001c4000e2240d8140340c18034239 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 521034559 1250 521033309 521033311
    0x31b070f02030d080103080421060e07051804030e0d08070209101a03090c21010606080613021c0b1513030c050108250c120908010b01050418020702041e14 68
    0x4060184c00d1004101150b4000280c80490705900100d00110810100402d0040300090000300704500c0c110340d600201e2800112582521002d4a5118401c0d940e0601984500d0048800800041c05001c000c0210f04219040303444540c46241c5940c241b00050340000c1001000315410000c0741865402044000b0b0f40000d1040e140001c3c005540c61400c088040c5521903095038025809204100c070b4446c50034201c18005002c40d000c1030003c10056448203401045094181c4049109461300080000c14484604c01c0718426100c40004040d5800e03490309080c0074003103103002c00e1ba2000425034241c0d03500d40420010300600da414024055014118030f403030000100c95400080c108407081c2c0801807440703c0d8044000da40b00c1e5513000b00a0302d182440c000c035520705000000501400f5041a020003443e04500c4203400c1c2c450540091004c0c44807030740110b40c10700a620442102c0c1008082d5a2640172080d402000310fa8005000444d070b41c508001c031680002ca410190040440d55984600c03d80c0507030080e25 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 521035809 1250 521034559 521034583
    0x8060118030203030412020612010b04030209060f010c2411031801060605030c0d09080a0206060906190501081f06020708190b060f0a032108130b010b031b070f0203 72
    0x48803106086401207a545d001d01d010301e903420381c100d0594106551f0f80e0400e446c0003000903501c0c51010f6031650480102a00036100480c098445800403a6080c035100c204080c2c0f02c0301c10303500c02c002c0040c40c2d1075105940358141c4480ba04200b1060600420311040d001d00e100c0d1320310500d40c00c0c2e5241032000c0101c0c0120401c80e00d0400b107900d800e400303000c3c5a900404998211140040440e203503811242960000e01c9481c0004202450020b0030000c1d4580110302c05200744001c41c3d4940f55a03072003030240561801c1102c0f50384001000b100d801d100c02e40c003403407015030060041c3c509403000c0398544040d100d03241c08542051000d6841000c1c1003018031010404002003030200004540c080700187e990500d0064043e000034800d0805c50302c0c2d41003903180d141700e01000f503420030303607061040240c4030070b02d510060f03c1c100031000100000b0010f001101d499020a0348603501400880407a880e15100d4266078001908580140500b00711880301c0e851940081d2500c0c42c081c02d001c00d0001c070280b0416203420824000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 521037059 1250 521035809 521035847
    0x1503021e0315120307050d05030403020f01020d06031a060a0b0d020d0c0230040302010c110409080c0d020c13021e03040507060e01020d0f050904090f05010b0f06130320060a080601 79
    0x1070f8000040007c40c1c0c1d130340c55083c941015601c070380b01d0303160503410060b40031760410241d88003094010608003244c00807002c590040815034541000307407030309144980c01140d0858028205a0082100c1d0012400600f0900c2034518010308085c1d480c01d401d020f03140c088043c3c40040c0e00c00c4050b09200000d18500a40c400031b143d00c100b00300d41040031180050f00071840b010b03040c01140700500003401241d45101d510740e00c4c003c0c000c03c80128146890100ca400c0186080030610400000f260024000506c94100010052110809001d1001c030b98002e5032110540b17120034140144001c0c0c1b4000c00e20041c6015074400d401405542d0b0901000400340c0c1c0c20074004a04540c4042003a010381608000703140c1c015121071070071a079158003503008030700a04071480004020b19050007150b0240003040d404100e10303440c1202d00c0166110110200011070060380402800310b41c1180d0304000080c203c00805481f041c5040d04022440709140014545030008420a000301c0d9000c0304200c02036034401d449514039074400c91 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 521038309 1250 521037059 521037067
    0x201080a0b1e04290108070908030a0206090f07030308010506030a09080a05190801050907080405010e0f0708190c0e04050114070c02010e011803110f0d200a1503021e03151203 77
    0x1013201640c185001140f0b05001c86000891300071440b07480341c0c001070f000030400c990340c501700554002c2d5901e1044818035101e0150074441d200701d46001c20030404580e0950303149200380c0d091104115541c1d01c0600008401903039440c1100009800c68098181c0300c0c51130315415222824245040200103082014908000a0a005002c5a070f00c000d02c1c141c100c03c0901d07104100340d54610304240180001181c810b650b104030550160303482d100082d08000d46101c841600d4841803401e0510b107280206981c001e02384130304628240040c044502d00554020b00810000c01c0f00354650301c844100300340c00d4610400040720070500768255600210f5141141d0383c00e107040000340c12040c0c0121183e21050000a0420301e200452100740c1c3d480031a00082d00c28002c1c40d8941207a4140b0340104c0c0741280d1a07080d040030422401141062802c00400d804850020000c202030980b410000c600a60102c8402c00700b61160259182500e4480c401541c0b08076010250100000990b1003042034007601d146420480340d000304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 521039559 1250 521038309 521038361
    0x20709060e04022b0b010f0302040e01050907050114040f090506030d0207240e03102a0c080c210306132304080705010905060a0b0d030c0201080a0b1e04 67
    0x7201c0d10400c80d04840061115044200e036034244c0301d000341000d44922204400882c0d541400c40648085038401c5504001801071008014261182110001025000701e40100721340e50040920010f5002650300c503034501a11002c0440d030b180d01503080500025a00c1c410002c0e507003000c1042c0e00203460701d800104022498021010f0200c903e1810441c0251601e00002c84868018a550560034000405031407400501182c40401040e1241c4e4802404408135000c8881c000341050341d0343c400d0980d03920403484000700e807250307a5181c0c0007a541108501c982800700c9000d480c04120160441d002441d030720b5483c20480d0070081210b10851502201d2403400e01482d0844c81e01842c2e982e08510f24103929669a60b840c1044d801900410402400035400c1030143c07000c05c000810090722078280001c0400010b0608014400d0580030004c2c0140495500454000598000c0c16400c0d88400381501c0411036950314808102450603401c2c2c1a201c40b000100580c00798078103806000380040d0750a400800401d070304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 521040809 1250 521039559 521039569
    0x10209130e060703110c03120708010509190c11100f0c03020901050301050d0804031403030a0513020102100f061a030a0606030207150905010f06081516020d03020c0304050a06020709060e0402 84
    0x54045014160b85415811400c018001506d03080301141040e0f82d00e40a05201082c49a80100d03003130030001d150200040f03030514000e008180260b983c030b4112a03040e40c1c40703d40c3c034000300000040c08041c03007003a40c1c104010b5403040007003000d96808010003059901c2106808016113181d20f420381d043c03500501c07500e80c150340e105055904442c3c0480d00000002410306110384203108940018002044900c0103e8002200000850060440c080100142e50340e5450001709004102e8000740142c11107016012512500d402c80000d140804034001001a52a05030401d0141445a210003484000c8104030f80000345208640080201d4202949414800c0c1c0c2d40d0006680e0300d0f0150034816503201c154034140f0200350300500c1d0304098a60100109515034000b00e61f10b0321b0b01c1020b2596000c1050010716802d030f500c504105424125002002c28004a05041d0040c0d04034003081265444240000226540d4659415000b40425000303400c805040c12031400c15a00a41c00c03542d440071455042c0302c0140c0f51 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 521042059 1250 521040809 521040811
    0x3070308150105091315060c052a191e080606092a040e0103080910030e10111608040e0c07030e210703060b0f12190c0b0a02010209130e06 61
    0x412205a01c5c217026214000c002440780c00048003030b0804500000c9100743d04250089070a5016004a90080110400c81d070346060740071038044040741c0c00e4158680d00b4108140300d000c44510385860030307010b1500c1e018140101800c0300041c000160303e00d10b042001003002d00419810080c1600c10820600e048000c174007031444001b0002034151100780c1ca40700204003001c1580c1c040c11140c80c151985507901c2c245003480c0e412a040711031185142619000d0060302901c40c0003d040c1d43d04d80602085490740c0c00800007460305114000c06038070204401c0710365010100e52082c02500c91841c0a840e581442d2070800d2100000b0091904132004001030000301ea008501902c4a202c04c13100c0311714080030b5000500d000500142d0b40754403071060240203c2085119044188a240d06550b0b8443c0e101c0114200520340080054070501c03030b001008008602d9014045074680280500409c02c08245e036600300b220b50b44d0111081d000140d40c041034010752890f00d503d404007c0d8000308000e000c041080310302c0c2515004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 521043165 1106 521042059 521042077
    0xa0e09030f071203050a1a06030c040b030a020d1b171009021303111c0206160f03021f1a12011d01060905130f1b0e0903070308150105 59
    0x361607c01e1100c0c11900c41644c07140314041405005c041c1d4000380c907a2407201410000030842d100d11500460260b0b0802d000140c3c0e43d40000b0120088554804219190040800d05411210350101c0d5800d541c0d104402002034645a0224041a8620310707030140b03650500101c2c04200308203c0702d2031b00c021a801781100d048070b840e4400030009112070f1040d040100030004403040e405802c045014254000182040703c0d116100d13510340c0ba501c1910a1000c40069011504107081c092a607204c2048948a4600c10300c080707010746954100580c008641980202200c1c1620118074200350408000341e031802107d40b003206110b4135030300e0207008240940d58905045c00e01003031202e1031307024070307103d4081d0410069480468141d6803908002c46219820f5480c0e81c203000f02060342038092030428015422500250b5803030081d440c1c098400d40e0003c001c00d040981802d604040350b60000c0c22960026 = true := by decide +kernel

theorem cover : BRFrame.Cov 520863309 521043165 := by
  have h0 := BRFrame.cov_init 520863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 520863309 ≤ n) (h2 : n < 521043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
