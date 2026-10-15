-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4473
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:43:43.272057+00:00
-- url     : https://prove2.me/submissions/8530e26d-e391-48a3-8179-fd56493b286e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 804316546 ≤ n < 804496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 804317796 1250 804316546 804316553
    0x50901080403110118030309150e0a11040b0a06030203160912030837050903070c1e0305010c050c060a09110d0303140c0405040c021507050d090501020c0609100504 72
    0x4401d4101d0303014201404074050320f19403d130250102c100964140303001100d80c0810164540c0c480c07405a801031102501a4054664403002d544000120078a581d010507c50808a03082d42407007480e4013401080003030b0030040070002c81c0d407401c0c01d0350141002c80c1e03001c81000088900740200b080c26425a25002917560304041e02c1440c40c1d690203501504000782e00c000140c004003421076010746100c007800c5008440d503040c10700c800b07031144407501c4039041d42c240f401145443e44000181d5104039840190030604900341540000400c0c680303034000b2022400c3c0300001002c60001c1c03240d4500c500c801c0c0c0d12103564010441c0c409141280142c030440c4030601d0040e812010500c1450704845500c412610704800c0062070801700d002d0315640500c400c20f0072109052020020303e401c000d00454200303417028071082c1420b80c0c081c1d1310b42c00d48601e45103032012441c00003000b0038031070f0004214640c44540c00043c05000d0b5103845003281c00628904241d41e01003014400c1369582040410035000481d40240814503250f138 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 804319046 1250 804317796 804317807
    0x40515040b0117070b070c0513110d0f0b09070e030d023d020a02030307080121060c0309060204031406090a08090f13091505100524040e130c06050901 66
    0x400c0b8010840f440c054154840800d00a5030020184121000e86441143c00c01950b5600d07144a000e2007000304030038400a0344501e000310540c22810310300c40c0d410300e20781a115001609485010040e0315969449030649555407440c071900450305607491240461401c0189031902081c9084402594862620200c04e441c1c0c04070309640c4107440308103007a81e84d84010281031245184110321901e03203001040201c0c1342e50703000000d503201c2c2c01a95038201060f66215611400b00045001c403149200c1d203011050007007645a000a1140c888034a80051044d00a0312140100c0e0402d41048401040c1c010030307003004c084200301e00e6802941e890040d0001c18119550030400e0300c60a84071a0150f04054906c1040d5a03038500280d00044a0041c10b200c1c8100c0392030880c002d0380e26181c8030601c0c540f40101151080c0ba55411000c2500c4025080801c508100c100c5005030f814400400003241004010118402e19185000c500951148150740c0311510707071303140ca0740c207490b00c13600b0070010028240500c0300c0aa9105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 804320296 1250 804319046 804319049
    0x3071112040e190b03060711060105011d1917030306100206090304090c12020c010c02060a0b030d080406020f0a0f0305070206060d1506091b02010b0402210c091008040515040b01 78
    0x40f030303260f040d59910400203c003512070b0010441c1e05008280030080c001e41c1100c0705074030700d140032816501c0c1680c84100664000d00f4208401c065000d8440a40c036a5040c94050000b0b0301c110641904c52581da900c0d440b013001c003900c01080f141a00040140b044038201303203112103035807100e500140601d49002d80c009903407401180300e412101c40e114482d01640074000d040400501e03840600541d0358144402e48103028005040040c00103105d0040007444141881c494060023460040241042a100800403280c8000140c01a500c0d1642040401f1211850030010115130169455034581ca1001d0107018045070310041ca030308150b4100004000581d5100c11682544a5001d6155061031013000015802852907800201000c0c2c949113910002c0948403c071000d0300d01c910b074002e0040135400c0c0d040c00305a0040701d062014a003801d018222103118000011030b8800c40c1a40014104155980020a030880180c0c0c203402140d030380d40522092140c1804000c49141c07200b89503901500303040c0d80e2540f181405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 804321546 1250 804320296 804320311
    0x90b06040504020d15180b24060a03020a030e250e15090406020910020c03070f081c12050423031612030905011103061801060915110303071112040e 65
    0x907441455a000001e9010402e0b0100035400c455503050207150045c04040107980c02d6600c51001004e41140710081c01c80425100d0014100c2401c18024ad6070580294200401d408140740d03c0703405c1d43c04802c0d02000403c1c0c410b0450145804610040c079007884018580d500200548910002000300f40c007000840f40d05444c1040e61440c00c60303a2142050002402101282a40244040c09140c40603600180786583e200040f402e40d2001c23540c071115070591070a01c0c424445550131111840ea400031801010004075011403d10968800c400c4242400300d600c21501103485600409150180c620840e5070200704904940081d0b1030000c003400251032500e0556001890f21000c50000c800341031094100605559002000744210003e401c1102c1c001e400890f803a50040d6125410207410107005008203040700d42c15150800c217241045c65a00028602240c0002840040c0c000f00000708800c000441c412091540e03009881302c00b01c8440d40c1455929003085408640501040c03041240c00342070711b50803800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 804322796 1250 804321546 804321563
    0x11030310091b02030712090e0a06181523060712030f0b0607120908010e0a0b070e3607050d06090c0e091009090b040b010503070b0412150c03090b06040504020d 70
    0x100c12604032503a42040c8c00100702c8211003014082c100b4015005001500d10360224459007002c07142001c4121200106114100b41d09200c0030401c812800b8075021041002c0e00807001c1e4501c0100210300642d00403c000c4070b4600b142caa1203407040e41d244c8034140b1101d240b4481807100a4060307002420304e008880025007400e5040080358822800f98008800400c603450080c054030903200e03240e544071500c17010b0a484814000000a102c54811071032481c03144001090368003040b0b00c0450340c0d81d0140c0d0700d47e15a044000c224000050690201181900c50f4640d0ba0b9440c1d950410071030300d4000d94609601030b0301c0c030301d051180b41c000c10360704440301a04802003900c01c444560340b80c0c03044010900d83e42e800710001c1c0389007030300c50024000104403051086010700310f10070140e666042071580da049140705d040101030040c4814000c07120340001c20b030f08480c000c3d5880164481040c451508503540003c02c80042580c80180804000d0103507603003a40203004990030805840d1503000720318070301c0031640700030007808 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 804324046 1250 804322796 804322823
    0x110307092115020705010b04050105090f070e1e01021c020d030e011103011d01080c0102030717192015040303110708030403090302040f020705100b0111030310091b020307 75
    0x11080107221030801d030481500c2c641c424030011500700941c4111015107840d420308104400c0d604181c091030381210005010011950b83d5030306803c0443c1c1000d010398003002800d03185c80c80c0c1d543e20803083c074440841c0d080c009103071800840006458401860400c050030004440040100c54000c80c292011a800b41000704040740c001010034014a0f0f002c070b414104400c08800444d24140d100c07405007101d05007442c0b030031040c1d03261806265100b1030480402d0069100300090b500103100e462400b40a4910480d5080c00c00203240c140b0404440ca5801c00000a60400e010380115214040380c41c0300d818980f0068041001d00320b07802e0541c0307140201302a0034140caa805980703101010101f119000d035008000591a8282443d000300352403640c0c803040e03208508110514a60360356030300c02c98007290b078490020041500c001584802a0100c400c129040c070a0205006c3c1c01d80b003081c00254850140c4180a103400e9080400000843d00420301c00200516050708004046400004507041d45030404010951740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 804325296 1250 804324046 804324089
    0xc030e120a0c031a0601020f070b0d110c0c130902090609070915020106032108042003030c100501060e030d121107151109013203040308090111030709 66
    0x7448041c01014011011400010300c10f08586042e480401c0d20508030141c1c46030001241d0ba02d0000110b69482d82080302d0400c03004010300000c008403d024400802c16048120059540d070b082950090030a41101d032032602d191a00110384006200321035010080005960045000210300804440c00f0380c2d920008079401500818001e002849020fa03260318000020400038007070702040c40308035600002100e0700580300d200c5404444c40c0f220705030b8851840781c0d100e8541d07405001d00401e544910f40001000c7c80c0494900380000e08600030400003d1511040301c00c4408112030b8164400070400001c0d880078a420f69002c60405040f05007413800b4600c203058080c0103001403606004c187c04150002600c08208941b4440c60f48803980100402c00c1200c0c01d600c0852064480d010000d400100340c00311a204907200603021518201c4c0c41403000c100180303106440c200c240d2007031700e00354080790301c1f003081201d600c0c4c090080c0000020500d90240c194140303001b0281c1440d070907000b42410000d17007030f050300c0c040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 804326546 1250 804325296 804325303
    0x50f1504230108160603020307080c070f0816031b0c060503070207050a260610060513050604060824090c210403110f060115030c0219050610060c030e12 67
    0x401040044062155a40c0c2d4410f41e519a005403030048004e203500310000d40701c1d01900c2507a110b04601c1e143c00540f0ba40d80c2c52401d005500500c0b00321403910078038074400b011665010160031308039040d01c0b16050420860034003805810104150403410281b030002c0342c0000b401015000c08070303142ca08149860340c640c084141e041ca140e0b40c10503600088601400a45680031400c10140c455400760200e200104103508540c4680d011220b01110844025013082010300c40d9004089a040400d1075034040780c0c46a00088480e4010fa01c21030000e2882c42c14040766001800c07003a43c40300481d02101d0714541030070002c00c2a40c00001d11400003800d020a10841c500000c00300c00e801240403111400003032401e4640a8283c24402640651601c02d00d01c004c0d07080e000014405d410b8880d0550380290b4800881c500318080e200815232075086002c0c11140c0380402c146007a88803c018840c0002e40790720301e4403000000b58080998445410829028022000b103030300148019400c03401594200d20843c0d9051240c0e25 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 804327796 1250 804326546 804326591
    0x120106140d03140316120b0a05060307050708120604060b0304030e090a020f190206070207050d0210090f030c1401031e0c0207051c061508100c020c13050a050f1504 72
    0x42c2c20701c000100811001c40303a440343c420300d46903100c0380d1086d1a40001281100d0030780511a4000e0100041800503241c00006154406a1881d020789041547e0780c1e074502603000a0030841400003c10244081403400380540f10103007135000f01031400e62a040c1c40081804248000349406030040b4400b10714001104c0c0c044074450344112400540d500305915030b00e148030042e501204018041c6001082d0220f2000c02d0100407240c0040407520031080342e80030081c1d4480d19011200610003011400201d10041500c89402540100c00c481002d41c03a1814035000840c40d030074024109880c0442170140d808840c0c0e05101c86075111040001d00b04c101910903464207a040e0482a8801130700c0741c008080d10907251100c00d04600c101000d02c229943c18882415200c582e000d040d1041c0c01120a80000304d01a40c46118200c46c0380c8100c07021200c5030300106201464106a440c4215120303000c0040c4800140601078000e810541c0042c0b4070b10380101c1108540340f03d06502c0d44511f841d2180548100005603030303a403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 804329046 1250 804327796 804327827
    0x240901110f0304020406411005040e1e041103012009210c09070315090e06102d03150204081203070c0b092a120106140d03 54
    0x1503807090858800000e5030030484040b0f204a09100d008150b028914a002011301c041d40c8100c4204080d410740c8400421080081c0340309580d0490f01c22030269103184c0c00260052040e11915900c0341003100d00c54a84d40020114424070300154203250400c402c94104c150f02c03d130002d44011040c10b01500190150200340c1500c11807a4080c901d800017080014000c3c004c05200f120300840c0603004c480c40420201d9000d004c00010341121700100240e08040d02c0c01c6901200c41d1070000341000011580d000c1851454004c0c041555503849000c00c1201e0070008960420641c040700c0400f0780c1382c10101c822941c0400d0103100805514000101c07147c0c0600401ea000e0b590044030b29075600217105440c0020b400c1485551254403440d070000c420031410208a0703008d2000350781c0e006007941c02c9440342a001c01c0d018061810f20700c140750003240c47c03101c0f2003625440041802e5480800a0300b400400c00a220901a00c045591411000300700320900728460488a0105039642c43d1002030605064500c0c1c5207100121 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 804330296 1250 804329046 804329081
    0x6011401171f06030b0603130c0e01060c02040c03050f011e0b0712020c061c1e05070c02040b121507030b03030708070303060e091e0102092709240901 66
    0x46100c1508200004401c900125080c4002c1e680d04403c03429500e54030407031a04004d080000c201402c6501c172405407014000c540340750100e0351301c103001c1d00350000c01d07400307940003800401c888811858a4000c10f40156424034080c019401c0012174150400018400d10860071000150f241d10170326407400c3c140c02483c1701c000013170b281e1095003080d81d8142080e092420060040d40d00c18003581c0340940c1512008001008001568000401c0d200010711031403003003114000c0e64502c8801d00841c20b00420f4428101540c40c01e00c240781c070b031061000303031100c115042e4802c0c1002e4610661005002900f260030850348145070311a80ca91f00070903801040030200160700f601000130321100344500100203150042c800d40c0e08008007603a0b080404401e0a0582d030402a940101529140500342a0414400c00380070740001071810407200d0020346c1a51858402e0340c000c021071440c2840104142503401c1c3d009000e80041d000a40c1a03103600c0310b1442644040e00c428210176408600045404d40c003242c00d00c20243e809 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 804331546 1250 804330296 804330301
    0x8100504062d091e060b0a090b07030c080417060105032103060a0f240302030c040618090518070801020c030a0c0309091415040915020d020f1201030314040302030601140117 76
    0x4092184a0008130780001a09110001901c00015021036560b0b070501d595040b901c1d800d103014244c0c194131040c0b040c1c041056031400306e40402c43c00c1004000804016220000314500100c1d840d00b0010140c2c09107100c1e401c006030718545680403240c581c107010740082e0307460303a00d81c1d4090006070700c1d07101030708089607240c0c001901190000d0740c042490400003a130140300368a8900708400310f059100441e140c0b081c0e0301c0244800c2010b14040c00c0c2c522140c1c0000c1990703280b416201c407000070407030354210740d85100c0d2540403800c107001d503909010440c045d00a50009515000e124603080f0340d0781c440c065551040006e07c2c4064030038948940c2d10007020b072205035001c2c80403c046205c1c82c0d12003042520b4502d039103118510000001d01d414410182e80f540e100d401030038044058004403000350440109100724607020000280246c0c021002400c6284c4129418643e039415814001c00302a2001790702001948108828800360380d00084250444143c480c03640300700490700c3c0040b101491801b1518039038080d02804d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 804332796 1250 804331546 804331571
    0x102120c1b0601031a0a1b02010609060605071a0c12040c1d04030914220e0d09140f060f032e1d04030c080a08100504062d09 55
    0x601c800c1d414aa07a5201c0301541c0d1100c961200d0003840010140d108416840c405d004030320701c100b036105252407000100541000c0e001c44040703601c50319001c010b035941c034814402a0078038403401000e4034691500c1070616a0540e102942c81c08480c224101201408002070204000ca000b10b50b00d406001d95140290b08042c500b1198500d0304d40202d064046c08480c024000650030810144220b0700365030b4241e1450b1400514901521010700029000500c000c44142581f5880740300a05041055600250221034030000d6421320303030303c52032210401c40c00c070004205591138a41c01c540b20b10401c4440804070070100002801078400c009210040070310100c20004d00d1005160191000181000c13211000d400360003035170b0100103081c00391044c0c1030f20308410200000608156294060f2007410b0001c0f0403849610b4502840c0c11501e88000010b199030200610340c00810010802800151002d0156500700136030b030b0558028820300b5042d20940c01c2c004d0302d6480a840c245130700800500200b0000c0c54401c07003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 804334046 1250 804332796 804332821
    0x8210408120d0606030b010f0c02041803050705060912042312150c0f04090b120f061014090f07030915020c060f090d0c1b09050105011707080c0705010212 68
    0xc2d421a0380c0d480e0003000a010741c0079004221040d1016511121080e1040c03100317a451250090301641c2180e90b84c5411140d5654040b00740314094025110f00d600c0320100e10b00280b91100c010080c000a82100800c04680c012140540d416a5080c074030719400c04030580e0800e03070040c0c00040503a46c07044a50b0052203001e00e02280700803025800b0481c444095464022050032481001080400740204000c1007040d030506030712101e403a60004204411220b00001380d10314041c0c54640c040141d81200050220361240100c0120007402c95075255a4000d0746003000030051080103080c0d180b040b05c030400190074184030303501071070328a54400b008854405a0714007583c001c0d000156014001d100355004904185a5030040c0351041031403074002c000c807148000040340d401004080840c1c200d0001130b003072016049192000e00140800c42c40005240d8981000104441d4128a42000707500200e024401180d1f40040c1d880e61052600b524a80d6038581403400a009206414169081c141c02c0000d020b20f841001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 804335296 1250 804334046 804334057
    0xe0c0309010b04091514060a0b090109080a03090e07020604020d030f020c0d030f1d090430020a110909061b0f0316030501081504061a0d0c06090f0821040812 69
    0x1042425040c2000400e181029991f2a40c014040d02341003248400340c8000342980201850428a466a0b0309580303131030a92881c4080300032880125091040d0400c10070415848103841c4014084c0703061036001310350520007510000d402c0010241c1d041410a00804c400c009140e00030b072900c20050307450b040c024011440c1c0c0819100040600414022170400c82a1007401808000d16404154843e81da400d0f6214100401c200c40d0080302205204440c4a40354074800800c070036030054400b101c0fa600d0312100710354622440034030032030408050120030540001c18552100d050311f00d1101c41d003520003910055000d02446002c02c0c0348e00004000201c84011850b00944155403420720148e40c1300d510b900d840e403440d64010308240c0201d0001401054854100c40c440ca00f0074011107008100325002f0415080501d1029181d20110344010400c0e40c5d44044100d00911000141d22549810400b046446805030842034840310104142c0b000d48e40919000c44008040206c02c42e03424640d5404402a0f54011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 804336546 1250 804335296 804335333
    0x110d090c05030307020a230a030b010302041b0c0f080d09080c010c0207150806010909050c09010210180212101b021b0109090216140c0f0a0e0c0309010b0409 69
    0x900c000885060000a81d1119a801060307072010b54104003d130030709a0b510140c1c01929015082d1500e629449507821500a140280e6140c41c40398114010302054500340300140038039481060200d15801e81c85820000102c6e4400d10f45281d00003c2d04100d8503c2c051900c01c900c0c51032928103480108103814006106d6030361240c009110b0012000001d90316034a05204012220109020750100d46108068031940036005042003150903494540c00d00882d1401c0b100c8915480c80020100400d68040151805401e40c86000f444444400c141402890340c610800078001c45861501454904050180b41c01a07008200100704500c400c0b0b4904d191075003c0460000903000e09800f80d0003100d48070000501d50041030b140e130b072151450012007400035840600c1d10b000e01c071f0b07211301e03503c0c00118403c004c048400c1140c0010310000750500200800280304e11031080c4280d40c020310130004142a1100c40fa413001d0403909880c1c8031307a9030382c5982d400343c1540d0401b00c0e4017034034000130001003119864800c0e444540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 804337796 1250 804336546 804336563
    0x8180c061305150a0906050c070848011d03011b0908010203090705011202130f06030e1f090c15020d0801060f020c1918020304020415031212110d09 65
    0x1042c3d00a1110b1240e50b5440c80014410b40e0b09008550142c1c00400d00c0e20303101c60446445507602d1030854100743e542c411885000c01806030b03030780400030200480d00644003000020090194010f03907000a42e0391032602c582c140040c1303040460083c444243d240301d040c1c07000780c001d00040250340d4500c01c030460282d1502001c105c581001290036401442900c0c0314010103002481800d05140040d210250403110743c01846800b000003440368551103012600070914001e40c3d4400c5400c0c02800ba040d241d100300c60801550040750105803050421100c04400c40c90301c5030001d103440700c1c0c0c1068944140940c203c0e83c4182d40404900585650000d80c11600201e581d45407102030f600e450084400110311508817005901140803002e442c0b40c40c0c0c03407071400d050300c000c1c070869103640d102400951056040340103248507030301004000c2076041500401110b84031600010f0300183c01d690b654021165841c82c0c907000c00a62a1041038000c00700d90203c4140c07030854540036110802c400000010300340e4032500316085071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 804339046 1250 804337796 804337819
    0x3010e07020d0507061104030f060b0a0504140a090c05060a09180e0a030f1110021308010605060d050a020d050a02030402130b0622151d06030708180c061305 69
    0x28808a20b201102400780e6841c0d24040254503080090018194084c0440b4400c100010004850402d208030080c4a05404149071220004101c01481181e2001c1c0c011400c0070a03061500e80c00c04045a40030042c0140050700c01141e0404041e800d40c00e400854014000044003036125420400358000c032550680c5041d440030f00c2c1c001441c181c9030300c0b21074843c02da0321200c40a40064048d1100390081e844038a01420860303044030b016031811850b55800220142e00007200d08040c0350810059000d018840e00a1007554601030210b60a44501e10520400c40e030b842d0003042000505404580c80c0c000e0580c01400b42d42000941d0100a60090340c0c00c911454000c40c4210403901240506680102c2c001d0100e82001001400b040606101e4044182295281d10001c1104000840104081602d5030346080219024901c0d60030015440000103211f10420b20801c1803441d071028400d40e003c8110617112140140818a507883c2c00c41403c100340d400031001c146002c18006130f910803c1100c008443c0081d031131 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 804340296 1250 804339046 804339061
    0x2040902040e150d020f0907020f0d09030b0105060a0801050108041707060203150301050c0307050a09091505102a081224040b0306060607020a0f03120905100e0108070207030b0c03010e 81
    0x480c0d01610080d0010303000e00404030246040200d00d0b2344180c89005a46542c0e01c0c814405040994244006000c181c4042062040c0900c1214050251106542d02d5141010050003c0c0203210140b00d001d04002002c0005010080542d8100c03a140d13200000190700c80e1054500b80c4065001142d44415035082108100960300d01406032500a205526406145855809086449500c2070b50f41009020000500150141441c8158102218000e21001c0210b003441d040010701c0d403600d6411010803e01e50181044201c001000e5000703910980342c0106940c1c600d1404821130700a031040d0080050120003004a02c9004034500120443e400311a0010040d4802c2080201c40e101c102c40fa80650007200090003d0038828014060a0f00040c80e0000302d66560810320798006454104842440386000c2e80c804860300255010013030a01141c0c0c9040c56009808010100b010080b4050304105e4044041503400b8000e210703000203590014006249843c100c11700c0361090380300f032260368071002c0c9880010b03c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 804341546 1250 804340296 804340309
    0x31a042c07230f04050a0e03120106080f09070506130b0d050106020d020a1e1a07030c031802030a0b072007030b0105010822022b0b011401020a03110102040902040e15 73
    0x89440042c40c10302c21111420a000c0140305c024000b001056698440350241902040078003402000d1a801d04a6581001030090516002074001500c8800c41c00901130041c41c0410704000340d402c02d0303861548890043c0100144002103a2104621800002c0d60b603e29190540260341a43c01c26021102c10040480d000c90343c0744060240a0b00c3c035400c01018190078600c0e1700b14580b2090040000382c01c402c0d024145180c3e100c0054500d0004a5611090030b40884e03058000c0c804000038150b151440407240341c000c60b44a515481c0002c083c1913000000404076400742c015042d036101c01411800a202015030071035601c0407940016548040a800001119841220300c0d0f80f04142c407001c00b00d4450029900504c4000d02c0303410407640051818002e410078207007c40410042032100900c048c104829062010320f40d2010380080f03101d04102040641e07681d0700080c4030314200d685880c0c02050105c61001680c024011900100c41c01c41c0000340000318170b40207591080c012400d0321000c10f407003401c050030400c0c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 804342796 1250 804341546 804341609
    0xb091f03090201200c121e06040c05030105100e100f0609050a170304031b1e051207080d0e0111060a020a12060612050606070209040606060f031a042c07 67
    0x300354490040c4034100d003004250200c11b4140a02102d00d0340c0354402860501c0e20011507541580d17400fa008000034841804030b604000c040c160000c02280c2440d00d022020071005001d1744806042030070102d101102c51b40210402040e0b02c60131070700001d85540c8001c0002000b403180b14420750f01e1510120781c1c00c492030307070391015456003034000c515261950b911001003403580c1580c1754440e456a000040c003802d410320030740d00d802d030300000ca5103025007070a08020f4404000f031404010350340503080601c0140400164008604024100048400c00840040711160340d43c030a080600e001c1d05080c020301091980103042c2400940c1c44486143c003504504004844440c424000002c0e204003624004a180d81d00c21a00844080d14203864150f4503000700b40d5081e030980d005c85909544090810500f940000b40c10001d1065180500c03918100b51043d050039503800300303250310566440c1c15469071a22041c2e500240ca010b610407401202070081145515041c444c81101e9650300f029045c400380d084083c2d00d03840c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 804344046 1250 804342796 804342857
    0x33807020c030f28060c080106090b0c0a030810080109060e070509090a02060f12160219020603010b03060102010b0d080a1701080d1d04090f05010f0b0603010b091f03090201 76
    0x41e03070600360403001c1d0801824599907000280510f0136404149a030044e0b414800c0144c84021265240c104001d140080d2039120809410f03045c17106200f40d28000c58800806c6405207450f6460703444000b280d00060308658042d81a96103072a240380e080002c581c11142002031000e055a84059a607401c1c4160b041e800c584a071059000800754a00600c3c0641c00340503045a02c2e5001404c06040340000c3c8940c1b02c00307035280d6003840465542150346030b5040000070807203810003625140c0802c1941c00b00301d1500041c000d01062410110005400341d00c00d500203002d004000b0a40c3c1c091001741d042c02441d0b030303210300d2001c00044c00c0441002c0c0790307800405220741200e0069000304170055114008403140141d0150702010000b03540348034000c654a0380951081b41b0700903080202c0b00c05c007070305d07089007181d07030b030407401845a0b052500c5482c1d1a039030542503e0451784e100d01071603507030184000040c0290304000c14916140b40001089180320b94107520240300d461007a03c4142d107221400c0c44424100a2030710740003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 804345296 1250 804344046 804344053
    0x30c061503121b0a0b040516170c060c010213180c02070e0c09041506020d021c092102130902090906091b030a0b04060b19080601033807020c030f 64
    0x2040001c0b0301e031901c4804801044282c643d25201c0317549800c4810303000c0d1810380c3d0a6101500031000c98082120100040070300480300c104800a01880e01e0300d070201000348038424000440c281c00c40c0d0300290101e61031400010220165181c840100070b5101c0080007a60b0030451030808180841800021007074103440120540000176598101810615445580c801b500b083d00c0310225941d50100180000140c44603801030094116042002031620000140d540307030300002c2001c2c0240180e0002b628609884140005105591032800f41d00c407078185640d8002d40268042c10389011031695540038203405031085550203045d44400300759943c1c81006603030800440d0403002c540540c803012180c0d10300c0403140150598005200c01e84035406080801c40e41580c5e090344944407404245000c3c2c407007a01000204400408150920707145955518050000404811240c004c1a844001d0000350510fa10f149601c01400302410100030406640c0964030766000d889840c4a0019601e80811001040071058008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 804346546 1250 804345296 804345307
    0x70f11100e1c051c021c1b0207150315082407180519051804020f09010605040b130302131b0e06030f06150a11060105040504031b020103020c030c06150312 68
    0x81c000e132150000c00c4041010303030070072414000c1c07110300b0507040060b0b50400000642208035034a41c144001404100e400315000280103004140711070018240442c0545800191603055850030304c030707140380f5070032200c11343c8500ea001080c680d601801510002410b02014001ca464500c02640c8980c0703001d0710141c0c50200c161080c045810251111a287c08007105114005a600d170040392070325011840381112013413454100320a6013001021516400411707a0107a41540c54158000c01c10700032030044540003c8001111481c0c0c0810101207000386400a00304a141214000c41400518100c0186a8846035880a0b80074150080c982000f001d1400f038036a610755918030304103950461008100d04e50121f0b43c50003c804500249010f881c011700c80d522031101a10103e010340c1e04c0d10b01e0580c050381c411420b2034100300000c2d500ca0390b0300d0030400e144004009814543c1c401a07002e40600710381d07001e491101080e4013905440000d901e034021481000c4d40c441e034404440c01c1c592207198078403c0c1ca20707020040bc40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 804347796 1250 804346546 804346567
    0x1c030606020a030e2715090405030a03090614270303011d040516030c081b0a050f0d0203100c120204060c03051305030a030f0305100e070f11100e1c05 66
    0x304907802500c02450402010395040916080050100581c0301030130b81c130010070406d2900f0b03070403448625604641295961800c0e0380ea5959a00c18030300141e08058039400800100030040c1c05c80001a81040100c25007464003e000245c40c0340280a040e1403500c0419100c4008440030003164180c4050414010340c6404000d142c0c100070714080c10455880c442c3c010944440c104091404014512508000d4002e602c1c103c1000d140c02c80305c00c080c4100e0280c95110742d405503210f40d41c4008989007030700d100340c21002204c000f549588078040f010f50940148031245e4040140c0d0741c448000c541e241d440c0d54101c400b034203256004a00940c0100c2d8082285444504c000c68010409442188004000c1e00c400a1b00ca9001c24206055440114003240d4440c42810380d01e41c06001d40d40c1d0005000e0300d0450040d00d05200600d60507006400301c828824131100e00c0341070714840c601c2011048030301001c03500041c00c5c0d940001d0090695555941b920302984206031500030f200d0701e01d600320841f19500c0030f06015a0a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 804349046 1250 804347796 804347807
    0x120309050c04091502181002011103061e1503180708033109061a03040203100c0201020d060f0312021b040c0504080f07091a060d0203070207171c030606020a03 70
    0x600765600485007280e044070030020700043c11b035810302200c422150040300c020710002c990880007400030340e41054000b10030140c5810a81c4d500c440c0072525000304604401052048001740e100345500310844003d407102d802c94580086000d03010010080e42201a4054034548944d0140218009a00b08100e5440c0e401d2030b0310300004043e102203084c0d2f4048042550115a2400c044d8010780b000d0780c031441d08001804600700c41100030540940c88510f50300d407581c000b944440d0a100d4006260f5607410342202c0d024402d6060b07418801d4000d000700511a00c6801300e03580c040c40352000310789030100075000e4281d140c80484d080c50032031903044040300e03907504070010013025002404c021010001306000004a41404010380c20010714510060001d9034200010101515948403607000c0d2040442c10340905074950b5000c8604500c0201c10050b203d4841401c1242855800e51200c4800700d0500e001405e4000042500c5150074060315656040c80d51030b400079000d841041c440c080140c0c2044070000301190256 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 804350296 1250 804349046 804349061
    0x40b090402030601090f0801050118020a0210110d09050303160e091b070f240b06071b0f030309230916021f0b0a120c03020105130f060507120309050c04 67
    0x1414a078074100e0b198546c0d203100c881c1d40c0d801003400340e44a0b001004190805a0030318948800020150b24100c0c0000c030295640d40301c110900b40c0c081c0e50f1200f400e01a020241a40e4098040f5541030011400a040c582c0c0d49400645064070341c09038020380e0310959070081c884840d4205002d00307440016624201c41c40d40f090000b0b60b0b403030462a4100b0603c00003a480c110301c1c2c00c0b40c6202d040d40d80c0e0100c582c0460381e03040e850548004081c0d10701e00441c400d0b0903501e00042e00c1c0f800d80e00130040b940d101c101e00b040403081041d692014009003d104004010540c00094007000d1b19031041000080e8088078110071103c40f1000d03040364008a940010445514004c440f04990460f1401205c040101108a50310300c580c07041c000404c80750b6203080c61031092404500c450000c0c070031880154071852003511802c560a0301807000134140000043c81c490300307201421841001b03000d048c21800086995940240541d440784404032240002c0d031800425490183c80b07200310b039582007030060000c214450b00303100003031004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 804351546 1250 804350296 804350299
    0x1515020709020a1101150e0a15030507031109070806090708040305090a030c141207060c020109090c020309150703020a020111010b030132130f030504050315090d05040b0904020306 79
    0x3035000200c0c41c51000c0c0020001d41c00f20395510100c08500c403412a003100d006d8160f2400082281404000011140e902d00380c024203242c2d0006003403020815021040012584020528018148004140a15020320440e41c0c0c209644100860b80d42501c100d170344080031646c1940c00034019020600041c030036100039910038407138140640f6010703018000400150441d0b20403070f00d410001c003013400b41d14040b0304101040c084c00d0310300440c1c01c2c5106c118070761585400d0003102c04000310b400b801c0c02560720a501d504014a54050100000300d168a002512680f0500ba01402010001c00c0700645100043c2201c000f81d4141e4098108502103600445072070001000444042d0f48600e00209290b40030b201d040d01c1120b422580441d0a0300c07488045030002910400491001a1041040701c0d42c2c20740088a1580c55206050300604003903841c00750707680d01075608125090701c2a09244414840780500c000e00422441e4103c5940e04282d0004940030b11483c00f41102e5000184600c000c01d04280c0c01540d00440c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 804352796 1250 804351546 804351553
    0x11d090d08061516030905010219020f0a050901030506090705060403020f300615090106020604030e04060306020c061f061b020a08010e060a0608150103140f030a030c030f151502 78
    0x3078203007202c80541241000d4100440220111307010150011014001010280040c081003400000c81c180c0b040c41c440c50107401030342110114182030780c8480002000c0c01009022075101c1d41c590800d40d64480c0126605102c6102c0c001020400349085070950302120383c02031400b40d0b2110460240a8003810340e207181c1c4103400011a6142c8201c42d02980c40d122070414400030482c0e407410f000d2000711808110000b034090184900180a941c0c3d003c038155601c25054241295044080f0021400070402035001a060034408141c40c000c042000c20b030503001d428022050100650324030311043d1408018425080850b05071b032249244442d48204d0380d00c10703030b0004003402c0c061540c0d142c0036801d481012244441d00d400c02e00c104800d036003951080038050b015080c02400060080c00220b04205418000075040c080002025030800c1c4040020780300001c56041625180c400191b0003402800849400801007428a19090400f807034600c00c0d815010100c9907001785d1189050480e5802030b01048800c0f04600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 804354046 1250 804352796 804352819
    0x1101090203010e01020a02060109061a07080c0a06051e010b03070e150d0903080a06050109050906060d090804050a060e15130e010608040209060d02100305060a050a0e011d090d0806 79
    0xa50a1140d20003241143c00003594803801405c00030b0030140140c01042c000d43c07920409101c5801404c0b80400d9064240001d03560364001410071441c1402540009000e510980204404001c1503802c454050f80101e26140d4289500003d194100c8109006d04070007030100b40b0004080d28030911245032030450180031030181e0648182030084030b6100c9003e0542043e12881d80c0300c10140e004920303d0b84801703200d43c101710160070000000c0c60000035100d80351080784000c0119085540e0f001c01c569003109011000c02c4150007e15040306c9a8000c1d210380b0348110030100c00010013074050301d18840015001060501d102491501b5501507401400b10f41c0e5140704000c201040748603500701c4041c0038001c00d441d08880c0c0d04d050b10400594030710042c000c9000c0e0401c4203401006840f140c652074400c0b4030a0801081d070b5600d9001007950340e00c0c00d40c0043e910448041000451004140060b4142c8411410010320318034048074030040044180ca02e107540c0c0d880f0003030035000c0c5841040c0203070b0886401821380e20680e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 804355296 1250 804354046 804354049
    0x160c0203030d1406061804020901030f020d0c08070504081c05070507060804060f0207051e030f0d09020f030a080d050415020403110307150903020904060f090804090b150a11010902 79
    0x60700030880b40c891881d0740301ea0000c148081c015400303a11140c01c992007403502150b48540702c4125035089003540210b4000c81d00940701d038040c0c1c0000c1c61840a080c011500c03442002c5e000310140030310a0110020551282c04aa1350602c41c41c202c4003a10b8806008000e07038105c40d1279070b001100c200320801013008000c0c405000060360a01c2248004c0c411a501c40c0001d0400742040000c56400451446c04207104100541c002400031400092000030081d4144004000035a81404d601c2515801610b8400c0003078a5090036401c0c0d409004010b00030746e900c1c649a80070340241581c40c000814050111030050100140c001142e03001513500502c11040f103406501c0c121110000d9030010b03003080703600000310764503200c080c107040008100600c0a140d6128007045d032404090003403441c0b804043d0058604c800043c040c0305076900030304080c220300034040101d42e10074106a0301503002806150452400c02031b424a4902d44400f1109014141000d25440c1004011007622000b2a83c01c403908955262554140075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 804356546 1250 804355296 804355303
    0x20d1a010e10090c0f1d040204121a0c0301031b0e180f0c1c050102040b030f01180e0d0509010309050f0601090c030630061b0305090f06160c0203 64
    0x78980c0144a41040c20505030700e00c102d18207030300242d42c12440d10707495200c1c0503803240856002d000d1900700340c07201c3c3e20700c6441030000e02e040c0112103400900008002510b004d000007480c041c18000d1010701c0f101d00e004044e50400c003000b6104143c14210a00051000c01c20300004000012219840c44002c1507440142c000c580780d045174211200c0304200d0405000d03403800d00601c042484000082d00b90000c62400003a00d51070401e40000c8000c0b0307001010b6003040703001d5040fa406803030340e180c41c151680350035807126132403036024000c40b4035562440445803040c030514001c0b1440441024003800202d600f401c01210b0035004003454504040d290302d2468041071060181c0344c00741d40c0740c0300507001c258141408103041c1d410000c1890300709403030f080080009240482c0801c128080700c0036111404c00603401000c03034401c40001c0c00313007401d0714102d000d41d244040c2d840c1500c0303581d2240c0c03001d204a5940000072511220b1280380d2a40c1500820006245058802c2c00c141401072241888919420f041c0c01184c42c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 804357796 1250 804356546 804356549
    0x1202090c0a1214070825050c010906150302032103060f0f10020a0209070903050a0204020d11031503060a18300201091a04020112020a02280204051f03020d1a01 70
    0x1c0c1c22070f418064000c0c1d102500780c0e48410200c0d104100700040403000901c3c0b000c10748082081000110340014444002e41246500a8110405101664040c00484141e5010b480221700c20710403010807600554050075060b51054042c82403d007195181340500407034500c001d1801c0c3e03202c0d52443c0c690085076a000120b150650180d0b00910141c941403042c0440110094000c034240700a4200420004400040580c8403581c16140540c540d00e100c03842d000500742031032a200c4078610100030030241008180790404401c1045080717680946030000064204c40b04101005445200000c408000c10340c00021039000b01d010180301100c00ca900c042094586080300f500c2c6006035100c01000f13003885580c20b00d205505003011400c60b65801c082c1d0029045d03120281e5030381c1e203440d00030498603401402800812030503905400b2902c1881c80c84605c014042001590403442245030101040b0a0395403404034403400c042011980010b1030458003000446009620101e5420544000c1c001401d48038840203030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 804359046 1250 804357796 804357821
    0x3050403021f09090605030a1716050609060a021e0c0c041505040501050f06030f0a0e0303010306060303030507080c0405010e03030715090c240309030e150c071202090c0a12 76
    0x2401111400001010100c29030b110b614410f041490071b0003d60782c08503a0101260340019070341089818801e8241d0039010310260040c2e2404605512802d00c000420f00c40c0c80783c01140c0c01e5514980d20443c070b002c01c074006e84403406443c0088840c202800d40b21701c030080c081c00e19680b0071200950b03440400501601c0300424800c8900d100c80e20100018145402054090501240d4030380040c41120003090942c00003c011401c04940e440121b0a40d01c000e0f800700c0c440b5070042d41500c4c2d40790303182d08000b005041f980c44100c00091401000601031449542c20501845c098a18079107040e03e890011524440c000d04581e5042c0000c110f5a000a042c110203480f068032402c401144206142c107000200c2d00003640300040a15041401c1c001c110382c85c8080410002107030a0015040450303040c1100c1c01504100200c0d082040018401840d0085801a1440080107401c4a14103501e580110341013061240d40203402c26034540102d505020b01178041c0545401c81e2420824140c2001c1103802a900b0001c0400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 804360296 1250 804359046 804359089
    0x20d0e070503010c080603030f1b0307060c0906080f010b0d140415201c06050301050a061a0f1c022116030203091b01110a0606140306010f0603090305040302 69
    0x104007509007070044400c80082070800c1c50f03061a00502182d16071203801507951951760000384a555585000703da1500d45903d0030100c90b00c0d00c0103843c10b5002000100f4076030010030140350000400310301c50840f4910070135071551914a030f41d00e88100240750740c10560344400c225460760b034901ca01d0110070004a00c83c60040d52404140030b03451108100700e0b16041c5041040f904120020013101641d4000c4801c03a03501c1c0003035aa0780350180f000140040c01260801a07042d42060305201d5598185e400c00c00964030301003d003108440400c40e05201302d11034a1001e1180c49401d02604106100170b000262200b070f40e526026290203100b40301c12000200c01220b0102060410051052102c800da070740756000303040b9003030452071400c00501c1d441e42e070b5004001418491400503034030f104c00c0c2d102c0c00104851419020486a81141518007a4094011030142911030010100308482c00e142c000340d039070704881c01101c281c040d035803e00000328007138004030506600b0300404001c0040103807901c08900500c0c02c803e1032030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 804361546 1250 804360296 804360299
    0xb0403140405100806040b270702062a07060f02030609010b09010c140703080f0703091a070b0621010f050912070b0c1e0a020610081b040908040b0c060a1815020d0e07 73
    0x1c231705071110060200c0e002c40d4400010046000d030341d0009242c030300002130200150f42e030842c0940d501c907118040c0000c20241c2016a880da00c45d110341c002e98040c650481d004041d580e2030360b240d0051405901c81050014482c01a9000030400d0310015860140d010401c2d610320544076101c109050740098264540c2c43c4c00051510300f816403080c10040909010800d003802d4401c03106250445024214001d014090f803880413691940c0d90030384080784c0b070365100b0b0b401e1101c1114101c014020540c0604100c591400c0200080c5000404580d440c1803250217280d01d8141040d68480d0410503030010490080d10360304004000c0300400307a108003000010300012040c0c0d20110020300904081c1c01529003012514401014001c01d400450060641d8201285504140702650001805805060701c050180c410000e40170448110761801044584802d10450702e06485000120045548440030041c0260b075101490b000216804804000440d09810240c1051f1501c1441c01c101c8142c041e1040459002c400c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 804362796 1250 804361546 804361609
    0x218010801090509060601050f090a0b0c010b030a0f0b0c0403060504050307023f12130e011706010605162109060311030a05061c0b0403140405100806040b 68
    0x39464090900001c0603c454108a08696966400038140a051100106d41c810807803141000b40c03003a0341d00003007004064507910303044d403961540271241820081d400c24a40300c203c3d05002440200c500e03400018112030b80c4c1680c0b00e64040400180c0801c504901c00c210000200c0c0c00c03406030501490180c00515528102841000074900100b1b0f4a0b0241c2d01d80380f06c400a8007000008070741034281940144650403204c0480703550401f401c0420310408840b0103d050725038004d4140c441000d44181070710156460742c9036500c1d00910010780800c04482d500c4a0014401588660085c142005811240380d10525055885407141c00b040500411000010500000c0096200c0b15000090580313003010481c5800e072000d0381300988002080c150001e41c580303012504070b0700c0d9802c8020000c0300710903034540c4114035890280412481914141c00140484140e032104520100843d41120300007021209a0745a4581c01d0790381980040c01c0303641c000d5036140c0342aa5510b602c004035144011401484918201d140b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 804364046 1250 804362796 804362807
    0x90a0815010f0e0601120c02010b0d2f0604060e03210928170703060c0809070b040e1302011404060e03150108070e040501090c0b0c15041707020d06021801 68
    0x14040d104001a440500c04c0eaa6042480c2c8110501404030100320144a404142c0c007619803d41244d81107001e0580718424020b105480f50740c80d01c8007040303841480c102c0704880c09004007000145540301200304410000c060081d00c044103800806020340d07880790341c0c40d0074681140d0000501c50302013030000a24000f2503d4160010940400415040d8040c07645844c10081c5655071405868000c219a10303d14441120402c860801543d01410074000f0381c10880f0000d00c000e00c00d603045441d0f40710703021005c15080e00f090b0035241a1010300e03600480a58400d2010304540100c1142603042c0000400c1c004032404c0004010005040103840d0500c407036050105162401c07100c0d0205440a00c0090018801b000340424a5800c8a00041c210a059107407410302a00412403070000030210700103010b00160004040c80a002d03010b00315010f40b80d011112400c51042c8202c2210010012586a441070300300545003409001182d001410200a1480a54804040303a10442c80d9070801c1c41100c28003401c0b5a03011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 804365296 1250 804364046 804364049
    0xa15030b010201200a021507052203021509040e0f01020315040911370f0501030c140310090501080318062713090308090d020120090a0815010f 63
    0x20b10003008800c00c000c440032501e921070803004006a40c0040d0890701144208210000519010740d00405418a800d01600592114405443e410301040944c40400708031039000040300d8025040a00e1a0350031f8540300d00e1075212820496200365071301034103495100c0030801042d00814840006035a41440e11003944800b098a00ba01d1060f41401980030000b5107040008a50b1001591014410307042040134a500804081d501045802640c40902c55902003140c000c044424003140b00c0c60003a100e000441c251452034043c80041107181640031040a000c10055600c030740301d2008040d800341c031480341c4403e03504207a10446103907101080034908030854001108241c6400c403000c6140c0200c64852a55401d9101c02002810544880513041500e4065400c40c400c9041c1c1c0041040c00080d1034041c00683c0f080c0c2d520450751041131038800805005204035a604008000c90b44502014040120940c0e0b014502c103d401c1500a42c00058940f030800000285801d09008485a0360600c500c0d600503080f60b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 804366546 1250 804365296 804365299
    0x6021c1704031706060a0e040f0908120403140f19020708070e09070f080d0f1b060903030b010504050a030b100e0c0c1b100804061508010903030b03010504120c05010b0a15030b 77
    0x130056081d00c50b400010f01903a01c0c80948002c50900e4109c91290000d01c900136010b050b101c400100105211002003416204512035210800b61380d000c50700e019050300502c098280d4410041200d00401c00c203504040c040b2810f94812038a0036903c0d1100c0600b40a5a6440296801022020b2160480c410310080002d080815501084580340c41c07803481d85c407004000c560b814444504c040c2148148268120001a8107041220342c1740c608518040e401440501800d078002490701c5403441c903540c4200b003140c08482d8000d0034a1001401c42e110b0450202c0007521003080509020000912100b141140701d100d011105205511401c1800c0c010b410303d400101c0c2040d411007502d500c01030503a03580d5100034400500745082e905503035503458128000e01203254207801c0408a01c2c40028108070540000e1480d40c441e07031301482003070b225000b0305090318026103000300140014852102d1441c86188502c0d5800d00603c0045076480c0d582000c074403441c00d40e40090307080080c01a0f07400301140c0c050044484c4030f00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 804367796 1250 804366546 804366559
    0x7030c080f0718110a0509011b0210050c01020c0714130207031704060f0911130603051b1f170f06010210020f0403020603010b09030f0706021c1704031706 68
    0x51070802588491240c0035090070000c00c603038070159a451541c00842c481818400b03481c4d41c4c5c00c00b00c1010380300c0d4201c4458140001c0e400d0b01032811210360340c040034103107a5019040c840b2101c1c0c14a03003034a86421400c13041446650174465503050400c100700a01c01000b0000b030b107003410050401070180e00c1d030200c6c4500c140c041c0100f0401001a5020141400046040c02e0300401a2540d281032400707000d909001040490800b5041d200788800c05032100d0a00c0c2007103132856000081004010251780c42440054a41d4001e01c0c0750040d0701048220048003210018010359110700022107800107441b80e14101c1000a484828220000a0b039000ca103400010500000b1341318940000001d5480c0e5000e0002c56549030040350340d00c07041c42240d00303442c09164010102d1392a0f40c0c54200b032075125008030b0364007032003482107080c0507401c00320200360041500e0f59540542000c403001c60380d12014000d41f040300010003240c00da41030400865400480d004a22995501c50b454000406411260001070802d81c40f641 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 804369046 1250 804367796 804367813
    0xc0804050a030c022e080703090201050702040b010512040c090506182a04060c0218010b310603050a0e01050919080d05070203040915030812250207030c08 68
    0x8900280041141d42d040c54800c48004083c40445c03500041400c00005109401104201c61028808000400e0304241d5032100c8540c0c1d40c1c281101500d10384030b80603010540801148000d0705041c1c018440122040c1481881c0002030202c0c41d000c01000c0b9404da4007851004c4041c04021018040c854006030101c85803464819450b509000080b0094202640f50100003620550000c08100c20722030607418000c06501c4a9441c04050016002d00400b2031182d0b000890401d0020420015507040c0e500d19640a41000e03008241000c490283d41c4006100303286280c00c4009a442c41c00004000c0e0003c3d64020070a42041070561b01a41d6641e01c07004816410842000f80030803000a07410305075000f900010005c0b0184d410701407002d2084440d00c8e00810b08140400c105c0300d8000000300104c1c3d9058104102007070f0928440074003420207000c010880001000110080c050010300d2a400030313840302034104c0740c1c0f89003015050200450351121000d608514010010702c81c140e420310780203044420180200e00e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 804370296 1250 804369046 804369053
    0x12140414011d030102041409091c0c0501020d1a0108090a03080c090f03010e0a15060f05040b0f030a060e1207230f10020414190b031b04180c0804 64
    0x2040c003005034100140040114005007141d0030032a81048050000c5682c1d07a2101c0d629043c0120781c6100c28018400c0c0804110b00000c005090b0200017680022086a40c2060750125031000400506446544d000d00c9640145400b0b4420015040a52004002c44035018400901140300007080c001082d00183c101c200802d40111070141d009441d981c44540e145036110000d0040071f403504074550590301e0400c0400210f10f00007040c0f01e4480c01111443c618898a0b81c110b020388940b4080c2203034092400348100700a086c29000442104002000220403508a801103803802c0c024010540710962a01e1003142d40c84018407046000c01e0080784c0c41e918050850f2941481c0ca42d8410140310780019112804075100c40502903003c0d0740f00504290f80d581d211001007180039400601400307c0441c00c0383c0c0c0c40f6115107080e041c9a040303001c14100c00200c191902150500c5504014101d004141c046038950628024010042010f4181010380c06060a4044100012500000300110a0210200501020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 804371546 1250 804370296 804370319
    0x201021c142a03100302091609140a08010c09050a050d0c03080d02040f06050c1c121d030403050f0f03030105150d1d0102030f09191104021303121404 66
    0x80c980b0241400520701016100036841002045100b2140040b052200b42003860401100310f034000c0f6196003054030b59044103000108c0290203c000718080c99030401040c40c010b44190f1103084002e00e0701b482c0d00d80e079003800c40c2520414207020b400a15000300501442c5400c6484d14042c0c08103682d0040030001540c1d8000010000d1702000c0c00307691012a503668480319540455001e41060002c4420240d5038840140c0039030030000355542203002c3e402c1d40e07030a103002e054450040a440355842c0c043c00ca850005032401000d00e0041d0a1801000c6030f0504c941070b02c10801003000350301c00d10082031020f0502513140d081800a00560756141c00800040280303070b4490140001014544040a83d54410b5114480c0181507c00c105500d03041e14400784032803c10194083e5205610b40400512aa0303521010f192b10761402c000347c1560788044071901c00100b9081d480113a8404c1c4040d000600c1c0410240e0700c8903040020364012180e00d41424540f051155002041083c0000c1c0c2d401c16606103410000e45808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 804372796 1250 804371546 804371551
    0x51e0a0c02190204091b030c05091005090a06151106091209120f0a06050405010b01020a030f0309030201090203071e0806010612050402040f091b0501080f070c021206070201021c14 79
    0x780b141046055584e103a0120300420341c414181c44050311056410700c43d00c80300d840266640e1941a200061605220710814424407402c400c1041d0641050100700502d071003e0031404210341c2d150004030303c40c840720300c040b044905242c5500300c01c004050320f40c61a207c1c0080003079420384c203c1c00804542000900983e4a280030890b8207034190f17200a40400e103000d1001c250307802c15110f08440c43c1e040c041c940d0310203030203503000e80024019580f0b49001a03070741d80c2c50341c04000e00052601800b007801a02c00e5001c2241c1511903c001f15043c9003c0d00082e01d0304646420042c0300c690300f02034820070142820b03203250043c502c0354041c0c045580b40500192801d07c0c480c0300c0e2689152218002821565954441d203042804050200701000e8603051504105e200c40a407407200e04541e00300480c0c4d80d80182285803144100176613904503541d4800c41100e110741e5511040360000e40300240400241420f204680c0b00d540d882e8001a11030980c0d902280100525000b00500b40e85400c4400010b903da141300140d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 804374046 1250 804372796 804372823
    0xf0506180c03070b070f150b010e011d01050f090a0e060f090c091905030f1609140412140d0207030813050d08070212070308060406141c03050d051e0a0c02 68
    0x1601c440d441d003807080c402c170044c3c6d1009180c0203480c0c250110070651540310400c011001c3e81c8000b2062004030056030310b14643c0294020147e405031501c150b561185000f001d12504540100e401c100850001c45d03081222600304400740401e4008100e6542060441800c460108a0b00304c8078604010800404c50300c0749888160051445030340740c2c801030105c501c28000500c009402c86150424690919071141101d04915080b4107580b0360014410056018590010500c02d0041c1c000c2c0d01da6590308c121102d101c0c209a000d0090686041ca0b442801d14041c16114032041405a42c0300c041d032034000d03c6c580009100c41011142101c249010803400166a0011103441c14801c446444140c0280c0c40d010003008920340c42c0c000043d20b0020954040c02d041e00440c1c003681c003445030070744400214206032961881507412002e00182d00c0000c00452480b40c0816010f03090140c83c1860304016507054a40849041031a0038100b01a1040d480903881000c4d40000380d850204030080c65180003d403195004248034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 804375296 1250 804374046 804374069
    0x9130612060c0c23011401050f1c0c0612050601090608040303150e090f070503070302150d020d021206090f061014091306061b0b0118090f0506180c0307 67
    0x120325940100c0b0712442c041d4201c540803004011500c004a4113031041c11038500c040d400c101010001c00c100b480014169680206080d00781e03540c031024000341d06000c000c1000f1203050302c5180c1e03002c2000d01c1c001401910495942c400c600c443c000e290010f03204040c01c0c0c517041165080c42000020303480401345400c82d91518001c11310000d0150300555042c07075034200c001e00316a19000c0c86803680002881a14a5646100303079100b4030343d903030101503c40949100107508580e081c400c2348000c141034001094203030212040107003031500420001080383c101c2003e01107004044003c0c0b01d16441c0501c80c8581c0a8070b9035105003c20320b0b0103008102c01c60507600c40c0106100c118241400c50b00b80c00300544003080b0000d4a44515281c07423218450280c40d9621461022441046410920601280340914001d41005c038035820741e468060000340400d11190201d40c541e654183e81c1c000600a001050903c40c000c00041006040206140703050142c07045406415078850406464542ca010460b6404c07540c05000c407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 804376546 1250 804375296 804375311
    0xf0402130b030d1d0109050d03051e0c1513030c0602030c0c010f020301031b03050a0312060b0703021b01090e040206030919050d02060622050604021e0913061206 71
    0xd000d0304062040035418000c032000680c4041d482554001550f200041001e280c07134909005507901250b0f03000c1e05402031011020540400e010b0700007003003081d0303420910007480c114204070341415030089003c500950b004006604c01304400d24083d6500030b000d1010311031180c0b0701650b02411000c0300500c004c064580200026400074101c5095581c46081c1000078805075449502c180c009500c24001214449a41c8480b502900000140302e0281d0f54000e0040c40d0354009906c0a441c0656840d00002c02c068485c0404140d0840c80c002401c40d81b40700343c009022030b4007100d40c449018200190342e0350401c034200b2000c001440200807001c1c1c004c0d8040d03c0c415526205c06802d9410011603110a403140040119201c0030003000240590302440603a00340d443c0e030385580041100105241c5030f5403450060240034192883c003258080c5401540007000180360039040d100000c00d13481852985c0802043c08038884056051510013840e0048a207801004094205940c094040340b1f01500502407035980c910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 804377796 1250 804376546 804376579
    0x305150705090f0f2b02030709050714070c0512030a0f050c0c01110c12060114040209061209072408010b0f19051c0204180902010e100c06020a0201020a0f080f0402 72
    0xd1407403c00e1600017615903c0740301428210710784220071000c900034400d031600041d035410b8502c5031300d00512290f900e030301003041c90303210180140d0051103040c0c4200c40c4020000940341e5485800702d1341c800f0074034065501c480030010041c03d0986040135410a0120400c1071400c00c51001c525601c1e02a02401c0410007066804440303464010040605508014680c000c16916540010400c1c100e408210071a14020a803106101c246e0054007d40d0390402424020190594000441c41b40d02c000c000d001c640b4040e681d11220b034140740d00ca661403882514003002403204c46034440d03c0780e4050504000c05910749060140030174070920070303186040039003030100751405122445038048441c50350410b50401414114400c10100941c804c0c4034682c030780ca04191466414840d18043c0c00a5a80c0503101c64503441ca20009000c0c650b450f040c00c0c042001417844441e40096070b030344050084410b6030360006840f8441600054040700160081000b40040a41004912001c42c1815540160706807400a800944880f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 804379046 1250 804377796 804377809
    0x5010806010f1e2003040f03060903110a381b1603050405130b03122b0e1e030d02070f02180a0605060f0d02070503040f0305150705090f0f 61
    0x906001c4041640900740c4103076030384030701400c000d020000c51104a136075151526542c0c0b803242d031141c120a0b018500c81000841c040b90b20810300035000e82400c003181185d000e42c907410410141402c84078040d181c4415031030580892078085d106825007540b01d101d10a180b1184c100030000808118a0008500c45900b4a134054004d4a49184141c400f619071012107180c090095005409001e001f504512611245030100780a82140c840e00a00503100c032444c1000c0f94809607011001d00032521650800c0801e000ca214003107036078046922000050580d45400d102400c1044c11001d0b070a070038030a1900c2d13010084020040b2507801c4140c8800583d91070503032418880401c095880a9881034400210080220785203071a9441400f00c94801c02c9143c3c0c4640801c4110302070380c207003080e4078201440444407403895507000f008128011070484e401c1030359070f80c04105082c038280c008483e5074025152401c00d0b80e0a03550000d8021200303082850034051040d001c9040361140100786440303446100d0704207a503500c42c3e6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 804380296 1250 804379046 804379067
    0x8071202010b121f020304020618150706060f0b0a1707210b040b06130e100e070f08060a0302010c2603150109411305090c040605010806010f 62
    0x5401c0b080f070511408101a00d506410741c50203064903a0111068907214940f086074400c5034010040c2c0c0c00c19403810440503107400c1083d895a00701030308032106203c140c008005881018420500480c8031801c06c02c1001e21a2030342c0e4080751140c03406100364048580c128090701030100001604030303001d617180e00b41100e0804085011803000341040c1c081c0c0b601e440c0c0d03030b812403d20114142c40034424044044144110340c45503001c81c0c1e07042401c0f660b05001001e22158082d03001102010501c61080d2203101400c2000010b03100b040100e40c025002070180ca4202803216402002101c0031024980340da00040d000041d1030390010500700da604070040f20b4003150386031241166103030082581c40e4030b402c846a00c43d4448403503c540c0840c505050003d80d074440302290040c00315075124620044801c80b520020031509500904010a08070580e800341a29048101c8455550b00900402c15040c0105640e0504101d000b02ca80a2401c00c0780c280b169036000140e403500040286001e8402c0c0d0741d40c000849219525 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 804381546 1250 804380296 804380299
    0x305040302131410150906020303270709050601090605090604030b0c190306050a0b0316050a170702033c090a050d08030601080c0309060408090105041e0e0108010908071202010b 78
    0x507034207000c0b03c0240c041005085c2e416020b5a00209aa80d80c400c0e9007002141c030544005074000c01c00110f000c520701040340c64050501400c82210440161072a041c502207401101c60740d036486040003940e6031301c13400040042100f400c0840c03400740c400300800c81c1c40c0705602000e0f11541801022403c03024006080b81c81c01380035854080e0700710704050070081c00b40030288a02442901c0751940031403c1c80001c01128018100100030210310904a4010b4030140c00c02d4289030280f1002511442c1c0c0881000f041c54490300060b4007465032540410143c070103460400c5070f1090036403030101030f80d802c50b9880c1942d011600c2180c02c0740e5482c1c190f01c1d030008140002c240c00a0f6045641c0300b1400c070030040307098040d500a903003d13210680300303540b04040465503020440340c2150380d5000d4000f01e00070428071001010b1245061400914003a2038251161016100c1402c03583c10340c00908041003c44201510385026264540080c03001916584405185004288024100da14000210031215001354000600c0150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 804382796 1250 804381546 804381581
    0x403081003053d09060b1503180f03070501050615071208040c09140115080708010608100e0c0a0e0102030f09040209030102040801090506091c0503010608040312020d0209030c0d030504030213 84
    0xf106a4001034000309104030341c454100001041640742400c1446101510a6031190459448042c44038035a0480c5110358664026820b00210345481840141035080c01078001180300d00b480c0b0288003a00004040341d2001c16414091f00001a4101d403448429026a1410b4852605e580c1000803035800f455006440c00c510300300c260300500c52107a05040c100c0390a562128030108003100142c0c1d05600454017800082d2038100140182401540350b030b6080000309425030703003194540d0b0f05000b00324000d0b0f55610b08000c0c081420f843c0c440d400344d215005072000784007171420700074403c1e031917205070140240d070600c101e40114000c40e003514254141c400034650030009020305201030600b152141420b49803100140070b44500d45840655024074010080e910740c0d174240c516842e00908940d581030140044040000d17851019a0740142c0340060428a4450000160b80b01480c50070146843c00d400e03503c6001d81d03640e409030804250030009030b074110382d01603920038036142d0380b00c00d403800900343c40244200001c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 804384046 1250 804382796 804382903
    0x4110f060d06030303060e0f1306090516031203540215040807060c03020114010e09240103020f0a0305010f0f05011410030c020c0303070803040308100305 68
    0x99140c100c2c2040b680243c404004441e1280d64042030341c0001c0f58041c01c08000c45001c00e04445101807003008990298074001508480c80d5513a508184100e40203e06500b015a42401400100c6905028900d40d90404020b49400d0300c40c0303000105607503002c89100c0f94400c100c48461a410040800c1140c032030f0b044991000144140440b55280344400503801180c41d0b070000036405041204031801d84400d400108140b51401c58110f0300414404401c80031552242d030200600081010120b018180480d0111040e14010120324078242c80c000080750322055890146410060b90108107041d00d405540100007a01c0d03000101d0f080d950325a00c0141650728004c001c12200b0f0685d8007402c55404500350501c126681c2e803012112240c82148040d030f124440c1400c0e800d00c54001d600800b140300060065030300c0e0722045d0340024116040a501950a5000001084100340d840412668095070496200c0c00c0e4509540701c3c83d6882660a00d14200c1c1804aa000070900381407500b4440445415044c3c4000003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 804385296 1250 804384046 804384067
    0x14100e0f1302040906051c1719030c02010c022805150c090a05010807050d1a0616110d03090e070207050a032406122306040c0e130201050304110f06 65
    0x3540103104d41000345190060200c1d0602d04651420b01c007070491040440346035029120b51242101004a5a00c0c02008105903500301840d560340f0f02e1108403680300040c0d48282c549000c4c0c250b4a03080f900000315040300c9405201480c2d00000749514028407100f0041610a61402a141c11a000642c0cbd001c041c42c40104880d101d032070f000401c03001100b5107484c41090380da00e00541750020b054404401140083c081c007400041154000c0d01c0c4104145402049442c0b50300102d11558440c1d81c076203000941001c01d5000b03104200031000301c000300c10b54011007000c0060314001c1c40801a40949101c2c90038910200d007a0a10030400b04020308402002e4680350350741c1c0e00d030000307052601c001d0341985124543c0001e1107245940c4140c9045a00382c06041401d0369265803801025244039110745076143d000714034000720070010018148100e11503c00203554070304040c0c24041d2420028107203154059810410801030342d0203025283c0150b404a404000019214000790300b4050141c12183c00160100703441009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 804386546 1250 804385296 804385301
    0xc0102070b1b0316120f111b0d0e092e0915060206071b0f030305182107051504060606142a0703060906020a0914100e0f13 54
    0x350081452482c2e0b2a03600001aa0960000701c9072520030b000040726505030075004807011038070175071400d10004401c0210a014012034000c002c000283c050003249404050040b49050b24a50041d54020401015101001000354469400c400d0003038405202050144140308445000451036071400700c4181c5d00e10350f038200550740324440e820285041921136074115486c4d4050000743c4100b0745c0030b00b0055413001e005440401466070b80500c0a1611106600807034040104128100c0c407981d004101400c11200c0c543d03001050031005202d5401101d440019100351803113800702031000c5825039490b08410b007031550808007440c000300780c0b030301d4404204410000c541c1c0c0a44180e42142e1506040890320010619407801800c001d101c001c850204600c200603980d41d003202d0003038400000c445226450303039102c0e030569180384021642ca5801143d002c440c950441c003030074058108124070059002100d0b00040c04140c2d01d00f1080113102180c5001401703612450580e00c82c1500250654011200e88450341c1d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 804387796 1250 804386546 804386551
    0xe2701090b07030c0e010e060a020a0b10090c0f05070204110c0105070c06050711070b031b1801170720010e1902040b030606010504030303020f040906030f060b12070b070204020c0102070b 82
    0xa440c214403401304a000300f42240d011401a51601030760005138083c08410342c8541415003c1d449002510700001300c070b99941d18441c0f030303080100c0c0d9502481d1035024003e490001e03102500340812204a802c1403640312040e2040650101d801040030940740b1004031042c8180d004051340c03542414200000c6607040b82d071041d9200d20941c010800382d44c070300d101101d402040f94580c0c003094001000401c1343c00f51800195410031926020fa044142d0b06010000d4103500c481000a0301c0c5100000030b5070150303000328500420000400308040d452400f010000d00343d050f004440b00400c000d620061040e51400d5120041c0c050f0090200d031084098031101c03441a078040d45040340300b40d040070603024240c10b0203c0d080c0c2c065807044c1c503805c0c10b0500315a0150060741240064407030341001804000345c1340e485030107070800a5001c0d000b490351b00301550500c041902c0401510b503010300020030a1003004000091101c04841280e88511f407558003d00c0010003a20802041e02000e40c0041419030500000c0c20400b0f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 804389046 1250 804387796 804387811
    0x2040b0d090c0f0510080903091002060a23041401062d080d05090d060e0718180512130f0311030d08060303091e100801060201060f0e2701090b 63
    0xe5042d503550342c5003c142c8000b80100340e086140403512015a500510110b9042285031065908061130b81c40400c0c0f55040c005039501c0142d0185080c041170010600c901c0d040481ca0a0340b90402800c80c48040d210082c1c060030007880e01002c0240038444020a61009014003003a200c2d6a5400742e0130380c0704001c0040e45400035440914151400030700900009540c0003c040c4917112182004001810003e96421072541650101c2c8ca1b21007030940c1c1e00c1c1c1408401e002d891044151060881041e0494003240c2e092041401403a2150306484042000082c800804008005c9210780e20380032a20070300d40c02c166580c00300100c803a80d054084108864411901e80c034100c242c0880d0380000700400211400801a1502d0f905074004000402aa013042030307180d803c21280d810801400000c0002140a16000305120b070000707070249006004681d42805003400410f18440b601c1546420301e03210504200c4043c1203c042581c020305e00c100c000b2200002510b45c10b0a000003001055868204501640411280c80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 804390296 1250 804389046 804389063
    0x280501060906020f072c041a150102060f09031e071e03050304061505100207080c03150a021315020c030613050a06240f030b0702030a050a1202040b0d09 67
    0xb2440300d2001403184114042200100511441c00803080b0400341c12044455038210f0200c03039036585602c00078070503000b28400d150702842c00d444207010022201e400344c000003140340f1001215141780c5e4001040703504503058407020295621480b9070303289948600500b425000c483e40c922003140f084541c028004281c0030342d01c2c11318041d03803000c00107010f900b05150007004240d0902c007240100e0300b150311220304a86003141605080b61250b0001d000c010002c0a00c0d80141d0105006004100c1f050004d1800d1000540043c401c450600f4051440a43c0003043c0d034440e194045030051403450080e84442c014011070103805801c034142c0030002e480b140f880c490103000344075220114161582c41e80b4101c00003071b009809458a20169600e40b405800702da80100101202000e010700201000085c081c001e020344103542000c0d0b440c625000b400c40d10300070302c010195001801b001000607080003c641d1201e800381b42419041c005160f401d002401541c00440e00c42001040c1e10702102c48503402212201d00681c0d44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 804391546 1250 804390296 804390299
    0x5240a200d0e1e09072106030b06040b060309030d0216020a0e0a051518060406091d0c0f0904120c06021b0105060a182c0c01170403172805010609 64
    0x4544a40081d00d441580011900001843d618811a4268610100d8884c481c90b000e00d81411b180a40d60650800d43d81401e6039000d101f8186018440d00c01ca8100542d851411440e04280342500c074015105000b40c446e0300018146440c580b11182c8095943e0300400c016041030f1540300c01001012300f2540c1102c01807406000c24442c500c07800502901d0080244400c440b0b03103440c0d404404102014040c0e40d003254840d03001040b2a111070082d07407018203822911344001500150954608020441e803075014036000311440005480718075082d94000d4001c040d80344030624100f401c86041c010650302500c160310205265003020310b211401d1045a14603002803040791600c0302084011103946c810701d1242d1071700d05038000e0140310f1a00908141c1d030120f41d0100098405408058000d1030702c407917072021a0010300c0c00030010340c0c002e44844542c00c88851131602a2400b82c2e170280204a0480810203031400410004c3c40145500400c0796020010001c00240b0300c0d44110482d003c2c203030a025500216a10450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 804392796 1250 804391546 804391579
    0x3031906270213090c090e100510021002030c0d1d07030b0a021b010b041107050c01081909060504140a0b062707050405240a200d0e 58
    0x1103009954070240070000c4001094550885101400480c0040380d03001c0c07040c9224100d4039201c4500500c61984046805011a8001488442e058000e9118445110144052440010b504100b80d41b402d07225107998454110050303103070140c641440c4410900000c00c000c0003855200140c503001d0043c610921902e4024035604101d40005540c55240703500c40032082000c00c0ca4056855040041a0030051074210700d880401621051303030100001c242e445008101450900388904454a50740070102070800c1c065a49064075080b00c2c2c09201d04200340c4002080c5a1907880c241d01100ca2031061003004500806d19110014002c01c130b40c15102440001e032002c0e0104000300380404036541c4000005119a90041002010f01600c0030400940c690101510341c13201d5031407080c034010506611040e4603180342c2002c210003150f426049046010454115003e8942c005080e00c05588150a0a84403141c0580310b802c0c0240111003022220f1055109449540d500416400d000880644103405420081d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 804394046 1250 804392796 804392801
    0x7110312070b060f01180603050f10122d1a1612050c07080309100513030c0308041b0b040306050f0f010303110a20030c010206040510090807060509030319 68
    0x10005000c042c2c04000140d1103203050880d8244e440c005041071282080f901e172050300341e1201500640c01095a88042c801c90000b074005e5164421070041840d10382c42d003085440e0904204440c0000c18003000501b07240e90240d000349a01e4001269107004000481050401d80d082c02c48c15110aa408003145020401e20a03440c160800007445030344440850048180b2003030000d00d0020004000c010052217039400043e01c0200a50284041d81d0081200702c032810101d00c12158003410440c028040d07038520a0004e0f810001000400b03405003481403181c1d4031418014480345c1040c00c81e488121a080000c908540c541026106980c02100200310544d101c685501d0340d000181c81c10500301d0b145400410010b48685540039500413410141c5400d04141e40c0c4d0410345030303c00c0300c01d100c1482001e100d840c50f5060030810001d101c0320900c020011800c26841d00c948501c010451080d045440d1081c0c1e005200d0400121000c45911010030000c40c5000c0d503070710f622500180c0e511034200318502c030110051000d60 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 804395296 1250 804394046 804394057
    0x10f1a0a1403240108072709020f09010801150804060506010c020301060306150909050703260a021b041a040b01050c0303040b070908030708160606050409050a020108070219080904020c0307110312 86
    0x40d10348060075450030304182c03404000e00c3d2201074024007d600c045810030300c60000d84a000c41d84101203460b054450300150004005030000060401c08036208080316900007006a0044e8001c2400226070319140c004940005007888065059800c0030400400c002103079101c1c1401e002095801a142504c07034010300301f600c1c01c0c102e014203a035010038800d01c04650a160750b1154000703c11440c0c1008011008521301c2d43d0052054100540c0201c5a00130000384041c0d50403c461004840c200445409220103c13100b6030299030b4180201c2e5941c181341504d9000c0d01c100c4100e16005011a43c40e0314240c600a00070381d40c111101000100305041c0042c2407030700001aa02c0c0f486e03000300d0890408549a81090404216484c141c0c0c106072581d0000440d900e0702e11603030b040d0b503002c0c6016120403a50b03800090005240075048030f08650000403801010724190710780b9580f0031b9111100f82e555171011000100a03010341002204a8080012110200b0003428111a00b00030142d047e02c0d200400054031007000e0141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 804396546 1250 804395296 804395311
    0xe0f070305160203071e0209040602130918060b0a080a0606150c021e0d060509030304230718110a0906030e070f0b0705071505090306010f1a0a1403240108 68
    0x41c01440009070031b486400c0341007050b581c1c000b24007583d16000a6183c01081c2e42c1510b03c00c0e8000351200d0500000500040070303102d260b8041c410400c1d440700ca80062240d241004d0003503592041104a2552060302e0b01c4010140f40045501498140c2441c0d0001c080b284244a1120503c80201000e00d008041e12511990018480c43c2c0c00e8030407403010340703001c2164544241d1101c0741103500c3c00007410790312a03540101c0d240d0000355144e113082d280213444000c0c452900d040804001001e040f101034000b604800755800b00c6020762504e10072004540c042c20100c14503074020000410704807402c9a12030210340c100c62031030390140b1070083d491030415141c20fa0b90003103412644040310705101c0689044002e2403014401c504136002c0b07036030f162060030345e0902480d980c10001704000f83d12009881c00b007000501400305061035912051038818451210881800850340602c1c000c120760303070682d005100048000e503118016944d613141c501100405000102c440b0300ca0704071004d2800306075500c90b940b80c40c8150750 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 804397796 1250 804396546 804396553
    0xc05031b0f092e0302210606010c021005090f0a060c0203061b04050423010308030a1a09010e04140d0f17060f0f040e0316120f020c0603040c0e0f0703051602 69
    0x1004034000f04407641421403e00f01e1a08200c00070040e12039000c0c01241038401c0c02d0b1000000c2a4142d00c90800340050903040c104146100018050b954603c0341d420744450505101e130f076415142012a4103034800c0340e8420f601001140c400a0085e401203404251a44210103560903603170780124101c410840903c0c0181c0b000d030240020300150429500c90221243c0305241c04220048030a86202a0311098008440ca8500401401500d040a0040c0040100e036900212180001e20011031000700e014400c41c1402810038000c28140204040f0381c503034078107021060310f2000c40b5400f006059110034a03000800601766852606200700c0b2006a280103403802007401401d10340e5041040b403007004840b441540b01d940c0314410704842804000a004c22120944001c103842054104881c2c0c11408015003070901604414a01410b940401c071600701c4203044600030307141c3e00e0314100880c0c040d00c2e64001c4955590340d0400d00c012600e6100482e8407400c4113542c04d1000d544c2e19000e21108420300f54001000d6403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 804399046 1250 804397796 804397831
    0x8070c0c1202010c1b0801060906050102030f16050303100519030308060d0309080f07030c21032706320a0819050408040611010b0a0e040c05031b0f09 66
    0x39501c1010840038014940901021300e192910044032180490340740c440c510380300c0304019040c8207024600c014848044104401841c200000c2e48074403c41078016051000041c42d80c0764a0400061440c9041d0860f080307a1b240d242001d4002a00ac0c51401100d200e440b40604d1144901180480501565415528506152a01c01c140000188a040110140030f40442e01180070f440402503050f06440704c10041081e1461801c007003200400942100391020800100c1c03810080002c10f1422510342c4c103207000c02c42c2880d0b08012203c03010040b810800c540081510028005030700c154160500c02c503880c1700d1480840005440d404124045a008405080070300805c103025001e04a1103500c11403100310190b17441780790fa0340075046a5080303800300d07940e1078045828040e0551100284c125420f102c00200b00702c084980000e4203902c8a0311034402a41c0c8140001030402207044120001031a0107421034000c140c0c032060b2074a605144000c0c50780a0f003c0c8070901e1407246401d012180c00382403410203002006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 804400296 1250 804399046 804399059
    0xa081312081218010c03200406020309060c0a020d03080f10080d030c0201020c0d111606020606130f0c11011404080306010309050f0f0304091109010e06030907121208070c0c 76
    0x581c00078030461a0b202010b03000d000650080c0210805c1d1031203580c0010b50845250100419414a285546c407000c000f4803060100d107400004548000c0340445503c3e072204c168814440c505000c11030005d410010841d0940300b055003242c107180c042c0c0c10300c00c05003280750346108909800380c40030300c02c8910235840100f04401180c0a603002c803044288034800076181c180850030140c42c2049102d1807000140b944d005014540c00c042c080e40c004480591020000b240c5885002980ca0360042e020900c254030710142030802c03c4956101000d070100300081032180140c1031001508850b005d00e046102542003030340c00d840c8044020100c500c81c65000c3c1c4500e00710380380d502c011401403100000840366032080c81a01040a80c0402443c0510004813004543d11420301d20440160356030020104031a04042c00218030681e080101e0803100102540c070341741c4070360380c0307400d60b514090041d80a00c904501802064003440000385c114480100141c441c61344d19200c00104031142901d1000150115002d81c1d0148202c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804401546 1250 804400296 804400327
    0xa0303020319090c0303020d05030f010e2e0f05010212030a0207080f030c09040b040b031c02160f08071202130504080d021209070e0709030311030c0a08131208 70
    0x18401408070b555252401141d0b0044943c0034409841e041e41d07011042003056030411039104003000c0d901c0c01d1070a5080002050850001c117004280c18004440d0003c0c072070854143d4020b180b90740c80c0702c0346020440441003621580c0800e0169050081040b072011481c0e500020b007110012040300283e61a41ea0b0380c0030b051009412050044840c001d0400c1140303040001207003d540600a24807001c3c2e5651007000c100701c2110400c4910500580c00c0c600c10781d1445d90003245090854101206000220f203161504a0500c1c685c2065021640d80c500d00106541561001102c244d44080007110051a26050340b40303415104901c0c001c2d0700014014440607484000e420080e0010f114041c01402d0254484508040e6007110b02030780386409035801006200502001080700800003850601418107001c00010059100b80c04040c050218910114030003200400458075015071180640d0030075082413410005903805600b6610340000c1d4060042406403609a40380d2040d6800100a45005100c8095618 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 804402796 1250 804401546 804401551
    0x614160914031207050d080a050105010801030204090201031b050a090b25060b0d030509090f160c0c0f0e250207140102100e10060801050f01030308270312070e030a03030203 76
    0x10540039900c005003003c08804040d0444900c50400340c0314000d400c510007090724400400000c000c40c240001001182d81040000e81901e03016200851410224001a80980b2081208545003a0440c880205803a40078000c2c0075580c860b40da613402c2e03603a40c581090f04a0301400c84200148082c54500e001e40803900b00450192034800c600c042000c04042c070010741c0000c82040e00b42d010030000507a8071f40f2441c045d1092507202d5590102c10403242410300c0d10034800c42e10007090000307001480d0f0f2420103010900902c4002402403041c407000e490341b2643c11000c2c2100580d486250a43c00c61600c890840b01c9030022030900b13440f42d000700007961030109a140c51242e4114440d0560190817100c454420300c50007801d80c40b5a120005004182e00e2001000485400b607002e2401645820700b030105180c0c1c121091811207400d803030310f69040d89940014061075038510f0072002152a00002281140e030020000c2c1960030031500a00030305542d1500180e5041e0401c2822581c150011000320000134040d43c040c64 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 804404046 1250 804402796 804402799
    0xb090906180a0c120f05030f04090c08040b040303020310050a090c031b1202031e090a1104020909061504080a03080708071b060e010e03270f03100b0102030706090614160914 76
    0x800d45c40301500d4441c01c0d507209081014603d80005800d10805041d40968440b001003440c0c69070851520740c450318007114000d0b02c0102015000000304014084103070120010303041c0200000b414564032882076005050002c0400b0119041c92180300b0700821400300c900c55041c083c0c036102104448501c41030020342c0000c0038401213412012070310441c9603480300b02a109000c3d01d8001d21414859040040124400c0c00400c2d00c502d00400403501e0039110381c0f1341039401200c1070795024906500119004c28034055500881a0b0388255034076582403681c40341c0c040340201c0c41502c40392341a8a03034803001c442e41d46c4c460091400408000c40800c3c00120a0350114a910300c4c2d4000004015480b06252819030344000801c0900c410503480009511640d484000d8171910300321480828007110101198940d80c24800303075284551307101e21010b0280d00030300c01c845d0071592107181000603070711601d8100c000740310500840101108000000c2c0c2503d0041c1c0403031600c500d640d111019000d2500c0c20f00341c2014042c0d90144d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 804405296 1250 804404046 804404063
    0x705090a0b03011d03031b1c0906060305061003060b03011107080307030e100606021b0f010807090504110d201909080304030b0f070c02150306040b090906180a0c12 72
    0x40199420901050040601d0304e03000d5035590804c101001600c0c030840303030001c0d40100c0811514000c00301c02d90900d401c1d070303045400100c3c5001d51404e111006000d507501c0a0440e00802e020451030054020382d00060307070700c15035082290116001c00d1500b01e903034400c08807684020400010010410280103540e0042040c940403d07460f046130b240c941442501171925402644070303001400400e406010701040d01443c1301d0601607510242001a229410800c522414440b08101199880c3e100b500b9903c041e01c0050000e101000a81040203100d901c610a002a1280782510040140114030b2844030403412141c840d50400d0074005050400014541c040c50511240c0714001a02c06c0d000d101a000460040741d02c64401d1070041d299600c0001d00030101d1042084140da0040140e03101000b0102811050910503144c1c1c0d02d0401082c02070403801e000b541c0c04424103040045401c4006520761060b00311110b02004030351220300e40355558a0b140c1c0010608015a102404990144012001018010030f0b00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 804406546 1250 804405296 804405311
    0x1e020609010c0206090d03200f070323010e100e0a020d1e02032a060a020304060302130302030f100606090b0906070204110c0610061d12010b04020408011406030705090a0b0301 77
    0xa106c8482c5280460118502080209010348040010007030840c2c4400070f80702c044412002c00b42c9540f2907000080001a0501111414010b140c030803c04900400380204890007040e4419542c0b4101620035600d680d00b45030b0809441c040201d01e981c0c02550190074010090310f2030382d421000d80c40e5881d0110f10200103030701d0300025950802c00310140f210303c05100d2410006211024842144800c1860700034213003003141110096000040798101d0700b040c0b400603110b00040c0042e50b031142081d40060752502c1071800c07019008502182a40b5811003549007000070a59448041d00d0608652290300801c800c1445070844504006000300082c0b4402440006d41d40c06a02c0710700300680150f1900141d582c05141004041d143c9600764001502d40741c1060760300f102001504046006030307901018060702c10b1002210314a00250005041003100800070754481e92918030307060080c000d0444501c0702c0720f5410040b401a0074081001429941d015014004035580c459424010b03141d040e00e1160550350302c030007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 804407796 1250 804406546 804406549
    0x204020c0114010311060412120c02060712080105010f0210051e041a060904151e0c02030c061006020607080705040b070c030201020f07230622031e020609010c020609 73
    0x608801031a0a41c12601c81d50441c1810421700020100b10380c003c0348104414001c07181445c0180d010a44e100201101d41d0b444c03c44112440524210025004400407440704100300e01c1d214146140c0c4a1580c80280607a40d0f10300440c0d08071803002d001c1e400750300142c50082d074080082e00015440444a01c1e00d42441c4c100d02e07101d00c0c008008607026141420101f01110341285003640b01500240700b01e1341802c5a0916403a41c4508000000401444e190340e8901001d040507241c2c01c2400810100a08024807202c1400c086c1d242e0780201c40603001805414005031020100c122404161002030b402440c076981c407072205842c0c815001d00f8000c1840f0040c0000940f42c0380e540024944248201012000d90b45144006440d01c42d001c0103c2280303070070072041030242010090510035040040c02c403c010028200000c40c60604c1407240c850080d0448829500340c038403051048000b140e01c0386484101100d01e11010f03004d00c2d580800d000354083c9040182d05034941c45a4510b1000500003070140789003100190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 804409046 1250 804407796 804407801
    0x5071b03140c03041e0302060d0c02010e011a040e0609030d0509071a09010f0302121b0f030414070e09070509060f03060a09060b030d1e0e0306010e01080d11190204020c01 75
    0xd0a40200f903000181c103010034404060204419100d6440e600222070550f40051418050b4603007884040ba6291074180c03415100b508120815152603000f0055429510480200134108825150049043c040c804498060018001e445000b464001c1c1d03003070030000f070361a80242001a02c918002d128622020a0403505c3d100c9660001c079011003490b981c0c8184100140caa00ba40d110341400349481400141001c8890034640b40d44869030713054401d2176540740c241040180c0180d0815584802000c005c001c01c010241d9408400004c40f0720031209803540e01d40c0c4002d00781104a03549441504a05030421150070143c48003a0001d50040000c50903040c0c441c04245032003011070310302c800683c840c14210180035a5200380310744000241d0141000207481c80c4040c0030f150b2200c0d101400450f07480329541c00c0600c00c140e15200d000004041c0c8a403560754525000f1000e600b0f01506405001740d0040c1d81c2002e003e591609003504140c0d01400038403107504142113855070b0100041e41c02c00e40070001c40c03010000a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 804410296 1250 804409046 804409057
    0x4020d030e12070305150105060703030507090f0305030912030703021903090509041a09030a0903021e0907020721030e01050c070b0f130b0a080f040609050106090902040f05071b0314 80
    0x94000f04400e07840d50070000e107444d030305031100503020405000602030f5403144d80440f03241c5a010b04022400d17031a8044101c4d00c5c9011f5500084021044000201c100040800180001c850440740d00b00c00c442e86171109501c0c1c5c4100440100981d014403507100c1c119000304106c1c0d081d240641000c03104543d070380000c905200422202242d40d100c40003400040b50001a03240c0b038020f600c5000840c01c0022000002d429401c2c90b000181c17050040c080714070000d02d011103800d508100081d01d64041401e1503c006507a1f014640100c5020803002c6520034046200d00400d03120440e0165904078049840d40015985a40300480440342d5008465010840c00000402002660752010343c031079a138030a0495544070407966420030314001004101c1684400c0d8028041500203503070309420465a181d40c54407100500040200408d6542810030002d14818950300458225000380e0b070600c510803541040300304603582103a101010620301c4900788080c43e151102e0075030703042c40317400c10f1040c004588611a4213500308 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 804411546 1250 804410296 804410329
    0x3060e060f0d2406150c12110a0c030809090f100e060607120e0f0d170309100f1d0f1203130b090c0a0f080d03020a05040b1303050615060304020d030e 66
    0x1318203040080c5044100043d03041c511900e007071003959000ba91a00050b2000422400c00c010003a0003200009006010040c44158003c581c000c450b81d8a140507030f010741202d40d20310b2054403010001a0301001982c4924441d80b444440f401c0e80b18103100551031660006010550400010f004140004a0b00d401c00c000ea8400342e2036940e01412100e040102110740300203000d004a1140c4043c600042d030302c0d03c5103488000d250054503229a10905524a042c200c18140c010040c00c144d038403034061995611a0040070745400c54081007012007002c16a03110514400509070340d000341d01010050050401550300004186502c40411461740c445011202e4117461080d1540c200450055484c5004180ea038010804802c01c004a5458409407545821006160106040d000500080c21a100720704480180802000d00c82d20b440d0026411184c14400f400200c0c0d030b0744504000300e4041038100035600d6034560001c0c0080d1540d9501c0c0d080c0b12803904036a800b1014031440380f540c42070aa0301c041c0002e609920 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 804412796 1250 804411546 804411551
    0xd050a0609020d1b0c02130e120307030e01060f12030807090801021c0c090807031415271906021e0301171c05070f0302150a06030303060e060f0d24 65
    0xe001304907801c50110500401d0000d003100000c0161a6906980c1c065042d4600000d059400c0c02c16240c1880c0f603d409200384030400004120001e0b03016840000300e110070f64000c12400fa00c504001039440c0c078501400c0c0d42481c140a5040000b4890b24030365074814400e180440019a80c0c0c081642a6008442c1044d62102c9a85903100c0850303039407055829800361845c0c98001c15141c1540d440d03c9018501019003079890002c601e41c00701c42c040054041c034061000d075421151410428902c0c8a41c000690804d8040c08010010310580c03002031804102c0011003084401e510465480754000c0d070000884840c03502a203504003404440481c09180282401d031100018210b0703007400c10b41041401d66070a10b46d00700c0b00008910f5070782d0103c00d0350101940f21100500c403000f1424141e10780180e07420350b6640000c1c81d008226030010f46401620031244661018040113494610b500c40814003216200d41055130701031019090b24184404a518a003d0244655a00e4100408082e80035228044201168 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 804414046 1250 804412796 804412811
    0x7030302061f0501080406022a061605040605071a0108011d0601030b01050f04090203060c0910050405061801050d05040303050615091807200604050c060f0d050a0609020d 75
    0x5406001c142e0b0302c9030a049100d442000580440c002401c10b5001e401d0420403960300145c10400300c0e90484018820040360a0480d551291000401d8400c6040801c0c40b8066031011171051029804020303040860364643d5424141441c2044039607410104c0b099820114413170352059016041240345003e80806400464500031004014041c600b01d0310b07581c202039104800420220b1031030a00d440c192075084844075030640c001400207018054040010b50300d8029001800815005880185a0500706591160000c4242a410341e058002c0784107103600040700b0030402c00701380301c005060201c800050401c203007400d2409401c40d0840c0c1049800720082580c0d14203005592500001110781c681040d048140381ca0b40340740118031030078100810f1552095014001c10b41c5180102e02c20034a41101c40000b280700340c100380460b43e80e500c1c161010ba41038022184030540c2424180100d0b0344110100e18041c0c500111f00315003000074407004003044a000e950b054086032044a0b4001480301c50b000740800301e84072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 804415296 1250 804414046 804414053
    0x1005010b0a03060512030d050a020903010c020c01140a020a02060a03241806051804050c0303070609060e0a23150106021b030102090a0e060406090e0f07060c0b01090b04060b04080703 80
    0x321201c1d004103204145c04039118644140010840d0700c105c408a90209080c0c0b15000218045d0160190207941942042c4048008613130000e02c0c2001000b00b41d880400c014206940c0c0c0807a4400c05010100603044045401c0140c01d10740000c01181d40305140010742c9486010130003604c0210100c003055040712010041112100c181c20b01021481c11340000c200c0c562400740000c41d80f01d8140e180f04060004040060240324050014a0320200301805a9507603030418600b400042c82440401c03210686800d5603e9003100c0d0005100ba0000c3c0d0000041403403cdc00180d120010700040d44031085070b0f11403900508040c0400d100018000e2400350000c003c21841d4902503003440e0100103046001c0da01c1403150444a5440d944001c003254041030b440d00d015166100841c01401c03203500b00c01c10560522000d030f18030101c005081d08a0820038000d40b41501c1c0c84060860365103003e030f500900100a01c0006111070b88580d40402140c110090000500e40d9447c0300c0c02c0300750b42150384101c04c80e800910080050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 804416546 1250 804415296 804415301
    0x4181b060f0305150f01140408070e010b0906041e08011503030206090610050f01030f090f050d1403070e010c0209010807090e0118080a090b03150f010e0f0405091005010b0a03 77
    0x89240350304050000e85440c072070407080f402c1d13182c1c40360340710b010400e08000340f690146032041840310107000701d260349079118590255105081d2061300c4001c5c01c0f480c000211111110300751424040c00500c45458145000d003590072007040610140780c040d11060000540d55024030132020b04800d011004607000b4a142006410030390002c1c840c510340e40040c401c12507a0b0010f80960400c0c0c900c2180c4041c084069400120014072000c0b40104503989480d0864080c000c0001040744002d200d41c0459105912004c0308030f44c940503003117031400b01040a01c041600c0340d005000d40e80b851a018035241d0013042d22900003401d40f15080c0d22200554100000600000303209010300c0c072594002c80024040307400c20300d068140000032040e0141c803401d400b00b1002601441140075030001d01c0000c000e43d80324180018111441d00740c103a6183e200d420044a1031020f94084c94403001d00010041400d030169005000f4080a0301000386a00c80300d00a54002d103d00f004107100392800b8081e11700c0c2280d2101041c100107001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 804417796 1250 804416546 804416567
    0xc150c210f0c0a0e09071106010b0c0708150105010318060513061a06040e040318090c0306090b01080f0702011b02010b1c0209040809130e0d0306050a0b0904181b06 72
    0x88110800c10210f200307400c2030042840352802d64600c032003a983c115085508840740d03001d1102c11b0080d000005500107154001d01300030b844002c10749820f607030741d00c1110b0354581e000b0314072200e2480c0d0440100020341c020340c4542e80d0800c04110000542070641d41308000c6440481c0c01c01660030700d80306d50205200b081d100741e0441e58240103840031111807030b00018800e40114800e46195034603280008040500ca81c071804401109804140400c9071105007500c00b81c0424211000043e11b40a00043c012243d4011040c2c030030b0040e19203e809072900014000c1481c8010040c80c255901c03184442c1d0007141d8900f41d881c0070a6a580005a0b210641c0c04001558084009441c1d0f800300048012001d607542c941c0d4240c104d5444000c40e603980d030b4481e02007007242d680315582ea24014901021680b0a10002c191080ea20141d0f0f40c040003040d495008010350301c2014082c07003a5204007840600301c2340c2480e034480d103c00c44108a400c040c540e500d5a80c81120300d6034914464400b210408100502c68000c0032110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 804419046 1250 804417796 804417811
    0xd03170114010e19030203070314160b04122f0a0b03010321030e030403080a02060603120f090f0a0306020703090e0405100902060d05010e011502030c150c210f 70
    0x58800071400700007442c02d100d00c40b0041c4214550030b041d0001314444414800199405030030f84a03166502d050128480222081040090103501c10582460311210341c03030416614200e10490600c2c0c2800c1e425010a01c000b4000c40d00905036001071000305042d685e90381d15180c0080400d1130703070a80010078072461826503400304890900501c010700000d141044019034000e8032a0650480d034000d418105c02a04421a0300c44880c0400540402888500740080480715072640881d03020392525824150360351034100211404030014880448007000182c014460030000800004040009d0390000d0324040d0300d94070850746103030b00144610030160080010401410072018020991800351142911400d144956240455031804010115503030303103044e80c803030b0f0780007080030411903031280310240120000b8040c9a0742302000c040044103240c0b0001c1220135810703404014000315101c20030b51050f2120050200603000106000c2c000340b0340540003654a20326a012100e50b00390400304c010a06211016042c00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 804420296 1250 804419046 804419069
    0xb030c01030506150f070c12021206071e143004080304060c05070515040311070503071e03021018060306030f020f01270e07092702090d031701 63
    0x2103e20f58030000000081681500800c2d034130001c14000a06511615600400c2020011004180003c00c03c0c04222014401e440c5500c2441030b00450070341e595005c48059000400c06074a12003c1038150b01007013a0385a040c24821411101604805083c0c0c02240d280000d509a0b5160320783c411184d041412500116000d5061460806072a0b040203440000d0025083c0364642800b000b07454440c00450791255000b10a4900445c034440b51075482d4102078a0a6000464407061450341a901240b00c00c200c0d80010010601103280c05504e61a8a40042c0308001070ba1034440000056220031245900702c6404e40d49944220859a41800743c3c5c07040c035001242018541181840011802010b00d1103c0390100c50085010000000403540096242c040503032182d980c440d00710150b441000d031803083d180c036003402c100c041c0c0c0c0c1c452040701e040724144126008009144200ca1901c0901d42031310181a86101004d854040d0000104803043d011240440024801002c0704600b440441d840c640506414000d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 804421546 1250 804420296 804420301
    0x30109030503090d050c03070f171c050604020a0c030e032112070201050c07020607051e010e0c1806010f140f0306040f09030e011b02100507050f070303021b040f050a0b030c010305 79
    0x1c947ea07800768542c01840310500504400910113074201c08244007031210506070b655004055110a864855844801d600d400c01000c540719141a0094803600081176981c00c15001d4551011680000c42441b002c1d014090b00c160350318222248050043c083c1c0b6000c20580d50f0f00d540c4550510303501340041c104007c5900d81000d02181c4060801103921040d01295540e4031089582030041c2018004004c4850b41c008001c1e1008071114190840c02c0c10f05103030700a43d6072030182481030010220101080c0103401040700001101d542c020700980c02100a546014459540e50038840001d940c400f0f2a0300f0140341d808010080240780502403600c0b140368003001441081c0003036070081e000d2408a48414103204683d260507000500c41c049a4200700e80041a128055008580203011540001c0c1d094809020b402000c00307a20300e002401c103089aa140e07005013458078042c007551032680d0302808080c0c0d005466a2402444400b90701425000b1806540001004000031041514004a1440c0141410305003802c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 804422796 1250 804421546 804421567
    0x20112050709030b0903161103010e0a170c0312131403090a06050307030b150307082818020301021b240105040908040f080d12020f0304021e030109030503090d05 71
    0x2c114044079070240c0f0740c0f08180c03200b0100a0450041d6101440004000700100082c4040c5103d03c1e900040c069008024804d166078034203490b003462100142c240141c01501d00701300182c500c0102114440c41054a0a02e920210803510b01441a59040801101c41c0908024842c2141404091218410086150005450124003502050b100b0320341401004000039080038004d4000000080c40140110007101011400c003451380c0042d04c40f140001c0e40203000403201100041502c0840022000d11035400301c24214440141c46103980040b004141041d10074010f840034000352071803c41c4e04028410071610a207843e49010078001c9075180250f00001e260401881c070003101c41c150b03001698086aa0505800d00c480c40344680c0c1d01c000290340c0640030010b030096010660021002c170381c0e55001005500e600409040e40205112300b921b80c0e01c10000f180062412031100b2021051000340c40c00001c104d0030019086445d04401034001c5980082040075008060000803840ca0942c10000d01301111000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 804424046 1250 804422796 804422807
    0x314060f0123041b02030c0c0d0302120c0109060513050c10051614160608133306080a0b0a0c1b030c080d0209010f0c02100315051c0201120507 63
    0x20068403080c04601580003d45903500845506070784035225403860240c8035002503881d446005086c03068001c1064111052419032000341c07078140c141c0e00030000c800390880c6121090784441038041c507640d41c4003050b40000d507150160794400c0309110501c54007107010741002420b00102100d81071045048480c2e10f8a5190000203844810103024440060084145170134040d054540783d002400c2c2c80b0b0700303030013807031888203410b65100b40c520982ea0158240ca40708204101a410510024401d00241c042000c103000caa10b84c058550309141124001600b84e40390880032034050750800c810340d1700141031401c10f100c3c0d07911565030490382c941000c1103401c042460003007250a03150030300d20b511140500b61800b031500c00d0f00a201d00f81c0c2c20110703155a03542107111001c002c0d400001346502061520101c103810f1402400c65000b03d80d006403071003851441e2150120f00a00056031303d2081d002d0403c0f800301e40340e180d5642d58842d081d00302020b252412010f00016003945803540e503007031009040c1000c1280642d80072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 804425296 1250 804424046 804424079
    0xf1b0303091511060a02041505040f030303020309160f050a0b070c14060c060a0506131e0c0c080c0147040b3d140912070314060f01 58
    0xc00c2003031010b1180004860a101c0b4202c0c03c442403040505100c4806003643c000d000700e540740704071001440e10402081d02ca0f4002e51180c2501e501c114681003002c40e000c0d0f0019a800038200c0705a0346540c644014000c1094240d800500c1d040d54241018801d27810034022410203080e082c94464101070384c079039401030703803041314041c01c10101041c145d0303e07a007a120302064640b00c186510543d0454544240e0500003803404a61041c0318411380c6000924499003440342228160040c8000340e04c030560802c9030005001d80704465020400c000e600c00021401c1c00b0080c1c104610300300f001042400c00f003400300c1000c400c200140c02c06c0d60440c0c03180c0a80c400c11030128240441036442090700b0803103c0d0300050000d000e07414034550000c0f8000516002011050480c1c0701c8500821200f40c2010070160300d01582803041d807403c2001c6052044800e603007103006000380000c09401003128a0210740c0350f03210b501744026a44211843c1d041c1c0c09800020340c00078400507602c074681c16094210796162501f00e0710b2a0400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 804426546 1250 804425296 804425309
    0x609011104092f07050706050f0d0902060c030d2a02070603050c040509011205010c0302090f0108042303071109160e031c020c0306010938030a0f1b030309 68
    0x1c0f50f41da2901c0340040180700040f140600c80002811000110240055210f594101c07001c1c0100c04002c50300d80c3c015001d50f100341c401000d20034100051001881c000f08a601026680850705000c1c11038081d038108001d140c0e0f98000e0f000458904c003004822418039544d070481512068405046190702580000c00b8000c54501d8500480e10b525061004c2d0140d00c9a44c1007036030460607642c0040380c500380745502d07006803e00c80d600070040c00781c400b00e04404900580005551110f0b0f844c036802070030340c420740000750060302440c030303404991080c0c03148000181d50304c04151805070008104101440f103000c901c8250b084056400500f64945181d091100040594184045c4011100b40850b5034500700888a21400340c060246c190040529000c0c0da5001030400040c400e20a020021601d0001030180070165442040c2c09860505100c50b10800314911018030140001d01e510301e02903990702040910f44042c001c40c0c00049056850a0400d4980301201034039190504201d030420000790301944500440d8a0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 804427796 1250 804426546 804426551
    0xa0810060c030f120c0e010e1e060a0318060c090e0106020705090915010b0301051311090906010c0c031a070216051e0a0b120f043512010305060901110409 68
    0x4455410384e0000c18800c05214241d00e49108184c8081c0c01c1150f4071500c620076203030369280b440210104040c402c3d0507264200004954504503005042c510081c0240a241e8200410312549500300c6814036200a0016511540c445c2c42c282c41c81c640050880d0701034100103110400b2513040c0078010750b4a075807600c2441d01449000000520444042c0011038650007802840923055955151048183e0028021944100d20605c65a0006105841100e80700b00310312803264100480c00082003150300340104024103014051904070b0000707046007200300180d80f00b209000788070600300044031482c40703008000c1c5003558042c1c845914100c003800b001708102c40c01101e081c00401a005000084484c40e001c106070000100b50b00032610b036148401a11104500c40f41c2e68a860f0303aa0310400c1c04068080ea8090300e06018003e0001c000010f02d034240100c601544054942d406a200d03401c1c8843c0e0080e44003140d4049601c00500402c481480502d402105600003030141000803252503005208610a56803c0765 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 804429046 1250 804427796 804427817
    0x60a080d08011a040302130b010905120601030b10050a170d0c0b060d06110a030f0e03040f0b0c19080714010c02030a030218091e1006080c0a21020a0810060c03 70
    0xa0fa0481101d010f0b59002d043c14090304040030b1008080c0c8400c1031014007003512004080b03028149410803151050360314004111381e074a1612402641c1c0f13005020b00100f03401d40200031840d62070710100b40c170080a4500c0592800780704194100d00340310b568038400e41004082600e04010407003854003d038004c0800c5030038059200c080c0c074011004190b400640180d040d0b01044154030341750140d10001c0060000a4280800341c0000002d540f80c1c402c41c00b6081d84002044401c1c8500031061014111076031540d0101c41a2100660303400740c40101180003150003c00000c0c0c3d00c0100054641c0050308151a18001e04c000c442c0d409000e5100c2c007855145030704043d404902c1b0350b00e260400014050880300603100128604052448003212001101c41c1c8580505482c040b03002c40c400074901c541142c00030f9803420820340b960481c96605600080c030304000c0012003200800c090f071085003001e10058004030010307038810704031401800c0030360010541c4000d8500c240c0104100c0740c01c20500304006c0d1f41442e00740341d1803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 804430296 1250 804429046 804429089
    0x8151801180b04150f08060135070f14220b06090d050d08011406030c0c03070606090e07090b03030904201603030e0c03100e0a021305060a080d0801 65
    0x40110591290f4050305003400c1c240c0849070f048140c802d41d524429a500703201e46418080340c2e1040c0030711035156001e140885860324854041310058140d403502203080301543c0005405440e1a06a0b008141a0460318034100034190300481e18000d000000da40d0320100700c0482c052064109040d040c0d40380c010340c8a0b4582c1c44555100c108442250360300502c120148080c509026aa4040c040148408104420b001190f00c02c01d002d01001c0507400141304034070b1a81d0f21200c201898008144582d030b103100900c150b400144450003100c0103480600b000103a01c8800e80140b61900205500034840b051811b1742c52441502c01200325001e095080d60040b89030258070a04c200700035031059907400207280200d42c14001c00020854108030307500a40d010b01c00042069452611131040c0750500d43c2c9075000c01442145000581c1008040d20f1042040d162142e5154000c50702c042d075050100550282d9603010000c0500e0f12070b104c00d000c5c0000c0001810603181040300540010018001c02528419200811005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 804431546 1250 804430296 804430301
    0x80301230f04050711100e0d0507120c020409062901032304020a03080403083604051005030111090916050f07050309150a1e050a0e040605040c0815180118 68
    0x40207a08030441b40710350720413005100145444004c010300c5029000d1040c00003840350003600c101e01e81001b80c15940c804a940243d4403031246050890b002030300c0381c3e0031002082d55441044a600c800b09004001190035803603a541c824001105c2e80e0503d86041c3d082480b004800c4100d0b16411060081200561542d0002800c0700b0b00b50340c001040040c000601100300803e80c8043c04948503441c5414a040d001804038100703444401009400046800128140c180303403a42003103070084001610100213540301d401190030b5601f020020081c0110020300403005041518000e54800b0b8210b032404661094607100818611441c803003150101030102e09041480814802c907083c60800501000c0800300c030481200d0141c000052550100d100c12556032060061907850100700c2d441a51001c0c41c052074980b0594071426207400380d44e0007560b40d40c000328054032031f48a150ba00380e2003034840360240d1814030b070a00e80c80b400f486842802200d080c045104001c0700400c1d9507054880c2030203010b000c13035903150b4603000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 804432796 1250 804431546 804431567
    0x20306030f030a0507060e010b0114030a0f0c110f0d080103020d0c1e030b07020703030e1306050901290f04060302030c07150608070501020606090609070207030807080301230f040507 80
    0xa05000c000343c00700d0642c2d0400001c0c00c101d44600f000340039880282200508840c510303d01580030440fa00420000d012010004560200c5100700000355043c4101c3c4903001c8580782000308011401403024821350002c1003000d000010b400200074403e141c098400240752010600c8001e0081c80d10718800d408109003988104054164044c8001000e51114001c1000d90700e9403105523800f2000401140c08a171000c180356040c0c0381c0503281c020b821130075502400498030b0b111580b43d01803599080040f441e9900c045502d0300800c21400c401076020350b8040320080010781c0d804125150b807800c02050b44450303140741c10f4404403240c5040041c1c03039644110110505204040000f01452009500070701302c00c02d80e9000300151401c0d1411641903680754001a60340d10b03010380d4070540c050007400024070320b4034000b150640e001541d44155a1503a6696941034041d400c05d940c2210715003004001032045000500800f014a030200d00c00d071914142641c080b80681c11b202075031501480e141ca0001d1035581c000c150000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 804434046 1250 804432796 804432823
    0x210c030433050c0717030426010501081504021306090c18051005040306090602040302091306051b071719030b0f0a081203072a14160902030603 63
    0x301c42121081c0109201000c00105001a0324110141403064421029994070568070f00040600c030b401c020f1881c6054620524030030183c84104008121602c040d840c0342d030b40b030444072070650003601c40000d42401d40340141c2000c0c1075035014604201071a12140c00f8660401d806480c01e0602003a20b0f408240540080d802c60380e407090401c400500702c1d07940010300e400c254503c1207500d00307881d885004100400240c101d000000034018030042c0040b9007103900400149200b20001460203584e40e02148444030116100c4070b4110100c0d02030000d1100901440c0c0d4046a1100c0105110324100c007901346074001e400000d0844030b40c2c4844a030212100f00c0c226540f5031910002c0e1412601c5071200140546605c4401c070b80502400d0300100240d00381004641c0951304a00041c0220b8030304400a016540c00040c10081042282d006001e0550080101d04500b130b122000c0207500c9000741d041c640d01c003981c207020701c2040b0740c13103c05000d04920720b0741610010f85150340300141c1e998803140300092400200c510780b407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 804435296 1250 804434046 804434069
    0x304060e011407230a020a02040b04180305031009090201080711420405122104060204061704080301050d0c0b0a050a0906030c1403040201050c0f1e210c0304 69
    0x841829003140c003801042c3c0c8408008060030340d00300c2d4130038024000c1c44203120140c0d020b03c0d1410b0041c501703a00440070100c0080d00c0010102c4c0d041e001c010108090003030640c046107000081c070081031603c0141e0400fa19441070b0500180e98a68002030100c01d00420304010001c00000458110505000b01d8640300e0414080d004c0d0344440c13250080041401d218207a1040c1c1680d4a9600150241d007880d44c89550014060a030301203000102050640c003849142541e50a000c0301c0c5d00302d55074201d02c0d07507000c0c9004200058956041200240030948070f0000006d24600e8042007100050a80d8210b0303065990030788800d1291003c500d400720302c1080c5900000390046010400c40c92460b4010040c25007204980c1e580c641d40c03a9101026800c40707030709180c55400140d02010a041c60b0100100440d00300b803061405a2405441140150034444134096512486d00116641c9542c02c3d074012407188083c64840c0513007000d80392020807040c3e000410741d4100e07868a0102da010300680301402070782c0042c2040c10b0103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 804436546 1250 804435296 804435301
    0x5090415080c03010c1b0311031905070b13150e0f0f0c0330030c0c010f0e011109060706050606070b01140a0b0406021525030605090112080304060e0114 67
    0x1c151244114550b19001398a002d40300c451403403041c043c039114912041b4000a00f1641d0762400c03265446020b82d900800c4c401000954200c14a1441c2c820b01d00300c480e5107a81c4c80e6101403514140d0fa03074011301409041c016960043c0d001c681d07803503a01d4658290090000440310703602c0d01340d030303041c185000614155402184540002d481d000304800c2029103045056400940003c00880404883c2681003080c150394403501480304d001036001140c202144250950801200750b900a080d110070040300700007151038601a44403030383d090003002d100c1e500c50282079090440c000042030490080b180050401500d4101080d074540329035003151022600240d4246072903850b0140040f00c0003003a18140d0080e800110f000400c0c244032019501590282d82c0540400191030038008a00071025100da03070100d201c0c0154104054071764602088141181e03d0200da22403510701081465141603200650101c03000c01440000f480a8040b01e900507445000015009005a4410300500c2a20030200004459009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 804437796 1250 804436546 804436559
    0x50a0b0d0b01080f0c090d0819020c0f03101505060f0a0f020a08030103230105090705010305010f080d0f0905060307030b0f0d023001020d0b010207090504080a05090415 74
    0x1040d40e0850180244074105120340115042d0008030780004125488038082440d030a00384005144e14103009010414024254942100c1d0f81c1c448030415283c40348800c50101040d03010300001040c420304940c104684d02c0182d002c40d031103451a03d60b0b00760032640e400031100180141c00310304000e0040900b07400d0325040d2003826110594010720202c80400c9144605281403403000448a0f02c80354001905802c60b4030310341d074045207414100038030380010b41c2c02109068119001d2240301e10880d540c01c0106801d40c45c080c005000c4440c1030f0041d07003e001072540c0c18024614002002c081c0101d8901e0100f03010242103004403490491500415841080007049c000751540c07582020451240484140c1401c816500c01c110400461260007034200085114540d11a6003003824908142280e2281400000041d111310b400ca912441030041c1182d0340c5c52104d0881c0d40e0400070400540000c0d0303c02c01544c2025211028140641c41405c2c0401100140d007400d02d403190340112050201031016044c0c134540703425 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 804439046 1250 804437796 804437819
    0xe01021b0d09090612020d0f170d0b0a0503071a0408030a05030f0109090215180301090f12020a03080a1a0d030819020702090a020d0e1c020d0e130c0207050a 69
    0x7507000000d4890300c2c002c100301e0030620450084450701c2901c402d0601707003070f400e02041d184009001e0302c2190128085001152000c4224007460700e021501a41c0c514a60f25030300f00304c940c1c2c01083ca000b0f501d070150a0105840004419054520301042032114048442d0302000301c0c07003a038005040c140008195503458542020285008403000d000040c0f0580c1c8981c00007023114580c4e100a90302c0041c50030304000617003d00380284141d110000740446103044030401b19003900c0280c01c08940f02402e03424030030b09000110041122000340c9201500036409113807002454444c01030506444550349005090f2005504c6d400b039074080707601404d03150303440f0352504000d01405001c0301c2054462101007502145600248211303040280d009003407240d584c40c1c28144000a420103a0000070042d502e0007822410b400c00c015442011038560442440000d00762030090900c4c60a550030402c2c000c4049180e09203980700c1081c00f0b010a8440400034a00c586c5640883c40d10040d0307440f90750052001d290100d003108510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 804440296 1250 804439046 804439063
    0x603020309011b1d01090b1201030203010c080403170613060303111b011b08130803041805160e010207180c23121b03010b1206040905030d0e01021b 65
    0x500200450f00e42c8080c059580680fa40b07000c00019441000d0740ca49184541324040344443c1803520803c05900d41c001e5543e9540880c030024141130440004004515090184100c8408035240c06105810075a0f405004032003407683d11540031500c80300088d0146c40d5140032038504074440509228580e541d081c00f509518084140c2c03190303801404e02d1b000c9120a0300b002c0894024040e9a0f5201480410030f88000044c111a0115071070300742001510015000034407500c003c0c2040d42e001d95526450b25000301c000001c420aa2003031142450100403494a9005e20a810800d16040c45400380b2240c0004070300340002d80d003094082d082d503a0340e983c14010040c0c3c0007a29007032207a00d8059284020100615035450000500d601a4008100c0c40039030300b00422104d5004070f4100c2140b4580040180c45003e40e070400d8000502224020400c00c030303907018031001241c00070b1013603404001c4d190b025290291a803245076000502c0540340e00e404d2103190402d50450750080d81c5550b111b205980400c8003980c0781e0868 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 804441546 1250 804440296 804440311
    0x302070b040b0105031b031b0604082b090311150904050709060e010305010b042c0708040204050a1514010c06060b0c1e1f1824091a04140706030203 65
    0x1009000401ca0034015001c034481b00009008021403a060540c1211101c900b002d41900094140b0001508150801440605a4503c020742005040c1302000b1400d03e0341125080c01009007000c070800105941e4540130030030110640303089030608034903d140501442a04003030381c1c20a29041c10084007a80c46100301c0150f0700c15070f49980343d23079071588011820398500717014200c4100300401c010072010702958405500b00c03c00701c00c2080c00c4504c200340503440c0c3d5011a80d61000c00c4081c002c01c0214580b52041992001c942c00707042007591060b191420508505004070300424003103980900460b8016012801d18a901450070320040e510b0329183c20f0300f5008005900c6107485450008042c1694800450744010060170051011340c600410051381c100c5c00e0304000e1900c1e580e0701c0c1595900075001c607016000c1c900883c00c81c0342e290210b000030300c0000000c02d21442468904044080000c1e00c4a141325004071019080da485a11141007920901e544a1040081403040b40c100254803501500a98801c060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 804442796 1250 804441546 804441553
    0xf060708070b01291207020f030301030308100f0b0a0e041104080f060c03070f05130f0b1b030f0703120b040203160813030504090f0f0e0c03010e28030302070b040b010503 75
    0x1404041410100c10f240011140051300303200d56904c08445100c070030751041451040741c440c94064000382e8155031003a00290000752080041049404030704041c4070041c000070300c41c04d4045240c01c3c030b0020103010700040001040002007508009039910b8221201c4055a011003954803075032000540d90f40ca01420f06440e050043ca0000340181000100303581c8a080c1c01e8a40d10214280c0d0700c1c003110386a00851000450030448000405c0e00707160155401c002d41110300b03d107943d80001040794100300558108840082e40108805106011510243c0d018554982040407100b034004c8461006400c5a210080e0498408020071405e18411509040c4200450702c40f03901c191508102c424010b0b000b00b10281c045a001c03c0100030010280d0300a524050a5039000a1b103540f1007856141a0345224504c170301d8540c0905000c280034a028810043c0c03e84203c030003081400c840301300c000c4400b100c801e40d680c9140c20590701c103001c1c14040d40440d900e640c0e00c003090882e245080d00d04420159402e02800707002c0d12 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 804444046 1250 804442796 804442829
    0x11104091a0f0603040b0c0c0d080f06030a110f010908010e06010f1e0501120e0d050c25150203070618150507080a0b0f150a1713020f060708070b01 65
    0x41611591000c11405001c4a14540e111b8581d11143c0001411802400d03008111410744190300344211030480c204ca560f0000b1905054208010101001c0c001c18405e40080c0c0c01c4100094040c61907980200090b034417010300740340e200016109c0c0003c5500140903942001099500c001c00810031605a90800120801d80c503101c01d000c0c95696203c0c690112204818081441250700038585c802219103800c00100f42080007501c01420015141c040c8004680007051071103036402d0500040c4201c041c0100e1000703000f40c403000000c0c5102c0b41842248903044459008000b024070078001c40d0201d1341c00071404d1100b005160039040c03901c0e070540320030f4032001c0b07068524490500e901d01031580140a103a0301c80702c6544a401c40384008008071070b2800c1c1e0008040c4021041c585502c04108245052401e005440301c59020001e44654000720380780740c000341602d080044402460300552101034060b616441c003042a070f0041001c1e4840c1c5038002e480c0c15004201c0804009004888a041c0c2d0038480c114180705 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 804445296 1250 804444046 804444049
    0x6290a030204051008012c0f07300c06030e0307030c02060d0e0f0c01030623040e011508030c010c08070c03111011090307290d02040b03042108101403011104091a 71
    0x11100040c15000c07a4002c8940ac000a0001d41e400c06404500484c118940020b03482e04411000c041e01003c40301c0040c0d00c4810046140c05d0720035032040340c0240d40a980b60004c82c1d41d00801603184180b000f84107500c0400c1c0304110380420f0340000d440a80300c0084034000300c40612088d64034005a00f403180003134200180410f03402d11401e144424110006158810800e0241c1000301804103180340441540d80e51480144042c00d0800c414000d001c0700000d10703030300e801c5c603050142074510a288030b809020b80c14090002c190f078414800504140c043c6441c03070100200c419407509006458164403001030400d034615000b864070100510044d10100c0860310f20513030710b0300c1900c13140d1058010403c0c0014003181c03e182c01c00c42e0034000d0442c3c03141d440d40103141586070701410b402c942003a03906548ac1000d1110303810f030403400c1c42e05081c9075004904001e450340c600001c0c1c41002030040d014140542c240ca20034088551825008541140704504201c3d031503945500102000303026000701c4502013500490011680d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 804446546 1250 804445296 804445303
    0x7260c070c032a0e070c05010b090a09140c030c220504080c0d0305010f0b2d120a0608120706140103030203031009150506070203120706290a030204051008012c 70
    0x1100e0005200050741d617510700050364500e84540701600c81d5503d52100e40300540c0d6042056100d41070102000038065450300b0010311401559802c101d01c3e80c030050440c1e600e6a000900f0f881c140d00c0486000441c8001070b40407101e039902e5241e50002c894240303c1407100b001240f50290902481d4082254640140a84114240d450a2160301c01018031040b0074818100c00e40020403441154100d00d50110002d070044000007855082d07002094003022900f11800e200c1010032607044002003005100e4541040c242c0c3d03443e0600100c4400700e5a40000b2080b0030800d0030381086c0f0840c6150029a5460341c2c0d20f09000e912688108d030310600300c2c6015200420428040c2c4541201e03d41f80000c40c1e401a13017802e01340b0102354024001640d2600c24000c03100f0310300c0c0c000d40c003d110792842200d001c41c9100303034032001860031000800c8841c91000c00c2114076000d2345a0221841c00c40790110340c0030807182c03941443c940d003449854100c0c6003d9400c01a012000c03d40000b0300c086003040d204e02c26003d18000e02103040d103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 804447796 1250 804446546 804446549
    0x918100e07020a0b0915071223070314090d0507061803030f06121509031b0309030309120b0a110c0d0216050d021809120a0305040b07260c070c032a 65
    0x611b0026600420f03891441058200c040c0e464804000400c15202807a114501c00040a0f003404da503480004c1001d070302d81c0340c0580c0f0100c3d04c060000c2599418240101919101d40140d41401c118011485400b80601c40d005207000112400b403072106000c190030010081e0a0ba051441121424101c000607095441c030300341d1a0b034940081229803c94061307165807004e450303040350580410a68044141c01207000645824950f4803e4407034050311803842c0b4029108448940c00f01c1020640c61108070080b8000740107481d0b00151142c4002007042901240c80514011005042207511842600300b81d226000941c00440801e55400c1059060703031041044a004040b14000b500020b0368055000541c00b080b180e2600a1454015200c02c006440f4480c00c05802c0082c00c907001a407038100340418400c2ea100603c2e0060040c0c03400710702c800c0071400c040c9805c013009070584d01c8c121818400105041401c100390b8208507400b02c202c590084d0350303040443c0841c15009908048012410b408207a491300c040c070440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 804449046 1250 804447796 804447823
    0xe06040b060a020331080307050d0201110a030f06081905011409030702060d0917120f01030c060c170310180e0c01030e0f10061701020918100e07020a0b09 68
    0x10300d44100e00c5d600b126095056000505420f400217a00e10400e41010292405032580304001c1d0f4540714581411443c1241d020079000569141561400c0e0100c2c107034044030220310044c100495402c0040421100a00440c3d1040040e400349031b050004980440c0341c1029024050380091240b60840b09401c400c40200ba41c050703001d54404c001c03031401410024040c0095007008040010316140e5a113500024144011035641240000902c0028000541c5549034004003040400c507421340c1941d90701c000029840c028007040c016a00c114034200140f032840d0800c081f402e03604860320307410000a001118450360040742a4051071400e0564030480358031442d05081c2c012402044200400c200641c000d10740603403409524000c1507144d022021041041451204003080000b49452408250301484004081c1104407039004000d141c24581d1a0040c003c00d0b0082c48544002a446000b82c0140d030b103140d80d1010401401d05020000c0c3c45401092000039030f4055407050b030166a0b0030f01070715101c60300c00b036110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 804450296 1250 804449046 804449053
    0x10320190f1508090d140c070b1b0a02030a14030405040222050105070b150d05010e0f06070c1505070908070609030c0605160308060f190f06080106051207030f02040e06040b060a02 79
    0x106846201d80585d25070000303200c031f1320b084050318045041c640140c0215031192000109040640203195400401764554405040866060342c000307501d450a040c0c0c00b8001c80c40c0884001c40e50803061044a0003000020021983d9100c540004102400078440d9020314000c0c0300300004095001c0d0044601c40c42c1d00c224214419a03600e002d030502c05110042c2c0c0f0350400f00c0c403040036001820074070800c052007091000500c50500800d1700b4514110f401404403040064070022400041c80075401a0102c03484032001003019514148119550381040d4031a02280c40b0310755000030b109402c00d41c0a42900d001b251150072080e143c0078191200e119060801d00000d0101c800080400c1c130468a21350450001010300010311000c04c0003c2e51410301114070b0448a1300100d007048800c440380300010042c203d9081045c0c880d85007140c040c1160140082caa10035210410000300b04901c20b902516016100d174400311b443c0d0b40c894010242c81042119010300840c58004140018644a0140c40b032005881d03008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 804451546 1250 804450296 804450313
    0x612010b13090303061206141501050f0903280c080d0c08090a031b090b0d031709031c0b0f010e0a090c05070b040303020a1403010320190f150809 64
    0x1c00c1c0c0241030118041c0c0801d580c032140810040469650209101d0003400c0c0454048051170709800100c030081c06e8038600c82003c40c02400c0e41e07600300003610024160014403c1c1c60342c00340c001003402c0c400761101d03120100c1c995007501e48002100901c81c40060307004440c0a5555604c0348042d0703a48550100301c410103d40081d540348001141030004214120001d0b221050301030781c1c3d90f100001d5084114407410406141081404100d840740300c0e100d41d00c80c00f1920380682880350b8501034440758103070074403000b2042110000b4510003c1007040b0f806c4080811030050311100c55401c40300091001d1502c0a2040610591408156104003a44104142c2c000c0014402a2601041000501c0c82c080071005001042c000440800c0d28034143d0341c4614001d44000d07a56841901c4020002150400e800329222814401440818090a080b0824814001d035244540c0752900028aa0306800c0c900005100c82c2c100020412603221100f400c11200500341c614144a80040b06032030301c9030101c0e0380b00302560010704d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 804452796 1250 804451546 804451579
    0x10110307021816181211030d030f0b15090603060d200109080f060c160c0e01051915030b0f0405240105040803030613091203140f01050906090907090905060612010b 72
    0x1581780070030700c19049010744440d00d601080c04d28601c1203441012a9440311641030f00f102c14059440003900490300c8114100e00c0343c4211060b401212030060044401100145068440c01c00c103201c140d1308042c8030140895001c042060b000d540442d05070020380c65500c001031340c1c14006212420444800040d04060386c841075011069040002c42d03400d00410f046030040890128100c040c06002400c0700c4070101d40c1086c00703010691000710500f03940302c0c2041e04100680c1c0e0641d40c2c940500005840c0224041c0601c4001919035884c881020342d2051504080c070220340003c86000110a00d40d000743c00540c1248070046d562801281308a0110307030000c000040c01440d140d2980f92075000080d00021b4840540d031030752a0080805d5a4000120ba41e83e84c01c1e41c0c0c04056000b00d16880548044200c44540c1044007042625a001c1c01c898040c100b00008039455a03c10f00510010b0030241c0410803038140c80381070041d41c94405680690090090356100e506600040c02843c8040030003070400340c0d41d40c8a800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 804454046 1250 804452796 804452819
    0x19050904030e03190c03051c050a0806010903171206190603090206040905010e01170106050f04021b03030903041805072a050118060b0f1011030702181618 68
    0x403415a49400350b2008500301c13a800c2d0015811907402642d5018446085240082c42d0446000240b00c01d0000861f40d20409544001100c1a140c468685032807941c0300d800c0141c5810503503400040c010f18040c1c901240c0460b075500039088580c81250300615648614060080c0560841c6e03c0ca807007414031110501c1254008c0d0400d4142500c0544010b103801d40d9400440c0803240c080e001940565486c0004004079041034100c10700700249500200300c20340c988800112800b03450200b0900458011900064060b0030740d0202e05404251002d03a6640c0c503104600c25205d0b8000d0084140303012000d90780c064140340074419140308120540b01c1c10303000d01c200034801c020060000c0342440c000305891243d0001550a00a4580e00d03808022400310310300c45480c0c120f060310211540240280e0204460301101c0d96541a510101d40c6581002494000b04449060441c805c0800203504810420b0362072420002c1030085601c14400031036a110325036420002100c0d445420540e0f0480c0f001c0981e0b09100174030815 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 804455296 1250 804454046 804454067
    0x16120f1e02340e0112120201180c080706110d03023006120303040b0714070503071a01050d03050702060901050918060405070f0903080d020705030d0b1905090403 71
    0x140100d0302801c0b000031291403048a1912580300c48040040807a00600420500e400a081001450711041d810710303080c5400c0712103680001e405a0840f0075070440ba14001c2d400400c11507a075006514008030b285c28000b107002454030603585284107003440001d100303200c3e800401991107854080d09038441d010004801035006040c10305800341d02c02c2c1280080814540300600811080603d000141c0342a204001170160004801100d5030405c0080100080f242c0744450fa100361a41407120000c000210144283e0140042c010980d10001034507005005015100e030201441a010440b003036078070749040c002081d820100080100f441402000d0052074000d01a000c03030030040c501203052142d2040081c0702038003480c54408822035440c043c81140e0600380219680201c80e800c280e1922000060010003707445444050030850020516847e16030540d01140c1419070072000303ea4980300c070189039000a01295000510940403140441c60342c10010464000b280d00040c02d040f80790740c8030345054400d81c0301d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 804456546 1250 804455296 804455357
    0x30b0a1502150a1a040f15031103010f05040503030708090c0a0611070503030c1203131a1b09011403040c03140601081b0108060108100906120c0f050603180c040216120f 74
    0xc42907410906441c070015140114011271040411074815404e16003182e682030642c454050404c005c00012031400411a0303040036081c60001c01e5a5181c0b01040c2c1803000518040b40e000303001d080300081c0554880c0300850350702da0b188181c0300341c1596141096528801c54100200ca60000201000e6041c11003002e07580c041000d4010312310484c01940c03040ba000e000688403081330408041031102045007101007441c059192424540381c01100c100103000100d5202000030080310020000c2e0070410800c1c070680c0110362068145021031110b16160340c4a94007401845058800d955161403a00d0041140000d10303401130319000140e482d003078011100d2800c001d1564040c00030480d40020403201d1449040700600901140c202001494030700094a61155880b003500141e00c26018401503440d035003120b0f000910f52120301c980000b80d40c81503003401041c90403a54450b1001c6251908413a100c80c02c184040d120743d1a00304848480c610640e010001c01010701c000440010030340c030001410010035184c0006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 804457796 1250 804456546 804456551
    0x1006140a060f0e030d0804030219021c02030c030d030b101e030506031903020304050f030604020a090b190b03190e070513090c090605240703030b0a1502150a1a040f 72
    0x1c1c80040707490441c042d10b61200040381b0004200030f15605100c007901c0900740382c0450300c250207107400094440716104d00019070400000c000108550b410000004c1941c405400d0741c0711002501d5002d402040302c000034502a184021aa070306076442a003051002c2081160a80b00d2020f0918041b001032400070070180d098801d42c603e55400800d11004403103554800c1e401107030340341d0600b420f001d455105040c0c0b040c040d6110320280030060707585002d0441a58a100c0002540c0314100f4005081d4035000907a0038044102480040313040e00b003d0004510480b050b45400d050071030341009442c00c458038481c0c40384040e00003038002d02041c5010072030607040c400c480c00c0105403120681c458401806c0c09a000103583c0c1e80c0ca000400c26810b12104500001e103102c4006c0000c0125140c00340301e0b81c8142c0303030000d0130160394540d40d2030103941d0040ea40c005440190a0011030007016203010b99103c00c034042c80450711040d1000100180b815000b41c0080c1103168000008031001c00c0f080c00007070309002001d07000068 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 804459046 1250 804457796 804457817
    0xc100f05220512060702100b1318150c1d090f09162909061605031603030507021b0105090103021810180f0f171005091006140a060f 58
    0x1a9085240da200d803e11401400342da0810002c082d182c0110b20324180c403a18108801d508041d41da018140030030403000c05000c00da46242c0c1c140100014101c50300200000303803081c41c20341c040c82c00794401c400c5902c481d00d40d1140f0782a9514102d0700c60390103040d0560310802280020701144200051550000c3d003e408651110182c0605403407a41c0701074002118081c500300080703c002101d40c448181c0300e0328091440b0b1400c8203d8021449500c44c1c90b818060344602c641c918020003c0800c00c6485400041080185a00e11480c008024020596401005102d40940030f64485000a1a5100c0303000585401d0b251900c0c14005501a4008100d08101d100c0c14401c0e50a240d1030b0544500e082d1502c43c0d41d41d00720388034a201e81d07684000c095001a5288003031600c00780b103c1a8010b108005503020740c0030101903040d55805452404900c002c01c610703036505050600c0b010303160000d200400c0704104801840400c0e1245404004001c541540796808018014108812401801020700340403841c9801400d42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 804460296 1250 804459046 804459049
    0x5010f030902120f0712050309060f3a0506091915030302030c160e0c0904090501060308040503010e030306100804031b080712030519020c0a0605090c100f052205 71
    0x180303800c40100100b900a002045910f13501403011401404104174011090202526616a82d02420390442c0c00303840c3c0040d441201204c450151034400030301051006e05020305840c940707030005001000e40140a18a100403101d072503640203492041c0c1001e0f10390a030700d544101d400780d503054070980441492980c90301e202c0508024541c11502540c0a50000c41d49d801000c0003e03441c1280008200390508038010082c0f1810101c0d03d4010f4000c0e10324200280c0b107954071400280107084500000307040d507107003000c00410065000060030450740d00700e00804c02401134040494503840201da40d50b17032000814103684c01c902c0c06260241d400038001d00d07240140103003000550307451030b0314000241c0d147e4001213028801c110150702c2e40302041c10285801d2100c0d0400000c800401460510b000e1261030b004600c0c80b0b00318074100524094035400c401c0610140c1482440c5985414115551b1405903d00d11511300c40c0c10b00903060040c24142035540c1a25021948414881e03e2402c040c040041508190b000580e9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 804461546 1250 804460296 804460309
    0x4091709010e06072604080a0f02041d010608070b09010801120501020f120a0c030e0309010c030e1915020613080705340501140a1404031a1504090b0105010f030902 72
    0x1842d11940200311980c01010310b14544070b40e024040340c005c0900300418040c0410105e030003c0011703031240041d040c0c8a07140c030005000e000e080b194000c0c501c0c0c00046450000a0540041d030480d17810f002a1110300740c5075400781d4003512903452443e0120b00c201c0c004002004030307403038040c24442c050000141480180c40100440741e0103840d00d28550743ca42d40600c10a0222481070351058001ca0034204140f0011041c542e44901070310038503034188103e001800781414003501c022001e10b1002441101d40d05c000705102041c0014501a0a00f140c03010310381c03403001a00000705a401540028910030000300d00d6900c411569010000484050080b40d4258000d1054488400e40381b01030380600c0d80c080c00c0707035000914001302c056100783e0411454945010580c2014001c4800820030340c640a1503120b40040c01c10a18865540300500c0001c00400590007941c1c1ca6049901a003034840c01c10504140c45c0b0704010503500d005c10042e100b05c05050040003c2e60107103554801d41200390a005c6101402e58000540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 804462796 1250 804461546 804461557
    0x8010602010515120703052d070509150d0b07120f051510050c0307060e0d02061612090b0703020a02070f05060a0c0f0f12020705010212040e0c070605041a0604091709010e06 76
    0x2201000e0028420f1502900e0484031000c8d202c008015051411000449030f4802a0000c500082480c824503069101c200f45801031941090201849040c0403030000d10b02c402000c81c1c9401a8a0071542c9459900b079800b99900842d204e01c0d0641030351210408009401c6000301b00c800501c5010000d00341d05440603c09070400d0381c00b5200018149624201c951b05101c56004808219000242000398950384a404039006030314600d03088c580901400034600040c004014050071014104c1d0400c0070b804d51540041a01c18542c1d826078542d0307a41c1c5c0e2000c06421880303000d040d620040c01e01c0408481403003621050240ca01407420500b03194082e480d815140b00c00c1101c107981042d00015044409901040204002c0000b84020705009110102c0103089000d24000c0c1981a031059003c101c0c40c0e850b22080d0340007107400c11010841400d181c03501c80d408090f200c110b060b06407141ca0010301c0920381071103000c081582110010306070600d1000840c2c015400600700c241441a031000040d83d0b40c480c40003800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 804464046 1250 804462796 804462823
    0x3031303141608070321090306051e01030b090c010f021f061503061e0b0f0c010902100f031413061512030c0c0911270607050d0801060201051512070305 67
    0x80301d0440c1040c18141c0b440c0c0c11081c501c6e140c410319020700b542d841031007501240e800c0203001590b40c4480d038006184640b100d901840c2a2400d40010041c011021000b5015603070384e0003203030721500c1c00310010b44640c540b072000d02c00940c22140602c802c0109850040400034164480080c040d0b442e0480103e50510209a44001903511002030003224101c01c2080b5034020a15006540030340340111a807030070320034491803001118010881e079508100940100003600d41c001c00000d03158101a034018030355800c2c000f8100009040603443c100090b90417981c0c500500c1101c2e541007036030b010343d00d880014143c0000b40c1444810440c400158950400c0ca01740102c0b8480c0d52891405041c1d410561142d266581002109519100c2c42200c400082d1088584d908007180d4500021001c0300c6110a2588001c62101d81101c00000c02d1000c1141c04902d80c0b030b40605648407881283d80b980c00403030894108071908000340d80249c010701094540950090000150041142c041640340c1d0b8030355040c400c3c40100d20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 804465296 1250 804464046 804464053
    0x27081204111c060c03020310030f05100203070c110901030b04030305070c02030712031404050607030c05070b0f0306090a09051009050304050d050607020607050a080f040224031503031303141608 85
    0x42c100308950190144064144c64198114185040f031401c0e4004603110040c0024481c003580d030704105081c0686070700c800c0020401c40d140e242080f00075001c0c0060381d0048505c0e1a0342d13000300c0071614004620714145d0b60008104c074010754071541c007030740100301c050020310074840c2210300d840050307804000d50b0018110301045001d81080740c3c075000d052140c1000f000755186001303020501c080d459400c03e903401c6980503d031000d000455410f1090401405d500300c40c85400c40003c50314082e81c40e050055028107000e4994613440d81d1900200340860b108042c005086c2d410080000022085613000040944e0060301aa40350a583e9000246078404014040790680c200310200300300540c05000380740c0d014041d0b08143d49880e80e40c14000f814104000c0c1103810004c117503000b1074150b403100008064401c0304001c00181000340c821124509402c2181e041c0040a8450b000340680d00307000c000d9804a29000c1845407103181186e588078001000c13044c10701110f00c13601d403c0c15140c00e19007400c00300406400018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 804466546 1250 804465296 804465349
    0x62206110a0e09160f0512100f060206150f0109091b11070303080f0a060504021303020a12021302030a02190e09010509070f0806060412062708120411 66
    0x3501010049888610981c00b40382009683e80c00031000c141e03c40e1543c075000c0032540c0d2040c0d040d200b9001f4094280000790a5004124003080301801c2c503c26500d5030741c0c410807001da8942007240d03511400c6801542038580d1950391100c41c100281105c1c1e4400050401020103602c40640a08880c032103440c0c020550380c407205040b040c42d0440190039180740e006000c2c000050558030050840d90024101c5004c00d5071000c00034180b01070b10350147c40a018024030541d030310040c40090000c2c40446000592084104110000396020313500c0b50704500940c00707002030340ca22911801e600001c0d0002404902199001c022303103508662a03503e0b10780041250303110000c0480c01c503828481c24020580019000c2c014020911420a4104844042c900a280b4280300f140e80ca25011400758062944030803000c80440d00c246003000119080709008030908012424500344960305144603001032200030346116030810580b6280520003c815034000d010f41c07038240144005101081801d0315034110380000b440c00707041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 804467796 1250 804466546 804466567
    0x30d0e22090b0c0a05030415140a0903120513020d02040f09050303091c090e100807290403080301050603041b061707020606150a0c05060117070602010e06220611 71
    0x1c015801800303c0c10340c80e08106100c8809403051101500280004094101c0840718030803a4104858452043c4a0441541440ca9401c006481c1c603e2040f00494076146101825200750711500d84180070b20400d000540e40550207000009605075000d0b078000391601070009020035a800343c0d40c5110700c140020b650385d00d0300103203c60804025026004000400740b40020095a000941e102030780d081140c50038094485190015031a030300350340803200600440c0d03000a071a00070200c0d003e103c169024000480215a039986500030300c01c44c000181400c1082c40103028604001001d55070003840b0b101e9009a500b4041000f001480c020350020000400607150a1105010707403030f403070b40c002c4054002040d07541000c20024215202d61000d08069000115051400600c60300381049002c2c0c102e0161a450b503107030b5122021070040d5403144440c03440341a10010f0090700c14828203110b00c0a01380039010b0354444224108145c201c49140c540070765603081c204004200704d4801c1012000c1103401c00d0395207159158 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 804469046 1250 804467796 804467813
    0x901060c0c12020109090e0a021005130522020915120a14060d06022505060103110910050603070c0203010e0c0405090102040602280c080609060f06030d0e2209 70
    0x30490b041c100800490100141d03007001440c1e083c2d906205001c2946079802041340d01d0003102107400f17503100703410716060980d49800074001d002503030310318a80c40c40840d101d2091050f24903051040720b55000b08000500009125540980f108601c020020305503003547c07800d1810140c000301050072120000f1070030300c601c2e081c81c0c0c8580070031034100d0f50010785a85086070000340f5528150502403c1e2640000e024001c114014a0020308451a00c00c004400c03c4641025a9a04000d000c2100c4121811100305018548808070501c0740212102d0310000e507091000b44001c07604082e044409100d001d0340c010006a500f8007400c11410000d0b0020004801030404001c10b0300d1010300440040d07481004148903840c0e0111b40d401018022000381c94411400c81203a1040780142e90001e0059100310380f02040102c40429103a00900000303046950340c1c0c4589030200f002d0f03401610300b00e900d50312203580300002c039000d010701040b04c20300107003048401200c0031600c5500e410040b90480700c20b60740d05254810080c282 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 804470296 1250 804469046 804469049
    0x5131707050a111212040f060e1f030f060e0109060b090d0f030e090c270f0609060d110d2412051e010207021201050f06060c03040801060923160c0503090901060c0c 72
    0x18a0003d089c0c1070040c0c0070802600d04644c98558150136040a6501d1901a4100e141d0200c100305080089076900d002c00c0341206028020250201e0a1001c00140800382d0404d840081500420602e03060b8001d41e9001c60f59100f81030b048060110000e69400329036248a4042e2150340328411580c0e43d029030520488522010340c50009211140c1daa55034002e131540000d000c00d0782415913540d90340d00d00d54000101c482c0244400301680e60304000703110f205498840080c01612040c0744080c00011070b0f0092044c0c1074480f1806031002a800e200d001c0000d00e424050100c03049000b907007506c4400000710503401042280d42d00f5805640e400060041c21420f12b850b5004040140b10002c01c15810301e400d50000b6020302400240c8502c2000c03d0042e0030010500440f80108540d074002c000c150394490944000c0d11002c0409800118101c0c0d01598200c0e034020000c0c800ca40f0181c440310034900c0000e0a03101050541b206580500c020301001d407070b64031100b6006000e040701c0c0d2600c0414a940c0d140030b40121070355 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 804471546 1250 804470296 804470309
    0xc03020c100f0302090d150903080709030f0209251d0a0305060a02070503040f093606020d1415031212070507020f0405131707050a111212040f 63
    0x1c0024240d00c0742d002103450000784a40c9000f595505200c030004145044842c00034050b090b040750482c002c06260383c00700080d03d20139122461165034212041d0f40c0b0203190b10010306010066400d5400500d000287d0562140d4084603c2d0901d182c1809056184288124040082200082c10262a003007129215500e29000c440741450141580d680980752480a04000314040c1c01091007400c1000c2441505c0c00b8042c0c02401080071503a5254400282403000c0c04901205c0d5144189035031039080c40025a4003c0c03c0d880c454445008982e554002035024007403e01300c5959514100d511441400242c82c0a600c8006803030051503450001c250030540c49034109203031100c04014100c000807050400700d07031015490a215403134003010b002007041340e20f81e0703c100e66101d483c000820100710500c02d20844c5081c0503081ca10149004504074003500d2040d000081c100b81e11106103000040c200c01307090401d03201e010b080501906030038004640342c030080c21000c80194401040074000b02c00070f1103886006151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 804472796 1250 804471546 804471559
    0x60801050a020c0a0b0c0c030a0e090106111b040b06040b07060f05090714030102130806180c0d060b0d050105130318050a03060c0e060c1005010e010b1b07080d0c03020c 74
    0xa04032110b41d61100e89010040c0b204002d0f00c0016004004d0b1b5041d03511010070803040d01da9408520000500f88882100407034131946e8140000304596104586214912a01600800b07031510840250b804009240314441da02a45840e4402e0940d111718010300010303d042c1140030b88646003840d18900f41d07041c000107134805a1070001000000c5100003603180840f00510460b8145001c40710101e4060b10590421703139032045803240700003180a0002511032290400804142c69815209072030380e20713600310403a5943c4c050b0f000e08000c004180d10307620055600b0030081c13256800b120907544d41400d6801c2191100b1604509124150505800c074400040c83c468218600711aa4203100000e240c2c42040e0001401c0139a0f66914030b1040c43c001d42d200c50810000070040d50f00c3e031600d03440c80c07a038485c0e407440041d140c28205000051080002c904040c183e42c4184440760412802c04840c040060110303103002d040c0d205140c40051408000d108010341440b055607121180341075403c020b480c104030001041d00505 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 804474046 1250 804472796 804472807
    0xa02041109090105270f06120109150e010e070b07020117010b030412020f0a1b080f0a0305131a04090c0e090a05070e13050106030c0203071104020f0418060801050a02 73
    0xd82d0000b0a40c15500100c400d4942d001180d4a180c201140800320b030511a02c0c0903050007118401004010300c03404048500e5203818008000302400c0c3c61515500900c1420307208080c00c100c0c1c115401038000507100100000314090900241454076220b03500c065648a80022110195648018807021030500c0c24205121075140c019100b84900c030050001d40a040b0410700d0448140c804e115100c4002c50741c20403510004040d0a00001d0031001c4400c0301e010a50007500003d410314041038410348200b41c0d0340689641c5d034141d10160358903448800030003c0352000000c04500b0409040004550b942d600f20700c561980d060100c450100c8502d4200003003440000c4901c0c05170307a1b40e21010554401d89142000c034980c0c407142d5050b00e68a00c108030b4654400e101d04034a41e2519038540c0300c1c1e4125000c0d0340d414012621001c9007680c80340304252010b0076041e1007001806e45803d00b60002e0210824000c00f661600da694514000d940702c1051845011903282c1c08200800c907000d00a141e08610140001c500d840e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 804475296 1250 804474046 804474049
    0x41b0e0109030803011a041203200114130503041703030105010905060c0d1815110601050a051804050c04020703050c160b071103190302030a090b0306060f090a05060c0a02041109 78
    0x4c0c0014810101120088401c1c0100f000010060f107000b000d88505000188a0a03c0c01810814920b1642d00e1009100005009260700c140a10707180410741d120030311290740f0b42c8280b5810f40c0055440039030b0f15200c03c000c00580c50304002481c0c03030400070b00340185440703505003c001805c4004991003d84078030b00500c0340d880e07020380100d985c0303800c4599403c150005450520a804122210340d000581484580861002040d0000e4100410b914100d054684c103a0702e8030208020801e0074010b0a40110301400142d1f88141c0075001030b03070001e0140d401c6604034000c10300050140c0c1e0002004034005400407441c0407030042c041040c2d1681915815036a01d00b02e0500340c01042501844501405c1d003140300b95081002e032000d00044c0104507001800200515030703420b001e541c03580010080000500d0800b4001030240600065a000349c10060201c1c2c41c22403c140c415806401443e0129441688404000344370f603a01c41c01054504283c1c0058070030301ca9a80104012610b4844550328076840800141449 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 804476546 1250 804475296 804475313
    0x102010603170c0a06050a0c030e070e04080a0c05190501050901050c1c06030203100504050607020102160209060102010e060a06080c030712030f14031f1508040b15041b0e010903 78
    0x4500d0b6401d906078807042c02c541118500300a203040580380c245450b040c00101e20444c2c00c1817448000c0d81c0c406002156070000810780d0741200c1d101d41004c1c04044400b16000075800002450900107a203810f6001603400c1d1070300c2c0e040c88009003250942c1078802c00030400700b05080c0140d80e444117902c40200814a0f081900e0a50751282d032100352600303042000c00310100501548034402668002e004c540c82400341416510041406582c10307140c503c250400114158414000c40f0300883c204c0380c402041c000b040d404c1c00ba8594002c1c00450640d501c80c07410340c40340802008564401c901e03070440810b2061401000c00c0c00c024100004030700a0304100c409000031403400c07810402c0c5590515084020b0702100d070702105c0e840d00c02c08440e4400c07040002440f0000303442c44603d084021148400c40b00265842101e041160440300340e1601042032100042c1c0810300701403204ea80950800c1e200c403001c04072400014122012401400b210400001c4001c0c8283e41c0101140713280303242030800804143c01e5442e503118 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 804477796 1250 804476546 804476573
    0x50405150f130e06090606030c2211040b0c06160c05070e09120c070614120f0403020c03010212010312020a0b0c0a02011112040501050c211825050102010603 69
    0xb030100035202d07071a1a00d190300003815000442c05071001c1d07041c40014192980800c0da0030324070038855481001c2c03c514020710901200c2119810094580c00740c004500003401001764140c036619020700000030400100d40041002c0d1340382c8005445685401856640030108401140040100c07640d503100014100240300015030701c0c104000c552070785e0342c070142c00c1c80c081440c1c1c0c000b110b400007c1a5a49900b5001807200180d810071380b540400c5143d0880da44609025a032068450491000c02048203410340720411074000340248152954a4078030400300c1c2c207a0f41303c2e442c1400c0c0050f00200400501c2003049201d404504203101508481200d0b4440210500002d89201e0740c00200181055101d8001d5010507562a038a001d501e803942c900005c00d10030301000310340071396070380d401c0400041042a0180840d221419100c49041c480504801044001c0713a004214402c201c65001c10485100300030810b81000710b6a052041d80b000d85104100184410707580d1040303056a04000c07051000444c015000103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 804479046 1250 804477796 804477799
    0x20a272f13230d060e0a0503042d15020f060709090506040b01080705031f12150e10020901090f09151a180d0222200a0c02060d15050405150f 62
    0x3c41555803e0003030013001d03a015000024410b112a507020460048003130001c030745d107510103502d100244160034240007a02e110b100a01d40300d46270b4144009282d149082c024034a15104403504200102945464001c040e6600001300d440c1e02030402c1111414003595601c401c054170244043c91000d0000303059510b02030681130600c44003100060706070340f030314900b0410341a510303540c42d510580d10301207c58050964a42030b590700014004041080b002030180c0c000b00c60006005050000c070001c2468000d4200d101d4190400c80c0e411030000300600068046005000d00c64400281d04ca1401008003914085074080308000f4400403840c0c0d0b004201c05c0640e40002c940c0400b00301d1000d070301d100060392182c0b03c4070029440314005031f500c0650101c111401003808482441040720103840380c440d400d8000c50384109406000d08000070504c5601c0340d9405031442d4400382c07100741080e6801107004280c442e400c60786100122610820803403490b00f4011b1641201e021801d81e003044d050310b004182089003010725079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 804480296 1250 804479046 804479059
    0x7080607111c0503100e1e0a1d15060102070f0b0304060b030307062702030303010306150b0d0b0307060e0f0d03120c0804020a272f1323 60
    0x380006141400030300103100541e44100700311038805001410a030025600030701950303170070103001c90b10f002000320060242e4074000032445000f40c140c440e040100300041400344000c0e01c1d00603030b0981c08811846110803d250030090600d80814001c00c00d0340341c9006108038119400343d1001c01000d0180300d42e00042d03484d0340354559929661420544045d0101458003505403000140348018042190711400e00d83e01c4000e8814010304000d05a50f81040c40800081d5041d08200700400c0080c80390b900850000150303000c5441c44a070b49018003000740d000481ca034115a0340340e0f0400c121600c1d051101c10301903c21428000b145950712000300741c4100160300c1041c090200801c0803028580901d030901006202c081c4140410340c40c40703100814804090303a017240102c884100c0802c6050112103010750118000f1040040440c4039192f9001901d07006648184209140d2450448800c00507111001d05607030b42c2c68169154030039918004501c42d1503004408102800c02c0e034280c0743c460768034180b801d1001200c05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 804481546 1250 804480296 804480317
    0x50d03030b0d02060f030f090f120d0b03031c1410032901080d39110604030b061e030c060a20150a0605030d11010212070216050307080607 61
    0x1080c0d52102c140070180d44580d001c1102418221013078010f40c4107000040c0c5082c06a158030707100c16a540b204480d4410b41350840246010550001c401805030b81c0e041440c0800c90b91003400220707003550300c258200b22014000c462030307100c0103115010f5046503d0030072107103041c149400180c803552000e1a01000706064807000d0101c5d82c424072100c4c1e5403440f011080145000c5c0d40c0d9403403031542d04c1100007c4074001c1207103c0140f00e0160f019200240a11401e00d01c8902c03901c0d02040310035420807004404549206058246024a44402003d04042d521600c0202501d0405030308000310108180c00064050109c01c0c01c0401c6a100030404141704034095910320384850b0520000c0d1000340c0c0c00c04801130f80f46c0801d4104244488001011045016545021401c1d07480718031080d01911594010140c06a010030031958043c0d2054a540303010b00202d00006050030018802a010700e0000c1c0c2d03085c0d0041e4440c00301d489250489040132001042e080380204172451500c558980c03030b030100400a00a1001100c003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 804482796 1250 804481546 804481549
    0x8280c0201021218010e01091709030a1a0604060e13082a152d0604020712020105160207240504030b042a0305060f0448050d03030b 58
    0x42d10341c20406400618103614010708800c0500c3c4000c07010b08025802c0c041b18240c100e0040c0b01e0001d1041d0014110310345040070718081c0c41c1c3d9a120a0f10f07250540b25511801021039069088620030904070001c42e00203040a1040005440e82d5030080303211039800d4410b001c14410480b42032918141d0040c50b07d911043c484016441c41070001000c05d4280d101040700c0302c001a808034042c07404404442c1c09080c5900c4112803043e44004120310307800320b504404a42c1060800419040340c2c04200240302500d411080d030b86299280c817001e0360343c90160703450341e09101064001c0380c0c01c410492580d10081c1001d074548403094900c10080031031401e02240e0352042038503881c07003002260059600140300d000b4608103880c1407402d85000179849034002485d614484207500b040200c0717008403030b000b800400711a1a01190005800d9020300111446188600300d0700110002d1104282c085011a82042550008004000f403c0c2c030100712000c80166211001e002c207650341201d950150760503160002e000c4c01051b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 804484046 1250 804482796 804482801
    0x32f040b010507060f11040e0108120a050706090809130e0106060206130204200a020f1c05180a030b070207060e0f0a17010207061812020a2003010b0a03030302030708280c0201 77
    0x25404030508100080124010381d4000c1d200e412200ad040c1102c00505048988003030074080c2c01910700c0050410000e1002184481d000024914060720400d482e007299000040e18422540843c140555110280031603660001c3c8506402413000740040d01c40361900030001468407550020003441141d17200000000203622401c148845100070000640d90703e60000042d640707030300305040102684554100d174010f1940c1c0e0000200c103d041d0b81c49103410030552401c5605812201614143c00240414001000c01c0303e084030180580b110380c001c0c02c8094144000200458500401603016a01021051450341c40314011001141c00c071608646440e405040341a0186c821000c014001504000110440e000340400742c1b0601d51141035181b41c507003010707030307003642c84440020000d030460b200b0b60060950f400d00c000741a00b070088000c0000488845410001d5070700c49994001b5030010394080108000c1c8c0d074120283c3c1d601b201c000556821160703089080301d07800024149480c03200b035480c0c820009040f4000d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 804485296 1250 804484046 804484061
    0x7050409020d09050a2f032d0706050904060b0c0604020603040311030406020d1709120a030b040f0c090503060114011229010201150602030313020a032f040b010507060f 74
    0xa01500c05c075070316078141700c642d502c01c1541d115000c44050303002e4000c00a180d85410300d03150016000d41029490285004100d80301c00003010708402ca5202c160f0784410003030100c0c2d00903025685625880d0ac00032010f2000321040c0390004803042e60100494901100000707540c2e548140d049541c140d483d542c0b45421504071000340a400481c0c80040b40103e200ca401003140300b450a07250b600d51050b181d8600f44030700c550005544d4455981c0084104100e411496030040001103454100030071410300903c0804e080700d1460b5180e03070810b91784c0d0060300382c2a82c0c8000d905009010480081005505000c1c0c5c6588040b05150503030705004019450700310bc00707141d402000c084200422041074808a40541c9212000b0616000b13006518240440900b00c0180784041c058038850b030300550a6a4442c8400346050052400581e444244001c0000008407a66890861111205903841c1c100c03e202c84000040c00c404d011030f0303101e00d0421148082d2030340c6c444261610240c1040c07001c10a201403090306002003282 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 804486546 1250 804485296 804485303
    0xc030405090c0307020105060d0f031d030d1d0337060219021218010e0d05070f091b050a081021020a090c05040312030f09060b1807050409020d09 64
    0x40d8070421041410501c0914490109030b0001e100e01d40d41c540810103c124990001080d0044c0c01d00340f80c0200b845003411600c40000000b00b07001c002c64140019203004004010040015041264207290b1950400c030100c0d1003000790002c240c5242c0c46000f400841c0001c1001001c980e0210403040507100d03201010b0602650003040840d5512924481344200c40b064510720390140c85050304600b95032141c13100f1641c1c00c4448116418910010000440c1d00342600d01e101035000407041400d04c0820818810040101000c0c0302d07048816203000b81e00829180705c0009550400229403050032500e802c8811924500e40515101510740d90310210090901c01d503401c118260082041d0584c0300002d05c00210710f00034000c0350001d880503580c120030002d0b941c064001000269041c002000050440b14a2003280350440c100400c81e801100e003000200c400555041e61401e844019152403810044030401d00d81940c0c0c901c0000600d0508030103041c40c0b00e80d110303083d08241c1c0080c18102c4040c030b0390f1043c6101c562 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 804487796 1250 804486546 804486559
    0x510110304030219060305060f062b05010e04140607021902040e1501140d0203030d02070f0b131703092d24071d04090c0803031008010501060908030f0c030405 70
    0xa40c0c003104c200c551400e01428001c86c3c903160100b50940340403002c40340f0034040100380d00e10b484101d150b000303400c402c502440305a00414064501d100500360044c24064200e03e00c04003018a0f1a00b09990680d1410800e0100340d0030902c1131108450780499100b00300e26001000480e019807601c0403400402100070000380c54000c94020410700b450a04650341250207849420001c40341105c20495596907100e8000d5040c0d10070411410b00030010340103021201d010306500000e00c4001d4171200342c042d20413981220301d0b003c004952010800c600304401c0c400d44035aa41e140c20b500e000c14850350380c0c403491030f036040c580c000314003080e4401e42982c6140b0403802110810389900031010740000012800100f40d104142d5441e00004480520428011452241c0c18502120603406541484010019040d007500c5860300c01d02c010a0407201000290b0152080d80c080c158000d15084003c0d0840724180c100804004001004010f034403070000580b07800508220490b95112a00302e21903107140715540c041c40e003140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 804489046 1250 804487796 804487819
    0x8090c030c0111031c0912111b1c050d09060207080601051005070503030c1e120f040510020a03051e0c2223010905010801080a171b0f0d0c0213050a0603020603090703140705101103040302 82
    0x480072500260f10600ccd43c41d0040e5442d100c500a036110411406500003517232111004003c0bd143ca0044071202144505046252100a0700d80905641c421607841448100004038605640a950180c1d0b0810000c041d9403420406e40e044281080100605080750700201c43c40031a041c00024805418a004c125104550b10b071100c9001402a1001316844540424a200440c14001c202d0303002d80e00c6205851449483c0144840303083c8039002a601c8001aa00074a02010904e03025440c2c1e2035506e08003010b440008940000e000500229140d0010350411a10b800108601c0308001103907020725600a8111a030340e210030710098054080c1900310500c2060210780509200d80120300020100c1c4040140d800c4240c0c40c01c01915030780301c01c91000b90007007400c0c0c40c02d020703401c8150b0100b0303040f09010341c0104200f40c0d04d80000d100c641050307034203d1307160b00a0b0100b0001c01400d421052000070b40795025204d42d6180000080e0040404241441840b01c071020f00d118000c070900c102c402a40e4018a0415840d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 804490296 1250 804489046 804489053
    0x140111030d06030312020c210d05010906091514132003061e130c05070c031b0906140907180303030c08090c030c0111031c0912111b1c 59
    0x28802e6100075808a0102c8900ea03407005080d00803109250b1010b00185803240b00e4120411511982c010b0000a00c00c2c14000c1045001e0b070f501840f8000c0c03107020300c040340030f50400c98144216000d0628610007810b0481040010300d2102d07031030451808040b109001c604482d45440d402a020b08440110382c1c2844000d0b11104c640007202840c02503030180c40c0703040c6102600c03248190000140c0d81c01540300c42c0e04900403800c89000e40243c12001314a00d04981130482954881850307103803e400840d041311840ba0741807020a00c012451009269210092020310328110140f200c103007c0e4106030b8040c481100010300c0c260301400309001c03a800340c4000a94019502e0400900031300c039002805001410050106c2c0654400082c94083c0340002000f801890f0960401074800040303688030540140418021a1280358400040c0c58000c804d072200030607075a04601e03024445c5480004e1071018840715450f054240300d0300142160106200c0300d84a241580c0100001d048180320060781c8011198500045080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 804491546 1250 804490296 804490301
    0x1302031603230a0b06042307140901121d0607110c01080c0d0f0f0e010e1203040b010e06060910030e011401060c0b0c0c150f010506070c140111030d 65
    0x1224020380d081540e0781c25066010882d14241201c1d1070203a4001c03208140800d00380c0f14400c2c1c000900400020701c0c42811400f54040319090809895004600c0081000940e0855550400a2000b241c11031a143c0380000282c003513401d045200da01d690b941c40d18078500d8400700c404d5252002d070513021500186040c40009112400a142d82e1030503016200c803440441d4099000b95018040c80280582020786400c050f2004001c8065484070301511100b80301281101c81c41142890341c070f07400000c90b51034014000e0620700441481d941102180c01c008100c0411800704506054840d00d0090514946640c00000d41380c0c0992100c6540c8410080f90030001359416900c00303c681c0c0c4079400244003c1070050103142451400344a40000320f4540c01808000403108101503074411001d016040c2030011540d803185c07510040a008005203140a000d0200485548903c140140310845042e4034084007580e030310ba070520480c881d90364030344e0031866024403582c003440508900c2401e40080300e48625018119101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 804492796 1250 804491546 804491549
    0x90f020a081006080102071101050c100c020c01260c0715050106030501050f0d0b070c29011811040302010813060911041a0619050f04030606060e120c04020313020316 73
    0x2820300e0154002507181c4180243c0740c1c00758100002c007038141c01e4840195020360180101031801d0003000c0e3300c820380070707214810b071100c4402c158020441c1a14500006d004030588081c400c200500c0164039940d030540210f12680c1c040c1103020595110086440d01090700512525514065410500041030455040d400719040707a40072103d958400640000b1700c56002c1c4078102c09021120000005200f40d4060310040c04803e00c1841222008401030000c400803400d42c9400b4a40c01e00314000400000152a40a402002000c3c504004421110f2082411031040b4440281448042000244800c0010b00d184031803c0c0c0100741400541400d140c020300d0000c0c1e18a9003807040d07190600310301c1ca481000b555006204000340616244c6413101072081d00608409240c02c007000800c0048041c3d907108800508006c501c624408100c0905200b4081d04901e501441d0f2805420700100302c5045000008400c1d240102c01c2d64010783d6030b00d500b0703483c403e841105900030b5094400d070801703640e1a1000260550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 804494046 1250 804492796 804492823
    0x20c19021924030b03060103110307030503070605040b162106090c030b0102070617062e030510120b15040209040c0203040911030405060412021504050a02190612090f020a08 76
    0xe1000d5280c2055044500403d00c1303e4060744502d0042c00090052030710381d44145e000070110b440c00780d6a991228a9544901d10813151075480b10144030030405480c400c0d54201c1c50051800540c400e4811009011410000c8480009282a5201e000d07000c6a9804000680072804090040c2c95000002901401000610034018480c140c0c0c0090810320480d603000b041c40d8150303600c440d1503c0d11001c20400004154210ac0f04910446201138011010b240540500f80d050700c1c0400d803468902e0194545421130b17404400c03400021003001000030624290242c0c8102500020700000c9020300209009004c1c02c03c85582051400c00413000c455000405803048401c06402032021402064280c2080c0c002603800a000e540f1a80200380045d840c0100d8002000c024412500c6004c3c80c0705440b007241000742e07405d55898002c4917018003503040040010520142040f440c061003072a01e400207240600a00d251010740d40d072000000300f04410414071181954006010141141d129508241c5440c83c008034174 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 804495296 1250 804494046 804494099
    0xe04050c070510020a09060c06020c0a20030703020f10020f0f1501090b0a05100210060b04032127090504050c011d0a090903170103030e0310020c190219 67
    0x81480c6510f60085510540066462500315884c2c41d00555520400c100110b44603a0207020002280808101c5602160300407120500c800e0300911142c2402840952154025007051b2400d10141c0c454940210f02c440058907101e140701080e9004070300700304048407003030960f019501c24040301c0302c40000d060303240d20704a40000f4a180d0ba03d05101c8200e03070704582e403035811542140003000146400312080041c01da07180142c034101900404503408850050304210f56910010601f401401000b1030702c03002d0300d60194030807040c603d840b2101410103c0a083e100c0e005144243c90890710a101107100e20003800f4500b02407100d0304091034000c0d25060b076492801d0018203440310302541c84140c98150900d501c3d0103482e8180302d5042c9241e0801501a845054081c08410320f15844004e401849181c021402956070002c01c0002e90201400d041c1440740d0800403c0c01800035240001002c521001c20500c040c408070400d0b03000c0d10114070078920042c0e403040005d40203074000071508000f044d84030105641204c06c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 804496402 1106 804495296 804495313
    0xa030b040605090a2a09140303070c0b1e03090f0609061009050a0e151f030515130218100608240120030912071805070e04050c0705 58
    0x300c00194045420807c0c5285880e0000046000f00c015526248140e2516005001d29000b032000c240800516140742e51310a480e000f480c1c004208071310b034072454006001c40d1102c00b000310b006001d01540340014000200401c03410310640700a090400c5090a140780f0400503d0010038a82d442c6071b989200c01e000e10010426061040441007603001245404250101c0b01d5a14203540d45424040c40300900c00501c02141300c1d503d0700101c002c4079219960714031865449806081020390070100d10040010001d4104000c1e80c8280c00300309503916036176038414044401c0101201e207840c4507180c2110302d0000703111134440220070001c145400b55105042c400c203420041c80400e03124400b5480010b1003426820450011089500880098040c06e440c18030b036880340d2912038048940b8035641c0c0d400144083d000e0710131140c0151300648201b0a134030300420340b0401e030751044078151824400d0911 = true := by decide +kernel

theorem cover : BRFrame.Cov 804316546 804496402 := by
  have h0 := BRFrame.cov_init 804316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 804316546 ≤ n) (h2 : n < 804496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
