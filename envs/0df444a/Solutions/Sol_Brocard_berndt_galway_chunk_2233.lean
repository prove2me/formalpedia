-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2233
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:27.986176+00:00
-- url     : https://prove2.me/submissions/d97f6e25-f696-44a9-873e-3b7c95450fc3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 401438848 ≤ n < 401618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 401440098 1250 401438848 401438887
    0x23a0302031603091802030601080a0e060f0a0609090602030a0c0903230102070818010f140403022103161b0509010302011d030d020c040e0120160f0b040303180503 72
    0x2400c218030780c4d1341c1d00c19003061004906010300c2c2d005074010043c400a560441d480940241603820180301c019060ba40681d40e40b400144080d828054032000b2804c100d00c03030380c0414082c0241d40307000d00100c1c51038207104019500035102105958070b000003c089880c41802c90b042902d071300c0700c50010002414010150040c14200803c4d98955003080000c3c0051f6000d40201510450303070b9a80103507110100c00140c074020302d003e501d5041c0300030a907030080c81c0d41000c8119003d487c3d0447d40103030010b0710000400390030441c10080c802180b0000030108a83c017540c55245001900c6800c4a445404051051940b0314860744a000e4001c0012030046c00198001e84060203070700c403d841e240450500400010b032034082005100409600181111200e034142070240e1070014003220300a02100009049861100c0c0c80300d03044901c0d00902003039a84074192504411000a508224681401e0005051012200780182c800314042450044505138126140c021004802c0e0080c1c00f55080c4407880c80c085807400403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 401441348 1250 401440098 401440103
    0x1030f031205010303090303020d0906050318011806061703070b180a0501060308091302090312091201020f0d06150e01050a180f030302060c180402090a03023a03020316 74
    0xc81d000c0803a085824450640214000d658601c10a032a600f006407e0084503801041004111b01c810300c052604042200c1d04074000300c4008045d0040c1500190060448071260f100d07010121640b1350500c070003504588195040e41002c441c0d03103c802ea00480c1d5074400c00000074000c4d0005c02c005001d603802040700103445401041611401c40b46c07507075401d0071241c15401c12a4841c0e8007040401c0d403070400880070107004101950031440c03c2c407000006a81d412801c106007051560004d000354541c0c60f403c5004003036902002c002c0d5110140764440348440d0b0000e101c3c0e009104e1811500052105030311001d042c11004984500100100441c01180c140d030118410700d040c80b40c0000444c081240030444d4000500c514020104a182149002424000050111103d41d40d09000f400420202d456075000c108804840042e9500800c1c2c0c045040441c440d0300c00ba60017680d810f1120500305e500c0000c2c62410000703c04150444060086001401590010145c0140d10078040e90300300b040d004600b071170545e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 401442598 1250 401441348 401441357
    0x3080f06040f0203090615010306030f0f0303141003060b010903080901080c19020a060b0405061305071205090a1716060e0a05010c020d0f08010501210905120903210301030f03 77
    0x2441060b41c060b07900c199070b20a40c552080040101c410070800c01030109030024078046c4006031840d00d5811400307004400281404003508030104c1058041e901422a003400806000c640f03240094003e00180d00c42d21050f5816414000030f036400398404c200d4401520380c0b0040d45070404000400440e0514801001e40000450030000c110b14101c4001c140440428a980142201d805600e04042528820005240204d080c841440070755a0758000e91100f80101d4000064160b40300c1e5011503e150701010507803840d620b4070080c030095000200d0301d200254019021004040001e5201c00710311300c52864041c52461400c0d01c4400052400e42180355040d03240d0040750030400860700c840f400c40340681d8401000d42e20854910b601d10707401c00c1e50b072101da2081c2d0500450315894080040e00c1d0a901d04510380b04508031300301c54031008400c2d6004814554106c4215024841d807515550f2041d07001e40d9215209200e00142d440014a0900314101480c0e0901d0f40d06007164603590702c1c1103200d50092011000d00c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 401443848 1250 401442598 401442611
    0xb010e03010e0d110610030b0907050a0b090102060f070221040504021602030d1b030f03090f03030c110a05070501030203040302070e091b0f09180c0303040e0a060f0303080f0604 78
    0x103a409010344420181c402d00075000c0301e9005803003d414451520f04107822500504100161000b018101d00c1c01c42c1e8001c0038007181c0b40e03111380c40c2500704441600b0480d48444107003404226455031002030030440360207030200c40040c0c540000f0b100b00b00700e0407140c88005900403041101c2c00e1480702c00c2481d50203e2814518102a25000010241d82220907890141c0c6120b0010320151f2500308602841e403071103810004c55500e203c01000c07000c800d90f6480a414018002031080c4201c1c0b19034090302c12950000194101e8504901d8010041c106c417050120000e0800711818074000c20100b002c403042c84e8010000e0914600d080e005401a4000030000d80541c0290714001580070707c0000f00e18030848a48000d0404100c03500010035844c002d084101d0300442d0a101002c069881d0252119001000c61070342c2d81c03105c0c40581c6018508041489081d03010f010208000400f48652a0158001e00322040140030312034488000180c080e599200c040c00041e54080841c443c5059203038850742180c4c0103000429903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 401445098 1250 401443848 401443877
    0x13090602191b050709090f050102071b06090503210f03071101051e0613020f13030605090c060f0d021e07021905030a11181e010f030b0a0b01 62
    0x100d8000104848010340c2480c0039686542c0c2c809480a0072040c5560789440340d80494940ea80d45a015020b60309501b070f034400d213403014001c007e00b260103043c1e4408000d540d00c403041c0c507009444001c2c200c603050b02000050008614503000d801c0700029a080a80180807407800e0300f0300603841080c03000b19081d0725401000900d00203410b2078001c600c6440141c80703219814900c0d41e201c40c05c4800050501019180040004401007000a1042d400000844a6018000500c14144003d2250301400540618001003401d00c0e0103104140c03200700c2c0d004c0c450030002a5034501655407034810020b00150f0001c4100041c40c034060101d0003401d46040c1280c0e0041c02c04aa15081d6407606040320070021854401240200440c0740c6810010f4480c40c1481c18519a00e190030046a9244007010008050b0811111060016110312505040d804503129185886043c0314080000e0f41700300288101c00c100010300080783c0d100c02300b84804100c960240b40f80c451a070b217040c4040300a2020b20300c050b04000c2c1c0030700d400c0c1030b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 401446348 1250 401445098 401445101
    0x51005061f36080f01020a0905190b1c0b04050705030c1308030403150b0a0302010203190c08070f0201110606030a0303050403020c1305070f1103070611040f180506030a020f130906 79
    0xa007140c0c401c004400c02d400c2080840c54103180a00715425607004200c1c44900d1540b240d980070842c1e03803d655844007401101348080740002d19401c09150a40085001c402d140080c1002c0c941c6625014420001030600c0800c0c001a9481111000c3c0070890400100c1c0c42d040c010401062300080e44003982c51a991560308042c210386c0607500a6440500d4203200540c01001445040d9038401d08031035246401c0d1840d40040d40b00c1c040d0050003809040c1c1180e40380c2095002d00b0600096030b0344290700030354454280c03074082c011821030841a400580c505030b8610b001480007e4050040400600901d0494810f9034114007400008108900714011490885200d4950b085100c04044030204080354ad0324083c900201721071001d001c0441000815000c1081aa1010084918081e080f4401144101842206030428400d40c2c0c0a0100904001e00009a03d0160f110400c158085500b042c41152242c60805503250306a100281d0300966030b09502c1d0700c6203401d00200c144551456000726034000261100030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 401447598 1250 401446348 401446427
    0x1305121602010908010c0c06021e04030c060215100e04022206030308060d0b0406050a0204050d0b04050705010302040e0610020123150103110d15030609051005061f 72
    0x5034a144030440300e60441d0380124821002d0f059840c0204100f440224008140c10b0010502800341030b4006a1030840c0c800000c4071000d8464208241c6a441c5c0c0d6034074000300c20880602c100c00045c016a450084c440505441542c051640c0307905202a00382040702c2d4a500c100b01030000c80e40081c0c060b15003006044c400280d072491041101c000583c2c00d2550a001d040100024074552155600031110b100094540c0102604250010800600f0303643d840d500318001e21403904810751220500540c9001c2107840040e841c0b05034410021740791140d9942c001503060380181c2c010100b0100780c0c0000501e030b0b81401140968030b8030341440003003140c400d2101140360b0503600c07408192289000400704892444001205c0203214428a405c02c900b403036404402805015002c0e0b105a51510f5a0013480f0059019803080b0103183c00100401840c403c92030203c0d0b41d80c2d22891030291407030514000500c14540362450201e081890085112090b002c0c130380490781c1c411102400728207101c0c84812164140b03407626018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 401448848 1250 401447598 401447617
    0x302040f020c010b031212091e030c070e04151a151e03060a12031115010e0a1b0c03030f02030c04030215130b0703021c0f090509010e130512 62
    0x59444505070503050a4444c2d4030724041c0254801c0000e02c68048002c0100c40341c0340c001240400098039211300d180e040900803100d60300302640c0d4120307100c0c500e8400302c002c02c8018607600456405995416410f903800008071009003101c007080c220450005038940104d47d180901d5190054120070340d1000071070394041c100d0517607111382c400700c0c0403902c40d11040303008210001200c41c800c4c218509100060418101c1340102c014550000c009942090302800720340c40c48034008070079034024200c110078403604580c2c03d210f60030b040311051012440040e07452184a00b4101e5403140c2c0c8241d001c000754140d400c0600d03504214205513941e80d003120007101d00c1c409035010350131070544182c0e02e80c0355004200020010801080b0074031000c04c031403170300c00070f12103020012224036442c0603441c0c2c0150305099003001484c13400aa480321302d000c2c0000398164002c0c1450b100440d20b441cbd01d00b5554440c0280038403803209009250f00c0320f03680350110b86001c225451006280d449041203038181d01404d0070b400e5094110007000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 401450098 1250 401448848 401448851
    0xd030c0e0a03150b040203010b030402300607080f0403080f060a0b0c030304050d090f2c2514040905040624030c052209060b0a0308030117031c020904060302040f 71
    0x100f1a54071140a020790500048405600b194188854142284000b404c0240f2402c07840c0b41e5802c6441a07001c260300e084446c211001d81001c0848001510b849048a01000046c007031000605140d9000540c07030301a540540c0c4041d085d650f0201ca60303203d0751002e0117555100e19400800191a82194011300309210104059604c2c4d04003403500034a04001004020184451881c00b030043c0c04c48400100e089560741c02c000d03003e0310f1000c40505c10190b40d01290020740d48004003004a11107103280490325454864034108500e240210b4219840c0b400e04081c02c19002c2d040008100c450344542189802501460002507000ea81c641480a030000c50722000140414046003001445100760303180d0000c10080d41d4a074004104255004040c184221803e4581d9564090305020301c0143c0d444100c42400c06005c032100d158590901081c150400d1148d000c80129420200b0040040401a90b60102c001001c410340000b0700c407104406900100c10054005035114000400360b900d900a050220400010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 401451348 1250 401450098 401450123
    0xa0305030d0c0509031b0105090a0306050709080d0f140f0a02070e0109093305101806030f0b0a0f060905010305010c020106060203090f040207050106170d0804050d030c0e0a03 77
    0x200750055400c010300d03101c00d00105000241568034041064051008201d8000c4604006200180c1e068003c4980e03140d007145104002004102080c0e01481c000c41c01030b11200c40b0a99501c400784d540340401c0c86003400250340d05043c0b0040501034440c0324107400d48442070070300f00100da40021070a50040400302005034800c0e041040442030003407540c1d0161020340010b0281d00c00a49070200110101d4510720b5034046500085117100100c03c4030602060a28681480705080003085104080f09500a16000318441d2040d221080083c0c803c0d00e0489a004007601c44508860b1100000300c0001401181c82c01e4550031315420035505845010b0242004030340018107541141071445c2100c29038489801568501002440099000002d49000820448494019002840110b4040e01071036000410540c2010808501a10a03007060f1581030708813401c940c00300003402c60448880c681070310302404941203070083c9a00349100340c000b03015010090815402041c41800415003c00c11548191404000040e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 401452598 1250 401451348 401451367
    0x40905011401241d03070e070201061e05040504030c080c1e0114150301090606090b01030b0307180b010516050609060703110414010905060f03041209030327050a030503 74
    0x541c81d030142c4034000107040400d110b52105122461250b040d4030501242030205000185000008000280094251496242c1d01e111243e181c4134260b03000d802550134503401050010700340d245440010080760b4440110381c0b4140030301000708000351050702000308559141021940203c020080c000841c00108840341d02044000d07400c000403100380391540d0502581a0a10f00ca04807150b80241e2802d00c3c0e0143c03911544006801006582c000070000c50521070002480c0c05564008140000c007a00c082c030401c050501015103070050740c000d101c4041103601e445d1030b101c0c129a002443c58a0181011803518605280c0085100c1d1060800c64003603000f9070421500420a01c400f5404c02250b040078880105080045020780c060380c00717400c1051341040c2e1204030680c82624908000c10b000341006d43d481055a918500d50340c002c4170156a20100c1c48406103106109071403500c2241c4e013564030310078190320101303604031455283d4600c003003149014030b030100c0c1d81d5481c0b00d041001117110758000c0d40d4920002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 401453848 1250 401452598 401452631
    0x2030f040305160e070c0201210c05030a11090a0303050310030602072a060c0308042904030e0d150911041a0f030a050705010f11010218010e150f071104090501 70
    0x190085044a00c2904c103002000e0f800078a5000e482d40c0c2424920307001ca1050725a048644490004d810301c25082104207111a07420800131801810380035011302400e0f120a500743c44501c2580d1086400035040c1000300082441a4060754004e84032500702d44550741d0f01d031501804c1c1d80040740c06442034010040e464a9900100e62402840034a16400348544c1d40b03040310103040744d90500006801e1016070000202003260300300603200c41403c0e03520039100c016451080c10b1340040c0308480440c0407800d00321000c80705127000e0b40b0b420011a849100100700c401485c07071100207803a801030115210b881d6400c50b440d2507502c50183c0302c0364002d0714085000c81c001580420100c1d06000324040c4c0a500621180d0003c11070101e0b100c07040e5402070820b180040244c6004480003080391000400c1540301041d28081c3c80304130040c1003112003090380c504500300100401c21040340041c500d06100074904101e5050200029030251850601910042806002a90110f41500c0610504031440d07590392080d8207460600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 401455098 1250 401453848 401453893
    0xa08041509020d0606050108181009030e030d0e0a08070e07201b010e1c06050718030503090414070c1410090c030204050f09030a2f06070210020702061902030f040305 73
    0x140f0003c0c0034182450030940b6101c08001e0030b2b469229840f40e100c001458000c03e4030441260010301210034001d0912030060040d030f000003c0c50f129812604001841650018840c0300303507a5224030004854581e94420b4580d0f540c5103550340a44956403034100d8a0040c00c0c000482400c00042a40030746040340700c00103020500d1110440d10490610180e06485508140c00d449084d0f0701090000b110380f900541915400014408420f01d4000484040308105010002d084100800e031800e002d4085201000540f1420440c2c6480c005003120b804e00c0e011034282000c02090000d824252000e01001c040d0340d070107852035810b09a070510110f81d000c1045080070f00c80c066210b607403440540154208921000d40340d01c104680c90701008103025a0b0b03c2011030b07034140303990001300a00c40707103a60410f4260f04646481c01114000054082c8200880154070280200e4003081e6000740741a24040d8404801104161407298050840c4070a02154103000d08420042c00079502400c001c00802d52404204281c455a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 401456348 1250 401455098 401455111
    0x3060e0717060a4a030717090604050307080109060f021215011101110c0f030901050409050402042c060703050c041e0506070503180f0a0311040b060a0c020f060a08041509020d0606050108 82
    0x108014008111010300780c078501c1c007000b141150b0b44ca11908c0026654026138000075418040c4101c0002c02403015404003401508c00c1e0310502942e4a581d421a0880c041c10039140030a80002c00080c00703411340d1f040082d01c500d40504100346543e0070040120b00b107840b54803011104140000d004086090704121000700e405800c001145400d03484000288180124828804d0300394840000c94210b5036541c0141107107024440b0102c1214664000765910001c0e4100801c00301d010751408a010f291003406020300c6030000e4a031740c83c5044c1c544990056500100000861a00746c410b07000700b40c545e511300080c01024000c7d00196110b00c24512072281030000ba942c814451107010702c504016860760880b50048035080288104a03000c1080420081d1541e45075241d4019800204481c0507908240f00c0c0c1d800308c1c0296450115200c009083c001c3c54419540000d01003140103000030300281100c4160f000344000c49101280103222540801c81c1c55124450413500503403155020b11895901c040756035807024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 401457598 1250 401456348 401456353
    0x1101020c0d110111030703050613050103021e06070507060206010e0106030c08150303090a0f08010608060f0606030601020f0a0312110304210e0a03060e0717060a4a 72
    0x214401001aaa801254800400d0000701c40c0c0c124800380b030030750029112800c0041036540c0d0b46070455006005213001c483e168462076040c00d00c00301400e001d21485042c1d0360701901d84011740c449040310b0840e6080b10322180b503001e601040100c3c001001030005100904031034008240e07950500d1801074400310140c000000b05454403440c0002c0c40d5015601580004140c1c0e840014440a040860f0661180520003038100920400000d4040ba100d4401c1044a11440081200b41c1d102c44410362912019641c0302010302929000c500d203480e09400441d086801401120b0520120814070780c105118540c040d4041042c480c50404102050b0040c0c000c85041400b025240d850107070b450611400e000f00030880c1180140b10030002090080f000004140c000900203102c55a492404001819100b044281280034000002940c40e017030425400c00032034a980604207039911045e06400402800d030726140c111002103401d2208401d404500d080541403500d00780c10864010b030038041e0100704030074a8101e03503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 401458848 1250 401457598 401457607
    0x9150f0c07082116030e0607080307090501020106060c150506190e04020307060c1e03050c01060f03020f0406060c110a05040c120e160303110703060c0210150b0a0e0409150b01110102 80
    0x146140d00c4e841a40b03503250178150401c05048020070070038080d0003001444a54000705100e000750300020481c2c22074070264024000c05850f04c0c0308880602c000072004190f0310302107030500e0b0707440079a420265010001138007825014241d4660110018801d0384a01050386114050000f54141030140ca000f40400c1d0521501c2c59125603681c0508841d50394882d441e441c0100307580c908242c03141045805e1039074810001c0c021030f51036040d0410315001c0381c071003248114001600440c140c100303400381000301c6000d9200c60552014646411105030b989500181d4050740a010100b0315548510a500303c00c01a44e03609960110031400300822203400c1b9030806102d610866010640b9090002901d00350703581483c00170401a5034407290707440c003080c2d41c00007424103080500b00500320b5400213005003000c0380100f00784041c2c4d00720009443c516407640105e821011040001e040b070301340640949010600058800143e0448070f8482c3d41d95640c0c0300b40901451519a00700c00c11945c1d0100f855607945c0e03001d030000c5260 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 401460098 1250 401458848 401458867
    0xe0c060406031503020a0b1216140a03090501050f1603090215130302120105040b0c09060915090405090f0f0f1e0f2b0509150f0c070821 60
    0x99010340d208030820151604805404000000441c0c8010741c1d000d06072100340e5864001c00d64050700b15020060b06030300140002190440705040c80c50118086840e60020000da000d00440c85034000b141850506441d440d01100040d001d01c10640304559010942800f0b04000078007801c59031a6100080405007011254000341e501d82f0b8175207503000540c3c84003680d80c801041ca40e03240d1707a04507400658030524011051082c1034040d001940705508c1403010301440c1d0780b040c0303011409014131145560804424403540e4818201094061400c403820010141409031010008050701c0b41140d000c50543c1241c1034403103008108101c5402c1c000c8031030028100500400c080c031540e80d0408855401166410040301c01002c1c410320000301d400040c034064481700301d10310140403000d4814101911104051020312146284101e056825507030005150a00d009031805a002d031580140406c212260b2003001425200302c030820240e8010000174024005001040178140d003003602c1c0c0100118420710800030f1089 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 401461348 1250 401460098 401460109
    0xd08151f0806150c0604050c1012020f0f07060e06090712020405040c1d0f01050907050a0305090309040627020f0f0711090405010b1002160504051e01030c090e0c 71
    0x110032005140c12819581d401c40020383e450091440a05a07481c00542d083c1003c50110300c03580700b54002c2003116030080c4200f06001d041040403c020b4001a607039000c26040e540e10360003c240c10070111540a041906444e007a0000d980125011904513644540a2001c844144842503014013403002501c0f01c1841c0c2803200410000344d000080c4070300e5944c0c0c0068108900d444403000a40211a124078200740900e8685482c141d081e581c0454030340341c100002616103407a4075150320480035656600d08000140788180d0151001611045190205219200d07194440b4450003000b011005540c80ea400e0340d0705100c42c6c01100b60980c09821074010084c1c10284060401140c04155500b1000f5642c3e030010b06001003242c401220340b55101000340d080c44240300b41504150300c1c0200441c0e0494811861703c1c0280e0b5a000d10443d441d45c0c4610212003040146441c0e48405c0c2d00058215000c0b08410b15000101400f05090700211030200c460b030810b00458082e445032076403141442008064122080000a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 401462598 1250 401461348 401461399
    0xf090e010501020a032601030f0b090a03140922090606090506102303040b01080d02060f060f0d15020c070807121211010906020307020f0712080901110d0815 69
    0x1820320504031083d481c0c208805145514100421015115079612841c1c0481c003403000300822b40718a0440d0011031034003000410030340b403002c2d495250701441d031a9002004003036800c43c03e40305070b001519880c1d05da00e82003250f1078a507612030f281800041e81401c51070b00404645c3c0540101584a11f0a81003207030741d440d0302c0c0400c10244810304059460108003100034040c8040e1001035a080c60001c4280010800e41601250507145100b06503040740d80504022a503491007101c0d0300c00c5491000c000b00c1d800e4201009010f03102c2202900140400c2015211150b420301454004a5526400100300600100c107006c0d540c080e0103e00054442c0740d1400703808045140900b0006065140903050814032207010301031221500700e01100a10001d41c050a01c0300003500200d07404009402251082c1200880208100050341c2250709289100c48082e103176a41c00341c000310300044c180b202000403400e800c0b000704600e0310352500356500e281c15441c0404c4251450003a4030b11031809107410049480c0510f01000341c80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 401463848 1250 401462598 401462603
    0x213150807051513120303020a110a2f0306040b040209090303070203220503100b0f0609240705060a0501060906091d090c06070f0b060901120312060f060f090e010501020a 75
    0x403a1100040b9112134402d003840d501c41612002904180000c158058004d44220755150701c800310401d604003280b94483c000b2a500500004004280701c404213510501d90700b0392603080c0c1c44042e1046a0700046031525000f5030b82030b070303e0361800000c010440c9080b00c1400e0340854200003450a50502400c041d44d00e010300c401c41558039554401e11500406906014001803e0040481c0c1c2c804810b00c06a4000f060b1100b20a805582920310b20a0941041000c40b048000054841c10002c0340000c940d0310b010301d06c00d50f0710140c10010008500480c0042000c00c2c00f5041c20200081c55501d0024041c006030706a50100042c003000182c20009102000c0503400c001020000b180300f1a640d4069590426402c0f040b615130000000c21018148190000810705042c440c6c980003596486500c100845080244140c5503c000501b0550300002d03c650742e5950048410080807850f44d885000040f02003886811640019500b005009221903006280400504c00c00c00070085650400d00005d44840004401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 401465098 1250 401463848 401463889
    0x405011502030d0513211404050a0306090c0e040b090f0111070b13080310080613020306011203110307030c0209060f1509011806031b05091813021315080705 69
    0x5010603181d641d042e81e0382640480c00c0200048503a1026039400c0154241400047d1134800c111030060070703113044405a441c0101050798044c5180d0b0f40d81c1c0a06400075003144c1c0d40f9502000040c4c0b102c481d04905016602c15056018140f0344000b5040c0f0341010590307080030680c1440c120b0401c46110004541c038958000c0c111480c50750322650818403010b40701100500541c000800c00c1042c500503881b090688200c40706981c100d890f295103120041203588006503064000400402014242d0a41900c903244a0705288200300e01c03920400f41140c110040503008100e1401d961000c619064810903440b107402c580d8000c5504c85a4082881650580400c3c01d11402c0010301744d4482c0e001c1d00601c01c2c020000c101d0250740d00e032640030007000340c64903190710030905804400550300c0d48e02500c10f4515240003e80440101c072120f003036600d200c2d43e016005803c4140b0035403140300581c5a400704c1241c0040590f2011500701100a000038020207290b018400039049a80c06021581d180c003c501d9032403811504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 401466348 1250 401465098 401465101
    0x20705010b2b05103e271527060417120c100b091009050711100603050f0303011d040204060806070206070e10090b0306012606090f010e0a0e030f0a0e0405011502030d05 74
    0xa214407807984148990707c207140c4003802250106d010014040c00c59164842481501c0e10750b43c00300130b41220700e03040f039001c039050005100c00181500180124460b14003104d00348904d66a01d0401c1e50300050500940e0740100040950a0000d40a03c08103200141d608291900d42800b03910714a10310350217000007258171080406d030104d224014204003c603446e02910644076000880c07000420040c401100c3d540500a030850080c180802624121000307020342070080340c0c14103081d00b008240104205d07400346d580c11000c5500c113003c201540c800c0103103170010149802c0060001c1c1c01281c6001c5268442c2643c5081c0c400300562040700c0c43c044403450f944080e1a51541c40050318917110b50640404442c0b04000c54000c0c4030204bd0328a0700480d02941d13002640d44500841c01c4d240102401803240c280718003004503c1030039a90b0b02c6408e2003006041664102021505e408d109540001100700c0000c034081c540800c1032800344220340c0181288509210b03d800204000f0351a4004e401d032208010b6a11030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 401467598 1250 401466348 401466397
    0x9100e030709020408011b030504020a0e1e01081006080c030d081902030709150c120807020106030c0b0a0e042007080705030d020705010b2b05103e 65
    0x500081c00340b100c42951a01d0f01c60180c0c600808010310130314450240d1100d8500f5050007071050034000c0d6005000e21001608200703c1c1e00710071202804126640280d8200001c0e2240290f10a901070a480710107403540021910f20b0b20152421a04080c0b0541c00680d06079015030303000a02c6034104041820800c0307880d590380740e107070410712000c88607452458000800c02c00a41d034450524420f0342d940c44d0036990111000755007100e10340c80320400180b42c44060940c030700d03c1034082c80303003994030011600c00810410340701c2d500c102c210034072940411008a00452411955074100441001e0004240d03010091900e800982c4080904a03460448117000005040740c00c0c01504400c68200541280499a030390001d8526013000754007089c4160f4003546410804003e0303203004c6c000391164500401c0020004003512100c0b0f01010824a81126284515a0301120551150280c1020182c0190b00150000040703850001e00c0340184600c030340e0b0409022840c5580c20800c000707558008043c3c85036180c00c5441d60303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 401468848 1250 401467598 401467603
    0x308091b0915060412030503160c08030106030b0f0a0f060210020c0d0e03070f03111c03080f0705070b010e060a06180b0703030207061802031207020306060603150a08010c080c09100e03 81
    0xc2c5c10805e90701d24100031010a06410100842c000c004103c1070340e036441191402200c038000000d600400c1808200010808188246c01c03441000c00000d00030f4041206d1400012020007140e8011401054084000c01405805010701513200e040e03920254038205040c1d4481d5150b2071003003001c00900844140700303071103a01c082201201030121403440d081c1c2c1a8503400c0501034a00d0f614162480340143c0082007444090340b00d80c07044d09070742c991170340c0816031101d4029401c060b03070060815042080030301001010038140c0001500070816810b00c800607040039001d0144041e010703000001401000e8100b55591100740189400320f5912008081c0c45a029203021006445803107000303003d079414803480550740c0d0080c4c07044507070040c4200e040f2030b510034070410600842e00030003c0295240c5c0090000036403504015004650059000c240b9220400c1d000e000250280c500740c00411050307641e07104801c00035412070400c54001e499200c4907070070000b00c0800100b05c0145034017402c0400480c1d001480361610b08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 401470098 1250 401468848 401468857
    0xf0a0204111b0f0115030b0a050411060f040e0702030a09060509060f030108010c0306080d0f030e0c030a0b07170c0a03021e04180623061b0a0308091b091506 69
    0x3407080c1030290b400b04140c0305540b140b5071032081807254645690444200840e400f110116a84148108000ea8a00074101e0090a0060007940d0001c5040c2d105c244c5030f41c50200900c0c404480c083c0302529581801c0e40c202d444903000b08080150350080003d0855207800041a904541081c9400e5583e03140800205d4400d011303402c2003591080380030001060650301074000c01034007500d0380e03005c210099903014495910703092200c00d13101250002000000e0136204e900800e4540c2008c50440b1303020201d030710100c2d24115444005880d2104280d051000d001d070700140c80316070b101d00454026800d0800f140030f080b00b1301c2030b1140002032545c0041c0042c8611165103004440d507420586003602d0300d54481448007401038030400c0e2a8014685030000c0743d100140585080da051504000b00280c04c0104103100043d0b0240c0c0c0c115104903a20482401c20810030032580007024483e41d0389801c1400e101e00707130b14541480f44141411900320280780300469140d032620700d5400070f0303060b10031507030407081d98040394480c403d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 401471348 1250 401470098 401470117
    0xd060f0204030c0509070c0c210507030b07080c130e04030c021206061002031305010c1a011e060c050c06090a03080d0204060f090807120812090105180f0a020411 71
    0x8038000003408240d03c034110071a0002d0f68103c40b550f5030701001b10f03400b0103c0040201034803c07502040c0304080442c18001c103003080c5034046091001040d180c0c030b441c1104660040340c100348031008100090790310051480c1c00c0038480180500b010402d0081c04e803403c006021319201014401c00142c2803522401c01845800e4000e0300a010b440764000d680c0f030300c40c40110f9106000e1004040072000803840001100e819840306c2c08178800403814840116841c040b01041a50300c0c14100c000f81030000c1070240414001c1c50111007195040e10090031a81600c82c450303001c0c0342070060100101c004500045a0481c1100080f18030503900c5146100140f11b0401540019049210228520354087c100d503000f002a120f003500c5100e2000c00382c14086a0b00041405400f02c00e80050604001c001d01c008851215240701e810400d0038800010007845001400311516030860391110144800c03601c0c0c1421040c190711310710024040c1100c0c10341085646441a95009001d10759070410415492b2840003940c610f0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 401472598 1250 401471348 401471351
    0xe0405040302070303030e1b06131503050103060b12060403030b1c11030120070f0c21020406050105041a030606040305190309121703090c12030c060609040b01050d060f 74
    0x185410002c1d514074030f03808100c0104e894140c03520b07100200011304010041e131202011902d16640c000b40704c69a00004242610000c10420100307840140c800401c0c00140c055900090075851402c101c01078170b50b1001440d000e64001280d003107070404007040c540d0b400750b01418046442c1407808003190b024800b2145440c3c99000c0301c40510100440000b4840804200310000c0c0249840f00b0303a8010b10030804d00c20b42600303a404010340c100080b039090f80c025034240140c040740c450303540c1ca4501549080442c4800c112504c0c50050000440c84c1038454a0040c000a190650806081c11001c00d45451003c220706005c0f48017000140095881508981c06141d0040a03100c05503460003d080d1400c207400e1b000c60201d46030b410042440c403484180501043d4008444854036a914140a07907280c4c0302500861890144442c42142612042c400c99010741864004554905030b801c515400c006001e01240d2098003082c0a10010480c4a04101e054440440e1006501e5282d883d0881c020003503e402c080a0a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 401473848 1250 401472598 401472601
    0x4090903140a0c06050f010e061c02030d05030402030115050618040b0409030c020916021005060d050a1410050405030702060f0d060914011707060807110102040b090f030a0c090b010e0405 82
    0x354801801c3e000284118070034001900c440d0544218014240248031001c4008800030700c903440e00e0a0701190060040d00500c1d0b00c160550007013070034055112800030128800006200460609208422085007543c0d945c45007a030800001420500c0303000c903074005040d10290210825501d41e0b2100a50600082c82007050701300900c0c029001e098020300a91040c0282000110f9442c0c2000c582140c42c4a2030b4003801c2da42ca0328904140c0100809491140c003e00403040003030026208121014605010711800000c51030714a80325480c1c50b02c58610b071540c1c00e040c0814840000c60000c1500e0078154112112510b520001600411a005da402418a441d060050000b8825003035400050f182d804445a0b4400ba0380b03135050003941480300e0122101543c40040200502407154041c41e0300310000f4035101440044000041e07003640c0190f04a100410380003c0c0d014a50724040303100d00380007582903000e04280c0020703403170384000803c003071041c0d4080c117032a61040c807402d81c824034040b003010100a0041109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 401475098 1250 401473848 401473867
    0x2010f060e010306060f0e0f040c0503030a121508030f0d1b030f15050108040f02011b11030f0604030801170a020a170705010801120311010b0301060e0403080c0307050409090314 78
    0x1407a07028441a03c0d064039145010500c102c10320b41940a8070424000000355440c0c9041d402c030320800090094440c1003240700702113880e82d818130080030b003040c0956030b03041c00c15038426109040351a4100c1c1900f034032002500401c9000e00120503152a5080300c511142c841e40489aa00090310710008444031808a03c000000d20a401d541b100108403006041000072100303040f00d00450f03240d079025803404115040005000202e01d520714009040c4180b4054920741c1042c10303141b1502083d84801c17106106094080503581c101000032002c4428040020034040c109910b001d03110500c10301480c40c6480c804490440070042c10440300741641d13400b0b0440403505175030700800c030f0b180c0c060444c0c041c2490081520000341c6620030569103041e21005260100450400d9905881028005072009569526104c00d02400c0e0303020310500d40200551800326030303a454140b40c01454124014080344c0c6010042c000e01068a5200e01518165100300400095001c0c0f1801d050707a25180030400301c03000d480c0c0015500f01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 401476348 1250 401475098 401475119
    0x50409030206040528021309080406030e1504030807050d0e07090603060b1002070b210c03090f0a03081b1209030a0e030c060304030e18070c02101106150102010f06 72
    0x100f140101c00750381c0c130119281c880f1810700e8000302c048041612960124009803510915042e03c5401c145000600d5001c195502503080c3c1080e400040880c0e07039645141c62a18050251050b49224981150ba85142503075000c8d00c00c807005007011040290104203000c6a01c2c60b5132005941007070350412a906556100b400c0c0002c0c0c121400111489428420740c1d0b60503042810446610071402d401421160703040c4103424805030402e83c45981050311120110001d004161140c50040c03e0749050b4a641e4903000314501e14251402e0303007101c01a0b002483d1580826440060103400221100040c00c86100071142c41405011f04601c51002c1d004ca07030244122004000001e00c10070034103884001100100c4010941c59501a0703200d990071500c01c00000b40040c0c41b40c00d42d480c80300c900601480344c00c41000c0015184540071120310340484c5145a43d0401e600d000850070440e428245080c84062040c103480c15240c4001605031444030080c41c0921480c3c1c0c7c000c0d00500d40a20016008001705551031044030b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 401477598 1250 401476348 401476351
    0x18060d060513020a060305191a060c070303020d090b0904050c0d021804061a12070903080703170c03130b150d030804140a03021c0c0c140103052208070804050409030206 74
    0x7031080300130240000d00c813402801070520030540e00c60030f440144108a01c503c05450706501010480c01c001ca001d2003140e5584000d04800d030400001080700303909528010b840c1c8804a201941031203039019040000b81c8941c6e045481c3c8090a0354003040340d488070b1000900d00c1c05076281d420b00a1b8000305150303001c82d54400d080e250035070040700c0c14440203544020042440308043d000c05407465040042950b003010208a40390040d04900e07051003010b0f941c0d11101d4050b04102001c0f00001d142002c4403d0031401241429005803100100c0b900c1c40c14401c108070403416098034000c0c0b84082d810005814441490920b2880c5800980000c0b85403010b2b1400404a030402c45046940c0008200340c8078004100103803d45000e40c0c07607001010301d0482544414100c01c1080f19050070407a4600910001808200b460b4009152401c108000c03810048000b406842c802040704075001001549084501e03001200703c802c90303801032010741d92000c80d0706003030403644035a40242c0d0700305041092038402c0603800140f10303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 401478848 1250 401477598 401477603
    0x30521130507060305010b0d0b12070e0f1005011710030b010b090312030f040f0507032306090c2202120702070302030d030212010b0a1701061805030c18060d060513 72
    0xd510b180d44644099003142c10a00441c001303150b09000300f107a4510144d00a43c5640340042200e5010280d840800b4070708492500422590320780902407081c1035915880c2d8940020f12002c1d480d00e01800c1c000001e12150300052806812004400420502c0b00710044007405903400a02803030182d03031070303045a04040d4042d40c9114004e00c0307400c00c51165208080150303070003100c64945203401903c0b0341d201d90303034050308a01050380c2600a1542c00000507007c0e01840d0162041507141d911130100d00d540340d42c00c14000510324010303a04041070241d0a80d8610f41150020007059a62216140b01c1340080c0d402801401c810b003c80b020280d060180e042c0d00080c0003c00c9034400c0302150301018495500314240e000748d082600c003000c02040140140d44480001e00200043c51400e080f042c41403400c0c410740081c084c0e01c01404602c0102805400030595a154030146c24150b005000000070034012500b4444d09112801c05190840080b40c050359640154108003500107100340140e04146180241060004004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 401480098 1250 401478848 401478853
    0x9040f18081b0712060b2d010f0e210a021e0306010b04031707020114210c040b2a0601030503220810330302040c020705060301030305211305 62
    0x481d01c0c42e000185040982c0d500b0b00314041c2203040c0d40d8425000e02440c90302258050780d0040e55207200e0035004110030700819400403091105070325000244c20b040c01180341104000c20361b0046885601d4020f42c020748080d1b1030341d000d088a41c075880c00c03a040c4442c0060095000201281000001c0b040e0740c0803402689046050740c516076030716444c440480c450b43c800100032020150b0b40d607032014414400f0308801401030620780884c2c40e079141c00541603030000c803c0032450760481e24070714550104038241503403007025100a2441c040c102a8922203501450060011303074508090305d624105000902e15100310b0f04041111030780d503100e280039604e9801502e5007007502d80354609118814240c409841d41104c501d10060b02070714100c069084040d21054080c0e02004c00d50074502030840703104111180180400405058000b41940704020588490040440c21548a80310030701c00b680c0c40350f00b00c0341142e42c90700b0455500c00750b121a20020014007440800041040307010013240681c0e00e42c026404a11541c20b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 401481348 1250 401480098 401480137
    0x7050325060c0201020a03080403050717030f01090216020f0d06060e0f0a1401030605060103060317040905060a051810030c06031e0501060f20071202100e0609040f1808 74
    0x401c503007010b01d161001e801a8801a00302010a0151001c141c1242c001d15200345094040d445800388920800d2642c00790400000420084000b0180968007600c400740c4e0940c680070a50743c41c0d0031614501e035400fa00c25404000140214ad403000c0c0c401c044035500030020f0100ca84e8a41d544250018100d511035550130007040020070300700312071182040f8504401e0b01070300540d080d0b840303080040000a21035030500d1f0f5140004000308900bc03980765500d01070140c50780d580d1401c00c3d19103401c1c0d5001a05c014003a44d4980010b00c0309030740303400c030209e01d4032040b0300a46096038419880c0400c00e40c0990010b072540c140c0c1400400c1d40e5a060b00240d03006a0041c00923174102061610b1030046950921980c0c0c0024544005030b25030303510030107080303e410034044443c103400200c051013503040c601282e100e006801c1c1c076084960b0850801480c012511182414101402d41da0743c0b0110302180b09000c0c41501c80d5a40b500b00c020392098950020a032214044c1c60500d500300307145801d0350a588511400442000c0030b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 401482598 1250 401481348 401481359
    0x1050a0501292719063608030901020c01031503030509190303020703111e09070509031506040e03041422140403080c130b07020f03030a180518160207050325 69
    0x145881102d02d26078030131b4802c3e180d9200c6414004641c1c2541d5405180161040300440310003080c04000d841d11102a690b984903001c006481c0c510080c0c1c440707052504101060071081c88200f030a1007200d400d410601c1d525241c9900292004060070a000d850044c40074011081c1640010b0408c00e1300c3c4100c0301010010a00f1003007000c83e03260282d0881080b92a03400c0c00b400c904000e80d059070002441e08010b8201220040081c0c05d208040c2141070708601908100034481c5040d000d50b01550400a015600c2c007402d0900304514044501c400c1405005415003029100d64028400456400481010080310101442c1e11050f40340c180c030180c0c0041e03c0c0d80040303855a91950308990f07900d490f0103411000141340610188041e004600240d0b403003035500c012040740340c4050000f800300400b0b0b50380c1c200a6540c1c80302c1c1c2440c0395100e900494010550150b403050603444590f0416084148440300304154a59024101d15210f0f06402030380e00360003080ca0f48080c40d41c030154503c1074650340306030702070541d030720354 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 401483848 1250 401482598 401482639
    0xb03130314090f120c0d14010b0103110d0c1b0f0314160b06060708041e0b07020108070e21010c1e05071202161202010201050a05012927 60
    0x101110741c49560b5070b10056082c070b010104e508144114500340e4580c1c00e110740019413007a0311200191800100c1da00c040d0404c020038800e00840c5d0609007410000c1840005140c80c281c0240c07007142c12082c0c2e42d9010b150845000701d81010b400600e401c2241814031701d41c038001d6001c80303184000f18003043e841d61007981104180c0003641d01000390401101180c241c103441d0f21030307001c80140550342c100001300001ca000c40c401c84024030240c20110f8412104070326a40c0c0c031202ea088a98031418200c2c00600c007460050303a00c41e8205402241a20308118540307561400039107010b003a800a10300d02020292505051a010b400001d610306c001d858515410050400c99203400000d40da0001c00220108610780c00650f581500700443c00c1c80344100d501d0115000260217140c840c070340188a0b09a030301e0696008560742401050f6100503031482c207004d50b52400c034020a201da099040f540303004840795001100e4144110035034034582504d801515a0501002500c00b10091012070075019091400e40d0032002d89c01d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 401485098 1250 401483848 401483857
    0xb04050603060c1602030703110306010e0702150618010f090f1103040303020a170906010f32041808040503010e03070807062712180807030b040602040b03130314 71
    0xe800381195554800f12034080768009501d510069484055030005070310100170b050042c0d4451000100103070301e4402090f1400e90164440e1079003e04110401c054107a000c1030781c904801c290001c1c0710098540c07a000422030803a2008a44200040900000e58000315010032021903441840400c5940c900c01c0c0e039102903c1000e24101000c10f0100b02040002c0c4c840d03801050301c01c49503d001240200800c06c2c04014540640f410f0407280e101e0001444441d5080d41b4030401007035107404070b111040041c15003502155401b01c032040e840148940060240c0c580e43c000f20504003c0f5103150303003920b03210707c1d102c170580e0094050f0710302039031038546c100300c01240004c220740006401c41001810442d041c1c2c0d800020b80071050009003d000800c041c01d401016080034061040d112342e800304078000c8031290003400c020030104141410440000100132200000c80ca0b101941c0e003000c40031a559880b402c010000c2d128a0348000d10000000042181c0c034646010503154072442070f80c4038400f4000c09400000b081c001e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 401486348 1250 401485098 401485111
    0xb091f0c08060607060603020901080105041b0303020a0b060102101d0d02060402010206150301061d091b01050913060803070302070602070b090a1e08060702010e07050907020a1e0602040f05040b0405 87
    0x1640307004940207191060141980034858880840c00c82c1e02c90740030174400d02082e8130554041e912102440100410314030203075034086807222001000c1e0b1550700c00075514ad140d1200030f880c0400040216103031780d2007888030719402c001c80b00041c0302070080d4011000c0c4101801411504c2800b4074040ca1000700d10100704540520f8059000f41010b4840c3c11449c2002d0200c4203615525658038003000485c0542804c400f0124211740c4810a10381c50310034200d5003010205844035032001c86910300440b05070381000136500117100648104c070482c82c82400300760050066030840c00702c521002c11554105a800036111003515156400d5424003580c4100010310390146d0b82c41c0075840341060304d00b44128440c43c2d08854401c514080042002544e074100c16043c11815295000140d4480c0300c140e56124040151000074441564624443d11f8612802034403440c803901c0007002a400b601d4004402070001c0c110007100e80d0014011960707141c3d6070465030382c06a482d04c103070b0380100c1c1800d00f002220725141c4a094450031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 401487598 1250 401486348 401486357
    0x4050f01061202070213090b130b070c0501020d1d071512090812010e10080307020f060c0a0b09010501030b24090705040f08010209040b1c060b0109030b091f0c 70
    0x342001420b40d0225402101c003001e09600344103440150751113412040c05014140c0d80022400001e04007200c2803034004055040c5850318480d2240003900b440c0205603c04d0052030410029415803600c18060310448082401240c1004e048051815100301140f444400e030b203084070100c2d03545504855142020080f40340c0070030b2058030003039503404180d003000707502030310411403249030070550705081459800a0f00000c20805d41030040089910103249002c026110800c01182403100c241e000410342c1c038041d00d206010f840c01041100092070308005241300f043e40201d146280d490243c102034000d000901c81601c80b1900300700410103120314061042010007001c00c6000d01604028103108030703000c1c05007840041000420001641d00c4a42c04410702622220b8005669181c62500f0802a01c00000106102d6448004070203002c070007400c5c8091074580d0000004c103030202d0000c01a00d111240d584090500e441d00004c008010002044140f00845580411001c40e10006252021290042032400114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 401488848 1250 401487598 401487601
    0x812090d020705130603080d0b21060a0207050309060a051804060506160804120809040b091911091305040b010f0506040608190212010303090515120a0f230604050f 72
    0x141021003c0c4902130100240c0031510761b507281c0d101045a40b00d000001e80081c3d560300784102501d441e0060008218080e06000302007036a621200b6203941c0c02030100745510b640054200100071084c030603103c107513900500e010b0b150005088041c18544c09000d01c0c0026042400a040c920b18146c4112801c0e20300c05030041e4100f00310052882580460b18405a41040b81484002078a918400700c50465078490143c03242c48165020521040d100b8510041d4400d80da40000c0128030004e2034603207402c5a8207401d001c103080c070060400300800c0c4101d440603071304000c0c00762420341c0070205504050700030380c800c480c03403981c60303903a40000d404680090080c6580841c08010401446100b140c82c01e8002c181001c0c00c040344400ca45c00741d4120707480504600c111409000c01007040c15003154801008000a4030445889805000c500c5090320406604207409041c550224941240c654044100c001ca0444100841d05520400c0075410030803115c0c403036501810720002116400d1900036103001d903003010f80000c80e5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 401490098 1250 401488848 401488859
    0x7290115030b12010513060e01271a040c030b070e030c060c16030c08070f1203050327030c010b0111060103110d06050114151201150c0f0812090d0207 66
    0x280c001c2c0c00301c40e41c0c030650b18440300d408480700303210b280d0158500003051400f0a001d1715151003610300400002070281d24006844c2280c03400b100b407241125640c40071700c2074103007000c1c9019012050f26024035140f00e00034034100010444000018025039018a00100042d0340395032085500140d09101c41c0d400d0307004207190b10002c0c10924050f002030071485059031600c16900400c14280005030388156003420300c0c40400c121802d010b01040001d4581081c3d0b40041703a080c41c0350707044140e0f00d801c002010084001300240e40c80e24140c030802400640d0a810802000c00d00292594a03005000404402e510b030407012115036000b804152003800741400a00496880c0d0f486483d4100d81071040c540d0407004a925900004000d849418040c00c0c513856070500242c00c1c031050094401d01500e810f80c001d18104120009601ca2400302030444803ea80c003c4041c550340c680c202c07042c400d8044001d1010321a0700f03c840c01c00c000e600143c025195460011503050f80c0d040080d03551a80e41000020141e088010107011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 401491348 1250 401490098 401490101
    0xf051503030310050f060915070b0708070c030f030209120d09060e13090606080a0605090106120206070b0a0e030f0403021912060b031603050114010504060b18040905030729011503 79
    0x4414030300a0881c7d041c102e480020a02030030822241d20040342000601c44100b105c1481683d4112000f85402e003900c0c60b007800c001d4400042d900016080c8040c001008150034420780403a40225030182500510b41c0005044960343c40d00f50920b4404500d0748400428028800c05084220036802030548030700d80c4400c41d20200620484800344e603903035100c101c04110900c1c100080f190a904c105000602c070b282c404421801c442c00740d044044440c03114088100544e0350013080d60031094020428181d0740d118107000d4070050008000340c010500001c82c0300d0880c0f41c9028054401ca900a4a00c101d05102d400d8451100c504e9501800e07111001085140c0302003840c55012551035600501100c613031600a041c03030038004202d944104c2e0661344800c050000111104103560043c01c068505004160411582140b076008018500558902c14206d494090391190459010720346c00030b064036900c01c41c604044076400301c42c04480515030008007080040138000e4079614101d5842c8509007180c8402410200d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 401492598 1250 401491348 401491369
    0xe0f07031b09020307051e030613025502070b0706060b1602041802091519031101090f03080a0c0f0b0108030c0115030f140703060f05150303031005 65
    0x409078800110109040c0a41d1008600031446500c6132511060101c1c800080b02001206808903c1010f00500115884148880720b4813441941c1c0980c68041012500c4044008010000604482c0b15100941ca5070000359408250415882900c15410a02c05003030a0100c070480a50050384040c008111840b002005803aa07184144c8002c2380341c955560000340d140c0c200400000c1c00c030b40070107400e204500c0d0500ca00b5803007005905011201144076000150030f0f0b107000f880c40910100502814890340c2c0c0700080100d0600501c909501d6080d100d0414100020f03080d50b0090100360f02d0007001c502e044501c1070007400c680d404801c051a10390481401c07540381e944508103e481d480c1420084d0006030504000758040c200903002561201d101d410f40e1030a403190710517841501740f100c0c1818008a46516070321032441e900002c040c41655650044149003900c02e03031014104030b14210349c5e0300741e02d101e5811080c02800da400c48202c000d9070070b5041544900c01a00c100c0101e01000004226a050100c90074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 401493848 1250 401492598 401492633
    0x610050603071101060f170a15020f09130c1412013f020102010b0d050a021c0f030f0e180610020304050301020c070504060e0115030504060f1406040e0f0703 69
    0xf00da0808105100c42c252025600240300c80801e11200f44441442c54818060190000c0d0060a000c0101e8891038600c20880c40010070700c1d0f030006212840c1010f1081140c055580c064120342c400c00d2120311010040001880090005005104030480017001d0300903a0000611400070543c540d1900d12007040c101d86800307903007a41580c10440422500542080c010441407442917050320006584002401c48880c8040184107031064000c81000c00d000042c507a0b02d413641078503007140a043c003003204103050f01d2640c0300914100d085001c400c101907002003040c040e45000d45602c0f2086503c40304200360704450310000c182121030710001489070320b403c200e000660740c114010341c0c0c42c0c1500d40d00802e013079034040d08554030702d944036107810411800d0603c140300c01030800385d00411079941003112061417900456208010152a5004281071080c1c40c2c2c807401039098500c504004602603112a8030201d401161442c0c03090389414224101d80d200800c420425080960280680508640da106404050b90707072803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 401495098 1250 401493848 401493857
    0x1a091909030c021003020a0f090f05090907030803010816090b061204021807031a040b0f0105030a0b0a0f0302030c100207060507030201020408060108010b0a0b09010207210204090320061005060307 86
    0x4100580c03103680701e5643e0101345550250380c80b0f4081e000504007050301c1c0403180402503c4401003160004541d102e0f81a210b085481107842d468100946207442c1c0350707401c081d001c42d00010000568840010354000542114086200b02958580d0080202d5000559071038002ea4100000c0701e080655501d51a40240700501207d0582c0000c0501c2c8803074101104d8030000b0941e0380d441182492400243c000e207100085400f48036018032103000c01e010100342c5080a05101c03000c00403520081643d0450f00c214100a0b100c00c04141c2c1d114240c1c3d5648a051009a01a01445440f0301881c182a2030f042d2409200c0d03002410013914116040300d083c2d12080c001d4045541c280004a5501004d0180a0081c03c00c1c400200d8041040800c0004246041d030080c40c0c2142c003006115100d0343c001c1f441c0c1d000c5951014500d11302d0281040150f80c035508100e00250300502d090703110420940c10001881b031070040b50030121517004101d1203081d03560314165081c40d1400451a010031492410702e00665000145140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 401496348 1250 401495098 401495117
    0x90307151d03010e060403080109061a04060e0d050d1701170606060f090414010302010f0908070911040509091e0703021810050a0e0723090111010e0706031a09190903 73
    0x201941005e1054904030f0018040b5001044141107502504002e004030007150713613803c4205110b85a60b880351348203000600800c8640d0000b199500d500141d942604030081d180211450071006041e003143d003490440c543c034418004a01804245000b401d0039407010020706141d11203c0820100342c000c9101800c524404001000254590b4002c0141c1041c040c00c4035805941548009403008410308007510030032404640400c40c115001a200d4100c0e18907a10003e201b2900300440d00182c840c03900b1164001c0c1a020a00003000c0001451182121000070001e00d034080080760151100454413029601c080e1512a029124102c0f401d207582240502e0403003030442c0d8ad00d1020071104081030340300400009807441008071240d00560070041c0e00f42d0b503811480a0f010300c4880401a8020094010704000c20309021100b81e074400d500100451100d02c040b603003c990f40703500043c0034107011303504007400540314502c1c0c05850602003055402820000318194031403650b000d0a10040041c26416420041d03001c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 401497598 1250 401496348 401496371
    0x5150604090504020a050913030807090b1b010b0a08030d051f1d06030102070f0f02040f0f1d07050102151306090317060f130c180902090307151d0301 66
    0x600091150300740c0400c0da8686801089084600d69210134000d854820800580c82403090504000c04d6140c20f02c440a03803901541140c010141d500030340a84040001e0825003140484805450f4084901c02400007030b69940078050b1410207845031070050341c4103000c0c01d8010b00701908007035401504030382e00070b0a4450b80d81c2040070704070556100780e0200204900002c04041c041560540c0000150003c3d032810246646441c81030110a80c080e0031300404007038038000c654403908950107001c5065014000c80543d403603241b000748040c0c5058206103076442d24a101c6040049441012110142c0103081c1c1c1520108111190700802000d0f12440b040c0b02d08a000020340c0e52003020a00707400b940e180080300110741c14040e030260007e022584544081445220315999100715000110741d0002d000c160311704450b0b03080d20408200f6241c03140e001c980c4500400c100318540c0c00752aa401044088440b810303aa510030350710306080104008001040d03040e0801c1c03503007214001610340c4400a13000090201000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 401498848 1250 401497598 401497609
    0xc0b070f03110a080f0a05040203210702090702010e0712110d030909020c0c040f050f07050d0209030f060402030706080c04050105090109150306080c01030b010e2b050706021507120515 81
    0x200c40000b0135500d9080c081d4a5030b51060a50f071140c00500100203e0400ba0000303a0703a80e4035520319202e200d09805200c840c400605041d95001a13002c0d10110040c1400070010b4046c04140c5002b4103180b244400000b03603012140307145050b241c0c100c16407694480700c01082c4850030054007400e406000c0e002000290141c1c070751004105220000001e025100b0301c0004010640340c0a1540a220300e0910b0107210030811008005a000502e0741401540e420240c1380d04800b900410406030ba140c002c0008508262201042341e13440749200710b00b910700d0aa200c090a0b1085241525014440c1500380000e0001d94040d100504008405040a0020581ea000490001803000329010300080d11028208450502040200c0045a00b409c09009801c141c20008001000b80b04019206054401800d03136130011480d281554441014080205c1c81618280b03540e95040f948503400052003981030105c2090502031045000d4003a40e41e9200308442182058006020007074450258005150100c030a1669030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 401500098 1250 401498848 401498857
    0x40b0c040b0703050301080d03020a050a0c0c09020409061502010c0f0e0316060c0c081f05060d060606020322051c06110301060c031d010804170f0f03160c0b070f0311 73
    0x6684d0302c50780c80d07041010443c149901880100c06140c01441307054003164000d403c3c0c4040100514001e0026880ea00f8003141200c195807160300a507200140215a250464000c1070980d0030b1000c0802e44008013131422404ca803034407144c020020720815162020a44210409107070104002e0883e6000e0050f50510b5505543c250700140118155400040c20842d900c031560004210319006041c0c1c0c844822543d15507207202040c80403001c1e5031840000d140e5520300b85200b1890740c0009042100b20b455050181d0f80754409003078852175070b640400c822040480a200c4000b40c07000a0034114032250745110a07000101084400c480309034440b5009026405154055402005242d0b2250b05426041c04c1c094101c01140903001e00c2008903a00400450742c004409079081544034018503429100c450094030701d0b0040e821040f01d04000060200c0c0d12000e450051030050038401c030300080140740c942c0c01360380000c1441f074003d122003031850009205c2e60050b15520b40c4000341d403d0214100c1000d208101c0f05a11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 401501348 1250 401500098 401500103
    0x50c03012a0903030905060c030f121e130609050a170301150908070b07030903050a11040e0604050a030305100e010803030a060f06023012010509130803040b0c040b07 73
    0x3500014801403610699410581d141e038282418420704588005251035020b016250088000042c401c0c21f541c4100200c80508000c540802d407502a0280e1604090005440c82d55101d1404d10f00000c640a500f81250b005450500b807002c1000815a2030401412181c10286c0c0c46000e00701d04400414a07170000c5120a00d5103e110503500d60602080040402c180140c0340c04101110106212626000030000305661821542c903854020f645070484130820707240c1005100340511716446003001048540d001000104075020300c103000384048080c3e9120340464014101d980400ac25201281c084d070f1200e40c00802100c00d074089523480701c00c00361003040300b80e108900f140d00000c104047d00c00c00e4450413000e0302c2c144500b40d2007103241110081d80c850714400c008031000fa80b102010f251000321400e03100b180701c49045158482e180d02c18645c0500d042441480d009251480c00100703c0d4482c0325810b07440680c014009819600e0b503484d2100c5c0050f0040c0301112000041201041458610014059151 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 401502598 1250 401501348 401501381
    0x301050f07120603031d0a03170403170307050a121d0609060109050405030f0a020c0406091d2e090803090d02010b0108040b0106080603161815080712050c0301 70
    0x62404006182e1042c54040c41295483c0840920029501900c050100c01c2d08580c0b41110000600003c1c6940c40c0b960b000030b0403516007100c0d00306441803d1002d441168007885090350141030040c551111480103c2c0c2490015008200d1644418003420b01c6a8000030240720008003803183e0f5400710064060591070316150f0f4000d404004050781d00700640380c00f51241020911881c203165451030390381d0052401d607003400000480c5045e0510710800041204110041040c130202e075649003401c1c0100790030180104103514481d45480030240014103d403183c08908030348001110115908504031100700a003035003854451820b900843c1405010b54088d09010000c1e0601c292001c3e0080c0c216111550f2036418054440704000110f5601c055490450780d0700e007400612540c410002904203400350030554403440e104100450b11b80705551249141024000017001481c4102c555070703403003014620a8202540c407480040c80f40c050802e80d401c0f101403050040324030680274400020700303582d102402d00b86403c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 401503848 1250 401502598 401502601
    0xe1303090620070f0f05030d02030a0c1109010611060703060e060d080403150b030601060905030309010507110d120905030a111c140c1c2f030a050d0930020105090301050f 75
    0x1598502842c03c01004d00700c0048c4840c0c000003001031b450380941400c40040c02079035407480c1c00f40011b2616140031414000c1c40381c1c00ba5a103c9001a0051000290030612403084c2d80016811500a200b0702d03058072402850042c0981d507002c1003100703501301d0100444170b4031824040080000c2c42c0d5000b010000c40384001c04a0010300fa101454030b4640c059205604204280c0b10400041c1c80c003004880902d01c0c01e1034410307500e44c41c42c2020382014190403143d83d0000e03407007008041071201009640390306c407696030b880c042d11075030391020180d0711850100d02809000744171410413580c1c42c3c09100d0414005108440c020405030301d44a0409440340781b22200642c0c1c0080c001d544651419100004030b10b0208003030300800381c40f262144d41010600950480e0540340e002c1080802070003040d43c0d0006600c00408840c0304078400e252040d10303030038000b090001180c2e52031404a4078034200d04080fa20780c0c1d40703644002c0304500d00d111402000c041c001d0050341404400c10110006032400c0c0150f900c034010490042030903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 401505098 1250 401503848 401503859
    0xc0307020f070303120213080d0305090f0703031704060b03100b2b0b070203041a0d18080a0509221e02090d020402071b0602070e1303090620070f 64
    0x400028031208407140e005030a00b0b00009820840e178494046541e440143c0310041000c000b60310a65541003d0307554071801031440400780c0e0682240e07214a003024240c0d10308010301c9408690701c0c0c0a0b404018040342c8411141010f03200301141190b4841e028a8000c02e6208018022078104041c103103181a10316121401e01101d0304020076070502000100d51001410612105914407802071a0b000416509a0340701007180640b0820544024011b100c01021140704556503042043c0d01003240001da542c20100201c1706d250714160058000398100b004039190503a050022203080d40034106180e07000f10408003282c98286030120388065240c2d60341000a0080c2460000d0109501007000004590f00401025680340c480984c40e40101c0e90607600940c960915141c6a40c0c014100c0313040300700203107508030005001c07940066010111001c1407605072550302d6a90450449039410308003d00455010403041000c2c520428000c10500e04880b111080b0100c107031a010706040499019840e40e0340140e009114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 401506348 1250 401505098 401505103
    0x160b04030f0206010605160c0801180212010209010e1327030e040515040c020109080d020a200a030f0c2f18340804060b01080601140a020106030b0c030702 68
    0xd000d00780e000419907585003600c02002842554104414a0040044071003000104030b2140090500c0c00000c4c00800441c003a40300203c2108041603210305c072007048124284406108035610b810069603400c9840900301e00344965030003007151924401e592031082144c1907007402120743c0060142061a40304104604000f400754a0072410988250315020901450300003211390080d42010644020590f040801c01c140d00510203008060011000014054189c02d8560f00400ca100156255504055139142804840d140c44007544415944180124030200e8010045d01c0c0c48540399103801c8551050079074130f0389140380d07170105440b448500ca00703a5015808210240c43c510710005884007044c0001e00b5901e0300f4002c9010740800c05031902050340d00015854101c01c81400307855440c8401c00305015110084c11f019085a05940d803510384540b00d10103600ca10422805840141d452110b001075502440c20781d03500510841003959a03540000001800c66090648100d00d00517140c0d03140d00d40100d0290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 401507598 1250 401506348 401506367
    0x305010906050702011a010807020313091410030b060418020d030e0a05060a0c170c0a050606090a0203010b074e020a17070312050a020310050307060509090c160b0403 73
    0x2010740e41004105804c010b1101c1c1c4a030b06d021003d28000d42d8584400c02d00340e0441c071800c180d4150b203111541002c615080e29810441e421150407a02040e03d94400380710500c03130182400001e1405034148081102c901d400d0b00312821b002c003000340c0361081b120f440d8000342a075805104110080b92202c0007100721840c11310b8a210007480c4c2518400d143c5a180c0c0300003044070707501580003096002800c4c0390f6060f80d8882025a00416007240840c2d234891480c0c1001c0d070361703414201c9034184034000e0480040d45142460080e64101c0d035a42d0512410100c5641d072b950f10541d440300070418006002904681c61039a1500042e10341e201d9007440305c0b03900060400503622002e10b118071100795031100070a90002005020310b0345542003102e2545848038514942201d07002e02c1100c0c828800750900051084040342540194000c0e02170020128080d6510303014980c5550140c40f519000c603800380b0000d002c071304112140e10b500000d02c250700c9242c0100e42040030400540c4400c00e461704000d05082108054005a128 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 401508848 1250 401507598 401507611
    0x31503060e0f06061305040c030206030f0a0f0903140703020c130207020103110705060105010c1a010f050909010b01091404060510020705120f071203110f060718050f040506061201030501090605 85
    0x34556440e081d0003240e4a03c2008100204603580c6d48002418442400b25500107542c0c0107207060b0b681d0622803070888200c40261000000b6520b006100300c801c580c148205e075a425410384910740c2000707048514a2498000034020f4042d402034061100980d61240100445201380f84001a01c80d03085d07000040490b032540002d8212000d04000e041c0118400044241c1119024a00a0800c52031031410b559402c80140e0403240c0c812040e00007040880c500c24045040e00d40035a07801c40c195541505d040d082c0e508002c00307140410500e580601000003c660414a06c2c03002074004030b0402d0340c3d040401d0111a01141c06001a00509010f0100386011140204016000d000610040305000e80040c1c8a4403d4400d014810080c0c0100b50b04140c000da20071201100490150340000745c5c1d180340030b0345406080380c00b00000341c80040c0c05c0c0d600f45113071203501e4107030ba40160050100c481004140301c02490f01030041070340a4020701a1890b4000380d042c4113406188100f001203044156440c2003416284040c225 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 401510098 1250 401508848 401508853
    0x6021014010f1707080a0f030e0105190305070302070203030d0f051807050103200d05071413090902030a021905010e060c06070c0c080714090a0228031503060e0f 71
    0x400040c0e401812000907200d0151600381e07481074612120780780000d1548a1117440c0100b00040c0180420301e819020340c6400ba454000144100030011901c2c1e102e4101600c2c01142180507001d40c987c42035015079407054040c1401854030b01c254000a245400101c40c40c04902c0e103030400b000e8802e9040c083c0c544c100e5041c0020044c407814402c1d84646608442c0201d0341015038031042030100000d821400030a840710103904690340c1d2000c038103c1c0c024001c11200800812a0810544101c0325080d003100d03e4402c2c849000070f01c2600713001400000d049981340a07a454881c1d441d80c000560344043d400000c054150000406661501c070025080c95510481a84070741d6050040c45440000410260344c0f00c07030340e4903000421300f225180641c0404c0a40c2c1122056100381034002c110408903503004984d180c412604185070359200c41400041e0312071a1f07002c07200c1035402201c403021305070881c0002d08103c58034140071503020302800c0c5241c081001c81d4010349106407200030900c0b0354407081c0101c80031882984007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 401511348 1250 401510098 401510101
    0x501021809040f06051f090c02010516020a021c0602030c1b0d0507032706021f0b0f010f090806190f1103181212040b0901092f030706021014 62
    0x1180141800c0075000a0003481d10b55000850380141c2e416103902c1c0c2441c03080d46d100881d0301d60412100070185158400c1c0550720300004181b61a400001c7d00d0760741c1c03c1a43c01469820020b90900035100c2e010300d240c424510300c00c0c1042d8009061800514410b08041c002e041d04c4241100c072109107d0382e40b90901c1c000390403400341607141c19401811a034050742c260600c02e071080140241c50390451003a1540d0010f100300031f08e0200d0f21320f9000c14020a5044150042b5603941070780c0301c41030704a6804a00403640309404040b0740ca0a540616803086000781a400c00c2d50610343e5414296040200880f04400801490f4498190708440c40c410100010707032801c8100200200c0101c107401d176110207000d5107038844250700b0f16240030908004000c0703c00d500f002501e4980c2152008018000d0060350b0413680d9500880010f40c0c40c801c1441802000b9070041040c404460b5003440301c05041001c41c00c03c0e015490350140039901c3c1d4030200007010007841a1341c0100407144100d41100112074980c15641c003d08801c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 401512598 1250 401511348 401511353
    0x1021b031005150a060e1809060403031113060810170d0806040f020409140c0a0801060c03030f150317120105130e0a0b0a0b040507050d0e070f03050102180904 70
    0x400c04001c5001c0c000018140c0c6400d284200310b6150303c03400e580d003e02c011001007152a8000030942c0307258011b40d64030b03034400c40101c15940c00743c40031262161a036000c1310004010910070341001d04c4100d00c4a401a280928110304502014041d8100c6401314550303d06120402e82e22030081c0d0700800080d0030007480b03082203091540d154a640701202c42048400380110f0003daa4541c40001d2004030190219922a50390641001418802211009a0b034683e400100c11600740e008032204820140d542c12403907802c00c1415076070651010700035005c040d42d40074141c140c2c4000740b040b04101409080c604045c0780c50b626148506204044400703026400c01c2c4040e1103e24441200c880c1501c5003141c42d40d5000b0680405030000344400c2d4a082038601c50a01a00d00348031a48a00718010f401d0510140041d0307016100340003d65400740c842900203801080706d02400b98003035200b44040303100703141501e4107540c1e1400c070000000c00342d0304140d4042c0d500280401040302030751210204014251401c107482d19194 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 401513848 1250 401512598 401512603
    0x91a06010c0f1b0315060f05030706050a17071e0207060e010e0d080310090b010801030309090207150c20010b0105070b15060d0e06100513090302030f0703030b01021b03 74
    0x2440082207240100741c02810000d1040da2200c00300108003002c03450664a0030f20342000710040741174007642450030780041288551540404192000500201480e0f03140840855007940130100da601008003074842c800880c46030704169030082446a4800d0406101d52510440002c1100312080556212007001c104580d00305611458500c402d00b0200152070b42c6c1c2c40452040441003c0080c643c10700003042110107010641c030355068441640302048200c00800054408003401c1c000034012a00215041100d51441d4006003180d40c42188070060720344824226000340c035009000c980110701c0d0f0006040d080707450400c075250320400c0c0b00300038003014400300c0010700136100d4148007800d51051540007807003183d0404038285d54001c01410b140e0342c40160240f25001030102010300584c0380903000c08031301d41810400b042c809440008203c5410301a401000f84000c00c400182281075000a00035030145134030a5002e03041250094134042003005851000a04084425400400c00d410390311400b003030354a00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 401515098 1250 401513848 401513867
    0x2091801031110050c0601080607080a05041509080909010602011a030c0d06111b0607110f060a0b031005010f090617190f080309010e012f030a06050d06091a0601 71
    0x241c981507040c40280e2400c82e564407030046110300d06d129610001a404800045c80ba08c21005941d90407040d450b0b446102d41611780c240c4000e01500c05445540d00811141c0e840006041d11854415141043c0748011502402c400d80c00400940d54400ca81d412000401c03541c410070b14802c42c0a800c5800000f400200c00d41000741e00580400d545440e800508505c000441d5440070315074640090b440d180605250703885800301c45e00030001d03190745200d095180c40011503101e590305801c09000d03241da0b0a8900c0e4000d108140b2071640c54842d018641c4c11203e8148141800f07031805807602c804040c107040d803407015900c2c50b42c80500a100340403050082e15202050607280e030a03801045620402c42410080000d50319080e010301644d200005101030281c0560224441c4001d01000348200d003803c000000040007a40c0c160070640e00c101030a031494034902e00055511118040d0000303115901c0740302180900040c5030040701c04075034800308602444501c0181c40c1c40400f500700341200f1440c0c0742000074003070783c1e6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 401516348 1250 401515098 401515133
    0x60f041a0c0a08040315020c1c0917060901060e040506010b130504140f0124050c07090606021e032a120d02210c040620010f0209180103 60
    0x150302044981400200129204048807600300c80303072060b80d0300304030303181c3e0b03000d07200441c0c004d080c010148240ca80540265054100080041d00844000031a052500d02d4203e0b20300080007580301d0040b0741028041c803110060352700d92000b070090b840c10400c0c05003124001c0c0c01c403402042240040200040c00000c2042c10364000c1032841d0780390040740300100c08551740d5403c080e41c440c1c02d050481c01c0614070710785074a214039195a20b0860310b9a0302c000b642900321a08071200050f181d103580d02082d06001e90003e0210721648030403100d0081e601d0410300200d0300650007480060300000c103c8480d80c4410700c22400001c001101662500d900640c26a120000100d20395007000c81702c0c119100303503640a00880b41161001161142d8032500e00a584d402540602c024030a81d0038404105000c1d29129082e080c41030340e0300302125150908010050714502c12901d4000e1300210000910b80d0075141c00e005161202100003000340c0c4421403501004407038003520a0101e00b541c082c20040022400500f8101040c80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 401517598 1250 401516348 401516369
    0x41b090f0b1c0e0303010e0a0f0c0504050418050f070f0914060d030309050604030801080f0a020d020904170d0203010e0a020306010e0f010e0a15090806192307030c020705060f04 78
    0x5607440d20407020300741029240d00f403400048000216845440105840303944201420407440003400001c500721203031050a480000c00030b010034820307030809500444100043c65100c1030300311a640d590500d0560601d624004035000020304000345425a0344010241184120500c55030407103103a00c40da140002040366200b28001c61032142898080c0d40409407007a0000252110f504c1c0070b040203407005400f23100d02002d030700c04d6919a1083e0390001c51540c00c0954002e1014040c121284c08006000f0f0001e0000e072900d0031600d00003da950b44410040c001013203044000742c0c40f50302d05a40d01100560080101c20000d00400c10810355a910181e0300c480c01c2d400302c540c00e00710420803004841049800d40940d4103c0701f07240d00400c03500c001906044003040190748844425843d911104c0c2c81d4401036412544901c1e52400c200d500c813010390000360503902012072401071405440d004608550302a10441e0100303960700309071010300754180306160151009032802443c2800404481101d441030303114580742031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 401518848 1250 401517598 401517637
    0x90f1501050307050f1204030e1c11030c121f060510030f0b0a03050f0c06070b160c12030506030d080705040611010204090920010320030a0b041b090f0b 67
    0xf900800c01d541c03001c1c0350004603d8a60802d00407440c109a01078805501046222008520918103240001c8440c101e03100e110b54190250365031140341c8480003990307d42c18014640c100d00c10307850f408511f20582d03045800034000d1280c042c0c0d24011065102c1c0002c071419040200502c600d44816040902405261a0000b03804401c13041440c0107084198106030b00008400d800030500000182c2076828400400940da50100042e00304402c80c0300e002001442d541900d0000b8502048900040d5041102d0f0308017030355010303103590351040184981540c4d00b011903135a80c280b0005050420406440b4001c40c10f0000d1142003603240601310b4020307482041c081184d071035030002c6000c1081d0140d50081c400c00c1c50070f2100c4186071418880450f072044a0640c203000080300100290b20a0140c0c403110504020b04072a02c25084040300324680c40142a502c1044c9c48003210509610381d0312070098922500c13442812042903a44008040041b154442e000b882d04444007408003841e01400c03609960181000d00915 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 401520098 1250 401518848 401518861
    0x20f04030f150c0203120903090d030507260c0c0307051e221d010b13090f1502030106020706030b0a0509181002191706010806060c1b090f15010503 65
    0x580d6188140790b28181000b0b400707040c2d0303a000406404075030b101d240200c50700c3d0f60302c045c0d40742e0b680507445040340d00c4080360500101081c0143c0050503040d0107000c079a0120810101921045080d2a002503035800e030001d51078000708010300c9800041801100503001c0c45151000007150b021030344c2e0a8000007000741901c00c04550b80d016003506000c0392810302c0004040e00c8000c40c401000c002040c03d008c49010181c00700082d05c1880790325a480001888d01004114007041c19005100505084906203909079445001c01d80441854001c85074400c405643c960410500034200510359100c0f00500d070074020402007980e900d09115040e01c10950344804150340b14a00b86101e00b0341d601e1840744038080d1580d66601801c2c0e0360001c04140d0303020f8141042d8040b1540c01200c001c00b41080d0040043c0700c19020071055889904020b0304420000d06550030031701844100e50070550300300e07820400081c0103c3c0006003800d01d06286544210b541030814581c1c9445200240d01e840070021075410003e001002030700d0f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 401521348 1250 401520098 401520113
    0x403030f0b0d060506100f090303081e16030b030307030914040915050702010b09010612150803161703060306071112041202011e020723180403080a020f04030f 70
    0x804080202828100002410702100a2109584407030181b03840e0444001a60300410b26007104014580d120401d03113240d034808480e001d101916448082468081010203444801d000c58003074011007482005c80d8040f01e4024007101e1010490744c0c000c0d0400d001903c0400e0f003240984086503580c1c8842130005030b0b440d0003d0010a620240240203041c0c0000c41d000e6000603602c0230748104001d070001c00005000380c081122000d402d100700700000f00550116411041e0319086500d01e04810160900e80c0342d107071488a403c0d5000b2043c100a4610280714407000c0c8511175045044110300c03684d1107441d42c1414000b00e0b0b205d24008048805000c80d64450f05854102040350407550350803010f5861303c507901c44004400045028034140d0020322400c0c09120b43e500402d80706514102141c00925203240b4003002e0342c400424110304940f0381d40c3c486c20400415150b0b140d890104408010400380907141c20714028007489805011056064414440c0c1c1d032540440d1000c0b50300380d031f401000c040711005151403c00c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 401522598 1250 401521348 401521361
    0x1110f01020406090810140c07020a03150c090b070c060f0e0d060912020c03031813060608060310060305070302040506060c01060e070f020a0b040f03051e13060806090403030f 77
    0x4a0940c80010700081056010302d80e030003520109010345091341444c000c07000c20750303c0441c00d00c07120100c002d0202d440e0048103402007081f140301406c135644450f074030f032901c5070000d85440c031006c400ca071a0185c400c40c650340301c0d4414015100c0d500c41e56040c4101c6d515001002c003540d000d42402d100700c40141c2c4650601410484011460080000f1101015494068094080c0c1c440881d40306544030780b903842683c008551a150010043c00442c1014840c2074066002100304801c590442d94008248010301c06a01410b409002251038000306402d00d0428907240040d075047c211192441d0500910005001003070700340480350111408526920340100048a51062640420140d0b10f00000007422000305c410310307449844c1c03a4442c00780701450094142d842e81d01092000b0544900d1a000400040c039006003448401e00910b401400d00003051800710f182286582c00302c01d400d40100704111002c42c140d5118028000c28a401301860404d000422484003028000a080c5503c83c200a80300c516a90b110300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 401523848 1250 401522598 401522623
    0x90521040e010b1206060702091609050904050d0806031603080306011e03140601090e19110307020a02100c0809150d060902090a0b0301050a090507030b09040b06120610050111 77
    0x51296941c01c441945544188001c0b244c620981000a480f4078014058992980d009401c074902d03a40c03032050210700342050100400511015030008501519041c4416116034414801403815180c1c2403006002070700f006145910aa0010000000c04c4d820803103c601169401409283c480d201c51005a8400d6400f0404e441a081941c2801c01d21a41c0341c1c110141480303c80c4c01801c001e444010046880010314000d00c3c842100800204d498541c81c000b0801001c2100b01c00000c0c041c110307404d07070500c5600607580c1d4001a84910f2500b011751404904803030094006061100d24600c003a55000750031301031500180d1045041039018440c4010400444004544000042104507200c0004600035003080e00300c5409103c042c0004030318042d9507021281a114000c0849042916000c031080c050720004100c1820180c6400c0b2001e03881e1610005940107910a01071031101e803a00302d0034032880c4d40c40304960704055404801442007143c8640c0031001501c2080c0f0300030440c4019402410710740701d03222015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 401525098 1250 401523848 401523869
    0x906062001140f0f0a0204120206220f080706020d0c02010e0a0b211602032a0601030807060b04050f06060c030408030a0801030201090905060f06070f0204052809052104 74
    0x8203d150400c0301403040c802e2050400c0d03600c0a407641700d0018200d00941c0103007034400a21a890102614000e0301428150310448881030100c0300e851910610813141c0e40c441c1c25101c0d011101402490414403441004d08070307a100030309205505050041c03020402a030302038107210031002013030250b40354040c90001408203503078803503501d051000c0074015890000140440c0b0381e01902c081852503407403644001c00c070b491070340c000c509005c0700c040b10b201402c000c0c9068600307210900c040207088510a0091a000710b024480b1a0b071101c031181010f40680d40400c036801c1c132135032404040014184010448681000050301e4190312806003214541c954070454104200c1403102141e8250100c3d8810a62030603a0f06c03e07620301d01d001341c1e260000416100141c986940c03100c6890b41e55021030030000007418909006000d1302c08407841c56000f14046403c10358283d8600103451190080d41d80f00c00d40c43d11354180070b40c1010048038903281c40303286c1c40f194403415050b50a4810443ca0a081d0b00150a8030050600c2c1d411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 401526348 1250 401525098 401525101
    0xc02010e09330a0b1207140705070609030c14100305060105130e060f10080c03060a030f0302070303030b0a0302061209030702101e050c0604060e010e030d0204080601090606200114 79
    0x22400c2049840d4140c0305548942d40400c42e22020400e40729a031000c6480b1810f19120100103440c0e4540707c4225451146041c8803940c08034900b04900002040d44e5110070240368158207111074a401142c01142013819040c0f8030f114242c950035070312264a00706260008042c2c0b0790500403035452081d00100c4904400d01e000c042601036a14180d0f500a61046031000c002a69030b005010711034403c21500d6012561800c00240040c0c0007000565001c20014507414820748c490b80c5001041c900c410042c0c0059006020500070503402d03204054001ea82290020072191a55000030340720300c0703001c125041613003920000c9541c0400c00c01c152520540d0003009103c002c0112134005000d001c0070502101f025444070794a22070f242c010421070f10001240b002502d0076a0301c5403210030240074090140203e03076503215525007040800b8006003040c20032031000580d0325031810302194a40001030b00702509051030404104010b0307030060401d20852080e840c030410211140d00e0028014103482c04901003d42580c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 401527598 1250 401526348 401526421
    0x41401210e010f053102010203120717060103110a0c060e03031e06040501030c0311030f073209040b2203030506040e060f0604110d020d0e0d0c02010e09 67
    0x41043c8500000d04604000e10350b58611040701c8802e100d0104400c142000c070b8244803401007103441108007070041c0101c80c0b410107441040d0004240407a282400a1814282089581c03d01e6126540280d401d10b4140081c0c49280c1c880495407052444880500044122600820030590440c00d0031a4188060702d4892401c0200d803820f1101c400c4041310400010000121146020710402c0d060b40c4d00009031402440c11a41c0d082184208846265858400e8590a00803448104000009820120f0000300b82c200c903000c020844860320350060b03154800c03c140c0d9140e239841e1920515072058024003842915121240d048689046001d1a00810010882a2018182c140d00142e00500090fa400c11454088100080d00c0e90b10503100f196005203c00b0214900b481c094100c0d000b00000d540c1080e1910b03071800c00010032030b44020540e4506e103032179171502140c4043c00d0080003072400240c14007110480c42580020884188a08501c2c450030620020078400310407980c0c810100034180d0003024255034401c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 401528848 1250 401527598 401527601
    0x22080c030a0909090f0308060118140a0603050c0a030915020a080601080a090b040813080a050c0a0b030c030415020409140a15030b0a0203070c0b010b04060f0302041401210e01 77
    0x5140d4040400e4a80703400203404901c904c0b4882941d5000710b6600761880c2e84e55070803582903002070200c50400c00c580001810a07100c01c2049801400103020101d8600139010501c51144010380c0300405262600e0100310441030004c0450300f05898602d00002d03030000501d012005d0628051481d99150310100343d2020340b0303810011441c014a401d8903490819610041c0e520151011158010080a82d0802150014030140043c0807840540100104056190444603141102c801f0303058900f54003940030380c0182d0070801c030100054620050300070300e10b1038803807141902c0344030283c030041c40d002c00340f034044042e0482581900c000e4a40d9040501c00c0c030090f84550300c807040341036501c3c420741c500d480d02d005038004004440c2e00481c0d600c00ba01d068180e43c4c90440300000d420080c9404144000b45031000c00107801103450301d0180c81c1487e2000d490701e0604070018440c0718480b0f503101c241481044280030303ca02c0084600584082403a16145800c048a24582201c1900e2004111b00b401c086001e418103134103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 401530098 1250 401528848 401528857
    0x6080108010b0604060f081b0c0705041803021203250c05010b0a05130f0605060705100e06070c320109030e04060605032d0c04170c010822080c03 64
    0x40000e00150b0100c0040005611840c807840001c5203581200c110302d503004044140c0c2c440c01001c3c01c507036018803d1048102c02d61119411038283d4001c5507042c00b540c80d107071042d00c5000c92840c2d543c030700f0348006aa02950303030702000c3c200d0030a02d840840011070f06038000c942c0c0e5107500014079020080304100d075005411100c0280e012142035080a24140c1181440381305181280d8005114421400071086072800400341010b41c0402c00da2100008603041e180e04008100484c811401000e401a4140700001110000982c1900340e40015040c001c8041d4044040b1403041d03000402d1812401c4014448003500c035030101d2180c001402899880c83d503003810350007140350a0190302c8801e07040820701c0410040301c81034090200800e20601c0807610540e80324a0b5100c005020105084400700c0c004460010701000b10345250420314002001c0c002e80256402d16094082140002c0000b9202e2000103405104018160380004c4c2c024104405001c51440b80c4120403034029000995030310301c82400a8503642b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 401531348 1250 401530098 401530109
    0x4031202100515130e0610031e050309101e050301060f1e1416151415130b0909031201170d0302070809060c010c02010609020f04120206070804060801 66
    0x81c25009003598042070042a100342d0352440b42511128160081080c066030070781e002e0720714030394030303448860b15481c100b08090184a60209003110589146070040b0100d5290703000b40301080883d1603880010310004150343d10107000b19001f81c2242c030000d40850318040350383c5102c000104912980c40e440740c2c1100003141a40c1141d40c0300c11020540b032909030351100f22000b1180707041345071200080a140c0b05811013411880c801d0780702d07441e01070070314400d002d013003141c00701507400450311428200c08180ca4420384015841045540351546825482040301644007102c150003111012075a9039811250351152001c040c00a00070b9080d42400035108e40c4e2500010181c4d010207a540c00013168942c0001c01a034950303100200284400304c40302108030080d42008008450440060256205580c0c600000e480500a9030300000b44116040f1802030075510135500010105d841041119089a000e01c1202c09840c44010710b46200e40041c408540a445228000741111030b0100c2e000c035403e81e200402034120b90 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 401532598 1250 401531348 401531353
    0x90302060c160b1b030727030203060612030c0f1c0c0b070302070c09020304060f05010b1608070f050604050a05010501050a0501090e131502090312070206040b0d0905010204031202 79
    0x80d41c444800d0100d120309a801100c4032840311a01c0c0005401c0010640c0c014200c00f55111072800e941240c2540e908107950701c6005c18100041c141c0104034503a41030040d20380001e4000e88907441c50300425111070010300194002d0714501e000e2040400c01b001200d0300c0580c2c41c011241c1c2a90050304d0280c40342a0150740ca0700303e5041c2c9088650103407003100c000303031101c0e045600b90a40e51521942500294407000f0110740d605c00001c0005603204803440910b03c11409041d01249198401c4840d0088610580102100e4441401050000203108441040c0a035001c1c40f0303036603a00340c0760500020350440310b0b40050051050390708020412a001c03401c940002e12501c028030090b40c07194200b00c00c0d504036020b01c0c1e00040007031303030f0400041c0101d41c1090b410030400d50340c00308081c1c0540c407420070001e000e0701500250b90700025456110708082000c2c2248545192400e0b0504c016580012494801c500c6002595123010424185078402c0b64001201203520400071942e80ea56480c050f0401c2143e0f074030340c40160 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 401533848 1250 401532598 401532601
    0xf0e03010b01050909070e04060b04080d0914190918120219030503061c05071a040302060a030b0112021c050115020703061107060e010f0e0304030519021c0609030206 73
    0x2414140903904400c40305854072403e02114106004038608000c02c1030007002250200201c20b9103940c822880903111002d205503849041c92003891070248206500020403051041c10040c0c03e03100300d44500049400c8641018584102c1c605d071002d10107542082c400d00d89000c05260448004a008a86143c4607214003e01c09101c02810398855031012500301484003000000d40009210703400840d403122000f41180301c56100c1c83c545403d0402e0004080b6100c0d0f101070024450307400c10640b40112010141c644030314042c199400300722580190030b203c42c01d01d600c40b454081c0d1a07004010031018030305d8010085485421105080c400100e4169200c00d9880c40c1c1030002c00d81d80c0f4104001c003111042ca0300103008403850759581e172000308940b04040e181e142c41440088000380d142e004024202c024032001081c807000340c070100c01c02c030f41c2c5040d42c0d1101340d4030130081000064004160700300031142007441e030f010b0070005002003104540c0c081c00742c0440e55095000b141c104a21713a840400c03d94004d50031200503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 401535098 1250 401533848 401533877
    0xa0b1f0308180f09070906030504141903031a0d060911031219030504081603030b041e4d12042307050904080d05040f05120f19020a080301060f 63
    0x82c01811781d81000015aa908240056406601716541081c8034441107502490716403130030f0703040512501c0b02c5080706440305620810305603d805140070800004003040300e030848a00000f000e1600340302c0e004001d59101d01c180c005200700710882d0f1034080809816581d018440064100943c1d02c01c00c0304200d000741c41740c2035400240c828800c42e03101c1da6002c0c030301918003400340811030018400220704408140d220a8400d00507107841c0140b080258060107411002c1c01d01800710300542e540d900c0c01c060b0049400d0038007035065071a43c2c0d6175050540105218040d040088980d9003041d0022001d41c10480400615852038400b05140180725502903400114048c594942c008010300c0d80c8002c014203584600d40900c039a151003441030390094031a00c103c0d0325160b2220b0804c800d0301c1084600703684100304000400c1c10300505104800341c81d042d00403418036080140481000a004a1004841601c1d40ca00c90300c4005000b003025031800d54101c0a0716803690713582c100c0180303071007180790138400002c9008844541c2d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 401536348 1250 401535098 401535109
    0x30705150705070602130506041403190218130c12050607090303120e01023a090302061b270a0b0f190c0c030302010b0108090a0b1f0308180f 62
    0x1c021541c1c072249041e0701612400c0180d00203188550b819060380d9000186a940c144c000e00c01401c0d120741c101040b8034110704141c00c1c1898000e070401e00c2c0c00c188120000507619013141f00c6601b00b01180c020b0703560b103894890000c28403903071200926030190200003080d40820005140d12140c032030360890781c550351010002c40e298030842c80020040756906201e5119014190004007039404007000041c1010500004420000021a20603240e142d01c1e80003403501c01b1510080602a8003d1b010502c0180950b680c000e6507610001c16888000d030303d1030601401203131000202c400319941d00d6000011450021081080340200505503441a00d1407080010702c0c140e100d060300c00d0903450030250b41c2070100502e09042010450400a0100900405c081001031078000440d00514041d900019840140340c0001d8048003024080075a0f41c1c0c04581000c00240046c0c0100d42d0105080d080203486541140360b090642103e500300402e12200450240c402003400c482d400c2503d2012240381030005620000d012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 401537598 1250 401536348 401536351
    0x30518011b060c02031201090911060f0405040207060e0102130e0709030c031b0f0f031a13060b0613030302011e02030f0705070c050a0b0304110619111e03070515 71
    0x800108100301050200d07142d944003006011143c010791707251044640c0001e080c1c0d08260401042c4a40c4da403400d005109245250a15004c4240c2d04079182540340c10341854140110701c6030701d03c1140c0015007681000540d400103e0000c007500c00070342d202d07030920020490b03a907190702a201002010700d001400d420300c1045401c00b00e940008803202c80a045495a0620854501510307401d0a603644000a0701840c00034500002d20075002034010b02402d519060750382c4000c04907942302030440c6005100c94805645100000942d00040005181d20700c0c40c0400d00d18000c0582c406850440c2560001c01e040d019003251681410000d1304030708120341008580102d02080d0f0315207150680c1440099080307409071004103241e500452030b620505607a44006400100c0940011003090b01c040240002c01c8489100c086000204407a41030500c9044101c1d080c581544000000400800081c1c00c2c2c0902c8062140c45206616844188110500725445035605d6101c042d0840b100d10034100c2d1345110f5181d029035035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 401538848 1250 401537598 401537627
    0xa08150a06050913152301020102090f191a070203061e0402010c030210060311010305090f03030610030617010509160815061f030b030c0a0302090103030309080409050403051801 78
    0xb030800943e0800d00910014407040e155031315030350300540000308071100c4804000f4043e0100360b590f03d400801c85042143c1c0c0c1000a541560300610007116140e8078080034903203030401070b50321840d140b0180c070410700c46059940c0071480340d0050194424001524070020004140260111919616000303503c14001383e400c4044131403c48141d001c40c00541c4038035603000055000e071040700c141440c40c500319000c4400742d0f4001c452040c00c0981d52102940c250082650140105024140380c4400b40d1071561a840003e000500c52403045002003206130095020901805003d82d42e104140c4030110428000c000540e00c0704010f100b5400ea08600000c3c0d1202e40d025a1800702c00340034074400710140101030503c0a03004a03030180303192000a01c0e41c142010180e68200342d964000c2400d106005c185810701c041c0c000258090b155100c0c0510150729400d906d2b5046a41c54900041c000680d4249902e00c1d0246401c0220701c54244000d000178036521a02500c030a804044d00c691003480b41c040155280117403800c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 401540098 1250 401538848 401538857
    0x61a040509060604031709120c010903030509030118050a0314041401031d060a0504020a1509050904060207020901120c090506031902130c050408010e0105060d20060a08150a06 77
    0x80c01103041040040d504440d0283c00d860510381c980d078543c0e96118003201d540c032100d10302082c01d200c14584804043d800e00d503240d014101044c514000285405010302015007030101c00180742e0090b480951044030070b01c400996180030003c0900c0d00c07540314506804241c0000f856030b00c0c030b120f45840b071408031402c40e0311070050300012842040054000d0f003e0740000c0c0c0c039560308942c85030200380014840d20b8803400240b840000c01e03251902c10440c5030070064010850703051000403134035007154006280c2c9040c0c9208450898075545c540c60004060320810398000c1d040826a4000140d5654512050a44510800003581c5d00d50f22120380d8400c40e841100e006625500240c1d00842c1c801c0042000c0980c0c0e40040c0011502c403900d078020400740c40310075401c5000590001001c212021080c0300320ba022481040081c841d6003000e100182000c00484400b8005015940003040c4c030320a0111100740d0810094002038446150f810084d0044000320303824500c240e5000e00003006072038115440c03401da4540d030700d0303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 401541348 1250 401540098 401540107
    0x20f0d0309030c020d2402191404031a0106020105010b0f0910032022050109030803100f06030501060f020d020712110301021602031b0a05010c050c0d0501020d061a 72
    0x4084000e007001030019010301a642c0d0051001d82c40e000c034a00003050080342c180d016840c1a005115103003412a90403962a881400088920120b244480c401485940380810b6503031540303411140103105641c001440303408030420f40541034101c40103040c1221796980080285a0b41c410031400944a401d8050254010410400303d562510300005800d07201e5510300020030007141500b60b6800e140790340a1584558003c04c00307480c250700000220580d403140700c00400c14217103410000381c80c08030079010082c00c030800840003402d00c0d40c1c191800f000900124048044407550b50703030050700420080c025071002843e1040c102d64030500015900e81c2c01e40190b030003407510515102e544020160509001c841d1000d90021666103a60240041c101c00594a0301444865107984101841d180341003001c404100403001035520107986482c4e680080703030001e080041d0744aa03a8074000742800a00c20015501108034540c9406001c4150b0180c05079032003150003008051703258201007a1441c042000703666151410071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 401542598 1250 401541348 401541373
    0xe0307080c0907120b1005090f040e1902060f070c060e06030f0c030903090a0e011d0415020307051b0a1205120402060a0201090203060711060105010908150411030f0102030103060c020f 81
    0x10708090216000c0c0000a403001d402c00006c550701d01e014000000602c0100c1c4514840c42c0520b01d4444070074044808000403403540b52025140d06111034204646002045018299228074003203d2040102d211116580c090920300035241d05c0d524002c0c10000b80346a0b1003105542410b2044034000c1c000174810040503512401c42c00101d90000f011104180810312840d081d41d16000704d5100078180103210503885605140840d189203900700c203a005001500e00038400490300c128030308141200c0d142c80240c1e80350349112027034030076115100180014076080c18044108180c0440c4041e01c452041d001045001400031040b00d65014664120301484100c501140051500398001c04e40b03541c03540001304001d08242c00007030400b2400c4440c0e0010409640501c02980d4003806154050320090801450349070070306804558800114080840b0408200041070030b2247e13501c940300003a60b0007401c032135580c020116080c2c040c0d0030a1104a0b4507504040216440c18000f181814206039038000800000c11b042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 401543848 1250 401542598 401542607
    0x20301030c150512090c0411220b04122405060102010b06040614130e310305070b060a08010216020108060a050105070b18160509060d03051e1204030e0307080c0907 72
    0x5040c4060038490707540120903984035402544407000380a4480394070356092445d0280a00d021069844041101c080280642c40d140301c0bd40e810b58503e039528010480e018500b83c0c080d08108804920b8044008005100f60701d56a044544101400e900034003101e1551428000c650203203000302c83c085000c07040004170021320803000d00391f43e9070300b01e03001c11180d541e03101014507103001074980b5581c000054403458100c540710003281800d40122640b80d00d81110b076480c0280180120500146075000c2000450007945e500311018014002c10002195650302c02010f207600e181007800c0413800700b2515000603000389804180c0c0d030b0442d44180c581d185840150703510030020f41402410704d11030300410500c5641546040000d80c1d08004c90000540086007098104030f00303140700512117440f580c1d0013101a4000303540603007501d150b0100319000d454504001c0d9544030f881d0145100340300d4001d0707200c41004241a449a0500440300d0242d09a90b44591104403490f04c0d44891080c50b60030540010209820500c038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 401545098 1250 401543848 401543851
    0x19090203031801050f07050c0a0b03091009030309050d0306060e03150c3709080105090d031e1e0b03060103030507032d021e0a030909020915030109020301030c150512 73
    0x52501318a48490182201e20f99081040c059a076a4019114100c0e642003d1038080081d1244c00710003400c2d403400f0365155903194460b40d41096082d8a91301441c003058042d811110f480c030f9004003030b00c2c844103000900900a1806100d202d002500c2d92400300203074107002c20355800050040c10003607d566120280004d40da401513101e5100c0c1c104880f031107031400b4012580c2130303da8080c40810f0103200501110081c4803032500d4100148503450300007401100c8100190906082880d4200841c101003200701d041014000041e6400d1810f003044864519045c0c0d1485144698482c070008115600e8120f00f459510341c000d000040224a08208001c0401e009100720642c84008180c0c00c030f0344110101001c0c0c0302c0c841c0b5902482c0564002040d101c03014044411900c00321408800503e94142f07544c400400d80c044c0391042c007070050740c00100d8012544410609240313050a5100306542da503503541041000354000d200c1901c150155140103e640700c1c140e070720002001760035512107003481e00c08122003508410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 401546348 1250 401545098 401545147
    0x100506011b0809040f02120f06040608150907091509050604020706020a020a03020d0201110a03090507150f02010506010e010804080a0e0909070302041a012001061a031909020303 78
    0x310124210480012403581412807060a14603182d11800e000c0c4000e460444174003090507801404000c04143d0341d40a00340e482044400000e1154407024041030041415030401081e502940e2401e0110601400c071071801178234641c040351300039542e89800204035681c084c00385140c078420303900401c1202481d81000f904540c0041005281c007515581d4581240c3c0b005807000c0150300540e0035030041c55018002c1c03117083c82c02c2d0b000a00c0340c002c1d100103402d890300c50b00004005040d50b501c000700a03c42d0402480001d07040844802089d0303401c1c030304007805142d00541188010340c2000001285948216282611400107842c0e1440e107403207981d203110990b0490507254080090702080e404850740d4041e046c5010781110710141215a0550041c002a280302c01c00180c8040007080504d0b0f5640d0380000c0321001d02c01480c201400e410b5035040942e0161480350700c2900b28040c0c248a454180b03550800031406010300c504008100707050400e004e0f05481d41040017a6058200f808845504800804000744404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 401547598 1250 401546348 401546357
    0x120a02120a0228030806030109150c0c021e09101401030e0c0d0c0512070503030a0804170f030f160f180b070803010311090c1602010c02040212150f0310050601 70
    0x1c4900710300000c540b0609288891a40740d58003082c10b042d0040b01711600040c00b0340091180081c540c640c001200c040c0e141c81500d140d0b803070325900313545071060f0407001510307500420308669020844180c0318044100003d043c8603918180c007141404440309003200072030305061000e90344010448015802000c04001d003103014003401886107619960444c3d942c00301c501c200e41010840341414244648a006840ca04e035490340101400c0c481640c3c0041035410b40000c0b0b00d440341290b540da180010002032250080c0007040c10101c0c4000c095030f120360155228801d1140780c50071b581d0b0b807803024000c06000c0c1c4002c00d0202c1c03080450406494487c04860f44000d20003407590403401e030741c1c29031083c603540074007030907140fa01d000300060081005a01c100302c480e02c4115036104c401d060015068181c0c0c81619001500400c0d107280c04011039001e198403188144d00140115281d80c1c03244160100e4205c2102c42c00c0001e41d03480d040c2041c61503c8070b021146c441303020300100b170b8409a4031210002020050b0100f41800b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 401548848 1250 401547598 401547613
    0x31e31060c0305090706480305030a1a0918160801020d05280b01091710060501050c1b0a0f03240203011508070e12010e120a02120a02 59
    0x3a9030307018008036000d099800040c185880314500c0d0078408141c20480812000e200701007100718164058a002070101540f00c40340700c0040c20304c2c1020f0100349a1040d00c0300c00e44401a0305240d0440c001d140310311500700301405041c00c5100920040d0240d0702443e40d20111080120f00d83d40c00d9103001e00c0380d900c8a00100c0e04408400901035041d02642d50200c0b0703c0703130340024181500c0381c0c06020b420340000c028024807100c62035111000d00040003000c46501c0f03090340c4600f030110300d80c41822000c00a00000380c01a117100d442116054032240110300d801d503041d027000d000090a522030002c46d454802c01d02c01a0a0900c20741c03644034041000c080209601508402010400a5440c0000002544503841d40d01c3c0480507180740c1d040d03088580c3d038541d080c00e1060004000e03a0040b800314011194140c03814014a96807140c09444000c003031010540c1200d04022511042d840540c04905103840b01c104480000c11079000c0140309200b001001c90040c6c2042d05c01d0074085d40c0c002d018085400c03050060744d014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 401550098 1250 401548848 401548853
    0x703181a09190b040302040614030c01050f0906070c0e090c0312090406080d05190206010b160201050d050108070801110f0a0309030c06150501031d0c010f03020717031e31 75
    0x190040c2da0405540702800050400843c0f415126880003041b16010300810418030700002501c60034801c6030503062010006005400050180484110301002003909490f4845400c1564003200140145c0075040c001c400402c111180014600320030000080c0101210b54031081c6220864202025860304907407226404241d035a41403203504120f07185550b401d070b00d8615511566075031511043c500b1055411103001400303070f035544408459060354a12080c0300044c0503880100c800e0711400d0980440140b82c48004108440003203614000c88000740000e200809880090710214401e80e003124410440800c140d22000780a81c018a0744503010f0300300a0080c5641d41c0b030351070540b80b000f1030640101a40074024422513030144600803c034109096480d00400110410503541c2070038030300d694144603012a10b203421502c69011600001c2e8085102903507003007810045401da800c251072407907990311a4483d95030f01c010040c849621a0011581d84201d0020700d0049800e0007003203014100ca9a15803107902c001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 401551348 1250 401550098 401550139
    0xb0d110604180510051c0b1b03280204050a050f0d0f120906080c22170106030506070e0303070303050a2c0606010f0e01030509070306110703181a09 65
    0x501c4080c0100441c0c01d20700000c00a0321100309401080c4640b02000c55000d05031030040c07074051047c0c0c0c050315281440d103420102e4400c11074040c1e59030722a61000800c0151080c043d4100c64008500250001c501c1011503464605074040d40c080c10350001c0c41e02408200600e400340c001044100b01a10f80c400d40c44560702e0380706000c00081c0c401c0e42e030000c9800481640d258003c7c002c1d001024a841c4ca03c1203401c0c26803200416100d80c04e44506014401c01040c0c1c031075180c14003030314010101c0f1048540101c559540e424041c209510094805001c2c41c00021840350246100300c09100340107028503c3c00c1c1e02c46c2c1c1e00f50010306000e8504a0f203036513202a101c04c01c01c0103c0c0d0ba000c000201c58110000180903080052030000010039640c10052628900141d064104440a030700c94000d09000c112592504820351030891035510103060710b030400e5112055620010010040342d4001e0340c51040b8207200015440c9260b00318410380f2101c0b4002030241c140114160701074810300354000e08a20a0600f80c50302840c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 401552598 1250 401551348 401551379
    0x40b04150b032d0a0b120f100f02070309060c082a01050601020109080d09030c0206031602071703040e0c070b0a05010801231501180603021b010b0d110604 68
    0x1480c0d640020a22401e407840384102150a0380e004000f2a070055181e04603d4103000140428081c107841d407040a460340d07a648180044805050104c6034410341220149644907041500700c50480d140ca0044140d04d010341c0202c0d44061f070580c480d00d0555181031000c8888081a600550b0001b40510010340807500c03452240c840c0040c200c03900f644181c07010203c03a003110fa000d011203056a250103050380000d28268180c0726600400030000404046c00e0074151031501c00081c0c02580003c1c00002c2106503400d041003101c00c3da16036401c443d405034030380041038020000c40c004580d07150710034803041110310f0001400f90381c00300000c2401c40c00c2c0100c603a42c103401060156044070071036444070b00501404109205030f80c110000c4440c0d08008010141030003400c2d01c00502640260304004804c20400d07401840b2a507001c03d0600700e25080c5641d1004024005e40044032007450850006004410340c040500400041c00d80040040100140d1990b40410850314101c5030b41d04403c0034400010040c64070304408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 401553848 1250 401552598 401552609
    0x3050a02120f0d0e10022a0402070b0a060305061b030109180602071214120112050a1a040b07030908180a090903080417070302120313060c02101103090c040b0415 71
    0xc00354915114100041840c800ba04417045511000000c0485d800d00da06e03020744218992100304201100c400440c010344600100070b001160300000f8410804a80d41c4110212809074040d500e03152900740c0b140c070a1188240407490038150503c0144200040e0f03038055421305c080d4900c0c110816003d40c0e58601640c00000c82500c080000d8003c84900d2034101c403c007048005600641c0e0714003045010816441941800b607070303001d034021030908400c1003801c200700c1f0803041c1c02c0300c29454000012900c07280300e50000c890466061041801207505140a40a6900a00d07400000a401c1030390541c0d0300814002d21078141a4030410109000400300e440b0b101d42545580699202d0000f843c060030020960a420313407405020304030420040020a5000c01c542038078801c1100c0d90382d640c2c1c80d040005055403005031005050700c1c0c5080500810103400164064500d14040310134000005225540103450104494040054000022140c201d14065001c05d00c0408002c100040103140c103070140f044100743e500035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 401555098 1250 401553848 401553857
    0xa03111603061517031e12091b010518011d1306080c030a0b01150302040305030d0e0c040504030f0f05040306061502100c0c0f0602090d0b0a0b03010603050a02120f0d 73
    0xea11000321000d0740741025201c04545201908401c0107110785e04e1148680603505920340da0880d024000704141142d150000da903011901500700591940c0e01c4400b02c0c003500d410302ca184000e020265008006a60040c1c041c0701d140b0340b1a5000c0f070015100c40c9610158580c00140c0e100b500005561244c3d2500c8078075083c00d0001070b2080c1454806450035418956080c487d40c0050120740000d40c1c600c4005056501000340700084000500c4150041d006a4000420900010602680302c200325070000301d010f1311050481e1124400d0906000440d01c0c296409800140c68150b0900c03224010b25216500c0b502501d040740c5005d580380c03100001c40f074181c2c00002d888411a4410b00341640e042184078402040454100102000824050f000c1011401e004114490440f4000d0900c5172aa0588211550180c80c81d02418007614081d200240100d0f42e42017080e01c2d02480840c60f090520031801078a91200082100344000d40070020000c21010800c0c003103124510070808051024013490191003005c0e1079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 401556348 1250 401555098 401555111
    0x1406160f02101d0d08030703020c21120a090f12050c0106093c11210f0c040b031f050a060c12030219140f0a0815010804050a0311160306 60
    0x3590148044102c4250b07114800e81d1301c0034030110344081d0480742c11200c0f9090040e60ba10405092a04080d02d0440c4141102d40040402080042c410000c1c40c001004900568541e559048940c00311410540043c024030032000c00400020500700045203003170420305043d400d00c3ca03040f01c1c03503007510310399009204e08541315a0b000a002071180780220050003548900000490441c14074030044000c0c45081015036100c003409070744aa0014122441c030103c20100b03403000d14010403010015070007a21720550744118032001414000304002910280d561242c1c010344ad48e204c80000c4001d0160180d651290380095000018071030b81d5405203200180030356140c52140402904102c3c0342084000c403030405040c01008080440707000380401403003502003410306105505c1c061070021281c1c02200d20102a04030001180c940c03c50b041700041d40324010b10704105880750a508011100c41c00f090f100246154450000c5200113401030007035003924502502101c00e607114400341440e00e0915907105485161366000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 401557598 1250 401556348 401556377
    0x603041e020424080f0d1d1c05010c1d0a06030902040b040e2103040209060d031202040810060909030e0d05100606051207090305060c070804080a0c050a1406160f0210 73
    0x1003041940300880580640d000406c030185c03a01c4440041020846100100d5a550b070303840101d40c04242070180040319000c8010b00c0d0240c02003010700202d00104070f41402027103a820074120280000721015100ea000035240c040284d01070074408604136030081d2507820154081e15548100c0d20038000c01802000840c940c250040041e00c00d500381403501502c10010040562560307840d0981065080d6035011403c204c0d818100e4140040094102200d8000940042c0140c0300099109034411101c100b0044141d07588400d800322280604020081000030480a4462901c0d210350503175140260143d401c0b04e011701101008583e0640c0220011901c0460485540090a540c0542c4041581041200607045494103a036403000100010444034001a004040146220650300140404001c6550940a52030015005072050048034052954000300040740c20350300700521288527001d00703200d1074090807070610380c90315114203000e03240d07445803140490040e102c0c2ca44002d4414a00c1e82e4001c03040b0a0003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 401558848 1250 401557598 401557603
    0xe0d051b100e0307030b1503061812031005120708031215030604200310050c0318030313080930070603061404020a020a0203060106021b0603041e02042408 68
    0x203501d40c0304201c0d0700e003034110309a1030000b0303a0300c20b480e004044101d503076a070511010001c0910407800c40d058007659090100200006907000c0004040c501a20708801e05001e001506002c12a0ba40ca988001d01c0c85c104018180301a0040040d035400080d81c0e501d80e259440c1d580307183d0103041800040101c00040004500e501079440c50b142d8801c40103405281400c3e124034400d0000c0e4901d040000d5130030309280382da5540400c00f621406000441c00d200c24074000b41c0303803ca9070304201e80c45254002080340c004122003000c07089038450b43d0303c0f503d240e0550a16417244060368000000c1c064004007403043e0504400030152403000d01c4140032101001e0303400002000d600303094095101005150501c1002d004a401061032000d59040903600140c40310441c8000301c0c6081e00c1c6031030103900b40c0540d00020a40c0c65002c101040e04c0b044107130000010b12070103024041984421100075201c81000b030541720489a082c10300c4c40c1d5440c0000d01c04038900700c980c2c101c07200001083c5400b000c49501d41d5820052160b09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 401560098 1250 401558848 401558869
    0xa0f050702030606090c04090c26160c02131407090515041208040f0e0403090e04120809070e0a06031407032a09020d02070201030506120d0e0d051b 65
    0x4514055080c8011980481c2e03a0360000780969206280450016044900074020713078009143c1c400040c070115000304809445c02c0000409886550030a0080d62610301100c003a4034080c2c0d0003200381b614010144101180c0c2054081002c980c40001d40070b80e00b45048290240c0c0b42d68030140316020700700b030070b1400d00070380841d8080d80080e0007000f21490102001c0328140c142c40c100c80c3c140e090182d41400f03a28044001d80b04030342041c1c2c280405150b01059001d000e4010501c200e100c0d40358420364540740d40c40c24103454005c4a006020000c2e118000c4240c41c442d00589070000c401e0800c862003e9110700b0310303081c0107101f25111460955a00d90400503c12042d00400040d084038019042e4181561203203800007511020b0500f14004500000000d102c64800c00002030008220854460314140d41000195001c00402c0e4002802c110200e0a9441c0040342c0150050802c0010448590082001c0c0c0d020f1108540044d80300802d0312481e03010400501000307004003503c40c000181d081c040c1c2c0030454041103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 401561348 1250 401560098 401560127
    0x3020d15050123100e04090c120501050403120e0705010302090418210305060f1207030c0605030a060603020315120c060301090608011b1d0a03020d0f0510090b04120908070305030a 79
    0x2403280c4e80e40c0e046030442501520b0381c00944012444071100c2c1440c2804c44c400c0d80c8481460b40000e1186802e0010640c42940075501c02e41ea682ea10440f8482020142e03103058001c800d280d00022400c03c80366009a0007040c12407001792020510080f281d0200dc048c1000c1c1e0030580d402c1d00811548455900c0d62454a00d82c6e1900d410100241d040c01c00c0440c0c00c05000124042c0240450080212412000c2054000070359100c80345c40f0342d03503884a100901da034200740e4014107010700b4154045081402030007503a11440c80d50001c03441109207241000540020221260b41c50302590440b2102c54560b14004c501030060104046041440e1010281c2129420462900c0c01087c0e1055181415400001c2c00c080c507070341e600700d08506030401d4000f4860086550000354401c00d1940c0e0b09040200310b210568602d8061000e95001084007485007040d10751604000f003070305440c40c0008000425a032064241340c241481c1080f1800c1e02c074202a4513000c17a13504145c80990000c1414414580c0c4507900550701030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 401562598 1250 401561348 401561359
    0x80d090603050a270219080115090b03060403080a020d020a0c02090108070303091208040f030609020f030607090545061c03030203090f0d03020705060f0c0403020d15050123 76
    0xf030854240988000343e203800c4c81e4254030340d00311032030942d5034001400301d0300d107101c0310107030035043d920030119000b8283c00030120072208101c400002c4110051145889504000e0040d20096440f41e5046030f6244c001000c0f41c441070760030b01040546601a10281160304002c2c0c98620698002c4c1c010800250300588c0450416440b50b9000d1000950000f132441c100c400000440140550354500103856014940100302c9504415a0010a12045410100c1100d00941da41406010034806141d1150011500c0f0004155403080c00c10060030101d4015420140c1d800084114880229080380c58000c0e205900c00d0050600c81803610407a5040006034200600711183d40c2c000c3c080902c145055180c16070081c060541c0400020b040705014404600003061010564666246a41c0050001e4000010076a650b10076000040c0d60801960300d9035010b52910b440039424141b6690070030142d501030640442c2e00c2ca00410510141080f20f0083c9406840d5406080f12041c1e40b001c4161020103601100c5031003503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 401563848 1250 401562598 401562611
    0xc080d031113150302090405100612060f0b1b12031b040e0c070f0510060617010f0b07150f060315050f010317071b060801060c0804150306080d090603050a 68
    0x600095000d00702c416600803c0d80508600c07400758000c1c02100e040603045030600342081140c8615500b00700958100d6210b0306034600482a101003258010b004500420300f00150500007009000d0291140080c5400c0310b1501c0080d0384200750501002c82041d0002a1006c000d0106240440010b0040c40e41300d21095030801d480c101d100803144501400d03043d4241c40c001416003d0000c1c524160002913003000803642c181c0b0429070550b000340f150f80710300c03000150030212341215001d2000702c040c1220030b1040705a1030903041140c6a44940c0c0329507421918004041400304e0441d140740901300f40c034007158000265144c035500305042003007010300d11a070740c180c42c000c1040741c2d140d403074040141929003040070708030b10000c0d0340001e2079240b203000409081e604090300c8411081e00340c5c0104000b42d070702c5c03030360313140082e982c2c1b120103440704050328000801c08a4240000d01031600808144614400c0034038001c04d5443e6125107141c18083ccc42c518150012b0f100e0392051010341d415000c3c9a40080c542c010030010b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 401565098 1250 401563848 401563867
    0x114030c0a03020708190c05010c020c030c060c0c12030405030d260601050c01110306030705100c0809031632030307020103020706020909071e05070803070804020406030c080d0311 79
    0x500c180d1031601c0c240365002c1202010310010105581c0c15081d140750000c41c070591341d0000b0300550400c0004a8aa40c20710641c20100c80c8046a401c14040e0050300410f1003181c144100800c540010454800520035010b11480940e6003480c10b82498400780d018565890a1109143c01d10700c030110100148000c100c1d204252403446260840c12602011140d009500c0b0a0012100c52003401c034004025801c0c014a9103103a003810008600030304040301240c40140d50b81c001c0c014598803440f11400451001e1140c1404680d0490040146080c01425101f840c015141c0316181a2140c1c0c001950422a03030b004550320811080301c0600c4c0d00c401710815000c0300302c2c40e03000030383d2032042180080c10141c010540c0303410480c498054a400600080241c070003894000c0c8001d286801c500a0031204030007194100c0c414a008208460b40b40703820040c5541342d0356078281c1c2079810403000f030001c036081542c4200010114800c2c101c001e020300507450260105095480d401404e44d500a0104c4000b03450400c0a00d4a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 401566348 1250 401565098 401565121
    0x308071d01050a020109080d1e1107080d0608070f0e09120d0b010210090f05060a0509070311011205010e07090f0e040f150f0603140105060a030803090708100605011403 74
    0x5655003441d00d00d07520400c4401c04c9024010010307004194413008544c584001701c10790800240d090403030082d4009980305840e0703c419a002d40c480c0483c80481084030307002180c01e680003411101742e84a008103038607946d030104910781640340c3e00070000100138010038856182c00d600c60b1900820580c0050942e101d03078822043c1107100d074010301410199070b0810380c0c5030380e4001d0105c07407082002c04d50100540d140c1410700180041290504a03828003407000041c1c5072203001e11131207000d00b007400000c1c60602c1c21543c6180c45c00c1048052a0f061000510903844811958061903005e0000f498030030501c0d00341951301400364030807900110f20f00103800781c083c00340e13070706180800748c0c020340003190080f4100c420700300360054050000c1e50f210864101084412000600e400000450784501130186180030f07102450750881f0000d890595001072580002c00c0892140405183c1240080003947d100680c0c840c4503519000c203a84410b01c031181c80344010003483d0303040b0382c50340c0202a010f8489440d520f1305140022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 401567598 1250 401566348 401566397
    0x705010506100c170c1608010c030e0d090e0709030203030a0315060f02101104030f0809030c0609130b0301020c10050f010602030c070b130b03010b18030304120f020d0209070804030807 81
    0x213604030310100713110844620802c0050186490030601c603400e40d45440c0c43c135010784200101c40020905020540703145074400524856030180c140e588074207a6040495021054002900f4081000416a00800560703007d00003080c2115240e1000103000103407095005000d0065030040c01403001c0d00118071001c58001c110107000c099800030016400c5202c441484180c000e40d040940509542d69441d000c0248482c000c2c107441804404481d407400001c02040014070903071003201d030820310340c83d00c030021203503141c2008451b20f80c010005070420000204c1c02d8a8100558543c0031340d95201c0041c00300d80c00c881c003001805468a031014529001201d81107e80c1d0b108584600704204800103410720b445850404041d001e0180b4000307460b030b2541e60f2021a04250007880118a030080d85240300c1c0100c0c500081201d00316012942c00c07001d61891a00c550901030182401039800c1b135088211440113980c4c4254040c81741d0000d40720510141802d090051041340b00500e00b40a0001030381f00860b4244190401c0f5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 401568848 1250 401567598 401567633
    0x20913090f1a011e060e010e0a05041803030b03010e072309071709010b0102060114011205040f050d020c031203061306090f1109090402010e0d05030705010506100c 72
    0xca5005801e2500d10a03020151001070709807040a803140500b0740c80c90300ca490490b901078502c021400883d4610b04c01e810410301c110804501000840d010f0795000d52081c4103103040080091135840d03682c60102d07044c0e40210800040003901c404c103100030140c05200323904000302c0940c02000f079296814005540c8420600840000d103140c80d00b0140e0f80c5242160803402c1000c06865402c0394249070401400805060b0044840c020104000402d100c205203c1d0489040701640240100d0b4a0715480384080d2841c280c1d4a0304018a5205c0d41c0711080703a82c01010700a501c20380701c0c1c603000391a034284a41080c0901c0308400031904000040100d55600282c40c20604091184940e56034507444000380040c440c140600301030500b4200c0006c3d280100e40d0251801000080b41441035800c12101d441080c07085c0b1107019406600d00c030105015511404034007550b03584c082c1c078069140180c1d84583d455900b1498084480369107410800526050160940c000700c1424104541001c8440e0796031640803e070482e84 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 401570098 1250 401568848 401568851
    0x213060201051e0907080f03070b0106050c0a06051902130503012004150309020d0c080c0d08030c09040b0603100303030b0f011704050705100905041d0706110a1212050901020913 78
    0xb044030300304c01780048002010b41e28110341e4200f145092130303034032504665019145504075030b00020f1070034003031801c461002001c0070107404250f90b82c0c0d841030700404028048040075010400310b84001c40c034500c0102000c0024040c2001c0e07141c1741800701820364901c0e804501c14108028207048400d003608080d0b40942d19039603410380007040103600480007807100d554069440210300301d0300e0082c400850011416a10382e04184c1d51078a075003074140300328045840ca004010a00c00c01c00105065100c801610b204000100007080c1180b0200006e04190019203240c00d1000b01348800708205a014070420303295003010794000044540c080c001a242d101c52899601e00004404001402c11405020000140000030520300303085030a410010010310581c001c55001e585000c2c2d41c1404081c2d02840092804640401054410304001c0126031032103c21000c00345900c00c031500e100000b100b5140b030844842a5540d4010b811840c0c0c0d0301e07082600d201400d000b00340d920401c00c0150940b190016424010101c080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 401571348 1250 401570098 401570101
    0xf030c090f0b060f0a0f0206220c150519020d050304110f040513060e06012106020708030f060f18060105160204060b03040309060915120b1002010213060201051e 71
    0x1200020b01103100280b903000000045040780c4100d004c0240c04c401c0c03002e940d4010101c15105040e41d45640944007000d41c5100030080c40e075003c11561644040314132400050341e095641e83da65981c80403034904010080b9101081288550510805141405007188001c1100ca00e039404007a20360b100180000d403a800100c4080040c0e80c80781c0e0b008070040540504104001d140400039a011444041003c49500b400d085180070b400c0c00c0050154181c84039001e228980c211107840f911030350200c003901210302e59000d00414020800d920302840c070030100c0c1080b00550380f07019410481d20074081d158061141d5250f00300042c5041074100d449511040c20b0a0050740c80214481c1041d903200b9609000f54002d04121000c1141660080a14080c511a0701c41100d503546411050740d40320040d000e40310700c0c400300a03441c8440500c2400c06a40b49a952000000ea80d002900411340600d0b80c0d0346a0342c0903039000141025003021040d8100014503080c402080f1604014018800b05210b113a44440000203000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 401572598 1250 401571348 401571371
    0x306020d02070f030f090b04030b010918051510050904120f0e030f0309010e060a050304080913180c0f081b031501090e061018051f030506040b010f030c09 68
    0x904440d405504a15042d5030b041c02c44ca40101001c070840f422400044150701c000809005180a031000d4950201d002c0103207a0a0a0023100106044803d5201c0d1110109a1b01d0110f0000d200c060349101910700302e88002e00e49281410314002071980b009005c0d03a90b040030040491440099402a6035062400050b066260201103c2001c00c0c14140e552500030b0050400c10264000003d245140080e2141880034401008000c15801210341043c08540b042001074002038940009200c209070080822032800307140ea80c0e0303e00b152460003230710084000400802052102c4180260001c1042d006030000b0282040c189940341c890315122003280c898220745180741c0c0d9034140548000c0f04004420002c11350783d504103a0b40503290041d0080301d64004c1c00e000c101004e0340680504282e814090359044200504014100180402083c2100c101d400b803039149010100c1c19586002903004100400d103d040c00e00b8030501c01e500690000c4400aa102002c2000612040c1d801c03041b2040b00c14006500462030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 401573848 1250 401572598 401572601
    0x3060515010c0303151503060812090604030f06140a020c010e07050f0d170307020706030b030c090c0c0a0803070e040b0d11060d020c01020403031706030a110607061d010e1203060a0306020d 83
    0x46d08001c0c20508441816420b4544c5548180211022802114400072070312034004d07003520921008a8204c4820002880031402d0000102c105038416100003400d54010303200c84a4045c82035408420300b940015180e2a03a44003402a81f080c00031181c090910f9601c0c01000481c4c0d00b021b034030300381d000c0c216a420759401d100903800d400c11203240c08402e0381d90364503100e08025180c1280d8006c10011a1074492400400e06000942219046001d00002c1d002e403903041e09a540c58000c10912045031144107258400101458081e500407003898943c040411220390812040d61300c45000d043c040c45130b00c0134440c00300c2e0010300803086507c02030303407601c1d9155201200c24020b48240e214140181d800058000304260b402024103244002441e0000e080f52140d40070503482c1c0d44030030f0028022540c4008044118a0100004e180c6503208200c00280d00031000c42c10510f404d00050080d60603550350b4000c00e4403a000340000441300c1d011842142c0f4514200b000a81d4401040c040034240340d5010440030b0b00654907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 401575098 1250 401573848 401573891
    0x512010b09040c03150207080a030905101401050a090e0703021c050d183204060509010f092d1a06070b09010c030e1507050f0c030403060515010c0303 66
    0x5400841a0b181600b040401c1072101c0c03008844e4205555046800c0301543c2c402d0300c81050348504c0307082c986281410b00320090f100064050750705000d030f0b084030511694030784107c0503003120700101c0e102258500400c005207100b8640c4101c58060a06d040555024030200d5454103803541103500200d1000d02e40312400c071681c143d40300240907100d0905c80c601e505030044441d1891400d61519040c09503158108913161968202c003d420214040545441a00c1c020001000c1040c003e80001201944c0301d0025100b404280d11a03030602031079100a0248405501454813220380a90302c03052070040c3c1d9148640340384500c15591290554624505010301100d00040001c980000e22507034031448242030503d032034001030302c051155628050440803868040e008040034000e00e80040d110550710303a0009010325500a04c0ca03000c004c0c040241d00305020074030021741047c0300c40c1e100458841d415440c21400f112806005212030980d00310030f118aa070380c02600170b50116454600811980038600b503040d0102e90307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 401576348 1250 401575098 401575121
    0xc0c03030103060b1e21030d0c03020903010609021c0207060f0204031103250b0f0d092f0616050a14030903010b2403070c05031605060703050907051201 67
    0x2c03e01256400c94441c814046400030030b00b01075070b02c0304080c0e810701040840d0400313202542000c010041d580651052800c0005032440c0550b03070700b119421a8600115203000c6580480c120308242800d00c1018082d0017a0b080462a100750b0003041400803a0b628405a4200d80001c1c190040004641104800758640f507401d6444070780324645031408084003040c00c1c0c081c0c0319809041c1d440d80f80010825a1080f289a00403800702e00380045c804c82170344078480c54081c4103c104214440000a40300d4481c24600030241900092101c3d6a0320300d01c0d82282890524003101b1a510382c4c02a640c0d00b04583c41c0c0800f0f2000170752045064070b041d07410314030101009400c01d59034101c80c6801c024080000d0216030005c4008020a015400801500c444244547d038942005508240b00e074044407002107070410031031309000c85558642d07560545150b2151640c1d201c43c00c1941d020800300320703080000c6900140da41c1002e0202d840d02c03145040d9108004d22415100e007034101c1c2d10b03940403038003076018000484 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 401577598 1250 401576348 401576353
    0x9060f04090f0c18061b05031e030106120b0907030903032309071706060f01200a0b06060307140f0702210d110c04150801020a03060f0603060605120c0c 67
    0x1c140401510061484295880110301c135035035800b80200d4501407610580e170168603983e031001d1000c4150258a01d0b000000ca80d5403204000846c5507104150035010302010300a0034030703940e40c1400d2006280c502c1d00000703003000d6401d01c6d028000b80ea481c551003e034000c0c81ca160004070700e191420200c01500c0c02601030010320202c070400c800050802c61400d403162944400300e8803c1075031403000300111515550b0300d64541c0c2003800810300a00d8144a0844000b80514000440c18042c0c0c2c0c030360703d1051030791040c44250b601411242c42000b40d90031000c1c0c1c0c0080304440f2035040d86000304014060b191800b0103129a20310009500013400940b0041d03642c1240c000e085041c802010300d0500e031200260b00c40d40444c502ca0002d0081e0900e1041c20200f8521a0100203000c00840e00814803028000c0c0c0720111001950444c80071681e0300091019203021700c11580e02059843c507141ca1100310a4082d086130382050300b0311500f4421036800c01c0482e0010103110012420603a5403181c4205c0300d014902c60300d0402d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 401578848 1250 401577598 401577611
    0x91e131a1f020a030f031b030623011407050703081611090c030a090309090e010f1a18070903080a021b060f12100306021b01060f031a070315290f09060f0409 69
    0x47c0d0740356001d035041d00c171204084d00d0b044a1564406281915100a0500040303442c09144001130038200075282144c8618200e4940c01c0e220b65606000b50000003402d41320460724000c040c180107500307400e100801c0060396010040d00304a001589948001803004248546a103c820300705840341810074014402900204110020051024064210446000c1300d003400c01c0c00082e8004170f0050303100c040d501e000302101c0c0c10300c60034400c1c908024001854482030202c8010700002007080c038801000d0321421507025003c0032640d80c19032184c02006402079801180240580074814080408448034019044258501961034580c240c003080d09a41000b441d4034008218107226000d080800088030b00075074000c0c081591034001b00303500d40c00a40f0001d0719181c0000400c00300041607400b007a410100c1480d0214009e80c5e00a110140c8000030761088040c00031021004440c118040b221880c84030352032140c1c510309a400d68558000380204041c0c148100000122035806040031030450307005180d02d600c01e0104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 401580098 1250 401578848 401578901
    0x210170f0c1902161502060108010e03041206020909010f030b160e040902191203081302060d050c3703050408040e0603030d05040503040e0c091e131a1f020a030f03 72
    0x685e400703a881000d0321868002184820040c0078100c04044c500005508040c580a900c218401c0e45a006950040d401c200100701915420460b03800303410071070070301240240355103400300000d04014800103400085242c4220030551100d10b40420300011600400c00140c0c1d4000550780303a103403141101e01c400692800098800d07680a0a80140340240c4590a45680e480101100d003408020002c1d4066803c03c10030b040c90003e5800b003904400a40c4095003860410003a078140340c1d651f000307100c000c41c02500795000b40e000c00c078041d403a007000300b071a043c8000e082994441719940078501501c800c01d01c8074800900c960f03d0805c191414804d5401050000b030a15013020f0f42c595005000b6550b982e02c84600244424010104480560034040c1c01d104506c00c0031031041d01120000141598010016080c42d110342409015000350b0000c80c048210103104000d0401c6504240310690f2203550b5801010b01c0720981c2c01060500889400d070800d030058680b40300080b4002d19021800d01400d4032040307402a00f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 401581348 1250 401580098 401580119
    0xc030309030315030303330405270706021c030b06070c030b1e060d0302030f130905060108040f110609030f0f012a0e06090a090c080f09030409090c030210170f0c190216 74
    0x444c03030030b00ad800d142c0049148080e0b02d60b1a64001c00e80968041c2d0103211001c880708016660781ea40324503000825001c4800000c01692043c1c6040e034034000141c1c024010b10000ba5181900300d402500e0000b2204030b400d080c0701d030044009211030f1081c11b507241c1250905000344121070f081d403600040c4647d03511801c11001e03c1403410303002da01c255901e40f40000308554007c0360068080c40e0005446102d01e03816075519061181c102d6030854006800707001c90401074030100008944020340788058aa01c80c441d01880d42150000da0005103410220302d0804143c02002844142d610300c41d10b806145c603441d03440401c04038840e580d43d042d040804540c002a00c08121b40c044000401107554205590b11030840301c4486a106844991480c3c01c10001008190b00d00c2d07003c40602d074803620101c0d03070144d0b594001900162030000da000100c0d414003e00300c0f45100c000d440a0788a100b200c440c14042c00c0071400e510041c00341a01070002e1513029940581007038020016000701c1400210784401d800d0701c0d1154042d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 401582598 1250 401581348 401581381
    0x60f0c0c0f0f0f050105070f060b0325030311060c0a110c0910140904080405010c03090305031b0709060803071e02030706020f0c03010522080c030309030315030303330405 75
    0x2846058103c40403031a58464401c407080c071074201c2c0c00000e6a81d500d440300d80042c08091049541442140c00d200100964050001141002c41440c020010710b1402c0191003200c00e40c41e44007070b5401941c100090381a01e00240c641010040c685004078288096280f868001100031843c0d211010400f00040711601e0000320f0b06031000c2e201c59510404081083c842c0c143c80c19140180320311400d000c107108552162503260382c458003d140c114070040c0d81e0f4484070305680c0700c03100032000c000c603509816111801c100b184800900044a04104c824944040c4540300e001e103010040482c0250440c511220105a02c111602034000301500ca1155071000040e69800d01c001d0160100d000320b208900c0c651406209071449854a0450807142544d9500b10400e903407a0844111000d0400b4003034032070542002c0010b03510505030000150b43d2070a01e400821124a01c0c0e10307481d8840e600400811160200440a4600a10500c0c01c806140082030248044402c0c03101c4c40707182c00900d82410480103050707424200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 401583848 1250 401582598 401582609
    0xe04170c1f0b0d120504050d060501060f11100c2d030b1c020402280206060306010b04060e01030b030c10180e040c0303110c04092901060f0c0c0f0f 65
    0x441e12501c51981003015920039910741070303001007240540d80110f42901d100030403282d05481c1c01880c007a103a8000510380c22840d40144d4680b0b550701e005100d00c0d50400800e4282d0b04c602c1c10141c411060300b16078240d0301d4042d803401940440d11540000e0100f4042c080641071011001580303283c800704c2030306945104800e1249400020304081d002142414000b48030400c0b1101000320000c40801038003440040d511405066407200c0b00e48909060008407141220920401c03139000c0c1040f401c000040502d000f0040c2c0200d5502ea20030131042014640020034003041c0d4900382070104524486100185c00c101c85401202d40200c2803241c03c2c99069031041d0494518006404040d0350584c0315007001d64050000c4400030403814891009001103400b440e80d13205013840a004680c0c070f0b2404400440c0c2070701d2003200f0480380c10744a0802c07404407615818910030100c820700008456503140c000000c001d035900d018008213020381c4005120520440b00e9016014003e0780100c07240080d620300030300c070110300c04c4d00c1070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 401585098 1250 401583848 401583883
    0xb0a0804060b090c1b030d0509030a02010b09191a1e0415050a03021c020a06050304030e01020606010207060f02030705032a030702061c0e0a060209010201060518010e04170c 76
    0x5a00d52911843d664090b100c0d0064032802c1900d050340000301c4014090070000329210500001d0441c0b8420f016051082d100b02c009992158142e02003c0d007500d035100b04891280060900b000810000c0d8080d0b42e044074490540441c3d0410340d811a00000c180d40794519410514074100c040d81d110f0841201c44040d442900c04022082251142c0c8041030b2041c012503a01c1408200100094500b80700c8501d81e0090316002d41450614960000300c50310029031102e404160003008010900d5002844040007200a0024104030300d88400001d4903460240505024428000c03078829149200b001690701456200b0301b01e954404032007078019442c0c034500c0d01c052041e046480c910344d26440088161003104d80c1c044e210344d05158024540c07000c3d1511000c103584205a1315142d840d0201d40401c407019110b40208001666844000002400c0d10030541140b80282c49140b40c007094448207015040c1103400719840e5495644a9240c401001156080d40350004080071800360303c0404007081040da5001c04406 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 401586348 1250 401585098 401585111
    0x812040f20120a05101e0f0506010e06120103141e0705031c0f0e12150f100e0103060504030509030715081005010804020d1509061b05040b031f0b0a080406 68
    0x4a1565840c506400180310b50024113501c0d03145c16140d004146c0810442000c0781540c0340403401c02040310300e2a030866403181c4d12034060000d80e58020409082000081c5d640a00d884c03d48186030030080c5040c400107040703120008440003560828081c1160180d100c81c28030861189000c0b1a9503a041d030b600500b8400c2c014200f80c080040440c82003d0500351154a80e00502c5569400c15904524110b0400f03410105090a440d0b0280c01840720b540e0f406180b00c844003203070400d030040010744003004010701031241450205002044000340e2060440341d0024012800c3d03516450101d40c18001c0c0d01c0229018425400d002ca4400c02c10424030142c00c08560710b81e100707507550070802c0000d240346205240c04224a40003107400750034010784070700001d80030f50680350030b03080b51210581c2103c01d808000d403440d503034a180205040030030001880b189011031400600303060411491100758130014050740ba2000300903038031a40f07104602c002403000f4011401c0705134440700e603100060a200d00c201c1e0111116480d001c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 401587598 1250 401586348 401586379
    0x3070603020a09230d0308100504020a0c1502090904030801140306040f0327080a061802090f04140a110f0312040909140307050106060206010f030812040f20 69
    0x1081c0c0e90700d40c90581c0c1d0303d07000070320300a408000c4410040500c216076042d80e100003201c2e140e040404d001c4078070070395031a0b2040c6000ba049141510310303500310354811401085004100356124810b404500c1d0070411142101c8001c1c441e140091140e1000e61b900b1428000420040c16001079055040b2609080c031102d000c8200020140c82c2c03542114000d00ca8245c0d40d0181010901c186042a0090f42030581d180c0700d4032400c182c0540c5005554850f9007070b54410645402004401d01034445003000618444001c50300e580d000540c0e0b08001410041140048000603082c4190044481544501e20003555001040c60410340345080e10340c0201d44c050010102841d03c40d050010700e04c5240e841c101c502d641070508050081d409440022015616404010039600200c903084c4010f0111900c240000900907107002e13001b0741801c40503405040c0e119180d103000c102040400c402c0b078502040099800d00103650301e00d802800d007560f06402800100b6010340e211800c3c003c1070340403003803002c00300c654140e601c0a98 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 401588848 1250 401587598 401587601
    0x170c0106090603140d0c0c0b0d0222050f0618060f0d060612050105030f060c09010507020301050c03040c21060c140d090519051515060307030203010e01140f01080601020102041a070203070603 84
    0x4010041c01e40387c3da042c0030442c010404003c3d2a9801d42603001500d41503071810005407811144145090104c24003100700043d2900014445460400755180c504040100d01005008060400b440f8014100060800d010018500444110090f25242000038988a407001000f890324840003d01d5240380c0000440c56140004200d0350042c4224010801039039800d1105417180c002400780d070b051100503c1400c006903400e0003514070465001502903220b103041d0628840222159001c0f800360b0f05c00e00141e100c0190b0302c8081601c03464101c40c02142c2030840341c0007114021802d282c00d000e03454000c41d0407007078140c040c0c10003984d21b40243d003203411006072650762041000d81400b0003005070340071500300452450301601360782d409061801507111440088011460325403084801100103603000005200000507000302e03901400c100300303112022101d4440480c1504c515071036101e05000e038400004a55038401d40484015100c25082810407840401d0841000d4000c030804a12a00a1080214096109 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 401590098 1250 401588848 401588867
    0x60708011205060403180906060c1104020a141303061e1a01020c010806120a031107060c0308070305190c210b0d020607060e160e070804170c0106090603140d 69
    0x801e01520554559940c00c0c0d444190f48801d1601c083c6c0c881200203640b0782c5920070b1100900842e00d07152264551446c08400441600700b015204a10511030442c1c2d0f03643c0241c2c0342402411031400b442d07440c002d8001e03500e4603001e00e40c00209034a0801d8a40510071100302d5442e1009030701008148561000320090001c907021502c001070041c0c0c0b002070601410362003459483c0e000704018101110518414403d942030901e08402500416040505580c815204000460040101e86001d880080c0140d4008140440150001041644580208034070400144240d030150030021800c001d91040100d0107070440911507003a00c0a03120f58088504084c04030b0069010079100205410b240c52500e80c200840303604030500c140c40650b503485501c58510f01c00c000180c40017420502c40c110107480e00f90190383d4024010f0194041010003428000081c1403608900314003c0c07080398681c1c6411311300b6240b40c010071300d40d48005495070600c1800020301000540c80d007205403582c01941e01c0356041150a0350714220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 401591348 1250 401590098 401590103
    0x11b0f02010519020a0507050106060302040f0e060913051504120f0e0a03061806020406050301050f0f150c01110418050105270a092307091406090603031b0607080112 73
    0xf0150b000050540301c1e5004210810450500504280d02c03900c9050840799a90407000100e540003406010001c640c60010009000d00314070020b9500d4103002042c9002d001908520300c0215541c40c182c01c1040500c10500e00d210151019101ca1909c0d0420203031240c041414800415070300b0302034048443c400d80d02c540c1c080401034010090b0506d55603d800c01001092408030381c001503000701300000390071707400200020580b07950f48503169410300c8108407084a401070030610580047c0d8401c0ca480d02c80e0a03069240c1a4100407140d00c0c0c0e01e99680507070250001c40011010303150006004540c40007507401c10b182d0b00560010070005e40c0c2c0c07560140700300c046d48903000410200944076811042408001140c2c4d008071410004100070102d642e4905c050080000390440041c46642171a182c3c41e01040510b0007003a09079814450684d034a03600c08460500904628042e190039400a40c003130700d0030800c40b28103e540400001e1400d0913801c000d602d81344203440e0680041e484000001d48500d0462420302c3c4281c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 401592598 1250 401591348 401591371
    0xe010c020715171317041d040c1503050a06050301060803030c0a0302090904080a081b09060708040e0f07031b1d0a030804120b0c04140909030c011b0f020105 69
    0x1400c00c0c000850300b50344a0003020800020156801071105840c4003e40074180c00c4000308281d02c4e181c81c12800001c40c0b04010705440c00d0921003005040c814202003010325010181001680c1c840303040c04c0200384115040700840420200780c0d2013a42d0f606a2005200b0018000c08100542d2250200750a8440031b00c201030b801e91081c40411380901c00e0740000d11091406050051403e104200860202601140d040d240d4a1000c11109581c580149029070702516515080300d03050090007600380140110082e1500504011500d541045002d1049402600c08101c40300d080380382c00504d4800c1d00c0700031070391140060f0900041d1040c001e08100355001a0045841c2d11200d0f8128181e40d0310351940c003d00f001d50040c200400000494140300c024800b4002030340c0405246009418080f51000c00540441d840900030001000f05403500d01841d1005070b41125142c0c10354071010030480c074600564280c15429480d1520f41d40c124004021a260421030701d8030303030000c0c0342800070303059088400c01c8540c0748810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 401593848 1250 401592598 401592613
    0xf041404110403021e0301090c1716090c020c04090b0115050702010203070209041a070305090d02031305091e1e0718060e030717030c0601050a03150c05210601030e010c02 75
    0x10b01d08403d2074168005c01c0c3c9502c3d4580d5240324006404d44035607000036940c111034100b062040171140410045510b1515005140541074041c0d882d503000c07c0c503c1480c9440f07540d000f440005610038003c4200f82c140082003800021400d0900d401080428810101c54080d911000000c60740135401345d525a680580145080c01d01540920800003001442111032003490242d520220b00b6902085000e04050b41e4001694540039045d1881c0c186010701d440c080d98014000c29444041e030700d0b603c9050f9001034813086042e842e0b07108039108031000300b480900d0b5801d0702d60810419040c100c016001d0410301c020300000369243c001080d076440d56205800407885410640c18403c2c1405075a049140c000082c0031600c003e540e650b010003000480c3c1c00001c107150000511031107070010401503e40541011038880440358034654036003501c803141011003c07000e0344540d103812032030b40940c00781d035101180c402d2040c800c2e1190041c43e19200804840310781c08280303400b03410041c242052203001e400801580041040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 401595098 1250 401593848 401593853
    0x18030a0503160606030b0901090506090a05061605120c0a0f0503130b071b0f051e030d0e0a0c060302070303050106090b0904020904181211032503020a02060f041404110403 75
    0x2d007040d1040640701a91924030010002e0501d0780018402c4000500005150245281c010f00702000a0001c051690003002103001180c00812031a410803181c45010214442030034065486000b0803801c0003003910540c04002c05e08400400503c1d80080c15615100808030b00c032000e413040d000503617603001d0b90b41880500c14005144010b00350381088690428840c41d070520001501c50045914080b41d04404400d503800804c441086030202c0400b440261084001c400b601032030b5603000301c00010302404e850310115030040784148505038060390000f0b406050f4a031643c00203000b80d4040d2804400183c0b810000040052143e13003801c040e0381981910030310b031581003c200000f030b4118100070759005a50b40030f180c02504502051050310303031007890020b50480c40d010000d020701503100a04c1d440768100f0441c211814082c1c80d00f0b400a021000406080342100d810b04900d480384101000f900000e00041d804081104000544111040c02c103c188806c4441c106101c2910b0800d060320300156800d1209000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 401596348 1250 401595098 401595127
    0x602070201090302060f04050901120b1306150e0403020607080408040b0904061701050103021008072f07080f071205030f0306011b080703262a0c0318030a0503 70
    0x295900524020814036181d800003200b50748484010601004001030030445810419565030060410398003a4001d00c00383d448504050741d009013216040700170b034120b42c420001c80b640001311941c10703007510344104d135284e044410702480c05450031381c05442100e00250720705204400c00740c40ba99010000a041500d00160190306801c001c1c4403591085c1c4407840881c0041c00b003c203030340c90b2480d240004200c0394914014042d00e942002c5000c03040044050401c00601e40041c5a42d440301c90120074101000c1c141c03961408509190703000c048141c0605400012441400a24101c2d8050741c9000c1c0c0b288142d43d01d504802400a80b00c000f0700680007405030306082c519850145070720a07418103011606503440c000340ca980080c00031040760b20160100305881070650120600d42e520000240495504a0070070042d08020800ae00354030980560041481004075003110840e1001088542c03076855040d807808194494012307059185440d40a5070403440c00340f80004012100d15004030155240084d003201c81c20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 401597598 1250 401596348 401596357
    0xd080f1303031a0d05150105180f040201030b0301181101050a120b120a082205030a06111605070302030c0a0b03010e0901061a0a090f050102071403010e06040b091203070c0602 77
    0x12035903c40e1007010b04860311402c0a510000e8440c101424581c0c81c0d0700c0d1002d22540c5c040e0800750041d28050781401c041080c40b4056500130310b5403807496889617141c0c80100c000d8080071223040d415508040410988a1341c00000d07400d903e1065000b0f039000150303c1c004440c01c1c01030045440004070300f082d0380f1221000342d0340040d03d00317000900311025a06052103050710b4801c02640c01c80e000030000503d8013010a040018a1030658040001020307640340c940043c0d5180421240a0401c903611034000f8003211080084410000100f08506094102030400340d403201241d2009074000d002d413001c11401480e03d00c000038255100e4010391fa045074281070a0520b03205004180b100c0941d82c0b50004240009640b80c00c8080d8440340d080180c0d51101080c3c0100f42806a40c4080340348194042d00348100ea8010646500b690020080c03240c1c4010f50b00e000a02514001411a4031350042c1024802801048248903225411080c1103c480d10000c089120051008507000700010301e210007440001440c580051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 401598848 1250 401597598 401597621
    0x10e120c03030a020717031303032615010206010519120507030c0b1c060501120c0c0b010303020a03080f04030f0c020103020d0f02090a050d0c14030f030c0d080f130303 74
    0x40e2091048600401c0c5160700141d07610300982c4c01414200621002c480314407404100400140d414101c0601d02c01400e048240402400c6c4a510303401d80c0d60f14501c00000488071541000d003144070303041c00507030800e40c007a50700c8856006004010020400d401c0c1442e00d1800c20030105941018a49060301c2c0b444640e010010882c2d00f806541000004101d89140f00c1e40500003202400d039844030780101403c0c0c050408403450452900f4030208002903038100e000c41010101c030003000701d603030031288204035200c02c02408020030084880e40003005041d800114a01e42d01d1090b10b803040d664403103442c0001b59080480e0700a00059061014800c1544108225222207206040150400c25881d00e0001944c0700312445012440c0d0106486c1d440c0c8ca080c052107001080d0076950010048050b4542d900f01c10024002c01c290f0320f84e01d012000a84d201008045003580307564090b01e4585404e0340b080790b1500c58000c0c9107400541e0301d4020464200a8103e01d5010306e20407020102c3c80d062954040d0701410750500d02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 401600098 1250 401598848 401598853
    0x20102030d0c080a051302011d0d17040603060f080616111506100903050622020a0303030c0914181801140f0703110304080c10090602120a0209010e12 66
    0x184001d4880b4000c1030156540da803101c80c0145400c2c0310580440740000c0c000820381710801d0f40c85e00543d800c00d150111400002400c0c03124558038401248030742d03408038802003260107403555003016400d42c28003034010707600a079806200141da18100403c004696000c1d000345030b041840401e200d426440304a02d4808610b0809115510060103180c1c00c0c00119003101303102da1603460821070795150184000000c2a890b0921985460954581558494008025107001842c03180081005055030500c0101c1580c000d1158843d140c43e454010045c00c9050018800315110800c003040ba514807003000981010b024100c9484001a800ba0650001010304100e881c0b2882008881c450ba00038001c02c000908070b405410801d0404032456407600000400c41340415140114464541000d0383c1280d0304281c020306c109444118041c40c1038242111032504807802441e0400000170040700c1c5d005450b64904640c002001d540d22007210f0000d910544440c2d80c0011040500c10b10113161054403210400201c2c000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 401601348 1250 401600098 401600107
    0x408040603050a060b030906072c1c06050405032d0f070f1403040329010b1c0f0e010e0106050307170304090f1515120c1e030606110114040f02010203 66
    0x1c104680e8400c0c0c7d011110742c2c00c60020483e607103070800b0150801c882c400181600000c030280d550602c2c4000440c406201e000031423540c0c0e4180c05202800104a07401c82000c22041c1050319080e9a6607010001e03107400c0c419005a0107a0a05c54410b190110003090104680340c000d807045010840d0b404200201e400d003602c01281d44c080303071048281d81c10940d9584000c40c0d5903425030070144120f403040c0718030702e207040c80030890702d0564210368004a0444000d0000540c80d40302e080b0315403500d5040025806c4040e8070740783e0f41141d01350b10b0780c001d8100f200c034900007001000d034540d81060981d4884d014854060340708000801a9000301040190380c103075030100396400c050704c0d9909001a42ea600100e031451a8417410182070a240100c00c440060a40340342e400201e501061015000150214800074103968582c1b8000750140a00c0b01902c4e1040100210300740540048800303001020340b8051000001c00c90880301070210300c148103559040e40d00d004070101c02e80d43e07030340c035211242c0a114040f411070000b0310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 401602598 1250 401601348 401601359
    0x304120b0c0c150106030f1b0e12030c0a110d030e0906060702182d01051017090f100b0a03110117130506060d02010c0204090c1503020714060408040603050a06 70
    0x8152180b121403c8031601c41d0b07500d8044014140d0b805041c0e80068545010060281c101560510074411403d905010046062400000706080c080f034414510300e0100082070507040300d001c00c0c4a4403042c0f081c80e946441494603c180803505240303203801008590540f48220040c070300503502c01da02c028010541d62174030f00560301049003241a2942d10800001c3e910500c201e51924a44000040c0d00c00c0e40340d500c910007000e1440c00500c4062040c0740c050340101e41802034040c89440e480c800022154039230011801c26442040d600c503040100a0440e0058034071036415184c05010303003a4203400044c80c00381c000c1d00310b0700c1e0b0384816140c03215402e052051000040d06006000d984061160b522086905601c0d11503041060414600401a510030a2951000740041c1e800544508040b40c044d5400125200145000c1040f00007540020441545c0c60015140d81075146e001020003d100b0171451810000f921341c0c1030f643c0c0605840c000c003214014030050002c984650f0007290b10003c1e03140042a041c0d95134 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 401603848 1250 401602598 401602603
    0x2090a23013203180a02011205130b0f0916080705091312020303100801020a090b180918161d040c09060b180a3204020313140304120b0c0c 61
    0x480180303a0002c4200000c02d84994400c01c5104185809480d4203109540002c03c4452140e903042c1074182e0f40e101194490ad00d401d255207210340d1001038010b1a00305100000c501d0103080754000980e200b40d0b54030f200d40d0054a0318000c11100602d0003065a2803c02c07080010340e040040644001840d03032442c00d004070711035180e256020301e2160041c541d03d04024910340050038860b041a8030603030041051480044d80312001908a4490084d5103844540e116201003030302e950317200d80c0341d4000002c0050200d8005d044007503032103044950007207036403500c6504d542045900081c40340e8960212400d5520860213070300b20409501511132200700b00080e844e0f03045141110701941181c81514004901c0014445200c0301d18044e03030100b280e41c1c0010a10b07183c495070ae040340a40c1c44000c0707041c01c1c0c241c003000400520f00240204800400030f40d01d038178111402a40349920040305680c690240080c00c0c5410302e001c0300701c034182c0c0c003044220301c20500251640004c0d00800740900a0428081101040c0e5090070f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 401605098 1250 401603848 401603927
    0x1536150e0616020a0b07150b031608030405041d060a09020303130b0a030f050f06040c0306031e05240a02160209070c2109050d110a080102090a2301 65
    0xb2036080042580950050000212030794000480300300040002c4404120803040741d208602c141000030074030280080229080080c85000e500008864200100310488088040d005491302a40d080000300c01805003400442110305100c80c1c1c50f0400e001081d502c40d103d4201c1106980003030304032464a407005050618840d0307140e2190030340441c0443c1e488002540b60265403802d003444902840303e810184803080402001130030540c8616074031020300c42d02d14001c0d08050001d54002c401100b4580401d11005099401c240046a00c2d00619852240522213080a05501c0714292003007011075032400e0343c10000b075000202d03d5100c1d41c2c2c41110000166124031400d0f01c103540e150b0f02c4440d003490038500991048071400d00c118101a14120f00066264048610011101c007190100218040e500f000e0301d0b490070400074581c10260b011804915600150010000104245c80100348107581352082c05d4080c00203c11880d0340ea28900d0b13414101c0d0300c03517007512801144071040c03400b4131002c168014101c6840c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 401606348 1250 401605098 401605117
    0x203040f080f0a0806040b0117100906090b0a050405040c060e04020909070c14010b010c151116030e03070308070b270f0f0309090f0703061536150e06 66
    0x240001c201070b02030340c4078051030382114090758144a101849400a44107080c400c1d10040c000501c14001a03d006d0030b045140014050b011080060a44400310dd074003500e410080f00780649900c0000040e0b80c102403164511468001900b0291b96090003411070310303c03601c0c0c003000b0381c025000c0c0240300c4070741c1d070b02c070340040c003ca00c50307100c16000743c0c90307450680c154030030740c58803400140d14004902c402d690304900107081c140e6101c401000102040e02c0610010305044003060316040010454243e2203a8264001c0740e13650080c0c84009461504208150340c5048501004003001030500107440062a5481e0550b000603401001d580d54000c216000c1815452a40042c445548055581645400c0c144500381c0d042e0b40301d0025618100c5114080307a140c1c3c901420701c4803120f084100042c11103101c0d500c510302402d15a5810041051091001007400c902c0d0500001d24100702c1c02c425242d129000700e0702d40007441c1c040d6402c038500e140c40040207941141d481c5200c280000080c3c00140c40e59400c0051601e420b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 401607598 1250 401606348 401606377
    0x11409040f02120a06081c021614010207080705060714030705011103161407023706030c0f0f080613090609030305010b0c06060411041d0a0f1a040203040f08 69
    0xd03108000c44080a01500131460540307060024130010401183c0c1c80f080b0b82411218008110030060300702d16240ca00b03008580c80030f8a8807400304145042881050030014240e084808040d00c42402070385801180c03049680c000c50070090080002c156030303100d419404030001a40e003400c6058656509460b06160156401c4070300108110000c01402031503600e2060f289407516455040f10806c80141c420800007034850041c0c21020541c03080d8500e00c03603e485440c890a001039900d04200480c982d119802070102080c18000140709652160319a04090b81c419900c1614070b0081060582e40a000074028540000919030900e261110078044c40702d4413841004000791030307c1181002011194103800c490030301c0e0400c0101441c82540081d0003504000100c5000840c02050354424400d44550344c0f103002d1008050707d07103592a11000718000d00c150f140070800c0c0403a00f55045103401b1100001c140a01404003042810310780d080a03400f9661042c401c0c0b00d080e42d0003017580c8519990303804c40707e0750a1622 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 401608848 1250 401607598 401607607
    0xc0b030708010f12110f0d02061207031404030c150e010204170c060901090905071e030507140301060507060b0312070c03060f1401030209060f04051302032a011409040f02 75
    0x201040903000d401000d540c1d000700f401810030303905c8a11120f440300c070052140544841542403030b600d0051542c00c250340105100da40e000c100388c282d079950200301c8808021a140c51103218a04007030f903107010b1141e98540c1d0744075045080e583c0c0d5032840701180180d0145055903100c824503000d000348010030180c14a60201400040500801440c0402402444c2d0152000b80210580b503600105400d090301c00700300c0301083c1d513500c1413001c0b40c0b0802c0328100e04808110150b2900d01c003542580c45503025565a0303642291f969600010303041544428071404001400800c05040030480381c3e4401034400328000c06482521803000c148000c0c980049a05440071602c1130310410400c10107109541145201290038000c140709650340000300201444045d005905031400100107030b41d0318110b0341400d00020410809414406109080c000401d40106d00902c18804007000b09040400301308243d10920828584080c800001107503690080070f44900b42940600c00e402c40c80d9250302074500c00300c81d18000103854 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 401610098 1250 401608848 401608859
    0xa06020a060608010e070b0c0c030d0507020906040605210a15051e061e04140f010f12020a060309050307060218010e18040809150f0918070c0f0c0b03070801 69
    0x102e80b41640f00101036071600c04204440362000c94420211a4444102030720348081c00c04840c28219400b105981c580101024800aa50040042c040440c02610110a1959202d06100c100c441c540119a8000800041d0300c401c2c0390300490a0010a0990040d10800c0305240e4a41c08682c0d5040c8194056503103410402c03500100c100341c1000038811058020056080441c04039002455008580b14000313008490600315032140d40004900c800040f84508039031601844040703282c0028041d148100004190020b203400c00c0c0300c80c600340d480c2c008041c455041d2902c1019130080c0440030003128103020038081d0390041059440909240750348807645400100c5414001000c500030f242410784a2101d01e01e000c0d0103c0d44955406074419400320750107070388184180000d52042e1038200200c00740500010000c201001e070344042e14906505890008400030148040308104030219076034400a00200d03103c8002c0342104c41104c20160148500c811515260f902c070703002590003203484902040805004020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 401611348 1250 401610098 401610101
    0xc0f041a0a031404111e091e0109020403080405061e0a180611030307111011120714030c2206031e061d090c0406080d030e010506010c1209050a06020a06 67
    0x1040100d40601029480d142e45e41c0d40b04102d050304004d0050101119880700401c0500540b000000020840d103500c0c0390204008440340582c804480c4000c2403840001511034250003501c00b520703800b0420904140c1400c0038018981c202100004070234012a9110761341e1036285004203051003055444003606071500d06503110120305640408100001d24942140302c29000c8203a942010080c070308600110840b400d4140340610205001c100741d0319040c2130036403050f000001071030044001e0811070b010340e403514010381e02d542c050316004181403010000128410300040003001880c4144004a02c4101400c1d402c0d0051b056581044c400b01e0360f80d500c0110b0807426030380d1003c0000e0001d441444010304104048802001520000103406174000100e103100c08240032803c3c1014016004116031355403850785940e200401017140022034035140c40e502100d1018010130344070307001c1a10f800c0b110071059914208a400b80700c010700108540080701086a0383d80181c41e00007000540e005081071034083c04d0050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 401612598 1250 401611348 401611361
    0xf290105090106080406020d060302031e070b03060114030c070804031a180c0d0507050303131a12190905010608010f0e010912321308150c0f041a0a03 66
    0x1442040480010011141d03c403070344540c0141c1c0111b0142c1c41d140f00800b22006000c0580000b1340c58002c010031120303940c80321200c200c030301003080381102d00c03444d41d42c08080c2035840251045800135140101403001c030740341c2c40019900198850503062601101d0344610702c2a030000d030000c03501440c86410700d82810820300e100c5034008546006c41d0303001d0358018078919500c2c940403100340d004084400b100c07400c1c001c09100c10703002042c01500b5640d076903201c841200342d494080c2c000c0042105c046c0d841e2580001800095495040322600444015180d00d8140810340c0d08114040c01000d8690503803000260003030041c503000b007840c01c1c004101c110030201d0503000e488854081c410141c0c500507000d00401d2070440950501515130030582098007a0319128a445110580e03680701010018010f090880880f4008000082c00b41c0551640749846092442d25504040c03140c20b181014a0007195681910000070802c0c5801c4c035103528070b450740e512400700c5130340d0310501592103041c0f0204440c008181c1501800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 401613848 1250 401612598 401612609
    0xa03120516090e0604020405120703060c090303020303190e0f10110f0f070809030a051b040c0206191e0504060b0d03020a060c120e0f01290d0f2901 65
    0x6020300030841c01006070200d84920f03403031050708002064241c2c03515411140a4400039009560807420503401542d03900e0688001c5480714601a082403003a48a00a03c1c41543d505070301941c5940c80e800008a0000381e0503181052159480b4030250140004012100d80700c5640b2000d000aa1100300c6210103c8020005141002108003d19413180c00c0300320490f06010240400141c4841c1d050038a90918050070400079058400c2c10755020074001c0011340215100055901108e60070908000d000a0764045000000541d01c0100401d0047c03444411180700301c400c00c400003440048004c841c0c00441c014800082d04175607184180310a00015004220754110240d407610b43c1254240e4009545e4441000e02401c2255940d0b6584806403180c0807204060301c1c80c0c1e00a102d2074402c0c001c180c1e01c40c4490841c50b5007540ca45100382281c42020210012401e02035a14440300104910030300c50107002c503644c11a040e0302004200ba00007041c09103400142d2070076184080c0341d0341038030121071060003040c0c100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 401615098 1250 401613848 401613871
    0x702070504020c0304051903021203120a021801080910050c04050f030c0315070507050318090601082a040e09030403020a12080703030b04090204090b090706141207110a031205 77
    0xc3c0c100c48800104030303011a01d0540d182d0300c40d01400d80309102c8514058000940c000c4050900810789407001010703120400d4003460404403511207100943c120f00c180502516048000c03d03c0d86500e6001703015013079000301306e40145c80380c24144564107003c99104031840c58520a02090600c51750824000a4000403401d0380140296181800000e503642624411149480031b40c50001d141284070744180c510383ea61180489850780340c0d00d001303082e9407000c100e241d50240082d003001900645c440d8410300c0c010350090f80402c003490350303840031810740c10002e01d40b1200c90f2208101c002800c2c222250030620840d040d9010307503204c0e4114410080e0007a55584116101c0344c1a52880c408500c03071108452410707071316050009540820101041c00f410620300007962140c0b074141d0880c2440000c0c0d00301c1d032048002000781d40a00707440c0d4005a4101c0c0448030281000c0348203101040c12140b5007142607401402a060080100d80302c0c00382c051a007e4403a80c105c0001d696100084d11141082c052032b500b0084c6901c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 401616348 1250 401615098 401615107
    0x50f09010e0708101e0c02010b1305190b28030c0605071e0609080d0b01140406120504110d0c050103050c2502130c0e1509090411011412070207050402 66
    0x41c0207503201c2202d0806130200780d807100d02213070201ea10044a051020100f206004019004102038008c2588510703060280314081d8200c8400389c4184203041c4202d0340c86c00801003041106060a00500040d150039403c0004d03c20440300102c0b03202d12102041c19034290760320030a415880d241100100a500410910009110440000e000c821003206007158803042680b4051460402c0009004803040161100c00001040e803240c00e10742d00550500c500c280c907500c5181d45408000e0600d4811441503000189802012124840068210740c0d0864014421041d000b191140029000c410744c61040320b0700107102000304040d50f010300419a009071a03035002030030401c08481c00741e540601c0c110803500402108140e40115075840030740741c100542cac2710310400c545003d8500191840c401d5405042c41000440035800307084103050200c0c0d03940c0802518180182e200c1c1e949416600840a0180e81802404102c01e40e90144407000303045518030010004070740c0d00744107101a0500c0d1898020398002ca00400c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 401617598 1250 401616348 401616359
    0x13080c120a0c120c2c0903040f03060207082115030d090512210d0f05090c120a05062712191806030204170d090504090f0204050f09010e07 61
    0x202d08000c5400f00050348501800a26100500c40e005400c442d10550000d403018540d5140800148170b004640c64014600707444e500c00c80d035964001c612420f41c81340c00a003001d200180040c1c01900069200d0382019041c001c5102c01c407840b1882066002560905c0c80b4200803404031a007c80e035042d502c00350301801964085c0c03030380240000110300a19005045200340082520002c01c00c1803503860320110b1500810074520240ea06a600c41500a413089041480c4e100200c8214810f250080d048600142503460191082c00345011480001c00e00c140108609071010a00034481135105811210409402800001c58046002e80754616901d06911140800d01050185411200d80c1d0402141c5003000c429164030032201c3c01540c4002400000c601000000c000b80c043e0054001c0c3c4103034012072091240310344103050b910000d0312a01800106061b00c10401d50400390b01c034001c81401102d04108004881e0040380950311300b0394001c0b045c243c000c006c00c040301000f0300c81c4601040a04006d4a901e62a00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 401618705 1107 401617598 401617613
    0x1403160f18060b04050118030506010303030c110a2d0c0e010602060106110303040201030209041103040b041b0e0f06030c09090a050c010305070215070513080c120a 72
    0x40000d00100c403415000340c600f5100354102c801d040034038100045500c03032009510380004403e903000100c045013060041c580694082d0b1004945030390311220090540103202e8402c0140d4124468910000d8115084596030800550000d052164000c61714240c0103080d800c01810f00e07811403800074814140103401412501d56400303540103a80d8840042c2e070080d04180a82c0d1954001b00001401523000c0d40c094082c42e44007920010f00441c02c0a170319699580182c0303080e40d5a281404c0ac0008124003900340d0324014450700300850b0351a14207c8040b10015002e4122042801c912000440c1502c040003458442880280310303821038103000004076281c00780003a042d26513000c0e04149a00c4ca5009002e80e9000781c2c203950003070809202c080701441029101426000c100141000207081683c0b018070480060a81e80d00908442000c0070104011030021803941d90050b04001c1ea8200800c880 = true := by decide +kernel

theorem cover : BRFrame.Cov 401438848 401618705 := by
  have h0 := BRFrame.cov_init 401438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 401438848 ≤ n) (h2 : n < 401618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
