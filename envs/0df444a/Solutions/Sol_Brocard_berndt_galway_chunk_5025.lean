-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:29:57.618193+00:00
-- url     : https://prove2.me/submissions/dd3f661d-13ae-474c-a8c8-05b51e8445e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 903597122 ≤ n < 903776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 903598372 1250 903597122 903597143
    0xd02070503160b07170c0a02030f0f120a05100b0a020c10030c020f120a0305060114121b070b0103060c02010b1201060503061803030708040f0f030c140a0807020904 72
    0x30400c01c000802d0702d129001d03651050010541010200d03682c1c050008020010300c0c07041c1944d0818162500d07500440c0140384603545168040703050b442e601c40c3c84100394505d00d000c1080707042910341c90098081c07586040303110140382d40d4500120080324422a100d0007403010508003804442032038005010903125030b00480d000a00c2000000c0c07507003900c4400c1c020000c3d44031300c500e5480540c1800761080d80c02640300213061041200540b880d031405001084400c16640380000390403a8403e400f0300450b5810305020590311512041c3c043d100a1049541010040034402c9421034844160b085a1040790400300c01a1144d00b50350342d281c068095418840f0456481e00c40d150510343d035511404100c03094282c0005822441c00040c10301300280100103050489a50880e40704010002c800c413581b1201c1854101003503610352505201c9c04010030006010103640c1e030300d14410180c0100b00c03800780324081c1c03450103209240c0300120756580200180041074440140040001814040b0a942d00540302e120400c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 903599622 1250 903598372 903598387
    0xa0302090a0605040c09030f0605070c1509050610060c03112a100f3207080307080a0e0a080d060e040b07030e010c0e06070201030905030d0e070803030609010b0d02 72
    0x30903016003034801c4007240d036940c1420040c500e805d201d003110402c01c0b8140b00c1d03030843c038541710f20b0500340101d10054204c03600c6a0002d200284102d80f40c4103040e6001900c0040071000704c034410010003072005c00f2516445505e0200c2c0100c0300303d5a9441c01c9030703102c0c1e403900c0c0711005c542c0d800c036544980302c000c050682c0314241955101d20a00d050403000a043ca41c154040030b00304a040207699410b0f141d000090000d418041c2c002140e21001c0c428000150001d859020121081b0303005404400c0205566450382c003044c141c040008440c0218016215907407003a0030364460704260760840b52100754840c1680e116042000000d100c00c1c0c003400101010200c0041c007650707600c40c040076071032044500320b803001c80034010040126018032a07403107401224002003041200c1004080d2a0400d8a10740610500c0003045c500f086a01c644c1080c44083d5202081d84d071904020b5a01c0c801501080b811950b9074000c54001143c2c8040000070789100d000c00070101c008907481c090340008194003652044500a40800802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903600872 1250 903599622 903599629
    0x7022d011b0314060904030504051002030c01140115020c03030406181707061404051e030307120207060e220902030a060204030305040e090f25050406030c08150c0f090a0302 76
    0x7a0601035140840c0c1d4001c0c407074074415600340c0204881d119070001000d000200c0d60200a55081c0d810035a40700d1801c402c0002c00340c0c40c500036042e403d000d41d824424041030440410f20039074121203154801700c0c1000b070880410303601e13070082c88110368060307205003c2040740c9032007a000000614034541d00b0049050f110110304550810410041140368001c50741004404c1e8004c214140c10240c513400f0500301400d110000f12860546141d031003112042203091070032544d09008032900d40354006030503d03281c2282413029486000d14071540d00444d005500e04081ca0500002c1408100f42e44007442c09105090203202004102042c01aa003600c1050404d0002914501c02000030794001d40700d0340c1d1200c0c0303489031038442008003e200d0304507500011004d1007072201c00110f40c410741030f000c9210400981c5401078401e4020341580000da12a042c85400414400030006100c252000c40302616819030b81110300030943c08055030fa0b20000103007040b0310404080750b2800b500701c1c02401004c00c02016560b8000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 903602122 1250 903600872 903600911
    0x100c0e130501081c050a18050607050703050c01030b0108240d05031e190e2404080d05040320030703060c030209040c02210c0304050d120807022d01 65
    0x92a000e66400c010302c14100200505004a0603210340d04d07103607903401d041c01003007030146c2c04102c0f00703010b03610041c0340c0011034500c040c0000e414050b02d099100c030354038248140d40c0d9801c4c1c4002d072454000c04880a030307254881e020f800842c3c0c1040c0c480419a4a5004030000c00c14880c415403d5080d694014000c91a51009240b402440c05080215100c514240e020451801c03440b05080341100d04001d19500f00400b40c180b2950f0001c0c80c1041203080085201013811452415803034401e149000103402c0b081001d00f80504140c640600c112041403124071001d40c0d45100300d0001503c4032610604035080902c501019040401e0040d0039141201d5482d59500145d0342d4268021002c80d401160054003403c0c00d125203502c0d080c0510003000c1030203540c0203400c8449000010303001208000500d60203140d00c10030849000744000b8000000000340707418410611f01603024924009120301303000c144054400203c9400c10184c0f18000c00f8903182401a094101c806035030224125525103140e41e00280c00580d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 903603372 1250 903602122 903602149
    0x304080d051e1003020a21060e0304090605040b030606061b0a0b0105030d0f0f03020904021b032a0c121e1609150b07020d0803010605090a08060405100c0e 68
    0xc01591400d801002d40500032001005002e41c07240c0301c1c00800140ea50040c440b03080b00e80c4080c42c100e011580b0840001846080c401c090300160501d075071103410f014000003d10841c0da4098003005100e03100d0f010171003070702c40c074100f00740c1d040e4440302c08240e2503e44500200301103a203044603107034550035000c040d90504500350402d5032a654403400408c0181003e11032040c81e45003500c1c000d038408510310030281c03601ea10090480b042650118150b025503c8950460340842c15005800c0080c3c0364002d5020b580368014194030314074100c0030b5428422142c541018400325502d00f0042c200130911001844030b8103000761034111245c8114080c0f010000200030303a08100490400103022030380b182221168811019034049100c0500d0315a1340602c0c2c640c40b2215006640f1601c207401d80e100e0050001901e03900440f00090107400d00003000183d0305411400610034150155510711640d9a0307040d210740c54640896002d001500716004918500b19158410030404005080c00c160103106400030642200b103400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 903604622 1250 903603372 903603391
    0x2e09060209040608060603060a1814010e0c1503011e0302040c03050105040506030c0f0907180b070303060e0f04020108270a26070b07020106090c020d0f020102041a0304080d05 77
    0x500700441d0a01e402010068072040004040320300f03040011954a40740204001c4a0aa0b40c005000c6450742980d4940c4003141c000c000001c0d84800141c03d6802811405c400700c00d14850380317100030040d080c4001c0c903000d12801c420080b42147e181400720680401d100001d982400c50004020006a82c0c61088000c1503246580004056041c0020b0000b01c0b00b02921841c0b29911001003280c2d03903030f556103000703000c0304058408000946624109a58071a45040d941d03c1100f52644d01090390001c07070003d000854042d90702804001d50360300301c07008410026103038411f9000c100700001d005540540d215070341000c115080500410200550490181c80d1810490b840d0b4000700480414070820281440b011301410b601c241d845049250f85074911f2043d103c0c012b11340e400081c000303042d15000394400f02c010f108100d030030300019101d054000d465078814208130001c91509100095400e10500c00c4c0d505a0301d030411501d030000024441c1c6002c1303410090040310100c0c070410011800c10810301860303010f00e4849 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 903605872 1250 903604622 903604627
    0xf0d0e0301060f0909060b09100b0f3a090b07030515062704060e1b09090c071401060b030a020f07020a09050f090a0f0b04050118051b122e090602 64
    0xa1a01031b05a80c0c462040d80c3c4120100e07030601908012802e45082199100c5d815266904011178a104440c0a180040542c0d10300f00e803290a42c4c085840c4c1c503405c070b65542202e074440b680e5202c81844101d803100d1001501103a21800082c09a40c007a502560b00140b00680e18440b002e04000001c9080d40540c1c50511500700e4001005140d810b4030b50155000c02003100c050251905144000c129542c000b404004900c111788080d0203000040821509401000f80c030b40d181e2031030003503107280380c82d888414115500c4900f041d2407005d43c001803084501b5501800320307440c0745843d0210900080c1d0030402d40058200c004024100c016551481c442d801004058804211450160103049540030300415045107a004440d0390f40001d400b00060720002da41c0100c50310030940b1141001c40c0100f1003900883d2401491002031002e1140018185542a081c900481c1d0272061140034041201505d6031950101c0c2d0207070480c90f410444074880b2402d0810801200da10318074182040304292003041c43d060f03d8041c0d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 903607122 1250 903605872 903605891
    0xc020309101704020904020d060c050319140402010e030102040b2802190204020d0e0a060509070602010c0c1515060e0a090b010503042004090302030310080f0d0e0301060f09 76
    0x15814008180240c2c10070180450030340c2c4104400520040000b485083c104000030215510b00d01042900760b000101004900d9003000050500d901c29078100412112070003a1b60300b03001746400f0b9090080f03a0100d400445032102e90054900400d03030000581c1c1550240004144032020b10003810070024409c010081208900708400d44102560901c40c0440d00a031030b080c50302c140540501680103505650040c0c1c0c0d0050a2000d6000740040300c11032040d401a078901e101448407036009140a920300344240c584a5a0342c82099088441003031031880802c10307801d032000205d03088014084501e2940440400c11102d07000b02a454450030760401c4001c2040d0300c45507010750901a94000141440d00410000e120b9044e00203009400001e000030072018041c4910b854108044150a18a0002400501100d5100e140c060b4694204603840780c0c9502c055400001d0780940000c0e00c06101705040041d20304150540c000300da15000c0099000d41664035600c00294401c444000f0f5001040c2c0b001000442085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 903608372 1250 903607122 903607129
    0x19060203180a15301a01052502041506030213240315150c060c0f0903080c15070903051603171308060106170f060a15180b07030816051204020d060c020309 68
    0x181c2e5104181002000e1064003400e000e4680d000d140c4014001c0520f0b0803052301c3c030008000d4000241030b501010650301c80080c070f8031f4140c0c014040c88401d00c04c00104946c2c6a4204040610a20615110007010f080c4e102c4e086500a81c030104483c220048840c0380a51540c0d48120b055540c030520800046c010518503061000900c0345952420192402101486c80e41800512926080c0409080c4000008040340c2d030900c10401d4002d003c401c03142114051420f5003000e040404984002c2e00c03580108850382e10b0140c07009051005907940a550381a60f0641c4400786440341c1c00410b40c05045040600c0302280300003082140e02e00a0109a44800303c45203c102074448840000d000749011894507400d0045580d1800240070542d80311003107020142c202010103c902e00d201c1e2038100c00d00c001c556000320740105602e00410605001e41c5400a19449910080c29008030316010800000e8080c0300b10002034a078a5500c0c1c1c0c200d4001098500041c4690701c0782c20441d0000719107200540d2001403584401d04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 903609622 1250 903608372 903608411
    0x8240708010807030b180601090e011109091506070501050a051602151609121a0f130803060a0e0a0b0a05121b19060203180a1530 57
    0x5055103803261407945804022640c0d6803450100600f10501d25000910948510612145c03c1c90308508480c4c59507503485020004001590b40d81c0c146500f0f025012144101c0c07141252641d280140642405507160545c02003042544901550302050400c6910b0200c0c80034040d20b070203008119000101410051030b10320026040ba4022810354000917003000001c1d540c0754000d5030006c1c00001e580b03080071071208101d406006507041903c0103000c000b108001d11160908685403141d240e200b8018503128446c80403000901140c0c00c8115072406151000000e0020740610381000c801b0348001540c1c2d07222449046251012039000314065910300150703101c0d01d80f00501500a1200740c654080701041030202c240c440040e90454803946031030440200441d1501c0c0f540c24441540b1300c178038108003030302e0f41c0d002500c990084104d0102c40781070f030514482514104120300c040311005002c4203802e00303d98001b85e41d4490040c1c004d0210219003d40043c0b014160341c9802d00c0000302207400112403282025681d13000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 903610872 1250 903609622 903609631
    0xd02070e240108061c0b0412080c040902070f151b11190c030c180606031b030c0917030a08150102030301031704050a0e0603011a0105160305040824 65
    0x445100c0110300c89001c0c0051501101072003840c0441e01580e5a0010900354002e040040300050780202c401014042d01441c494051849100c40004075228944100c4e0051b8007034074182c1d000441003108200b245441d5005081c00c510521040e10b0500701511444513180c040f4200e11041501d4032070071000d5003940044000710702494144645d000340d4501c081c503030b90310212003d03440780c51030718100206010703017040303200d0085610501c0010055140c41c0e1400e044c44104140075100d5050a0f400b16209010340590103030800c007428008006c1c0d20f088011000b0b0425001640107210104802081c5601100082003000d182c0c0340045540d294081001000d130f102c02402d0340e001815a5080c1d601503a800300840e0704494011180780004203002e0b200000500c01c83e071103960310110a0500244801c00c4001c0b0f03620807a011402004200203810542d041c10f16182d00c5107002640800a00d0103e10309c410340c01103154000e01e0880d042c00d8581004524001048041030034444240c40c0c4490144440356005074807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 903612122 1250 903610872 903610891
    0x70c06152c220602040e1e10030803040b1e01091d0118060c0215090c010f0e030a08130503190c060c0512030601110607030e0c1009090507030e0d02070e 67
    0x601e881c050781251803400e40381d042c540024180100c0203000c0b4640640d000784c00c4040e030610f41341c00c22070050f10085250100403140182510000790700003408440a41c1169042440186907076075640e5000080c40005000110350b91114501142e41a45042c10701d02034544120009440c01840855580040c404529200c2a0781440c3c896104041c142e2002119564490408900c44008031001c0e030138000700590001110101804210f4034100009060000b510283c854080306944440c00319520b504807852107030103610149010000510882c0146100054038240101d055102c1000a00303101140f042c45030440d0340300c134858040c05907004a000041c0718605000c0305d40362032556025143c0d40c040003005005180400082d807580d000d501c10005100341d03d01078a056180c504805001002a01d2180704a8415410071800d80d04001c000015001020f032260003003280344c04414800307440018031540825458032541050107108021b5182d0328042a00a49103140c280058000e81e01e0004080e000c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 903613372 1250 903612122 903612209
    0x120b0108070b0906190905030a030806100507080703080a200705150123040906062405091809030c0f0303011811090108040f081603080907050306070c0615 68
    0x3d0780d140011a01010080150008010100d040c1601c41d402294000f40c0c00d0300606403800c0804d60310441c1e0910800c1c08442e506880030504408a4441c0241040146650010040880464001c0d08815400000440c1c04a81141e241441200c1101074201e401142100415902e00b0004103120701110646801c410100d00d40c902050b60a0003030f8034154504001c0360304c035010500d030344030b54005041054000381c0a204440d0303100b074043c004031032401c40c0d4503c0c1d80f05014100c4a8030303c110221001240c006011040e80c105581a404040e08040d054560741e120070405041d0800d01070020301c41c1052480080c546a600d040030300c0f81c3ea400300c00700f100092450000e680da4601c00c440c0980c0c400c82020302e488907050780c5615080100c00381e0f803034026141145c00300c1c08505810ba1391040403a02842940c96035016102c0421581e80d4022602620b94150001e900080310180700301244c1605900a820200b0802204c0c081c2180c0180d00344c01c032240d102c04001e03144d056007182d410164901c0c8052801c0341e5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 903614622 1250 903613372 903613387
    0xb1602041833060b0c010b090106080114030309040c05030402030d0c03020604030e01050c0a140c19290a0c02090705070c05010f090305101d06040f03120204120b0108070b 75
    0x11804480000d50400c60b440410a480c000554040303030401c0c003808190200041c81e21080481e58503044418a001c5070342c00e0505040380c030708003058450304840164841460316400c00c103054480404c100c14140d010300c400d120740021a6a2401404408900d68607078544d641082e00625040000c40da241806201002400ca40065400600c55038019094035021400441c0d000c0101d64621501c1184d5440d80304203200c180c140208103400d001d80c403244504071941074250f98140605005030070348400041c1c1c5141c004120302845524007190004d4000d841c9510f1000710b026044468001c9040a4002000126884c0442c10440c0c0c509030080d00c50b040103824038800350394148440d110750140904004503041164800390203103000c0d802441d404070503100d614031502585402040700d0070b0980450b000428440e03021100c0402c6607030145401003514207040303105442c00d440030310140885001d203035820400000c58894a4020b01b81c400c2c466000141c06501d030601240c82e290454100040390b0004000f003d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 903615872 1250 903614622 903614633
    0x6060506040b2727010f05010905120a0b0a2306031b03031b0f16050d0f03200606040c030b0d0219031a010f15270b16020418 55
    0x41d0600d0f00005810182c906540c602019190503011070700d9002010082c41c80002140c0e0900080c0c01020268000d08680c1e0fa4001c0e501d0115061107842d011440f00c6a083c00b484c101240d418280310460811211016255516131451101c11105840300903500d110403c000754800d615020301500304003ca0141e414110700098449054180c00e444002c4252000c1400b03440a000351021601604100304080084400581d120340a041c000c0049006e0411604000e1060f0100c1c0801c0d41e0015000e2100c0160b00d03581c4051104444000380c041c0200c51091501d0350038414500c280b05080f0f4001f03044903081c01070a00064802c4801c0010074103007000040340241d01e0384902401c07219011a90900d24044503400300d40503c1807a0005420514151300c00d031013040140501a04a030880c0c070804010642d01c000d03181d00c141c12400140002010003d444040c1081100c92154040701c45844035a0700b80e031070400b44440d42c052103086c0401c03c0582e00201c01d618003846885400c12000d1128004419240e640 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 903617122 1250 903615872 903615877
    0x200604080f0c0a0501050702030c120708070816050a350306130e071e0608101223160b0306090a0c0c20100e090c09010210050a0906060506040b 63
    0x4419a0702141584000d2010060880450b4002c0001c002d5428501c1000791a40c1c806110f4080c1445840c141e40c080c022080101c1d003003207403c6100c00c3d040c00d0440d0b448403a2a232000d107903002e016103008000c00114406100f070715042d5220300804c01c000e0603507204002800b21031035560318040740780c4420300c0d50342889a02102e61021044400c02104266a80e610f80206044100300c082841100c5010400e1a1300c4504240148410b580124603d45d40782d00c22280c1e0602100c104200700741c001801c10541800c0150b158159100710b040c02e6502c001e20b01214199091300c23950a00a0384003080540d030380c1c08990030040c007814104064074175500d0100040350380c1143c00f84c01184035035a640e510031010351041008800b0a41c3c4180180c1e0982a003114031007200c42d005102c648100c0406810403c41030041c054840040c1001d131019941d6500c8190a0f9043c0d00b1044131181580107241100c2e00b08009442000e00c00c481c52900010b0b00b02042c200241281d2280c0c0110780074007010030041c07150713440e12001e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 903618372 1250 903617122 903617137
    0x30105040201091712040f03020901080a1e02010c0b040b01051c03080103120e031608010b12060f0712110714030331060603050f010b01020106050f040f061520060408 73
    0x207044d070300101000040e518001444107140050b00002c1400724800c2c0d107030280c40040700d00032956030b2031590700c0700360082c0c84901c203a40050100078a202c0092816100308161040d00d8014104042000003a031503400010310200c90468642c1100300051001e807414000c071064802c03821090301000c1072a0f98002e0034805041c040941a800740701e076441800d52094903d01c100501c06800d4440b042120001040c2c5c802a80c000c0e20459401d0100007640384c1000040c82c0700324003203600280520744541c1000c50003d03002a02820800003c0b042555801c0a00c2c010032000411070b510030395480d4103d0411064003c2108400900c4c4c0e08208180000303600c075811202c899540c0c01007003805503c1c95090f60b544400a00400404090400000005106000c00c3d11440041c100000f8041e003c0a00012422200c41b40143c03a8003440f80d496002440c24242d005c855404451072002500d1500d8410162050044480100004103102003070300850a03512201c00200c0e101d40001c0ca170500b403554442c082c0d0f000390b40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 903619622 1250 903618372 903618389
    0xa1a0624070606080d0f03050c07080c0c030102040602070f0f0e01051c05100501051212040b0c0a051c180b0315010201181112031e1315050d050603010504020109 71
    0x1200300c81448010021142142c0e448501080301d03964031540d098031481180a4803011440155050f188140240501442010442c188034a44403003039a0b0710105411204491505201340d0701d02202e207031000d00c000c1000d880ea80c1c000384092494686d00d071109250a801004610402c100200000d1140341030160544004840d0f4135480500c11485102150303416501800c0d511074221854045080c5901040c1a04c6043d180e5494411101510560310407000440c00480401088104801c01a0b032020301040c107400001c4d00c01c9415a51102850409407003452224030240c070f5121a4121b40004c040c10200801d262a0310740c052401100e144036000044c15405207011801003000d1aa2007940310b1105c01c940640c2641c1402c0d210b0818600b09514100c61501070148146c0b20a94141e0000c00d4981d000d241c2410070812003803141c1a560b07135030804501071121100903040442c964000703210000d060785281d44c0301a21a4404c03480d200030366401516480c000d9140c40144400750340c0c8005031704180c2d401803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 903620872 1250 903619622 903619669
    0xa0504090b071b0b070e1e03060a11090a03081206011e300605120a02060711030106080607020109020306060a030506060405150409050c100f1b0302010207140a1a06 72
    0x140e0711061000f6094008000840800410072000d401144410040000b510194580703540030184072091482d00c2c0309694541c0c0b0850000c0c00c502c54641008809880041c0540c4c200032590010900d40540d81c2c2003120b44400100c3c0b888a90810740a8440c0c0c0000240780944914022030010750106507200d041c00c08100d010360508901003002c001d0412081100b005824603d01d072095800020103003401410311840d81208120718000c4002044040d07030f50000c0001303140c400b40b5520482c18220070143c00ba015500c4140000b03440d4414440c041c4a40d0541c1c0020035402c03403610402d8100000180315600c200700404c018000300e1b0b0005200f603031001c000d582c005129100c1c019600722106c46480410380c868141002901000008241485210400d507038076040f8201d001d205545403508502030398001081c000c0300c84080c164185d00030240c94080d000051a1280c691100703000c01c2c4540704512807641c041c100400401c006072083c41c0035561502440801c505285000902d2110211494504003041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 903622122 1250 903620872 903620897
    0x305070302120a18051e040f14010b13081902060304030c02091005010201051005010806240d0501051207140103150e090a2105040b030a090f08090a0504090b07 70
    0x3000745050b02c00100032240d88828201500805214585241403003250640e000010700707042c2501c000b8100031840e64005100c1050030180700007011041150112940c451403e90790030448040040d018008050503680c3d903400b10a070210750716066030302107582a440451180b1881e0315015450b0511f41d8111042e0740e0701c0e00d480c00c049030032880402c0d000c5d43c00040d02050065810032032035800c0403117000303070000c0c0300c5644c96010502600d8407502c00d4901003001170300000c00764500340d0300c0146251040141254481201c121900c200d03001100354801c019500d80062180740f0f0100f9102503464840f00003020f0440c24580c14628040780383d560349042c9034076240d190b0341100e003c4001502812003c0b14001e09454040c51081e45c440d44c4000c156002c55416485010140748000d038482070081c20344440d40f41910b000d418500a520040a208400b540c2740041d500050642c3c8203c4841da0280c502151501d91003020000c480c403450303001c24030652034241010001080c0c00c46d80741d401109820070520360200f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 903623372 1250 903622122 903622127
    0x1b0315040303231b04030525030b0c04061106131104060305030f030406060e0f0402010f110303150405070c0b060d1110050d060605120a11090a060e030d080f0403050703 74
    0x1070410054450040c079400c0041d520306880038261080c4e480029189400ca1520310700c001a215902000d8017a41000403a80c040242c1d042030b4440039906145129071036070fa25111085030700c0d01030b2100038414200240801c101d941c002c402d04c1e480c2e000d1001401e03c0c1e00b4402d00c0542d440d00d46001c003c02c40b00c0191107810241e82c65907c00e400031038205040d2a80c82c0594121411103a00440d1b040301c100f0318140c408107000840c0b000103071007410140c141d4802c5488980066032600007608035242040302402100110440a201850040d11998504a041d205c6d11b4104000e89200610b013071708101c0e0181010001c5954400d0058210074140d503600501211810040c0450108041040e01b0420000450410b281d00c20010b14029441040402585450742d50888841c0f081c1040300f00001c4615000c996502001e034000905d0074460050b0341e24000b48600400d0301e0003129400880800d20f84405030100d03003403e02260000c22010310300320400d442c2c10301c0c0001d641000600060108280490344004060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 903624622 1250 903623372 903623381
    0x1e05011e0e1f020f0c0a0615031713030c030b0907140303040612090c0b03041b06051c1e02040e2a0304150908180d0503041a1b07081b0315040303 64
    0x1050000c0d01a90341480c80101d51ba035841076001100d055107000382c0c2d41000d10200b85180141c80d0302810020701e400400254580302e0304400c030140c0204060000000c0000e50518a0000a41c82856400281d29000030841d003404d40303903800080c0c2004586240541a5004412034040d40c03140e0400b800c0c048148484140244000d4100411020309030b02c01007206c05540c405140308911030180c1122581030020304210036400e5100ba034000c65000d11410f0b02d403003a03600b1083c9a5503400c410005d40017041c5d208201061a00b94512280594000b4040c4124a01c5600385a0b000300400026070b540b11a9890501c074005000802400032a0003001050402c40701c101841c90480000f10180000001e5003840c06090784241d07001d540c03000700c25007010380e503003000f800788040c1541003000740d810145041c0301e83c080c0c0200f9610352950608100441c2444c515205040c03a104640c0078010a0524100414185401e11b4000e603a450041058101540c1d036070000b40c082c80c154060b00300040d007901c8505c1e00358041c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 903625872 1250 903624622 903624637
    0x1270e090106080d02030c061b0d06270504052d010e07150e0918101a01020c09040b0123031507090609031106071e05011e0e1f02 57
    0x11120102800003903101504094165584281a1a6a041001c070260307640c1c851400c0712007050b00850002859200d0050700344070f81500c0305605515007840c000240040f40ea140d000100d03a02e429001614100101c0483c060388498031243c00c0000b0704150b102c0d0f5960741c40d040903640e110650000c0e0441c0c0c0055112404101c074018100074084801360020300f5840b0703030180c0194001d051640003140d0240d48135124003502c0c400060300c3d441e00344c1c6810440001e222110300c040e0000744100c80800d803c5268a105803d0f40b5038101031204240310050000a0600118080c203a00c2505281d06100101c0d00c105002030440d1070b4501e204004141260805030789908408049d60715014802c54203040c11a2248158031400c07031a80e032084215140c81044e100d09909000141c0351611802410032035003010030040c204180103a11004d44255021520385030306252801c102e4140c0d456030f101101c282e40c1100c500514850b450000c4c0504c0f05ca9400090342c61000b402883d0300c00686051a0f4441d0400d40e0407540107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 903627122 1250 903625872 903625889
    0x10050306010605071208060108060d03021207260306010210020915070b0a0f060b2502040e0d03180f0f14061006020601090b150a120204060f1701050127 67
    0x650ba54282c040d00b030b038001c1c81c02500c40300e81080014101038407801005208141c161100340003a25130130140f05d00c100c05000f04030258850302800d00e0404855034040e1030300b14401e46400005002030800380102e4445503140c04d4040328280140070585e038001c226000101e402c03600041c1c880075a0000070b1a100408078041084241c00190801070141c1c403207200f442400300030814030080290182c40c504a030031900c0f0b815480c10f020b01400350b01d20f15000e0403400341c0e5040007465200310501d4000030215038604144098503481103800c4048940c25000d9101062034074905103090726406e071100488101d040c0c400034802e6060110708402c00011192030400d2850300d1040301d91500e00821084003079001070080c5009845100700010b000605809101c21408020706800100e0310015405c9005812650b41d81040c003103d0020f00054107014405400200600e03515003650025143d0041c1c01c00e5100a0355509021002c2d0051005981007403800f400014400505a820764200a05024050301354106110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 903628372 1250 903627122 903627133
    0xc03020a06112103061e063c0d0e030d0e030a201507091806030c0e0912160503030405061f080d05070f060e0d030b0307081203100503 59
    0x5416a0001e00c09260b50b4141e012184182042090108036070301c8040c1c0441030000400010303031710b07040030b0f1500000ca108060301a81c60600c0b140c0020456001025030040808600c5001d0260040b4281314280b88183c008555034100410007040240b40f050281c4041d00d43e49076040c0c1c02400030100101c2c0c0400c901a2010412508000086a22680802c0b000000550103200800c8040700d840300c1010142c08007001401343e807040035100035441c0401803c540c1032214000307000983d07000011106038070181117040026403600303600d4885007e00740703900a405203039421720400420240015101000d0307010b0002c00ca4590304c5085081c0300ca1002c0c0c0368024154000030007804104100096654068040c4005280880441c010403220700d85031440340c01030643c4200759071095140107800404444d03024200c0c00380ca04856441c0c0c5008d69210745101c2405074013022000101942c903106041d01080114082c2c141945410759040c1d880c1f40081e040101c276140040400c00303818061640100030030002d000d484 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 903629622 1250 903628372 903628379
    0x604021b060a2a0c0605060d05190c090b060d09020307051e100f0f0c2f1912020405130b04030207060305090601121509150b13020f0405010c0c03020a 66
    0x200034201d803102c1207035224030600e9031010000144950802908040c4d44003403402e030325900c403080a4035000c1d00190f041501000c204001c40c0b000c0c4100c818010002145031720140d00ea14108200381010381c002111985043c130005030b80c0c3c1c0e500c003c85100c14203803000880d50641c1c03400040d04100d05640816800848583c02091641030303d4040c0400280c1202d80300540a0f4201e000da44490900002c030380011441d81302282c044d400791080d90b0043d406940811240a000c11408a002c0d032007100000320b190511f8a2001b582c9400d0488a40c401044440c0c140141d1400c01e903402c003036004803002841240c03a0000140b50380c0603080c10701e04150700040064a0b60801d0b080280d1240e41c54086c03000060704042c0042c0c6c2481000481d1412a4140480c0028030082078951914501d51081c3c600c0d211030b00c40403040c011403003007192100b140e010500c0000b61048100200240890030150250b0910300600414001001e0a401d8604a071000c3c204801d0000351031801940081d004e8000942c82140e004021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 903630872 1250 903629622 903629641
    0x1401050607032a0209010b070809090417070b041e02060d021b240c1603030908070c031b06110316051609050f0108060f060111101107020301060605120604021b06 71
    0x30303c0414026070b010303900d513600c2d0002c7e41d0040c802d040001c7c2400c8005c011405140c01c2254600f0384c864020014040c0500c5080c25004d0302d43e0050105a41e10284a010700050201f205c5444422100ca41c5290600da0181c0d13010444074000d1407111081e039903001c100d241c1c80030041d0700094400d00d003034015120b42000d610750305c00c5030910320492607403144065000103400e800c0580441d0404103213005603801030340c0759540840151840c0e00702120710500c18402c41002030172000d0f1910203988217510120f844007005121070307807004a681c0428100b081000c0c0340c0c0c500d13010201c110742110001d000842040841407c2031b5152a1074240061400c1c10902d01c0010050f0050740100e01840c800014070030640da90310b1445543d040180c506c206400041400f092003503000e1103003e10f1990a10090728101d080031403c19046440346d10401a000c03800086450440c40e080c400c070b00c0034224900b0a1402d28040400400c409500103040c50700440d40092182002403c040d40760141c1007081040743c41c586403c501c0d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 903632122 1250 903630872 903630947
    0x30e150106170c180d06090609030813080909131b2112030b041b030608060a05011d0403051c0e1203060f0d0206070804080d1101140105060703 63
    0x1d16000800c060061841420310122241c001d440d01c5551134180b2054005026152140844c0b80d44d001800c52000000982c00780260760b020340c003540d0300003400049810003400704103008214141d1071950303441d002d00003040704064a80e208401e81d05880c1c1a81c0394503a07004501c2c05040081c2c5080b9110030304040718902800034200303940401081c0403850081000349031640740b800100070282c2203648400c1001d41d01c00e034450420118001c001055401045ca49001c02c512540c4c0302c00000bd8036a4400e00111408100c041d8019180751000c002962415080f07010300003030a1141d0050f00800804903051600c100c0030b590409841071404102c201c0710b10b032207600502c0700c1006180240a03814464640030441c1c001e50f40700c0c01010380f45c001c10b1108141080390220200c40c0490f406030003404102c01046008002d8000f400c2c0142c002c282e40c0070360702405000c8103a840d5030152582e0601ca000b01e01d10316441c01d090b04451090790541d44500135480d041c0e44040b8035240c0d2040d03c04ac08031417000c19090030b07140c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 903633372 1250 903632122 903632129
    0xe07120803090f0c130507020115080a0b1e130809030327030105070909110d05070e120a030f080702100c0e10110618190b06040f090f02040c030e1501 66
    0x2152640e600403400c0f0740c0c071141c0000109a010040699030300b100500340d005154810620300c0001100b103040c07092141155015003003680035900804842c000c00540d044a560024480b44104036020b070310f00303205924000300801c6000000301a24502013000382ca0002c1c1e95400e940101513940315130000c07251142002d0720f4580b20100780810000041181810f110313650003000031b6a00d522035581001d0204024200045015426620410101c0c4500c0040c2c858540110710503619541c40250780c0c42080340c0c80000789540071075504000c98090029030000d00d0402040c1003400d0070000347d1340e0040e0603805d00c5842c0744510301d02410081020b480c50b501403080590070b88200c6804143d041e0015003100d04074480b80044131035900c0070021803442d0f0300c42c0e0660a0261000e03c21250020150b420014401c942d02d01d044a07440124000d200d0a07141074084c24501c070b4140d40c420040040161180f00303010440040c0a400b56550f101c0c03002d0365910a4120091000c4540c044903150b450b03900003940303040350910 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 903634622 1250 903633372 903633391
    0x11010c17031605070c150c0501020c01050a05061801030615080607030c110127050f0f03090117040809010e060f120a0e0a020d0624060c150b0a03060e07120803 70
    0x4030202c2c1d030b550060056802281c1c20070010340105042900305080c45580b400f00f002400009107001c5e0004809000030074900c1e41d0348002240700e05110070004140c0380007800302481050244180040c001b45243c116045030303002200407072110a803001c900c9601607242c1004c0303043d000d50010044c0180d05504400348960141c0e45182012804100c43c6007250080504406086003201010354000342e40072a505d116401041650384910425484070300e00002c0c1846c40040e03400205418540390780002207440710f0580010f4403482c42c5003d595001c86881011803481c1848480e283c0102c040c5c42d4a002d40e041e490070010031a40d20041c1282044255808841c03800c00c041c00c010008003100004603803013541550281c203c00803110307035a40e00c00180c5501c005410075098400e48078200004001c0c4248000d0509403104030b4141349038100740100b01030000d0950303070243c10810b0401290b25000ca4200440e60000b00000d01512a40070880c00d000315a440281800f81c60b5035040144140c4800440c001d11044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 903635872 1250 903634622 903634651
    0x1104090b01170c040302010507110a030b040b060102060c090103180c2d0b031909020d031220030718090c0509130e1b0d02090a06080d140711010c1703 66
    0x26141c1082d1190215001a1601ca051004000550045028002c0b8620030303078038020344940b2540450a4440303564800d03991660b03068284014403820219203a042102031000d002185401c0442e60f03003074826821624100f65130384140007000840c00c80385c2480260300000c0640f14039038446c0c1d034000d8802810021803003500104142c184417000b4800c43d6007261040340350f581c15a99241401c00210500d02107030031051b0744486005c00140c3e0307039088141c0d40c1403007521202c82d0061000050400c0b520000c44c4000a00500d0b10005c4e02c8454210541758006214540000c1407155030100c5400d0400c4c2c0c0e803010004074100703150600907036004809003e4081c0d06994510110140701c20b90030a40e0360200c940c030002e80203250380208215400c0d441d40002003020b03014009103442680030424400d001c8500d805d640b55a1001840303000014820802c2414541c0341a4041e90520a464825841003240003031130310340300082d50001a4081d1600e620440c0d000340000c1800c0e0070580c4030641c1c540c02116a8820800300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 903637122 1250 903635872 903635897
    0x705010509030d061d060f0105160b150316030b191e0c090e01140f030a0b0f1503060a050901140c070c0911160c09020c010f0e0d0f080601031104090b01 67
    0xa800301c0e04417056072103030010441e0b200d000500c1b48400c00142241e0410100700111341018040d1024101128412010a4078074907114001c00b81d08910000c45511a42090003000100360300c6034220025290041c500d00c0040d15003100d0300681500d24051011303268142403580111150300d1014926000d20034805101d54030785c481084a118070140250030500014600510450080140300c3c04c2186c0d0141440c03114046c0c5000003442e04031040f20840b10402080204542402c0312071003550000004407400e05100f848800103511160014000407100e9034900c002100600d094001c904d1150746005e40304ca00c0d0030f004108282681c00401d0644640101802c00500c50a06100e0003d02030080c26603c0d00b0f0007404501c0303001800c840f40c01920103400740400407a00c682e65100604034106a5800001c070621500b000c003050754110300c3c03110b100c0c2e00080c10030100b05400640350f000356502403030030110300c0c1d4654006034010100c8201460400304007007004100101c41c1c3c0c3c0a40c41840d000d880d10113a51b280e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 903638372 1250 903637122 903637139
    0x709061a0a02060c070302010603020d0b19020c0d08060a0504110a1107060519030608070f050a05060c060f100f0b0403140105090c1005090904060603150c0509150705010509030d06 79
    0x384801c080010382c49500001c0d41d909042c4050a0f01911910010036015071f260006110308281040c1a683c800c0004140502c60441400c030327002e440c10b48a003d41c284101c404c00c4079210b400f04003040007445440c1c0000303a01d594444011102404005108000e416101056807001d90031850120000c500d051071842e1031600001445411943e01d55106ca1800340c1c2240415440da1840d10518189500d8202c089040d210070710584001c1c18425008000aa203048104030300c07403806500c4a8080e4008018a83d0300c3c50009c00e080c0c3e0300805100850100e0f444400c011a030038810795003c050109034003000411010140c0000f00b0031a4050741d141d074100010360603060708941003604d9001c029444038030800c0903403c00c0501280c9143c01820301c2c81c1009202c3d40400d003090022074040360541d545810034020490702e071080070203005200340100500e941e43d5a001c1c04605c0340620143c800c801c46607210405900e10030841c1c404981c820004c0c000342c1004001203a03a90402ca00b0b25098034100000812041c0303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 903639622 1250 903638372 903638377
    0x80115050405030d051b011a030c0402090a030204110c030a0c0c170c0108090313030602042c010b030a09060e0c1c0503030c0307020a120e090105010e0d020f120709061a 74
    0x450081c040c200700480000240c61725401044440d0310007203540c1141001c040280300d003800100001280000f5543d090003010305004941074451311031481031198060649840c0c07414030039668161303070000d4446000c6119000e240181044150395200010390188111341c4a0350001805201e00342c0030942c1522400204e14070488a26280126444201c04000d15031154407883e8204ca2071206803458522078829100500b08260004e850890b0005010004404032541850081040c1c5c540c0403100d10360808c61002c1c002c01845070304090b01000c0007041d5260310f9a80a0260b00c0e078850020030407a001c8400c4035403035001640d500c6124011440500c296100c01e904001c0713409920401030340c030315507a082003010940c0002d0120400c520034101c0500002d20000c1440c2c07c3c59000f44c80d62064281d102c0208801e24005812017230400a141c041c180498841080346540c250781110304111a2400a02107217000b400500342c00450700c580a0001401841980008143c5664804002e00d9442560609002d807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 903640872 1250 903639622 903639629
    0x714040902010c241d060109060807180b0603040b041203020405030c01050c010e03030108030c070503011e0f2903010f0b01052b1401240207120309080105070801150504 74
    0xa1612081c03400055420062108503091000c074a15900070f000104c1c4003100e034041c1c0d0362940c600b280860b2007401401002518010030807000c05200e02810b002d629a26800c0b14401d0f080c00c40d50300d20140048075404d0f00112030b001400f80c840c0351a45454100010b030004140c1d02543e0041000310030001c0c0610078002c440c140c501c0600144442510700d80112210360104403200d4055680354041d01a10308241b00960007005104015611103440203051414500581c1c402c070b1080e0715202041190b403000031820130030b40d40050000544108401500000f0700000b00c400900484408108198032020569201d00070030b05400810444191400900440354030f184000d010400912016091414100001c0c5040410140d04491078a0350218001515440c009004103210164014412500001c11a0f4405514039604184540003864040e40302c0c800d602a10b48608044400c030003d060148807894004e100c07140c0200403030315001d000144000e00030302541d04168a1210081c0c40d4a1265040d1410b8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 903642122 1250 903640872 903640877
    0x50a200a0203070b0c190c03021b030c040905010915091e030e0d03090602010e12030f07111b1206040c0312030b0604030501060f06110303010b0a0c0506040f050d1d0409080f0309071404090201 84
    0x1620300030481d5150031042b000e0103034144548007100740242c440d4024031681a2207130f0b0004c50804c0307940c035100800050400e1160000c40c07514141c800410b00c011b542c250010079030300b100c1e0314a04550900b11600c12110f295580c0080200c01d01c0010035034814088030440d0120390003040300017100000182c450310203071540140c0800500c0410310241c100c03185550440c04608243e02643c50400361282001108500102c00201e60102c8901a04160844407181c0400341c02a008c1e500e06903440d201c7c0714800d07000180c006031020007601d8103e4003a500c00d0768544001000f840e240d550300c5c80c00da4003030724280c00341000c02042000d001644074016041004c0d2500c0b01c07406582142e007850459501178200f00c1030002007212120a51000c41c000741b0000c0d02031801845021005102400c00a103010401400c1b002040303c2d900704c410521101c002140049442103401040c41001414900540e0050f8801001c0a003400002e20090400011b20300080303418400005020155003410042141c1004502070701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 903643372 1250 903642122 903642133
    0xd05250e150a020708070314071520010b0a030c0f0e0112140c060705010c080601050a02100b0307030605010b0c0111040302090a2d0b0301050a200a0203070b0c190c0302 74
    0x1030008050701030400744a4910440e541d0070b5988524914180090380107590800441d416514101020721079040030b818800403181c81c0d03c00301d48000b80440d0085209004107d000746015045400c290440c003d981d00051018140c540ca074244042c40365080c0c4101b05000304100b200041c0d0603070009207a412240f000004051000b4681c0b9a082c442440030740c4c13008540200d20410215903103900107440c81314003d17030000410301c41c10003019000d00d1010302220305001c0103001e5642040d41c001245101030142c0e9001188080440c004a403034007525420041601d410321002042400c000b801404180c01000c000380103d900c5110a41c41034404d82c00065080201000040c2c480741341030300040c0780d102d256410143c104600803913824008a859207003590007a150039808032186800d0140a80000c050002001510300d400c20a44110f8140f4981160000700403c80c0e9010500034010395403043d4100c60b0f120303a149040d51072a003c42d8809400841101c0506540a256a22402600c202117034181c00a11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 903644622 1250 903643372 903643399
    0x9010e09090c010c030e0303130513050609182d0d0503060d03110a140d1701080c0f0310020406020106030b25080c0f0403260a021c050d05250e 63
    0x1210244002c101780d0a0182d040407440c3c10b911b0030001048c032101760302a8202220f00380070401051442c9aa0a44801806e003820f0294a5075240d40ca140c111181901d80c00302083d0140640c2c0c241624201e42c904c070b642400414184090701c4ca0344080d40c511181041d10f800080c0d4520546060000b6208039400901042081c03002900802d03107202204041011a13008030300540c2e0b6030514100315840d80009400ca280300c0d944090301320311a90101840c40d019142c1e650b0410072010b6464a1929205126806900d4501c0203601c0c00c0c01040040689488151b60b601d072114000f9020301000d03c070484064007070710f0000b40c0c00001044420307100004022000c48044604204a0314100040c210201c0140200040f0701e4925a29001300004c4d4440c000056962a0a2058064120071103a000d0300c501c4041119441103540400d148640c010b24403805101c801c1d01da003044034079002d444036101c106c615100500051601c4200803ea02040980309880c082500d075a00700c03010440d4a080980000c14881e095 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 903645872 1250 903644622 903644627
    0xa050304111c060608070515121506041d0f060f09070203040b180301050a20030403091a03180318090604090614071d091306090c0b09010e09090c01 65
    0x200d12950003411041c021803012019600340c00441030880303c1c250340304001c0050b05418004003005003401c60f14804840d80c4441ca51700c0318410f441400c1c115490140004580031859440c001c180307080035043c25111070f161381c158000e48040550078107481840c070340004e0b1270920108d29941704e0840900f46074105031001051000034030010304414150300003400045941000d94016080803001a83c3d4007202d850400107150841e1383c00b40440c2040b90600c15202a058a8041080841c00128110941d41c1c0c1d80c0d0f04044803c440c3c1c0c0d4205420704c80558140c40d444601d0340010f1350140c0e10b2040a070300110200c41c81c0d25070380d00c00c1d4038a10486501e100501e5001d4504041010b52288000d400801c800200c6d17541c440464203500b90300e522038a036a80034816000d5018071607119105043d007550810580d480c000035a000300c01040000308591849000040048a40000c0c0b40d50b0382c010707038070f1107440c0c0c40f441d0a070f141c0c0e0009041c0500007460700040448130324154441602171641a00604403640511004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 903647122 1250 903645872 903645893
    0x20106150c14010e010c0e0f060313080c0c18240a12050a1e1406190207050f100506010323060d021206070e1503071409131a030708030a050304 63
    0x2180b0103550300c0c2400074600c0d00a005410b83c142c1d441c3d50b05040280b050302000f2605081d48004c50081c4014020010007150364020084055001a0b0b0345884019464016240004440b0203070b1f0051304880300c2ca0114200b0102507402029200d42c803040c058807803500c850300341e0101e10180d40c0c4940031010400c640300c104081e0a5810740107070140e4580100c90340310401e10f10a1500b4078400717003588411603401e02c548076068190000d404070240040d41011603102240f81000c2d480302c40940e60001c0c1c04800c0003001c2000d1425212848140c820000c101c515080050030100c4515010908008000c8401c1e05044107080d42484248684e00b40c903140e40f010301a541e40e0208040341c10102042d00b0007020390b4100103080c810107466407a009528a03900500c02094054a0300038407900c0180180555141c001c21080e60781316400c42041d8554010500003000c0c000e080c480c1090982c5006020003021040c2c4407200303c21341d415401c4820480d502c03000c16030340340329191030040041c005101050004554441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 903648372 1250 903647122 903647153
    0x1c1b0e07170a141e09150a180506150f0a050105030408070303060e0c21070c0308250e03010b0a080a06020c121801020c09010803041707080a0c06020106150c 69
    0x42c0e4031240201c1d21105181541d45030904a4070145141201c24804134607a800402035000e072508402207165001141d502a002c070182c11307220105d040f04070032200c0c144840c094214040701c52600b0310340205d10b490000d02d400607001e107098940407d00c4d0300700800310004444060352400d00e19621034681d1000ca4000304011807c142d15a0710008040c20103020345c41c02400c2c1c09100b55580c101840700700c580c4400543c0c2d030360601e00e01102000710598000044501003501130401a04c9030340d90381000d00407480030023111802a89041064000658410b60b00e50b00d454040c1e000f0400b100071442003144544203441b40343c403951b0080e803034040000c043e40c02070100c0c10208400c075076494055000b4201036400ca140c1003004810414103e00745582d04104044020388140c8990070036504148910f6123a21031030164000660501c445164549401c100c0a8001e00d007120030b039030b401e0b800c0e071038032075007c0c00c4612684005600704030340031601c402c010342c40001452068030f60b410a02142d0741d4280c5618800750 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 903649622 1250 903648372 903648391
    0x31c021b0a03022e09030807031b0606080f0712080a0c030504050a060314100f060c0f0c0305150c03103602091207080c09061c1b0e0717 60
    0x401c00801a26825101c0c443e0b41d010040d5010314085043d5030b1180d4580e514542010030500369010404180400c04407401c641c0c0600d00b00032880b40751003440d0002401e008000388100d203054000203031800042030700100c1c0e0042c1015078401a40c0d640304d1203919204004040c254a00c2044072081480c081d02017030240c00e200c0c0c07e1070350400d0381e14000600c0c00a8142d104030042070311420743d260594200015262721003001615010005c0c1402c1103140c282d0701c0c0340192414000c0c003981400a204820707040301d5072185d0007001e07040c0080c1c807031800c191141f0b03280601b6000d45820801207041d0700415004e0340c3c821751001001c3c0050601c1d010540a4030841200f241001d0440020501c1c0d0741c2c034020584a074080ea10410169a40400b44184002045050613812081d00800014080c8003008502c0d4140082c00312060000c0780c031350308005100c1801e00c00f1925215411600d00c40d0404c81002c9001d00940c1c12008a20070056859184100c00c01003285d20f030000500c00344071006104035240d0440d0304a070412 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 903650872 1250 903649622 903649639
    0x30c09072a0b06090a090f120302041e0302010e0603041709151306090501050a0207030f080f07141902060a080705130807030b0901060b070818041802031c021b 70
    0x40180c1d400400380c4410940b00d41c0310300010070609041c5000c1045e00142070700790400c1103000742c0c3c4608651100341c001c01041441c1900e14107010310705c80d80595020300414841003480c500c12100009683c0340381d1100300c0c0860340b02512240c0328500002940d2045810614a107a4104a011040c4a40d8000c3d003601d90b10026588185c140d800004002e01500d1303003100360406603d410322001070443c2c030950384000d040040c02c1100b400c14590101e01e182c1140c0e030001c40b410340c9500500d08954180035010344034441803c013103031080c148110107050305441508601070751401c1e0311007070744c1201c6032038002c50107508050108520a0180e1003142002d5201503d0710b0041d041c82595101c802d0200490f510560085d07000c1d8a040c0700384440044550340044072040204140352801c204a003460013600c1c405403044001041201c014075800e1080e400c464401402003150342c1b0503240c0c40c000015400c03400c1c2d01074031405c030408411000c00c440d001002420b0b50020450200ca4001d03146c1d07401403088055070024040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 903652122 1250 903650872 903650927
    0x3020705030711370f14060c01020f0708040e0901050c09280b0403061407020c01050c07031b0e0a09020616031b05030a17010308180303070f110f030c0907 68
    0x10518615180c3c0c0c115102c0d113803000d0418510100031200380d0044880d44460f40810080010f800c3c00142c090101542c1c150b40301c130381c030241980c02801001008003808200252910400c20510000c0042d2159210004281c0d140c03595094200c074012514a4507413841080440c40628210018031107503884500c0d541490001180c25101154255020711003040000c43c060003003040e14000d9484001c10f03a40800003901d0400c1000750764194050840d4103100001940107110b0009101074005150402c0d1b1401814141c1c03620303006100918481c0740070b1000d009000c2840302a01d40641c800d141d4004140c6802c0101c000c030030409061007210110140964034031000d001a4006000c0030748503004202031a15a0b402480141035484c08038001c0010030480c400520015a19100b91050507a502402d580b500c0c0c11000032038910321901c0c00146c0b940903290501010807081d003058001e8180f05489821084c461201070645e40c102144c0300c10f520180140004800074414440d115195160800740741300c0d1410b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 903653372 1250 903652122 903652159
    0x30503060603060d02130e0f0c0901062106080a02010f020316021315030501090b180a0803041703040c050316030305030a2007050c09010b0a1e0e130e0d03020705030711 74
    0x600132009030b145072203407a1f07612103c0c014044011b419441c0400707003007229007850005a40309d4050040205100f4188845140001170252041010081c903008010baaa00c038411a50f4803510300004900080e10013400000c50303031011040e00d480d550307041c40c2180c00a50aa08202004405144881d412561128054000200e0700003d40085000301d0000583c8080d078100185a030340020030f080740d95410a08150104500010150300c3c45130031031031203a1280c440b41f4185620b140e58540341d0316900700210602080c0701480c070404049540850032903010450300310703404007150150311004d070200d00c042c00021450401d070740040d003c031113100107425407440b40840011155040894280c5055100d0040b1203d07504207407658a000d020980a21030034019124001080010f40c41d0721410050318084200e440320b03000d009144c03055000107002d14ac030302d4a07200c0007030000c00c580e01103900c4511441071040c4240303002c2e200311343e1103e400c071019502e401a1134030b500e1400c42e030303008009400c0116000301d9140b540c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 903654622 1250 903653372 903653389
    0xd0348080c01060f031a0906010b0d153210030911061c0b010509150a0e09180c0907021c14040f0302090610050d090c0305010c09051507030503060603060d02 69
    0xc0c2100d208540074114201030039070100c1c1b070222045142c00708040c13215207100095498110740c000502c0d10781d10a07100f800380c405440801c94903001341103c0c41002c201d20018895501e80403022101c10350b409080c030482010ba401c80d150b200c5402484003900307031010500c00e4000c91091170041e10307080000744803a800300340d490740035098a1a800780d07609a4803441d81000d001c4c0c2c514107102403a00a0a1165000001c0d0407140314440e03905800400081001d4801c4c01624407904030f52006051a54601d003009034490480c480800050450080300181c035075514002854034010031940d030042c002c0d0b508620940180c0801e0004260500815032001001d40e407010000f080640200c00c3d145200d9490751062260310351010300321512035500d003118940c80781c3c0c0c4401660021000120080380e5041e050500c0c41d030f036010782d81010704a5401c2c04602c460707513a00071003100101c4209881803a4080d001040d048580c0c05880300050029a040005c52540e1a201010b1a040130004024101c2402503070300041c41070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 903655872 1250 903654622 903654629
    0xc2001110a230324130c08100503010510060807090f141806010c0803060a080307050d1b080f0d06053c030604120e0d0348080c0106 58
    0x44000400c060700540040b0b41520368070780000a6410f40c24044040a400b007003041c83e1410b04044050103001a0303460a40c6040100d091403010081101316910040081c0030446031065072840100002501d810140310b124803c4408041c440c4200b4200320045413032160141c4001c0400403900000304030a0303505c0c440d00000349840003404c1c4000120800f8401c603508041449103030041c080c02044000e03600112500951544816101e070b99036220800141103001c55001068107110114099041140002d1102c0d9142d030340d0b071605c00e06442c65228048101804075001841c0340018007004450a00040c06400e440d082c805000c0340103601c44020680072142561711031071411052105200c03400ca070494141c15001250082901c0b9181c450219640700000f40c80244544002c8079150f607200d2180c0c4241c820640010000340940055003402020f1054591001120000861490022007007107660b06100d01d1124107902e05451000200000c0e08800800c03da500e954200100440c0314400e10841024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 903657122 1250 903655872 903655877
    0xa050906040905070e0403020607030204060f03150819140102070f030e040b06160606060509010905240c03070c060c020a091508030307091e1a03070e040507050a11010c2001110a 78
    0x1240307046c7c14000c1c0b810074058950414940304010500c5160380c042d13512440b1021074100401c0c0c1894068014800c061154040c02031409801800030720290890f041c2d940046c040c040c81c0c07034440c0559880707a00b03e104443c2d0042008006003503420001c3d002d405042c14803003000700001541184007011a82940c0204080c02c60008101d82c07401c104211449424003800080c6442410f240e030b240006080c02c4007074000c3e54440c9106041401c0039a0402c989880740202507007007280c4031910010016502d41007024100e81d2500c0a11000c12a03610420318009602d0b00107002c900b150307103001101030007013146c0318002000807030b160b20124441c0070030401180503480507610350702c0b054507140d0444082c01c00c500d802400c0104881040011038240a251152a441180c0b565502e071100081601c1d2806595812a0001c0c2014100b0072565040302c0603204025940d01c483c0c2c2c0001603145241e00b00c0f807500302ca04e0041007004808210443c900780d52240f284a07440c00010350486403038411100c41e00404c400400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 903658372 1250 903657122 903657149
    0x613020904110307110f102f190203090a0b0906120702060a1d12090303130b03150913110414090106061e090e070c0b041104060b090a05090604090507 66
    0xe005070310601c4440c60f004d17100064800614200301540d11928403e50480090b5214040c0400e181a6036a244602082440d230801101c5038071196403070f0507000801d10078210a49420144805400401103a0403204001d0210888608003040311016400110215800440501036096862900d000043c0030300420b0b00241002d18010700b21006441011204207400801a03c4201d0841400a01400102d904110807030301d40b005103020915500030352401c450b014209560000b05010a034006500a10202009081140c1c3c5d14040c0900c011f020764610100782500c418001c040f0340d070a9610f101ca860000c10114101081c041142400030b81aa40c071007581e55544000c0086540154240100700301c1144001800c40305c2c4000500014800d00c900d10301390b804400000d1000d40324004061030b15501c5050080d440c02e20b0705011024080c0c1c00c0c40140124580390000c20925500c2095581d03404c07000700000e03045400c0005100c640c010280030306030002e849540020001d40140045400b07041c0c603901024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 903659622 1250 903658372 903658381
    0x60f0c11100e0a120201021b27091c051806040f17010b0d0803012709030503060102010b010e030a0f060b0301090f030e0a060905060a2307060f060b0306130209041103 73
    0x60b500403d40d2090710000c401010020050b40c02092450895001c6a400402218480c002c60b0703141074542c01c5a08050010751b2510403500d505502140580e10750411140e00c00e06030104003070540031840c800e80c0420000d1000070b0312407504400300c010705000038110300c0c10142d03203500c01d45052120b500440d00c079030301030000d0041440092280c4000000102c643c082c00099588075041a03204c10b0017600001c0303000000f0141d0035000119894072120021008105442550400410307a400c29619a80154200034079070240b0740c4500c840c9410300301c00401400d925401d42d52031000ca02040c5204540507511340411220596080c41820701540c050703500342480c01041d01d001401c00154036681d03886420280e806010455020071503009075042a03901c1541c2d6400c460055801d9043c052008a15001c000e007611400c0a61b00b0240c52264404d220600c80d01a00d248054240c6583d4003c4038085041840010558038042c8440781c0495045100107240030408001729040c0c41180d058095424000010300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 903660872 1250 903659622 903659629
    0x1704060314130c180605060a120e2a360f040803010308070816120210020705030306060f070b01090915090f02010810051e0910060f0c11100e 62
    0x4a61001d81014607003a0042d96a84002d1201d05038055100c2083d200d2541001d10015580080080c0100908081d141c00030310000410380848140416009820018200184403001410f00d590040000000c60f0b07102112400c00743d040c0c1d5503581541d124403060101c00c400c2d410910440c01400e045100d1380940c021900028040e280d0180180300d41200c2882044042420601030340c0c1981ea10000d2981d4580079030400c8003450140180344c4440144182400c001c010204c4c00901030400281c0039641f4075413212044100b03d0082c02c10180080d0401c000160091610000a01d891401300d11420f0800d170580d1204030b034801c402d8000031512a6104002c00c140800ba010541c040101c1c090113200c0e03240240d903000c0c01c842c8060f0000b0705010403540850907041d801e6000f1005400050800e0310410042e013026800d800b11000c44900400c2c031140490a051580c919100a03900d079516a10680d522a00b0b0494000d17040c4041603881c003d0341103000e92290b49521403002c0d081c41e19520012040c8101040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 903662122 1250 903660872 903660911
    0x616030906080705180109030b100503100b0f0d2109081c0c030c020f060d0b040f020a0f0e0411030c03040510020c0705090a02090a0305061503160504050417040603 72
    0x14080c44040400c01102581c0201126040c180b1041d0400034140c01d1001a1145400c7e030b08010b240c45441c070100003803109144a56412114100c084443c0300c250714280c0011070b11040100e680000441d1340030041303400d1801b0040c0041e07101d4041d4020b07000c15071201d410180381442d2003800180420b00c08010310002046030703840c1000015042c0f1002c04c0c01e0000505150040e0100070140031245814206540e03510200b030300340c43d0014102c10342e6108820340c460014100b04c00e15900c11440d001c04e46003001400c2c0300f5521050003540307900d00c0341d82000c5819280740741c0d41102190705c01e0b02d42c00da000e01100300d60301442c02810000c070156106e04080c600541018021600c1e51107441c414004010030712000aa41702c111003081c0e51600e02900c4a240300c030040c0c03141d8900700e41c012055080002c100600000c1c102e120341030300010700c829034008400701910354101d06004030382203449800a02051806038041600b00703100780c00c0480503d10041908005400a90142000c02d555111710190520031040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 903663372 1250 903662122 903662129
    0x15070510110f07150b030d020f120903060127020403060c02150f130201090909080a1403070207060318060501031415090a111201020403060f0e010504050a02010e030c06160309 77
    0x30381a007040002d141c00030182c091100050144d509000000c681c101c29a4071001c40780d2000307020380b030000b0403400c400b0395030300d412020240e001e110310240394441003110000e640c0c2004005024043c41c0c0d1800b050048942188901c010306683d540b011007403c958288001c0c0021440381c071004c00c81c240d11140203800d2980c460001e41c55502590200722452041c4024180d2120600005401c8241c00b800102c40b26040780d0000380616107800003450a0000d407402078892607165031b0303a02d0f1451032004100c440b9800150381400c00760f4400c1d04140101802604103c0c0902c520101054140c5125145d000a0784c1080e40700b0f45180d400181048603da005008244c601080e20001c511541017000001d990b03058800c2002d05172024404c0202e51580d50260010740e42100c43c4000c2d521662213040000c0108014028020840d113400f84c9907800d0300e0180602031007190042c02500c1c24420700c0d0010b6400d0070704204c1840d4140165000802756a503200c0141001d000e900e0055450b54060f4500a0142602c1e9007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 903664622 1250 903663372 903663401
    0x312070f14030c1507020309180604060510080703201206041d0a0b0402030a0c15020c10020303040204091b080309090601301805010e0c04051009050615070510 70
    0x10f5641d002d00c00007a140070045440e9020005130356550b40c00c0f800c601071550f030a0391000d8820301c45d00e02d0248103003080c0d000c3d42e0f00725800c10070550b0711700410a03c469100c1440c008100035400140082e40644d00002c52a4000ca00c40d803844040e1250b400c40641c0201d40d0002005031071030074083e2908251041d883c2c807520040003815076a44080d140d0341e4a040d981001404010758a00050840d01c0900001034440da01c114403031007850b1240c40c18180c0208080036240140b2400c403801229207480100c921502c00f0540107580b0b5510383c0c1e001d00001d814074100950b81800c2c40c1421542000c1c100820500404e1010065604c8400304001c10181c0f8801900042c10080500354042c1700c400500074200c0342c6145070b60204086004101e44001130603100c03102030b43c480b0440d51194103010341034004e00c80c04030008042d1401010180f081004072a019500191110101c40b01446108080c0c0d00042e007240300207044070041407112200c004540c0c4101001c45141e001002041950003042c0101d4510b004003c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 903665872 1250 903664622 903664627
    0x30327150b09061c0227010e160504050103090f0b070903060e010e15090a0b1305010c0906024602121504030f0c0209040803090f0102030108070506090312070f1403 72
    0x94000665100404004a040c403803190081e50455a13138001100341b0030306080100c5501c1001c0f1004480e101c0c0e01348102c040390101d100c00640b00004d520200c610244058842d1410141090011402000c1680303003100c61140803000200420f0b000240c00d0700c0f403899503480401c118118544182502c111814403412607051004101c07010390042418010341510001540803655030102892030140c2d209030142c01d40e4030300010301c100050051041c18180340104000d01c004e50b4481822500084180309550060b0010030070009035110010100040c206450300da44044140a030006000d0316802c004004d4120b4122803120450038951005405038085501a00f0060520090449003c4004100404224a25a000c619240250040d081c148e40180c0314050341c1c506490468990751040c1c48412040c490784c4450309040303805000b2281a903003000060918145090180050f94001c24181d41e854068619044440410030015260f07060103020304404040e010300740411590307031740c961081d5590400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 903667122 1250 903665872 903665881
    0x11011b0c15170a0c2006041a062110111909150c06090501021908060f0141040f060903032007080a080414030a0f030327150b09 56
    0x30302c2d003159482500705401141c5610700701001c413041d1032650700d011441c031411018083c0f00c0e40000b408512036403142800e80503010400d28050300025040303605507400003c1c49461506074089508040c42080d656044883c0c3e100259540c41c240c644542010a2040c00801c15000e281e030b085482e2a910040c40c145270540500348207a403000c010030745981209018061139000b0805c2103503400b26030182d4010008640301c2c543c121241000c010350713030848400104241c0100362103250511500700d03031801c16198920703094030034082c03103000c1000d6160f0303074108400400d0b00801303522a2000d0095000030304104641c0c0c031b6085c160505041d400c260400700c1001a00201400025040500e1101104020784003000040141282510344903907500b000541c0c2c012400703240200182c2e607000d0400d4500345c80003165541a0401815583d03148210080d10f0591141c02c40c0001c240690b0142003c07004491022072138141300e40349070440e11624402140d030701c84199883c030150002d80c4982c0700340110840303003038103a03090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 903668372 1250 903667122 903667157
    0xc1b0b0a05030705091c0201030506031903030e010e01060b0703170c070201030f0f020f0408060109050f040b04030c020d080d0515010f11070f09141b03010311011b0c15 74
    0x65519000140a40000400c407030501904c01c2e81e9580d0703002003014180081d800511401da94031a9401c03070109050502245030b91902244140100003c150740c41c81219450320308501500c125142810795541e100001a0410340038040d400107044a240116a603c1c00d9143c0109075005240c24011607800c01c00611414030600001c40c0d51242c1c0900e00491002c41a10640004200c2d001d01200c01d40e1000031610000c42c1c2d401c001d081281c03409000d40c2c600780c1c0e071601071b4010740e002180c0489140f0f608000207400640c01842d0160450700030300d07141840552a50103d0071080c080351054440400200307101c0d906000a003d00345d4040240c00c941d04c02d540f00800040c0000003800a01414403480c20010001c1580412089008102e10300c003824856036a0744021000b40454242000e62000030703c000381c82100f07180043c0c0601c0d0040311190f85147e00c0c5444040f01e1503a003c01c602c1c1000080720307521008201c0d00e8000100b480c011480040d80900d0f20320010901103102014a003481284c0c04594155107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 903669622 1250 903668372 903668377
    0xc031220030408122a04030210110a0602030f040c05030d0e0103052206090302061e0a02070804030b090c010906090503120f13060216050405090a03140c07060c1b0b 72
    0x402030030010351603898600e0103901038003540c04105041c080c2d5500b0080069507220782003a6040c0b95001342e022001400004450510072800040e400c0f800c0d4001c0d07600364500c60200e13440c0301c5901e40d003941d1041365585e5035a000d0f80c0c41510b003020034009035024403040c824440b03080401800200c0060000d450260f8010f410343d80c40c5844641410380c0c03200000d410080f03d403107048001d0100841948480b4242c42c02c0380040c0190002900107224500000e41100c00d45004002d134a001c0805448444d42c03803072a140007030b5005240448684030180030000014214400c02402030a43c0405090302c0c40c0c11800040580020307500200c1040390014080105132404607401c10704116840f00b4641d1035812840e15a0b6a10800880344c038072480c2e02900044d480e6002c5401c20b40c1d0710711000d030320072401d81d0b90302004141c4400341c80352070154000e110b003200000c0c0110300c1058501c000003500c41c140b14003003000d01c0c18481598410700204400103000303420401c3c3e4000350605601c20001c14800300e030901000490740e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 903670872 1250 903669622 903669671
    0x1009031b06170601030f0c0507051e06010b090102121b010b060f12041103161701020327070f1508010503010c09121b180e07050f04200a0c0312 63
    0x2a01002c02190a6902c281c01c4102c00301c2216105100d0405441c000400c41d512612056845001c0c00401101c41302c00141c1d501600600c2100030010341c0d00b020b001e52043d034003151010b03055220344820382c07800740c1c4c00002400141c1c1c680c58160500f0400300714807600352401c1080140c850103041140200a141d144140c0f1020944516810740075035452500080d207a0003044059894895024001110400b01741c08205540400c4240d80300c1801e810200c03420b074001501c40c01c0650f801e64614451019408807100a90803526040b00c2c0e4030f03030340c0d090005203d07205504185064220a400e40c0403403030700b010348a401040b0036402080050305901000300005601d018281c2e00c440c00c030118900744280200143c0c000320700320b8007016459540707500080900c14140104130354142844050880000c020490400b1140d002c3c0a190203030b08080c0c03c010041000d00103403c0858a24a034560700d860048004c0d10106200392101c2c3d20b29410380c01c02a2003005a803009460040c01c1032403000c92104410b604501c00b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 903672122 1250 903670872 903670907
    0x90c0102060f220c141305090a1410050108100c08040c0302060901440613201201030506130c0506090607060c080403140408030405060d0204051009031b06 68
    0x3841e0f000e030010f9030503003407042c0040c044000ca142d0105009001c03480b419842c0d10100c40e12900460706c00512800e480303080f10041295040000a80041034040e003034842088488001c0d2109081d1039030301641114000c1e08615102c0d8031842814418032001d00c120742c416070080c1001c03456454150b42d13200b5074142d1808002c1c0544c00200f403480c1140d00480642485142e40142d000e00710a040a03140078500c07500b400480355220340b048800c261101481000e01034003026007100ca12941040c02000034141ca1900000aa1041c00c2401651803401c0302503c01880040c04080c0b05500d9402d08070300e401c030080c044804901c2035890120010f20344440c840c080b98001e0b99000e0301d562078117001034550701071017001030196801d02003450910b640c0820901e120724400e860b8080004052003110036103002d103014414195004001c14001440d021001d010140d9841402619054440700412510410281094049084140c0501c00c01249901c2605522146a42550704505d045402004c0c40404130070b894a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 903673372 1250 903672122 903672151
    0xa0501060b040521030906040b03040209061002101d07032001051614101d070e0c04033f141306030c0309060501140906042a03020c060f090c0102060f 66
    0x11070341c003413054400306c42001b031219854607a1030030301c0000c0c0d07441200e08a202e403e03920b000800e10f1a0403805802c2603005a0300074108046000000700040042c1e0802c40442e05440070500501c880420110008d0362052660004104022002101044202d06494184a41030000d03401c280e084003030f46085203400030400d0300260300c0800403074100140d044071100d40382d081451985819804070704a081d480b401d0012900c140b40d84851000010030180d581b6100d8100402042000c01da1441e14260a80000161070710800305682c2c0c00d005442c40c591905a0314a29010080c68654120705800c070480350301a202e0340785c41c00340010f9014800c400d025143c141aa01c07041400c5143c0704c3e9024254507035019108006958641d4403410002040b07040040c4540c0d07640e0000782c0b0301e0929005403c07440c80f1107216100c40140044010080c0ca00800b00d00d401c00d0303800d00600b104845e04100740d50150600140803500c6040c00604c981c1480041c0c0c1403241958851818082e240840013109070780901407800031171 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 903674622 1250 903673372 903673429
    0xd021f0603020d0206030c0d022b0c140c0f010c020105100f151b0c0b03090712080301030b041b0306050f161e0e04050103080306011e05030604020f09040e0a0501060b0405 75
    0x11f410b0090a0501002d81d102194003c400c07142002c8070101380506038912217060030310f11060401d555841180c080081d5001512500c3d01e4681c030080c02e0040394580031781e0280b800c01848282100d8105480c60010b039140c02c240180c00341c2c060a078001400c00c041102404e181041d604030006000c0740d0b050700400210b5502c442e81160754681a001996000b12041040c50ba2084003080541003590400392600032940300240199003154426031407a0b1145259086a19684550740c4881001340b0544000f2100c00708501071440ba0700860300610301c1504000390a05050030503002c134160003400750714a03840600e0400105904898840443c811095030703852491038440c0100c0e80c0801207100f05402c41d041000200401100d0b001031445031400382e07030740c2c2100030044003610242c00c1940801c10200d0010400300b20503040940040054000f01450240340040040104046521210316821f00c1d40140d8009410080280a40c100402241d4078050901c2c0c142000110b5a00b105004140e44400c043c4444 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 903675872 1250 903674622 903674641
    0xc16020103110336070312020309152a0a110319150b030307020a1a190302030f1f06050d09060c020f010f1404020906120d021f0603020d020603 63
    0x1800900324403a500d841c4e0802c4034080710b00203403491188035001000380e07880c001c405501c4c0d04103040d10203a80c01080680e281d6150621603404181c10642107002c20800d2200729150601c50000c043d8200940c41c1d50740303421042901000341114004811003108107034000701560005a40b18003150001ca11040124001000902d00740c132110524050900d0740c85000b050020004c6103294001075010b080c4031242c044002c0584905c00c81c200250f00442c4c403c01409a4086120505100c403010080f07645000c1c000c24000c5560106120350070000380c1c002007040074045511244a402810340d100e400301c00c0800d0791040800181c2d42c0140c10030000041105c01010045070400c802058200c030381000441c4903460000d4403003403810300c1c0e600290b007000c4804500c0280e611540070111a2081c800425440e41da0030040a500007800c01584101c0c403841c0d64503600300500c103095800e03000d42c00902181000014101044001c2a05050700da89000780410242e22182c0302c5407045541180c8450340c0e566000c000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 903677122 1250 903675872 903675881
    0xa09081218010507032702060406050f0903010603080307020c040603150b0d02060304050a02120304030c060f020c0310060923040b070c0f0803010303080c1323270702060c16020103 79
    0x40d80c00d40d40c00d03c0f0500400a4141e808042c2e0041e071007040011650f00350000450703550b4010f0000790089400c00007001001d124601500640480705c103030515002d40500040d081d00c1490300241d401c21400428070850a4040140d5103904509036411b00c911880c6861340d8030103480104154901a84031045210315503100c1260003201c3d81d0042001f0b07100e0a080c103100d80d584054000032406040d80f1040390050440c00410f0b141265070055198549a051910450701c1c60340d80a151070075403141c03201610302e941c0e0600080f022510220303000540d99141c4030310607090702c003d0405159940500d1100482d444407510f5800c0d40030340c008240d4506500e4145084070710464400300900305401102401c41005442c500a40c12a40680d031440e0a6440d03041c1e0140f5a0311031400624003440303122400b00610300b07240c864401c22401003c16007007241100c50201d443e84d556011a40752000391a0150714116900ca800709400411501c01006030703141142103140300f4480d15203134508412001143d003003160b210703030030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 903678372 1250 903677122 903677161
    0x302100909150801111602040b0d120f032409051b070c06120e1c050c030f030a060e06060f0904090206041508090c0f010503090c0a1203080a090812 65
    0x42089070314612030b0501c035007610794029000a5424040e42c0300001e201142950498125801002500c84081d4204001442c000c00360316084500d2181101c00300b034800075852050010741d21004207040841c08000c0c01c1b98039207a603a00c00d500c54114200400d068008905042d034040d04000640d41d210340e07110396540d00d40c0c5103410303030380002c0054100304100400010000312009078031001c040c03d9121901d20140d032840d00f820441d550040b2444610300d010489510a0f000160910514082d201003840741141d00c60541e40450010010130b0120340c41c494032443c002031911640b000390a091000000790203104a500c4421000008a41c100080d40c0301d5010740d240c0c07980200600c0c0d4850303941414401280c0760400490200c2c030307601c000038901e80c030100b08005002c0d802060410031010000056030103030005041c41001d84a5001d865819885900503100503109207030420340c00b190707203280080000030000d00f003240850030019a1030004132800181c40c2da00310061a07822050b81d8049104034640000b40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 903679622 1250 903678372 903678389
    0x7080c1b0c040903090828080307140c0a050c0315070c0606080613140604080d090606090e060103050708031204030c020d170d1a330c1e0a03020703021009 68
    0x10203c804c040c5c00210650480d43d1031070595120790b44100140183c00780024017804050411401c81d40014034080c000c581c006503e00303004020075064000e022003900510400007003540112406c2c82480004c200000201030210f00400407000c80206400206d01c02030070750700620014030604001c11060f500302401910040044030300520700350f01d14405002c1405021b5074428880100d00c10110004580c0d940b085800030f0145140803101c20b42d9600409081d50244c2c0ca480e60340c400420b0315401030145480c2d80742c450006155650440c00c0280c1001c11030350000e4110303401042659075235901103a640d03a0298150401981581d25400460b41d200408040240541640c41200180c04003000203080203030304e004030800c65000140e00c1020600301c00502541e000803920011410400e5541611502541782e02e43c074030810708e040b164010141c120050902194200c4120800210f0450000c8110580060000e115441403a200070791039080d1800064000d40210103d031480c81d00408542c40181100c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 903680872 1250 903679622 903679631
    0x1020f0a08030f070f0207030803060d05010501080d030e07150f030f05131e0305070821011410030504080a12020c0f0109050705040c120504020f04020f030f07080c1b0c04 75
    0xd2034545065842102c8241e02c3c0d00c5a03d001c20100c0f48501446022590f0355001000360504580760700100d6000205110ba100003040307100c40010b0f100b03000e02802400c0403030050000c031456400c081e050310360392802514598414602003044040400201241d03c40da030030014880208030074101e020302800f0352102240e9042206005841010007054820180660002d1040341a0384002401908070850040e0008109010241c0400c82d06e50043c10007400360f40307002d4070608112140c200301c10000d80c0401115000c400e400c0040707050002d2022200c80c11890f04112500d4503a90341090f41c020042017901700030703031104400c1c106950360741104c454032a05000c40d12014680a40d8070701070640c1040446090041590000340c1e400c0500a00c00c00b011551180510444503100c1c20300203000040059038090050481e849807611548010610f404540d80c44a50368501200045203004015054504018241d01080411295481524000c0e130000c03800200c3c0091090700304c1d10b084481c90303e665000340340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 903682122 1250 903680872 903680893
    0x30209041a030c040203190b1f02031810080a090218130303061a0a1211040303030603052e1505030303090303011827031b060209010210230601020f 65
    0x19200510224904038211183c4900c10401d10050f4041a61032850081d0091140c108000c0c41e07800041811b4030103801c001c007448417070072a002c81c150b285000d00302503040010818040c00c06e6030000b105000c001d5030a09101d0200724401032010388001c1c60800441e07a91800c6404644d90f4001034082c081d650010b542d4541880c2201c542c0510421604501080c5003100000c4c1000c1c0641403076000d48260680942004543c8500f079134280f40303440964025070703654403a50070482c400030060710185000790ba001a2f10740c21864003903d1b10f00c0202e40208280d0100c100f0180b040b05a48040402c040307861000300e0b1321240300c2001e0b1200d40b00c6421465250001104001d00e80a00002840c12600c40c0c000041d0403100600e1b007070f4222031280c100e645806c0c02079944000700000014520b00340c4d43c4030b0303c3e128084080f200003242c1c9030107a10008994181d00001e210019603030401400e4a21001e151081200e000b010b920750303803015403d41d00000c01544010028220761300a2045180c51128442a501e08001c2c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 903683372 1250 903682122 903682151
    0xd0207210b040b1501021b0105030702150a1d0c090c0904090c091a1002030a0c0c05190303020c011409040510080a03090306060b0403021305280203060a0e13030305040303020904 78
    0x1c0403203004840032290482540f540d880004c07047c011460400c0110030f620058001195a03a100404100549c4200101d96550304095003c2501c6845580340c0000c03a03c500c00c00c103085a9080000702d8415070301150b80c00e0981e5540108042d00402c5038413070241e440d0040740c0410094014941d02402201c00d40d0400620701e01c4030b401500044600715445510031414104011403403003111800e50040c2c2c41030021108460103414240d4180f4001e603502d1016a0b41d6100042500f01e030011074203107512030102c0820030941c04000c020b41050342424201465100101441c11034010901e0280c482d94540c03003ca100400c0d00c12051000d0b004020955800a102e414013404000092200701d0303110f494080c0000c4c918804c0340c02d80741503d90060803049140c3ca44081c0701c02600c07025000042c40080303002d000441c60640907003c03d03946030b1280050b80302e260500070006032404a6100070800d00752001086541c0c0c080658140c090355040c1000100c42d107441c24200d00078043c1960054109207031450851800b41c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 903684622 1250 903683372 903683393
    0x40803090a09020f04061b0c18140106020c0d06021204200a03081903060e0915060906150f25111801061b0507091d0d0207210b04 57
    0x842501c489025540d03404500e03040f8424003000050503041840180084e82c40b030040600f4281045050203170000351520744548111455000700c116150380e010902c03a40d03585000744070720304007800b110030007070741c90200065281c0714042c084610401c104a04070040024503030548604d042144008030fa00d10706860281400c0101c100440e20050740001a01c0852070f003840f101e000d4030b90103084a17003013801c0c0300400c6410711a00100740040c0742d02c409002c1501c444008056100302c035240004c2c4040d40e144680b0f038011500143c5680d006000314000c10209031942040000b0a0024414150b130b122150803900d8500d01582a81c8420780e882c071041c081c110360149026450312805028804103040f0300341c04015900e540402c500b20005240001000f801e4001d400035881e904656581100403c21542d92608100f03c076000118071503036862862042e01c41121040034440c1d201402408848502369021f95560554400c00012100304c0d140c218174640880c0c442c00409074404415001402c16140000d10b50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 903685872 1250 903684622 903684637
    0x10f20060a023402010c060e0d02010c091e030201050a1803030e100509090105040e0a06020f03090c060408120901050705191209031104090302010b120a12030608150a11040803 77
    0x10140ca0001e88454030b6420048450b10301e40c0d001e00502d28510380d0041d10a0030b00918191f607220758821801003400800e200c0d183c6100e4241d0b000103400d08008001a101e000940c00c60029000503110b08141d6074880d1855005590302400c0841d152926020704a6040440c46403410312098501c01c00020190026405000c192084940044003000404120359074060030155541c0140356400400550400c1d903c051312558400c42502e41c5882da5455903400c3e40c0c040008544d0808000041000e031905c01c1c0301201400d041200c455107041d28203051a9550700400a0421a501002400c604d141e07002e40c040725046603001d000c2c0c40c81c0400c0001c2090300724101050540d90748090135130320a880e40c4140816010b0b2a80f0940c43c0420400c0002407200a00050000701c09540d43d070001e8002c80d0340c0d40d540b081c10451840c8020f04c9809001d20301000e14000e4400c495090600b001c10a21504030017003980d80c101d42e000c035906001d6955101140001c2c2501800c1141107079400100400c014a000c001000d54 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 903687122 1250 903685872 903685897
    0x509010c2f07060f17061c020303040b0a18091404030509031c02030d0f1e11070f0b010f05040506010c0f050c060f0901080c072406050301020a0503061c02010f20060a02 74
    0x2681c2c0d007802c0381042e00c80c00300c44041c1d01c5401d41030b583c051f43d00c8106038851034030b002500b02e03401c281d1590340f9084182d00070b00c0220045a46019040c0114908902a5000d014000801c1c0306510f004031106004078005403000381400800b0030202e42d070380c50800c51500ca4030340e0340003807a41e10310b4181c201a440f6030202e4081401541808845014103e40d800f9560720803003055446c00703a020030703414104002d003104e10511404240800c003003000f2404455080c44918002d601941c0380f949484003000a107440c5920a034061424a4100326890f03810074515007140d6040180418426014a829030504601100250784130354003140f0000d82401010141850410a0f01c444040e074131081e02c2078000e80070303980b070041021551003054400303c20703184c410fd0308404203000003050450b1118006402c0e0781025590800040010081108520301021403104160b25400c3da40311308401500000c10340c030000c403004018010b05000140c4461409251503624a480307509075021802c0800200300a94002c4540618 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 903688372 1250 903687122 903687137
    0x21120d0b0907140a0e060301061e0305131121030d06060c150c09030f06090c0914011a09060c0604020307050604081f06090516030509010c2f07060f 65
    0x1030300e0614078501d81c000d40d030702c1e00c03000810720f081a0030320055888891800200030450f4256a016112200a103000e8192601c800e400101c1031080880c4090f032000250003010f08000c00e00c1940d010319644d50564030b80125181d90000c064001240c5682a02c0c400300f40e0480c1039460354070190700c0110103040200c0e100001840781a0303442808403040c07004c5805c0034000b80c54200c2030b41e01840c1c4c50ba0000040c10058200f50b00c0300d41e82d03510307241010001003405885454440b00f060301000b110000c2d20028002030b81c0c0400c00e840c01c00142101119050040d01c400013041e84010040602d21002e40c1c0450f00c0090403659a4503140b50790a45919042d90224028401c64070041018507200081e01c094407080f0000300390b0205080320308030920380c410182d58513055440b1f00100c3d5100c00b17805114420003040b0b59450461200c0721004084038070040c029516179240c1176641c1c005030b41c40b22500a0045120200700390179400500396401d41c0c1d1100d1050400303072140079400111150001b82081e0500c296490b40360 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 903689622 1250 903688372 903688391
    0xc0203070b0705281401060f0f031109070509120c0a051002280b090102030f070203090a03020402090609040213080f07050901031e0c090207150b0a0521120d 69
    0x1801042e00c02041034022010301055103240d440c44a00100b14100400110012901c5008042c0e1403100d041000d03075103410f014065810306060500042c80c20200301920780b80b45469100142030124400351041d074201d008100120300c01c1c3c0c180c42411000030951a032800310125119941e9527010703007003170041c40500c034005514502060340380106080764000e08905420b14a9402c588002c2d201011791a0005034506004070b0301800f443d910401d460000140e40c1d042604d004900000010140d034115401004896402d407200c090b500c007100e0b0b051f1005601d50420030009100b40c06500c8519400c54404558101140300340144c841c00c6400b140252035150f42c0510030f0548491090044c0e40d040742402c00108000b070b84510a141d900340c2041024040c1000f5580c0756040b020295000808094002c03030020240000500c2c035a0101600080411002c01d108000c41e4407941c25200d428426100d0003c1d0790404c0d00c0c01120b1581098480003a2030380d140041e101d4000c1500107070354441641d4581001603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 903690872 1250 903689622 903689639
    0x8011109120d0e1c050d0327051f18030c02090a020717030403120c02011a04050f15190e0106030e1906020307050c1902030f030414010309020105040b03070c020307 72
    0x20000302d001980d80d01e030600c00800521050944401003060b003100a0700751600442d0b4144200c14684002ea500403c11206e00700030b02495a0150328006d01e08100c40b05800300162000690b0710100d601c0f0004480c00d020b0444400c8028110240304500103840c1004600c10503600000780086940b00300c9200078503481e842501e00403401030a80040082d00840745135000905038a0145521a201385020841721600000d000140c5400364608005030f03445905030307a01c81081642220405800351400c001a107050003164610395406000701004d043c501c181d030000e5840380c480450004c5542100e02c0f110a0799400c0d5591404802d100703400000345040140308545e9008208205034100700b2000d00c04a40380c0380c41d400c00a5001404420a000c8100028042000b0a01010081c0011030b000380036508014010700d410300a02d144441c20a41080009002c81d11243c0f0401484039000c0c43e000520380c540c0e1005079442d21454010a80350300001c801c003d2182e0b40194408a841d02c20303810760740344581c1e41120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 903692122 1250 903690872 903690883
    0x91f03060903111902010c240e1e06060d0c1203210204230418030503090d08060d11040f0518010e0304081e011506020a14120a1101060801110912 64
    0x840241080d622500d001756118110182425005081c40d001603c000e689000d0f0b0080404510035400340ca6003070541070000b05001d50039445120b1028610140106462240c030303407600a09030f41c420001d4250b140c040c002e0701280310014007459581c10741e88064605000c0d01c0003d00b10b80300d031810407000001c47c020794024000e07103088682c0d204041c2102c114821031114000d002c0c9518642041d980e02002030070802122030340591f180261100c55490800458441c00c00c82d03d1014502400000020300000d5294011038001c1e907900100790250a62450340050094a02c001e00c1000041c02c0c907040c800020107000030304104c2040d20000f000311130b11110310980c8038041c5101e405901e800500400740c0302d0a14401d601290714080d0300008403807042d1134198808241a800060050b0700504000c3d0030840b40c01101070b4080c40c9800104081e240e82450742102d8840c0c840b14608101c86030b45039644205094000704058401e99000b4000e803440340c950250f654105030000c030301c0341a80d141c0c82880202d02107103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 903693372 1250 903692122 903692143
    0x904090812040f20150912030d0606080c040807060c030509030a11090a060b04061107120605010303080f0c040302040216020d080c0d1e260a020403020405180606091f0306090311 78
    0x15480c0030b84038110005410002c0c11b5904000e40001106200310180000d00007150100c02c001001414080c00401030b010007811800c1100307041005000140c40000d401e011a00a46040e0504040b80d180c00c882e01d0140f80748540d01845560b81d0241042903004a0582c0c0d08400d44401f1030664039401048107441441c402d0f0f200d4a13004100910100707220b15001d4a0240344070040380c0d41c0541d00c106c1c2c000c0348910860107039000ca56900041c002c150b4491501a08a24111400e040320f04208416541d5841241f01c028803881d80000d80000c1007880300d00b04200c15400402907211143d0608195110f0b42c015200c41c00180101c0045140d003070b0058020002240900500450600503000c003a1030100c0d01e0176002040005150300100c2c0844101001c6100310029100542c5440c41d5205100030744101a0a152441030111155410300f200015402e0340440c0468030480d81e81c880e0710104521a0a046154400007000c0a0220501140350400e00031036119580310102106404041c50b04c40303000b500c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 903694622 1250 903693372 903693379
    0x70308120613052509030503030405030d0c02070b03162607030b040c020c193b040203060a0515060a1808150c0c1501060e03060c0f0904090812040f20 66
    0x4982d0109201d100d09404c40010740c0c1c1010b1003101d03140c0c1c5540785141c01c11507007118a588001424100410f003800b03a9803050016000410046081c6401c001c0640001001008142098403c0c1c080300c0c0e2003140c98481d948080302601020780e14507401c0701207103035084a400c40401d0402c282140ca44c24180f280302e112442c030754040d095440c81442005410b12249508500164610b54081030703400b102050b50440c500c5908168210b0030354042048403080c0007030181d210355007030301e8104009603c010594540c00780440c1e90014403a580e9a0802202180750a01140c000720017113042c4082e1a002241440d800c00e140601003806613035401543e41c0c030740710105004220480305000c1008600b45c1d0002d49400c080b50810fa0700b4801c0c1c80602d8070f013102d000748d019600140c400d52154665040611000e500900c400e08418940040c0c500580314a104040c811401140e03a0790545041c400c940040d14044a0380e48005a1541040c1c200841c00021514050302d80c0c819400c26105140380c0c03c0d40c058610b01010f07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 903695872 1250 903694622 903694651
    0x9060e060f1608040e040c0806070503181e070e01120c050111012307030510050a170109120c05390d0b040b090706020c150c07030812061305 62
    0x5401010960b0440d44020404441d0195030000003090180034201a0044101c41c00e001c1c605801d0043c954011a44043d01541004007406041741d840343c1103a900a09106070680014681c0341581d2070288056020042016001784408a02102103441c0c01202c0c1c01000451081e600c1d814001086c103031042d070003098610400000c001c00c0d401051020380380c88614000180074503004005d03080e180319003c08901c0c041230080c100b000854141c454550081e5036855100407041c04d00300403c040d2100e6010300c0d084180490380390b2601d01800d40080d824594170550b414101c40c1201009084030410ba030b003c941c203018003c101d44003042009410301c40144030240d4940b490b12120b40c2030b408649290080350304508807031048004604040c1c004c0d07010f18402d0326002e03118070b04504030604121841d0401011900400d107101140e503148841564040c01141da00c44d950480c074025945004040c0c1e1000741a200c020900b51030405890341706910444c401e961012821260482410458004940000d81702c04c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 903697122 1250 903695872 903695887
    0x40506010f3003050c0105010e070f0503070914040e0316120c0c051e21061e01052b08090103060b071a0411031501051c0f0b0603030f16020109060e06 66
    0xb90020400940241003581c81d000080c070003642034550907001440001008003e01481583c040c15028000c091460114110b0070b00030401852080940b198a04420130705070015010b0740c3d1940562000d0a50314211781c0d46007145080c601180040703403010b50f010114200e07980300c160f00484140007410307804440d4040442c10300081019850241003040314016040d011300307904c1d8136100003e8680d03004103401ca11130201003503040d51801c24020306102018804440c821000c0d0b501c1115139064400403242488030205501c9484001ca04418000560360040d0703405505000100b0028100b151007a68180840c83c0c9400011941d03205030754004000d060714480040b1180c072a080e02c0341d00a0701c20000c60340e80518800009290a0403130b1b42c910068140580100701c640f52141020240810486201981000d00d489219420180400c003800380c0070800c0c00606184c3c2c0c00d100300c511003021101c0e2242c50341c090400b103003802141404c040b0b000c18644000440e2003401042d51801640c1c00421071b03840d1168 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 903698372 1250 903697122 903697199
    0x1b0604120807050d1806060b1806041a0306060903071805160504140a0510030e0105010f08033406050103030f1e210203010b0c0d1103040e070215040506010f 69
    0x41070349001c01400f003c40c40400022002d001d19030040c208440f126403140406046411824440c00c1000cac41414200000c0108451417040c4085406001e4017150301d0341e0740e03000400c003103101d4012890b41c9030142340b50116a060410000851624986c941003216a0f00d080207800b0003018020600041141440f040007a03190300a007444090307a0242200080c070b56202e01007503440820340155408651114406288001c091081d940180030561414600501d0000310325120702c1522160000e80d25000c401c25003100f407142d0154010b4810ba561170084410382d040901c0284000c2c0421000a0049034040310314038072507581d000f007601c18041d42c2a00000c0803c82603400c22880000402d0840200c002121f000c81c0f584080d50007444a0401b543d907071103000204c41d08201e802c2d043c407418072040420000c4240f500205842c1a1858062180003d8443c093f06030300d4035140f4084c1c0c0c10030504900c104010448007054080c105c40000000b00340083d1030b01c0c01e1000c5440c01800045010f16461005074040c0c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 903699622 1250 903698372 903698381
    0x150a0e0907170f19290610142208030703031413111e040504151103100b030a020702030102031602010c0e01022a130c090509130b0406021b0604120807050d 68
    0x522680d0410380102c4d030300b8903014505804500401c0858805c0f400c104081c245132000c200301070594906141080140f40c8040441c0c010609140fa02180e6590310944482020300404040c1c42c0348000c4a464111502e4000c000c0d040d08540b2038002c0101d100402c05a41150405201c165404451034003c4024401400804d020740c40507a81007044403851912540c440c0e106807801140103901815600749443c107118180d0b040d00c003121100501c20000c004d92000c2d1440418162012103108035a42d441e41040f4a02a000f94130f40654075500c0007092064818000014200c261883d4000b4000040408401c0c2c800c010300341241805a0059806001c41c21122000d084245174045040d628200e0314502041c407001c410742c0c0c1261440d0b603404129a685401c040c03180020030044982c04282d02d0000b200c03187c900c107160001090315001c44042001c0107515010b44d10154010140000d500d0701c003103c03a036a00e00d0b0544007a500c03c80d1680e1640241c80c4619181403040301d182d1205403500d0b100700042d10007007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 903700872 1250 903699622 903699673
    0xb1e040b101d0604051804050f0c060f090604030b071e0906120e0115060f110c13090611032d040f0f110a060305060108100608150a0e0907170f 63
    0x83d104000214050703840154030801c0f600d02007000c0714540307881c0c90704a00d480d101c450204419841810392006541e100802c5400003100c185100c1d454081c518040b800d5800349800c01011200c0d81c4080003003aa0b80032510304040400011a51801c401e24901681c0f071b800d00e8054030703001540c9506107003482421030f080396040c0885540005060700d2204d80002c45500c2a0f0080000600340c1422110001e40c804200e545101c1580042c01860480e800020b01040002131018041c5803213443d11002d00c012070380000920900f59035a11b6481c070340408148001112801c1c640f106110038182c26180c007124159081c0304985c8004140b1041e482030300c0c1c1240c2c03842520001c1307941d01c0603015103402c1515001070f060020006500d020071b0908220300058810b210080c6100c0c0c0c69618000c0810804d0760280c00e8a030400040c03d8480e0485c01d9280208928121903000028400120300502c4000d000010745082112045400904840c00e00518543c0b944001071096200741d1115001030040ea84410700006030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 903702122 1250 903700872 903700879
    0x409080405030109030309050709060506030f0411031e21090d0804090f090303060b070c03030315080f0307030215040807021e130509061b0409020901030b1e040b101d 73
    0x50540d01c00c002400c0d034030a6201100000d0720b841d030003001c0000c2084444060890010f081c46824203080114015000003404004820401c5020401780248508034a8800c40054191011400c062030b200a50460802c1440c0c000e01c1007140c2003003050410b0040b0400a9120410146030580403010004608a1a0030a49108008100c005001e181d10310079000c2d45901c001e00400c1481d03540c1400740427500c081d400071541140401101c0009407075010520143ea40c14103001803000844035100c450501c00781c100300c145214840c854001050000003809a0921070fa08031611f449520f00480c4941d00284d8004050710428000c400042c0740c40c0c004180c105a140e400300c0344106529000400c101042c1e82554081a40e80d0f062100149081c4070301070b0302c1800c0e680d402c4440c1c2d1210722102e00d24410381c8140480281d01041c0c10403030f0382c4290088018144010005118002040100100303c2501311041e40316528003640d440e01400c204034218206001e85e12030040303e05500c2d000c0c4000512855500d5413 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 903703372 1250 903702122 903702127
    0xd14090a080d0314060103050c030703050421030501090b01090803041a270a05041b0813050a0506160309021c0c09020f04091d070b070303110409020c0d030504020f040908 75
    0x1c1000040001c12494100c07540c1c0424008842103082e014288040c013014100341c1080c08100f0300d41c0c405030450343c014065140009140e541d03810510b0088550030601d900c102c022107100460142e058003d03c1c1a995403060070800c9052410054441d48c00600c540b2200d500244410080d8030804048044200312540e1110b2802d01c03030303141c0c004504c1d40032141c42d40c100000e540310407814201201240083d100c10740d0100092100050b0641181210b00b019100700088200050000c62604c2c2680400c198080d08840a14640340b03000c5440710720407075013000d1802140c90406d070014842d0180e04049600a000b845075104140d441110140002000356030083e0f21110000c1d03210810310081080c1404030700c5e0706468608090480060340d5100e41c00700242c0c48240c4159103424404a00e2604481c00c041049a0f24181450160058400100300b01c1c0d088401180000f0140b10580080c8241c0390081c082e00c00c2c40d1001c40064089a00c00ea80c06900720424103004016801d15a0202c1c140718081e020050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 903704622 1250 903703372 903703379
    0xf0e1f0e0103080703030e0d0516050c0d060b100e0d06020a03150b03090114010b040902031b030f010302100206070816030b06071a06090c070b040c050d030e0901080d14090a 76
    0x5080042a0b00807101180001000700c02d150341840f0f22001c5a00035000340c101f0740d00c105c1c002040b60003144130300b000140102e5030381f004014007000000020040139003904900c1c80c079802c8c070f50010040fa1502e42c0c080c42e80d01e413080101c0382c81111140c50325a80100728600040c000d80300c40e0000e411420300c42051541d00e00300781c0c00ca809448100301c020f061403441c141d961301d01a50000e0035242102c80c0c0075014500c81d40180134440708581600c064801640d00184c6035502c507406134002d001403071002c22142c0c034000103000306800076002180c181da000343c0712204107200e41102266103510484800c00010b100e000402c2055418010900f0380d020249404140c814694000900c180d01010040710103a015030140600352916404066018100300e6030b205c481c0c94046030b5040b40b489040741c01402520540001801c00844254400207002c025040d618012524030300900006154412140b107043c58000010721140c0c00100c481c000c203a9a40c0d00704545e200030000307102e00c1d001303c160154084001d55011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 903705872 1250 903704622 903704639
    0x507021507050a03120204181116150b0d08091509040606020609010e010605030d030b0103140405030a1d030c061605010e03030a0e121b0f010f02070c0f0e1f 69
    0x82400e030b4041c8010748880c60300741c40d018144241c0c04038400942d0b0f0044c0010031000700018280c03003402040306404601010160201c2a40788565498001041c10a040d510107020712082000549203810b94100003c20100c0204018103410311001008030740e04009507401030034403003003100f08409810b00c500d04200c80c000c000390030390304950021401a1f11041c02c00088480900034007a00d40c0d0005d00803ca80c0d401d0401198840310700c65441e000380350315800c3d0044e569100b68070001d00d00f001041e02500c02c3c10a8604503449502905040e80060b03405034881c400c101a0221042030408001c0c01010010480f0307003440b04079000000d00305403045c80d6403860341c0841c0081c06142000c441c1180a140c0e41d180c409590011203803100200151580100900700e908140036040b10354450b22404034680c0201d243c610717189400400104620320f5402e1502c45059024660040c203609441030b603035481c00c10b4484000e40304420551260303002c107080107400f10381c04008510b0034a0b40c1a407824a420549603ca46a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 903707122 1250 903705872 903705877
    0x7062001090c03110307081905070b0313081b070e06030c0a05032e09030f120c02030405060921030a122703020f0f0c0901060f120e010605090a0b1203120705070215 72
    0x1400c1c408c0362903d10103003c1100900002c0003500b0040000b40c1541003030507030803c410140c0900185081000200c007500e12051841420000f86441c0488075500d45440304140403080c2525294000e1044440309426480e055402030152500075008054811007110768101c0a03407040c08a4690384c0d8000000001d201250055400070360081d116603c0c802001c683c014400c00c8550f5661136201e00d400204040150f0100444c1e0880d901202c1c1246c5400c03441002071884d030000084100d400d0300503a01d49602c500007201a0440704060b032154036060341c1070445d4400360707515003d00f0002280011980440394138000c4000004600900c100c0c0d4180300607810240c644100303002c0c85084c503809024000e00a1900e00f80c1035002d403d813882c045200f90340c00310015042102403264540095100d040305403496100750300ca0001070800800590b0241401181000101044c13002d03213014081074400700c4d84076040002241c103c81903911024080b5681d0030303000c031880d8120b040700b2684201d0a41d036604480015801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 903708372 1250 903707122 903707143
    0xb030d2a080414010c050703020907050c0a0606050f030705090109050a020f0a080906060d0b07080a0f1401090b0913030507051203010602240105010906051b07062001090c0311030708 80
    0x2901c90391142002d1050110b000e030044081d040088a082c00c000140011500d80c003160360540f2405103548403c2010340e100e01403600003102912489500d03030f0501105800a01c01c4034419100d59002c00351040030b2548584c3c0780c2c010180c11001c0c4e1b400400400c91a03501580d070140c00900c0050400403030781d042a0700e950102c101c0400088800301804200e540c280304c06900800100d42045261a20360740c0e10344840c0d0700600d81c02c103000517100012419503044d04100600d00200f007007040456040310404800c0344080c080e0114581c034040034040d0604084c6101e40c020307155649804200c821680c2c00f01d5507030340207010840e541e025101301000010010130186020b05910340103000d01d500e448800201c03144803c04180c100c403442000400159800201c0791095a065240a581d1405550210070317004a203c0d9001d04c05100309000091100e610450a442840303160005018101d407114807a801d8903841100503140741c0074a00e040000554443c2c2c52510b085000c7e056411f050303900d01469040045149 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 903709622 1250 903708372 903708383
    0x120c160b06151e13150801300f0314030109150b03100506070c0b0d090201030b041a1c050d1e09230d05100203100501050315010507020a03050706020a0c08010b030d2a 73
    0x30060080c5501e148c0351440706060031903540030305010100c5ca0151201e44c1e10007c1e2422004043c03140902d072042c01c00050007909240e03819a0380d6901d130070340d03401002e80310110ba201d46521400031414041180440e4041d4981455825009080c807081113250350001c9404c44030401100b41c00aa0090000c014200e200f03c000000035001e026400054142c881d2800e50f180700300e00e040d501d800c05c0c00c02c508441300c50200985008480da5020a8413181c0c07000ca0200c0a4403510406195001c166485543c0f10202c021211210240860041e4140c2c0d00808034021448907034603900081101d0300301c014403000d0891009042e107043c091142c40b0715042560040000480540000400611107058402da000501080c64a10b00e1490240e44225208131418070b40e9040090000d0600c040d940c0700c00b40800655000310036180d8007070b03440401a580740c21030f0760220381c50484000d00062801c010b1041d00380511001e40a07103414209244101d5144e82180f216a030038000b15105824901c180e540c45c80000c51055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 903710872 1250 903709622 903709637
    0x30f072106230f1e121902010f0504030f172104030f020a080702040207020312040815150102060612071503090b0105090c120c160b06151e1315 63
    0x1850784030342880c45440380d80038982030215140c06499413241146240c0402d0004415151800001500c039810b821502d41e00780f00341c10207503140f20a440080b020b00e070702c06d03240c07031544040000040c0c0b8280220320000c0c3c200c140c40015040411550b9245000008440d000c2602d003482000d94032000c1c0b41525413003011100c8440800c420103030000700020340803030140000c0070781e041143e481406c5480b802d44024011a000700d618801c6403000c000408003201452000b40c0c075203440701ca04940d06d4001d0408518481d4901d0081030f15100721380110101804182d001e800103603500c5081c001d0b10500809130321014400c1d00380008200100048506c4591055a4041002d10040c241546150f00c180c000070b110340e030b21209010041400004403003001c4207c5814980c01c0e540c2030043c0c8a10f003e003800c403c41d810b0452801c0f80c2000100c0001170f00c1541e003140ca42c21a14001e012001860144401c5014a245014204071408071442c0c00351107040040c0d014030208039140da00e0520052200001500403079041c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 903712122 1250 903710872 903710909
    0x907062607171014150d0c05031911030a05060f15070606150507031b1e0506070806030c13090c0303080f0c03040f0305030a0f050129030f072106 64
    0x480041d0b0800303081012030b0015404c00c80807454001030410031a02c0341c40b5141801c1c070f006007814240d4403d4100b001e002c1106022007030010b80030760f0044030880405c4207120320045040020b4403501700300c054907040322030560303495424000003404050300c6a40d1002120103042c80c15500c1c1c03900a4840c4c0c00b454441900d810051403c074007529611380003059900010040c10b0901a40b00d4140c0e41155018500f02c19450030390b1140c0b0031804000000501510000d078200c18445c146445e808030399074890400c5035040c2d610301400700d45142003520700a50580101032111041d1910080142800d55120000940301031199254aa507000e1640100c020610301d1b010003030303981d0258451070b51228000603150329511702642c1d4680100110b150080c18400c011001c94103101c1540d104642d200c400c100c08000031758550b080b400d1050f02c000342032040c04d405044500610300103002542d0040b2031a00031054241c0b1340c0342c0700b44c030020180d1003090080c481402c0c901040d8910707800b80b0707402081c865016000200c1c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 903713372 1250 903712122 903712157
    0x806010309020d15151202011b0b0f010501091e0e060f090a0509071d040b07030e030c0106050a0602030a05030a0e011b120b0d051506030f030d020d0c03050907062607 73
    0x805409085288441010401c5031002458a46d01c02e5091811051002c0000700740d03603c1140159003d09803120703007420004000200780c0000d051f64000d0300d40e4034401e56a503400c44246840481c440c03600a031002020000c400d8183e80d80b5400c62401020480552030303110100d0040903084540007240d036100e40c02d100c81e419050000b0301c094440c00c1d0843c0300c41815908410060310001d4002011003d007500042e030000d00ca0750000c2c07101050481943d545840c03e40b0107502a1015009843c4950415907001441038000411903641508540fa4507065507282c0d01100000c110402007041b0035501c40c40d0b000d10003624041c00d200c00c050302d5101c8174000c400000c040c00c200d0703111701c4010f07008100e54004a00481d000150710b805060200f848546190f40e1070005c43d082c600190f0040d400c62201081100000c403039900980310010300f10404000c0070207001707403c03419558182c60766007094000000611020b4454800015852840b403415420038840e5941046825000c60351040015180c211f0701c1c0c405032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 903714622 1250 903713372 903713381
    0x906090605011217070305070f050f0106090203150f040603062a02072301021c031a040c0507140a08030f010305010b0f100f02100e0606030f0f0d0806010309020d15 72
    0x10220703031507869481c06951140c4403408503003203c80313807140c01040d18005c1510810444410640c005002c82407401c0c0c0c3d1034400e1381c810b019415a5031135420a000801c84546c7c0d40300780d0b0304c120103280e00200050415411300c00c0d8910314107c0180c00031349803000400070606c00d0269000010703040015140c9020411807021106038030300460340071074000101c00c0114145a0084151100424020f42e05062000d80140d140240c61000100341034501350001c00f010b5010f0703224862017691003031121001c84100082004070b82413407000d40082142402684007003103d040807046070241c85401c58400e4071050725a00c00f96001150400314101300f40300140100b06c800e000f04145100c00391441707011307004820300058a00c0d019188480401c801c5610403056180b007005090914401c0f86402c00c10724007910302541d1a84421100c560282c03040400390000c480000074450720790100c03140941344c1c589030340a003113400e50380c043c01c00760416484040c04c0c0003583d640d405504105201d42903003c103070504040c10300c6c10f40c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 903715872 1250 903714622 903714629
    0x1b070f060e0f040b030c090a0c090503190b0426090a05010c1a060f06190311031605031503030a02010e120f0304140a150504030e0a14041e090609060501 67
    0x314031078a5920300d6850703252010368041002c4401040c00108400403030300e020100700c5031a0340f2487d10002d0159030480390f40504202000350f503e20751030766154014103917a07c038068410510900c1710800c1d18085102418035640241c8030b1400360703d2100c1c0c013052040e07502c110b4482c02400c6541c00540030740ca0740b81c00d82140008000078203014204202a03203030b103a0200384483d500c401032404000040d48e9642c80c4e044140030340100074881500c900710400c0c0310100c429404420004649004080d05040005105070b81c40f03041c03403c00884200c0402807044915400250405294805a20101900d0755080c40505081070305940000381d01a5103441c56450141c403a0001683c2c0d080820000500c1401181201d40c0190482c100324490000c10361214580702104038040c00d01c00c00e1112070100c4c1e00560708528081c601a503250040e0594107003c005866a09100f60b41c0c0750707803520f807500e00386050a07000546190904000810100e28440001041d035507803074000c40f01c50355a4905d0380c0401c4060320440b0b000d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 903717122 1250 903715872 903715877
    0x616020d030b0f040b0109090f020910051606090609020612160e01020307030810030c031a0106020606010503150112020d06090e0f0c0108250e0f01030e0606060f1b070f06 75
    0xb400701c814046010110a0320a850060307483d82d050a509034050b1205000a0603581420410300581400c040025000300c2c0c40c55100780ca03000039101c01184901d05803840c1c054034a001c6c807074020480d034900c001402c40d180d00b06c035070342d45070741e40c100140c1c3d41c500141440c141a890a28510f1402822030388807440400c01c0e60040c881e14580c200e0141c1d0f4000140e0350010360604cc4a481c1c0d84038601d111021040c039071b00007003259124050200c00c110b400d4039043c6000400840d1001681d8076081d050703840c1c00c02250b00078006542440000c049a2100101c00381d540c6042c14100814011003a2802c01e030703408420f1035080d46460303c0342005034540034401c0200d10301d51074002e00000d440c00e41c011526800da14401a04000300322001c111959551070600030036450003200c4050f0180b40840150280385d0840c03045100d03129044560285502038010407884030048000342c0860386d603003002c010346900f1405811070510028404001c554440c09440950f100c40d9000078900705280c040b00741820002d0f50000000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 903718372 1250 903717122 903717131
    0x504170f0109230f0319090503070303020d110c0d06180210200303010e07050c070b0d2018150c071212050c070527040c0e010f05010c1707050616020d03 67
    0x1d1300300100036900000b000982880c201145840101c0341202242c01a0703a0500950034008105600084e07035620b00038180d02c404a05c1210040003d4071810355030141500409200841c00000b20141d0040c90703000c40c0350b4140b0020805a0300480c4998005070500004540d05e4105c0404004e0f44940920356403070031000652440d81031441c0b085e401d0350701801c0340041c44400320703a050407906d0510504007e40381c103443c0c40c2e4071448401504409400e004c03101c01070070040d1002c3d0048143c4410212001d100000701c07241d101000c204d050002c2400580101a41c2002c28404450307000d0782807181c90001e040300040040610203505141c0c090003d070900e8041440810026000e8031030b0082010790449104a402e90002d00703109070401840e9600741112002c0030050f004000800101c05030f1841601d14815080c01681c1e00c40ca000103c5014a00842c0d000c2081014210b000958140c1c481528801410200f810009503694103450000107540d80740e0300c410070204101c07505604201c070804200d1140360500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 903719622 1250 903718372 903718393
    0x13180c0f0807080a12020a080d0203100504020414010e0102120c0a0b06010302191119060203151504030f081603091e0f12020a1e080114070504170f010923 68
    0x1e58804c800c00008100d500d61070700b0a801580280f1055001c1a0001111640d40701c002c0190f0009500031100b41100718945030b400b04960821748280c6059400481caa01e0512030240e00554940c1500702103030381148540c000f44003d243c0520302034000d4000d0342006041548061606480c0401c1c01009181090300c1408040110340500c0d003948020b0419003018601490001c040b14104025420340c03c0d040101c90288000b00549a8003c0d80300303805400360403507070181083c2084081a400031051240000920080c404500d40d010072010a0b4403810095152401122240041c4d011000c1c0c1034010500003101040207248a8418420001d8004a400f409600341391716410145603d00801080340182d0140780115100c41061601403c1414000d81c99484e10b084240c0500705680240c03034855092070b0390190810501d240d19800703214980c40c0c06017418288811030203040004080840b103031240c900c6c0c5200781902840b070791111500600e0b07209410381010303810510428051209034244da0020180a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 903720872 1250 903719622 903719639
    0xf06030902040506032b03110313020910050a14060d0908040518040b15121c09170601120c12050109062f03060a0f080d0f0801080c13180c0f0807 64
    0x1c149030160002400b804184406d0110014511450358045034200002071200e801241c2100d035417120b108a82c80c5200755590750001035024001d03c5003940100c600c0c001481001c2c0030041d02042d560380a44a1030610403c4903c042c01e03202d034001c00307944804001070144850704000c414030f0314018000c25800420704140ea24666404801080080300890b1440d081826541d144102382688604a08580902c044d041d1500e6080000701c0303038003021546418001a85e804600340718036a400203c2e010304001da19080301d040c01c11098441c100ca084103c1034020400e41001d503100c03c0500e0181000040c03a40030b80ca800c030116a804000c00c1240303680c17880340d1707032000c3d86d040c8004010000d100c0c85c4c1c9440c1c0d11303000301103410806950480082900d85c503d010a1020001507055005001c030b64030780c80750352001d035410b031902442800341900940005510303000d6801e00454142111223500300c0044d40d41802030154240d46040c8030100ca4080c0d00f000d04200d4400154004000f404142c0041e000d118600500c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 903722122 1250 903720872 903720913
    0xa030207090c030b041b0306080f1504050705060307020d0e060c0c01270905220f0b040c0306060b0304031818051e041505100509010905100f0603090204050603 70
    0x1070380c40c1580c49480b031004080c4241c100140c08440600280460068428400300101c100100200000d16000300007400000c0054624007010700b0f08081c00144a88a84400040600803c140c400d84644140090913484800c01544a48080da01910b045200c0e04c100801d9150130580440c4a02c030306100d2544481c1001c1442c1210003403d00300300100d0200520903080b03094116000d8a4900000c080001301c2c8041501722501c44c07250400c19000003099414614018080d852002e06040d07072049801002581803030090342c000c1e00036111a00382c05c4d034076035541c8280c92040d080120004404010700003090303005400c2440040c4c42911040720607003401c1914220340700381d11885881c80c0d21440401c00d00c01040b00051440002080d94001074541410581c030130001c21410105102e10348400209540c500030000e0f825503100030600811030b403a2110b800050030001c0c184400082c04080009132458022003400700803c1503031408900d411a9004000840700010a03d40c0203800c04000c0c00078003c800e40c0d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 903723372 1250 903722122 903722129
    0x913202841030907053601030b060105220f150c031407060902030f0a03140406020601090903030b102c0a0603090c091109092d1807090c080105030a030207 68
    0x240780c03243e8985648601e40b40c142d038800c0f9080009500c861214005030841007440180c08414045280c090840030b0310924800d00c4007070486811030000c40e520358820401405182c0b54290602c0840850740004036400c8040ea0100440d02e09201307080100c101d034000015580005804c22218050164402820440b40c03041c0d071040c14000080c8000c104203550b88800c061513005001c49134403600c0024070741d80e6403d00010070780116685040502803c1600c1c4110340a0369041e82c090201c507460140041d000d480c440804800b07058031005080e14940b05c0350b20351214007a480e540d0844115440e4600000c092111010ba6845601422440740e90348400f00142d0450346285000103901840b400c0c0032001401982000c0201800c002e01070340c04907100d4020303064600040750b00340e410b034403050003e001032400d2a81d005070b00d009041c603100e440e00c5040381e4181d108002041241d60055440812420315419810035008980c4c3c0d40010492258022210380c0900401c2d00200720b03c80168034040d646460390b12 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 903724622 1250 903723372 903723497
    0x509090f1023040501020c010b0307030302031e0f030f0412030e06010e04080c0d050408070506121504110c0f0106170a0f03140a0509132028 62
    0x400840615803100c070501c461100102c4035032290308003440e01e24081e6200501d818443e40c2070a444481901e4040707915400c50340d05070021858007804034142e074a01c440b00040d8050030042400784103020300f01c1e2401140f04403540043c0030312a10746894000f0131103440c0c2c1c02c2003081515111b130b00314002d000000e58605580c102d60418a8698031403802c0c140030300c18403070488820700582d40d41800d00350b0000050003d445046003075034482030300c071002e01c074443c000c501944245a19000208080084c0a24500c2d5100009030010400942c01d42c00d01a041d4803c048000450303000c9000515420300a210f14001b40c00342c807091442023141c1c0c2c20f56580d07500000170b029101e40b5805402e401014080c105256000b4003001505440354060707840503200740c00800d440c50140e40107804880c200002841a0004001320481711f005c00d060048038280d0f150464102d5002c20f8921030301d81d14220343d000321b02d0344c132002e4140e4940041640000f815110001c0011001507030040710079103030340c0f01d402c20b4045400c00350707004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 903725872 1250 903724622 903724631
    0x610050a0303052206020a0b09010c050a1112030c070b010b0901141c051005091810020c10020708040305070f060e06071b03030809010c051c0b0120070509090f10 71
    0x10061650b224818010340400c40100d04c0004184e0703000311354020b26134000d40c2c50200340c0d90780c1c112441c01e0f9114625164000342042002044190052079517182268070001164160f800f500c5180c0c00c41d40c001d5884000c10312011801c80c04010f03691403d103000d0480025510b04204c0d4900c00030b48000d420220341c0301c464801040220111156048140c8070411042c0e0034002400c1c0682d1a4119104600880c0c2c090701001c40080c8c003000d4602c400140f044a240d000f0324244100031400f0000703400070300020000340140700320030780d0f198100d0003d4082c940c0507000860342e842c07952800da4603000c0c09500000c109180820b04000f1240c1068a64501c0c0400382c8100d90f880006240c148005401640c040d40d01d00800940071040c03561000407940310b4803456000300700c1d10b02034210644041c05420307030800841080b0710b0ba81d13034100c042350446200d1a006040a0300840c204400c0741e00084120b200e18002544480c000b0020351405a844a400c6509600034190140107008442d88628603007115461080d2074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 903727122 1250 903725872 903725887
    0x308040e04031b0c240f140d02030c1809010b0f030a110309060a0c141c0e19060f020301060806150d020715050105060306030601031e0807080c0610050a030305 70
    0x1841c03020603c01c0c90300460b224603980038500040c044040d401007800420000c3c06140b0341d4407006546803005403203901c07155a103002401c0110340c0440445446100841c3c1032081000c054203a002450040d90311880741920388917409803496102806c0042640b044074080010014500070b10101c40980c080c01c2e600b1a40caa43d45030040c8060000c42c0c03120f0b040c280c0000b00b0000c480b030001ca0481e00881c0c1c807400070b002000b48036a0840b9001c0c0540c0d0800ca02250030410480f07108004401c491a044145c8804541d0500c2440000d080031560320107080742105140342032040100d144143c0c9041951a1021800d650400714018219003009081c0c0d4000c8085c541ca001540030302d00e041e24039030540c20406550341c803c1e07071619050302d080d0742040c00046814076001280500c0c02c2c0e0107507486540007500800365a841d64440700000300356403402408031640b03000c048000c2242a80240205405409955502c0005194051416100404942c0d00f003060320000d10040c0d803054440d1003120b03014030307205445010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 903728372 1250 903727122 903727127
    0xe0a0b0319050a1406011a07260d0f1109040b0103091707020a12030509091003021009031a0c0901050904020405040203010806100b0901090e090a02031f150308040e0403 74
    0x5020059032801e0707800402103401c02400207400040544510401000ca030050750526035107610078001e2050074211600d01c100c002d00c1800c05004245d0240035503a0522882c1e08102d070f56111000b407107000700c07800000c444881c3c031001d0190801c9401d80c1f01d400c01c0450100d0480480501030721400c01d104940301c00440c40c241c0e01c00d800c036049441e000262882e04850049040c0300560000d107080340210f0b030508000640414900d10200ba064250303c1320703071410464004000d2500d50003450b403507100c0290080480542c8a001100340c0c07032100354455021460444c109039544041c80c1c100307016021900420041d00c03102000a940da5040300b82400d94880c5494800500a4095900501e422034800b00000a100c1800600707240910f034010354280d4800c2e2203219488042c804e080b0440d01280036650100400e00b803000c90503600240721025100e1121581c1e0000e0300708a10000400b810004218134400080968442c0d25800b40c00c5481d1042c140c0d02d107a98140950040e0302c02e580307055051000040c1450b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 903729622 1250 903728372 903728383
    0x91b061201140112050606040603240608190e0c1002100f021312030e06131206050907050a0e180f0f0604030e040209090a1a0d0f0506070302040e0a0b03 67
    0x1103003810414055038640d012a40300030061168240011500784640c80c4000c607a20901c3c0c081d0707002610541c0b5050500d801540034003d00400102210414000403008a403401c05032005001c0c941d89204040c2083c181d01881d01c1140050a50610b1405a8031000844005403031080f41c14180c0d44003001018400302a4145285640b55600c41c50401005510000c00d607801071140891b81010101c0b160341b41c94884034950740703698005001c10822513034048a4170f0143c000d08844404009411380303154450009400c05074011100301c400c9601d404c140300448005100c40707000740406440203501e641c42c2c800d559400510243c482e40c509441c200720368002d420184981420002c0035003c60710321031204001c940e500c840445040c1c1c001060f00b070803007440d8580b5000700c130707080000280240c440d5118024a0300007020020103003480382d0b01e81c01090019072102d89503d00411301442403044001c13030724140103060580c010611410140704100500442414000e00d5400007070b403580010700c124200c0f003c00d1034078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 903730872 1250 903729622 903729637
    0x30f070c02030f070b1c02130b1602100519030531080c0d09090515040e0a021203130e04032304091401080d020d0504121509032006091b06 61
    0x50050050229480b0f45e40c2c802003c0b0209560a01039034003200711002c0f0100d010380c8194034010a4001d02c20040da6080c4000707170812612a003100c1c0c801013580d50003d0b4070700c48003454080100b0401300700ca00c175595010326140c2102c100360400703000c586406840711006806039032006000006810035680c08040d044a4048450313400040295510559010247d4880101c2e6030300001460512000c2061116406098013805240440806101e40c5c2002c10000c0d0070600035140b0716224000d020030145c1c0e9400002c4044001c075001550b41e035100c8001c030682ea1059a04410814240207060000007075110320301140070b1000c070706407003c2d0301d10030b034000e81e021300c2240d0000189905003594940d0040904100038103e4084004550390140450703c00c1e41c96084c035020010214001740300070042040701d100e1541005206041c08a0b44800821941003160444032085d40001c40c04051445440584620390603043d0201d0004c0c6942d180c84030210ba51a1001c50714140c80d609034495100c041c0d1100c10070346180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 903732122 1250 903730872 903730903
    0x10806061810020f060106030e060703020f090411043b09150406020306092211120106030809090624090f21060a09030806060a021c03021e030f070c0203 67
    0xb1401c2d480700c002c2d034482081d405407409000317a500000304507020b4450340d50707400c4800380030b041306954203c015802074000c0c440e440d154100c1000b4960703a581d07941c81281002040344044507100d600784103002c1c0300103565034010911882048020245105118114251103600c100034000704e0342c1d1204100c1c10610340f01140040220442c044c0010040c141d0043e6215200c162014001d651b26000050b0000308601414002080101c00450100e6440400c10007204805810b41030403415012035a82105c20640c130a84080380081801384d030500c0d105001641100f02102e0002c6076502d5003c06215078003080d4920342c0442d05c001211481130f00c906110345440d0700020f1070390b90f07880d03002c20f000110402100700c810994012729002030300d40e40c4644100d024040e0103544070740b01d035640c40d400d006407a40040d0070041544185190503c213503000c1d4031500c0343d10680c0d95003d0380303c01084800b40c07009100b0428030101060180208a009608401c08661010851900106580450020030b003400950328010a5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 903733372 1250 903732122 903732139
    0x3011401050f0a120507092103021f021306020721030309020a120b091f0905030d02130f150f0e0a0e0702070302191d0a1e09031d0108060618 62
    0x120790744c1120340c00000c0004d65400b448a66a00340c070880d8094820300500200d928000007030704019420101d0010802d100b40101c4039603058004d00401c0250304030311241c0b08150002420f2001010441e40c1d10010801030009041c81800e01000c200a1858046c0c0c41800c0d1050b0045003060510030b801c00750700c032a009000652003070340310340d9050104c0034090b100390f5907019014081240704000007180958001e011400702084a82046030902a03d5000000d0312030f4031082c840407180350f2880c402041c00c2030402130b404034410320700601d59003d55403560100c0203201c0611204101c01341c02c104d40084a08203460043d00001c00c040c0011f0711404140c11030340007040ea49082000361600018a0016a4005c80300c0701564400e080120040140314090501900c002140c092030040d03000d43e02c0342d081031800d880416a8820f000d041d102a1a1000f94002c544e03484060000503d41c01c6201341c111031402c0510808032181c0480044c21105001e081d55000b40000601c40c002c0d6070304003030701c070b010603400901b0500b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 903734622 1250 903733372 903733387
    0xc0a0b0f0d1e0f14040b15011202030c0304020108130804090b0409060e210c07210b0403080609060d0b0f0705090901121707030807030c05040915030c06021203011401050f 75
    0x4200020004918134641414003080e04001c240307a500c1198811202c40d1070395641c00714410f0646c2103c0c00f4034181302102c000005040c427a800694030900c00d481c6010788929140c0001802c200010b00030240000d41c4034680300104221004444c00e40b00e2144c80425041c1001c40420000c103007611005e886540303451050944035001055401440110041041c03902600801415041c420000b045480e54050207041000c0c0303e400903441424420500743c08425415511740311800c1104072030440000d203400007040790504d410320070260002c03000d0754200381d40a4a9641c0402c1050044d18451020b02200d0024040c1c031f100f1400c4070448500640621150350b95010640712800c4990003c40c0e1900100d005003078600d020b5001d07a64000c0e019980e0000d151201101034008001c2c540241d801c02600700000300c0c3c01d01c0f4034003c1d04082a01c40742c9001c0714626501b4456098501034101c1011500148080d03180a880e01c029641036500703219948508240a50060b101482280e0b5841d0760290042a40c0703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 903735872 1250 903734622 903734681
    0x9031e080108010b030c010e040b190e01050a0b180d1e0605180d050d020306040213032001050910080c04170f0d091214010b031e0c0a0b0f0d 62
    0x2141240e02c400d000f804107a401c081095280c208032982c071800a8202e001c0c0c0c40142c5003039000940f00c040c0140c00420310460b1841000d16101c0c10360040090f0f114900c004004509042d03281c1c60003810090003080c186040b40c80c1002442032685801c0380308071001e91585051080c070f840e1100d4048510b0f4182140086240340030700c080e2604031000070005c2113540301c400030a10046a9081c1c0009540d80c0c06d45400d90600300e100081d040502510b8119130301f40b0401000e00c114100c02c1c4040c40c0100c0d480e509051008243c000060f2498031070904000d014851200710703407220348108400c403520341005400c40da5400a004030074010383e07015403c441c0300254061079030b41c80403607412050801d80301512180c00b5100740c2a07031108004e01c100c074030007480944204040b03500d0b0b00c109d003a40030f44140081150b10844001926001c44c212842400c43d003e10403101400234100001d140c0518180d0304414a1440c20311004100d01a140c52042c00301700c0002e440d04000c065a2104100743d086500b4840d8a0400e0402c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 903737122 1250 903735872 903735887
    0x4060b0a321206070f05090d06020309010f0b0f010f02010905011b09060206010b030a0e03070b072111070f0206070c060509090702010e0d03020c071215060501170402010309031e 78
    0x40c48003900c08551011880c2440c908510b04a8542001031040f40c4600b9000c031501c0054170a0310040050610040d003c56407130a04c800346940c0075860250f1a410501c02c1d8500311006c5500c0c40c00603038584040c00850780c0301c02c130801da00d9500c03d090005c0c1c180c0965909078090a0940c00081c20b65103000c0146151b0841c01e55151f00c403150300d545581c846529003200b66a1640203025a41c2a0320003440000c030040c800d40c00c03000c4500c1d108001d030303801d0908941d101192341d90113551072408103980c4e0f000340d0f00346280410042c2d85040c140c1000d01880c806549610600c0c45103c0000d041c44203900312034010354607140202d1300c1c0f880c0d100000c0003c080da2060001e180d80c02900803c1e10031011480400d00142c0705000700600d040d1000041c4c0386042c0c004400381c0096000c0300ca50056800707800301c00940f400c01c407442601040c0c01810300c88103c071410f640d442c0c00c03581c2c07a0300614103001d189060340161450341c0801a43c8a9420701b400a1110618181680c101f07503000d016914804041c600c2c842a190b02801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 903738372 1250 903737122 903737189
    0x60e040c0305060c071a10050618042f0d09021c0b060d1e14070b0c0f010905060c0c0c091801140c07032001230c0a050304060b0a 57
    0x283d900c0c80c2c0314580406924030030803d015005107924001c0c0100c19049114082c0c119094091040499035500f01141d40350b00030b00814000c102401c444104142020700541c62500380b01c2c40001410706080002084004100448a518650101d021002c0b5261a07102d1104941c000348255000b000c0712904c007184d18917041c0c00310762080d41c0001095042c14074200c1a0202c543c8240701c203890400e020043d41c02600d5851041d50400036a904800c03602c00244061409000f400c00e905a640d55003128142c60f00040307641c055416031404101030003140e004104141c02c000031041a80e80c4901c40300c0d10754504410b030300380d01d944110204280070084c10650324005085010380001d0014085880c00070502840c21161007407006000c0000d0b0b00082e208070b0410340380f10b00c0300a81500c4920180e03900e03421520074520003003141c0c62408004903c544042aa2948481030f4200c440c034140782614010305500000c2c1c8000c0c602516500e2610541e588d02001b171001d001c0101c1c0d484100304c240412001e441c80b403c0c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 903739622 1250 903738372 903738383
    0xb0604170129060c010f0f201e030a090204060608150301090c050409230d02060c03160318150f0e030c0a12111614010305240301060e040c03 62
    0x402c0102803030340000859042d1102590b82c07010104820090040551100f10b54a9680d545c406840d802d2140d2441151801d1144400000380d2103400030491003030081900300805964014001100503c0c1000c4401e940820f070180f0a6031640c940350884070250000c841d000f58441d04122000c01c1c1c040e4000e94052003221001408000c00070b01c03500303140c202e0303c4606002d0060b043c00101481942099000406020322580010405440611a200c1c1210225000e10015003040000d0140554104209504042d000c3d00e12440c60801050211190403040c98071002c0c336440b190044140d4054a40ea040c205401c01c03403400910b424100006c000304000c1354410303071140c9842401140300314000290343c19180600d0040503407490545511030b003055110008010130400710b07042c0e140f0b5903080c0841111b00701001c5180c52050708141100381c0114064003107034101460710b000c0000907500030928900c819000c602c0078003c1c0081801090142c1082e41004400c02e15203001d000c01c104100800300100da0040c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 903740872 1250 903739622 903739631
    0x918051005010c02010c060213090609140c190e060c030a0309021c020f040b120f0a0c0509060303030403080702010e030418141902030907031a0f1b1c0b06041701 71
    0x1807006540000d0280c0c8064005402d0044003400200240d0040c035071284450054040d1564402010065580c40e400c2241c00700d440d042e01c83e12941c15803540343d07003141c8450b40e01410001100d040c1000344042d800b0b030400f005040204548d40d51240b500300c44413004c00c0410340340e4035032040c00041c002e0030700440700301d019800500c01c2031182d445072041407003e15402031024980401c0300d020840545500d80c042540540e0701c0c8520300c840034040006801000ca088050101088a81040e90780f0a40035849140202004000c2000560f004400c40c1e07030207a8581005c000948820300124014000c5d041c16401502c000100450f0401e15062500348808168030240507090388507640c40e90598042d01c040c90804204600080b0703003085034015660043c00c2c00d00b2610300e15a242c940800e43c04104180b0b01c44503c420301413007180c4110000719544a070030001c46425241c200e50b41c0c0d100c01c0c8030701c074420b0a42000c40c0c0036040580000b508120103440c0c00404c440d440d20b840d00f50040c5030b040703142c0303010803030350300c0c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 903742122 1250 903740872 903740879
    0x203162304150608072c15040801060e041b0e0c03070915110106090c0c02010c060b06030a1b0309020603061e090f1602010b060a05030405100509061006020c130c09180510 75
    0xc2c0810304625401444c1c0e1030700384031b100b405100c000c4405080310561348030140f0010400050074403c1d08000c0040c412844910304081c2803801084140340c214440d40c030344d81c1c00e0034845000d2401600360040303626801e29603a035644207011030351044240c02840c1000c04c000303a4010001c1d800040c26207504102c400800180c0d55500b504021584111051400700305e05d1341c0b100001d980110409030b0700a01818002c50340c9800c0800051080e40121440c07505103548580e0620704440741c00c3e010800f1205400e04208051150300020303801d000c003d001d00d01c0b41d98a40280ca1a103020307038170240100342c00a012404039061442c00083d94078007c070b90050918075184480c032255841405001418280540388510b441248a0700304e919910041c401c0d0b40314852a40c0d1710740110f0343d51049034803802d043c0f8041c0000d42090005096603900541c014411584a4160840142d17101c0b09200c2e8901e04140c2d00003512030301d0900603141182558807088400e002c8041001d00000b00741c000c50b1040421030f03a44c0714520b88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 903743372 1250 903742122 903742157
    0x30d02010504050c2101020301151707020601031502071410150609031704121b08120d022b090605071103070312060b0f07020316230415060807 63
    0xc030b034094070a902851000c0101d04100000c00c0a9480f020108420a540b0707050f001e0076a80280d00103100340007000201d07030002382d0080c2c0c0b0307203080310b041c680903100340c10804002940c4860600024104841c0d2200808809885074125038800354000b1340084180722030740700c1d0361f2112054846684070134140b0079006000c91142c0300c01003d03114035855440c0200d04540f00d00c91120b0310203078800c0500e1006c0102140d41a0301119140089200d849103500b46103850351042c1d010109a030002e1180c3d407005c54080003103141e900a0325a0004403030001a00c415610702c0e010842201d0100103142c001845000100c8505140c002a501c24050481401151181d24048440510980e5140c0207900244000d00001e407040c82c10050420716030394041601c588405c0f003520b05500510000b60010400640d000440c2010b0050100c01044003210220036031405c00c00b0013060042040e45203480f20a0300084030583d0792540701704094004000d18441c0702c2d444001c0608081c4065404101080100c40303071160111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 903744622 1250 903743372 903743381
    0x2091c150606200304240306080712020f0303121009060b0f09011101060312050c1605030c010503190614040515100e18040b01060f0516020906060c07030809030d0201 73
    0x315150b4a03803846403d4104401401410100a0640c90008100000c0c03500c44110321000214030041200610150303406000e0704407500781d400100c01c0e40000c6000c00039005240d02643c40a501691102290501880003905510420016002c03000c5403a05000f4904202d464100540303405e03200411004e034441e01c2e0003d860141083c10704480000308600e9580d9441002c080c1104003420b400422001e40303d554040c0701d494000620000240081891303445600204104240c101d00454001e2545040c140804d0712180c1d011035281c144078000000c82e03091107400d0594403001c60600c500304071403610f61485c400c404401e1400b2a105905050201d10603040d0301c072043c88480c0004101071403003070300050191812000c0c3c0386203a5128a906816288084007110411b1040340b00d000300c0c1a0399810308401400d03d8545030200c104120003404440c1021048001d0104103d4048541202550702c020024020b48100d1900500500880c0d40000422420310003500000d2030071070a540031301500c840c04a00300c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 903745872 1250 903744622 903744629
    0x50706091503020f130b090f0906130c021c03060f090203071e0c050109061b05030f0114040609090609020109140306010b03040812092416080a02091c1506 68
    0x88200e4161100703954003e038000c0649290524401e8203100c1031000d030116003841513003c0300500000146268a5180c5894104a110304c01c032400030031403c1070004120300071500c0d46003d00040c0e58507210708555000300101c02d200001481210210405003070f0080250000d807080580c03520342c0801c00700e13070444a402641d10844e6155070303040380900c0400c90362140340d80d4a500316050000c0150040f010a0b000e010300d410342e501461000c03803092210803400e940000700c1c0b010502005400d1040c0840404049031940c11551100f5150401c1d4240a0000e4000d11003640181000d038503008000c0200403964000c1c10701e15000740c070713902e030410307a00d011100c9007061001c078582d45a001000180210b2105a01441d0054054111141802c092a000c0c1c040003030269014500c40c0e0042043c10707070383c0012000004080082503004006070070001045104018075240e84000c2c411040f000803442e00080d8140c6403821401040813050f26070f06c00480d000140c401c1d03410b860614110000b12800365440c02414102e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 903747122 1250 903745872 903745889
    0x70e16050d09020a05040237120911060408060403020d020304270f050c0706050a0213090b190b0c0c0301060b030103081315050301060f02071a1606020a090305070609 73
    0xc014581400740000c02c41c414040740d0240d8299404225500c59101514040300942d0641c65103141100c040c000132182444940d08524207059030101550f480401c001441c80e15400205500540b803a1403840c00c801940d5040e044203011030f000908410010340c1c540a540644c003a6605084890001ca807a8415801031604050f05484400707545045020300111410121b0790008207940f410f10581c087d80c0c005d45201e81e00707160220f010300c140952072003180d0301708006110852078586100700446c24403d0510428000c01d07a1500303031500c2c60300e450f40200c1c2410010028403607515143d040320307141c9420a9015507040d11820724584075a08051080d03005903441903030311905680c47c1d6a900b81c5c80358880061507a5036000520005a1545840000c16410342d0588403d03480c0d604040c001840449207103203000441d800781400304a4040c250215609040d42e1180743c1e640c0e5800500d02c8150340c880208010b20140c40050602744803940102c212044d24031450980300d00c0c5603a00d02c11511507000d070144064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 903748372 1250 903747122 903747127
    0x1030c02060103020f0d032706080702010506010c020409141f150305120a12110304030e011e030b030a1407060206060105030906070f03060806070c212003070b0405070e1605 76
    0x1032500c2d00c00034141041f4401e1914440d450103001d42c03605030368090202007040072000078050040d59009031184e64880201d2000b040a464207500092504a4a92010b4000c07951542020140801104000100c03c5d005003100c200b507006014011207030500324801038070b09140c00c209203c83ca011040e50800c483d080801030803020010106111540d005420036414003140181502c00780b0f090740915200b1042980409451380350508010b0720301252014014100041152101c182c001203202d14182e00b1001d1034001203032003012010920b0b10340e0401001d481c0740103059042109041c0000e0840a8615507030035520103841300001500c40340402c0e20102001c1c2c1001001940c00762040c245841c0c149030034034020600b13a66901801c0e05040080c1c9000001403041500302050007040b40c1c0e0480c07180c0900121401502d6407800003001000b00c10300da101a1400c1c0e00f50320003a0203040081d15100c6401140c2024581804e180280c3d0318651441415000441000000c0d400c50000001103002807907070300c8407032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 903749622 1250 903748372 903748399
    0x708060405150d110a0f0f030c06050705030711220203060a090c020a0b06030304030804171608190f050706111009020114030a141f0b0304080403021c02130b01030c0206010302 77
    0x44089130403007119900480045400201d05800622860040034210f48454510307045041c000741c8130b0035a402140c1800420820200050400030465081c0754220840e00e03901c002082c009101c14042558981d00c03c00c6411140e1000d902ca0350065009030780480c2c110402e5952500034501760b80c000503800e005600506901e50200303180500d13007584604000c2c15286000e0301d80d40d54403007581007500404900c00104803000d0f80c080d0100002c503290002501c1019801d03203407699899960030034000c800c500583d003048049c00c1241020030480c030709502ca801d56800c2ca4503400d00815800e0744482c0252030340324036402140e00110a10850310711b0394041e59150800000110307c01d403076034005000c01c80141e03500c072504047e02d0b174164421070189554001b10400382002d03445500b003582c0706400440c03202074100240000103010b90115000c49a054812900f0712070101303212014150704000182d005140c1c0b29201042e05042d50008034001405d032130410095a80c0302049030b40320801d010081d006004821200c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 903750872 1250 903749622 903749633
    0x180106052e0e060307260c030703021804020a0806130203010b0a050a02100608061602061015050c370210180302180907080f030412080904050708060405150d 69
    0x708a80440d00303110700c50008600104540354421103080001521900c03410000d4440f200481e010700003161605101c5080915040c043d82c400907200b103083c198001070411032841c40c14010303a101a002481151508034501000d000c144003161698401c03164060b0a07045400c241c400d0fa03050340d0320540c1150074090b40d044c042c0c0d480e900230a8000198401c2c090314072041c10050059602420b9443c002e00424245040703544103c51101e000349095400c90410401e0180804100108a0f540c00da0600300e4110200c0c0b05440500c178a42c600d101c98040c00761081180d13941405000e00f0348110b401780783c41c103151408002c0304000c3c001d0b400075484a0103ca845010502c41d078241c09003603100045c00e07086587d07603a001031944585003002558039500380c410801c0e01c02d000e0041d2001882d44002400f04840612265601c81c4107a0103002c40705441d8010100600c100030741914000c9401034401c105505003d44044e0061008a0303002d8802d40c1010001003840c40c40420395000f0040c060626502c081c070380e8cd1b48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 903752122 1250 903750872 903750949
    0x70f1505040308030a150614030a09030e060f030f0601030c0c12031d010b1302070b07050c070e070818011104050906040b0607030804030305150603040311070504020318010605 77
    0x110000c118041c800400030501080043d80500c0b100600040c40c14a928004e40c032516055000740140902662841000703003c0701d08603940540b0400000542071694078081d5080042c8400769034000344042a007100e20301c0d408000318007400440039160601c3e607400340110103454500084000242141440c07100144a2004a640d1100c140c00c0125034010f40741105815030214401c1d0301c200f42e440c1c205200250034882c0c28007a140c0c00011041d032600300240c459405980b4050841c0c0104480000ea03589030760024040b440290074940c3e010760f903a082210300140140e07015901900c80c0320352486c51095800e414420043e4078001d45003900c1c02c191a000810078901d43c0104010707002603d485190029590b660001c141091298a4180c018100790070000c08851008201800043c00080d11040313582c1e40206032036100d94140340100030140d80e44091070900c01940d0225820500201c00c2c011a414034680c5150400d039500000c00507135581c1c00c100603000c02c40c0b651140ba1110141000710f10329495080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 903753372 1250 903752122 903752159
    0x6091303032d0b01170903070f0501090b0a0c08060a0e15061b16080703020a050d1e0809180c030406020f070c090609320a090c090207060509070f 64
    0x2150050354408407001111011035500154483d90360403403809a0f6030001c52014a43d00f1521440d602d5203045845555203200701303030000c1d01c1248010b51290410501750041d000c000e600051100c1181094007041001d003020311108000720340b01d0000a410303403c0007040c035803c82d8114070303941500d51103c2c141041d01c0030017814003c1e0131620411003041100103407480e20081d0315244004241c1400b614012a40b910520b40104080360040030b4208007690703515801d501501c0040f01c076800c4c8040d00d80340c24005010f80104104465200004000074080c4c1600581030410007034a5a0100c10f20310181400b000c541140c1110301000c091001c82c0c00305025602074030001003142c00302854040141c82d0001d03410402d6100110300e50300d0762400e2080305124010720446400d00550044160b41e5002c2d00303062184000710b100004201740c0001803000c4406c1e001551000d400242e882885500c8800c20400303507001c001e05a40e641e0400010550040c4005a06400c40f900d21000410040c1030400d0120301d18030590 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 903754622 1250 903753372 903753401
    0x6061e2601020309150610050f0906190c11010c050601140111070b0c0c0604051309171209010507110624040c03091502090a030219170a05060609130303 67
    0x110901280d00340700550003001ca15004090f40c883c1804da055032108018400e600800c10000c80c02c10094010b000d9403907228070490f1242d00c031000400450a5030080c200702180500c003c03544608095000014207490b580a40d05180c1001800c0c8015102c0c1241c0c000000c01c0380e480600104081c150540d10a4010380c0149004030301e04288101852078455103403ca652190000181c2c0d03101d00c001000030b64503a01c8152400390a003441c01001606480001949030601500c0d01c19200810280111460765442c1001c001c9813144c002100307090100200b02c0d089012036107041c1c042100c050180300b8085403101d002e0000c1900c1e59500101107510403241d4000d484512410103440010740d55030241e4410358807540d4000a410100e420849240300515083d2140c46104001c1400d2a85460b84400c0c2540c1e01510841040e692801140c0e84c40d03956a40704d000a0458610500c6603a100882e00c020722600920464001d40c0310714080115036881030b2f500c0e2500c2d0300d081070320a0000e806500aa4801095170 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 903755872 1250 903754622 903754679
    0x172802040203011d010e04112202031009110c0c120118080c0607030b031c0905030106030b180f1f0b0a0e0a060e04150e071a03010306061e 61
    0x15808a416a042a004004200400c40368202c40010060030a070040ca06980e51003c54103050311442513407448103103198040d01c080c0200303124400c401c140b03485400c882c00c0e20442d52460200015041524540540740c81241486109414000c1c80c04c04d5039881e5600c0070240c42451001c0c000c000380a141180461900d5480b0030092032070032091115109500e0190b10200ea962052800003410181e00401180c14940f8220180e101e40d140040c0d008865126042c071500d002c032a0450588083d101c5512442d81507003071107004000c2028282c900e03402100c403100c1c0361003454004010300e5200c40000b00c4c080b40f41d03444404c5240b100d0300f0383e03a8084200c40458900182c2092040c0200e00030a240750405414840c48405020254880d0722500004099440c01d001180c103043e40c41e8600c41d02c00c409142419511a02c1008240c0b0f414000704004081d0b04604400900311801d5000d01030b0803d1105031854bc0c907001d00000c02d0750705400a220f402c0da0b88007001c2c01440c2800741032180a02660741094032516030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 903757122 1250 903755872 903755953
    0x708030c090d080c0606040b0303070b060906210f010b0d120c15090f050c04060506091216090903080703061d041e111504030305040e0a0902060a0e04050117 69
    0x70f90000b0a4004842000780140c0e28205c0148010382c1d072282c000c80d000ba48108121408600e0340701559411280450717031a00781d9100c01000900c01000b100c0011004d401028280c12500301c0083d1800101f1000c10003801105400b1041100300c10364601c0150581c0401c106602c001072160002c07a59452007922810307540d00b0000751160032240c001034101c90b510550250607050003410095200760401c00c440a000c050709000100e845401402ca060f40215820050061000014800382c03400c840c6c50000300c0091a0707a81258006800e4010054003c10700d54400300d52024031902941094902c54092170116001c1083c1500701480010401d0710703c6c011103c45441302c1c0030341e05144003189000c4c0c94090014403c0070100036101b50415a8003841201c02c010800000e03400c001a942100c2104039a038100d070395071003120006082259002980100000ba420094a1700641c4d04102140d0596080080342c2c0c840c001202c0c89c1c41e1400f0f4240a90703104422028203031138020701d0f0700d00b1500404903d2041c0d080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 903758372 1250 903757122 903757133
    0x60308160c030f030c0c0b090609041a150d060801051b070501060f0f0e09013602150a080a0c09050f010306090e030702030f0d08010e0408070b090d11030708030c090d 73
    0x40100c00c40004590141c800306000440701754901801c2c80b4a0302616280204001452750700c20b1004081c007894940c0c40c813115170140b1001d9684580005411091545180d0202c003019600a00e40700d1144c9262280220706950705208151050b242580c2c0c036441d011501c201d0494a03008290103c0d101c4d900c4180100f050107507e03c13040c00030031801d115000401c0c00c00e181c03030042503801045110b407689089a4640c110100c80f804848501c2d10010921003080300341822030707202c0c620f060003940110900401500e441c52050080c0402c004c07558030842682c40d005085010340320440111400202c46050501c0709103006100038201e10014100010401c3c0c1d2650b1840503100c0c1c8441c2c60300242c0000c58440b041d42400c2c401c2c1041d0044400191000c00408000903105510601030720442e02c0d0070358001005c00009000722580290441c101007214a014600380e5680c8080c00c11003000034010034020404400000191000c071507104002c14150390328442c204041c4c0d0006105039900c0240368032203901249 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 903759622 1250 903758372 903758393
    0x31e0a120305011a0f030c031f0b031905070c060c0e03100605030d080f0c0d0209040509070906060207060203030c090105130b07061a03031b1f1a04060308160c03 71
    0x12141d18003007903541c5084401141d401e80c000c00341c0104801040303040d04201c0140300301ca6110302843ca9540d165250345150180032011170301384d010361400c1e2007000b00c0c01e05540c1001d184240d41241c580b111005400e41110203489040d14003201103844004c200c00021995040742c280c5415610b07100c62a003860900180c03801c0c000e04a84c8503001d41c0c920b0240141c0c1014070084140240500300b25800d4284612007030341000d401031448021580100b0401403008042c0c045698180c0010814041c0c1d0511106041e11000707240f00e85071440e490150005145070000c1640011105650051429952044200c86c01940302e084420304000c41041140040200505100090445048080c4c6c032000240380c16411030b102c500420304d250a490030f020354180e0340001103a0000103196100c11080c8030b1072160034134041003008605401c0c204101e48213485091507100b0000d440b0611500c441d8900c000090104580090001501c1010100841094074101034615010644a07600c050340329903590300c80d800680b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 903760872 1250 903759622 903759653
    0x1e06010f1806050912060708010603090c03020604060302192303130b04030c0b070c23011e1a04021305011407080a050c060a06050f010318080a0201060320031e0a 71
    0x500124007002103041017a100c0214040c03c1c001404541892040602240b1051140c0c00801d5111004070301044031184000700219805888140c4076610703a04064080d42140b0113040608005060313030008184100048400c0c80300384001d03510062070482c00c1c6d0341342e030707100901d2038000d04151040c00c00012450320312107118900030b680ba21943e240301d01e020031203110054800c1d01004011281c0c5c034040b41c20303410304e4010505c07560180944c0c11489100716000d480111f800b410f8041d6144504604403056400c4085250380b041440620001503504000407030044401117200390556100600581d40607180350002405c080540500301030a50762406190f40c0290708000c0000c60106d144044640c0030010140c10002d240c10501c41c4900701004956001500c1402c01c1c105615a862a030069600c6540c224034036405c03640d815500c600e2614041c1c041e00c4148012220340c550b4920107051038080c444901c50350040203010313080c0c900c5a501500080c01498240400d5070080e030722424005445007040d000d11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 903762122 1250 903760872 903760877
    0x807081218010b0f0907110a03030b01110703170c0703050d0306230d151112062107060309030509090a0e060c040303020c10091a03010306051e06010f1806 68
    0xca241201c07081c0c0385161464000d041030307030500c0c07601c030f540790f85241c0ca181000c1c02c10b81d60a0015034500b0012250038150305200e00042c0035180c0e41000b40f50f41600b00c0c41032400d00380c076010b00140d4080106966840a8070000e440c56101c0144017404022001c02050500800c0303084039001e545035220b483c00c00442154000c00b103030b030719441003101314501101000d01d003001c0201151442d010034003042d00b220f20039200404420607510140c3c501c50440d40003903c8000d00c0a1401d888051902d004407015500f602c40c5442024100c0d045032114600e0304010000d0b05184021f0480c007440d2010640c0a0070003c1000c03420300a00740080303022a241c8181d064410034408002003040021041190f0800c0c0c405042c03030703070302d48010001880032980000380e1950045040d1070800203031080c50b00807100882c882c3c201c0c90703205500740d014507608020b80380030314140c07401405c0410103034032840d100780d0350a01e2403540e62054a0000c0000f40d441d60141100c4c1440522608081480d010300308031a101c80441500484003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 903763372 1250 903762122 903762157
    0x5120a020d0b060313062a091d0108031c060b19090e060a0e061203040f06020d03060f061d1f03291315120303150b0412080708 56
    0x1000149008460340c1800983c0d881e071840c1031501e070118000c4240c4002038001c1d0740700c0d101e100c40300484030100c400c0c104000e642e001050381c520344020110b206c3c40c0f08117508031001400a2120b402150303000d604035043c40c0011490460601d0b078944a000a05003004040d99440b000011072501002c028040072200c1002e100456203c090041c205040e16040101c0100c008420000c0300d4039882020070690310804d440c90300e00d170340380300000311076a01580c003001d0303e0701010900080f2480002c0481c2e0944c1d4041d02950400881e5200c210700312103040c442c80b01c844083e1f02c000c11149000e1902d1130a03820700250018000100c0c4004201c40b1442885446c03000e90900250b45a40c99142c031541c0c0a0000e14000c0b14002002c04107400e06201e141e5410304c3c401c0354069912004039080c0d61003550441c01c00300f440300b0141d80d25003424121600c5c030302059010038105203880c0784c00034043c0304190030381c0e892850003802d160402030340703241c280e4150604556150341002034401040604000d0144e034440105001c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 903764622 1250 903763372 903763387
    0xd020d1e031e0c03120207210207170607090e0c16030e040f02030c04030b09030c0d030515030f0d030b0f090c0901030b100c020f0109030605070f0206010602070e060d0305120a02 78
    0x102e00c0c107032290b00341080010b0b0002c07400030f948442c1c030003c0c0003645c00c005611082070782482a0b070020000040007400800c0c04d400004030f90007117204811100460102c0d103680001d000700b5600c81008881c080c0014601c0c00052012101d0380750807070380082e00c44503c5414100c88a0651101c0e40d40743c541a0041810300248500030301d424020000c003110401c2040d0309504001508108030301031400000c0040b04d44200165550300100706441c0481c80c00022507404108081000e0014a401c0e501c40d0459001a01b101003e400e0000f00c408944890340000d004042c11000c0c03c50003042c10b11100e40c2d10041c6000d02400370707901d080031640152400075800755100102c0340058211140b245040d8044c4504069050005810071440d030011501528410304c03108911004175691001a080240501c0c60710707050101d01584100310003580d0716550200d44980c0d89408050760b6a00ba1807003442c42d030f18480000940d144c1058107013102070754802d040c59403c081c1c80c80400d105100e4121903418145501090700c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 903765872 1250 903764622 903764657
    0xf01030b0105010306080a1e08030c0c0c060a05030a0b01020f1b0a050102010e0604030c170c0109020325061209081b07060e0108400615050d020d1e03 66
    0xa074010300c030908040002a00d0f0400d8141c0301c102d07151015003031100d40d1038100503c0f1140b031145600c03190301035095540d030b00d03004d41925040d0300510103916492040717400007240d90500d4000c40d0741da4551601c805045540c1c2e080300304003400300d522101d8110702a000d0000041c2108101940320400309000e40b50800e000d00d801e21500f2000b50b80505c0c116810084100050361340450f20342d80094043c9480b003e40c1c1c0e040e00b0703d40e60115102c40809070039100010492000f01d0107500c640c103054403c401713079a0300f610120b22414080448111800e1034009001d01040f04a0080e140c03114031840c103642c0840e02c41843e8541c85400e4008450a91410040c2d0702e99440c0791009110000c0503100e54107001100e0810b01000074800207005101c8906480a05160903540800354041080b240d00085801c581b032004015130301c0045406001122158104a032030580f0b02c95211885058580107080300560150300e808101001c1c1c80d524094410604202840c240e03801081c560000b45402911101c101d02e4110082 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 903767122 1250 903765872 903765893
    0x1202010c0e18160302070c03150b0f060904021b010c0e01140408060606030403020a05010906020901200a120504030606140a15230d14010e06100f05030417030f0103 72
    0x701c5120308258400d90700540058420b15070420044000400021842802500203104403540a4100300c0071070030000c100702c00d4100d001480300c5406003d0040e00740017030600044011071550180e016005000848085c101580a0000a1b1034a865184481200706005084400030084500018000c202d080500d50300074000030620158204854641842c00188545822015010a1103200000041410b0600c02c1020540c030642000080003a5089460058001e40c0840b0000c1e01084d041c074980a082a603c034810187c000100001d031154101543c1d41c2100c0000e954818400d0000a11012010ad040382c4600d601038490802c2d904001e600b402d08210704400150700084554260781c580e00034142d4046248044d40e614100d03825028042d504d500c0c46180243c8203800e00b050710340204000c0f40400c0701100c604071030403003c454095807208428455421206210503000c1454102403040782403280c0d00455201d4011034190480c01c903400301c0e060b6613501c251620740511064400500a00541611 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 903768372 1250 903767122 903767147
    0x21605060f0702030405310b040c0903150216080c0c010339020708100501091401122a060807030c0912020603090106050402070f0b070903110f010201091202010c 71
    0xc944098500764400940c3c9100c3e601445006201c4c80d204c07c80c50149840b960050020041d14407112141c1d0180100024003c04169a08c114100242c440c0807034003c1d8006800e6a0304a100b4140c01082c10718820080e500602440650304920f03604200840d041c44007500300541c44034040c003410402c050004080d07403050101c01c0c41034002c603160b04c584540744601018130541c4410b81d154211400000680c01d215083d07025040c2802080150490f00100c0d40c08641620700f6200204550500b0512420318098240510240c903e4608aa64080340c80c00135404400e004100c9030720004054040301411111880d440320010030450b009020315140c041c00f0b00c407454802032074002a03003854082c00619207010140043d004d0380c00000803803500340082d045440a04405030056650340b403285040300d05040e001a05a03010407581d80400c071420711502103102100c3d0803008070b100c60b124000400c80c210601203440c1c2e0641d9a00ea02d81c000017081c6140c0701c280c0703000039000014030090140000c2c00500c80c086 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 903769622 1250 903768372 903768391
    0xb0403050601050a0e151513030b090d090b07080f1201061b020604050f0409020d0c1502010209060306040c020a0231140f04020d0b0f1e060d2402160506 67
    0x2d03005c0c02203510070b09545500401000c845201c030500c6a0100d06000c04e01a02c421403128009640705025481a60603006c0b0782c4626880d2040743d4400c4001034541041141510000b18480c804010b11103421000e003411a01650340035103005000c80c0714010681c4908148110050410010424260406d000c03c0481a604000b044030b4000c0780c1c00207602e40700c8e07409a83d02c0340c034105e00c42000300d4840b0b030710090344154043c1c1210010000c0341002c1d00c0301c5126100380c00046100b020300004003441030003500d03c100409070045086446400401002d45040e031006407c40c8180c4d00a400941c0c0c075a01a0302c0b2030008554410080f020700c110312020503100c600b204681c107062501c0c0312915004503070496071100c84e010303ea102d1500c40784002801c1d0300300c481000d0309040d0103906001141c5020f1146030301900210b0490180040d04000c1075080000807030341241c3c45a10851584046000d20020f041030510340045252000d10455440702280c1042103107558900302e0146900400a0400155801401c0e62 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 903770872 1250 903769622 903769639
    0x207091d060c0d0e07030602191d010807030e010507080114010c031403061c050c030d030e0a0221010c0e090106022109010c060c0e0a050603160818070b040305060105 73
    0x400d00c456450101400910600d1000950304410b00c1ea254440b540714494442558125550b900348040a50071044803040b1508051030030091650043d0005045500180109818890780d640152044040103160b0010700d900d9182c0c043c01840c007841224454001a00d4141e0030703504203c1030203044511011070740d0610045030342e01e101103608a20310a01502c0c424100b07a03078980d501c0001c900c08043d01781a41c484450b00e00f11010810402041511441d88190101c3d1030201016200320700360760b00804404e030305402092100c40941803007211182110608030342c04000c0107a080c016801c6804580c41000002c410f41c80401242c030303142d502a07004002600c002e21060450343c20490f94101039160504c2440e00025003141c0d01c0c2d008010604815070403810400032090301c118007409051207103041520886071484c01013514a05481500e0140380030312005450603801e0755003680c40e1340004c0c1130001c490046140d0042100030800c5014081c0c44000d00c01519603140d4901986800010b030170203071040052 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 903772122 1250 903770872 903770921
    0x5060c0c0409050f060705030415110d05060111070609030530070609021005091206040b060f01031508031e030103080a05090f0d05210903030306010809031603020709 73
    0x245440c410318040360009200310062400302d1038400f0324500b08805014035400c11055030b4002020b148039a0058446007011003848480700111951a009002d41110034445101c1c9002aa40a55805081030405030080710404503054600403265004034000f958030a01402000410701512880300340e00407000314120040e040946026004107212154048041100814449550840c0c0c582e2070f009441001c01c5100b04800a1050340980074650003180b1061210300101c80000d401403050360440403080351034840d6801c02801e040c41214160401d42c40d92480910b88a1000c0050000c0100308000c43d55060307840340030804818603e0484040100c18001000850150001c40f01044c006d4604140d84091000c0003800c007581c49912250080d502d40001801c2180000300010180b03c9001d00e4502001d0340c586004403881440320f403d405400034070108982c2e501407012590030100740400d032810483d07803107003407041d0554240065005038490700c0100084121445501072408070b561a03021021603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 903773372 1250 903772122 903772147
    0x6030405070e041a0709030201092711070510021b0718091a070f02010e070b1c02070503030705030f151020010603060f0609060e0117160305160506 65
    0x468442c040c1e02c0c1455200043c200b0031a207103110038110803091228100d04200c40c000740029400d010803030125015400200d0003041c009102c0070b403103514841144406506490302000f4103030354961500074140030300507400058414440e0400784400c2c8040142c540038003494018018880400c08105500000414000d9540e40350b112429044050004960044107107460362001404180304801c0034030320380511030080d1340200103922041180d4000c4c0141d140517000152200b000d48980d60410f1010040010312007004203450f403003240034080060904100d41c0790941503174800c68411000176000070421040030036103102240c1042d100e400b1000741c100040086421185291461014040e02d4075092118003040d4440000703070a840c0b0001c3c04940c1d601d2504070050b007812502000c119062000c003140044491062508450070100036401591030641c5202c4031125804410707402317004402403d603011403105407042c0294407a40052080302145000010700900a4100300c1c486c100420001c0708051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 903774622 1250 903773372 903773383
    0xa0b04060b03010b03190504140106090e1b12120c071401080c090a030503040902040e150109032603041101121514010c0f05060f150d060f1514010e06030405 69
    0x44a807000190b485d01c942e80c400d4886c01004c2c3c0d02030030541c2440300b048104076001b000c3d0354058403100c009100450311603181406481c00341814294607409008842d11111141c1c4450310007030001f4101100c100d0111f6803a03030800614803282140c041d00001e201c101002d00b04041c0e001043c29050b0003588501d43c0000030140c50000c0c02c02061060081081d03403440d500c003075080c2d0096500c0000c8a9445a545c40254040c1d0014805c1d1300290100b000014000c45294000d1180000165240040c0070b0a40d035821207004400c000d1906005403420450090450080007540034030b020f01c15031078504800310001801c0140c5000b0300560503040c1b03c4560070001300041740c0015141004946100704422100403200026044c501070301040c1549031410502102141d41401020714850b0800165241003a6100c0240c04100c610707041200c01d142400032a074964800c0341e080e00c0766003001c920001c0c650300e0185a61455040404a00700980686109680103122030007101030a540c12815890030f900c1e55034451 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 903775872 1250 903774622 903774629
    0x801090530031f08010e0c1c171917092109040b09040b01051f020a06050601121409010b15030f0a02070f050106030b0c2d040504090305030a0b04060b0301 68
    0x1060007001041c0c03d102040000800a01d148410541260751402c50901801514003000041d0040129a404600304400041c0031109a60b00726007008805a03030f110446801c0701c0c0c401005c3e280034010303e5881209021502c2c01d4010b19601c0c00c210000101016071681e0020781030708110740c0034810f4aa001550341c508401c0c4203060103a2107480b0700410011802800f106154907603c2051070f41040100710f0003001050507200161005980402c04003d8411151442407140003d60300880c03103000001c019412069020406140098600602d4501d030420387e230150300070640c82c086400403c8400003003403195000105c001c44002848404001c42c0c00b13100d1001500214014006034001104038000e5012120004c2d0b02002004020b4030307604181c1d000b083d00e400200c800145040c0451992002c20040c0c0c0e04105035540e440221800000c00d034420280141030540621500340310001d500e075500e100c0c00556500a4580980c1c0b403408049140444005403070891242e0700c1c0c003030300303104d08010300060340d055 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 903776978 1106 903775872 903775963
    0x402130f0506040b160f0f14010e031c050915011e0503030304080406030b0310020307020f0606040606050a0c1103011514030105062b080408010905 65
    0x201e100b80c0c402c09140140501c044641c5151700e60300e049a15103d1145920b40061039a510120800720314401d4440c3c0c080120380a800000a0040c81110090074024618100c56050910080d64034085440d040399610000184040000c00001c40182d1031141d150100d51303907520602c00410118800d45609a10b424000100343c00c3c000141c81c092036108a040782010305220049008042050029070725118840f108140700701c2520046005c4c0c0581e03409484031450380807046140c5500504207e00035890176604001040e840b40c00d8503d9003076549425000d0100714285414449507512541f94513500e44090543c1c41c010007841c0030708568500320f078040240086010075003282d404850071500000502e20106124520614126810500c400240c13103080b466264510f140d08141c000712400d170b5440f0210414000c04001401c1864190f41b04010201c3c440818002c15800940318041e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 903597122 903776978 := by
  have h0 := BRFrame.cov_init 903597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 903597122 ≤ n) (h2 : n < 903776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
