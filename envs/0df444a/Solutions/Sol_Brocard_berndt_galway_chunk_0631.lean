-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0631
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:49:43.76001+00:00
-- url     : https://prove2.me/submissions/1c9e5fde-fbea-442e-af71-dbb7f3182144

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 113309352 ≤ n < 113489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 113310602 1250 113309352 113309377
    0x402090a0f08030a140901080105150403021009051c050304060c1e060903021e120c010212071101061e060810030605070302030402010e09090703080c01142d0103030e040c0302 77
    0x2016242c0404550b03d4008000700c20028a200b01510802e40c10300c03055038044681a11582da50343d00b0300d02001000b0020150081094100b40000009030355290940c3e40198556242c40700310600b01010b101406001d0030115a03240b08212401002950000444040b516a49030040d14a81545001c461800b00d0014681d480e80800355003409004480d0b10208606201350202c3c2d540000424000413103440060088081d604251003903209030440000905060000400040c5070500c080010140144c0a07100d03140001d510312180b0503114424443c91000d0040d00307550804102144a075040c01080d140030348000c205010003c81c81524285829401540d440441440546000300c0010002c2d00201c030143d000076030800001c80c003400c11001c81806180a10042c0c921282941c13681c0b0900d03030061070382d101c1c03565032600701c400465011415180070b4400e14008070b040c0c03900039003150f5101c0541d6041d158220304520041002a0b00300322108941d0350140c03400718042c0c2200d40150300a0040f80c01c880d02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 113311852 1250 113310602 113310629
    0xb03030408070521030708030403120207050601180207050303060f04060e15010e040204050f04050c0d09051c020c01020d12060506070305120f0903071e02031203040b0a15050402090a 80
    0x4080740d01003002c40a6410503120300b0b104400b9414204074020710441ca03900c19401c100150800300f20700400540d030180c000d05102e02030b04004d000d10400c17a480714a0903200c42d04000014405c124030001d01c0c1d4a0b0500e517040a40c20058142c03100307134403440050940d43c03241084160313203070b1251150b421985c01442c0d800c441c0c0c1ea048c40c000710b0350707a943d903594486107000565500d440c00f5985094425601900c0c0003504008014820509110051a024202950303c040074040611054824010b140c40584600040d05004513440031512000e0724181200c1c05640164500c1103007660300054a410907105440c0c02c3c8040d1541c8298070000740000d41009800050000d0407405040d0000c0041040c1164018029429992030343c0496200c40207441440e6035800400104021030328100900301c4440c00b46408541c14800c6a0000c2e160440700d80c030100b1180c501008000501c42c00b00100d0b0361081a03004203201042c0e2180480340f0a40050064503c9560302182d2251240c482c940c429004e8410944e8400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 113313102 1250 113311852 113311859
    0x207090e330c1206010f0c0c090c0e0901290f0406031e06030302060106050f040905090a021306060504050915040509011e06050d0b06060c0d050a08060f03070303050a030b030304 78
    0x40501006071050700104101c00c001c1600c1d01e54900032183d2074510b1030b00418460310351100441d440710301000d05c0c40c200b04400302480e02203401e1602900c000e19101000041c0384010703103c090f115050a1004920038401000100054420b103c01c0e014280c03000d144c142c40b00c201152400740180542e00380b0803e4050f02280c046080f58240e400340010f055140750424003c03112400c82010350b801e502000f40140c0103d0010080c01c1d0248001d0700400002002482c105071b02d030001c1131b0840f0011149490280c3c400c4104105506180408040b180e5843c00240005c0703041500c007034500d216921420740207060300800609000600000702145100040080c0510300300b506455000e40b052400c03101c00c1100c0e80c4803107004400c80d80308000880b5405841b04000d1091515000100780c0000d007559081802085240407501090080601c407642d1600e46540310100f10b01c0082031981300a2400e0f018131014026400d00d0303a0002481412284e042c9007099655001010840250641c00600c6030544030124021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 113314352 1250 113313102 113313163
    0x913090f020d030c0f050d0908010203090d050a090302040f050a1508191415040201030608010213030f030e19030b0604020f030a0522150507030b180406021201030f020907020105070207090e 83
    0x10147e400942d64141c80079144c0c1074227402c03844280ca19038184d502040da901952800f890182c0141c1405042c02a080c039500d4000c02c00f031351810b03004002e000741e0342c4040012980c01c40c418822a810398000d481c800c141449000c4d95079580480d0b84c0909000480440d4007000340144100c012501a0310965154100c500c0c4424034116064400300c1c08241880303404500c0031414400e4419a00d205014200d42e81c0c0b0f5600ea41c144404000816800c000b40c05804031070350307116000801c0032400d4400b08212068139608240b04c2e1081c0c0500114440e500401040b4580180e200980345c104003048000500384d04c41051200504000401041450030922500010b1003041403580d0320340e03062a542400300c0d03601d160088045681d6990b42e25840740520352400a8142c2d81140c843d48684203420061602c2c4865200c4500440240e100300e89010000d0004000c50401d0301da41600404030380028081400d1000c1c010351070380e100d40200c107050359a40d00100d40460013002042c02c00d12521903039480f42440c0312400f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 113315602 1250 113314352 113314363
    0xa0e2b02010e010e1c02030a17041401030b0105180a031212051006170703151202010201140606030c0702130c0207080f030405090106030f0f0c050913090f020d030c0f05 74
    0xa07070100d050007402c0091035010301103144289400802c001908100b01007000c1582c01c01071070a03a018402d007500c2c1c10004044501d0360f524000400c5055854900d000b030031209070070f00420414105820660790f001e40e640c200c2e040d034005001c0351003c501007044250119141382c40d00d920181c08c106540d0711440045400048008100030741d0071040c066640d511050340e90010706449220000741350403d582600804184016800c020709281c081201c5600105001544000e500705041c428a201e841404540c2c09100e0701c50640e140c003d10000c1d03803a0010004180380802044203001c2c00f40010308400b15903d405800d260070810728001c01942014507002580c070100c0b801000c4091142c003940c1d80d00c50704004291411a01b0003030030000c8503030808100303c0140c0030042d0121804ca072580d0b05130000c1491801103444c509081c0d43c400ba03d0703103600c10810000d20985a80c443c003003441c143c03e18000c20042140313034540c00e805840320350001c0d18501e412600c0003602040580402c2c80c100d0300d0782c01c11171301084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 113316852 1250 113315602 113315689
    0x105030d03090b0a020c010e0d051b010902030a03080702070e010303120606021605060a02030705070e0901060b0304170915072015120402060717070611030603030703030506030339030f0a0e 83
    0x711403502f10400100071300700c8900c103001035419401120344074002072188800941c80702c8188144e0321482d6442503030014610f021303001103010074008000044089024492280140158402000400c1c0042810502c030b5030b082c0602d60003444001002d1041500820071610110743c0401199400c1d595a101c1c082c5102042d01d114403207500b80135000805440c0107060380d0280d071b00042e10300050351038080071303414030350029510703c1d0000c0200b08242c00b82c0d6040000351045078011507a442d1089100e44000c52540d25200d0300d24403c1c1c4070b408103542c02c201d5100640d440030745180004040390320341d03000040041c0205940240041692084196500314240143c00514451801440104d414200300720250204660081d01a4414044d16000c40d100343c202c0341e00700d0000380640e403614948a201c82454010702d5001c11100010040c600003101401c28070045244080c0055400d02003982c62428051064030100700030801140c0091340140d882c2e6150913640040c800004410b00c0304282417200f124982d05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 113318102 1250 113316852 113316877
    0x3082e0f090608070e151305090604030905040c0909020c030f040807080d020105010b090f0d0602030a020408070b070c06140c1c030f0516050a03090206070501050105030d03090b0a020c010e0d05 85
    0x5500003807038180014160165004c000030101c0d81e0303840300520368514001003604c55010085600300030a054048c454240201c4005002c0c0c201890030b402c0140c01812240e100d14042c0746424600e040303e9601031000d1094071146c50700075130f50b812440102c40c994014a00c02161030040001d002900180001e0322400716090a003e0b030b01002d0740d0701000da00700c0f0000d125140305039404121444282c90300900c85075051f0300090a10444c04103c1e00c803e01240c0003180d016442641c0010b082c81803000030018407004140030584945000ea440d564450309088a100310710602620244400c3e00d083c00c0c005880284402d1000c40d42d440564450003001e00d520065060082440d0102000c40c0044500640744134031154284600001060101260583d0000000504065071f41c1208001645c5950082000e180504001f1034254102010941409061585c0c481070501d1b060455001601080070b6503400001d1010042e12598164942c501510f00c040c028050307800340820000c210754011000d00100850728 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 113319352 1250 113318102 113318111
    0x50f0103050d17040204020d2003060a1202030a020120121e07020307060e0a05060301031a0c03040302070501232703010c0c0b150604060207030317010303082e0f09 72
    0xd01055445442e16040c045a60f510400081c0140c101900103181243e0307108000610301801c41e5aa400180c2d54440048080c20004203009940c079200421002074200c642411039200111b50009603500880240241170280c04c601038101c0c010341400c00b1880072a00425a9841c0e03082d03100c00d0130789500040e44070140c1111000c14414444804064071820f90f0f000d0014024581440415100405110b10590740212009400308164446001071402548250300b06010030f0100003620680b00c00080c81144c3c982c80900070003001c0b0340c0c00208542210420708000c00c0c1c072040d410303c01c48402c10020f6000c0e00c030b08002400320081025101d05040c12550000540303404002c1c42c003090700342c1c3d840102c802d0004008966103000314216034800f60f04100800101000414403501091280d00581d104001582128004106041d0031103d60a07407101d0000800c060b40d070640e6406002c1060141039400380e60103440ca584503001e0000c54100e290b5003007031040e800032950f44205424a105a00422003803d040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 113320602 1250 113319352 113319373
    0x905090f04110d121e050304140c030d0302040f06020a080708030a0615080702010e06070c0b0a0902030a030909051f03030804060e0708010b011e08130c0e0c07031d030c060702040f050f010305 84
    0x501c5c02d18100402960764146940c40b80d031100041e20429581e45c0801303000f461041503403540c08214003082412507480240c0c40e50701d401c8905008004641c400801d54001c54007a80010fa0030104a50019501c840110b481c0d40ba030720814401030009400c200326105201501201464004501501c55011a40240030080321103d0742520303058140c0e545400f00b6078000348000025861588240d008000d10000900102d450300000d1501090080a03404180d41040600414039180107041c0e00081413400c2c1d00191840030f10b18100e0b20302902c8054200010000854204501600f101d040c081480c0708861005449030402402000c0d440251404102090075442d4101915001036845403199191801c01c0d0b550600070481c1400c0840c01107941c104c6004002c220030707000301c0c99240601e40e00001c035070325442d0302e10f0060180d901585c204560010280e400306059030b800508048600000c0c0d5403140c80c0c101920218010b071085100c000840f50900701008410409902454104d070300407803c5607500801d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 113321852 1250 113320602 113320637
    0xc020703170703020f03210109090f0809040b09010308040f060305090c0103090516090c08010602030909012603030a0902041103240d120c02010f0905090f04110d12 72
    0x5940c44010704071850503040710845203a800242c8000c43c001d0040d20350001240e84814110741c04100c4d14103103141c090440c08900a01400100d014000342c0f0400c001d040c00b076441c3c2200802c48401c00a02d40e8030002802045500c50f5005008020805050040c455840b490000f101c1c1d045406500240712001c20001410391190084a0051003020082d0040742030306401100a0041c1c0c6205441e544101403c10001805101ca0640200b43c1c156000801e5002d0030001052010107038071060456006011031015a40e542144a044541e0b4186510b031240c0c908ca11209403000c5030009103442d0002200700500c900c00b5400c241225842240c040081040071021130845000c00e85012072840200b0000801460f81d0b004403042d9440010b20b1511100d80755074451078841c0240d000b04000441d40304e10703081196001403c80705582c459042c2080524241400328100500040c101e511a402403400305050204000780d20115590103003d82e68001214102160184c4044d03071224009401c11146440250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 113323102 1250 113321852 113321863
    0xe010c03140a09050c060a050c010b01110319140703080907050d08040b0901030f060305010b240d090213020a0512090102030103080301150201062c1605031303090801050408030a0c02 80
    0x201c1040400601d0712028020402014140b070220303254428021089034560360304000d80342d42c0c07415984040da203c80302c080b031a0030748250349181d505100c0e4440c903400b003100740402a076030780300910f88151806041c0d07003000302e46184001d8056003440100090b000c09041d0b000620301d1180310208201d404180c6d030b520a1000f1480300c20005400b580741800700b404440284002840c070b1240515000c00c00380b0340c110300807048801980c8111096175446100700c029003000716240d200025052400300d6000760385403180d0f4840c41030000400c0015500c109407021541d0b0020309801c06603c45000f151541b4495030050101e0707004020030320316a0040e000041005105008903416282d10001d4039085920f880f12141d400040714020321b05654962001140a00210138269031240380040d104840c400441540c040c007410141554134400721a00c00000c240d50403204493f0000d81100c04000c0140302420121b81e000d120350401c4440303500f004280310601850002030b50044400ca041041100c8000b00140c0e51780 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 113324352 1250 113323102 113323121
    0x9060903040b0a03061809060b0301050603030301060309030903120809061501050703080a39020c03120c0f1c031424030f07080f0601050a060c20040f0e010c03 70
    0x540c8200300900218800102906854401c3c0c00e0110f0301640b0b4180804100c1a40e40d0b40c0c22440d662001c1c00c5c414403119000d00300c04000142c00800c19400c142010a44a1005025043c24103440b180d1540c20944200203410045400520948550380500402403402c4001d55400c0406d00ca0b4a021910301446a40b90902c01e40301615010b15005035550280d8107071000800c40e401c4280e440101c03e0410303001d90030b4610000380c0b242c00500414220300e20b050a00c0b400107100011507000c95180031854800003800d180071406c812040c1d448140040e66603180070200c122115450041c03182840c0c113004510400d64040c0695102401510000d81d030100445c1000c550b00d840039000b055409481e0001c02d48419003090780a420340d8000c0301e1000c000e91419140b6400600c0380c4d0322849940d420203c05001450162000b110300b03d910328030b41039006061244a10028054000c0840112030084040c44030740ca820001400602644c1c0594041000401d005031507052254281000d105515109110f0103100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 113325602 1250 113324352 113324371
    0x30c0a110406080109030903170c0705091b19080109050421020c0604030809040b0d02060d0c050706060602060405010c210b13022a0703081803330906 66
    0x4100549a01031220424000241c015580b18808204003e0a01035004000d000782c44140b00c01d461844c10700080c4034121107000164505100c450322292000c10301c00100c65089849480d240c031624040408410350702038030040701d600060050503092049400e072120301c480341c462480503aa09c007900415034008440040c141280d042850815488c1340d090a00c59220303e00c1240c17540d001c480c0202c0e543d41d010f500155560b5002080e5062145403500400d0303840075041d540308680d07411a13404162507010b010040d9000390b45030500c1d030700c60511440548280d942c110304184900f95031901e000c2c0d241c4c001076130241d40319400d00414031352690003007584071156450003007550750580342070304903c0040905100c0c3d260b00400c0d03007c00060440c0c47c3c0c00130302180d00d05482c24018014000215085001c0190700d01a040c0d044100c003000410340800c1511200341c8404003c1c1c010302c518100090500920304042008544000031000b81444854241c502e062824085000a5120380352540c0c0d031440112003004a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 113326852 1250 113325602 113325613
    0x6020316061d010507020708060604060308090d0611070b1915210b0901020c07080615010c020301090c08030903240106032f0a0813030804080a17090c12030c 69
    0x20705a41d000072800c0c10641068082000c02c91892401e4070000c0c1c070b08000603408a001400000b0003440004e400c00b80850f01040401c2c0b8550300d00500b800b600c4000c81c41910142c044405128003070b045010b80132101c00510b96100094070341005160070580f40905403440f4003510000491061243e005940d14030302c1c0300964a4504008a032114240104000d0036501c4505a0340001e0300c00e08225000300c441c140096100c0d2a00f18a151401145d0b9010340b0059100b8824002ca4200344982c2c0a81903030203182c22000b00c142400400e0240c14804c90090103810400800a0f071134002001915211130100c00b034503d8a0480007260205030a218280309950a187c001040000d0207071b401009041d0b074400e08031854480c4401a96448030749810203e25048001512524007a40300540310341c00520718400f62600121034400505c280e00c000d1005000039030000f80410750600400c40400003401c0b1841620080c600303e01d40e1500e17507e0244025000d0303682960b01d0314802c40301005031807828156400418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 113328102 1250 113326852 113326897
    0x4020402090301090b0405010c14030c120a0902060a02011e0c020705040203040606080a1a01090501080a0215040b070f0b060109051503151215060405070c0807020a0504021b07060203 80
    0x3076005000440d4150358400303500c4000342e112070106114901a900003d458080340c240600f184070710040c1c500c0411003c1003006500c2c00410705540c28406444c0d510441c6a0f1115a06801002c0c0d50802a52141000c18007801c01d560540282c007c10b10300015944c40d07201850030341c0c0140c5504d5524000542c1000000740329504081d80651b80c40b0340907036000300f1030b2036035140c00e1403d00002000c03da0300c01c40c0c0c060b11000044001c0008038010001035804011030f6140084c00380c0c4510349104000d2040309415000700024480e10103950113810305032500c9580d20154945600c0303401c05940102c0d808580000000c0d01ea40c000c40131082103900c046c106145075003104440402c55030005206025000a0411400d91078a681700707404488120a0000e10b007040c140441c0c0056103c00034452442181003070100000c00b40c0c441c06808006030300000868890f0801d1001a071a5115900920341080c0b01117211000b08501100b11141d0405400544844030344404080740ca910801d144d507046071100000d1503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 113329352 1250 113328102 113328109
    0x151e05010c0f0206160b070801030f0b04061e0f060504060308090603100b0301060c03030f0b03190303020909090106030308011a0403080a05071704080c4c0305070e0111060402 77
    0xc075500d407089505800c084940d40c0080d580f500980b41000200e4540f80001040120120320a600581035041000103585940d85021040d200a00001c090608640224041040d150001800062400b11104180c00c5c80800c0500601042d030640003642e050200000da40d08040c410502569080100c0c585030075069002d2005540c03000e002c0b85c0075454207500019007800b410b40558040c08440e69040b0b011800c1d400e008081d110200d808005007498400d418a180d03a001500120b40c1c00e4186400a60b07050790300b020780c001c2c05405c640c40d401032503a0f1308211010342c040d480740c800d4a22a45401c00d01341d80350000d4014907059a603403501441c10030481440406c0c41c04000d80411146071610b1490040b090f82c441000c00725400c42d203800030402207000d10401800f0b01412484642c182d984450440505603600b4100500c8100c00c112000310000c108846040e100c01c0400403080a201480d0781005a080103000f030004480200010718200ca1710f0846620400c0c140482040c841c0003004240c6564003003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 113330602 1250 113329352 113329367
    0xf0e0a031502070201180306021803010218010f0c0204090503040e070206010806130f080d0b040e0a02091906080604030f08011211010806010306050414041707020120030d0f151e0501 80
    0x41c0d0602034079983e40c88040c209441030001079031140c3c48c09a140c1388034040d000001101011524070a034014840e1845100c0078030000e9480317400900e802920803162003c1580e0000d00688003079049418581001d043c441c0010080c0708035400c03101d00c017107182d691120481c1c640360280601019500000086001e14562210342035200303000302c2e40b00b0003e079410303590107909070f00c07400400f8034031a00d5403c0b40c401071071305200300b0f80c0d0015084090690b0f2103c0e980000c03c01007004261030f00c441040303806000408060b501000180c21024121500c83c00d06041c0901040a6500f070300c0d0000700fa140002c1900c128040e20709030351035444500300480030403180041d5003280780244454109030740c900000a0a41c0c680c094120040345800e00e07003155061904082008280c181e0752500381d4be20403c0040c2c011f0341d1100361000b040100740480b170100340b40503000c1c6086200c2c8524101045040068031048a0030031b9010b0507001401c007203d010a40da41c3c003206181009640300c40f4044844000e400c221f19409400e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 113331852 1250 113330602 113330617
    0x4020916020312180d02061005010c14010207030507050606150a05030a2903010e0105040f082b05060103050f0910110c0d0804170301150e0d120f0e0a031502 69
    0x107580c00c2c9602c0e910f815918800840f9034a9903480d8450640b00e040c18244000070030003030070744060311040c80e1481008420420b188102810042c4120344081407000341da80105d490b2104100035952400c85060042c515001003005403041d010320008030340c6900d441e05240c2f190440c1e00e00707400c1c100382e1480025145c907000101081c2000e5160410036034003940140d40d400b280c02d02058000211403025052501b101d145010815103a803400c81403001184c0d5002d81d0342c5c240c0d0b42c41100250341d410a0003810740a4800c4001401219402c981c031000c440c041350b040a44206020f80c0c00b088190f03220030400d04c002400340e40521007508081d06861540381c1c150407444103512615000c6140c550f050b0f48507840c201031409448002840c0c00f0a102c10400074a8021115401801e2641e0455050032186100c00070f1502d103403018400300318000503a075224414417000042d08141140d51010f5030000151a107901c0345490800100c4407042c10101d860410000000c0d030342c02200080f441007100c42500001e600c00719 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 113333102 1250 113331852 113331857
    0x90807020909100c030509060408091318110915060901030b06070503040311060f0f0d0605091008100c0c1101140409060e07030e0604020f0109170307050c0904020916 73
    0x4100409078844059190041c020140105558843e45420800315a002d141c210101414441804079a01c400034031203801503004449607540780c20070320008981d100c80000c410000303402c00c100b000c4039003249244865084e010340c08500b4641102c030100000006c00b182e01d061401d143c141c0c46500f48c01e06001509101c036040c14006221b03d90200043e0680d04800c0040f203c44d88000b40c24020400d03800302c443d0302c800c02550300509040000030303c50014000d0b548200e060b00d0300820100184030442d00002d0003050060002c0c2e5041c1009804050b000b0310900131a0814803c2484c0b6101442c441d04c00e1441341140e680c0c41c90346200c0950383d000a15410032060703904108210300c2d881d05801100300200300900080b030000501360303c3c182e07141c100001d00810f41c07000c0c1440d10b2010840700ba00415101d130b02aa0440301152010120001a1b51100b450740003c0c0d01c60510b000c0ca410b2500f800002400709a0090f01202c0c8612403480822204100c00c1760700035000500d190200d81c40080a01c5031401c203545a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 113334352 1250 113333102 113333107
    0x10614030a0b19020705030306120607051215130c11120f03060f10110c0a1511120c0312010b0c031b030d09210c080301050d080d0f06030b16020604060908 68
    0xb070f4040c00590708102400d481daa000002840568906100141d14000f008800b41c40342d450300060103000ca010310390042130700c521003900040c02040d240b00c20850084000704141240035090402e00000d00c6c1c10044040855021280b080600500080c80a5a82c2041c125686008c0d6030f410b8144142e04054443d41c1c101d0641e40d00010f03a40c2c0c2c0d0b0b80036080d2028103a501d840b0b00c001080d4403240b60550b4032144a001340203501090100d03400969514455078402d00b03120b410103c0340100c3c3c0f490120050302f801014400480e803046880c901000401440300c01c000803012590300d801c11422b50703114501c80aa503d600400042c40c03001a49001c0212090350341c41a030741810254064501a110546400c0342c8044016500800b110244d51031300d0070030300480ca0851104405a40c2d13510b030910040c000c0c01d101d400600083c0003041514402c43d10a0000740b0317002c2c4004051428100c01602d81404115924544d0b000003c03070f5007074114891340c4a40a01ea0041c05180c45988642004101821301039840417001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 113335602 1250 113334352 113334391
    0x2e0b030c0c070302091e0109020306030a110102191506080304050303040515040f080106090c0203130e130807110a0b070b0112030509091501180302150c031c090302010614030a0b 78
    0x78102260701c1b811000344031204051a0300e450f03041401058000521407441481488001e072000906003190581c000c16091107150a10b00503440c140c4582140003401e00c0070b090460401400703039580268418480d4090140710b45403200c84e80c5901580c010180c0591082c0700401071740c0b410710b0802c1c0c20b503002d9211451a050326140281d00007006904207031482e070346420041100c9001032061501ca60402d2006e14148040450408401007062254504220b00480464407515107000040440d42e403011085540c0c00c3c443c0351000e507044511910600c0307802403400004036610004115451258440c04800e4540c2c2030012001603401200c9060b001c1000a02141082c1d44800708041e024501c0300c4840c011012089000520b1564407681f407046220340b2a00400c0143c035400900c0d5241c0081c03410958944200000c01031840c003e140b200300c215071814260800000b03603a07201610442c020750080c000151100400e101c0d00c0f1400c000160550301605018010a0003c0c0c0c205800629000e44046403448 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 113336852 1250 113335602 113335609
    0x3031104090204030c050d0f060e011d07090e0a03020607050d0603140307050d090f0308090609030a240c1209060902040204181a03030307080910052e0b030c0c070302 73
    0x5410040c0701542c001018014000440d81510091030304071681c1d21030b2141c6507210003200034003400c01001940ca800b8200280007082d000f005032042c81903040c8100c100500e002c160303617000c5481184800c034540303102100581404101c03489980c0e09900180300588481c10111041d40c4055150700d400303540c410000c00082d4200c00c550400d15150f4008540741c03c058103199083c070602c00d00407400c1c13102c604003c11072600b04500400403a0381000c8a2500d680254010071200d11030030300740700d5250050700804420090300540b841c49683d0021180c2e0a22102c4150000c11142c100d4400f6010506000c00b00c1c02610094102c04442482744d200400c01000b0703980480c069800c030f604802d524964404c07a030b00300082c140c82001201441c500d06400c1c4c1c001d000300070030380b03030f10020300400c0400c4a92800602000710811042c11a402c196204004924141581120450b0b060154035083e206c0031600085a07101c0c68408002e0303d000d0115a851503c841d10400074580c0802000d00b6117006080f0b00101598 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 113338102 1250 113336852 113336857
    0xf0c0c0b070e1504031b0f18090b0a050f09060c0301230a06050415030219050304080412050a02090c070b0f19061203030b010f050d0f020403050615030f01060b03060d030311 76
    0x2d40f8000c200d40b02c44c1549070100c0b101030b441e80c002520114400301040740c460b40d1b030088021520840094104c940c0526401400f4090741c0300c0182c15042080280107690745242d03c100c1c4039840111048410f82c40d4034140c1c0c0d85900c002c1d10040702c469018401071201c100302c1d681c11032072851458075048680c500710f408100300c617141c2e070720100c0441c9021134101714041d0340320640f0179284480e24003140b801070f1200000c010b014101c150307402000400b000003810000124126000307040d03ca401c540d00c81e50f103071070515604d94241c01c1c200e008117506d03808518030070001c40944403215400341b0411982c4d135407140c203c59614001003411540d14008410810441da0622902010344044285e030352500d0441d0030f0240640301c042c0e070501d041001c000c2440d80d220f5400b005403140c1c0c0044d1800490340a14800110b4003a01a682018082d4000c070018402500101d0000c1d01d0140020b5041d20384045008400c0350880b52180b242208508040001403400e2510580c034688582c4642000a03c1d012420280050b0340c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 113339352 1250 113338102 113338129
    0x50f0319090b0402010806060702150d020702031c030b0607050d030506030309041802030c0a080d030e0a0c06020102121f0b0d140103050604030305090105060607030f0908010c0e040f0c0c0b070e 85
    0x1c2c046441400305650b4032000d026402101918007610384990b941c0800c0016082d0290f1280d104408166054043c100b80c0417281119001006c0743c0c2c900c00d81d02511603000000c101d42c80d001c41d1510682c590b403418407100340d400c00c0b50441d01034641d4030304a2109501900c0000d001a6160000300480745142d600d41c0f04081c51440008a091800d2109206151400c0451556944a030005410070001c1a0300010000301c4203400385404074407200444017003031030074402c1c1c080200712001d601800f291031641513024101e01d81184084480d03030f40352000c140b01c90304640503440003589a0004280b00d8051f00f0401400c1d855604400001c42900d48100648500000e0b0001c032100c0d0032003414442816454090795800c194040c008003ca400c05600140075407080b15801000d0200004034228001d0203880b03a04014480c500c024458100c0320b40c0001d11140c0b44900142c8038914003005c100c000364561007a1401c0c8901511225040402915001c060350310080c4400100484070b40c43d0560740c0c69850008a15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 113340602 1250 113339352 113339363
    0x10902040609050405040807140a0b0403080925050f0d02030a0c06020f0c010c1410050c0c0106080606060301141504080105060406062f190503190906050f031909 71
    0x56504188000b000b00e229a4002480313a418182480b002c20101c80441d5080c1c3c2c4c1c0221a255440c1850316850b003080c90101001c2c00260401c1c1c200710900da0007180d418421410034080da1580c0c0c03500b800885010382c262952219191250406024a09011115042c00c483c000c0c1000ca8952090740040e24143d001c010880302015904820440d841e01008000700d8000d490019000d0900714200003044081d414001500242c259011525040d4090000d044803e81d501030520491400600030401c030b80c058601030710251f01c3d003940001c4c05000802c180b4054000109060f14691030303c41000407172055124006e13808180b0820704502203418800400c000d080d640e0010469203841400c00040b104941d010f0810302c41d40090145440320b00c0085007648046292402c0340120700500a180350940300b607040141003040b09491000d000c80000648440c940f031231001d01e041148240112601d0303543d0301c03415005c1007040c0a912001c084120103903a0203e0f0b42c0c103d803402e401c00003402100f550301040b4160f55 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 113341852 1250 113340602 113340607
    0x40302040f0b010f050f12070e09070903050c030a0c121e03030c0909020f120403050903070605040306050a15090e281407050f0105030a0603080406020d030c031109040e15010902 78
    0x40c80c0d42c118001c05080390450505d10b0030001100e1141c03616100e07034001400714100d440001465580650554842a030024040c1c103490b1a200798058100c0a0f0b40c007007541c040c0300b0318852518500d000510b520103070b07510401d41c4024a16241907082043d0149400702e0300d0302c142c0481c00074500041207108a20074020358000c1605401c448002d0012791141d0819000b0714010885103210024007411180c2241403110001c5440d40c03941003c4440b401205016545401190000200300d94888041c2003076900903c0200a01d844048a03001102d050041001800f80d03000e404108402c3c80d5440140c414042505481c1081d6100c11700010f0164092440807603e07200c10a418103004042904640310b0000000034009541004002131892005070f209604014000002546180154003c800107550000825488070b440307100c081c0d204d0fa0207014100000c1d1070183c0b00f4800d43d101f4001c1d901d2054000319080d1900c00d094080c003014200c1e416a107140c0d441140c4191010880d107000c10360007041520001078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 113343102 1250 113341852 113341871
    0xc220f05010c0308060907031e1a060a020616020a0605100305010e0a0b01090b0406082b0206060f0105030705120406240b1818042105070b07030b06040302040f 70
    0x4a58005412940c10820070070a084000703500041502e40016048880450075583c0743e0f801c601038586807504550718001180469481031240d0816559010040d850081803d0f60324244062402000c0d001401079001c00302007406e4036004c1c000700c2d2021003184142c4018810b140c45140941d44182c41e804036912083c80c0030801d0110a00c034400c81800f03003a019186045e8162145025104103028800300213507145220042c607680d0ba03100800524005007541e00d000300c81c3c442902e08003100c040c8407019103a47c166004a0b144040303040c03445140c000301844051403104004451135003005046d41c0510400304072100c4614205581284030b90b12540c408035010744030462000070790703080c61500e601c410440e010900c07071004070384140c0d1408403041c604564981100b1001130300900c1405055075450400600b4072040c802501e42c0e4032417a80c8450105955211100c004a94920901101a0911103440c022804031fa21a4011100c05200200254102a2a40c00150032102076201c4603481c142c2d101445c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 113344352 1250 113343102 113343119
    0x1e130609030c061110150905040609020906030a0c060507060207020306040c030501060f050d06020c190305030a0c0f0f08041403210106050c0304030f0f060905210c150c22 75
    0xa030140025142c08600010344d180080d986440302800e0484640c2c4441c45603814020030305034040140300c040400c1c062400c080c24a64014060007106900941c030b108002003250900140480c92107a00c00300403148d152400030121000d400c1400c003201c52a401304182c00160340c0c20800350b4011409900000c2005146117041400c58202d603100b40c08282c454001000155900003a501304150040700240ea1500400d40f03450400842c1c60101200071022034007041030507409409944540d400e03040c104141e100c84402135401800011140c0001a403071003c000010b4030480d84a5040343c425032168400e86001502c0c1401c41d08441e0028041a80e40c1203220034001c491400719004020720b007480740c42c00060a200a8403480b50b408054540700050b1801001c010742c801c10181c0441c0c0100c1c04002415446c903086440c1c0f1000b46c15008029207800c40241229003080c112403402c0c2100004003109010301d01e40646900e0b000348030043e502c00034800401c2d07014520104500d070806407000c0c0300d2254100702d0320 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 113345602 1250 113344352 113344373
    0x5060706050604061203031a030f1203060a09050106050a09050d02060417150106030b04060e010806070c14060c1206041401090e071a19020601030f11030c0a09230c1e13060903 77
    0x181440781e48400310b603a2b0146008189019818004001ea80d943d41d01e100c017152851804c0c0d801490041e10382800042c1c06030f403002c041c121048403a62060611999a0701700b003003090140d00080d6011004201c1040006600c580b0f0401361a11103099418110900c1d40c10b68034400240d1210012070b40300c00d048000d070718280c4100805008201ea4104e150b50400d41c25550f1928001d00d6107041c0301124148001748000c0d0100e03072000088180c111845486d240d000010384c0e41201c1c189203000800e45d004264685064080e01b40c40c6051207105044580c80c00100801410b01180601c0e91070107000c00c0410485000d0002d4458260303401d01032541e0350b80c200c103498400f407542c2d0184011034004400500c002100741204404e0a5040351880017182e0b40100020306207000301c00c9103a8440e804800006404000d41c11244625098050107901d00d2000c901d0000d64500c2121907014a0804020a0030b0b07012403c10a507641c846c410b082c440c01c0000290040c0e9002c28650007036004105132034410020454030900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 113346852 1250 113345602 113345651
    0x1050109080f190302160303050901030e01020a1e03020d020f03040c080609100b010e0907020601080607020d02070306090611030a020702030606040e150408161109010506040506070605060406120303 87
    0x41a49940c500c0440351107a800b10040d901d0512010500d03c01e051081060318034a042e01e51500040725603034980500164482081c550100e4107081410300b0031041842983d0b01e80845072108a60b5425810741031414000310a02401410b5080c01100d06505003407024160000010605503543d0410341080300002b2030a0744014550f601807400c0180403840480c0b00c100b041501400031960250440c0140d840360125034401e0380100d030034010044210b5000071828103c4406106858580e11081c030700321380341c40009100c038000d07a204503410400200c055100b031040a01a00002858052443e0285c000c0d90003590507400203074012070701c2010341c90705100300c0c0e0308202c080b00c0411440518188140c1c0303800c5101c40090107050050005014071910074100c40040510880050050b00b540c81c4c0140c409603900c1e103040c000c501e01c1c00080340c1420a20112015504010702c0c460528202e0756502000e0000140407641258075031000045240b864400d03111603500c252808100c0b040c0e45d06214012314200c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 113348102 1250 113346852 113346869
    0x120e010207050a080306031509010c0306061d010503180109052407090e09010f0e0a0c050a052103130b0309060a0501230f031b0a080a030e0906011b060501050109 71
    0x210740e00028000103411210690300908041d1030743e82c1c403000a424018101086c0d0303d80e114000c00c00c04071403819801090700d0409a282004950f841c0c29046900340c2009400090311035070320080d01c50740d6000e04007441c1d10000360302c504070b49918646200c03429200f03904001c0f80d0f20b5020008003400000c040325010030002191480303c2540c038209800400002c018842c5025184129012801c40d03082900241d5007604044401c2c80392485685146507180740c01d01040d501c4d06c130050707004180c0c0e00c0c3c0b03940e090003115030003405030541d000190600703112598900d40c0300106120402203944ca90b0b28004030a801000700c0e1801f00e07102c0ca0300030580790501034014140c20180d0f01c0d01006002090110142219040099484208255440002ca50414000c1d003042ea45031240102e484281042a4446a040001075400b03000305a51000015510582c1b0b600060100e600c043d4080040e0414030030040d40158145001d180380c20038520740c4e580700c00348007409652083e1240014016942c000906000404504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 113349352 1250 113348102 113348107
    0xf0c14030d050c060406090f440a050a020f060a05010303030b030102070c090f241410020d0c1109070210060803040605030f060402040f080a060b1c030f1e120e0102 72
    0x3120013034071800000d200500b110740d41c06041003840560b510006640343e01c5000891309030481522100a405800a8841c0c0d246030610307003040310000b40208440300c10310001a207080070a241010b035000d4000345004000c62140a402451100e803c02603607001d03982030500054554118100241a2091084034502907030041050500080c0c801d60315100302c40d600c41002640743c01410181c0c0190996031066014210b901e24140402440400000d0480d8200400c0074115517000083c040c0c103003d0b800380800903800508580344582c1c0182102224540300b8410085800c0b02100010312030101901c9810060740440b110148580349442903801820160006600b490303e0102c00070200d12000f00f4442c81254100081482c585a0781c0544000d80300c0700c56451030060b21408000c0d0b03102c080d0041500d40c241402c0340c0551604210b041c6c01e400f150315040150300c4802a480a9680d245010070200800c49084031410003030f500119441c0602e4115035840300d14600e22006072080d1102d8806158559204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 113350602 1250 113349352 113349367
    0x80f0705010504170f0d1713050c04090c080307050c030706022b09050607080a020d050f0a050c07030204020408100f1a040207030e31020a05030f0405070305030708070318150c0f0c14030d05 83
    0x8ad0b0110740030710494000c035441070b5600e000380384030700c6540c003201207480041031210800c403006c14124903075003081d41102c60300d0765a4031040b65204101082b64044a200d0703800344c001802001c001040901060600003039640d99240454541c4d40001c80c20b5616000100741881c60384c1d41400130842c80e000341e01d0114248241807920002c203204042010703040c040002003980550b04207000000003103400800441d100c1d5600d03240e0315213609410070088034161401e0304800c1e9a0070584a21001400c11842803401c28001c6814000294404a415001d114042d441019684c0d141c1d00105030004003549c2c42c007062208003070000c2d803000100c810980303010300520a04001d01e500000380c0381d001c01c08129807003141d1070741d0510909200990300301910318000090000180702582004100d034610a80d80c1c80f4803c0329098507070039440228010550b14120310042d00802074030489840004500078100000246103903030310490151460742c082c0c9801059442100352524051101e4180219a8105180390001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 113351852 1250 113350602 113350613
    0x501031202060903161a01030c1503020309030d020d0f0509030405041107050c041d010c020c0f010c0c050f060c0304080c1008040b01270c0306080f0705010504170f0d1713 75
    0x141e0080c0540c1c8141c58117100303060043c00004594248181c090002c1c031540c69080c50380092005000344002e50302c0c04160003541c6440f03031003140e228120704805075050160880382000654044001c1c11201e907101c1ca86907200460f41e105190040784980000c41c0e40380d00c0c203014041035840c9034103a0712050f0002d009003808250003154400b501182110006410742c41004881c840402c11109800c556280c000d624400e141c000130340703043d1035100720b42038000c4c1075204004451460310000014180800c0150401160500b0306002008400c010310346070500710403180143c603582240e440b005243d4072010040001c6d003428440c409040700c1d2840c3c81201c920f040d49500c81c4560741882981c0550b41c1c8049409903103801c510701d000e1000003031f01d001e0020100040d0b004001c0c008500400034036014240100b22541c2000400404895061715082d0034503103429401081c1000b0585d48204c03500a010020740717465402c0c409004030700c1e00741d2075502c1d900e88209846881480c005041240248040419002050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 113353102 1250 113351852 113351857
    0x2030909060d080708130501020c060301050d1202030f0d0b0a050d05060c0702030a080403060c0207060306080c0108041e0b011703041202060912070f030501050a0c0509010518060703030501031202060903 89
    0xc1c0c003514010500c0c2502d103065041803140300405001408080740245503484403c20a03c101c0d6000d9085448001419040204038482032140313582c0244245070010001d00c04c0312192042c40c20314010350f408c0480c41c1d0006070841c8d0191209141c41c5958041c00807252801d054900041d0000303071407042da50720300c40e602d60303541e10405030036090034031000b251500441d9010003007111078580c8240c55a0319541d503454030b02c2c00f601301d4180c2440540952840401e041d840780c481c08085071079240041c06819198401900d0047e40035205844503045803211480520012048d442e42610070712000101d58036207400c001c1c80f41e1141c400d001407500200020071200120603540c541300b640464103944c1d200440c8002844c410524101451603000342c84000603580c61448600301281d0041c40203001c40ea82d01901e8004440c0b82c00e002c40042407052003040c1030341d48513030050a003ea510000c014031500759a800103005030020072085000a803145c0050040007410030182d9660b045034001000c41e414021030240d16030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 113354352 1250 113353102 113353111
    0x1308060601050436020a020609010504080409090201090306050c0a110106050102030306130b031b031002040e0f060a0905100f0b090306071116080a050c0102150403030c031407030c03050702030909 86
    0x80c604102142035a603858440413042030086462407800d48035801d0740010750089145500907004082c00214955818040d0500c40c40d40400414907240c2008801002410811403d9042044600d004030000358140b0074107000b1002071884e1500c41d00740c128020904100481c6888007641810b10411407030340c001051f2a00140d017103901018481039081800c2c003e0119422140e81440781c0c410005491410042d20130f162074096058a03d8407400c3c0300782c0310580c8520701c50346040214010001e0100307001982506d81050004280205499440c0b00b501c050350015a00c20814a000460803c96140f400c414880203140000381513007090031600019031030f4007000704000c007807100300c042d41c0006910a00c089032038220b0880080200350b0700c0e001c015548040044085031035100b401d100202941c0000340d41090750860f01864032443d03856540407405840d00d2407a110034982c8802e150742806800126051041c0c04950b40041c010100103002000c0d01c1020700401d041d50010403c8400a890300a0001e602 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 113355602 1250 113354352 113354369
    0x30c03060d02030d0314060d0503030c030915010303090509060108010303120b03031c02130504060e01090b130908091f0504030809030a020405010f031a0705180109150513080606010504 81
    0x269610a80494803161444800a515018850b0b0381000b158166000b030098102000c000402c80d07540074240a1103c0800c14003900075402400020b8841402400469010a055003580c613000741d01401c8803c3c0040071703002100400c0900c0303014031541c141000c0303143d4800803d203400c00305949582c5001d0502025000994285502d0b40c04802150301c003081180c4100010321400c0184048241d50030000b034004203041c02040400c903900168500d09070203650700b070312120360065025911f80710007000103128a0f0007141c0c01103c0c8840c200e00c0080c0310311034014000d008040407036032005003c040100355100d08142e0700c803004240f1202220341c2d900005503020741e640244040d96030070210380000e14000f0f000b0780c000c0d8403d040c03c002007440c061081845013140c0c0b0508692680c0c0e81c80d602404d1002d101200c0074000140f05114900b0050b142c030120450200041c102900f650386c58012035142d95224480b02804a43d00143ca10750302016140008018030458000c1c08442c2040000200544118820011f8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 113356852 1250 113355602 113355607
    0x3050f0109020a2913090f06030206030f1005130e1c0f1101020f04260c1e0402071a161d04110d05010602010c0306050607021305070e030a050105060301110f030c 71
    0x484440302d101d81c0004c0d0b824240c04544a54030b071840300842203d980244840359040c045101c8540d00e4134000d560540758014616801d5a8031600c8801d0008401052100c503900440e4000806845d00022414000c000120100d80d00c0030b100550341c503100000e440c0100c02d02e520944a00b58541c0440b42503141c01e1070b80b61102c0401248040b081c0039008141c580c04486800050009000d507100070a000811010180703003280802c440303403c075200c8900005058020021121071412285c0c400004001443e000b040181801c80b103407104c41c03600004145070b2560354950350a10885c01040025031110702d14504c2d11020320440f4510520302c014910300380341d003d551180f102010011100b02951088000110200015030713440c48024080d03d481441c5002107468040d0100d110b06240080307030040754015000c00e01e012505400c040040400825403010400e061101385130958042c000304110a010b140042882d040c00e401305402c41721901c4100300c92100801084400400e29400d595001c40040762854 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 113358102 1250 113356852 113356889
    0x3080a05150f1c02030303100e011203021510230f04060605091003140403020d0f141b0c0613150302091c02011404080a06050708010612020c1e0703050f0109020a 71
    0x303a01502c3c01c80080d0f25010100400c01d0080c4000c00840480d0340310021040e00d40d03a62076104100c0d5484100103001a00009500240c010902144c41d8209160404e030203030403980c0b021286c1141cbc04100012546d0b000e14203002306249001d010804034070b001140d04104451500c4005000e5100c0d150016000e10f601101042060b4042d07805107440c0042540200c51074500f030f2030020745903446400302002203a5480014048507200d01c0381400ba15444102440c0b41040000041e418a045401d0310403040c0b05007911500706445100c00341c40181d00c844101a0701c0750070544542e90300c0a101041601305032062188081603034408503044c2080b0b241803032114103c0303000c0c0012104a0402041264007240016001902003400514000414040d1078100103a8440134000c40c3c07588400e10a1000041100340150014030ba075178002c08003070070400c040310083c518040220440605641c500b188542140100300700303100c42800240c1d03000e00c042d002080814102e07800100c20041c603000383d101d817444c1d240000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 113359352 1250 113358102 113358139
    0xe030a020120070803070b10061407050708011505040f020705060f0c090901060c060f050609013005031201080d080a021b1507020c09040c0b09130903080a05150f 71
    0x10002105500e065401e01501d4589950380d0350706c031001c00c6802a10020000d842001d900c8a40c805807a5166607800c00c0040d4101d050303c440d04907520941c1e142c000ca1a002031501000d2050810501c00202507a640d94940342c01c10085405151075021860b004118240009901164042c0c0c0529140184081915108104000c0d4003c01c800f131030b0404510300c000f007035480e00214000c00240c40754000b030003920002c140000c203560080d541550080921001030041c190300a1995440380341c03070700304010389001c0e050700c0000c0c0d07101070601604e035070700300040c1c46003804070704850b8601605000d8010401d00c0b106034401000d810000302159070860f40032400d06100000c56508c0c039000302d5648111001008180042c14140005456900c0984100e1003021040d0910103101845140c201c0604480c0740e01d044984021030f800700f10b44030380c00507940c0d50102c4001941d100f541c0704180a42e0351100c0900d0454103500441e2070103402d00c194a100301c0e5038084140d8640900070040b86090b82c0d61030407000ca0030b051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 113360602 1250 113359352 113359397
    0xa03090f0606091512050a14010212041b080f070b0a030209041e0b04060e0c07020406120309080705010503061e0a09021602030c090606040611101d0c010e030a0201 72
    0x62400341006800140c9035001c0d04000d041c0c1284c601c0e04140d4568039034605240c20504035004240f03410002062001c14911110803a03410681c00003d8078200c5a290502d0106004503000c81d400712948034030400c60000c0950741c01c040c084580080541140d154145903560030a441940c1000c0d20006030310344a24801c1c0c064424842c0060000c1c440c440460240350b5180e00740c0c100c804c001502c3d1034081e80141c03525005d85400c070b4000c10044400c0783c4030760b603c00100d540025000d90b00951101c0001403007611b0aa0032482c13480c0241d0711004080e04044455081c81290752000d81000b10034003d000032075403003002c01e044260b15034242a0310b131813184010032100101644102e0f0094408038400740d0200e01d450520314040c1c0301310281c0d5038900006040106284040c1c0b21240c1042c010700043c41028010500f920007076207200100d03003a404a0904000c2600d10421640702001110100e241e4055401c000d212031002c2c090034286450384003d000319544a0b05090043d0410218449051707150305403100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 113361852 1250 113360602 113360633
    0x12030608060c03101a030603150106050405040f06080a030809070609031e05010f02030c13090510030b2e06031a01140a050903070b040305070608010302090a0c020f07140111060c0a0309 81
    0x1a98010203480845c0d40b00560801c4070f95034020b0140c564003108003070011020a040c0c0308240c075910306181c00d01003408002d0007202040200d06a03a40d001254105040040ea048903220742c2c0c4611840c500f40e1141400e02400742d12003024003a1403401031001a24207141d182c1c4100014840d40ca44c001d00703081290161001c240354802c101d100000f400300d25202c00d8018405d001c908558003150036074039035089085480032100a40c800007401810f20028070520050b50304039003c03d45044080d80c00c0c0c0980010340c1045680c6200b80320150000300301c410b415024100325a1280c00780102c04040690018004c8084200010100c05c800071312004c240c0c0c050016a981c000303000d81282e4801c0e4481d440c00860b980280020759071845403540010b0710030310a065850689030701078801042529000b002c0409042959090340540c0070f11035440390100030401156000340b00c00d00407209801c1c1c05100240c4035011440c903481c61608004100500405208211403203000145000034600c0410b08001503403000080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 113363102 1250 113361852 113361869
    0x60807090c050d1d0106080303061003110d020d090b0609041205090319080705010506060301140d031b06050402010807050a08011a09060c0c030601170d080a021b060412030608060c0310 81
    0x601800711255500400131840325080020441d46483d00d010703640d1790004035002944011004500c1c86554401d4010105807503c45d0012414030046200d40c0701070b42c001d4601c41154650301c081410038000300d10b1180fa007009013039800c0c0641c0c0c00c042e01c2d4020311140d031780d4a15017807000c00070750010300303490800c48201e940030041c81d420702450032484c0150540c1c0c08060240c0e515820400440c03498581941228100e41604200384036006100040c04803c1c218100241c051141440c41c90040e020130002d840e13045032151038006004d16061001506184000d410b24040082c01d010800354160000304460648a126021000506c6a161400c1c8244210307911981c1088000ca604040c9040c00520460317125011801d0b0340c2c880e030320759404036001c884030540d500459108010412aa43c0920324540d00045640310140c07803c003800d10708040341110f00d45184000e034031030000c110620640b0480c0d210310560b03c0c0342c240500c0e46058040d030342d211005030500c110001c000020840f08041c0001e500c00909498 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 113364352 1250 113363102 113363111
    0xf040204030f0b010e010506040312050f0c0d110105010b180301020d020f0a080f04210201110f07020109171f0e0a03030501060f080702071205030c03070b040213060807090c050d 78
    0x1d1510b40a5078222103400c54001c400c40c400030480b000700c0201e19058071030181107141858903503210201c00701950351405050140401021a012114400504c7c40000640040100c0c0310791880c0103000c06da06150030340d20b07645044010302602074a8400c442c0a4842403651a125800e130000103402403080c041d542503190301c00102488090503810240400500070348aa141e01e80c0c601c0b1a42801c3e6100700c0d0005c00e19124a00d016607500103032121810614098070001403103180e0f0b070254000c0356120511140039040e000c03500904541c0c3c040e24400c09840d60340d074840490040802e005640c7e406006060500c072840680305c904406942d400328994080f000c0c101c82076044941400740091070280191070004610745040e00d2010f01416806001d00210350040046910b02500000301170007003181121580001c01100b1090040ec01c05081d18500030030100030513061a10400c24808110310b55003180364241a001c010003440840c00004440c0c003008049114100b07414121894440c900d1200300481c0b90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 113365602 1250 113364352 113364359
    0x409020d050603061005030c120a0b04030302132304051e0c09130c0c02100e18070f110a062d0605030115051f09030c15020d14090f0f040204 62
    0xc54004030b01469054094580d82d8940c1c0c00e00082901c0e460250b20f0301a408403800e000c0a041c4092001d090000c06000c0d183c00c4c40055070344034410303131007a1021360010b40c0104042c0007405e111040c40000b045030b04440b22620021503c0221044070380d804c10391040755150009980c610016840154441c41c0e80c00481c1c0d50b203003404000940780c01858045c1c0c0074601c00c0c91600d1000300c8134481ca1000201d1502c40100240046d070800c086514030041800800c140d80c4855002c03616400c2c408000742110306100f00d094500010300a0007401e04400400030050f218a010b03d115101050070440d1940103c0081032000d40590a11540c1c0403284111100b10302c0c03440280c601000a5200c101521022002408103024200e0000034207100d074080d182d8010241141040f5404502c1000108141c1c0d5050201c1240c0d6242c59858111810341e2103021541c21041c840450540d0501c022411100381c0c0c1000f01e681e4120803c0c21185000c0c0011846c0152074100d11a034050741c904a142005c0c0100620079548c4644 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 113366852 1250 113365602 113365627
    0x5040c080a060f27060b06040503100f050c090108011a1b03120c030c0a032019110303070f030903020705031c030506040b09060d0602091519140405060c03040902 71
    0xa60749445503032508000c401c4064480e02da0722220318139444441e100c0c03805070311a54001c0c03114040d01c2d03038403400c00c01000030b41c2e0b14148604410490080400600b6046441903002540c3c401003d08403a000100844162a13070050450340c10746805042e14000c03c10185051109840f81500c0c140004051071001940c41d14000010303c1945e0b8080e880c103030b00752111090701c492800141c0f82c481c91600d090001c460401d1082c0d0060b03403030341c00450a804580b140c9484560080e88031105480007002d50643ca001107907040b940d0b180b180385008008501d1403400c01c0b0004c16084d400040b0008040d2250380410615208104c941c0c050305c001010740f40c000400d2184503108074078000810010909110000f185440e09218100e02c100c03028044090b81d9a0711805c0100442501d5070458609138203120740d203156180c41d0103182107659849600d0380d4a1a504080b0903480507407000d020100b114a0214105070700400040d5001c60300281c501c80d489940c810102c44c158001c9800c030301007407840030a12035503010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 113368102 1250 113366852 113366861
    0xe0901121103010608030904020d110f190804030504031101020a06060b03090f150106030b0a0b0304050a0b1f0303050307111906060f06080c03060f030d0f0e01030c021005040c080a06 80
    0x140700710902030180403030300281801e0303807401d01c50050a0f03001401401082d0071b00360010091800140000a2448074a241070341140e000810658100348000c1035800c421802145414074144450a20802d030785001d03500100301d48204d0100410b2200b40c00078114150f4002c0200d01c194a0384003c0c18050544c44400075071083d0000ca400340384504c070399802c0301004500883ca1141c083c010040d42d0440d42e003403040a07400f400681402a40000241e1000181c41090f400a1401980700710050301081016040403000719402500003c07030b000c150f0342400e4040e8460381d403080c102c90703244c02c000f6103035078908809445202000c445081203020b10100c0300c44258503641078440091048900300211900e40102290400d40b6000301c0e0003080d90100465584c00c0418051688204010510284854280301180c1444000c02500e800b00d581d072a0b07402000ba8101c0030f081e00031030702807808000313140d41424002c0da07034a10030780c405071915614804a4180310900c2c00d0070014001307803800c440c0c1c000498a031910041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 113369352 1250 113368102 113368139
    0x7080304140106050609130c02030705030a08040b010603051303110313030309180908030f10031505060103050901050601020d0c020307090c020a050d020303240f0913051b150a0e0901 80
    0x107510f0f004020030946041001d840f120500545151800003001004000901715401000c0640c8000d00c08080018802c00041c03010075526070303071440c85042c02d00c1d1140002c001a0003010602d400d01c0c04002a80080e403000710324840d0103207020003885412089090462207020304d400c440b039030190008428150449003140840d1078000e10b01000b9541c0343e58503011903000c294000d24081040020a080b249492501500180080c03200320f01c4940c5e036600c0c0103400700e616040e004400d8030b407000c2102d03c7d80c06109035517200034124002e00542c500880002d480d8108400e00b642400fa41d690003d00355101000b41e080131300840c100420a070451504040c1d5220140c2c0317001c403007a03c902c0b0100f071f400d82c1c404000d030b038040c5609e41052080d440070340613202d42c494278000c0503503000012810407220076502c3c2813407140140003c001c1328144c01c506060170b03030500c0705840020b2042c14400400c40c1c140c1d155442c490984803501440701e07844080c40c030710483c0c48503200e1a17000d600c01d10080021401100707126000030403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 113370602 1250 113369352 113369393
    0x3032d06030b06090402010e210106030606050418170a050c0706020102071b080d080901020706060e0109110f0301170a060c1d04150302060c031e0a0212031005060f07080304 76
    0x90f6440c20104545201d040768000c1c0020300184080303000e41082060380c0e20f000f2a41020030b90321b4200100320703401c440c1a5072003a100503449501c1007245060a10400d50580f071000d00a00d2440e915844143c040e44000701c404104100000300741c0c011328400c00c02d854202d000c0c8025110ba865a8890082c040d400038138058a0a00c0c420300c03e10080c034091666002210440c1028124100780500151980a0001d08044095400f0001d020000304584201c40c013400b2003041c0c1c15103a504140e10301003200e0380381c04081880242006000e140c2103010065070704407540c000d0f035000d16142c00240e15003400c01c0c00710001e00c0c2c142803044c045007a036000300014104002c01c4120350f0204190400300015a000444d595030011401c40040c07016007044002000c60801c032b00c00f00c07460920118000034600500ca03008248a00e030200d41186030030b906002480c0484c040014460444c01c0200962100240c10310a06204410009002285013019815903410f10b03040090903032a4506070600b400c0c6200c2055070f4010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 113371852 1250 113370602 113370623
    0x90506040305030409110c070501080a0f0c0f09081b0f040908030903032203050706090219170f030c190f080a08061827151905150d03032d0603 63
    0x7142c3d038005081c7e60031848088011326400c1e00c0d1000640c1e0750340004d44060007441d240c420507a00d4045c1805400c2e685203603580c03016043c40240c54010031410440d0407256203900511071101209400355400034103410f0407102da507510180e40d4000342c004c0041080041180d540402042040306010000d54411107003a80002608407602888030080d440c00c80d002000306070103110541c04500c0c5640710039011440a45508514181040700140d4480550700652280300a0380d084000400300313101490ba220849801141403691046841e178845604034000303da1400345078581c0080c06851a15241225000107103d41c0d036655001005040d03040840e80c0901441d01c15241c4034400d81250107551213820030713185421a8401c1e4007a81e02000b1750f42c0290120512506c5500060701304c1085400780120015505c0d9030f403807400303880c40d9000d6600041c815a80c0c9074114444030b04a445880c401c8185036071501d40022040c2950615070318000941e42c10404881e41c4541c0c030100452aa8003039000d0303a0080040c42d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 113373102 1250 113371852 113371871
    0x1050709090b06040f09020d0917040302010e0a0806010513110d050601021b060f1e0a05121605040302012105040c050321040e091f0b010e0909070b0901090506040305030409 76
    0xa00c658868213100340c042c5c2c1c500300031805c20740e8007a00b501e030030000010400680c16110369540c00303441038109040c0072000400700215070300f280542c12081000e071101f0303610350b2400464980b40c040500c50706004420505180c0013014582e40704003501401d02922a0310b0340c40500c0c540000301412980b0501500c200c02400840101030310414130100d0008007628903160402c00c006003150080e940c0b6514144940308c00e40c0424803180c001c0c2004546a40e22261101d160003407280c5030034030140c88030740400140140950302d50781c04001c8500740c0f078083c00c1c01410740061125030b0a0060440800c213100f50b2510040c081001007072091801103420880445940245d0000350910088110400d00300042040100b044140d114003031180e4454140015150230307a4440024081d01e40d405880e40203440c0d5151060260b40da0888203504004030107590490051505899007542c1e802d8600454090b1000800c003914568070038003c600207400301078210354603140d6a1614a55070740190041130000c90034038030148d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 113374352 1250 113373102 113373109
    0xc0f0114010806090601090f0618050f010e07020601030f110d0c060206010b0906041202010e090a02130f060f0e040e0a08031005030118030507080d1a0108180a111201050709090b 78
    0x600855503132000c0c1649900c0c0901180080c18540c80da00a41e54a0381e400081ca81404d05201f60040e42500c4003180a280c04850150f904105030010340b0044161003d11010747e030300003540c5040d664441c02c08070078090f150900901c500c0b17506d6501e03540070610700e00140c104003d041e103032022940c658085890a90b254088540e05e03002e50799285801200511040042c40b10b580e28480380310f8010f040044c1d80c6402003000c105207032422282200035030f07000100541c03081101c2ca28000213290101c2c1c0d000b92070303040540041600303a060314000104141c18a0505450307485520007661009a401180c244d030b403170307494a0030403a0805c99401e008200314040000719400c040c050700300040c0700129040e0600e00342c0d56090311203070852401a200d80700305002110380c103403051080000d200309030101c103c0c0b00304417000018003400000741440036401d00899900301c241c0c40000d20901090303101314141d000070120004501002c1f5481a551481d60034001405283d940002100c4251000403800388a10701206050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 113375602 1250 113374352 113374363
    0x50307060c0206130f020a08010509030301061d090601051e03090a1509260405030109060f0b010903020f060a031b0807080c040602100b030307050d020102040501020709110f09060c0f01140108 84
    0x203481c002c100360303040748000944030200005c00900c0100400b10194840403500e084800465418105520000052184582009101004101e4000c04401c8030300d0360030100340703c0e85001d451a8180500401c60382489181403041a01026101680c651685001c0c2a4555103e01e03a11055683c0002c221060a01c3c8c0d90760301400c80d03050b8000304102070600d4001d003000a9080021070074402c54030180300100e484c0e0350a00800994034001c174800714003040f881403003004503102030301c84c1814803c56841c1000140c441108452070550100d42503038840c94260f0099019201034a0121074100d0005000c0c4011a0090250742c000c49403552517500c15682c00700c3c0009184258001c110160340102e008000083c01500109292500601a40d043c00f00c241d880525240703602d4045c5005d40d40104013440107590401c440c4001b480c1c288c00c1842114104601d82079a4840c1c1d0b40c0c00105881e000076042641e869a40c1200e921071200c02c00c40c0c24961202d02018003c2030070072201d100b0264460f0000644620000342c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 113376852 1250 113375602 113375611
    0x9050a2912033f010e06090a05150415050a0e0f18031c09051518071d09011517100506100c140102040b04090c050c0d0e0406050607050307060c0206 65
    0x24030700e4075043c6614980303c110b03110f0041c82c3c00d40080001d00085045107100101d0081c0f6052460081c107080103410003424000003042c00d42078900e06030400c10600304441d0b000061210507035000601d1006440140706003248c6400440e0004c0d071015000900d041e60000b00fa10800d8011003e00b50380e202e64100d0388200c1c42c40c501101a55209019088421a240344a224859510340b000129120266030702420403555031a03071070035040e01104026544040c11031080c074020100b000380c80c80c98100030201100c012420032848071034400c0c10000e82290003d6200c0d084e00384540c03213032609240e610b4011040c00040400c005485000780d02e20111900c2d2940601400f80304010070300003078008202d13000c5503c0a00b0b09000d9070000311203c140d0420a03000c0c40207101410542c500035a42d241004034a03002d80b03998141000c1044020490701e03011940218581407a40c400d40307802030881d01e00c0710020340a400b040d086642e200b03200162100400c14008010010207102e1003003131022544481e410b0fa26803c040302c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 113378102 1250 113376852 113376877
    0x40f0509070303080c090a0b070201020105090c0a0e1806090f121309090204060b2109030705030726040b0909151e011106040b101203050409050a291203 67
    0x440034000640981500c581c0b00307071070b070141700e003441c140b000001c480c0c400a0303020700703510000003070004159642030107110b82c010f40a40042002040c3c0c140416809030003440b40e84ca0f03a120640c0807a46501c0711035441440980d02c54220340050408002103a183c2c20070f4a19030000d8800e03840c07100c41825040d420303100c0e81020414146861031408140c1382c0503100c0c0c114101da00540d1010042012010040a45201d201111600446031420219044c03921030142581c0d850ba030062087c0d400040e0000115450180c1c04182a290460b400a00201211696000b07a0304003801240120b02c00c1640030243c0301a450481e000720441e1242c191520010703589030309664011003000b400c4031400110884805800006240c114402c03901140c2036410190145d0381203a400702c68100303006c407500e02c11007410f0161810003011481c9440981d005041032040e4454602600c3c0c0702c0340015840704480d4071180d09a031420380890700380114620700c2014130040340c580610490010421521115000003900c80040814 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 113379352 1250 113378102 113378113
    0x1906050904080a031803050c0c01020c0319021f0315170715050409090f0c08060c03070e06040902070606050a0b0403080301030818120a03030b010c030806091801020a0905040f0509 79
    0x1e8440b2902c50703010001110500d501d034240b0700e00d40c0c44c034840b808010034001e503142526011044201406c0c0b0b00f40b0324000b8115030002d665001c26950104020301d0040701020802d90402c564400700349142c44c0c01114400c0784980701400f0000e2a0160400408014500c1254002ca51504a4546007140901107003000e503000c50fa040c095003155658a240c0095142012814150f071820354500341c030380050089940200401e015030800910a801202070400c000240651b80f515195403043c43c04020b008030200001012075192a441d4a801c0b070b409004120001d55039501642050381c0a00101d106503401a00d0031000090a1980c0500744c40540b5404260070303145034030310344400394035400c072640c04c540c0c0c14464042100a80c3d07aa241c03604209140401500d05d950341420082c08440da1407040c2810301581043c5903001950200500754400011121182c0e29181d060080b070390f580c0240a0f0010711340c400036440016030b803c2040d5100b1034204880c240640c00301e815616061b02e0040e0360101c2964040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 113380602 1250 113379352 113379361
    0x6030c0903153d08010605040f020a080c0a0e10030902090f0108070e2203020601030302010b150304031214012d0e0c0f07080a0e04151410021c0819060509 68
    0x3681c0c441d524510a030744455100541c10300b80f000d010081a4030203401c0740c5d0343d1541080300341014007900c0200d1508400071400e0003051000074008003401812100440400581280c400d4001d00c001a038001000d44491180e11f030040c00500280350b05401607100360410f0002032049a6403405040c10395182ca800340440d14500071140b9203112002d1b01d44540f44030300c450703004a501c4001ca921403500d406580146541d500d18200642185c5014800301d004240c03215441c0c03903048207003007101d0f005a8146096001a84c250005000500c03650700c0d104020300d40340300001100154200c03034005003081c0d0308410701c41c22400d203840d010301c03204c91084604900040000640e0520b08001078198826203041c002e00e800c00070f42d0703031036040d81c049420400820b00c039010494107400c288c45001c101000e10007600c45810f08040248070318250855009115031054003000a1040c07003841540a4890220415015489070140281003504226940518100c00d12107401e281c0841c0e009240460380c0c040d2100a180c0c0310f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 113381852 1250 113380602 113380651
    0x41a0c0f1b041a090403020d0809010506150304030c0204090507060905010806100c05070b040f0e010501020a15050c0904110702010f021c05030403030e030d0b19081504050a0206030c090315 83
    0x3c1a20b24610b529070386861480a44415010904ca60700c00d17400340510300e81c43c038800f911040014001c8112a8901001c200345510b840c0742202085034940182a100d50395031804035480029200029005420030503c98108a8009115420f4400a031114804192200700440c0c1800c000c4500b1903110759101c800c2c0000c0d0b409044007600c1c0303501400c180e411568030b648003400310f6480303507010104d207080b03d05c000c009440080d500d0502500091018200034411501c90300344400c0d442e259034002683e90300100d11240c5031542240c0d4030403409041803252002d0007042051a41000d00d003640890445000f40c0031061003c502101740e40000003015000c01c0046100300c0300d41e0401070089091664584051000410400c0030740200b00019001189011a034000d1207500f4951100f056081c1c01c03041010f01000201140100c101000d0060200456949003001c61404d2207555010350000d01c00002c2c00741d403040c800000c01c4078840c150202c41a00300d1000b0150190001101c4848400030036030010505041c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 113383102 1250 113381852 113381861
    0x3173c0a1407020303160506010603050c0a1706010306050a03080d0c23030c090d050d0207170304090213120503040306050f0408070809121c120b01090614041a0c0f1b04 74
    0x280041c0c05c91342800d40c07040402c00741d419031806c1036410758402c500411069a140c05000d81c0301d0480b01e1a2030070034807076000191211000d600415250840341002907240d0744694066401040000c3ca1101d0140d40d074201509140c1c00b0403a108446030501548420880c042e1000f80c1052012440c3d6062040314841d0200d19a0030140c500d103035000041201400c1a038410405034403441c0a40c0282100100801010b45001140d52188507400300c0818440303444040030094504840203400d000d0b030b607240c8110041022145540000079680301c0c1c0301651007030050000141041d644035080030815a20340c81a00c3e26142802c5900801d540020490b050001e0352440140c5510070010300a2203207541901d2045007000d10800c80d0809140c101018441b6541c0d121100c42102e940f00c107010010141c165000034000710f0607000e400306002d8202c1c400f282280780303c41240e00810a90765128030ba6004811681d03010ba04c104400c045c1d92003040c510424546002c1000112818001c0401c4003c00320a8103000181 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 113384352 1250 113383102 113383117
    0x50705030d1508060f040224040f0e07020f1b010c1a010b0c010c05070210050306151603092715030b090f1c050403173c0a14 55
    0x103000500201901c85060700440d0750801e40300d010401030314103200c04945401c000402070540d80c0303084c0c01840301507202c480748440400d030642001013950110008000c001e03c0345038009000c41240c000c00043e580f03441842d040c0a080c059003551228440001b034241c2c2c41b0b0b0420740350356040ca07411101d40c03141d601405234040030b43e104050201304802501e0b040c0e44945002d0b0300c0400d001100265103d03140200b8400c001c02801c090520b24209141274010032150021540e409050001c0040445c0c9180d82c0c05052010b1180c40700030007980e50072030a1300f5042c1300e0242e8800700c011482c0d4803804101184030360005203c4079102e1030000300301145100d9000c007038462002c42c4082605140004008940c2d050b135101d11a0a9000c010454400e10840d143d1801c03218180d0080c103055403403201c0019551120845003200d4010071b03140c940c0000300d8034000300c0d44104113a010980c03204202c5da4811f52269601500458010790394116001d040c00040440c0d4801d4010b1100020010481c2007240034000003d003480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 113385602 1250 113384352 113384363
    0x816050a03060b2d0c150a1d01060303090608040503120a02090301150f0b130e0a06050d030c0302010509030c0a030c05030405060307120609180305031b0d0c0905030a11010507 77
    0x55034822074440c030340e4801c2000d08412031043c01161a40013110615000d038101c1c0d00281440d10743c4a00e5250703220102032091180050811020482c900016001408404010003800c140102c45000980c003c10b100d20045020070f84031900010b1007402542c0042c4525042405189040d10151128040c01e00c020300c4920255801e210309410703a1001d1051800c603440e03400c0602a0301e07080200075000f001060348842141e000130000c410341e9100004a030700440e50050038076101c07074445001181c00313010180c20494120503901d07036007814980d211044849060094008018a4803000c030065260712400303800e1031442c2d100c0c900640001e44603100c1d498903d0b0255082d00d040c241c0f030300c00084480c4e20546048001411806000102c82c080b403050a009101e900c00400c00d43c031f1802200c0505160007000a0140400407000410f000380b1300e00120100440d02c031061b070b650214125040010008003900300001105044c0c00311325410006640001503404c1144003a018180c4001160340e5400703800212203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 113386852 1250 113385602 113385611
    0x10b0f040c020708030f091c0c060513030501020f0418050402011413080d02010203090f030306030601141c12110c0f042708070311030913050603151302100816050a03 73
    0x54001c0148094000000c044006c5590f4000300c404110109040f0740c0450701800e40d10000800040090038030a0484105041040c2c460400c2c44803000401c54550000c0c1c119400010080c00201c1008000d0040e0340318240c8180d2201441303403010003281e00031130307009002c10f00040c410070040c07000c68080c0100d400501e41d202c00700d03034a4000e0f6504060352107960b100980c2d004410301c151441b091040c000b101f4281c40041d4258a030100010b0355030700c4d040c0306e0780b04008900c607031070000d40d1508009400c9490f401a000030964000345440c00040510312540400143c0f0301e0010300041c00702043c070103941000200240754468009081000921240341c009211541c44400036210a5503078400300c0425009030085a101d0400f820040c1c600e8101d50381e003550a8004208581c21940c5103050b80f0940f00c54424001095039581c8046898100c1d850403480c50b4004076001c200c0301c92039010341c2c098614070a5890200c07407068110150f80000050703809030b0013031210141e0f06200b00d1040d0301400d80c10200d8500401e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 113388102 1250 113386852 113386859
    0xc0d03050604020f0d05011412060a0f020702030102070308040b09030403020d060b0105040f120309060503090a12020f1207060b010302160311010921180501020307060203060a090626010b0f040c0207 87
    0x1529440103680901050f118401004100c1c940317042310f2aa010242c6201d04d000c035031548400d840d000300504140c41190b989092044601003981642c07207169000c1d000b10360b980060304010f0040d02e41210120f402e45890400515442404415202100c2c0e026010310100042da60702c0d503020780350700342000303041002c103003c0003841108000301c000090000040c0c051700103042c0c0c02d0003040074040e604480300f0301408006102000c0b0000a20f00b50003074000d600000b2252640d0f03412030518580c5040940148103401101000c14880c80003041c8980c070601c0200268404000190140c0c00740003002411195150380c0140440d008841c080300d140c86001c00040e00d800345507034080141141982c0000c0d03045185101e000b0040d00100c800f00030110b900c85003d100c600d0800000c1d607034030460310000c0c8042d03008000b060690315094900310103458210420b001d41c86c1c8444400c00c020b2110301078011050001010001000340610820007041005480141103240450a200c0a003204c1490101140b00315074002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 113389352 1250 113388102 113388127
    0x2060f09030313060e030d0c02270c04061806080103031206030b04060507031d030904020a090b04080f070609061b08070219051212032206020a0e040c050c0d0305060402 74
    0x204008801d018507088120301342100100f84141d00d40c0a82e000b5413180c1c440c500c40b03e0f00148801c0b50641c1c119103841c2c403804209401540a009003180b428a24560000e020078070044c08058010f5070740c140e40720a40364942c40103c042e100018480d50300410ba28100500111784281d080c210441c1c000c9201040e8113540c2d175101a0013040498094078105d584000348051203a0500610070070a80701900041d821006d40c000c00e0301e9104a0460600c0ba5900040c10000c0307601a038103c80040a99042c80b90315140d90300345050301c034500e40c020a205070007030320400324941d4000d42d249420340301070f55290403d40300101c0100c6141d402c4084e0944201a00344800c07001a50340c05141d20480c4060001ca02c0960700d0302d4280321504c0401084242280c200031404101d0360042000eaa600650066086240b0603490103241e18a13242c584010b03019a0000070101400e6800c00300300f03070324410181c030100301081d250301c011641e40c0511002003450303802600041241c14400d0300400e4010f28001c10040c40d005003038904 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 113390602 1250 113389352 113389357
    0x120f06010507051902011209050d1808060414011d03180d0219150201020f03060621011d07030902030c0d032a020f030114070804030c0f05061005040b0d02060f090303 73
    0x1341e08001c00c40b40845800c5592080c4090540c1074010ba003445905041e03900c20ba04c81c0c0311482c0d0181040350500120300e40d090300b00f8015008005030400d0300e1050034942059840300090b90340c05075041d030900f00c4900a40d0801e08100c080c00803440065030903d540014001d4503c0401c4002e1030303104260084440142e5120790b01031034030f050404110104540342c001d40400d444001007440c01075900c103000e1003055900c1c0358100c0384e11200403500941d44540d80040020603401d00d900c810312900903803001003000214948100b0411705200c91180182c0d40e0158118240c3d00001402500740d00006000a0107091002c0072074002403007401d02642c664140e6640100f4011401900d108084a01c4194810b604214155003500341003903009001f000900417450340c1c132142c041c2c640e108000304100000c050510418640c80e81c00e500284000f400c00035401c115558120554280c200cad103481c00c600003100e181070312401e40004d2002e002c044c01d10440f9002c110040d00086032041d19518104103080c9541d40a200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 113391852 1250 113390602 113390623
    0x702010f11031005010906020a03050d020c07060503100e1b03090c04180209010506090a03120516140105060907121104030606090606080f04020310090503070605010920120f0601050705 81
    0x80c01e07450b403802d424818403030205030740401c1c10300018440500c203155010178600d200c2901402e00d640d8070000e0002c060024801d09102d08002d004d0f200010076000d600000030340c0241c1c08081c10300282d5407030f964111311682042c0d031000fa80301c1c5002c0340c120b0007120407005558891010340c1519240340240010409070f60f40d40c220401e480c9005005a4114500b14000c5405030009580442c1000d910b41c02240c140034260001030608400a0394062103c0e114504942142690001907000c80700285802c2c00d00c1c100305002c0f011039500b0000081d40509018100c07522414050f45c3e5010340b068400c0340301004040c1401d2901c91100204404800b28a890290300002d140308280002c040d843d0043c0189084006403141ca40e480030142400b0160307900144580b045008160002056981490600d00e54416040700410582c1004000544d4001c035601c05804100b00150340504541c0b840e14001d02e51140d50f0341800070060060101c2c4103030403a40405944040181416460100d02d0386816143c00120315 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 113393102 1250 113391852 113391881
    0x5010912020c1207051c0804030503040b041502010203190b0d17070303060e010303020a030e060912010504020a321903050309030d09050d1b0510020705100c0c0303080702010f 77
    0x7840000780c0e00b00b611140480c840401c003d072014a05000000f0b540078881c0c40c00c41b20103407109040200b4420244c0c100c4000b142c0c08800c496035140d49083c010110380080c443c0c0502d00e116541a803a205e401030085900c203000c21011040000b00c1704114038020705000300c0c1c01d03070841040a11103000aa5408800b034104c81c0d03c0301d60f10307121980d503d801015070324560040f180121040d401000000e0300010300c5112580e141c100100c1d20300c02c0d8401705545003e13407044540e2080e003e0703039098603e00041d400b0078082c86c0266200485c69440e0091503000c0c0499411411b02e1103110308400d40c00e051010101071540c100203104400a54911258001d0710b030190300180c82e290030000308241c03a46000c110340220880780d42800c6a03600d1070140041e0f023005c41c6400150060314101d940840481e51003072410007801d001460241017001d030b21f80003981c60400b802003c3c017803100c0640003445640203000c000c006583c4000c88003045800d65400b201e072004080d00304400c1d0b64031041602c0c00da008902802c02141c0400c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 113394352 1250 113393102 113393113
    0x303031f120605101d0a0228030c020601060e0112020f090306040812010f1d0702010e120904240b0a02010b04060306090308060a0b03011a0904090f03110607050d090501091202 77
    0x400c00b031211076103d44e201303a811700078804208140262450030103500401e04000147c40b241050265072660f20010f009581ca190345080c00600d40d43c0582c000f035500382e070340c0c0c5c02c4403402d82c2c940b082a80d140b800c000c41c01c1d002c1100410242c0c01040306400400020b11084107041c182440c0c5808645002e1082d10100d407404408070b4003807030b5640c590740080d00400c1c017000340c010801c1c80c0000c40f95442a8000c0c2ea284041d64460010b84507a00035040020320f44800011101c580307402c800c102c0f04581068007901d118505002200307881010080003000c80203191200c031501940381a140d4402c40e803101245900355500e980b8000c01c00c0c0c1d15842a48003d60044601154960b078500d4000c0109600424052007407005400a00c14840d6544c1500d06455401c560401d800c602c100210180d4060300800719070141c2045010030800a01c0d19900500703520a4450003c0510661616031303c44100712014000a902400b60b56464000da800500c4054066000010081510744500540d10a20a001d2016030b110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 113395602 1250 113394352 113394361
    0x705120a0806030d0f0f080403020c030a14010f110405040e071e060e060c100509030c10021209030403031e030209100c1202010c02070e04031e03050a1a0303031f120605 74
    0x28402d04201e004c1c64a42980b89210024000d002100c24a11900401c440d04002504041c020841c00790b031301c940201101c0c6c007000240740c0f10344840c00c8160541669400d20310030744503400c081d004c1d45d10005100005941028100800e0200a204030159110a4854840001a640780c0303442d0f155040e41281060030030715030034000b0192640d01d400340a40c0c0030307001c1000b5502c102c01000c5000d0100d0f2002480100305504c034141034a165000d00e680788034490040501a10b40b034440e40d40244055800c8400c82040395452400160701d81c0140d1202401048401040c0c059820b4422111000384030745003001400c008429001c074a410303d00590000c0810406034a120a102e2015806010640948000c1c010441307030310b0000b921107150384075007644c0ba104a03012604040c02034190034610001c450701c030502d583c4a070700024050700064030f81028440c0f80c034a50a0381c1104d10b001c000d03a0502c000d001036186885817840e80d4001309a580c90b44010200ca602d000c01c0005005944c50740d01800340c800400d15080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 113396852 1250 113395602 113395609
    0x170301080f160b1603120c0206010305010e07080604060209010903060f140109051b0f07020603070801030c0506041412101e0e03070209010506030702010207060c050d05100f0b0705120a0806 83
    0x308a1691420603001c03001c10001c9403c07150403600102c03032010001d02401502e107400d8600001c0f642c1c03440750b580d0520000f128250b0b8000344180c12280104020b124000c100b4441c41e4548006000c0d1560343c1d00030000040c04039509400800c0380c541c0600d800031119980c2d44911049401c0300c641c5104543d102d5528444481801c40a5405800ea0319410050760908884411142d0685030806400c01c2011404032116611401984d038070f250003816461741e034946000c009200007400d00007251028074015000c521170a1480c203039402e88810280e01e04010f40c5405c1004405d84d0b002d00e81d400e09100d960320306004542d50740507088150f100d80f011411041c0102090006561018120100a82c418061400542d840c0c401c2c5904649090b903145a9985424100700c1c0a44222040a0305480c2001c0071840b4180e882001070606820114003041191117041c4e144201210a21503842c0c1054040410f118040d03001000304142c174031036401c60b0200740e170312908203407181c002d044118049a02c4004001c0d2030305 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 113398102 1250 113396852 113396863
    0x607090305010c09050109050d08040506120108060901020c030406030b060c010c020f0c030a0b010501140c072702090f090603070e01170f0708030715090807110118080712170301080f 80
    0x118900700010342505090000744189094488e00b03100d00075130780580090280100450b4090322010700225540e0314100d28100a00d0004c0c8a0715113180f00d000c0009000c200113102b40d41e0300b580c10001451807c1d02c0c0040480181401c0c0917015803003e401c04c00700031200e0092144542c50545a000b41105601d1110094240003821000c107020b80c005502c00000503040c0e17491a41500c2d02428007984900b000700f085103290103101558001441244000308110340f40341c054490565a05811810007481e509149080e4020811843d40000d48104045660f2a0402219a108101404031400079a407001d00c1c400c00c61081e0300c00080e6400c0c69103d0401614203010241c0c0034407400d00101885031070305000658901c42c2100c0030703140c1201b512842c100558242c00840307519820a030601c1d05c1e540c46040030a0040c2d0b020181d039002c60781d03042000400e545041000702c2116150006842031502c0c00c80c1c01221212415001c80754150058010a03001030b2800265001e856140000e01101102e0301e101440c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 113399352 1250 113398102 113398121
    0xf061c150605180417040b210117030d0c02010b0402040e011a04320604141e031207290406271b0f1d01050405070804030c14060709030501 61
    0x4106180f010000103107000882d80e0440d61040300329030005c05400c4040b025004a0b00b02201004000500840300d0aa40d0000210004540180140d9903650441c11001d40030903009854250010f000341d04044105a01c01200c401d003500001c0b40541c00341e40041c0c1281e20941010040f159540014440c04c400102448402c03032184504d1440c15040c00e4003008560807000e0080360315012200c4c08101c10b0101d034002044902d0282115071200d031944402508400c8a40d0000c0c001e20000a0424001c4c540e40384003a043c510190280c802c00d0081c0c014185141d00c9000180e5000000c1c1da04020b402c50311312032000c0c6031001c0e500000c000742010328040c1c00703540702d002214078407403868403280300d811442e00d41300381009a011440d058803401c1480c5044100700141e114201c5407000b03000001d00c2c0c3e00b9003003040d51420341e01130381ca4489a0300c0783d0800003111010395071000000d244e00006030003e4085c401c031401060084022145105d5030188891601008451450014100510810401c6400d02503801d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 113400602 1250 113399352 113399359
    0x90e011215180209190c0305090d0906081306020c0d0903050d020a0201201006090c030b04091101030222060c0605060d050a0201210207050714180f061c150605 70
    0x404008100281008242e00d0001e44a6640a40071807842e55200040c603891840c030000c01e00ca9a81a104081d00502044036048801c1c010b1440f0615400c0c42610911b0075a485a1242d000c144c60312502a01d849400d88011a4240c0d400c02040ca51204200840d68440390155140740c0518298a801070802c010000003030103550040803040c0040c0e0708010300f204901040c804403c0650244e5840034a000154108010308a01d482c0010038008000d802ca10081080c6480a01664440c0801c1c4811944003040c040c1c10f005059840641c88c0d8480d4004204001d07121a640401c10805507c1d803210800c154066408562200c2203841080254010b4943c016012690070302e149110391503a41d15101940d00084c10410301c2e016076601500c1e241102d88503028996821900d4000c81d203019030340c40d00c4034052820702072500305020000d03203080c3c8001e0f94200c148d6608080c198030350700d05e030441050001d000302e0780c881420303034105c00c80045035480803602a01039003480700544000075489044a07003a4018900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 113401852 1250 113400602 113400611
    0xc06040204061d0601030203070c020d05060906070c1509020325030c090207050307060b06040909140709060609090b0d0803070302031902030c07020108040609050304170d020a020a0605070201090e011215 89
    0x480783e500071203298041c07070030b00b00541d8a6880a0084444402c1c9000082d030060501c2008400d0000016510313100f1010601110140cad100e168081e101160004002403a185c80c020941c101e070101034018005051010701121500b810220360079410424083e054040301018500800510043c460345070018000c881c01146032103d00c0d141e241e1a8402d442002e0f1045447d0040c0790403544a00d07007150010a140001009001c400386080d40c241d030065200142c030f5120780354000c41c99442d113100e80340450b145900e494060b42d1910809001500030000c2c05640301d5890440c10010981b648021481303285039542c0140c2d01d15104004900c0360071000b404000c968414003c01a089018030700322000e0300d40900340309019950310718180015040c907500062503030102180c00500c200e401c00c17550f60300c02c107200c00b83d42c601d05203840100e070744205010001e54803081b5480d08100c12800340000382042c43c01850324202c0b80c4d8840022082e82402a880340f041c02802d142d01c041032100c0340341501c1d520140c0210501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 113403102 1250 113401852 113401889
    0x304121805060f0a0903021302090102010e0f07180603050d0903140a0308180f01060306050601110a0f02060a12060311030d020a0b0109050711010c18141005030a0609020c0604020406 80
    0x182d050040e032410a803080000190f1224880c05a4a02c200955004040d661070920411604010b9000f00c0400c030b01560a0200d11019850082012801003028100414565103050b2100c0c04081c0d0400911030246d50f030340404800310307000784421400812240c070391000c080c0c035515004000d0043c410500c0c0d04c9402c00215940003a50003e00150880d14948400b400f02d207046243c107041614000f0311103280c2d881c0072000000c010050304407500c01c04007600e811840360f403c03a40242e11018010002080c5815400306500107103884000f901400c0040d00d40411801c0180c29044103c0d0410740007603030140520485501189400c003c400001c82052024152440c901e0740c9081460030180181c40c0d8054440b000074100d1b80c4120f034148803004000000f032002e01017111003e40407210781000f50094092a1001041c8151030100b00e01e08240c01034091042004076440840302900041d10641c0d07003d40f10303100024601218005040d58280110140c00241400c0c07040004886071a8442502d440d817030700d6041e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 113404352 1250 113403102 113403109
    0x60e0a0507140c010e250b07080409020a0e10020c100311160609170c061b0703030902040b03030c1e011503030e0409061103070201060b0c0727020304121805 69
    0xc0075403207000b840d043d0320307202d5040e80c00d4090300f010322850071507102d6000400c2020340c00060680400c28100e4808080c552102006403ca21401c1400340098004000030043c1010b55802000214940d00d000044000c211000421300219600300b4801640f01c4000c90545262245170b0038001c1060341402c02101d02c1111b0204c03480d0282e6124400d016102880c01002d10481d81c2140b4110340e400f0011082d0f101c68102541039a400041c411001403140130005500c8075826090704943e664246070150400b10390ba90f045019001c0b800c801c90300325803510038110b12514101b0241001440380030151110030795109036146440c8684024004581c1446004072203065840b0300c8905aa82502d0300c0b4249100702e2010501904161400400040c68241c007184101c80040186001782815070081c800ea03651a544000b0f41d00030704003008040d400c204000c00ca1603281c1e100c0408421312910400010215281d81d41c0c0403070f041202c041d502c2c1c0d401d8000b8402100d901801e504200000208180074243c2440d020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 113405602 1250 113404352 113404367
    0x504170a0c02010809011d070609060503040b040803090f1002070506060f0a0303110c0907030605090601020a080417070b0304050303010302090106020616050d1e0b0a061e2109030201060e0a0507 85
    0xb81c14400b107500862040c031020742000f038a901d80c9092280b16000d51000041e600d20f210302c02c4170001381d5401000308603c0d114a044034011500004c5110792902c40d925402e2440e44050403048641c07141e140d043c203030700c0000e00074185841c14001700180c9900c600d00306142010b0001304818400e084c2074015a04c6591002e100030190307909860422045011101c00c039203400090584030b0b90058034502040b0395664075401c40c40a90f54140c485480c0ca0f1200001a40c4d500d6540500511040e0b042c0010b21064150000c0585059159021076092a070f5881c400e0400e58019501031310326410004c0180b09504019079603e0041c134a80c8001e000600e0300310554a2610100e00c0d4007820002c0000d2000c0301da030050f0300404400381004082204d013542d0b42d1207080041401c00300c0c0070b0089801810003e02d0314040c400c40030790b031140003078205030341d495880c0203c81540902c000d1460850740004800c2c0121028461046024425000080c10b207040c004881c4c2e50440050007a0050b600b0141005102580008c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 113406852 1250 113405602 113405627
    0x60c0216050901150305042901030c0e0f0103060209030703020405041505010b04061b031115010807080a080414041e0608010f0b0d020114040902070b010e060117010b28030504170a 79
    0x170300207002d884503d055240031040194507124031829081705261300345c0385000c46040b641324400c002e0300c440d9074005c0c1c0c04817070408880134209a1802001000803032420740092400480080585151548960006049810035030f410348507102034403c100b28112052090f103000d000c0c003104040c101890300d000140201056880d11400440b25481101010f004000119003004c4000c01e6600611707203034148900100c0244141c14041c0700307c03140010310a80200b00c002c1840c0d0012601880c06081005400000191601140c0c0040c1d41c0d409090406143c4130450444003880c1602040003803401c1c2c1305a00303484000c4103000f1074503e031001c0c40e01243d0342da014610401e40d0a080c0b4034100c4505080e80c040c14003841c1e102c02c0c502400050f80008128103030810a046e50522000003000e074962800448040e03035000c021010f01d04801c001840b0480c04040a051405152081420301e488040341d42c1404110840c2c0100c0420386071030600003081a244400201c41000d02100c90601c02100002031000d5101d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 113408102 1250 113406852 113406857
    0x405030d03020c010b04050703050901050a0b01020a0308040516120302070b0909060409020a05091314210d0906110705010506090f06010c030201020c070e0610020d0e060d09060c021605090115 84
    0x24010b00c0d43e4000c3d08443c0030b1050041080005140100340500680f0040392014019480c00d0005016101c05100d401801c1c10180e004041d288140e0b9400c0e6803001002c2c0055403a0300c18400f0071540b0740e40d6485054082e0a021030a5805014940f8029281240c00e802c403003c0f001d02840300d07031703240e4a072085003a502101c102c4020656803010b00120b40c00c842c40340c00c03050300400035608000e0038003084002442c0462140036140b0440c190015071649400c03490b0000c0d60314462108001420110a8000c7c040040d40f520300015000f92076a5a10201d0304103880c00180c100011624406000c422311906902044c20f661984a602d001041d48201c1000200b8803414008440c80e4281132600c01d50655544904001c11100c80c0798440240810401d81119024418400c110301d0b603060901c08100c502038805c20740c9030009600134074070810400307801485103c1d0078543e90781e036490301064160045908441494018008007119034062b0542c480f40c40d0006130281007040010448151001c01d240040300140c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 113409352 1250 113408102 113408107
    0x90402040f0207050111091327020316030c090e0f10180213020c0f0a0803060418081206090a0c0c0206030705070813080d0c0b0f070306170c0f04020405030d0302 71
    0x910701c1000b4021900058070035842c000c0401700604445000746412030085410b42d0342060309802001c1602c92078001c212410007031150800344250360801841f81c03e4030003800c1e5400d00d40d0710710301101c09078800d5200341c405d64506402045400c00078482c140e80c8124070005400d25801161000d591182601005143c0c5540c03506c8000104100f00400900301e83d004003d0300e05190254183c1010750032850200c80580207010305078664900001e00d116405a010760b006003150707242c00030800200903030305100404078910664000002c041c007005021800294807413180a082c00c1052015600005005001003450000701003405601300400e00102903046411598aa0768410304540724024400c006280c1c02c40800c0400482c0b603601d4200068404801c1220900711901e0b90850301d504140318090004c0a03413030081180b500c00300e201c4943c004203504012400c69a583c507010f1510242640032440c43d0000c4003130070124a8240c00105602da4101c41c2581013508101c00a900e541c0890050014507070b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 113410602 1250 113409352 113409371
    0x90f090d0f0908010606120b0904020d0f03170403020303100531020d0608100c180e06150c01060f080d020723030715030e1b2101050114010f020c09040204 68
    0x782c058000540200802444a581d03038070743c058040c00d510007020040c142040e240001c1c40c2000080244110b4000b0502003140e080354031070b449400840b400031b40401002e1505040807242d10681c0a0003544207038000e60b942d01d40780c4031119068010360051482411041c081602080c198200c42c500e140c000c8400d109502c20200414000f4070402114440340c5040000c001012a0046100d4040c041184c1e400d0082c800c51000860f0781c40b41c590002507440d200c210080c846a8481c81410343d206078050301006555612218603006500f1030784005015a4540a0901c101d0300602c0070301000f861680020b0594642c0d03c0c20107515843d95028070600b03c8903084041461000c40c005403a0003000c00307400e03170b0302d42070302c9184041c41624104c410901281c00c10355a0941c980c0002803041d20f0184180101502c80901c208200e140c2c035103201c5594000b21b6a0740301105c059028402d0600800007201c914403090305c2000050010b1800700708000564003c2c0c0c240b02c03100c1e200c8a54450380268105c0c0d0000340041e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 113411852 1250 113410602 113410607
    0x60307180510081b0306030d030c021e010c030e0c06030609070207091a15071a0a02071b081218090a0905030c160f060e04020903030c1209090f090d0f 66
    0x10303a0321982d8040316a80362030007010703002003501e401a014858030112040d20384820803101d01c0709aa038142c2550101005a80c3c1911a6108500460303992041e034080b1002000e9441d462443d200c580f9207143d544162101400c0d40502c5030000c0c00300b111025040849214000403050300008040038021042140012200352091100c80041c084108081001701540038981508001c0200c88900030740d41080d42d400031440d45800d6036030341640000032420b440c00d580c10018a0300e8001e424401895001e10020001920724031000310341c8000540501801490100c02d6031a14000d40014540c0d03510410020024518149032000952400d541c00030440c0c950540c042c000b04032030031016105010201c0d064000c43d40126102c03c0441f82e000c1903c510907250410421740c6c00591003141c011510900e84990503041c0764003d041058402415681071803000d4951900744403c820250b0651400041d094000e46840912190030601d654200301d2a8a011045195121a00c80e00901030040040340483c00a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 113413102 1250 113411852 113411897
    0xc020d0c0312050601170702010501030201030b181611030c010b1305010b03040303090809060d090203071a090d02030a0b010b0a080c120103030c060b040e0a170a141c060e0609070e060307 82
    0x1642c101b03002c0b060b1400c0c4000074000c0100303000480c00642010b0b9035880ca4504444111000c4901c040d4a544a482ea8025075504601800204081c010254451100705500780081d02e032a8134000008a000d025030f80400910b801e4801400c10001d144c84014859480c01c0000d032680246e050500080a90b020704085406020345c513031890b0b20102c002510480003540317070070000c8110302c00d408555040351107030308104000b1719042c41e108900005200c070b240303145000080c1c001014000b800b911024192501c0f5000310643c02d0300100b40f0301c040091600512a4025134040d807220600d02032500b8030f40728441c0d8810211b41848090108030060580342c0900c00c440e40450241180200100b060900c8081c425890304060030f002c2e2a0643c0c1c0704584549552600d0407580c400e022035032004205801c110021810390840d60381545550002a040c5614100c2ca214030009019070020090340b500e01178040108003080104500d0030407031505019044c580f03800091b282c101c40b21781025910308120b10081140c84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 113414352 1250 113413102 113413127
    0xd0c05070902130303030f0b01020d20010f0e06010f05060702010c080d15080c010905030c0d030908010501060c11010201151a0708160203070e090a02011404180c020d0c0312050601 79
    0x40b403002070407290060309440030008891298800b84203c00001e41c401c401c031946482400c2c0580c200e905801241c80c441c0e048031005410b04410340b0003802181800c1401c4601da610803240c0550b48101c210490130042002d40d006000e1041501d0b802818440824294080c054009050041c107506890400000d1800c0e949600390152080001d4440d2a2651842c0c591600c12500ca50240007111031407548a802e600d130a03208094010080c840456081c1b200c600c0d06030f0425020003180354008140041e080c0110390080c00150748900c00000d4a09280056035030003000c09040d60724040c01c200142000c000403c0c02c981510300d00f50300c070843c4010503584034425104018445400041ca076121401e020401000c414000e6040344c1e40c06440c0e0f100028140c0041c1c0d101c60095010191590041d84a2402c60080c0c200d5030014a0800360b4608101000c02056140c0061043e141c0d0f030f820f01426410021102010013500c0d043c90100c0072a00c000d012041415180404c0a0321003000620513400761b010305141 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 113415602 1250 113414352 113414369
    0x7060503061c06061e0b040509060d12080103020315040b0a0504020418050601090612020a030f110d080306120303070c0204090606031b03060f05040b220b0106050c16080d0c0507 78
    0x40d0182460f10710020320b09030094010000e109801402001c141c90303040c80a40b610004010702d4a4288801c008149034001c15490340951081c4184001400c4980300c1185098035480381125941548105418800100c150081c00603e0038108004600001032860b00120b80d1800001e0f26203036030011402804e10000600020407800e0300c07650401500142c4603048030703142a01046110740300c030021340006025110103588112005000e00c00324010b801d200707101c94821a9280788e41e65050b00440ca00c107880f07242c103a5404001000700310705801e121400c80744d02640d5501541c5545401140680034080669019006a948503040d000b000030030350010010355000096041ea004000c101c80880e200075000458406040100c81c24540e01c075801581c2c0600e50000b607094040e640d00c0c0054902c10035601c903001c20f00b40c0d94082303400402c2860411a019007034070341e11595907005c80c011952a010704040c0101d580d081a03501000700500208501c10700b1801458031171801e000c181050b61501145030400c080c3d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 113416852 1250 113415602 113415649
    0x61006081e0c0c0111070503040b0a180b1b060609160c0804080604020102070e1302010507050a0f11120a0807060c05190f080703090f1412070f060501170706050306 72
    0x142d0188100509403412280009201c0500164002081d80c010700d4002041070307100b440705001645414016090030501c501c2e080480304040c94841000d02d6031790380b00300100308000400112034040c841c810f6040800040080842d41404404101c2d540300090031403411a0110038150310241c859986d84a0903900108101c1d165030702d540d615521001d065904a015101c0d4080000b0a138442401d518450401d01079090300d080c015400545a650181d8001c139424007461903101d00281220160000e0746000c2d8502215200d008401c0c0108854210702e1403600d0b0340101a0000010702d03070402c45110940c03100020440d10850542903840740915008501000600c507181c40c1516401201c0342c10715603c95654900540307595409508540aa0308041d01d01e103039451420022441c030780300b60268203800408484070300a0302a055070458100a00c00ca4607412010b400c0814803200c2d00130203024121100c10b1038103020481e0320382555100c051083c1c02c00d020002c000180a07503204030017600100c440d111040c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 113418102 1250 113416852 113416861
    0xb0d05060603070e070e040903050409050a051906030b0a0b0f0a081501090606050a0f051c05040c05030c090f0402030c06031e090309060a111608070611061006081e 72
    0x30349800c421220503010f0703c19074000154403510492454050741c00c54481d00e1541d003101c010300015100064050b41400070030000000e501c8464404e8500c43c8524100002d16400c0c0416250211010111080781007400c1ca04203202080d00007000b41e030844911240001c01680780802308412002d18491140d1024016400003042c1202092000c06001c50548659481e1b80b2040030f507044955030b0148000144040c428003461074040d00780394002c200a070811703a084c800420110200c41c5a170041403002d0b103840d40148020002210b80800c050501140601181b0328050003040034107200074203483c0716100441c00310381952814080c900090001901c00e51750b030300d80441149000403d07121400751001d920800a0301084000c001da0b45c000800030038103450048101421106001980110219409a22610710b03c40030780c4090f010041014a02802080cad28103040941b80300007000c50b41515401c00c0c410080200c4001000c10f0036030b20300e4140b0b040580c4030814027400c911150411031501980360340510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 113419352 1250 113418102 113418113
    0x90f02040c05030f070c0c0e07020a120203071505040b042013021c05010f050607051002040f06091508010b07050c0909010b150f040b0a2703030f050304020f130b0d 72
    0x718418101d0f004d80000b02d46600b4000c55121181110240080c00705180500590005050b107a401240c00e2040b00d1020b68a519105429810003140b480503074000240c541c00c100420b05141401c841400041185140584501000d4140107000401d92800e00d08846001064858160701c222000781840e0805241148480000d5210440c0300010b01c904940d054256021030180c14145c1c0c3c0c0c40091507040c0352504046c0700c2d00c0d4004803811130706805505030f40565840b203440948010400c40c80c4001c2410b18144000c0c0c481e007003035001250320100c072400c000c2d00181c000b0f016604449081c0100c0c0e51301c00160905604080d070700d898a9903c51030640502c250f50b0310542080b029038100301c2e80d0348803001c65231403803204520079400c03114508a0309200410030780c012100900f84c51129030402d502c042c180100c69030008050a4800020449811800d00625502c90203191a68101d801c201d8036600340b540000e148140d800b81020304c10500303000c900d090710049401c07200d61031001414890100c11589003e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 113420602 1250 113419352 113419357
    0x207030b100e0a05060d030305101d041b060c03050901260a05340c020307031202061303050d0510050a0902040e0603060c0711060712081503070b0904090f02040c05 72
    0x46980b00340441001c9030b41c1000030311455010700300c014400c2100c49a41e507000e4014107001441201e100001c8940000d90552446062040d9820754075841004e141034504450714481105466035101c0c1060300920186400c04508850b154260038a075888414900040766400300202c1841c01e01ca0408802500141125031362034000c00c200c440c00c0c040c6540f0b40014440c94814222071105000b018110308090104045a91000c80e24038940b40561003a01c5d00400c1c50001c4540c000c44910750281d080014035075050116a0f00004000c0c10700041c2c01154900404601404c5048005281d40d03001040101c28400407c40041c00003074540c03048207503500c211600035001407050b884e00f1811480069000e21b000700b08188951781e0301d10710034102815038507070106955a00344c040d50400d10404c9030700007103001009e4140226402e80d4401c01c003454282c200c8203002802c02140c1d802544010742c280404000e0300c041c1c800a0340183c0c0c0010b400520b40c1040c1c0d140c0321116401039001031512400a0850740d02100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 113421852 1250 113420602 113420609
    0xe010e0d0203090102031204150e100c0306060804150b031b1203120c0c0102040509270a03021b03030904090506060a060e03070302041109030d0e01090801060e0c0304030207030b10 79
    0x6540944080303080c160307201e110314140f044c0180c00c00c104000e03100c5070303040300c441e007241c010005601d03803007200340150080f2400e520003128680c0c49103010004d00e480b10300072000700030b90910b8280031003450b080780540b140c14090030090070079040c1d641c54204200c060340140d0048a000342114560780c0c0c0c14103581840145183c80c280210441d4045111070179000003201c00c4003000006441ca65951840d2580e00d40c0c0107101c0003c4995003c000c0050307240c4d18031441c00d02170704c0d13440c40510300c1c0d04116a2006444610691180094100040e8840401c1d004510384005280103142c0810507113070140000d046229003560703198070a2030103401c003050100000314203100d414280e490085864445805988600c40000079a9040e03200140034401401c0c680c004408130048200c00500340002c4000007400c250081401000040c80f181c0300307055640c0d02000c001d00034042e000c020003145003003907580f2940340030042c1048416240000820b08040c42044060019078000058401ca800e20456100c0e0401c405e20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113423102 1250 113421852 113421881
    0x19030b061002010209090103020d080d090602030a0c0f020d0e04090c0b0c0601050108040807060c12020309010b2b02280303050d060b0f0a080a150806060316061b060207060e01 77
    0x80510901c500510849a01a030010900306c21a884c42d400c01c8203420b406e00b8200c07070480040c1f00440d0301c3c05850007014921403041201503100c4c03404803d49012958180c14400801541446c04502c003500402e001e0500f507920301d0482c03066000e02020034094200504020006001c04000050660055000d0310a800700c0e0400c1d280035999980044440c05029140500f10100404c8080c0c001041035102401c040f40303a050900951039451510000c90b0800c407032045150751240110046840c1a90f5894040c414182c4e5035051a81400c9404500e0009110024010080c050710f07248403106400c00c50500d10a081d48440f4a80d40760718000300303240c100c10a17108807141045008101602c400c415980360000002d403c9080c40031b4010111420a0090209c0141c1992052190507000302004804003608407030740200f4550402100741460041400c6c4980080c00e40007500b07000107940100c044200205100307642c0001c03041d03030030120000d10400200078041480d028180540c601c040d00300104404010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 113424352 1250 113423102 113423119
    0x5010f0509010c091814011e09050c09090a06030f030f0305090d0c0803060a080706030e07231003020c2a09070906030c090308070305071b030f06090219030b06 70
    0x942990994000300404801315100510030b2100e0030f45003107225a18015290003103070b82801e03006083c1c224402a0803c4208800d107801d92446041166410b4005040924040100c1d283c40004102103001e540c0205108030260008580200c502e80c0000024580054801a0181e171070700e0060030001d1145d00c10000300e820900040c402440108a449040d261612061128615561000d910f80d00082840743c1c00702c40181c1c04620110b00f0041c210140a50382c9000480302c802100781840c0100c0caa02021002d682401041d41003141510b60246480b826950141c964806072000c0e0040c1c02800c4c0650744074400c0207048420301c08054904072000f02c034190b0b1321588101003802d1008081003100d5010224242d11000c0103034600c01c2c0d103c203048401528000324100d80360740c5d030118207a104502c1034002420101c1e2013404d020b2908403240103072550380307409900b0341d24659602c0102d450040000d81f8070381d6503078810030554541c9581038401d140945c24800300191640307824100031030b098604500a9212 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 113425602 1250 113424352 113424361
    0x40c08010b060f0a03090c030b1906080c04110f19030e0109030c140c0a030803010f05061e0d0e1606030f09021c02040e0609030403060f09020603040f050102041205010f05 75
    0x18400d00c070140300c014000c10b140c000101d05201d031a42c00b01c041032017015035078214200400d640ba240440517610420042c4854140b060040e01910040032044c0c40140c54403c003000500c40000f02d410310120155804982c40011000040c0140520016440c00c0c05000801c4104841030030581012011191010840d003c903c5101e9400c8034440d0b00024041036447c0c00303240c0402e18900ca60105000f0b284102c50900401001141348103120342c0c4101c80300080480148405000401142c000c1c110968141d414040450644050005219490501030300000341c40391802146800103401808079204070350b03501500c201c1c0d0340c44896082c03041400007881c040c44d21201200364060080031507001040d4500300c410300c071010200342d03440b220101d034816030340c40365084410001d100ca40e00c02c500d04000f031a181c910f10b042000035583c4078902c8003034103880c0081c944016030f034840c15a50000e400c0303403d01e000c0601c10b207442c500a10958100c24005044500786104001301500030f81c0310031304025810701c2183c94 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 113426852 1250 113425602 113425619
    0x20f0d1512230715120c0e18100302040911010311040b18060c070e191506080411041a0a0b030c070b07090f150f18050f030a05060708040c 61
    0x24a00002030801e5891041c1e41d1007a51801e010700114812881601d14495491010b030700c0c42c41e40a214000881d171134003404180103a09101c0c0d95031121043c02c02e4003591a00390005129100140e401000c50481e00c2c0c00705542002c406140d802450b805070040045599904044e4104602041d040d400a424800005020003107101a00c00b1140c00424403800d002640341034190401e0045002500a01c0c02d0010b07224012080080740018941030904406604103002010700e81c19000c01c54110440c24200405407580c0706481c0c4504444991400e140c4a40302c81c54910100e07403503940100d90060070703c00c40038910a40c006d0030498001c011244030300001d40c2d41c0b00361000d6000c1128182601e010034003c03403020500f00388959601c442107207426880e851b211001c01c0e400b090b032a009081c0c80c40c02c19092120b1590400000c1c4240c4520f41810b034a4000d000c00380901804842c041c680c0211440901c0010644040144180c00c95100c0151003540c40d08041c0284242c0003101e0540d40b26880400001c1c407090f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 113428102 1250 113426852 113426879
    0x30f0301080c15040614070605040c0821030f130210030507020705030f0709150e07050418200901030f0f020a020c1e0105031b07030c03022806050406020f0d15 70
    0x42c03400f401a420503160050a50b4401c003208040e18004c00304101140000c1ca851041034401d507c42c0004078203560410a00a1400a00301c45400950914405840d1040030150550307501041c2c0c4840382500342c1e17582000554a503003454000f904001c0e024080c045050300b41c0c0107a071007001564200c03120585e95008050b03580418881091303050300482d034244118441e9401203a04210929120140e0315070ba103001500300142115500d000030000700b018090108106114425403100e55030074000c041c4001081240c03007a481c9150296003400207035019003a406a04013502032120f204003040002e10441c0e10034003a500545180700180148501f440d90b40c0303408454515a1840702030a211315540c402e005450f00e9001038a00d00c11005000310320640448090300a002d11403007a034450080e050307546000b83c03401201c6654000100c0380501c441c10341c042000c08107000543c000201040301e0b19181800b9000f4801c01c0101e42e812040000d15030100c1081d41c000c00b0005081d002c45210443c0c1d1410007a203082d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 113429352 1250 113428102 113428129
    0x4050105010618050a0e0a0914010902010311070209060f130204030303050402120a03080a05070504050d030513091a06340c0807050904080a09050a06170907030302060423030f0301080c 81
    0x254501005006e503481402c0c166900181a400003d082001510358031083c542040385640b0b50781d141e00b0043d0071940c0c540601d1101080001d07400382000180d6001413030354007000303010b14060391466020305181d5480c0103100481d001ca0b40c800319595601d90400070080d1004881c00d0b40038031105070a44038100d2001900c92045038140d62484003549440c4a42005440082c5c07042c000c0180c10700011415980c0c1d12150b0310b00c0d606c242c0b00c4950304d000d1060503a403044c03115840411000d2408a00141d580350000b820448690102c440704d650311040d0880c040990400a002540601407650240004003402180c001180c0034503440328806960f02100c5030b80e50040c1c004d882d0001d040202190004494902902481801e400c190b41030700d0b103d00c0490b140e000c00d6408100050403c40307035140a080042541c64108403408040c240030390450310080c3d178482014200918120021400c0c600d039000b03035481491540020b2054a079100105504080c4c40d030002c1c0682d0000d8002c42c038003603e807403404044000300c3c1d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 113430602 1250 113429352 113429359
    0x21e0603070c1110080106030b0d050d0302070218010b040812071205090d120807120209030a17040e092a0907030507030f0e030d0506060f04140105090303030405010501061805 77
    0xd40e51440750454490b500e0b00c00c1101c2030014503280e0002c940c0e818600000401055460480b030b585082401010f603035400c10124005c21050090301d002c60720224a0341980c10f6907007809070b59030b41c03107101040310400030f03c40c8045900c1000001042041d070040080003216a110300310780728010310444405051051401c01007503d82d0b091284680c3d540904098215604024a85041c821490300c0300c9150042000840000a06200c00c010000360000500081400540710460902e032a80d0081707603503a0260309000d00007904100229510f80451401c640180189181c0c145a0b81410203030a82e85850b00100528404d46200032402c2082c0c0302d0120000c0c00304000c04001c0a0b0702e07a81c509400804001d8156010140c5030f04e5090701c043c3c0203010302c000c121105070056a0311858803481c03002b25400940a0303071141200f048180800c0e8000c0058a06031501e07903c218030075a8030b450050700c40303120f4002002d80601000c410401801019880541240c00b281c44180e500d648090036819481e045000c1d0540c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 113431852 1250 113430602 113430607
    0x90c011716030e01150305070f0f05130603021c020f041b0e01110d0e0324152412010902090d06091e0b01080c0306010f06030e01090204020d09021e06 66
    0x440300e00c407520034491219814001951080b964030f0600791a1001d01c1110032a044480c10800c1100070070400000340040d0701e030450b040d800c0c01c2d0340251442c100e201d400d1055000b074080031000099980300c100115801803001c04100c1490708117034050301d09600c06902c0b6070524442c4001d103040038000c9001c1c03404900d0310404640011881544c1040514500e03d0400c81060b0a60008040c02c000012450074a9150310005610f00c5080500d05454417004d41c54498108900005030030000100702d400c081c030400a00342c2400308001255140b00c4100c0102d0f101e090840c0007101401e0518020300324400000320022a980c1c90b00c4456050f846000c131b041350400884032881c00810231543c00b46500c203220b008a06d45091500c6614541102040303c16a00388a2100040000c1070003080050014502074015001d0366140c9110a68016001e11510b028035860340e0110b41500400c0d80100c00142d4000c10440d00c91065452100080840c000100d005102c844030040040d641420007402210700241100d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 113433102 1250 113431852 113431861
    0xa0308030103021c06022a01060303020d1b080a0305070e01020a020a121104020a020c0109060c080a080403020c040516020d0c08220317130b0304030c17070614090c0117 74
    0x5104a0320001081042c040840d45400085c0c5074001080c2107100c0c081614070100600c1001041403040800c0307411240e1508900300f000a40105140c0940106c6003083d4407544184090b207100c2c0340c82c0c41c0004007615800141c00c00715a816074082809010541d4604203100c800500690342c0d9034803118081d5004188410805c90002000740b952652071051103030030560310100000c08c0a82e00300c0e55961025800200201c546942e004801000401d002d2134483c44800d056247c421580c170507107a61008100402c0c0c009824103008000c1041c07198009001048030b841c00c502c0e00c0c8006004085040010b004040544c0d50542c402c1d40c8008480d500121102d140440400707119038030b0607280c40b01c01350b0016100782c000040360141d540548020f1414868960700c600e401031004442e501d03a004040022000e009101c01f00740e1080390740b00101d074004188600d000780490244102e00415100900f5641440560f0810b40120a902030044400d80202c504a4954600650b1a826180c0d01903c40f54103803000203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 113434352 1250 113433102 113433109
    0x1801022205091015020f03030a0c140307090e070c02030d0e090a02040602120702010c0512030a0f020403110405150a034202090103090b0a052e0603050c160c080c0a030803010302 78
    0x1210720013640100d800c0c8569004170242503800403134482c40d070580c1d03d800f00316100c0c2c1c0105042d40c070722a50b00c0d4001d15601d40200702070300f07040c224050141801ca8401c0000d40d954007036007540d01495001411206c0015031010010041452800d2550181030b0a8000c25070100c640c0c02070310191031894001c4d00d03451320f84000da504145c00a44060381006030381d0350000040780050001c1c0700d6485500008543d03031316020800509440003000e0090100e48100420004540d8039000070303150030390468000c117003505c0e00b81c3c102c3d400c6414195041c1d8440741c109000010010040080030345c50510254100c1c0f00a200d0301e11200702c581d0f07815048151101184603c512480c55030040580710014180059880d14940307403150703900000c454041c0004d690300140002c02200b0703903440b0100141d0324082c945060700070080503800300c000d00c50382c0e06260301e4002084402c190001a02d0000c8141001740541d084e890502485409440c441c0c5030441c09810090440790804402240540740c00c0305d809461a461075091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 113435602 1250 113434352 113434379
    0xc01090302011412010b07030f050301060512090705120d032f0307050408010203010f03020306060f1309020a030210031d030309060c0903010b030d0504080714150318010222050910 79
    0x1400c107403c1c820081140103050440e003480c0a0180510701036200c900618010742803480b824040c0e020f2280500042002d81d9003c4d08485111121a10f82c0340242c560303444141c54040240c1080b54002001248400181c4000400380392110039580c0030311150076240d141c011b41140041c4142d1182d00c03135100c1160181c0152004581180700b900d4030030f14042e03807541c88a007207070001c2e0050700103080240010400c1d40740402c0165085038007110303500202d807590b000040080c0805403400b51816220001c8805541c1d408842c0c00045070080e000111035000303000018020700036407a07144240c1c06823400369195000b0000c107491141c02d46000900e481d4803010800c50f6283c2261810961540d241d0318900c60380e0f14180b00301d050361545500c401381c9850402e00b0040c10022150000b07009003000030380403030703c5076200300c00c01c049680d030342c0c107c5952500c074840b031102410403c408496096000082c2000d041d100103a003030719541c14800c0310442c42a110000c205000341e059581020b20908101c0a0010340b100c0a003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 113436852 1250 113435602 113435627
    0x1060e190e2214070504110c06180f060109020d05100608070507022b15110906090f09130512030702250801090c080d090315090620030403110c0109030201 68
    0xa5055402c0403651403810b11031443d051100c0a0b002000200901e04041c020680d482c0804070440742082ca451744425900c5100802403185251404010b030760401040c414031a0b04000001510f49942c2c5540360706011358003c0a510420518103000681e10340d04944118041e101c9558a20010b911009002c4a1540240109980c4a40008244101480300c028038400c0c030014082c208003420002c1c01d0078008442c40000ca02902e0342050740307800003030f41d8003400c440c205c500880b00c0607180c51401d808140c0d06000d885103907800507800004d01c6034204002c0880d860607885401100d00c0c12104503844a250300090f00c16a01590003018100305008905070054951242150060f1900340d60784805420340c0e174031000603034145d072100d9028062010203200301c0b2580030303250921032030321880c4d81e8441549241c07207803107140301f05d81d58403022041124642129860b911592070a11800040c2108070b1569441564200c0c0030421295448080c0c0001103019218001d058440c070b600b42c0d10710380040d510a00d5052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 113438102 1250 113436852 113436901
    0xf060f0d1e020313030206070e0315091204030f05060603070f0909060f0c03020a020c0a031a0c040f030b0105090f04050309010e040b0a080a020a061d0f120601060e190e 74
    0x74801800c0e08061024520940400ca44030001d1180303424041e081200117014172080012280181640b900d00042c40101129100c3c1403100c6c079901c50036424144000001502e02d05100040c0002c1030003a030b41006c912030b034004c44c161020b80d1551020103640c1c05c0d1a21034447d081102c0703c403c01030703c07001c1c2d84042c0d9160302661012603104c201c0700c2c1c000102e500e490746003400700340d02080e4006002e9040090a00d003003025983c1d014131360300310b480d00007403000b80c0d62441201803c507000040105198a05440050428480300c0001d5900ca2820321104030003400b90a00901d490300010b50706040072914180200d0b0044059850700d200b8000440b07000300c04503990341d089500c0c0d94800e44c1070381b194240140100082d0703000d0040c28804c0d2040142007085075000c0f0041261801001c65083c0030054448001311046540c061140441808241c22202d0300b00004128001c400000a60b00e81000c41d04403055000c6440d0300c01c984400014181030120380c0165241e0307808400c0014a100c10302c5580345030302c88541 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 113439352 1250 113438102 113438141
    0x904030c14060c190c08030c070507031a01090506061303020906030a0f1202151909030905031e0c01030c05070605070e10030c020c060a0e01120f02040f050f060f0d 72
    0xd0411a18029081d5618490000001340040482000d03008502902095142c10040b101260b1030750241d42c003015000c40d200000c009154420400300b00100e03c0190782c09071168a0100c1443c011703480b420024071642c00102c0c28100099002e2826904449014420300018035620b401e540900002840040c00d09815208a40c03403600850429400d240c100d500c640e8481c0e0084502c520000e0410b87d100e03256600098280007800665031000a0a2540000402e40082d5090650800b11008941c5038081030701030240c10040c809415500410507156039464048500340000b031401102211840a100341c002841400340d44001344441d000315800c60300615000300c55094030300016550038100c91120012035520b51201322026010310081a00590446601d41824a81e40d8060004850201105e040100c5001c81c0146114154030146c007480502c6001c40d101e50300c59a602119030050301416224400950ba074100720300d0110129030665030b01d000841d0401407048100c0c80504445c107201301c100d407a03c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 113440602 1250 113439352 113439383
    0x90c08010207030801050f090a0c091a13050315150102100509030d0b0a081519110408060a18080c0a20010816020304211524050105040b0c03040302030105010b090316050904030c 78
    0x24884101c00c1414a251942c2d601c1410380120721061a04ec2d000a00980081e01c009a081900386000e43c3c0c4544810701c0c5442c48032103040100d003041c90f036000c141c140a20708400d100c40300d200000030b841d039594000d07000c00c901c40740d001c204544280c0c0c130312880c03015900001c110610b50b51072429540c1c02100d0303110644448501d0003031240c142e901049a00c0d15403030b4081010080e419082221a0300210040740c100258107503044400b03506001e400c0d000c3c1814900140c03200091108000c0e1902e03140e0041e1800d1444a034204ca200001001c02c59540d00040c0100c002c00c50b644021605004d1004454009502e0a441c004060800313402d0302d600e24101206c444c208502240011000035044000d100000921445100c24a580404140c51680710400451805d00c11640c0000803a0161200e1480ca1501c600c030304c007619841c40c45641c1009415508100c000520000c2807400b51450f01c00131403d954207001000110401c413110303889940e90100319a030210707011a001d014a8440e96000c2e0b003400107100344 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 113441852 1250 113440602 113440619
    0xc090111030301030b1603060617070219061d0309090a0c020a0501020d0506011e080109020d02090301021804180506041212140105010f020111070213090c08010207030801050f090a0c09 81
    0x109031320907030702c080255040205c040c0b01c2001d40c2d8652034040c00c0c10000c1c10704284005240740d40c1032800840710039000010030754040c000c20001c001c01441140c0301e81c41b0242454860050040724001c480151780411854064030008001e8500c00e42d0007a0207941c02c7d50760030480748050002050104103600580300e16401280007800140070700c442c0800040380d1814070000040c1600c190410410000b1503402e081600c1660200c1c0700c41c1100c000180260f2603000300d1010303100a228000301070307605610028604013461241d4604e12100c21040383c0070041d0034505c01401c00301c0c590400c0300400300d80040c400180010700f40c42032045030103803501c1c02955603403503020844211031b5040424824241c00100400070340d0ba000301c9032141141c00344024454056006044240c500a0000c0240f15580c91080705200d031009500820a41b5000100724080c03580d602d50490007544070078000d800140040c0c00108541c20700324208602800c0261008001d5511034100400428441045008002c0107250001d040d44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 113443102 1250 113441852 113441857
    0x3050303090c030607080f0f1009020c01060e01170703030518060406080412050a1b051c170606040302100f03140c0a03140906041707020a03030c0605070e03060c09011103 75
    0x1c107410001d122140084003010b00d455401440070041181e0712007000000c0a124130203039000041c20704a0400c07501c070b1502030103d10003207410030203205102241e44040c0030030541110703044403804411081c1d02c0c0d888100b2030705000d0342400b110704a40c1c00b0350401c00009109100411421460501d075a500c6220b900c00141c4546c0103502040008001c50144024407071080c1c50703010f900b421801c0c2140b62041e03944001c0c01c10040c20b01e5a003c40200d0010250a001c824041d00c14019903d4880100b001c41c00c9101401020300f884e4811294682d010015802d403e12404890076603030014404110804000e0b4212881d450b0443d003c41055100c105d401030301a10350711441d02640008201035100e070184031008081ba8810b10080f0a04145502807005188004c90400e4000d504041ca800b080c04400604011920416800079004a01c1210003c241035120400c03580e105e22031003050000c2e80b50704000b04c1e0903034908a00b030756044d0080004114000c1c80e410044c040908107040210784c0c01d028005590075134 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 113444352 1250 113443102 113443111
    0x9070506030c0306040f090c050f0a0e040b0f010609030201050f0901051201030c05041512030c0203070b130617151207170a050c0102060106020a060507030b06070f0c060c03080c070c03050303 84
    0x20700707003c002e11941c1d01c1c160140e0110b100d8500c00c2040145690707103c0c07d82c8100c2910496000d510b6190071501503459010b042000780400c259005620308141c0307000002d040040321109010154000007003585481460403800302d0360140c2d0703540c1c24400c0441d10450b06502c1710b00a5030600008101045250822500c0f09008600810704180d8840c6801c00340815904101d1304040d42940700b00f014000c0c075105a01d809002c0da0945820003643e104c80c80401e1401c861500302e0103850201148858010390b80c0302e55001a24015a15400064888180c002040034240d4111400703500a40d20b0f031003d42040f03103281d00c0484131001200d48031a40e50320300a580d541030031581c00890300050165004c0c08001c00c0004000d08003803005085a614110b0029110307044010700070f01c40d503210307004603008600c20341204400f01c03070082c10299900d80b903140c010444801342c0821600300500120020b44940106085d55071140c2548031303074000345da41d461421900d510a9008a075550704242d000300c0429002c00286106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 113445602 1250 113444352 113444371
    0x206010b390a060c020105130c03060911061201080c040501060f1101020d0e10140915041a0c03071d10030f06031a0103060506150a0c0c0513020715061a030907050603 73
    0x1e0010b10006d007941d20050001e241c5d0f500c1150210005000340c40303000c01b104e800c8080081c103038045180c02001401d000c2c00503540504085010490a5440304046040301d000c2411900d00c05110418403099820920801c4081800002d1602405004d18503100d14141032400040c5801c0030302005800321030700760414604591000040c4003848045125507007208454034246102840c002c03515582c1c82480f42c00c0d42100d24031030000b1804004030483c0ca902410b0b543d070507a5a0364030b0400410601504101c5031f42000550b00c000e840e84180c0780100c0b12040800140403022242408039050b005004800380f60300c401c80c0d96840000209020340c40104510840e0320450200707500d941000800d48902070815031003001c5824010a58520b01000c40d10070358100e080200c0000042c1c00e1211000d0082c0d88000e0300000544d8900903030300015070040961038850b0700c040c070700036940c61141411a0b40324000c0241c030210410894580f40802c0e4043c44d403050046045401050700c2d040828055081a030300c0a55 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 113446852 1250 113445602 113445611
    0x130501060b09030f0f0c010c060f050117150906070c0c0807290a050301050d060b0405090d02010608150f0c04080a0305091320030601050c0610060206010b390a06 71
    0x3080c0c5024400e4480b0044c480300101740d408004904642c9801e001d290709030500207482c1071081008240d8121000c280710740301e400c112644e51032107440100741c20303510094400e000c0e0307500c8040b0004031110054080d4003840010201d95465050033345480f6003a02041e648000340c940c0005010a0810a0070050070b941040c00c00000b400030b041c100d80840e0340c00401c85091081c012041c00c3e41d840030550381103501c00c48040e0003106260405038002d2400c0b03010f09070041d0400d000c001003207100050442e60300c0034550003004581e680f1060280c076000741240480e45c2d240b4520201b41083c420030f42594200450803241e078505541e5a420301d140502d0900100c01045022030b001806191801d40d0798803495071030030b0902c100502c050b19000c00f00704480c204140d07003c003c0003203007803640305400340d40040c18108202c4d40d00e0b0502003a601407424262081c00e0041c4158800410f0036443d0809032005401d114540307092204002207801000540081d003006c0d25031a1103900420b1520801000083e107004460014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 113448102 1250 113446852 113446867
    0x51c020405180f030711060d0b120a03080903090d150e1501060801060806010c12030f110915040503100207020301110712020111030105030d0507021309080c0709150509130501060b 79
    0x2420581a100f1605858100f4401d080120704041056000c4441c1201e00c980d40d04500c0c3ea45030700602076100030513044a200c0441c56640c1c0400210201464040d880700c00d07490344c425644070b41e40d00c540c01d40d0541100010601800140c1141a40e0758416041100840d8625010387c0440c0b419080c15034a0b4600403071000104540d071780104405014001c546000380c070394903040e000a080007540b43e20080604082500352401940700342d000c1005070440550a018251004c4000b02a43d040000080d100b4211415a0110707a08487c0407a011a003005d0090718400da801c180210080d0000c50040e600355480e0700000034124440c00003444558401d5030300c00c0800072045802404c40d001c500541044050030070046c4065038001407104400d1440c1d18240360380b10080e01c040b54242d40421900d200c2c1c103007000101810080e2401c00340c2114100d200455241960b01d4041d14240d80c3c114075103803000750042c0000c4c0100c1c00e20207a83c991002c010050205484116500c0d1400c40f0201e030301410a604010a024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 113449352 1250 113448102 113448151
    0x60403021b0619080402040603050609100f05100e09031c0504140a0302071205011b0309050f0a020a0302040b06120f01290d0e1002040902030a0b0118051c020405 71
    0x107281c0715400380c40803401c002c060b550321481122001200d80900c88048002030455032550081ca01465104041c0c0300705040c0302403103d94410f041c225200502e82011116524240d031071003968803841040c01140c081d1032414642e828111000303440141240010448800500c403940005035070409110800105460300d030401d80c00d00b4003840006800d80c3c000c82941000f003580040c2c1ca0040d174030329415100c40820a40b48ca00e004141e007249503089401d0842480c1c4001d9095449074240602603800d5803121074102c80601c0e2150100800290301c004030a10900140c28181c0c48464149006451245480a9140982407403070b41112002085c1803404014080350010001107014000b0210800f520021020340400c07003401403810103081580e40d00602030811000b001000d4040c00108001c42d5240e48070b0f641c04001c0d40c0129044080241003288182d85d5501c00c074080d5841e401c01c0742c0605200b034100400c001104c41c3c003a00002c0c4240c1143c40c1000941d581d880703064081c02040c603286404c040950342c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 113450602 1250 113449352 113449393
    0x90c0507020f0315280e030301091d192904050106120209040803060103061205030403031e020a0201030905010b042306030115120206120a0e0c0a230d0506040302 71
    0x1030203500522004040343c03070510004c0d5001026411070815a004030000c401d210215002c00c0181c240c00c1455015071300380003000543c162200003600703000b404004006201c15442d001030aa0199002000702a03030b0f161000c0e0b01c81006407180b0441d12110b9480d5842e40040c4408034031014158008105020804c0401d2043c03800600908a83c2d602c081069000070b540d0480061014100d00c40004c00030b100b983c0301c0d60160000d040030f0f040c0e960703181c1458208a41c3d650414017048012400b100409440ea881d5569240002d05103070b030040800c1422035004402401540030100d80310340d290200300e0a50356840c000c1042e4000b1402104c1080c1004070040300080c2c43c0640031078000d9160114404940320f0600000060752509021540380e8800361000c29254031459907100b242c12030f50300c00e12803816550b412555035403003840c04441d0900a6a010807080460b07600c035141f0b09510003103000010358401d608405412600900c010030f01025601c4480c2008012102100103030003540403881d0750070b1031100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 113451852 1250 113450602 113450629
    0xb07050d0606030b0f04060b070b04050a12050a030c0c020609042c160506130b1b19030206060907081f120506040203100204030c03020603180d0207050a060c050c010c020a090c050702 80
    0x10b047c044030346811246041c03032140c420007600d6078006200107801d1140c100001c010044c1c0c4041c10703103840200328100500942022103200c00103400c3c0000d980d00903204d09403080c09690020500761421409104000040051504281e05116174160b681c21000d08038000722101031181010b4106c0e201c00c04400c5402a15680110348502002e00454103007409030401142640c1e1407424070341e620416001c031066690140d104031100c5114140c61f6074002041807010382e11131440394003202c1554840003b000110001107a44030001100790000580c3d003400200b8041c07641d02d40321580b0740015103070070a05031440809501520070364044014003007181400c021420402044100c1141090308683c2ca4410912691102a1040c8408000b2030184100d40e10f401e00d43c4c1004100700c1d22a81c4480358003a40315800c1e4417480e031040520510019801d40201030541c641030b03001c0c01800d841811040151042601400142e37001940103501103151560f078880c03508840c16940301c3c00c0d1118410b10404c03070468015039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 113453102 1250 113451852 113451859
    0x140d020d09080601120f05010204030809040e0c09040b220c030b01060c080a03020304020109051e011b021827010204090b0a080a0f03030b0a0306050603010e0606010c0b07050d0606030b0f 82
    0x90040110b8070001c1021419280d507201500000405401c200003201c00500015006505c0002c0000401001790010b21004105842c14446400011a015180c20000c06040e81201074940060b0004504015060707124620060b0014004101d0100303040301d10070030004a03400c000c0b01d0824424400c0c1c0403036050040c5080d1404506c0c01c0c0c80c581d2a400d0b01d0080c181040d003810380200205086a004200e0800504005401041d130600080401440c020306544d8075408561800000c500340e142d00005a039440e40c0160914a200702280700c08200c103400240441d01c0b0032604280705540e4020a41006440204a8005a1201d04100300e14003100d41c2c44580f24843c0510460810009001280420840750005400071248150741000c2e005400c220118951042100c240441040403070b41c8081d0040109800070024496030030420b9681e42000d96280d40440c203100c8400c000a00c2d43c005656104400e860503904110350509840b064034800d400c010040303070300ca03a00040c2509202840c80704400048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 113454352 1250 113453102 113453117
    0x41511061008071707090e0d0e04110f130803071209060f17090f1603030207050f09060904030c05060a1d280c1508040c080307030f0305090a140d020d 66
    0x1c4590b0343d04040d100d105000e4403402c04400701c55409110090080040c10002d100031a9002581611103000d248a40003017540446a548203080c5031041800d210f90030f460789071502c4200b0380c9000392600000c1c2c1669008408482c0466642401e0001d0019140302d81013001d2a10340c12900600103d0094108004100d001c21000d5441c5a0204282c1c1c22410102d24a4245845000e8510300303009641d000d0704220b00c280e0710005076401c0814a88811a40283e0a0781c600d1521002009592031940b0310b42507200e00010701060041c0342c03540c44650058880d080042d45170840359076035410280c084945146442d030b505414044048840101e001079601700018044400c201c103008440e40405458021050700c41000e11403c100c90000032901404440b51501c041c40c2d000f0100800300c403406c54045425080101d400503030041c0001c2a200c4441d81a00c80c0400403024807003c038002c10001300a030480303205d030744040c00120f1001a07085200702000c00c050545404c08000c081d140000d2481c40c0e208203c040d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 113455602 1250 113454352 113454359
    0x20706150e0405150c070618020a0806011e08030405010e0d170304120809100e030d020408070f081501030210140c06060f0a060206060613082a0f010507030e060415110610 75
    0x1c006c03207662503889207001403055603211500100c104a1100250040c0c1311b1304001c100c44800040c90f504a1b10180c120f25148144400f410005180714410b2505643c41031000744459030045210482c103400c050012015030445445400384240d0b00d42003070340c070b216001050105000324420540d0218015060030b4083d81808103061360303540340007012a225259100c002207440d0780c040c0301b11180d00001510a549aa450f58085a01c80c0000d04c601841d48840407000030b0513a101003410310401c20061005c10580c1c5c615002d001c9070940c000400b400300040320210404070320450000d81045038094004014910346841444940c0c019414000d01c0341980c894200042c50f0b0008403a07a2010060340c6480d2a00a4014082d0351034001da04081c411b405080f0841d81d02a076194612055001c168040c10f403006d030030400780520310401c40105800034004001c203602190040d21001c100c40c40140540d442c26503507400310000605038540c41d10002d0b0390940324404410042024a401c0b0719958856042140b4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 113456852 1250 113455602 113455621
    0xf0204060509091012050f010614032503021003091a012619121407080906070c090203070909050906010b071401020d05010f0305010e07050112020706150e040515 71
    0x42d04902c103200c1c8500702c0c00541c0344403c02003d94014110403101c1d807111852894802d8580501d000c02c840c2541c0b8105d000940d0040c0021040800240580501030078078407050425035401c81c5820007402044a28000801030303c0d1036040900103107040da4001001c280381e00d449420a0002040b0f410702101a034018002c007000d40034540e007a5a07812078081c10b0441c88022407810440444480b522015207454102c041c0841c0141a84803203a0307550303800300d05011003903a40501c2d00501d0b5002d44088800c2c000d84d08642030000040c815a400703502c110300400c4d92942c140b8181e074070460303107100010703400d88040007185e030715004490b000341516000e01440c1d0705096034880b0901920a001d0401d5040d09024108204c0a50444600e440c500c80d05106560315028045d42c1c1c032040c3e02c03040f1070039031810001c2405202d010440b001034030300580d50000680c0721611072501030740260906440e01662540d0300798104090a10881c0101030301c65801e400e40c902824480d00b1301c00744440b8031481c0802007040151010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 113458102 1250 113456852 113456857
    0x1b061a041a0d020f060f0a020601090c0512090a020a080115090b0303090d0807060c080411011805090709091503030905030303042d02060c010b0f0a05030307020d030509090c0a030f02040605 83
    0x9031842085070b903190001860f52072601c1440c0f84c00510000d0342070200300003800107054009064080707034a2641e035000440c044640031040c000000d00d0030300610b0f07426034440d018141c020306110300b00c44103c4480c0d000940c011100e035000400703ea540300180d650103080000c001000b0040040c04003c07401c0310384c0109890340300f18500f5038031503a0b41011304001c100c1d00c08140c40c0020380000d002c0040c041c48200141103031209441c1518100190640007125600c2010608150040100c2c2034140919060901214080107403000042c01540303200441c64550504c181c500203060004103564080c603606000c2e0140b0056080b0a010b500300b0020000810560320b00c987c821000d6102000300419180d240515640c00d118000390b01a00008114124050540100007804000c40f1012222801c0e10200070001f80c003442001c0e0150024851480503240210300000c1e1140642072141c9424901d0700040c1c070441d000c80b03800c040042c011440001ca1581407050f5440b01c0300500701185481d041500c00750450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 113459352 1250 113458102 113458151
    0x3010c050426011b0201090203070506041401110f0a05060f06010206010b0316020a120509190f0303030b03100615030501080705010c11030f0313051207030201050306010f1b061a04 79
    0x50285041d1501d02c060035408002c5000405410071012098503000070b010302181c00c0c0581c802c1c490180013054510740401241d0881c1c0d0301040700c0c6960f41e203000054540d51204e001c600b4980c00340700c0003810b481c5400c0c00403602c803d100d0030150520b464400712506000394041c1c0311030b04550010006024000010f0304a030340120030705100466402d05c45000324500580008020083d03030540c0100c40100350000041c20800c1c80c00c507500c009058250b520121210b01d50310035030f1205010700e0030800c080b038002d9101207800e441c05020b5941c0c1c80c882e4040c0000340c0d462580550940000204071916069040c07156901600301800034000035464100003c1034020520000303881d5108040b640740c0d03079a5081152198240d2881d054a4407a0002804031040c2c0c03a5900c07655010b10640d04000f40c138001c001c5280e005580e03058481da400c54541400450360301d01044540400e200f0141c802c02450010300d00c080711210700c00c1ea000300d140613034074410000c8044198a040d0059091503020125003c106035849200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 113460602 1250 113459352 113459399
    0x91f0824130f0f020a090204060f0c05060a1a10020d08100305060601081801060b0d0c0207080304030605180a050a031b02010e01030c0918021b0303100909060209031006030203010c0504 81
    0x40e600c504002c004000c1c00f6030020b51002148000040428003600500201c4141362241c60300f01c900c41d0803e44420444100c0205550450b01c0058401441b55026000400380319842801111a100106a5541c2d11a0034400581c0c0000b540110301540141a181d0100d00700000d03800a501d59998260313a9030000d080380e4144180c40d400541e108006401c45021005900d00a00c5074650b02c11512100380e01c9020b4441846040003441c2050b1400080c0032021519040000c40c600707861a04e850f0000d03d0f0140a04a03d07182001c0144034080701000300e9488507008002910341c01d02640b50107080014000040c100c040c100407070807000350707802c00c2d04041500420b081c04544c800a294080322504550741020066800003000001310640680c040c10440800c0d80d8000114000032140c1c03a52404101d50482060643c480140b220701082e81040f1070b0207114241c05030401500200103810420000b4a8203502c07580e81900700250302d024050b001c40d810341402c00510780703410004034182450280000074034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 113461852 1250 113460602 113460623
    0x4231902210705100c06140f07090b0f0309010216060b04180b040f05010b0d0807020a0b0f040b071e150c030203150d0f02030708030301030b09010501060e091f082413 73
    0xd88501411726030038510751000080200c4e0340080b1210800041c16a0820352148080000600325406002b101c025620804640c03400c01c06030301c5990754070354001482088555024010181d0803004000c514100d40d100d4030011411004100a1108a520080980350035400828a00c004a01d1580700d9681041e00045026a04e40e442d05041d4050694a03519503004003000401d841031000000c083c02a00c1c0c0700b00c4209450342d84d1400040c9550140c584e0b10002180108400c002c1900c00c400141b05962155500040c0040c030405a299042c0290b08155031035460708825004200d4503120324605241075040450860620506c1345201242e1524158050450040700409101c44012200081755000b022500986d45800b011030b1039400a00c0226107026034035010400811040c002c99050b514030b580c40040c902410030820504090141103201000510202d4802424181ea880c00c058504180185030201c4d4210600c80d00146d0a046100600340307030070074081074296000c03407001c660f5001f128010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 113463102 1250 113461852 113461879
    0x804031211030c0c0102061008060c07050a12050903240105061303120c020109060f02031603050c070609050f0f0906060913020a0e0f061204231902210705 68
    0x840c00608004008202c0c403010071028116400041c8007030556100b030f829103006888606000310420618055110346800c1240042c134400300074805000c485004c3c90884032491081c4d26145800801c511100b400143e00081e0040789003401c2028911585188907054000c10084010306909071042c006d07944074000c002451014801012880340240d81c00c00341c01f0440b80302140340903040740a10301c4102d000c2080b030f00c0c0c0001c601380120300c40b03900714074030b50069460f106105071304144420480800300c080c40014070400703a14000402c9940040d0035691204404a810001001501036144035450700c45d003c020281d110b1901c400341c40075080790702078036001d44039001840001c0300e14081c20120001c0c24400b241c02e1075015440454600e1290054800002e074003482410301ca064480c0180c002c680d28030030800b050000700700301d00318540c4e9052090000c2d0011507071800a402c01240d02c40740c2074a0509046190b0543c5405205000c008034001c20702c00301e112106070381c41d40380c080504c211031040c0c0b03541d400702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 113464352 1250 113463102 113463107
    0x1020304180203060103061203050301050126090610080c01022a03100506090c073c03020a140607090306020703050f03090d020705030d0c0b040f12050d05060d08040312 74
    0x300e01a00348010703501d001100c1e200381d4030001d410803100540000c1c1400d40001d070f04d02c030451540300401d8050b03603024a140c3c00c1c007005450003801c00090100180c20340c0c0e9240c001000c1c60003414040c0705048054040d034200308000303c2500e60250045d42050b00492403c050a0303070001500c000008841c0e403c003008104660129054941803909643c06001c0d04111040c1c0c241d2680c40705200d50005c030358060598854030403048c103074055075030010403035810f824459881070340d840c0d91907140c4240d0f9204101280060040c6c4a805500c242c0c00706d025910052017802000414102410200841030040c001441c0500001381030064500c4040c04043e400100d400906100d4000c681c3c40e480c1c40c5030349594031709060204035901e02d05a0402e000600966074042040d1401080840c41640320740c0d141ca50700c1c0105c6d02c030302e0300e4000302800850b2004001042100022150080b14607086110744949480e8040c0394040c909071131000b055175204064039400000050124400d45054070380212008000d0303d03d0310802d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 113465602 1250 113464352 113464357
    0x601020f160501110f0609030a021011070b06030a020a140a090e07170c03060103150c0905211005070503040c0e0903070602180a08030c0d03060509061c0804060207150816030506010203 81
    0x1004175009070000c00c039200200000400001181e50308076036092110942c1783d0b04542c1c0740c40307403062192020040403010a002e20a45038101d0780040a0351584080742e400191a080d8030340c00080c2c5101c40d0108841a860152060310080441c148240541c90401c2082c545903800c6001e2422618159442c9101e100c0d1308001c0032481540150482e13055503106d04081c0020002e107401103960600b07045110340032034481c0003044101c440150070301c20052100704216154410049400710710388650601c80c81003110314080c250080c510740c2c59143c2c0e41d0a181c10640b81004140c0c00203181c10b0507140034010b0f8200000106c401990700100016110407a141225903200401d490580d403100025002142c0c000d4041f00a044c000c2c028002c035505248001016000c0e202d02e4442c856104400a0004601c4d00f0001000a08030340107000d142a0011156580045900540c101000503030142005001001c07416a402c44241c4041c2403501140c98034945680401c9090400c442c100340c0c543c0c010640300e9000b00700303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 113466852 1250 113465602 113465623
    0x9140405060c160f0b0a0614010e04020a030e1009050115030f0305180303030702010f050105030a030e040c0203040b04030b010e01061103030601030902011b06050603250605071104090b0601020f16050111 89
    0x2031900c0805036600f086004032000341c40c041b1031185888030010320310321018119440000107855441070340000c0010400290010700c000810b1688030b04d29000e0315a8140a60072036900c03c2c0b980003550015a0402a0844d46041c0d805217030105250300510100d142c8104101c00300d0360501e881ea9580c00b4845244e07104602d40300001c3e4152001000703111001d501034010307081030711002001308010f80c2e85008140d6505800d580150104051002030a803d0620350004590290380d4011203140664070710604403107a0081c0c0c41610380200c03610060107101e0001c00010300501061030519803118045207980d40300e12015000c0c506155840a205086900461701070001401170031030102d040c075403402d000c00501340072241c6512038041c040f50300c001c0582c3c1440b080e095020b0140004c40160030100e0a840e10381c0302c0d80c019544450120b0b0840b04d48d0303407240503250301e0910a0300c0103010307030800c0000645021940050f41129401010041e000240c82d00f034030714203c1c2c5003481e000c104130b0241c103d114102020480e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 113468102 1250 113466852 113466863
    0xb03100306020a1707030b060d0213051f0f03110319060503061603060803040f030b090c03100c031d030a0509010c20090a020307080a0c02190c09140405060c16 70
    0x54401070064101210321641e01c1c81c0d000008207036417140b104a0844566450165000d04240019403004d020381d40541383d2400b01e8a08601c01644520000c9c00312011031080503000302d481951551411f074442c030082402c014901f0140308161301c560150015001c000c00100c0390650914010091940f581c01c200024007020f801d40e400d904100903c19611142080c0e4680402e013041e000081500c80041100c007140d42c01041b15018600310790304c003d80c940002d0f10808903031050702c1210520b9602400440d1001c441c0f40bc0c0007940c03101601c03014054505200c031020020788500e440004060021080f11500007240c540143d5542036003006880e110318070700c0c001c1d050f82c8256071442c80350051035012442200044032858225a0b80c00e240c4000d900c42115003500255452010460070700568101034204002030041d0307000742c0208881010710040100007078941314440c0704100030000803403081c4121506610b25400d100e00e060344a556440401404550079100d000481440103c82003d603040e1542c0d00c00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 113469352 1250 113468102 113468107
    0xd0503060616261e0c030307030e0f060709140108040c18090f060213050d080405010c030e12070e0705040302180411030d0c030e0a03050a0b040204020d0606050d0b0402040806010b0310030602 84
    0x1420700540c9034228a00a031308003044140c48400ca8a0000c042d03485042c4003038001e40c40c40e0b80d0300004502034442142d64000510441f103410000ae802030003102e10609081da81c40004c2c910340381c848502d100b0384075002818454001d003400040740d014141c0350107031520030f009800f2900301402208000c061005e00540a13241008101c2d0400c45240c004048410000c1002c000858440040000030000a00004e011a8041001300300e01c0d400b03100504041030290515a41c02404000030030701517a0b800326240c0690300500003d018244003000c0c000d400000c00c1c50018102421580031a54221186604915468030300c070001e0704103c81400048503680b4040c00b6524a0b925841000d4043c1100b810100c7c081404107180c400c1c41d060400920341241d4001c4020001e025081d00c0e41d900d050400742050744c01903000c110394450a03c1500542c0e00420300c0d6070f142903175106188410000c840100700d01902c0742c0c0c0100810081c1d4040001e000d03041d94500c0c1815696500c038440b880d402e1403800c3d400249524000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 113470602 1250 113469352 113469413
    0x14070309030507060305060108011401091d0405060c2d090411031b09090403080403031b0e0901081209121f050402011206030314070201050403050106031101020d0503060616 76
    0x20590490348030340b0444000303e480c0c3d0400e40c1036546c01c8030780710300240100c00104100c2002c1501e1014501d0107044c05810035440340f100b0b2480b08c2e0598244a4100706003400d000c1041005c00800e50310112900b041030402401044007802c00803145a030703038016210240c00401e80032000b022500d107600003c000300800e0000740c0346d055040d002203400c448070341881405000c040603803008072840711800038007521161342c0c1e980c0d055174a080302a00c25402c05030350307410140901c0c0119580c00d8544a0907110104150b40e00410440146016041000e0b950040010a5520344110059401c2c5601c00c884860061100804161405c16a04914081040e0b824600e40082c4419400303580520700030b9940a4030316103040f94003002d0b26120b100080000d502c5441610b000481c00014002c490710515009260540d40e490b15400d5034081d40003690301e20008a00e2182d40d68040240c241e42040d9800c24a08529013040003944034001d01a012981d220641c0b2224100905654020744160f00303a0100f10003c00d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 113471852 1250 113470602 113470607
    0x71a13050306100612060501050d020c1504050304080c06120a050603100609021801020c0a05100e03030f030a0b0901030f0312090501021204060605011409040930080109050603100903140703 83
    0x1481100e0114044666117200c800c1ca90081a0030b84070181c50741032034102d6040d05000254800101c455041c040d0380c03003144584810b2203149005502401c0255202ca0900c0101da007440e2002844500c1017100700040b011414500c0c1080340d101400380d0000030260b9900d40441d0500a40c041c0020130742d07141c114081000d40781a8080c102555520101c2641d101c2c0b21401680c2d0b900101c038402d94000c03038016042005160080020b00120200d1070189202c040e2000802d26542051403511030540c1d01004014810806103d90000c03403200b00c40090140d4591b0b16442a103140300d80d0701908104080c0e401f2070301e4803c1a000303201001d03482402113690b0050188a1200583c0c151000c580c250300f4017100182e80e6201301c1c160361003003c81c0c20f40d40e884c0c10100340070440108241001114180d2040d01e1190180c0d0984c0c079101d103008100306c10840201416038001b440d201050700031a00c02450710701070100380e440001c4c412807840c02d40a0009071742500b6080075904003413030742034103003021800054000401d603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 113473102 1250 113471852 113471881
    0x112080c06041a060a050108040b0a02130303020615010314070302030a11031e06221e060608100e07051603021608070503070f080c010c03030e03030103140f071a13050306 75
    0x140c0640440994a13801c1c104820b404c2907109003800104ea040125001c10140006240c0120b208000140f8010a08001412a00d5a680242e0168000038104124000b03010003070400302c10246000c10401d20142c1c140880c88034042c0c002400c0503404000240c0e800142c0e40300540e404010381a05482c4e103009499a03000010f0007071a1601e00b001e0b4004508a07040840001c00d4881700000034101c0094100c0d0180000d0020184115981c030169162503803c0500d4030445020b890381c2ea40c1d00034185810048031064031955480030b40c42c5c0781000c04101a940d8424241c1c3c02e11403420140341a11601e0742030880c58850a5070f0302d05e851261101c00060b00348400174a000c102c503c00c0d41500d100942d03c2c040748108044078881c121958010072403d034248e40c419200343d803c103482414001010040c04d0031507031541d00242c004039078031000d500c00085103000030803010b403034188070710024035000342898075074018901c644402507259080410062460f0340c103e80b8400c050301c405412141d41d4603005c001d420007007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 113474352 1250 113473102 113473133
    0x70302120d06051806100e0117070f02060c09010e0913061103160c0c030f23030405013203180a060902090105100f050708190f0908010903080112080c0604 68
    0x1d811000036504081000f044e100d108210040903060034020100060340d407031002041950400c9000d81100ba61043c00a10701c80c0942d040c0d550f03080d0302d0486000043d140c05406000140800028040746200307a90080701c003030003c082998900000d40b03c20a400d0403040107103600030546030502d41848c1c800d40d01390b40507510500380e1501d0f60f018205400303800d0714056910000900b04000c221028000305030124401c0f25128410061101e41103540000c41c04101807101d03540320980c0001034200701669200100c0c4002510110108078850100e88110f402e182294541d802d954501000052440c00c01c40d8403000c5110008c000d41f58640c1552a00900070b0040b204100c1c89001d40800108460800301c4042d80704205c0c0d601d801540f01038150050b03030742c0d40006038210f82c1c0b04020040d0100348107081e051070800d40982d49603685072850a10001e400c51880f900030000d1a0700d807154a5000c283d000100030304443e0700c1d61803c20400b0050422034020b21440113046468410401484104084201015001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 113475602 1250 113474352 113474359
    0x10f1b0c0506060603061503180c011e081005040c080105190302010203180a030f0b07030c050a05040308091216080607020705010c03030c0207051f11030c070b070302120d0605 77
    0x1861102015209030810860151090344580001045810050000c43d0408002810600d0a078907050a50403258002c542031400180229203000404d0000c01c5120032400090828a01440c16a5040c281d843c81e802000c008004106010541c510a00d0020a010700700c0a0010b000c45105000d0243c03014100303201d81409842d103030300c15241401203201d4080136650705a0296142c040f0000c0d086080c42d0020104517032007105601c0010014030f0140c4010512441694000d081d4600000c026080780d51081184051200030030020101c56030140480341030320740c403014503170301d603041400420744420034106800c0040c424441c00056801a442c040c900710341550003110681d03592a9403ca840d100d07188101c6000c40d10403582280001c0c029005107451500e948116800a543d0f48001460640c0d00340c00d00f08034800c08501c0d03508090388407428a281c40c05080085180046c0c102c5501d685080314825842d00c4440812403a00701807090045040510062891a0319080302541341c0f40103018500c0740503c0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 113476852 1250 113475602 113475641
    0xa030c080a14010303201608012405010c06140106030b032a090c0d0507050c070905040b0c0c030412030306050f100c061a040f20070503040b1b010f 65
    0x880c0e52034007a80e141d40300307003024a2510b40d103159029144016411100301800071140b01c844041c06041110041c802207082e4580401803829010f182190b580d0150b04ac4c14012040c04810510400d01c410300031203e007032904250b0245035040080090546403001c11340c002191000007012507143e0040e091130320085080c1d07054164241100030b505034104000303c0500480c0340c04c2154501d0605091503120322040385180c0f404545507105d000700e60044440501160010070348213000310003004400041d00245400300810b007495121402c46000040c50410195000250a40300c15403d0043d600113000311a642c1600c40c1083c50090003600310ba00034140200c00c400c00700085071400d45080c0c805200241c8641c3c0c800720180d199880501000c0500740e0b4071488a43c001d0070346466910990354820b01c0c140001808510507010b8503a00031224030050080e203c2403080380003040010003280c0483d03100100ca2651a904c08159041c135440e54249140c00303519000542e1105900e941001b0242c0700903580400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 113478102 1250 113476852 113476861
    0x90d12022e050c040e10030b0907051305070201021204151a1f020c030d030b0f010302030618060f060403030201050f06090114060d2705060a0c050307031a03030a030c08 74
    0x310400d002440d030755a8025034070014081940c407071600044040c42c9145043c1e242d80c1510b030024400d56490491090030102002800b440403070075600221408081c12481d46401e0002e00519503400d02600d685507580046500c0f94003d504a80b6546207440d901d4030300d0310f46820400350441100542601d018100940e035003854444104464100c1d0000f8443d00403203031508000480018481d208505602c5482540480799600b00542580b07407800b41c1c1c000c103c41e81042c05005002020a03000c0e41418018070920825503a1003490303004642c0c0d400715010f000c0c1e5401c40014000084da001c990740100340041d000c41850b0381034114a00c41c1c65400b0711051075448803000d05c40c0c110000d20890040300d031290241480d0340360120050095680745000403c180640180021240c1c82050096410a16240c0300c03400700706091090990241151008104c04100150080c1141c80300800c140d00b015944c201c42c055010070100b0308428440c02030100c9840b0305882001500500f400c038401804200d0400018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 113479352 1250 113478102 113478133
    0x30c06020d020328020a0b0901020a030605060408070509040602041d04050c0a030816060b0a080d0801060309030c120201140f1b040b0a030e0a1407090f02090915010302090d1202 78
    0x6482402d44c0c800c021600001d00c41102d1504141882510300b14028840c1d4140440c2800340c00301e00a480d40c200050703982c0c40014010f001c83d003295100c5401510188410408810045801c0c2c0031030302c0c00e841c507103078907a43c901d4180000c0c41280c0101035000089400f030540060941f6607680b103144500700f01c1e0340d0118060100b00407a8800d1000802140e0b08014410002081c404001d0321144039441c089941312143c40014007030541b640051000c1d6000301c1c03203000000c1e80b0010300f5004061303e040811401000d6140240841d401c804040e010210910001d00694800d41c0b1080548540d8030020145042100c403004003510203540c09181c1c3c0014500011000c800002100c04507424210341d40d1030710207182400e5001c1c004c43c07000001140940c4d0b036040003080040f100c07980c00b203180c0360151076403508000286007190f140700341203099a8418003902e2a0b0303483c0c40740002c4c0c00c00c011545165500040c000120003900c1880301c2145c0000f0700340101303400c0003000d1103620101c40d0b071502a10501001520395 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 113480602 1250 113479352 113479357
    0x801050d021e04060801110306010305070f0203090f0a090515130c0c0b04110d08030f0a0e1005090115030b180a050d0305060a05060c0f010606050901020d080606070c030c06020d0203 80
    0x42d6218141c1401001810241980484180406000415400e64030b1101600715100385e558444070320f40000c10050b2541c7d0500c2034540c803068134242846200b0480c2c800a6070f901a00d0034150155095031030303007e550f94800c014340f0001c020b00310701400940703020325085c0b01002d41030b06624007a0b54a9250460498094002c504000e4400d035941640d5a4081e01c1d1894072241c06082500c0e103042a80404200340c80b010301c94507003940602c0d640e95590800520007961031000404ea441d1307491500040a01011000c101585640b490721008074440e1a0341800c00c1c0100062100b5002910350f101c00041000680300a03284207012305407010301920a03501c1040d40340c5007900b800802d81d4001201c0c1c44079440c06540100e4104c10040c0480c1d901645507008070704075900c0316040007483d51001d08a164000c501340110006004680382090410f50440000707981c41320f031090301c481488034590000d040e5444680c156100140c205250007801980d0b41040740321300d03400c4d008150044c040d105540184038000401c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 113481852 1250 113480602 113480629
    0x30a0e100c050d0b040204050402071202070503010614010f020c120a02120106050a0e09010b0613030506150907050c121819030f1101021009060c09050a14060f19030c080105 76
    0x10340b00d1425110020580c0280710b1021020352050742400045002c1e00d0702e10103000224844e0700c10030282c02003000080e280a200764071661103681884002d00001400145000818100707080c451903001042100b41c0c103001c00c0c040c0041d00618448084186140c0000c0c5592147d402036400300c64070349000700000e090351110b02400c1e81029440700100012150050a80d078012840d40000a84031242d00000f1001c2d40b044001c5c442c5800441410300a01c00e061081c20340055001e60108400d501c2100452164080100302c10140280410039a8070441c06000392281283e120311308694520344c598a95081c0c20f1000401d6008002e91151152240070030700ca001c06903070f004030f80c031b002d64901940c94141130750545181d5811402228408048407409024060074544215400b19003e200001c0040c60310304198821442141c0d292005c2100d00d8002842000300d074810384400395140020210740c0b01c4c0f4400e91000500d18081e401f12401c0a5905903c080008012503848140381d03640c0f0030030032a800c449501c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 113483102 1250 113481852 113481857
    0x105042306011421010504050a020a0e1c02031c030621020d11090a050108010f090c09090f020d0c050a050607020325080102070b01150315030305070201090308030a0e100c 75
    0x200407a000390b0103503e40003600000640c0c900d1500d2039400d08450402c001030301c541d0300181d5081c01401503107454081c072540041c42030401c44c20b00740b05040050040307032003045d024090720300e488038040181c4904030a442410f401604450860001c510b0f84d0003a0080c602c00003000a18242010448510b044417284590a0610441c080741c20f1039020064101c0410004031545001c5980300c1100b5201c82c01100c0c4141b80780c910021705580b6205a25094940c03c0d613240b1074103440d0088400c002081d01c440c50050b222807002c0050030703066614100210700c455400195003c0c010309021010843c44410810680d05e064500740500c1d681c41061080d00d0080c114001d40c51742104d070102a9090b80c440b130450350451900d0321841ca9a070b0354000705003241c1c0445010341c0c81c2d4110000611032000f011030382c1060300d811454104005040c1002003210340881d8040141003001c0007030140150380c40f44078440042c3d0327049148283d80c2e04003a42860000e16096010607414043c40040320208551072240f00f10f80445078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 113484352 1250 113483102 113483171
    0x803070b010512150915070302070302070920090301060503030f0c0f030a1403091e010609050f0603060601140f21090a050d110703080a03060501090e090703060b040f0c08010504 78
    0x42c0c010315000000e0882025100d59503201c6d03401d0000300c5c3d00c20300a10300b030703103005a40d0381d010304000f4100300960700718460060402c0e0104105c1c0c40c010308000c3c0400b6150741c1054880c2c80c0003002038050642c981c8841d61520001c42c1680e1080028002007400c01100e904440e20140161b41c43c50700c0e80910305000740822520034000e00312201d010025980601080c080d030303010980759024600011480071700d02c412030f035541d4001d00402c1c10031320030360383c00c4107242502c803055103000c40c006503a0f00d00003001d840c10802c902c0ca401403071482d541306454021440030300b0280c8400321b4030580201e028869016004510003c008900c20382d03000300710b0014194002c400b40040c0002001c0c00c0d12084082020300d00180300358140040032a46800c06003580c64070303654011904a00c0d1500040001000303400c0342d031020b60a501030022501c00015040704490307018401180c070040345400100208807203030550030310501b0240280e15460380303c080541030b40c6003107804002c80c4a15203003000010075511594500c81d040c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 113485602 1250 113484352 113484373
    0x9040906094e030207020301090c060302130b07020f040903050d1802150702090718050607140c01090e010303030c17130311161a0c07120c050904080a0e060c03040803070b010512 78
    0x4e40007010307821700244c00030811940d43d81d1000c55151260340701c2e2002980c041500754288000214003001440340b40030250414060b41c00042c20441200c03101803045646500c000109030098044d120828030283e810412030200d06140c0494140c3e0700310483c49410b000158811465a6000352541a600900403484035524220180e450910308480314440c1441c1c2c0c4030005a60340c1d544014400da51180369016020102c990f1800e181c4901110460305009915034180003081e4040b5846045079094900412041401400ec3d55000c403c4004030184200100c204014441c10461100805100ea074603001c101142c45800354507810004040946056801e1081003146415041c0c006c1c41c262400d02c043c607028100074107601d0200154031003070130149142a4101448641c40815004210980748803009141c540d03545102840b03004c03501c8050104031040480c2c192112000e440b1444020402c5a50740d0382c5490702c180d640c4c0c0020204840c0d01991000110706414085014010360070004002c1401c81d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 113486852 1250 113485602 113485607
    0x50c0103090f060b150a091d040506040b1902040308090a06050310031112030313110907120c1101050907050f04140105010503071b030804030f080105010509040906094e 74
    0x104001e5817070b44085011040240c1e107800c5801880a074a040d15510800742c0341064502e84091501c03a4480c07142901c0d420000410b0005c00c200c0c1d0b00c43d62100418005540e464032400001c0429018000002e1010601004000078032005022600007210b8442c40d46903500d07070840b450310003100c0c46103a40c10144403c20002d408000040c44c00c0340014504100c079107000e980d1510b140c204032404000c107400306a0741c0052000030804d607243c0c15000d84081c81c0519100e40003501242118141144440c2d0394035182d03801501c0750b118175680c040f00314001d20103070401c100c200c0d540761150300400d03101d900c0b001e1566070760b07240ca8802c0c002100c0b81c0c0300d620b0072542e10306401074800c3c3d0402020b10061050349000310001d0315014081440c23580c0300b504c80103201d08082c1002040368060280e44418805048018480c43c0c2e04001601c2c3c400d50708039030100b0421001e144c09004cd0640c078070001c1c0340c420804201d040341c80844446000614603c040080e1041c141c074030030124029005d419850b0440c01c04900d010380c91 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 113488102 1250 113486852 113486861
    0x30c0308031e090c0f011b0b01030c080303040218060d0b0103050d1103120610120204060c030f021b060c030c070909020f1504050904020d08160302010f060605031611030a050403050c0103090f06 85
    0x1178141000c3c4a12000b814503402c40c440558030890300c18104a005208000301001c440c0007520740140114290701d0030f030740440c01107850b22082e002c0001a001c005099a99807805600b41183c0c021246601035a491910a5a03551600c0001d0081401c0070480d12600c0340010944098a070461282c01294640c0828419620804039827074042010303020390a040c80380710340000d00040001c3da42d24030380b0703007124100107004140049980c021908196240901500c00d0159a480c101d0100c0d802c60b6145080c50b440e918611803407d107001c083c02185000600d40b00c181d031110030341600a60302413903d803502108104036007d10008a2031458000c1c00280800e00300045140e9003c0d00c080e0001c0c840028684452071030790000c10340700b4000411088083d00b003560a000b441101d858019080c4411403e00c2700141c884d000050003d8200e0703400b510b02082d0a1b1290658040e07280300701080e42d03910840590014196445400b082d40c00e84030313100d003500240d446482103030042904078800868145450342d0b01c00103071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 113489208 1106 113488102 113488129
    0x306090f040503070212010b0310090b010803030405030d111605011d01020c030405060c0307020d0c030605090c0901090c18180e062806030c0308031e090c 68
    0x32000016105285c0c2d04842d80000c040e02c555070711780140340d040c0c1000d43c103126202d2410992003280c0c1c0280c0401340143c030303c02d1003aa01c1c1d0403001d036a803106440042c0360742e104014020300e1010507800318140d0b0480b4013900e8a40041c000501000f640d200341c0c1030710180d40d100521074142c80b40c80490954443c0c100001d500b001142c00046440340114820035000341e0740010842c00b0714009100300d400c140d60061101c0d9194a250031320604401c0140011501e280c41e14001c24018400010b074103070450300041201e695030382448441c2c4082c00c0c41010105c284040b440c0b561410390011a014005006100b01c160103209003a8041410b84005000021031034128030706204821b6404051522400202c0014090400c50600d4110052505a2000d4040101d2007008020481040d00843c094038007410300c004102c1e00c19440480c1e110341a90031082da58072001401311242401400590b9030f = true := by decide +kernel

theorem cover : BRFrame.Cov 113309352 113489208 := by
  have h0 := BRFrame.cov_init 113309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 113309352 ≤ n) (h2 : n < 113489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
