-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2449
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:49.139837+00:00
-- url     : https://prove2.me/submissions/973b0103-367d-4a78-9a13-3f9b22e35806

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 440287769 ≤ n < 440467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 440289019 1250 440287769 440287789
    0x706090b0604020f09280f0e090d1707121a0301050a020a050702150702090103150c1d01030e0708030304120f0206150405040201200f07051f0e030a0c0305031c0b011d 73
    0x1400d4820313880594a4107e12104a80c034410900d01c40e06080105907904804145c070465081a070716150030040c9880003420340074600404c02d2041003010003036000e0395440790046001d244034a4050f5079148800004050840f43c02400c0708820b40d104004002c0d1081c0c0010968102d20b404980490724180003210100051083c00d500079800755081c1c00110800112040c0020780651000c810000c1c1452013500b504c0d0b41c484110070110510700340c3c8403201c00d984a9041281054080001d8880c0b192703441016900e03541042d142112102002c40600d20110b51055881480d50703103e100800090900b403021a458440e5070481a010b1612900080c0035079000d402000000c039188910010300c05008040036403240c010551609060007540d200091610b0980802d1501010124041d2580c01c179401e41660890150b18240b909402040d400340c0120766502030b084015405003000d15a20310380b04503051a0205441141c0c50b0041c40c001e0460070690b8407103a5454420020120108801d4640c40003c1b00c42217 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 440290269 1250 440289019 440289079
    0x91e071410120507020a03090611070e0a0603050106081005061906232209090b012102060304080304050d05030112060b0301020d18020406170a150b060706090b0604020f09 75
    0x2003000e040c04280d17580002c1d80100c0c0c40c060b0b41c1302c1035030a413039120885013584500600e6910303601030481840300521230110305800c86d480082c001001a0b0f290303030352401d40f2519445074585401031024040e040c3c603036000b074640c4104111650300c502e40140094003002d0010f80240003c11103424002500320401540a00051410201c0580c0302d6210001210000503140d884034031410941000040750030312805000c03107090313110102000c00d80c20005410500001000c24134484103400141c480980c0f0f6407001140124020f400da141d603480c2c141082490300c01c00f02c0e00c4204000c01000100300c041030022818000d81c1d407003480480d018100100181c0680510000b03241564902550103841d24211300d5030360030092007038034107002c41c40e61070003100390742d4072103000035000c94202650141c00241c0f0101c401c0f00746000e040740040c2405a440114006812010b401c6440030307981c0305400d05110f811a6450307445601141d007507150000c58003030010701e801041910350144443c00f00c000c180d03100035207002550786 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 440291519 1250 440290269 440290271
    0xf01030605090312041203060602030307022a04020412050714010815040b130c09050f01050a12090615051c200d02060d050106180e010506070201030e06091e07141012 73
    0x30078142420f42c91b030210101030701c1c0070901d0031600044d914008803d0301c3c810300440c0c014141045c410f0081d8190708003410000340c1080251200c41181d81d58600c090000b6060f880c01d101c8507102d082c98494034156454000041001c5c0c0c00140103046d0303074000040d690010f040821154200c83c610007044c0074014400c070040c1d222029407480802c034005548000004181c0d40e440341e030203c0e522402d009072041015807039400102c08014070ba001030700848441d0540c0d52101000101c0c1240f58540b02c04440281811103402c14100d04104114500349480084032100c45560350801d035aa9950518a004198030f80d010724000d00210215603551451144407841d0003a01312a50740100070f0f0014018002400381401191000803030610388440f5418075400d0b25041130404805074200030401000350400e0381b00324109501e401d100c10341d4030400d2224034000c501440c0100141104424004901c1040e50800c0c085035200000810119201201b941c281c2e80d0180d4600b020382c00340d4041211170004008641c1041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 440292769 1250 440291519 440291521
    0x120c0a020a0311030c09010b0706050907170a14150f13020d14210a03020904091a100b09060304020405070c080406020a150c0e13021e030f010b030f01030605090312 72
    0x2000d40070490103c014421000d50740282e400c1010440070381c0081c02141304482003440b20200040ea540c2c80b2640001c0b40300c0446646581d100d0a103440032486004460701908025444801c00c1121410000d08880d00405080120500750200d214450000c00b640800e001d079102203899074006101c1aa075080d0050000c1d42c01100328201a400028002c1e150181e1780700c1d00c0d0944030020102da03010040280b8008030b0364507107156008214083e4100b0001c5903802944e40c1c0c1c0e4a0700081d4120007000300c0308181c1c44042176510703281044201030030055200045c5100100407200841d0b441c071040f0307984940d046400107900e460701502203c1c520744c103401c02403040c1000980407036003680020360b100c91244076920401801070000041e0b8183c40740c9090100100d2441c450301c01c1d0502c0c01007100d050b031260202c0014103060b038910003101e58403150340340400d00c034400000303100f801141d085103280544202c00030079146003004204d00d111f052051101400103030741c0340d022500040c814000c0310307244030107038004100c0b0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 440294019 1250 440292769 440292773
    0xc14061e1c090b0f042301141e070206060604050405220807060608190f1a070f080603011b050f27010806093d090b031509120c0a020a03 60
    0x200300070b05050301c01c1c0c5007040004004c50b58080c0781c07910481c0d01054007540d5041900c40d200603190030544500701552284189441c00d018005124030900800c040c1000060088625840d5900b0140c0401c0c1103401c002e0030050b441d25960101c9084500540c0c00158960380e0f10341c1c40050401c2100ca1400001070300c8600c17002d010103900079000c1d80d0b000b0304040085641d2036400c2540d03400380c4441d1101c086410003940020946035414054098003d8561003060070005048042e100c0c81100d85001280f6a9421508400d03403001003154082c01c00d40003001461198680c048001c80340d4992134040140024007868410780400c290b0b2451451419214104002e989c5046075500c81030724124001030a950000d0394900e06214098051000c1080d03180c061424900040c0c0034402c1c0100ca0800c0c81100f19100c40e8200410300a14000c2c5500000011561035410806040c98400000103944110b69400c0c41600b00b0041012050700d001c03008003039070300c080d14007403941010a6000040e611219000e00002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 440295269 1250 440294019 440294021
    0x3030201140c040e0105041a0909030408150f01031119030f02132901030e030d05040233160b07080402010e0303040605120a020c0610030c14061e1c 65
    0x1441107240380701e00010b551121002c0c1450300503407003483e00c10442240104040d042c2980320140d0203c2a81c07001606555290120742c82c0841030b5840d541c5607000080c10040320406101100709090070100003c56410300792004001e241c1c0600001d845410404030550450f65440c8860712595082c108401f1603035500e0400706481d508441042c0d00503201d201c1d035502c09210303511818401c00d20218010b0304400c0c0030346940d0b44044c010440b85040c90fa407030001c040d545004101078115004030381004135070b503d01071060090544503042c4a544900501d11030b200002040c220310311001200e00c1e80192159400d009a418000083c98090301900c100030a0050031079010048910650003a29000c0a01400c0d006066807445188669800541c043c410300b180c0760f031a400c469401055040015007802c48820b9414104682a5698803003200800010000c00001045450040136415140c0c4a60342545d80411034920400d001503803004400c1d64461140007600055854540c00c4080c54040c0d01c0c142403400d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 440296519 1250 440295269 440295281
    0x711060c191b060b040b0a090608010b0f010c0b100b0705010c021c02030403110a0905010b0d0e0c1c3e041803121803080402011205010305030f0c030d0603030201 71
    0x20300150606600362110301e0103414810907008844001102220850310b80500078100c4c100900d901c40d86910076400f460b076928090320054800880b0000b0743c036141c00000c5007101d00052820340503800301281e1507101e80c1c2001c02c82c007006810044010081da07503880e01e2030308010320f9000000340000204803802484415444001940403503000c841982280108076400c40501592100069004001c2440003072144061003030720082c080c4c40076100c1e607100c2c2820401d540d03098120f0410070001050b002d010030722038041d080549001c180075000a81004011855203955042302c0103815164440c200c6c20014049911304141300442840c0c0070510601500d0500c58036030303882d41a10784030703841c0c284209841d052081c0811881c200c030112001c00d54a07a015264070448900100c02c5680e246865004126080c0d81c0d00c031024480d07501c5c0142441e140c4009001e05c1c040c0c1ca0380c07803540c13403614006100090b03000003210304800410101395140d00d40c41003034074910320444032031901050400200100300b6805401007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 440297769 1250 440296519 440296537
    0xf0d050412110601062007090c120b06030105090c190905010f021f0b130203090a022803080d020408160f0b031006051810090504050603071d0711060c 66
    0x20400c052189070100d8891a025120440030b0308a6001006418051000c00c02500396501c031420700440807061031401c22880c4d80c0a41421622003089401c49075010b0100300616101c6101006080005008111140414081c0324028007000380450907080000040e10155a082e0007484a19141200f00a050100c103109031804100a0403504460341c2c0003080d2041c500d503d50707944140c1040200d1050740500716191015401089084038404104483c2c00154032034640c1c2401804014114030502c0b160340d641d008854611403682e045c204c08003440c038240d4001c90b43c01103603d41e12590f68aa155000744141d42c418881c0d44100c0101c00340d0350189480d01c0c001c86080080305040340c0c5d5103003100113007488110380400f2590701d100d13010b005140c01003014210884211660004640d074081c0801e407200308400e005000f18400000400c02450a801445d030310041c207401411055150a003098548c4d606007107a900c62460010016181320f00c9900203441075001d00080380c0a80c14020032000465000c0340c48 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 440299019 1250 440297769 440297783
    0x110d090f020a150c020d03050403050601030c1a0a051c15080120040e01060f120606020105090d020304062102070b040308041101020d050912160602030c07080a0f0b0c0f0d0504 77
    0xf80c040d00000301c4044801c0984500860702207507820814034545c43c44040301800800e000100200f0000c00019000c1d5104401400c103050510041445006520072202c88800c0700300710818410741e0200079210081c0804210071000a500c40350400078088c1d0329a1005400503921000420720303015008a8100b40c4d09924106071035000a0215330f2174851409007100c269107100c01006000e1244a01041030f07002071a01201c000000c2c003a410039500307640d01c4040141e444006000701204240b000b4a035084090004514291411002a100340d80c0341044d42c140d6082a80300503050704964040b10f50580e80500340700c0b16450039140c0034106440c00e480c00d50310311507803650b1000194000218642c00114070344500d400c01060f00108102c2080d0500d10340c00768000d4001007081c003400c0300d42820280045030090340d00d07601c1036000c90f4501019503002d03c8180c0d111501031804907482c02c0d5400d01683d0005172940003a40d444100d0070b2036204840443d40e008000055840c4418115800b60b03004501c01c0351 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 440300269 1250 440299019 440299039
    0x40f110913050603151506031e0609090d0e011e2a030801030f052406100215071b0f031d040b090a02031f080d0e06160303110d090f02 59
    0x141e00c1110402c81e0030304e8059006480f034031400d0000402c1994490120444e501541450a000c40c071207410503980c1d4200d00c00030500c09426403641c0032a481e8020003c4d00c1100c0307180b42c050036150b55038a00c0314100c0c00344400c42e12003caa90b41f00e03c1024110440400d0300421510420f04001d0688450044801e6400c402110034180c0d6025208500380c034a80558070040e03680d095403a108003205036103108035690b200d2a020300c03030190801140c0d03000c109034024000e0000c0c940074042c0011030314280180c50464200c000501600804e4959040e084429860222416031000ca549058030800000141400c4440c7e44590105a4010048040d1340c88480f48005098035000521003601c500e005001d03400380c40d450006400008560103160f010b210310032600c034042003e41c40021a00f405810003010380c0c01400380c03034884e00d40001c403480803030380c00ba10140c0c0391440c0a42c10704c150790b1181c0700050800d51521014002107840c001900c1c41c520b52607034200500034041c500210710100b000c408034090300c0045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 440301519 1250 440300269 440300299
    0x6030b0d0503030f070302091305010608090a0203281515090c08070c150903020f06060a080d0323011d06030c0d060509030415090609080303190506040f1109 69
    0x8400e400c4880d81c400c00443c11500e501c1e401402800c0014041c208066090040b01c000e5a5014600034418001210004a55050820007000310f14000c00040c803d40c000408440103071000a4981366442e210083c4074940118210300d0350004400700b40250400012010030041500c00d0760011640607201c0c182440040d94030714502040d91848010540415000310014141c0b43c0130388440440c8a2144641d482000030340c0c10310038100d9640342d001780c0040c2c0c009449049003110401c01d258205030119040160b0078500740310306558201c104500c0d402c0545404000075204511000003070588070702c010b103908568550100b981880c03820291906803541003000316449040118a0124011025007032050941940d2030300009420064182c442e988802c00000451010304260024555110380d2800146850041d005200c140c03960059103039504108180085801d0035055039900481049022520b562009c000600400d085403004039000c0c1800c00111084c22440010010604200c40100c5600128 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 440302769 1250 440301519 440301529
    0x429031e09150609060310020d06032006041802040302040504150507090f0605090f130605130b061c0b0a090c17060f0d172d122205031306030b 63
    0x1c05060810652400864000d013040f060309544098081d0803128034008030111902283c3c4000252401145d503440d06100308024a4040700506d0314003000b0040d000035120003e05603100d1072140c0340400080c00703105507419040e80c05580003150020000c00181c038041c289118078288040650303070024608000201058051004441900e00189080745030a01b82801524507500c9860b84680c84039000b4414511030b0755200180c01c071005141c001203109442c02092100c2907448038040500141490003000d1103403200020b40c0d042003200c800840da90064007613444002c1c44640e030800d0b0090a4003101041010f00380e04443d512148503590700c2448081074007080c448203800d03542d0781e0307120101d103010518a141a10700109224050a0702a10603405031007018680e51110042d8105044240080841d140d07007401c800341032104004101d40752a40103e00702d20300c11801442ca08038400442128043c41d907a4010300301a041e031181c00c5030b50320101001203030b81c41020b03441204006410540e02c05083c6c144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 440304019 1250 440302769 440302783
    0x1e0d141f150e0703020705011e0c050c0c04050a06080d080702060106020c030601030f050f0d0c05120304020d12140c07030512040605030412051903091104020c030429031e09 76
    0x707565028100604204080b010044064041c00070141c0034010300021880a204a13000c90421416001030350445400c0082942c96460481c030611a003803024018800000c100103000500c00c42d0000340c10360b60b62640400618458008030400e100303000d00a6050358209a29900400017038086400a07a40e03950100c0e52000031107031007501500042c004100082117441c03040c0d0349038856400e40f030040317034900a2540742c604d40c511000001181c68809109112050084902440d24800c503d450740c54140c001c502c0b5083e034150300400c400440c0001100192050600c600c805181c1d04015a852000f0ba841d6940d0b0384031400241d845000d6803071038402c10303900d00086800300d5015864450450b41c43e84c130f50030007144007071780b12106106040244c0390030305120405000c108142038034006042c17840c40c10407402c0144d000d0540c178003440c810048407a488030008203a030201c031842d401080781c0c1c5140083c808005c0d201c1080c000c00e402004814421545440c0200001425800c20030503a1a03403a044503a81e5800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 440305269 1250 440304019 440304041
    0x50415051305102304030f050d08090105072010020f07061d2505090a05011502010e070911040b070501021209030f03070c0f0b0c0a030c05091e0d141f 66
    0x7407030b401d103050010203d90075031132000000d02415007880e0b0b40740c4130240ca03408100e00442d22070700003510392031700709070402c42e00c2c3e4001100c500208001d140440010b404c0d50030769146102c10120903000280200000c00400c0b012807005d0406548a04079526060b0041e0000b103000c681c514104001545010121040c070072488003400002e0052007030032800c0e00c0a11800c486203225940c1000c001248a4990640d091b001d210300a000180a40c984045420280602d8101d8000c5905200301d4605941e0300149140549581080005050501d121b114441c0d1065521070f455200f40441c1c0c1205016041d805802d00704003004084501d0383e25007030f0076030300c2e0310490416680e00d107400e10128100d9880b600090456903c2103409d00240c84d10780c0c44261414030110741e058030f03d07036001078556001640360140350038600d414240107007465103c0c1d0000740441c903203000c2030280c3d402068840c03c5942e200010644903c0d006003022004018074800d603529603a50000c10b0019101440c2203d02807415480f07000300001d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 440306519 1250 440305269 440305277
    0x70503070515070f0c0c0509040f060c020a021e0a03030315080106090e06100f0e06120f1c0e0604180b0d0501020901140306030d20030c0c0a090501080316020105041505130510 77
    0xe0a00042088d1048041d0040d00c2e02d195041791000021150310606101c0d08840d001044035a030f180c8100181007610b5404050900340c224881029911500399400541e03a25080c0460318806e503025500c4420125400824950300b040d100003200401580415074840184095a0040e9a03000d0032406140f02c86c421640d4030342840c64100000c00000309440c1d0070490003000b0040e48140000c500b46483c591007103d61082d00b080c0c0c805840e4018460101201000c60f003004182134001d100003a1442c015481035020002e0845003803072080d0a42c0e400700e0854030300180081117541e09410440d00035004844003d01180b2040403a5801c21090400d40b4403e0f440240186a079110441e07003210a0048100f000243c2d020f01e0b6941c030b100e4176041c0084c18034420041c008204001900f001c01c0110f40083c0c1c00740107403170703d0a070040c4113540001c8204c8000b0210a400d80688a5052004890a01c95503000d01c10718100c0c1c0c046410346c10750040052100e1142010000b072071540305c1040001507072402e19000049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 440307769 1250 440306519 440306543
    0x606060809100b0402070807060506030607110d050c07030f03091403061009020c070b0d0c03110c0616050c0709020315030d05090f011101060803090108070c05070b070503070515070f0c 81
    0x102d508286501007001d00094180082a540c80c4540e400000b001c8a0701c035141c1c01000b03103904080250340d510601e10310f404540c1c01142c280068440d4590f10580b030030000f00007600b0010b640308001400045503c1007000c0c000010318200105240039500560501c0a000040d2600310710340000c403240a403030b10200e041002803510085500941c454103a03200c0c58081c0a900141d1082c03410003030550200e60341e401092840b04480c0080450300c401c4100d0400a00502050000800010354664840891084000385c14200348080e9054003d22040031700da032107045c50205182402d50043c50041503112418102c09640c10101612100030000380800a1400e0000ca0034a251865002d04642018184400601c441c080e001e42900d516402c410b00e40c1e800000c0250b55540d111a030b40d540314009250022044000ba5201501e03094548200090a400451120103214060003250042a800b00440f1420b124500225001001c201e0740d400214038403044802d1014002c8660014040d8805000c00103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 440309019 1250 440307769 440307793
    0x603061d07120e0c041107170a020f03030907151b110402130b03011d010e0411010509090a051503010c0203030a050403140c060f0a06030f03030522030c0606060809 72
    0x80c0d040018088420080d1009001c60214039a2007a140b600118001030303e40e0100e00800d101c1503038140071001034860700070484040800c0454600a03045000c1c0750013542e60b0406010200e290000e0f204844a4500000040c8201004001019003c80b2402100221150305a40e0306035800390303900444058020182c1e030501c2c0003c1001d00a903111420080006041203c1e444004140e1400c81e0003d2050460000043c8043d062090000c040d410152950440b19810248100e40001000c0c0008040085e1050525940e0b03010f00b0a45031004009040c0c03231214540a04510080d0170140c0740701d4031565001840000506040c000c0c07800d040b040e03400462464072208c40f001c0050500400035820484030305619a0504030314001405000d4400c0024516410b04282010252201410741100c49150540400c0090315843c0e48107005501400d0008903950355688940741d8241599005842c20b011012600c1090b41018008003a80d0041004021198440401b901c3c80e00d800d440031445907125101c1181c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 440310269 1250 440309019 440309069
    0x1a0402030c0901200d090812070f03030e0120071211031e19050307180e040b0711030408030717090f060a0212030c0409151401050c010603020603010905040b01060306 73
    0xa901d01084410100c8001010000c0d401c0c609100c445c4030000c1d80008040252000c104a0040b140122001d420300c0e01d0426075840c09854040c1d00c000b002d250310b80d03800415609081d03000007a1184444c085120f0310f1541494010790740e1000c1011108003c021b4841c1600901c190380c00c0e03207104054030045282c0086c07040412841181001d800d660399404003d003502c600084214040120010b4031469100e0802a4002e480050740b8480d03001c618044c2c001c10480d0381d0ba5021342a81103a00181c4400913519403903030480d440b1805140c80ca5691000090004100350004010454607004040665086400c81d07544a1140700d00860b046e400a60005480a0384c507200c0001c3c5002500c0d401142e07109004a1f4406106030001c4502c8a0f2000000c202004070803d540901629034070314140008000d41001041100e181c44007640e0350402001148681c2003580c250301c1200555001000e6544a6039103c010a001c0e26080b01d0486071720340c0c01000051418002e000320001e0702e2208003903d44111500d07942c05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 440311519 1250 440310269 440310287
    0x13050103110f12100c09061803080a020a1b0f0e040507030305280e15070c0b0d060503010906060617040b06011b02041802010810060503060d0c03151a0402030c0901 72
    0x103a40f20503071001070403840004015615229007086808904400c54401c0600400c01aa00000c140002540d41942d0080a2948182540d500040140c0c40314142c0d40704a00c4c146806100804183c031180440301031040702d0703880d03600301da503c40e00020712039441c0d0246810407001918018059804402d052000070301800183c203100311628030403103800d01c24003c13100181c41c1e0324242d07002185482542e144c05041160401d0820200640305610f4660240d0307a14684042912890550f01da002c182d10b203071800150001d40040c4002030003840303006183e040c05801062140718076030102d0301000c0a0300e000d58403004035511440d0090318824095440000550f0890701c0d9401c0c00900100e94070f00d030401a92244a800010300e1602d9030312503030030541d200142c0300320310103003441e039a644004d0b0f4104890b640c000110781c0e01c0071064518401c401c000e4900200e07640d030303540c000406001c40b40c000c0d0002c041c00c0ba070000440c8850241c85102501d151000c0c4070491006941d403e500200c10040c4100d5540208401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 440312769 1250 440311519 440311549
    0x21e03070c0807110414040f02150d0f0e010c020d080f071713120306080c120a0b0c1309061802070f0b01180506090105030304050d08041a091305010311 67
    0x780394200d030300c2e03078070500036900014040710340b00c03024413078542d81e410248030302d2640c60200c86c3c11040070308040e107030307010a00043c4100074444c6c0c0100700400d522110707440980e0007580103400140035400c508010f5001602c50507003c211a036183c4882000c15034400214848500b40d6034440c010035032150b8242c100040340041090092000c01c502a80b41070040c054003d22400e25040c10140c8802207280c102c11001030403031404101400c0000502030072001080030780c0340700303070880ba088880008607221b942040180c1c44040c0c01103a90300108544145004010a140340407103d404003681e4a81e80ea4a040307a480b4003a14011034400b03410031440001c02e42c01806518020390a00e45c01403034135910221702940036000800045203080c1d03000fa21040742d01440f90808c000302e417591059030501020070341d00e004600c1910310a00410030002c040c004c1c80e80803a409000c005002d052030203241880800c803907202c440c0c41d40c00382942011300e02a11245214850507254080c0300d10208140100804c01c01602e0b000fa9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 440314019 1250 440312769 440312777
    0x90c0909010b0d0b030d0914090f0115120501090c0f080405070e0408160309090b0f281a0909070e0d02040e0c04062d08030304020108100b0d050109050901021e0307 72
    0x1402c08143e41c101b001c059051002e40d601c00c0c41505002001c0850020840c80902034224441401180f0000086e458152040b00300c0a00844400358011070310250143c10000d0708620f00320002c290b40d0240d4010320a05c0449445181e03400301a403200b220644400c80b005407460304404010701409040d07540042d0443c1c09092a81e0030500c1d48551580c00006035641140840d00100040042012030301801241074000c07283c0901d9018404040382d528004069140180e0011304180400500d001207041c1c00f4106c003444011355000c001106050603400311048501c51050340e00040e00c1c0c0707482a1000c8100c110080c03d00400448140d0901024040188004915003d12680030b4155116032250600070242e034080c80b000700d20298982031b41b00041d803c1d00520003090901c148900c21000003141d4102d40c0c2071803c40803079980c0c0418040740d00803d4210110240c00000c0582c00c624050b0085416982548010040c03501c45009143c01c1f8882d501c080c4840c0000c0301c0f68506c041160b8409542d2015031824 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 440315269 1250 440314019 440314031
    0x30d11040e0a05060901081203130602041809061a030d0806120f01060f0e06010906080405010204030f060b040b10090603021308120c010e0d120506031f0209090c0909010b0d 76
    0x400c801c120104071802c50020b6522400c010092411126040c0100503550103071090104040d07a0099a100041000c8a035062954080b4100b200d154100c60040140801c0e480b500101d4000210180c2403d503400c1c0c2d252800c2c2000510300d002520041c003041c4400070001c01d6030041200080c1c0e181070004244544c4940a06252160381000703110407100600c0d2000000380d07860409501d00000052500a001d101c4c009004000f05660800b400c01d040e950103041501c999030312441d181e4003a21450700001e005802000c0038030100940c0d90050b0300651012501480160303484414024040403070b03000d040020741c01c07400c01c1029502a5004202c1d505405c070301d218146031110726413441d02140c000014416000058881188903081c4240070b01d02c00454060318400c840060021b100d50780038000000704542d504041200340e9400c2045500c0a02040300607104e40c0c0c141a11325009400080b640342c05590b03243c00040298031240129180c0c048000d111401ca80d00342824540700b604141100800959100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 440316519 1250 440315269 440315279
    0xa0b07090b12180115170304030507121b060c14060f1f05040504080c070603020903070510021c0e0406050d2001140c03030115030b0307090b0a1a03040314030405030d1104 75
    0x801080b2019170b161005000c03003403400c0c40c0070541c0040e100020400780c2051000b800041d00118144045030708070103051802080b00d05010650f03200d80c03000451414044c0a0001e0807940020491004900950780c517130000c0c00c2c0c0f207951901c558046501e42e014410180c0060250500300311245c0101c900d00171184c0c04c007500c1ea4041000c5410580b0240c82c060004103030016102d80411010700a010b00b403500754100a603190119039140300038002c080c0f29054a0f110058154801c00c04041541d03804c516103030754452031201c00b030048181314060601860520b027001c940ba0a05000d084501030b0311200c83c80341c41602d0504444090307000304426040107400b1241141142d58032000c0e0020400180140d9074039450a090003516801c40d2182109141c240b01031804aa50003040620468030303d4400130810550a000049810b20603801400303081b4000252204441c1000c2c002c0e511581c4240c640041001501920440d41c3c001120014280e90040140d1010241c0c01c0e000303c81c040080501490529031070b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 440317769 1250 440316519 440316521
    0xa0906031d0303090105060f0a031205070303021c092303090609030a020a0e0603011515110705060a212009010207170102070b0114010f031d07080a0b07090b121801 72
    0xd0321444c40d01d0391586c3c01e005191412440d8401e860388100d60040110b031035956107841d00d02d14450300304140f05d0041101401d00d802074040395000c3c072484000303070660704184000d034000f04401441511000180a14441500865903100b07590755251402141054080400c200c6241c0c0100d40c080e4050140204420040c5c43d80704071500503007100c200c200c40310301d441d200381405c5988507031520503110400c0d4130410070606144120145020149481d10035004034071485071900c10154081030300400002100d2008a9000d41080d12800e87c40401841c1c00264210f42015210350b551000414240b41200d5902c044680000704850038040c01a60000c43c3d4851880e4812003030802c6181c1345940014a8000b00706001c0d107401e001d040003015204000811400080a89c401140e00e0704c18559144540c03000b6221080ca82d0840c18029804c41c0c90650b2110305141d241c10006a08a603160212000304803d5401080c0341010ba43c9607203106c1d802c0c81104101d414000601400c18401c8070b05514210400c041c003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 440319019 1250 440317769 440317771
    0x20f2b05010b03041a0402060306010c21050a020111041a0a020a060204090e01051b0a050a030905060928030c020108040f020a14030c040b030307030c0c080604030e0a0b0a0906031d0303 81
    0x310b0300030603140e241c1810071981c0006041da1840303000c910a8100300c016640c55080c1c0760041400c3c03074041c41b1000185018400d100d2030100c0700100d403102c02903584903241d11200420411400358001c9c050841510410402402a8042c0101c2c407603014801d00d0f0010390b200080d020030300301481214186400d84e01e42008a80c440c2e004401600d461b00c0005541000c00d008040c0c00000340404803e451810380202c1034036006280303648003009030009511f40d01a1007500055621508001582c28908040d1002580c903443d0080d04220351020342c00f408002005960303822000d030781544550456050039401111400001030040b5102e94000320300a000d038030364950040203420b0f05a0034599280f502020945000e022622140c1300350b04041d1034401545000c8251548281d05040041a603a550b1a03c10450901500324210745c1c0304041c104800d05030301c00c1207030650381c03402d448a880907034482e4940340c95031062400d01004150083d10410200303101c0d910942c1400e10700c42c000e041602c90300d0082815640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 440320269 1250 440319019 440319029
    0x603030f0a020304150e090f1005152116080712090f060e010b0d20060c0606010f050702031f060902180f09040b070c17030a05070e0301020f2b0501 65
    0x88041420310410069540d034030b0031a015420300135004156036000a1111030020010144e03c888400403900c0100c27090700e102d0190400411544030451007010340203454208402d80d65407820954495440644149151806240000201c0c0c0c048168004213464420010b0700039420000502186d5600e08124451684120b120f6884010350104a0508200b03803820a84804000d034034102284443d552190200c410703a0394030204d000110382e1484201060903d0010185401400002c2c202e007101602203803043c80742d0350980318110a41d005880469250007000340094060703105007100c51f50780074614011025180310007400706001c2d8540c2c000c00166084a03010301d90300e1104030852105072911300141e8881c50002d6401c00d03020b1a15480d1150307000c1c0f0240c54074040c0a400800c1c1e1003400000300a0714510010241142e66030b040a950003001841e0807241000014212044a42c03980b4060013210205c104c074402d12402d000703403000c0b1180c01c425000f9101c0700500024a4100000101d03000d1103000f08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 440321519 1250 440320269 440320273
    0x203090c0a1203080c0301150c0501240801140411120109020604080f011103100b07030e091e09010b030c0f06042612042403140f180601030210080603030f0a02 70
    0xc0705464080e045a902034641715808609000500507144410992082440f00703107020340c1c085005060140c010b0021041c07270700200280c400c20001200300c1850290441d02003100801c811807041aa00441c52000d41303000389074140700b810815080c80d221001c00189140d520001402141c194001055680141c1c031a01701500000345411107010b0a200c0d42c42c1103002c0c188070700d14518080031480060344140c01412213124001c41d00d5014944900c01c8a1408100646500c08605083e124950202c1400c12001c404108440000b0565101030190b0100844050010070f0803907a2b400820040b090020303a0190056403c1c00006510400424904203521405460b0741c0301485500d1100c0c240111354900550345002004100702522a40844050303289025035515030f00052044114041c1c002243c41c03ca2a1427410248a14064081c5a60380510241d0078030680d019202a00b003522402d007480041c2d0300c03114452007011203030f0141d5680c5601040c0241564a031204200c46440541c22800000c0016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 440322769 1250 440321519 440321549
    0x212090c040c020a0b0403260a0213141f030902090f090606010804080403030e0f0d1a0a0b15030402060c030a09051305040519060f0204230a0303050403060203090c0a 73
    0x5400c042c400c800804045101030600210591100c058140c00034100804104403910317059891441e03001e07141c580b00c450410f44499403c1440400300a5000032581c0700d810340081c2c00c00200309280300c0e00803040d0075003c0c010902a01d41d8034031a0391000a03910400042c144c882070080e0042c1d40d6540460710415201c4505d81076410310b1804949007540042019052001040901002c2400e81003910201c03649403810390001c1c41c1101c0404e90491070f035072034140c00441c0400d01208201e04c1e9100d14007865a603852404880d40d50f0112407056910b540240d80d000800100401d1140030a44000c691060001d845645009942c4050a10b0f5901105e900400101e5a503000d00643c94601301007000400010010300c220300f030984607513032250282c40180304020a088c1c0c456040200c5a00642c02000e42501d04649440e961552002218502120409070f98111048003400d4901303407003d842940c0d0959103540c24070307040d5a1118000d510140840700240f003104413079211980c3e45030b51000034017241b807048109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 440324019 1250 440322769 440322793
    0x1020106170c01030b2701032105340302240c04170c060f03190203240d05030406110606042307090306020403080d1b02060c07080c01020301240201090305070213021209 74
    0x814095278030000210007410040c180d0960100a4410822220151560b4a101107251501d4012122041c0e940c90700c0c10503182092603000b103220b0100c1e5610007042c0100c510a100101403031401290081d1040500780028850312030403c01072502000300c001242c402d588260005081600420124590007000208101520030201c0204500340d07140341c0b040d4194103080004101c401c40f02c0e010480104102e45000c071040da10340c1481d103003003500b00096aa8803a26030302d009002ca410007200740302d14490030000c18040e0826104410100740d0f20300c0d1452071580e20b0b600103071201501802660410044803c003201241091008000440c07140c10801c0c0c0d00c3d9100d050203415030b0544500380c2c0c0b050294460b18070101c0d03004601e071940216020b14075035840c161403401d806140075849400340f00358404000440e445420002081105d41c80f01040101c9034100c01d022400d9600700400200068402e2010000504000030352403006000304802500704a400221803200100448084001d42d00840c06420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 440325269 1250 440324019 440324033
    0x40503030301090c020f1218060d0515040c090815060d050102130905010e0613051f0e01030b1f0605031005030f0d080c090607020f0f09040506010501020106170c01030b270103 77
    0x614840210301030301039000181c07021141ca00411448c05001224041411200d40d5114202c0301d28081c135040820081c10704c40050740d503009002c0c0815001d1803408000080c814003541080084400540061070b18a60080c0c034110f1100c0d01030000d580155901750380600103002800079000000f010009800d10314500340c0c0b074205940c010703030011049406e6003080c0a00350710b6600780b010300000007000200b9607440701d0028010f081d65801652408000d0388101117400690314200b141280d000c0c4000d0042515507150743d01184020360341243e1258803c05040207641d0140001e5075020f80c0342d5608044440d81d802c046410100e0800a026060b000000b82205031030b00481c44d241c01400d10002d0f0303403c0403480703000b0590310300c143d0314080e1240f0383c14095000300b03580b14200000080809070508546040520b0001c0c1c0d074034070a001d030b0f42c095401c118001c46d655680e032400c01081072814000b0450700c0d20600c0190010005035006a4003e0b100001c14808104000c0c07100b54014500301034003007203615600f0700c0c4d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 440326519 1250 440325269 440325283
    0x2d1a0307030b1f11030d0603150e0114040f050a0204020c010219030209060403060510080d0c0302150f1501200c0a05040216030503370c02150a0c020102040503030301090c02 76
    0x7403260f0000e082210f031409002104480120550400059801c1312034405861030050080d200010303401c21102204220b400c41c140503619503641801d10203801c88001c080d081c0c40c42511200041042c401c00200418401019030b404140114280c0f80028402e0700403c01707a87c401005924241e40010307070032503180020f41c80562410850b04d81103081a809600140040c0700310f00c000303400c29841c0c0c0b001c14208001c4440c94001072602300102e612410902c04058020300240d141079000d1b014100d100e80c01e000c10b81c1c0c4241d124400401c51310000f80d076402640c8074881c4004203141c1c10072520540000a0404421140c03d41c1e021440050994150000170010344802c1e0350000350046005201c0d0120008080b00c41d07010aa915007801502c9540f5084400d040025031450015500c58241440d51040d50a201c110002180007000b882040010602aa61901c091160340c1d0f0b07192490000030f94403010b9501c00782c6403010713a10003d0716240c1d403071000030318640080e08a01c1d091540c48543d0685140c04114031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 440327769 1250 440326519 440326541
    0xa0e01020d09030201020319030e010905010b0108150d020607060b0d0c14040213061407080f041701020705070b180915030706180902130e0a0615092d1a030703 70
    0xb50760310b0706550001f912030040b0180c410702241a070f8041c000241c0030b6041070041c410400020040e100c028101503010341070107000240803481c401d000c01c03104403400540c13004920024000c251151550390a01c20300740c0c4020f03019078644c4d58680300c00703180707646881180c2e840038019400620828105030031407040000c0c81d90400c0c851403042102c1c00003120010020021103959003070801d0f1040c0d0400c00c0a6881c440c0ca03400070004240021502094101d040203001a100c1c81074000505a0f00e08a03400e080388a101c3d4090115400410100b01c810100001441c0d800185103102441158500108200d0a019901201003000103050a40746003010415003004100ca4581509030a000d00151560400103024503840c0b50340000d404649031800380044001031080480000003854910213240041407140615880700c0c0142d030302950641e105118140c240d401c030300010004221801d890728102c949002c001440724402c0840000c3c000822202d8002500c0001582940e0f481c1440c17009080396817540f02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 440329019 1250 440327769 440327777
    0x9050718050906030a0c0f0e06010302040302130b01030204050301020a02010504060c0507030c1403071a0403090503120a05030612030705240124091e0311040b060f070807080a0e01020d 81
    0xa11a9400c81040d51902150401d0300e440c80c40d074071440702007801d042c016100909400510000041c00c010884030580c100c071044074080000f41c48400044050380710301e100182d8090a2502e214031000309a50204000341014100146030564800120f401d9030007180a000150b59a201000103000480c020880c0c120702c0c5141091a204107561701610542c1c0318a40584603040d050014180754000f00304070f82a80790040c440c0a140c1d42c01c331004a040110850b42140041c42c16040000c5500340094100900c1000e000750600b00f070041070003203e154000500081d8040300454000990103400c0c0010030030340f070051019280f1003500384c482c11212418903200a20000d01e83d00100300310241020703005042c400207004a64a1010300700704480308421500140865440142d41d0541021068540750450f4890f802d010411280301701048100c03480c0304440c0350801010030203203044041c464014502c0600c9440030317034140f45e107a0701c07400c90075080000104003003580030500b8016580c040018004101213450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 440330269 1250 440329019 440329037
    0x20702010314100605071403130311180601030b0a030209010b0909010b0309030306010e01020a020a06020d110606030a0210020f060c03010905010e1302061e0319140c190504030f0c090507 82
    0x140d1280f9440b040c401c3d00700f00407010401c0020802401c0e011100c0d41452012a5140d40582d10190540a440e00c4101c90350010324220801c1400c206003e80d0040c01c00c0003884642c0e44d41e0000640181050308103007a44010b8201e4048010b940d2444814003820a191034141c40d0007000040c030444480c180c0000100403010300400c076841d0000001c49a00c14001c0c60b00f5400c80c01e0400c0140e01d882c54100009500000040380440c2203a40000d14104058503a50f800e0340c1e540c254458980c813140d0941340c4503010f40000704014003600784140742c40703800360482c41100c1c0b588410034100d6080041c1a28025480d070400001044010024000c1c1030151041641001640c18001c03c41010740b408500000d0140340c002c039450021304d108102c0d8030710071016040c00790354070300d880741d0003202500010b150071010034a0003180a44681070081a14442c6110300807440c50a602c2d5444589000100990501003040070440880066050610b00c24000e03c0f030010890307041d0078200100c054400c006d20f80820481880 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 440331519 1250 440330269 440330281
    0x903160f0302011b02100c0516030b04110303071202030703020c0a3c09020c06130203060a09150f0e070e1005091803120403020c010c03120f0e070801020702010314 72
    0x514542165824244481e13114a078800301c44810908160180d030001c0c04120f00a03155070031200307815404e441101035072070302c6020400628201d0254080517014aa142d000107001410700c0000d038a004070010100c0781804003a980c0c0510b00207000e510710005800c0481c40d0800c00d0780403c00c1400c10281113a10f00b144500b0202c072120000ea40d801c3d0701104640c20040700c14081c81a0301c02e86412080304d0b501007400e50300c03000400b0103541b000201d0700b810b103d41d00002e065141d0000c2d4805031241d00401a02080c0c9461035080b020349422441954504802071a0001c4001d0382c0c4140040e0b05e00032040410240c55250641e8100080b507440748138201010710410070340010386102d01041d200103e03032000c85d039124034000000d841001c5015118078400002c44401041d02d9003809485103209a01300c1e030454003000c00440700003903602d0004000c54010035020580304641e410402c14401888000621790481445041c90f200007984084800d03540040d18000b0342d40d05004213150a002c0000d1304442d42018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 440332769 1250 440331519 440331539
    0x120d020a141c0e120d02150f0403091a09030d091d07090b0f0d05070804050708150403030c1b060609180c050609010c060911120613170d060b090316 65
    0x20b07000d03030100004220021099a90000b40c0196011032074101d078104046900041d55450101402d419012130007000601c4100da0b5a460520855050b90342c0300300c3d140781401c0c8415250340c5003445000da5006116070100780d10100000e00e05d80066a40b0441c007140b0f0609005035500340601c10103141107450082205080d00005000b0032250b00b000d90b40c0c0d441c0d0211031540c0e014000c0c071040540c2241800140302020780e0002c24a4062030043d01681c544a544841c0e4958540001d902c020240c200ca44c00500464029404100d22520310305041651540d40150810121005402281e0787c1e40d40301028440603c0900c904401c08000403c45141e0540944403801040050300c00c50b80300308030004d4441e12a074402c8240c684540c0d405401030000c011309140541c4000481c1040ca40903c0d107298003c0c60342c001c00110a40100c02d080307403c000481e1945c0f2034440c01c8080d15201d51380003c0810031003000500d02d106000051100d100000d803503991000805040110000d00400f0346040154103000010314 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 440334019 1250 440332769 440332813
    0xa09081009031d011d04110d09290a0f2d0b010e010503190b030609030702040b0901030803180f0d031401080604150c021009260408030711120d020a14 66
    0x1803500450030b0394000040150100e02607a501c0e01e180460079840401292700104c15491040740c1081500004101c0000c2c08511074002086031861400401c0003040d07150302c00030800d0b01500d00410f80da2117201040340d01660302c446003100300d0a0307031a800d9070b10a0984200f0f103050000746408414040c41c000028502c7c00081c0400000c20030804002980a940398010704103000042d0070740d4028500152004d489420102c82680a06e0512070385145074600042124181da0b4030289003811a129585c00c1e000003041c1103c14104d5214410414070400003c000d0304c880c01e00e2a40e00402d03580c0400002c05030b00303039040e07000790200da0103a8140000034a0f0800c1d005c1c1251014080010801c0c00454124500310507207080c01c04a42c50b148112062182040c50300c1c0c01c00007032401c0807007250030980441805224602c200a102e070018040036000402070031200c1d016483c010407080750401a130703503428108034001c030007800960710a90403030741040440701e403040d006d09001c0e01070001d040540d01d1208003044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 440335269 1250 440334019 440334047
    0x9061204061b0203220503010518060f0105061b0c19050a050402090f011b0c0314060f07091406090a0806040b07050f0a0f050d111b0106030210050a09081009031d01 72
    0x503c80b00f072170600c130030b048500b10040c0001002481607040684100007044140140741503107004420000e0000401da0007854100d520107801e480c50303c0e82502c0c2d5945010714458031141140100f291095840d615201a80c039042070460217502c0e1145400c080080202151b03000d41d0041c1d0040c8a50141da644014081100f81c07001c0c2845684a6010511402c0c0b079400d0400007056109000800b101b0b101d481121107017030103040700850703905407601c0442c098803035001c0301da060001d00709020500c1116010f0b4440d600c60807010b000c05041449a0b0f0018018a60070317008800b0650100c0100014440a64101600902c003400c150385004915180c86c0340902c154502841407001e1021044c8645d88074504891040712448420498440006004030307581d0312000180c00407030002d01d4050071120381803041804403940203000d0200066150016900c5030090b4502c04240110344500094040040c07046e0700e0614142c1c10006900c0c48903103030217000d4001104a01569a00c070a00c03100c116600f02b00e40c103000386 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 440336519 1250 440335269 440335297
    0x20a06030203130c080307110f090103080d1d0c01030b0117150a0b03041a010b040f090f0e03130503071202030c040b040b0a170705041b08040809061204061b0203 71
    0x107a58061000c00b443c40042e00285018910308000a8840d800300242c90418401c01c3c402c4a0301c03840c0410081d80c07441c044c003210b9001d0340390801040091035000040590f03900318003001c50002402a01d03000400104503a410a9070000c0c10038a09030b6905200360700c03c2303d9003400c5c04240d11980454000c0c01000090460400140c400754800700e035a191821300c4020062031400b80d6603880d0519010081e0740d02c030341450101410000000c544403419000342c8069070034056441c81d050f460490030700c015150a12802d400203545d44420044242c0620003000b4152070351401c2065140780c481070601d0080f0303507071243c0070500d000b44a01c0016600415003448040041320041181284000001c00520480301d8140e40301c426a0760010301c06c915400284460a401000e8440042d85c0304240400d07201005018110300c0603c03451050014022030600703420030302032603213581411240400301d20158030030500340101c085940200010011603002d44030046031015030150104800c80340281d0f6074080e1f031580a10f05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 440337769 1250 440336519 440336521
    0x906010f030f1506030602190302030601142127011e020703120216060b042703020c1e0f01020106060212091203030711060f0709060f020f1c021504020a06030203 71
    0x803150103e1500f07404400700c1d4003000034aa80346002c000a5100c3c41d480442d0400025003400410b00074400d69100b214181c4500005001018813603519034800000d5140c4210503e007001aa2020040654880c3e084051380030b90310305c48230000c2a01c1c080d40c2500380195030304100c180014842d4400f07805c02c03450384503040583c494601e0b1405a446042021401d41c41e00e20115103c88440120000f800311203028076020011074a2442c2480140c401200310080f0140028004c14112081c200102c88524001e10540e80b0001402000030700071507c450100c078000028580c0103074245040e1211180d8075509000030011a4600a40a5126051030740c0c1d50040e1500481c000015444420f2255210402042540e5803072801c1200036000c000b03c1d92020760a84115000940035840300d5481901030815501c880504600e4070070200d554481c400a09400c41c041c00c10b158200e0f810411940c107071003160041890751050f00d000001d20708401d4240300c1a44400400c103210150310f4000740340d81590b4a515015a403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 440339019 1250 440337769 440337773
    0x1f020c0327012a08090a03060c03050a0e0c011709030417062205070e060d150c020c220c0c0f05011a0f01200c04060b0408060906010f030f 61
    0x2540a2082031200c003a90040210301510202203101028400c2600d41c07641c280302080721640c2030305403019000d0003d070001c1811404144004080e001c46140201040c01094803552041b094549042c109404240c0f0b0b0414000c014100340034542c02501410003d040c140c0c807000009100203202d4010700040c49007940407440f03600050044501502006e8400001d046540950707580c0c50108488a41085054590342000c10300b08150600006400500a151850506088044030380e0f01030422640700d0400b05100d0002070100792164561b001c0241c0000c0d00307207040315003e0b00f080c502a00081c411105440a003200341e01d91008081e80c40d100280001d41010300740c0060381e052110000142c801681e9419600800005402c00d6010100c20700b48000c414072600f00f8070540d01142c2031000d01045006598525522800c0c0d000355449103071804844000d010580031804a420300e07040038204500014040c00019410044c0c1600705421100a0406615004c01061495514000180950090082401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 440340269 1250 440339019 440339023
    0xc030206040909053c120f030108010b03030f0a0822080703081510030513081c2d0203062404080f03031003230115050f120706031d030a03020a0206091f020c 69
    0x1101b401c40060680d4032a000c400019994109200e04480d941c03c007190700b282c504008c8262044900007690060034201141010b58003404000c1003650701c0403440300e09010703501801140c0710440d030140342615501c015504000308084002030241c114040135100303024182c0c0300c0c141c8249650906250018880c5c80d4000300b444262410900074100da1404603004076194804408010003840c1031038100074803000f9902c03070040042072490307214503911814003072001c01c0202d8000b10380c8020300404500c2420340040040b40c1807040000400c58940001c03800b0b0020500421550030700f84101030045040d4506480010001c004502005000451440714040b080a4005e540c442e060302c0c0100030301001411009164140e200ba00c680d500c1040e5810362038845050102d00c441d00c009030000074286c0a4240300054000c5d142c82040100d880f0b1400210180c0a4024000b91604072003590b409a518080c0c4400245408000362485030b080d040312345000800ca02c40d42441c811401003000c0543c0328180d19004038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 440341519 1250 440340269 440340283
    0x9230c0f0c0609070e1005090103080307020a05010615030609051504021e0a03051603050403080609070909060305030d060522050a0b09090c10050a1b0c030206040909053c 75
    0x3644034400c00c0140a45003030f0105035002511070003406042103580e080401314510b00380340b040c42e400908600051001c46c24100045030b0111090040741c035403a101c0d54409084451680c007c42c80d041e0060700c2001650303454000e00005024005080c0701c682089242c40f29160807241300240b00c1d41c0d0025051401022000003142240e0601840c96103c0d6006680a40075000460700080c001303050a0410015138003034450030b4000d9806a644007243d541e01f03818041c8102001c0c1010f800c1c44030041001810740d8541c080c2502962140b40659100c0070018520f00955605400551103485a41034041a40010b8100840206604580410780d03840d0446520000c100d495070560300949207c0c10009000c1000405000318a000d0700c2c030203074829055000700c1d480c1c0101040007001a01030340d4600b40d80d43c00c01c003c070321031907014100c0707080055920740c00116294020f83c0300646441c0c5548040d4140001405107415111617044000d10007034100c1a42203c540b484241c0d050030507200100e0100f1440d00300859 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 440342769 1250 440341519 440341537
    0xe03070c034220030703050a0903050703080601020f0703050708060a06061b0c0509040f03080a05160c06021b0706110c010f050d0912030920010917030f0d0609230c0f 73
    0x40350300c4801212803600f9540c421a21000420b050401284a0000701d10405c0e9036140c05070348032070038a02507513401c0300e00010140c00b050440c404c01d035207a01d0400d03091100744011881800180705962a01030358609000340200f901040e01d00d8039404019168110f00706003142c11350f42030340001c050a9460301655840042d0070554001d000794040004000d050205200c0c40c5002c0d1300e529155964a12801d4160f40c4101c0761040d4402c6150300e00d0180130701808401040030320030039001d070414619150078203c0001409000e2403541c40840c0802c030040c0c004031042008848080540315035940c620019100c000a03500c0003042190000701501c0141c420b60000d01070a40c06a5107000b44194410700070050009142e00740c68403140b1071601c00c12290065040d030074001041c2c4034015070700e1414140c00031702c0141e400182040d010401c00c036800c0e12525001800030303414043c000a6140d0804480404a9150f240c1c1c0030f4050040d6611040050f2a10030055800405050071301c3d5036130040840c103c45800740e2160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 440344019 1250 440342769 440342801
    0x6081909120302030109140115030903030207060c080f10030506060d080c0706021e07080604080708190c060f0c230d02030f0105090c04030f0807060e03070c0342 71
    0x60040001d500d0f8005504030390101c1410f1081881441c40c20a00000078494001c2c140c202812000042c1d000780c02c1002e00318007904005040c8081d5440b1041940c02d1541c8400006540c2c0c010420b2801c84413020315080f54a42c1c10042110742141d03105940d42c10040c00701c0d88505044107a1108019415040742c1544007500b0a0f9114180c3d9664080d640f40c481c050300c406103000c1080c020002c1103000602e4801c07901558018074803038071541c03510082e0350301000e002e0b98015410000d00e600041c81000400103041c495441142d204031034103140084540b040510850a81001038100b80241d0150815090f01c3d51440c0c440c8410171940310900e124401c01907a0f052960000c01088000a190080641213400c1500c49402c20760320429522100d20071404001c2054000d08100c0c00480c200c0c174086e00c0070798411500083c218900c41c041900c0e64114480449880d011544103108101070302418000315252031010002908200500c1000d0807000a05402c0da51104c0405000440b015004008140d48840e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 440345269 1250 440344019 440344043
    0x815130b040228080105011d06040b0609100f021c0e011206090608060907090506130203100518070f090b09010c06020d0e0304030309050a0b090603040302100e010b010e060406081909 80
    0xc03040c0070500c0c60700c190340031307540303408000100c103814600c89070a903203000145180c1583d1000101f00041c0a081681a0010018442c540480c1c80c0c2c035145580040c0951200f0410300c07c402d000900e050461841d01e0710004442c0d8845401c0754016640d40211503090800440105a10b549000207004592141200e203083c0b10380003c600901041a0b8069010b04040e24505503e0b103160300140c4505403280c9801c1040725103001040282070f4007964001c1c01820008a950b0790350000604050392221b80178080b125240b013440441d036000b05440d00c0710303460b40c1040c1c0307241403910625002074002c400c0ca0606100d0019106810410140c5c1201c91019485c0c0c0c04001e120705d00d41c603140d6070b504a4003044000c2000000040b5681c64030148141c201d074003250034949400c8141040c03101c0364201400c114158484c888102076154100d010f80307522504081c1c000503110100500040c50b248142104500035242007100380107103544460059440002002c42142400c0ac50155400901e4000000b80140001c99 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 440346519 1250 440345269 440345329
    0x20f04270513030216030b0c0304030e10200c0a1214070b070b0c0408070506070f0f110f010809060a05060315091615090504050a0915060815130b0402 66
    0x100b9180b07580c0213600310b610341246039000038140c00342804050640454900001c0c0181c00b07140080d907109219103492a11880e075040400c0c2145840c0c82c0d61700100d84040ba00d400300d0541d12450300e07408240c6c1d400801c4510030381c8000c195004014003464400004e1100c0300401e00078001c10200c403001c10b6404540c41c29035196008455074115142c1124180d081001245008003160107990903101424094070f5024644420440907070701c41e8400700c0300003580c080c9050104112203500307000c1c00c0c0542d0100f28510403000801a40710072042446060024a0050051122001511582c446e4240b10006030036111800000d1501848040700802800f440041004030301012032401022561402000b1f09581c4a06003401800500550440001c1901400300114546a003001c0cdd00040d040f034000410210a4032280340401030580444207240d01c4000810a00101b04102c40d04107400220341c2c40c041c101034000001820340c03400082c0412511002040540d075800c040c5801e1000044401d00f101c007200c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 440347769 1250 440346519 440346541
    0xf0d020f0d080310060f080f0112020d06140a15060207050906030726010605010c051c0509150423010c1103071502010c0e030c0a0603410a020f042705 66
    0x80c0205c200007400e0100800c400c50207810214041e8400307408110003682000c0b0081c0059444401c2a40d000050403154800301b022403081400d855001d1031000054941080900203640003000040c100c60011142000200d6020640d401034403c101d41c80301045d112140024a4468a50003080741e03105020300101d2221740000780e07440f030400020b00a103d0701d0354030401510f401c2d01b1440085c080390005200600032602035404110300c80c940c0e0070400d003060042c101140d03241d503080e14151040a0700241c24011000c0020702d15514214802c10f270000b03041c1c40350008000c5815218020704042d90510400d07600c0c1c0d01031008401914020b11280c55582c84510024043c00008074903401060068110501c5420b022411401120026081042551500c2c41c210300800c6001c04504035014580700d03807414403034442c8080e06c0280c0781a6500f81c040144825407a650800500b800318074901c10440c1885948210007a1400c0394031034840141c1c0b40341103c9500c6811000050000c040b10700e40f00c2048454992 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 440349019 1250 440347769 440347801
    0x6080a1401050f060603040606031b1e06020c0114070203031810020109031d01030908030f040c060203070c050618150c0d020f03030f0711010c0504060e0f0d020f0d0803 74
    0x40c11140d400340d44204045003210000e03504510325900d041c00080035420800300031a08544102c00004086550351610140000d03403000d090a1150008030801170301d500750308440c0d001c0b4401c20160385d4240c40e00078040d40c0c03500b40602c0380341440388403510340c550050010192060a900075069035a200f2960880030032084032854103034840d06204240083c3d9501c14410725270300c81ea15860b81c0800ca0101d035003c80b4101c4441c1445810142c036103000800003005007000d14007810791801441c100c0c2c1005d10b8012110741241e0040d0f011944203100e00d001003042e90130305c0750450340184da141755070b0003900d41007486458072049825080011841c07850803e0583d070000700300380100c200594551008030310303040782c840c210100c0d038406561082c004100c007a0944500550003007050306060500070b02c0c81d0141802d4a21510754800070500103d0300300241074124685207101a82250000d03000c0c0250b00c000341714000c4403140a402100c40345182c40081c1c07034004800347d03900c1d040700e42a5101d10340f0300c070313007c2207502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 440350269 1250 440349019 440349023
    0x17070806190e01020304170306130207050a0308011d040206030408090904050706021002130e070203190309230a14031303050a1e150209150a08060306240909010f06080a 74
    0xc40c0c4034510b10b1218040c400d490290b584540300040b40d49840e450113020740c00103002c02c2d03844074000102292024851004010341c41c415009001c1c5004981400340038504142c0c00400e40c003c000034121000c00340f60180c242e101d43d040302c0e41500c9445500302070860b030242e084810380200309a0180000c0c00000a40070048075026822907001c107242c1514441a800703296490312541200000500c10001100681c81d4424104e1040b6410700c2002e840328080ba50800c43d00c1404a9a40d1989005014080000e11603c060315180e40551400204543d076458100d44800703040c0c0d81c2d0074151009445810f00c00c844002615080c1c020240382c80e81013094968001160845e000c0150202100b007601509803a4011540c000b00e0220240601c04c7c3c01c0e80103544001e0001c1c0e84001c90700100c2c3d00c2c004584026140d4030300940d80b881d51798a07010040c580703450405402c0c83c0400210724151203628550040170842040240c510f02d24a0315095040c0b40541503186c100203c1e071f4100500403990302000205013010314 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 440351519 1250 440350269 440350271
    0x100c020f010e07080c0f130203010f090c1704030f0e1003140a0507021f020906030f0a052518180b01020706090b0d2c0705130b09011707080619 63
    0x2c601c0c85445070755071403d20885803d0380200c54050740c9842c1c1810300002c840c5002d00340c42c0e14890241240c0c801c9900907000101c00c4400d1b00824403419441d03106e50f14000170306050440c0300e101c5e401c3e0120b86889004000904003c080d503104a029803042141d180c8134039014050007400809014082c025008030b5030040b40c0580284000703018503a00307001d0507004440e19002b07051003a11210b16500c891140d50210450941c0810150b103403a00c0f2040118400d80000c0518011070a280d8150b500383e5401420907e00d280034034402c1d920043d41803107650262207403400d1485008400a588001440640d40880700401e8031846c265a019910f82009102d82001d0342034620301ca44860095945803450300034421000801c1c030440382c410a10f035200c001c81c184008128a0402c81c00c0320781002916000798060003940041c1401c101b01d062150800f041002d0008041c0940156107002c65000e000c1481003602a2030142c031410840c00c3c0c240051f201801000d01035030380e1491312116203030510b9800d80e148001d039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 440352769 1250 440351519 440351531
    0x10f1d0c0103060506041505131202120c010e042705030705010501060903030807050f04030609030e1005040503060f0a09020603090a02030607090308031306020d14180307150c02100c020f01 83
    0x40d0300c40c3c0b0801c4141c0d04014901402c26042007680b403040c055280e082818400100a5040c00d4190403400300010303c2c048044551b04605841885030001d002c004006e1540d1202400300fa26a80017402c1c0607200c9804d039070008034008140054010b108165141180181c3c5c950017007410300038003000420303c050040c40240300c2030740d880c40d04a41e0b40345039210103070008030a000440c40c0300f07128200030075100c5060f145803801d0a0710f90716410112600303898100d002c42c0c01c0d484c100f40c0300e00300b4400da40a94400c0d0b0801c1d50030f00b45400d0100361107030001000017600c04180da000882000380d0790b20100c0103580241c081500e91030326144995039252000016823180c402d90300003070801071280810b80d0035281d0106903941180c40e00411850994503006040751419000d10003003450b902244140a1940440300724456281800740444266001411036400c054008005400202d48007a1072003110034018040040c000d5081030b400c908180b00c3c14004540182460605042c19500240c01d070540e0350000020015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 440354019 1250 440352769 440352793
    0xf0b0d1a1003061a0a051c09080a030c09080c0a0905220b0a06050f0a030f0f080d06090608240711030d05010303030f0903140f07061d12070507050d05010f1d 69
    0x43d0300031700d0040c1000070810032a002619179104c8400408148460700802c1100c425a1810980e811604001001030365459034200c0c219844140d00c0010301c038500c054181c610310840404c44101da0380c0580708060380c660707000c24030b078020011180002c500c0321000240c119820389040510a1030a60700d0800c0c20b410090041914900900342000300035000380300d005c80300d240d40e8403c94503000c594002e54201c28488200d2003c5028000206001603071b2143c00070f251400c1408070b100321703540f5400566055010010408400300101040c86181e070348000e401c01d555544100440f4802d4903142e00b44003c3c0400300d4008813050150708002d0580e8070980b82031100c44140500740048805d000c40140c002803041e0030300c800000e0a00014402d14421000311490a0300307649442c01034880d144036060300ca101154481468440502c5118500f403504044940303040c60079141e03181d40300098010b00d84181c04609140e401c0220950141c0003003204828148032950403080b0000720300c090b4010b880101c3c007901c1c0391000c2e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 440355269 1250 440354019 440354069
    0xf040207030e101808301204030f02120c120c030c010f0207031218150f06080a0b07090602031806070203060f040209010f03020306010b1809090c01090f0b0d1a100306 73
    0x10706e5150b50281010340301500003400ca005500c54500c840803400420049100240180308607200320b0098640c1c040034003244600a00c0c0480c07000d000c101c00d220600010310009008914800002d400a618540f590110b81d0658114490b14a60010a601c0c1444154455080340c0140240a0003501e03542103c00181785880e0030340d041440800c050900c44d4100328006050031030074000062040d42c002900c082c41e681c1c21011941150041c0e20079900c441484c50411500080c5075500101c1c5203449041c2070305c2c0c0f800c042d58031f006a03290495042d40f08a003d00702c2d91102d2040da40519001000c0f1411401c0841102d031013000151016400789540800220f82000304007100b10071a5406402402c541e0f19012200b1101d4200d40391490f000100c0c102a240c040d50340e800700ea401140040081c2140061500000d48000b0345a8001d4621041d09002000520305100c05e440c02040c000002044070320b01403400000c043c174007264580c3c0c0804042007000f8403650580c8580b084c2c1d2290040b40480303000049180d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 440356519 1250 440355269 440355283
    0x50d030f030b1f121509050411010c03080f190504060b0a0602070b04060804110409031e03050709060806030f01051911090303090d0c0b0d02090405070804020f040207030e101808 78
    0x35000040c400210b07040d244106640704007403a1002000840c0345c20201441c0c3d03914074940c040c00e0b0b83c9840d1410720040c81041c5103000c10b840300900300120030401c01d0340d0182c02114020040c4440c1498900081e003034403009608080c844003445800c10141c9010320384a001482c003400601e000356403a59011030002d00020744c00056a03162048641058a805070403542080008c1040300c03a002400c040306c006031600d01610b81514400c0c0c84031445104c4800d1116494188904a48205400e002c1480000c503002403450061345d00c035160031092036a038040400d1a00800250029503503107000100520402040404000701c00c414006015182061084101d28007601245513495041044039500714070388982c020000b02d10413040002d6942d514050f8090f00d800a0050018154000461298a181c2441813603400680c5040c1034256052580103d402000301007072140c02107900049001c145401044181c1a0304402069016244c40c0f044000b09003005510f40c1e982401e41c0c0e02004581c2c401c2c08200342c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 440357769 1250 440356519 440356549
    0x3060504061b0f120c05091221030606030406050405010902031b18150409051507020c01081e071d0a0f0302030708032812020d05011502010204080307060b0a050d030f030b 75
    0x1070302c0f21130900ca000004000d40c401034028001c08100302980d40e00c071148101e0741070f60440040c00c080944162100d070341500c0032446c23a04007501001045016602e00095130b8009402c0040062140d03114a0014010221002c010f90b06110320810b4000b00420300c030680200e88002d80f0f241601c000c00c20040c640442e4280d905d440442c22040428403582800c0e03002d40304e0b09001e40300b00c5d0100d0f10070110600706008151900300042e000541002d5165801c0b002032500301c51038542904038104c5400b4400c3c1103d0000e0445406c20890080102440785000c0c2500130302c0d50b0080c0405940f66648564144082e0756100481c000c2c042e2160025241c4000300640f13010340c2d10f03013112500e00400e400050b4500f080c184200d506000b00a60802c3e5000d8003031000d4424401194030000d0154101840c82074450380d50300202c81160b004000a0282030008415502200c2d881000400c0b01e5811000094144006400151300280d40348081c000b410b42c411a080c030b070300000c2d032400c10501e44501d082c030001518290750 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 440359019 1250 440357769 440357777
    0x1c0326041101170103052811010315210203010c0f0c14070b0301080604060e03040f0b07060219050304060605030601050d020907021f020406021b0f061303060504061b0f 74
    0xa0007090700511800c448240500d070400580075a1940660a08001e81040d580ca41c030104c41310b401443c80011303050300c8043c2e511800002617020b40c0c907014401451464a41050f03190030210704145000e000200181c245030303031400300460080700d01c45422181540160322a41c20420400113030740c011901a13030311303d130f095880503a0a02130785c540341410351207104030001c18850702d070000515a90301d001450181c21140060081410141002c40688509c15400c66064000708010404510200310000031120100c10f0076840b1701460411702d000f8050484002581c0840d502c142c0e19855005c001148101d00c54482041703126150000e156440b4024011140c02c03000200802000d8940803964941c02142d610484903203c070b00740881c00b41a04039800c40680140c0208041c0304131a01400300200c40c0204810011940d0110b000051200b4101c504060258100090001c0c1a200c08010a009103030003010a00c0141024a4800c004002c410071407140089007402850707a440c8201c090011150f00303555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 440360269 1250 440359019 440359021
    0x2120c030901050a211e1103150a18051b04150302091215062110090206040b0406090e0601080f0c3703050c0313201c0326 54
    0x70040d15240e02c60080381040c0109030600090111132449070520b188000140454050004000d81c140c00040b440078404250804240d0442c4840b00c00549601c80ca1214500b184c520b98000819100182038000c00e1003800b01c2c030040c80d00e009032074000030301580000310407400c0d00a00c0250501280a14020180c8481e0f541c0301110016100b40c01402d80010010134610103040c00701c426900c2d010340d40501110100a450402100d803030300c0021081002a801b1503840c2c0c05401008040d210000c01c032041090b0f40d0399110038000d640f81d48081c2d078040c3c000b070300300c9540c4d41d9124240a044586107100d050700001c40301002845030b503c034000281c000d00d49107018807a5511800110041c2e500b0aa004100307040c8000790380980305d060186465405101607a10301c0408030030040003815030f50300502340400d1110070024840428460b58a0f943c20302c2e00600f03056480500b0380d01342c000139401c40e40059845070b5103270001d544210b00c03c528011440e22031745412401110007441c82c031040503014501c00c0c580c04454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 440361519 1250 440360269 440360287
    0x12090409030509100903060f020922020c0d02010e0d0e0102060f0c0d02040303030b09180a15060b0408340b03060d020d03020615090f071209020a080d02120c03 70
    0x142001155074070a040440c2030400b604041056800c200114100041c00c032102001440414840c7e840e08aa424409600c2c1000010210304865410f140080240c03403581c4081220a455030b05030303800c1d41e100c0c00964482c407160401c0240a804510500902030088e000e01c507800c80d02071043c280340c01c2d1301a00504450383d516507498503e034000031714130a61407404025440703411200f44001c2001d144680c070005a024440780c2804542c02000300414003403410340314142e14100d0005002984c040c0d114801c1c0d03540c8511100407001401c00369009050507903000c1000b00c0c0740d680c040303060042c00070104803001043d40c0744000c401802484140d00340c007210740044180101000d04004680c0304801401c414074604880d03002c40d000001c820401e40068000e2000e00c07000402c070307400c0080c581d07400701c070b4211950900c41003060400102520303290510104481010002c4c1d81500b0147e400c40d0010289181c0e5035681c2582500c40072036581c1ca400600808000039401e904540036940420b0401b0f0003581042460 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 440362769 1250 440361519 440361521
    0x1407090c1d010306080303161101050903040515121305010f11030105011412040308102301080717010e1602030c0c010c08071e120f020c270406020912120904 69
    0x1c0459904050311101d001c6074100302000118090784440c80807040074051004010700003480e24044d46c0e0326034101004d000b0840d00000603581500c2c03044916011001040314442021312458005240e80700b080810440a040c0c00700f01c001c0010b000e00e00074003040e030101c15a4021208203c0c840700003e42d043c40140700d00d5129050744c9a140c00c0c02c241d10f501c0c114103622480030314081102c0840000d40202d040044815040039404000e01511403045110b10041e800b6800c900c2200d44058100411013001a51443c401c4081c01c40f60721003103619034640c0d40c660003080d2607000221106807150980740b031407194180c400011551060882c001600361100410b00454440726101019103d1050038011480428291180d0781c002c2c540c4170328454400c401c107140110110a02200480030702030000c054055a41e000310b102424175100b161400004104c4079446282e07140810f0f01d4520404000042104000c4107030300801d94210105c80e5200c00c0659000c1d1556548a40800d80b5107211040c800c240040c105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 440364019 1250 440362769 440362817
    0x60a091809150b030115080601050105160b07200c06030f09160801020414010f081b190305060f090601050d05060f0d060b191a09030c0d1407090c 64
    0x1020004a5840c540d030310b440d0264141d04100c0440ba96540742e81114a19003403196444080f10705914a54185c9030a00143e20340b10144259810300100184101c1c0c00e80310100100740a543c4007802d01d6a83c00c0400000b0010403c4124013421462410203e11111784c00003181098108001c080920f15540d003074072050759960281c4a02c0300c500c60a042596070307034007400c2c060340034040c0500010385032450200d0400145d140e80d8421418803c01c0141d0500d020b40c010001e580c0000241a40c00c1d80c003114181c1a5000d1041900c038a5450008040e00b1000c20f42c950000c40c0206000c441d4980141004030400010600c1941c190307010803400c000f4140d082001c0d410050b80490300410320a1380344400c1000c107403030f600200000c490203980c2c0e200c200e00625140100d1140c011001c00b19040c0355050000c1107448045210300015646804680c10005560800107008000b41c00707015516540b00d10301d09550000000c0510280f80d0242c0701c1c1c0440c0000f07003840f5640d46050182d4034000d59141921602440c511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 440365269 1250 440364019 440364059
    0x703030f0603021f02150609040f1b0b04050909011812021501260c0f1e04020d0603030f03180b0711070b0406031802090f130501060b030411060a09 65
    0x901c400700000565110310200c3c182c0d00e9551180d00348039104580c001d04200d80050708155515026040c0505926074000b035580c030950007840c8000c104141d0424984845080c054044600c005000119400c06200c0241c400c85030300303a601242d15118000c29a082c2c407031011000c014041c0c401003041c08180304202050318510300b13005485100c404048030a541c518245c110340c100710030690780250416803070300c2d00007910707032b0403002802c00c00840c040007aa007074192450040c07003004031072180c4c400f203400003000007003a041c0188210341c6c030300c0042c1807000506020720080d008100500c101d0101c55000c0e000c1c1d0110b80c0c3c465000ba06504445945410042501030080e0080080b42d034245800705004114040280861039a401e886900e080001015140c01c10140130307540018400440050721001e404a03001090f0199907901039550394444031102c003942401130a17039030030076800082080c24000214004c0e8043c0641542c5450110188003613031044400d101c0001d07071b0300c01003040441c2c0d101041005d144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 440366519 1250 440365269 440365271
    0x80f0c03060d0b090c100216180608010e0a02010206070c0327050301050a0911030f070e0a0e030f0d0606031e0c0201020c010f0516080f0109020a031d010504060b030708030703030f 79
    0x19803180070141c3d03011180900560300581000c24a450104000346c0304506620007400010192010651070507620300c11038004440c80c4440d00211006604104080e00d0303520000c0204081594131a540d400a0201c1030f40580903400100305100d1280524102d05605501d607071030803007840403c4a040e030003d202d80605001c42080e0201741607800380039207400390b940c65401041070810f5080008444001c004101d1290340007000d01c191804010079000111101c880c0c4601880e52034001e84070180003501c1c078450b03060000040c1e03000c490000360041d041d4a54001d8040001c0798032100241d084844100e81d800003007081c4840100c01485c190010313100804035100150400c201121042c0c20350302c2240e0f41030401c07600c90b0100100084141c0e40d02e85400c0712803130580b0150038841c007904540360040c0107100c0255000540d1404840c02500300001c0059918038034442001e41c0c0c403501e40241420f8401b2503003941011040e40461400080103420f44210501441c9032900c01c0e80e041d4018030b0002c401c680300c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 440367769 1250 440366519 440366539
    0xf120314130b030f0f06010c06020c1908040e060a0f0306090c030b27060c03040b041b14030f0f250e090f06070f0207030b040f050609010b10080f0c0306 67
    0x682120480d101c020411190003a80300e04081c0401007811500400c00102c1140580810050707aa00c401080a0070341c018800507070300c0411a03942800c04010185892401d401e1140b0f010410510000402c1101d90340e032002070307150310f40c18100402150316100e8048401c544074070610200b040e13580140b824503c600200e0400f141d0366540d103040c03110204e8030103110003220241200c10048a09040c8805115100034180c1e80c036100ca403410140c0030141010744a880c1c0b90000400704154210700c8024588100c801d20085650307102e41c00c604681c035226090203405002d5440300a910b000410f01c1840481c00041c202d4450031603060940c0c14017103c00c0d0704425210b00c0c00001e1005d60007690300c4c0aa044900a04410302e000b103901441d044000d03040e0030800c0000309403164a294081030b83c2040e40d078002c0c101c41207a15103040030a0303200c2c80d00d000640039000b071000344a446241544048802c403402e450407801549140d0f42a52240811254041c822513810000f60140700b01400450703200000421814030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440369019 1250 440367769 440367787
    0x3070c1202060d022101170705092415070b010906060507050d030209010c0804032108010f030b0606220f0b0708030f0408130b03010302040f0606020c09040201030f090506100f120314 80
    0x80031001f0381c40008814081326000700403c100380100409040166150642c904100f1403100c06003013409401e2180303011200700d0380e1003030303480d9044019a42080b06516481c1c0185050900c2608400c0c800c034040a4904100000c03024042d5040e2224036400401a0004100f50b20056029600c40d002460400c01c441c003000e000184004041d0000d14054001255500e91500c011100d0110600e064418483c5a80040108001c0389a0480c140d03980284c0090280c0c0b41d00c00030400d2400780c201114400d4107140242c4111505001c06482210746c1089009400b40e078034020520396100b001000b0713107100d00810010b4407003030118035010b8000f44180b80061a22503a00b64540f40400302da0065945100c00100400941c61b1078010a400041c410070100451071601c180a56102d010542c038a000c0c0804000150035a8000c0c5d10922030108401c200784a120f5881ca0043c2d1203034000c1b42c03000865000640c1c0400e26035440d2203500140d580a8013200d941c0c01882d01c094440c540c80e110b4406c0240410045016 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 440370269 1250 440369019 440369077
    0x14090921030f060a050d080702030a02040203010b0319150302190302221505010912060b0603010807031403070512030c0c070609060f140901140904060803070c1202060d02 75
    0x106031000805041d490341050360b062a22010050000d502c604044001403015945042d62034803510340c0703d000c2da070307803aa980c3c80401c0c203081034164047c1d030042c4003000002e91081c4600c0114421134501c0195040c864810051400701c4120400d43c0c140000381210920042c1002c507001580078001c440c0e41da02d401d60f00d9000490410f402a0000900034181c4103941c03000c582401600d9003040704002c40020642080002450084107200b1505100c801980c2e500a00016030b2184800c40340151020303036a0b6856800603a41e8601621080f69844200c0a82403004180030080d00c402543c804050610034184440100b0390f504007411248816104012170141c0100810060000704803503107400100b17034503009000c3d1060840d45004024805a82a6000d1103403480040350b6002009007054280e180c000200c2021500540034100d0b00a0716000020442c071100202400c90303140b1889000303144035140c40c0b01c01c0e40e0f841518002034210f0000d00110a4a05280d000782c141c024041c0d0a90030300c8100c0c401051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 440371519 1250 440370269 440370313
    0x140102010b12010e160602060703020d0e0d03020a021605060a21060608010e01080a0b01060f0e030f0307060e0a1106030a0f1401031704080604060f15030602040e060a140909 76
    0xb010b81d80d920019640c0300b440610034442c2442c1c02d00760842d00c040c50f0100c00b80d11210300410b000201940018007a107816000e900845450140c2d8040324420072000c00d024000b03501455002d00503104140d01d106002c0e0100c807440c001e40308040c041034149158041c09607400c2034950320042401e41502440c0c00b100802e44100b0000304080d642c1c46103554900a00c100c1c5900341030b00014000d4000304850000305100f200d01c0c5046599902c0c162241401c4800101c40744a0240d140c41d07410701420380608aa80702c0000a0a040e0380141000c201701d03200b21094503030300d210003078004100400032480c100882c0340c0200907540c000c61034100851101a2000c611040b43c84c1000c101300195403e0b00140117110742c900c00045120068600c2c01d140c1418080750540e586002030004010b01d403600031548105455412001522003203801c89407011f62030746455000380d04240125148001c81a001486a107040840d42c01190030b0782c0040c9200040317550a200a044000b000c2c1002032113006081d40900410398071113 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 440372769 1250 440371519 440371549
    0x10b060304110a12030e1509030114010e0a06060f0e0409060507080412020c0d020f0301141303030c05041d1806071107050907050f0a030f0204240810140102010b 71
    0x4040b581c0404020400e00c0c92490700801c140c04243e400020029401401000d0412001ca461501804c82418544260300c00c01d00c2103a055400e2072a60b0b4101007a08003d5416903506020301107159035011340369000c0796514814800060030603200590b1843c010004013400c503001401c0804c0300d61841d161401519015a148400104070000b00000d01141c400708840c40b40c00340c405800030401c03810001d5500001d0071000784c86000441d03146441a90250700100d01c800f80008002402d1400700380c2c2414480070000150301080c14030306050385280c40340c400c907001c0d00e2008402c1d09a00001c85402c18401900034001074183c996201d018104003402c2000c03d00c45c1c0803030b940d5120003034002c0700c0d0941046686d900060141900c40300b8003409940200c2070711407070018003100300e454001004085000d04441d01406440d242f0015000c40c950070800c1c2090a80440e1081540d5201e510203412100701c042242c1070520802d001c0380038032040c50000c61040741c994052001199601031000003a6400030544c00f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 440374019 1250 440372769 440372783
    0xb090a0b0f04030818010f03060308031902070b070c020a090e1b0f0d23060609010510230307090b03060901152703060b03060114010c0320100f0903021c02010b060304 73
    0x40385405e5039101c450500c1e08242840e0a206041c51a564003000c0e00000c0c0c00f21440d0440c0214545000d185507040d503e40c0e070341020300d54000d810b001c82e01804c00c511401043e4051a41d5010124811000f1700604140c030406000400c810500d04003ea0741780d00040c00801c0d4480d003074140d0004031b0340c5d88000a10a0500808400c800d040b6110200d01010801da160300040c3e40102d0304000361036840e030130701d00e04540081e00e40202d41419404200c484a404001e1445400b03000c40f0f1001c810581c0d54040c500c6902c95840b00c42c42030fa01ea022090040c0001c4800cdc540c8900b245006110782000c2c00303c401d102d00503034100150703550070301821410120b01d0301001300703a00e500c03440d0200103209080c0105c03511460103a01030500c0c1d50509810f40e2a0203007070181c00707050000049510040600c95000c00c48002c14510419405c3c500d400985511075096040c1c15502d107092141090b00b0211901c912511a54103800900003411704200e080600b0100006080565594140c00d00e003a846141c003e5101381d100d440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 440375269 1250 440374019 440374057
    0x51012030906030b041503060b12100203010515030411010c02061e090a0b0310091a0a080c030706110a0f2307090c020a02060d050910110a0206010b090a0b0f040308 72
    0x8040304d03002440c080c0b040d07041400e5080390304408840b24040d641c10840104204034040c02055546a022040700403038801e010040328003440c26400380d41a144100c5040c5204507070800b5000a60109446c05090521002400801c941c000e0741281405440540b0450800d1103c10144c129480100c003010315042c40091114030600d0207510190103040f200148905506060007001903500075400740028403a41e81d001c0800c031f00e202c1e0349403030040d0034028829800b058841d0110394680d5801400c1301c0c02031007581c001003545409140c0c07245003203000c2402024803003403e403030b50a5000801501034482d9400c1003095140381c00984041002c03a18114020320685103042d4004007125a600c1c01e00702150040344408c1d0041c3d44880c112600107480220100c1c460300e4440b60076044c600b02d039200d40c58592401c08030f00409039841c0040e1204400c00e409890300f5a030388003141e01e158401d8041c0b440d805000800e0034060512000c0c047e051449603001c0c6c4500b03064407540c81064680c4004c45400b00410310704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 440376519 1250 440375269 440375279
    0x1b071a1927060c14030a1e0e1f080f01051e0105040515040807090203090303190e0d030608010b09090d050c211c2307020102090a1e06170a0510120309 66
    0x56075084c09498031100a5161480034100200451070a020386d6404c21800d070001c284451241c15030301c0c031407103009100904076010555080425a890105000422131600010311036603540c0c40c106040390809096101034010802c0d0000c40d146000c0f401a05101d018071000c14951158004c08600f600c0303800700181d4582c18010064903050140d448007081500400421402d01d0020040d41c1d0014240105111420041c0c0820805007210074072051303042c4160951911003540c59008a02200c10300c0008100c074a00700701c28800e1030070040b40c5020301d503444550095040740c810401020388031040010b88181c14a80454401d61241c1e2822280e01c890700400d0b5101308140c0310003211062a0354820401108840f52083c1e801c610840425906414012000072450b9000390111988182c009000180c072903100d9400210303002450801004019619101062450003402ca0b80405049507101041c2c9940e01400311000d401c000384a84401801103100007881c0820500544171240f19485000ba668104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 440377769 1250 440376519 440376533
    0x90f0b0903041202010e0d080c0c0a060e03031204080f0708071118060907050408010f0e0d0212030c03070905130e0f070f1a1b071a1927060c 62
    0xc0e0000c0c0c4181c01c100000c010704003040c046801810760a0030007610000701c0a000a0400e000c008001c0c1c01003000080300d0040700e00c00320321404450000c03142507154603103c120498812540c10080c07505544200010300c020344020b210650702a1103410920301d481c0709041c042065402264003102c40010114041041015002007080c0d2610141c0f210350340b80781c00c80c0f1004900103028110a005e400500c0115065a2040040310094980c690007402541861146035000300410301901c1c585018a0500c801c44510201746580c180c5400c901c45829030f00c2d0415000c816070710140980c1d007803291030700001400b80c6410914501a1800d0340e00000e07402c8000112030b080000050b01c00d070258101a50511903440040ca4000c182c80c00071000301c81094a00c0600d84140c4a81003402d0304d0310601c0602c1195600001071704030241c074001e6081c2e800b841c044044e5030601e4083e50741131400b0154403041c050003052203001c5003140b000000503c090034130a803601c03012003500140c105c140000c10300c61440b0b0612000b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 440379019 1250 440377769 440377771
    0x2030a0b0403030e0105060108070f02150115080a0203060a0b1803010c0804050d21020a0324180b0114070807060f230f040311030c060106020615010e0307060e040f090f0b 75
    0x1c4c0207100c1e510b0102c0000b005080000c0c600d00a1150700d00410159500c00c0040100507079804058110f1546c4611148039420003140c550b8001600050010701035004500980c0e001d090083d0440310000e0030b00c0842400c84d044003a214075075400302410040035a40900550030100c50517122030f611030500e803c005007000c46200c0d4080500010072072984a60250311000d40c0745040c04c07030380142c9035100103c085000e441841011100203252042c079903884145400f52038101c4189030500b0341c502c0400c070500c0081d2080000c895012844801481c0004d0441c08000e007546407180c0003003881c00034155240400c0341c80d54440800390b5940c403445d8510038040c1341204549819034001584003440e0016205241010040000b0100b0040b4541c0b0380320110100240c40c10301c07019000703544066844000096403503d044854101041485000700300030b500a000c40d9000b00b10180c083c05a030350605009640002082d41141d4120f82c0e1103055000c10f1070f40f4401c142c00f4522624500700d4103c4d40e82807000d80800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 440380269 1250 440379019 440379041
    0xc150f0310170303100e130503120a0b150906030a0f020c0c0418020f040c0203041d0405160303270b0a090801060b12010603050402010203070605011d0702011e021602030a0b040303 79
    0x803042040c0004188200c170710604803103007002c90814560380e146030320841c11800341008046100200703500300f81035003450751503204207001c1c00c040254040c02d41c1000700107071114072541ca94071410000d8003118103180c401107070b025100d94000715480e80301028220481c1d211411103041a048140807590a20b4240904901c40b01000030702d05c005c15064000030014541c200b4414800c07651142100600c50007402038400400809260801c002148030b182034031820200c6013101c51380917804400b594141d82e0401031080d00e400d030392904000800401d40102c0c1740300d500c0700c3c0c10340f070120710381f0010342e880700312000f400100423a42d10130031300602e4078103400e094480075003107440340b15410703c240c43d00b40250b240f80c0c5045480b0741c603020896441e5400140d00718804c1001c041c0c621810300c0004203585403082d80e103030790100000c42c00d00fa280d500e10b10224200c40307600303205005035030918408030105800c94005d8101403008001c42c50307800900c1d50000f841c160403a03404561175600c0504200078142c16110b5014414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 440381519 1250 440380269 440380273
    0x2060406050a150612060308030408031807030b0412030905060717060a060c030516021306032901060f0905040c02010b0a0b0c121606060e15030703050c150f031017 72
    0x40d007004982040043e4000c4d8410001c05600c00e114181e01c40c0c12000013540c011040030795078103050803d0390721903000300c1c0e1010540c480782c0c445043d00b200010305601140d401c401c00d80480e4036940d466002100c0b01c1e551080805455444580211740305200d081d006030510741b2041413104846010b001e401d5001401380788100e1900408012468111504603611740e81490220750303850150b0603041c40b0002500300a500f200101d40460f00220307a9a2025003030300c4c0954040413143e4080102140350801384411201400e4080c2e0040050a00604146580c8081400c04094041d12036010a040b15089040701005030344030206443c00c1d080402800d005011441d1002d40741c90308034105e09a8440c40841c117683da6600016614500c5440c4407402091903511000c18000145e0300e21100500c070000355103900840750903c908080794600004d940084940c0000079280d08103500c1b0800401880040300c082d980c50b02002103c5903c1c91140055210b04980200001c8082c10552890b040b00d0954000c0c841c25 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 440382769 1250 440381519 440381531
    0x402070837140f030403090f0906030b1f0504200711090610051207030204050d0f020a060c0b04080d02220f0b030f0a0908130b120604020301120f0305130602060406050a 74
    0x82ca071008211101c40104000c207507135a0701ca615045a245031164030045041c1e1042c031001c102c0c29410f400c580c0c1140e0182c0f014120548030110303040707425000501501d2841c03440041c00c003c40c0c05e103a04a0420510b41c94040441800805c10f008217661100b00122071000041c0d02c0480c0c0d03460400c40340c94010b5001d460084000400f0304020b042480341a40d002d8100c0008000115121300c00e40449000e4000031303000080c00340c81498400c01c29048000202e104a040342004a11184190b90034040541c00643e4500e2503107550315948480d5212000d400c41158080100035441c88064508000c460120b4824030350301c07803500c2111010701d5800d0b00050401081002400303900c02d00340d480e03244c028049420000d11003040d440c1140a61281c0d950b0030303150a804010010315090f1903000340560450505101e24103030380c0c600030841244004d000c7c0c0b032070031040f4800a001003034490b5864407602e8442d0a000d450301c0d9554030354051600c0c266205000681c803400c1000100700480c002d04d40c02004000d024468 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 440384019 1250 440382769 440382797
    0x3120f0e03030a0225300e010809071a0c060105010201051915080f0705190e1f180c1d09070f02120d060303022a0402070837 55
    0x41e480064044a14103401090f00819100301440c000b034201c80401d2028441081e40c80c16001c2e46060245c1c13a8495110344007101041380111007041000c465035910b400c401645000151034009c00031304008124403e40340c022505402c01012071a00b03001152416464080d0240754a14012050f00414116410314043c450036980c00c560010030104e0401000c6014803004010740340c006025844041d061145280c0c1442841010440704282e0700c00360fc06002001a40e0b2070042405031901c2244899242c5000183ca1400420041c0c5444400c00422002c202c2e60b0755003030750510000e1540ca4105580e036600d0311050a420102d5800003206900c2d0310b401105c0d8540000e0655a0010305000621085681d41c403440d92080c01051122a149407240381c1341c072000950400108910300040b4007610440c4448000d22500c0380341010b0008403210141c1480369000c00313200c042d4202d2801120158014000300e4030307501c5885000405500e15490005420380034008410540502e4940310091000e00b40384102c4c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 440385269 1250 440384019 440384023
    0x3020717070c09020906090301050a0b040c0207180509190606090b0d050c061b1e0601080708030a030b0d020405070305040b13020109090e030403050d0504062607230703120f0e 77
    0xc21180b103202d005840701700590219100f031280000290b0b25520304001c010304210b1503030020741804c5098a080051340d0409034107980c2c4030124064482404000b95170020514001e4011030340c07140311b02c0261524181f820a03410361441c09903e003180c10b103490741c00034000f080070cd2003030b0305010004035240500003200e07488032611040d40400c3c447c05a40005034041210040c0c103d900c0c84039100e003084985401420038600941c1a21010820075800b0302000020340010000c1ca1100f0743c0c8016028614102d600740041d4010504c198036950800450914880542e680e882544d02c285642e481c0898145000e127170080022074001c214103841d003c09904040540d9002c5a08000e8848031900014402d1a1500c850310718022544010558412810030608030b5500c00050422100c980e00c40a03110850b07040c81a41e81001e521000d04007083c200c00040c001845802c2510710b0f100346c2d0b1800c10209400c101510007a42c040c0740c05801241922410000c408080d2081e4400e805200e01c08205028403140c1a41e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 440386519 1250 440385269 440385293
    0x306050703180b09010b06040b13060e060406030e0a0209041101080702030a0507030c06200403170301121b210201140c07030f080c0d0c0317010b0301150306050a060302071707 77
    0x2070f00900440000900b0300509501900348513000400d25034803555100c00310015507215030b50001d450046c901c80010038070301510f900c0300c01400c001c08442c1040c0c104801140100410040000d0a106040549025031130307444806000f64002c281c503d140b480184005460f8080150000f030440d8001c0160100079648201a60b0140da41071400010009090616002421049030b603180d4070402480f03680301c1000d2480082c01261702c40c0421003036500b07200d10011624042440741c5440c0b61500c9081c04000360ba50303907010103401d45001100001c40c0c4c4036040c12049910340303191080d06105103801da100f5076030002c1408400403100d0407614a407076072114100d80c50344c40a10004220302c1011441c2c0007001000c0c415281200c145104440740c6c0303000001c0083c0021090103050300030070100e070469a03041c7d0150401605aa1030002041c3c65646454810507070046000c50074810580e41d504080303065a02c140c4120010801c42c1d0340542c84c2d0f403050400046001c4007101c3c20804080400820001400500c0e440c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 440387769 1250 440386519 440386523
    0x3181507050406110708070b03060108071d0f0409050703030221030108100c0210020f0405011101140c090102031b0c120708120d1b08040611070206070209040f0206070606030605070318 81
    0x2c4202a02c060307000b8941784450700040b1590284002c0403a0302c0c0404170145100c0c641c26aa031441c1d58469072425104410031540c44240da605224900c2e1a81c10094500400180003400000b0f640c0b02d50340324242811119041203005810802095100000400164140072a8000203074915490001d40700d5440c0143d20380140e07a142c41c0d400b5605854024012500004030801d002e655908003151300558561141c040c1e02d02180c40c02411100e0803105214020b486940c01d00500300366115039032615929088145030314114401042041d00008858181d80c2201d90300800a01c2030b209100b0421444280120402403da07219150401c8030500000c1c5660100281c914243d0b07842d80710820040252445002c070342101c5d24894a0340c00700503800b2403018821406684100800c1001884c128041d12540a029500540900c1100003614214400582007032043d1031041d0461403a9020840715041400c2c2603a06503070f07402d010400e00c0740c2c1d801510740c01070300c0d440c0803c1000550303080c42800110000380 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 440389019 1250 440387769 440387777
    0x2e020f0d1d030304050a06020d09060302070f420507080618060d080c0f011b0504090203060301020c0a0f0b061c0303020c1e07180b0a050d060f0203181507050406 71
    0xd01c03036039440601c200c42c040c04010b0328000b4819120480a9035501d00045004c0010b035000c400081c0740c511910a6600c000d0340a030009544002c103455030700c03450701da4110102d1a24040d00c0b0501e03410b0010401e0080c00c00f4000c118a4032410340d42c80080c21a48000c20560a2108250030090a0b0b5103030321038012a090349842c0c0011903103500022a011001402c0010041e500008004076032020005030182c040b50700d0402407042100c205804004220003040041c085031041c4020701144185401130340d88101c0203000103080c030212529061520101203801d981a90882c60710805000341c640e9640e41c011400e40720038031460400e000343c00070080118005010158081074500c150748003401103c0c0185d1504c0c0314000c0c039000d4400250740325000c40c825084117004141081c00900200c0c0602401014002d140d0721010b49000d041c414042108242100c110b5038980d0030032096071180c4065030044103004500101440100d400c0e81c60700c0b01c00303004210700e0221070701084903a950001c115015a04c144c07030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 440390269 1250 440389019 440389067
    0xb131e0806131a070c022805010507020f0312070b09060106120e0309210f0c030a140a080d0209040b010203193e0c2b022e020f0d 57
    0xa0801d0311520028403080c1c1c2c00000f8060014495005010001543c02111a46070304071180d00b0042c152652803070252200c8044880030070541d030003175000c2c1201c01c0c000b80c00380d400301d404100041d09000481300000070a03103001c200942840621054541c0c00034041c801401b155040c01006031802146400441010703445840941c4030138001d2003514940c62002d04000014508241c0ba826400c0100c04510418401c1149040da41c40f000240032400820240103081c1c0076240e5100c4d1071000c54020304103241849591101e07400241000028030b00e50207541ea005840b90450000c000c15100c8000e81c282c11984207004401c628504513070303500c4002425042c048000c920034041c420300350110115070812182c0d01c000050500c0e0b41d06da800080b47d00c0341c0c0165101a04040200210444166005c2d5980302c00011514000c1100b9560108220b0004005030000901a094080c844030200752800325000840e6074002c0543e010030110780d6900c1103402810314100c2256008080140000c248a601341000c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 440391519 1250 440390269 440390273
    0x160f140304020f0d0c05040513020a0e060103141603141e10080f01151a1c06090c0c050601081f090212060907061b0803040305090a0b131e080613 64
    0x21984583c45003016050594482c102e04104614000a124650155080000241d510207820030001c421690041c00041882d05004020000d81d0008001c00d050581e100300848180d983c01c0b001c0c0303200d5108800c00c001007101e0244003c01399051485001348103c100c1e02130004902c0310840c140840c21040c0d5881056036074002c8076285440955010840500511041000c40041034002c858030f00412801940708a03030760810b00d070a01008d01c02605100000b40210107100e00d04041110403450b818201065164650309860700300c4200c9440c036400300303d852299100300001484900c0c0140800006040002010b2101c1c4501c1071000125101d425a951400011543c400440c0d2021001120445100b49000006560b4401244c014500450300704104002081d00e042404604c0d503034070544103400c2d520307280d405890325002041201e42c00b5401948c01b040300305404018004d080a21858042c070645880d1103d4058460241500302405140d0310601c809030f0000344442e040444d00c089400c0041841c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 440392769 1250 440391519 440391529
    0x10e04060f02040b0702041104030f080a020109120801030308070305070801300b0f090a05030a03020d0b0d0605070306050105090303090609030a0b0a06030b0601080f0105040e12030c03160f14030402 87
    0x40441d0303000c25407011601050400081003c1d0580300c0c4291420410364044d82c860103418022448000c1041c66820390140006940001801147c51030380004078602a807540c6600e0b4014070394001d0000904440d0040007499403050040f0303040f0b041810100054240b50b00006c1c807041050080d0a10700c030301e80d80b58010203c411103c05000c50700325824107070607486a14100205503400e580d07400e03518039000045000410041520080341c3d03401002507241140d440c1080d4040e401111107040900c0d5a01000300003a103680c62180756041c480c8200040503c0c1141d0040d088950940283e8104501030041c4031040e2800421110115001c0750310360744964116001074900140344034003c1045180e070003440b164502c2600464280c912540390b400c5503607511001103914100403910780314120315032401080182000c0d480a402d940c81d00040d60569410301e10622200d0344181c8031500380d240d000041010004040410b600c5800482c41c02c0184e920343d500004107403030781d500f120032500c40e4000301090031940d803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 440394019 1250 440392769 440392781
    0x70c030e150d020a0e010206010b071b030b0406090b1e0a0f0e070f030201030b090f0a0e0c0d0507051002151b090411071101110a0602030a02121f05030a0b010e0406 72
    0x2400c0c1c1c060303985804000040180d008001001c0100d00f030f2800d02c0742c3c07030360010032121b06881c2e02a20440c04c04405c1d0700c1c0c00c8901c0e00c13002c00040c203401d4040c00200200300b02c0c1034001c0c40349001d000d002ca29140f5074901b0a80311380c001401c440ea400d0030309100300398004448011a42210403c00040f4140382c01c0e40c600002006d91400d2180203204c1c0079400683c1d0318a58010f2002c8a000362420010701d82d010003031100340c40301194000a072910420019039400300e40e0307212042c444c21b114101d0f41044030010114980c580503060503602030340703c110308000500e01078507410700401d032920181c44009140368014103c040050302110801c050901c000080e914088203031aa1044000c0051025458100e42a01c880d40031550a03946021b103e078103ca401e501510801851a422900800341030703020707445080c000e4001078265112203808203c00d008192010840e54000d80405581c016400860300c1404007500035903004502030b8100002c044041600715400a046402c0805241c0207a500c5c2e24100303009142c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 440395269 1250 440394019 440394049
    0x2040504061710020a0503010308130911040504290d030e030307030f0206070f09140117010b0322050c0915090408040512030f0a030c0513080109030e0603070c030e 72
    0x85000c07000520704a4000e403214102d2800025680800b11051503881a8441c5000c1e00011a804100410000341100000c20201545c000300c03490300c0d5104e100c44400e894440300702401205002c10144000d00c1c2a02c500f01542442c80110329001d50380080b10027943c8030080c00c1603c613041c2d83c0c038080281802200b505252031401001c0e2a511452840e01515406108100000501c100000912040d000b0841d80d40209207940307440800300e1400340701400d0342c081c6904460401c51941c080240c1440b0025809003c0c000015803291246071200c8011501035014948080c1d203402140c100c40414008142c2d01440702096608050700e50300c8a0302d9000b00140181380c203030004540810030080c410418040c0c000d40c0c0d8110f41c4000c0c1d01d903503d00070607a41d008071600c401c00720f00e0411900388124021340c4140c0c038034400340c203085040040b04000c418864655600200d1965180c0456804142e8403000046004404480b42c6056040c440802084460b4a50307000b824412032420b007603101c3d565490002207900c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 440396519 1250 440395269 440395271
    0x1030b030a031119031d0306070909020a0522030515010303050403080d0905030a0801090b0a081002090a050319120921022d0306060a0305030d180c140f1f050d02040504 74
    0x18811740360051940682c0f0104082030080419044c5461a0101e041c5010710060364a0400b09418494110020b50140801d113003071000400203101106540300c10500c0b080564000e420805107141009814810880400844840f500c001030001a4006069070245e03600024110f403500d454880c028003d060085000c2c0031484041840c0c502640d11082290507199201800c0c081102d000040c03101040c134602400e00103811503400c1c1c8021030780c1039000e0540100001d00d080f805031703641c5002ca410a1f4180d4020b1503184014180c50341800181c4403c10040b138014507000d01264908070b1750419200c0380070180000c003c41e4902420a5640d60900080010709441160960780c4e01c20000c82c0e400c0000110540c040e005600c00104640f510700340705011aa00300026514240e00d943c21403004100c2003d52410480507804503001048056030310030080d0180007611007204042d207081210780105108000d1140143c1140044880c44200c401507840d103040c00e0158560750f55042540103406980c010942107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 440397769 1250 440396519 440396563
    0x30a020a0813181a0a05130f0b06120403030c08070f0f03090818030f0115051c05030a0f081008194b120c0302150f060f01030b030a0311 60
    0x2205664400e9001c0302120016113440005041400640c0301c9a01c11568001100c2101408940781508010f1414600160005a070780c1c80c2000200c0a801c07110464541e106500c00700410141c040c410840408018102032001e0b00c1e10f11002400b86402410140c100140d0f0b140380d040c1c0c54080d400c1001080c2c0c2c0450310689507403e00c403c0d510300003603007007407288244a01c00d0050784d0111b0611030840e5040480525071481800c04041c0300a01400d00340b9020342148114203000401c0c000d002402d0344032a90f5844061130080702d0300041c5a88009002500b81d4120004200b110707290000d5001d84002c44803201c014580030364103050b445280c1e090220382211502804c014443c002c202118031300c00841060440ca488100088a13803003130740070031004002c01807104110110a00440c00d10f800c040c4284120b914140842e8200390780d0a0040d549020014844c006120407031600c0100c18500c5202840c00704250328900001907510a640d40014080c822031541001d20b9440c14455201030b14414a0310620b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 440399019 1250 440397769 440397809
    0x240303030c0207050f151e0d0203010306050105011107060305070c020a030b060a06050c0601141201140712020708030a020f040e0f071701050f01112404020909030a020a0813 76
    0x78000c44074580380180100703070011640303240440030ba103070341340000d40301a0003120013084a030a65448280e1007206001703003030740c3e84c003016540500500b4410076400c0003507140d5146152410070380d50180c100e541800000e006600354070324002100401c031820791030042072940705c1c0e59003a40c0741c1e0910701010750010041400401407104a0304050b02a00d400c2d200c19041580c1c4034802c407000d0040d0542995507411007001005003801e80c0300c1045000313030b0040459202400780700400e82114986000c1003c6c4001680400c6500c5400003182101e50300149010741c07616001b55150016032000420b0018980c6e070200b0754600442c19041903802406409400140c2070030180306e0034000350012191800007500c5240c118045100b1120710346c0c101d0394040d0901016a444900560ba40c8010030110049486690302d0300460075500100c000c0203002c8803958001c03600f0203005002d1101030051000b4070030780c8100640c0d01413036400500b0800c000d0300038580507241c0d010440c0104031002554807039280c1d00c69440c80454 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 440400269 1250 440399019 440399021
    0xf022e05040f0602030f160201021509010b0109060e1c14160e1308030411011806050405010305182d012901030903080c13030206030406020c100e070924030303 70
    0x400e0342e02181e000d01c9150f035942812a40c0e80f141381800c4400f40c001384090240c446900d60781e048804c2c0f050040c0d40700740b18007200412240c20101d50400e884e83d1101070200d0196082a101009040c030740c50402c800040d0100800c03030030415817070303a2a0200c10f200002814003080808694942418800356450100112102d6001c20540c4c096401c3c401079a9000c540200080d034889843c0c40d40c4034001c0d6046a4960300c407400400e40305c8001906121041d9844c5000d504075680c12406084203440301c54595082c40c2c00101240c0c0c1c000e1100c06202e4075100240865040014101d24407208425004e0f0a10142680420405c4888120440b15030a080b223502d45102448040031070820628000100400d281c0011000d03541c00303c4024000c911180042040c0c41c10f00e1000707010304003030040d1303840c96260750f0781c08141164021030b425140f4540c0030490101d0320324240480c07054404d540b00d017404040499410141c86008521032800f1040c0d44140b464940358054622813811549140541805540c904000d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 440401519 1250 440400269 440400277
    0x117011d0a0c0b030708180c0a0905070906080103170f0c1614091612110705060708010b030903090904020103240302040e0d090b0c03070f03030e0114040f022e05 71
    0x2503400050b40b40105200b0681000d81e84241c100e81e450352940d45920246490250484030140d0b02401a0b907900c1c10079880d101000c00080100c803000103040c1c58001c1c00200b08802c45c1e040003080010050040001c6000c91581800483c0b48804040d9290b0751140c031107045106540b0040d800c0e025000700b0203102d07115004024100c070000d2039002020100c0000300b02540300e044440864045212800341d01061165851071140c11242c500002e40da01c4a5030b04400c190072005c021034803640b0140800007015070040b182801849117141050560400030b20190700c81c000c48015038042d00d165000501968485e40200220f80b001128005c000d0380c990300111034158131030009a0249062840b44100c1300380000340e0100c0c00b8145c0c2c0d182000281403000d40310803580518910b05203440148421400f084491003c440e100c0d00c0703071b00e0009072044a0344482c1c0c03c0d207254280c0300000d1440001000080f8401c001e220840c95812600542c4036143c00c0f544126442c2e050714460001507002d0300d80d40703485401600070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 440402769 1250 440401519 440401523
    0x108060711060403030c12020f220302010c110d02040e0307060b0604080c0d0212010507110709091a060d0606090b031608150406020d05040f02040b010201060501080117011d0a 77
    0x284006aa442105039100311440e42404000d510032070000300841d00c04e0740601084c0b9000d1411002007001d484031003040e42c00545240d2100c4000040229409070480100600c08c0b0a817800c8130809480d41e00040e1410000c4000170f081015907602c43c800d2943c812101c8a1590f0340184200500c000d0500003507625003000c241110454a44203c01c850351811405440848401c500200072044406051200d042c08110007284c00c001254401d82c4400000e026242c420151999203591000c51101010310340fa60b1076100e86916840d090110300494072044441881096a86890825488041c04603884c815000e00141200d40707066000714140319150450544414101c04568031164180c2440881c0250340c0f2680c82e0075488400000e0314183c4055403280e03c40d0195800506001d081c01041040e60021141116100111880d05046141034482c950b040103080c07008105a5003040c00180c595035060142d60b040c2e5565040d40010390b0f0094001840c0200354022044804800104803503613050a00300c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 440404019 1250 440402769 440402773
    0x1b1203050103021809060c0a031b170c03011412031209070924030f0203100c080613140a021e0d0504060608031c05060a0302031c1b0c14061e030108 65
    0x203102109428113030b42a00400403e0040e0585880d9102d074a42c05522000e85001850f0326402c07096481058110440780a5000307407500ca00344030702e0300c82c1480c0c1188010302e403402d122410700050203010f01c0d5285c4024511070555040c0642940142c03010301e14000c6600601184810382c082020864011500c1e808542c03e8200c2402106000c14980c8580f00d4600180d046968540f1410400b02c2e001e0060301c01c49500140948038109401e00f156016220f02d00300c254080360015051201c9814514071031801e110413440204100e80b044611002a81406040e82b80002d40100e0665440341220317000e40b161124108680c4d40d0b0718111800d40c030140c4004c60301a551149003c03000103000e0707004000c4a40760809100030031a0006031145100042001900640e001031086030013100503241080648440d00a40c4c460782003008080343d0082080e90102d45409007090180d00060009000d58010003e03500e03a100404660300b000404540580a04100104000c201c5e00c01c1071502205200254161042802 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 440405269 1250 440404019 440404039
    0x4110909040c0f0611030915131212080103020f01080703060b040e0a06050a03170d2012090c0109090518061810021e030703060b1b06060319031b120305010302 70
    0xc06840903085d0702c0036a4402c0d04200141c0c05245400e601c46c40d030b10001c100303046041c80c1521a1411007061242c00c00b0103010740d100c4610081c44007040150001c0300e51440d101e000e03981107601113090301d18141c541c2814040c1941c04680d14038080c3d005040500310f0016100c0e03c45a44034400d500d800c42c151a20f03a205454080c01003501e0034400d83d1102500d8022040005100c0c020901c400c85901803207814170010b035905000224219002c00c010305a20801c1e040d5910344030024800c9034141030141c07814050383d00000c1d600050381d80040421044175290f01c0005466a208425803506c241a0b4480301c21502071181003148504040802c84840c0021602700c48042c41c0c6191004100c0c8518641503280980300b000070800d900c0300d140116480903c8e880c002c1034103a0354010440c801c1e0041122035070040000c0003000c0c0100c10801c42c1c81c0c0d214078110000e051160040c0354229500480e44005401c0001c200c2d0f0700e0131140c0e00107142e0080f4681c0a00c01c405d084a00820090040c18280412882040400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 440406519 1250 440405269 440405279
    0x110f150c030903040501050d090c0909030305060d02150c0f0703300c0204020705010e0115181404061d030415110f0706080703150e0609061e04110909040c0f 69
    0x6410740b072003220b21900541c41d01e420314005582c1500200d800d0a0309645900c4c4000001c4c000444c100d0007030456010100701a122403030b000e010b541e0b0040241d8010804c00034030790050398030b130003c1d08500c5100140d41641c820241c2e800e942400380b5482029518484d0500010400c1003401080203003985000000c20030500c1d0140c0c2206204124212900248110490a015180540c01099400e128200005e042010359002c2825a010080b0344580e00c02001c43c10020110a010400c840710116802004656828000c0c444130000150018201d5595402246203070843c0101001c04189000d040300c1d1107a50343d00115800340c0074055030f00e000407500181034900f0b80c0005901d441003208100540034450034580211005e003c014000020180c80b03c0320303170170145241c0c0301000203070448440b000028a0803d040c08001c900c00380000340100301d4280a2420075000c20454008e41c03a085078085a1981c80d000704190703501596042070b92194071042444200800d961203503044034908404203944607952 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 440407769 1250 440406519 440406541
    0x100c09080604030f0c0b250203070305070b04020402041a0a021b1c03020102040902160c08070317070f021203120105090c0a050c0115030506100b0708040b030601110f15 74
    0x900c80c9885980c050004280040e004002e80c0100c1a801d181001c410000c40c3c03906010b610080d03440c2c400041c1c811004447e907281649410325a8090740c00190b00c0c240c81942c009203248202c0c94040c0c014a51800443c04555071501294000c01c4140108920344881544844040c3c0c0400e6190015105503282d50344620007454000400d944010b208001400040301c0703080e841204000100d045550800c0003150b240700900c09040e0ba41d07482e05400324080c0c3c5c2c514020014048070b400c450483d500485040001408121181540440498400d51603841c0c51400746102c0c951104000e600203072078005801218000805050709500c00c1c1d000b08a41c0e6a580b0a00c134075802c081d01c3e01103080c481002008034440c011402408500b00082c00090004046007841e0f0300314002d900200d030303103420040521100f0815030f50b20350094802d0704501e61400c071080c2d517410b03894803503441200b40012002c8001038007a809007058246881c100710541d4812110880c045031a042c01d0713801d030101e5210b1040400c0078a030382 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 440409019 1250 440407769 440407787
    0xa05030a02062a030c0a0905190504060b0c03032806030807110a060e19080a05070e0a060602070501120f0e0607030c080c092209030203091509030c040b0f040905100c 73
    0x81c8407020700d16150548205c149a20141c031440034481159000109615000301c584070300e029440340c0d11166420f01081200346c030060b0b88291800c00f001e001005d40c100c00481103a070400b1085103100500750f020f107102c510390b480c40010307488010314010000043c03000c58001000d005114100c4500e14134003e5040007091142c07801240d0002d400b100d8250202d0401480d030080010101d0007400402d035843d010140b400d82001e07412141c940001404000b00c90401081540082c524181805603034105030000b0b5a5401e544030b09410090103a810300c2034101c01e80d000b03020781d8410f00d00520030031003510025546d03940180c0e44880000c1c03600501424040c4146052030107042c4002c1d0303880c58000c1d220104610300161100c420241c4a03081c0b21400c084400c2c1c403d8000c200d2003500a907407034401d0703034007080000d00d04010601060041000612403a03034012505080b4075604a81c00901d0202ca4004a030300192000e0805030414075090012080c8080096001502c400c0310400f440030071080b1b0021540c1d040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 440410269 1250 440409019 440409091
    0x14040c17011e030c14010305072303041e0609020f01020d0509040506040e0613022e0305090f030a0207030204060f03020306011703090d0b0601182102030a05030a0206 73
    0x48400040c80030708a0342e885100c2c00c030300d1205003104154030f03510344903007000f1654000c8080d024202c0141089581601548c2d92042c00b40c00c0c007480125080e00c450b0300e00200110102401800000040e04004658030480c440c0c080c02c030840000c9080a161486c010401103c05910a030003601c0700c0700d015803000075840005102c035582c003428a05a982840701074100075102645c0a40c0303d42030f000001c941000b41c0c51003540c2d03007041c0b5002c542d0980140074910301142d14900d10502b0f4446002d1103217a45a80055240082d40380005240e43c3e00c2041c50b0410100c00141c0d035040c0030000b90340820907030015801040e2402290104020356503510f9041c00c02401d40310080d056000000104582604601240451400d850540c5c2c40c009501002981010305c1c0c00c0c0441d100152581030007001d507445003c10f4003842c11664401d2296007003003a40c400904559051a07000080d42c410141151010710940301c0641d800002c072600c4840b43d0501039212141100c005060781a10166102d88001560204000c0030b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 440411519 1250 440410269 440410307
    0x1503010608070f0b0c0109332007020d150e0601050904021518131a03012703050c010903050a1b0f02092502010c110106030209010e04030c05010614040c 67
    0x41d01d8002d803c0e180b900401ca031441255130318007c103c04100c0c003030390302d1604107100404007122469182201c07561030200300c0720044140c81c08242c0c064801c942d40441900b81030601040d03403a4005d0784000b83c00643c52401c028552480e40507100c0459100b500900c0c0170b00f21041c1035030556130300ca00500954074011a0702944c0b00b001c80e400398100c04c1402c4000d040081c0042417101103424100045400c19064182d00010140d0360020502c500c1500c44613119044000c500a00c114100c009019030111010b100d1541c08440c82a107410815001d00116040e902c0080000d20600800b81030192140c2c1004102c1404110201603080d8200c1861485c1c0074603951045800c5141e61413074007402041003005100e50200394048807507056200501612440c410865800414013002c00d00d4001c0c4540e0006010003e40c0c2e042510520040e80c0c1c400480d03041d2441c00102810541d0f446c28101c610078103010303000e00f01d03510341507010800f01c1003580007280080050f40c003440072a9001070100c7c2c0da190072040c460602e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 440412769 1250 440411519 440411549
    0x1d040630051e07151e020d171504050f090c1012020d2a0f0905090f0a020909010e01050f0a061209030e03030c031c180f030306030b150301060807 64
    0x4000342c0031002941d400b10011030b200d15403200720b11aa0aa804440080420702e03400d0078003459485820301100c103001c2c0303102510181c2078541001c1c128512080400203800510400112140f9121b000d402400354000c0c8103120078141201d9107129004266424586409084c4d101d0b8054102505503404010441c1d031345910019052510394025001190450f5119032600380c4612601038620990216001792116000000091440a4601038040f2022401d00c4041d03e802c20043e52000645a07108851031a2401c407a03035190b0b42c280081c070510030740c50f030711200b08030010840e0440520340f241030ba0717001c0e82e400703001c1030401080044100040c420040051058114204003c0b01d0382c02100b101e5206e4140b044000c2001c4c0d00207421a0050450032840da8404075500b0f0040341a40700699910030140d8042109504045422500001e01030300903040c142c408001d0000c02d44243e111000468001c1801113050815408688084141c0c0b620307a03109608112012950350030110b14071080702e2030790080b0480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 440414019 1250 440412769 440412793
    0x3100b010f120603020604032001091d100f080f060601020613020103200301091509182303030f06010210052202030304030615030c0f060806011d04063005 68
    0x1121610300d811055183d10300040103843d00e034090009076200b26a040040d540081c40c032a21018400221410800c00d11010868806100c200450741141c6144c0788800d66140d1103141801812907004003008141904005086400840c1e142c22811420098541075120b0100480e540c031010b940c86924041407180c0c0200640c029071000c01085011481100e89150119401603a03030800d07446650b10640f81c1600c0441d0000700d40100c4060191500108400449048440801c0c603070b80e10010140c1203201c0d10400e5155040c40b00400c80c21032407048a66a103049440c1030400b031401d503842c9026100d9407000400305a6203010b02c0c0d100309070342c1024000d500740581004e8a03d043d40036040c2c0e052b000800c804030100b8058029820344c00d0700e41c2c40b1081181c1c694680042405030399440f8055840e03c92354140000c0d60300021041d00000c007480c14024040c0c59001d03944c82146007540983d48140303072060008004101e41480c14501003031ba014244691044109905122810000100140c00000e80005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 440415269 1250 440414019 440414027
    0x406121e050603010b030109060f0624080613020d091505090a110418050c011403070905010f0e040207150f09031b0302070f0308030108011a010e131b080603100b010f 73
    0x192051000f00017185800201000c00c0c01c40700c03100e1082e114503442e818180315808041c0030350310003003030102066801400301c13014150829a08220960130402c100740070600540d80e04030041b0400c406c4144c215503a10028100310010880c040c0200c4605902d58840c881e01542441001e110306d80c40809880304c26103a50b83c60080702811950b2507807103540c1b04140d02d24001c2d0700d1080100d03688100300a01c0000010000905412900000f2000490f400c100b0026210b5020b0000000c1360800e003025100f40780c60400a45140c40302c00007044e005440456000180300c2e03d000480e079000035828003004200c45103115501524490036010300400c0f954800d4441590480d08810107040c0684141c4070031a84583d220031a00c2070541c000e9410a03804801405a90028402c0180d0202207018a01c0e507a5900800070b040e001c0b42d00d800b079202d0840700a5a0420890750341101a580361002003040500240a10140400d078060303c03070500070b20462030541650f8010348585000214141c440903259540454129 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 440416519 1250 440415269 440415271
    0x10612030c06110d060e0603010f27020a030602031f0501020705030304030b04080c06010303081506250302100e030a1706010212070c09090b0708060a05090a020703030b03120406121e05 81
    0x6003520400c004e06412120180f0655000d0310002c4001c0e1050709020003054203403544061100c11b024680a041540481300000c140310ba0a091041e00e102d40302140000340c04c01100d5803000d0142c47c0008208542925080b804003403d0702d030001804015a2984012a90b5045074018250140d00c01c00051003c29054104582c2c40780c0300e08002c1c1d190061441003107080c140c00303a000f05c001c100e100c014890185502d01c10400851020b82e0598104001d0096006010b0040c81c0c041a9201d4a0200315051600c2404904140d02a882082c0408024568a159264410030341000010101c0a001444401280c1242e0080e80140e00408044144001100319039010460403108070b00369000c0010244920b010709070996000340c40704955850300707034000341001000030800e91094098030014801c0b9511109240d0b04854120001030311240d0600d0140c00424100e000c4940c10b204d8107c1d4004e1844600c03006009540141c1c1d10000c004600704220402c1d1020802c1d82645101001521210030003643c4c006c0f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 440417769 1250 440416519 440416541
    0x20c0309040204060306050a0b09060d05040204090f0506100e090304090509030c06040b060f030c150d140108060601022803032a090f06021b0f011e020f010612030c06 73
    0x149103000034500009080764040d92100021a445207000c004a240424094008001200d00c562600b00480000303401403241d141168000c5030364902080a41d29a903012001c210b60061002d01303040050300b072455441d6400c1b180140e40703e074400c102044518049000d01d00454038030300214185406c08020368090200100b214007188002d0198a0503058100480350045003c0c21800015092103810700c0801c1c056111640d009602c503603070780c548075100d94101c0f4018510310344109449080e98a01d41d0050309a1000d0f2244c4904050f002040a10740407605602a076400d0b0200c0300d0710aa881c4420800c0c04c21640c0500b062107000c280540468002d40180d800381b40c054074808801010070705a000440c0d14800f0398070000345402400d110785040c04110102422403400140306081040000c078000300d4113a4005c0e80103500741c0c112061385034004c026400030340010040c2c2c02042d403002d503170007581d50300500d04400441d82030140029140131480c000c2c4001c075400d503480e403600c82c2d41d42c1c403072a001e420b9400300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 440419019 1250 440417769 440417773
    0xb011e0c02031203240607060f0b0d0503090405130b0705090415060221391c031a090c070302070801050106030e060a0b01090522020d0c17041203020c 66
    0x200142d0381440100002c825992005840b41000c0c269558940160050701c2d100070070b210104001541d554060380c2007640d0141000c141c1101c400c294802408507800003a8000542d01a000c081110100191a0038002960f04209654900c50780407080150004060070211089000ca0300e4244104020711900f100940086031142c40201c91018049403540800f0051f04120400d610083c5440b0340c80160b60b5000c0415401d105c072108481d018010030141c00840d600002c55008000d06502c80403000202001043c0c60400746101c070116000e204032480440041c2c5002c1244101301409504c004e02c7c0f45002c4c02c100050f9a8050102005601c020350680135480382860004002400740180340c06410140c0d400308100070703403540c050716201000c0d1503455081d0410f079a03102c0f2a40e021a040007140d00031111404010a5400a901c0215440c9400c03500d96000141d4100c01c0e05440e00642100000d03130b41d894400350fa43e000c1021f410b03030b030650307000340b5500e61104d48000651080d0007500020b040301007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 440420269 1250 440419019 440419037
    0x70b0a090b0a061e08030d09030201110a0306050109080102030903030f130b04080a020d0905091f08070e011701050402090c03070e030a050706030501050102030717030c07020409060b040c02010b011e 87
    0x2101078410108581580e0700ea910346005001d20490b113074521484502d003090603080142800348150716800342c030b16141c0c00c0542e190000002d02d0b200f5080341e0104103144035006e541d070300c1e50310004000d48841d0040390701240350814001490f0f44c5c14802c691081c01644003840c1503803165884200d00c070001401c00d280c40c03000c461035180403813003c0114a001e14400c20310640d0700c0c0c55060001e8101825a080601840703041c002c204600d4480540c2c19511548107101c0c040190b007001c900741035aa40580040323200388504140483c2d45180c1104450580d28480c122040384500c0c075003000c5c2666022900250805110b001058528102501a607003100d141d00b0002004402840443e241103080782c41501c2a40c085c1d103003009859014481c03680034090a1000d5450704200d91203604c3b9903600c196a00c810f100380000041c008101d4442a0703251103600400c00d010209803400d006002c1c0c0a0180750701c1c480e601d00403540490034014403d01590b0031060719a020403600d405602c10441c01d0b42000311042c007280c20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 440421519 1250 440420269 440420273
    0x1202091306050405061c020d1a090705012c010c05030c0f0c040b040509031b10090305071502031b0702060729010506090105070b0a0f0e250506070b0a09 67
    0x254481140c0040100150851800b010042640e0740641501d0180c00758010100c100d0300110a071281c0340d6010798050980d00c01c02c6c500045030300260800c2c907a804401e2414480810310104001003210401d0741d034000b1818001c43c101c0c9158007040c10500c600c0c030914180030b031954011132000c6d4079940224156410140c1410507142811290034583d00103030080b02c06034016180603c00c00000d8502540e00300514a4190182e0340d40b4030030800702a4914480742a204c500b50800c00810421b010400d9050184015606c1e000d4042c0e0041c9008031620070109506a00d29452882680e20415110003402c5010900040c4c0d0041907021038000d031f8000c4002c0020f035000c95001034004d070031030034418034010243c088000103510800040e04250f01c202001c02c1411801d80c0d010040d101d1440c2c004550702501c1d207600b0061070062580b07072000900740e8288242c040102d803003c42d01903400f1643c41d070018021103000d618610184624056103500180a001120200d4540c0403490b500c02e403004c05c00503000500d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 440422769 1250 440421519 440421529
    0x101a041d0613170a0c03050f04050a0f080f010e030a0c0f08030c0309060a0b090f0a090c0b1c02040f15210605120307030f1805130c08160e01120209 65
    0xc885450407003880b034440c407040182c40d4444450300c1a2100d0903034144903400c03070020060780b2010406420028042502c8a44413910f00c01c44009210040403403804654880401c0c020380140e100e42140350045002d56483d0340410700070745180c5045080614a8102d03840310030f950a0300c074020141e07a4a000380c0401000211000300540c02401000d003160340381d00c1d143d200a440c000004055429041c204445040c0075101c11010982000c21800000d80565031010340400601001c4000350464009810000c0d07180b0300d2400070491825645191414511080b480100740e10840c0700e210520004003404001003101d4842441251515203800000d090114010343c15180101c58003000143c0d0b22602040303135103440b90300034410001c0f0502071400d16a240d100902038054681031441802003040b00c07110134150705848034020709001404442000c5d000c59064004202c0c2e8113038200030a4801c00030038101580c3c525080701c1030b51135a8610300e1502412004683e01d00c120507200c2943c3e60203024000e666a69 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 440424019 1250 440422769 440422771
    0x408010e030301030c050a0e01090914010f05090105060406030209340e0a0e07170405070506220f030b0424020d02031608093408070602101a041d06 65
    0x303140000c0d5102d5045003004800c81002e50301440c0700d100503c1c000c0101501a590a9044407a10800002c10f2500c80c00e0141b11002d00b1032202440b5485e21428489800c1682c0c0312902549030400200542c0c3c1d603080031f000448045002c06035101e14110f0000302c106040300304100071034201541d8058181d29250950161418100c201800b0804a000401c0b036401c005142d01d0040000001c03241c1c142c10540c2004c3c0038100d03d1800010800e0103000000c00780001000004010070000d4801c9030381d5403c902c015683c004525800d500c103190708070301c005583d03000d00500509694004055100544480c3c0c0e07100b100d8202083c0c006403508102038400004481440585038001640102682d246018040d45103080c0420000400b44003506081c4402064002050b9200d50f100c070004940f021036483c1c1c44440c6070482c020f1000120b484d080c01013100d880101d01442128800e07000c030749807003044040c0c01c1c00b07841200c00340a410001345940c4140c41d1038240c01401245082250450b1210843c100310b50602030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 440425269 1250 440424019 440424041
    0x708130b0a020105101202040b011112070506010806040519030c020a0308040918031d010905131b030203040809010e011101290307080a02060708040f030b07030e030a020c060f040801 80
    0x6004505030780600d0b028000d40d85c0c0a03a0240044290b00c3c03c02ca050b010f0030b400028040d0185039154590785c0580d000f0490482c03005003650482d51604000f8550b8903460740891401c0390140203442c00055440c100080040c000c50b4048080e20444100c4004880d40e010756400c1a810013500f0208500540c075110080b00265000399580c903540d81c14401070409a55100c405d000c0c038007116540300808286d0141d4440900c10f40e60032000312185841004864a406581006e0343c400d400c2c0c0084401c4400c2c81d4425601c11007004210310640924a074180d080703001c01c5034003401d01641040048499032040881180b482d0f41414005a0294079413003441c06c403210425170954405d61070b1042c01c101802c004505184440c100c0042c270403076061a41803901d644400c08001d0040c8c102003081c44c1001400c8003501e0181c81c105e16002e84c1c081e52070405800e0100e0035208900401d2030710520100f01c2001004039480201c1a400a02c0352000310300501003142d21051f00d083d1081c00500c004100e070322007030091038820b00d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 440426519 1250 440425269 440425289
    0x3040807120c030809150403031109040f021306050f0f0901031b0201051b090d060b0f12010501050a0603060e040b060319050106170f1c02120c010c09140105070206070813 75
    0x26002d481c01500440d00503014810b203501415000801402c0041007540c01641460007243d1002c01e9040249207015a2140b503a2150424001c07000c0c10220380e001c1d041900707030b100c1807038465035031440b06880b203205200c03007040e815404100c0a140480820001c001400d4189400503100941c1180d800240903070381c28820043c1d4485081c0410f8110300d000f030042c039400b0040168900100040060341e0500d01c01c2008044640b100003043c3c80365038490040e4003054010702008580003044034118000c0c0000d008441c8581c014410100707480d4840c2c440d80c001e40d60f41340c00389440c0b92126111050034a00090206a00d44035106124407c03242e80390fc0c0040203445540007050a504290190780b0740e1050202480703c40d03000c08203001c000280000c1d00d03404201c483c2d20246000c000058102d00700084070135186181500014051510f0a0550140302e214155681e00c103409500e0708244035503018644081400603001307100020240c5850001032100900c80e002191410b820110502410b0089030301c2500b0030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 440427769 1250 440426519 440426537
    0x90d02061b0c0a060c020423040305071505100e06040f150503010f0e1e070305070f09050702010b0901060509010c0b011215020c1903111203060a0b0f0f0304080712 72
    0x10300010002d20700030100c2180c0c0c604081d0f007848001440c80c100c1c20b10191041c0c1c1c58038038507003a001c008200546140c484440da6a06403030582000f0700103511151046650080d03003c2d00e04004042841000d0142101100f101800707440c2040e44556408041c11a56120742c0c2e890300d07248d100e003140c4149213584d8180c5070b0510100703282c40c08040c01c641d0040010300d041d50500f1314010850401007101c0040d510410155102d00d62b241c0120751401c81540c00040291050b41c6011904a82d520f14070703011500e00d034102380b00c10358909004a00b0303036512001481d04050001c006000c000d02420140ca40d074103041c03501d43d020b01030507140c00d0444c080c20b80c84030095868403a41c0301d091080004104440c01600c030019464040d1044110740d07108000013a0062171600e401c01d480400d40324130110010491002c040325a0041503000c610b9065005481d0380e480740800030000181294404141c0388181040c0d2201810300300e41c07404ca4191030781300610890305603804100307490001e42d060341005a01d00c02075440c8025 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 440429019 1250 440427769 440427817
    0xa02030a1d011e0902061b03120a02090f10020d0818031b2e11090607060e0609070b030a020304060e070602030307080c121305070906063908090d0206 66
    0x35116020488500f9542440078800c0541c9030354080340c2081c1c1032203200a5091074400b05080c10b5003d0440300b182041e10500611a0102c4031740c000c0c0000310800c48040c0702000441e400c00095a40e04440900560000040c47d002a0b0199060961068000282c56101e131308040c40e960640d40007076002d81d00c04180342070240c201c0c00c00308049508161556812200135400156070794006044143c000b0340c460300c580c1c0010308254203009035118403d000d4a042d888410314a07110000e001c0214259155114000004c1c901c0840021082e00b15074200c181ca80c038544907403030000c020f5440180300780c5407103031183d980070661001000f0134001403106a02540d2a82404030004292030406803a810041b130782400080300041d02d60074841d4200070741c502520b100340c0b070b1450060b0410103568080d500341403911b400081d0386904450f18176003411401c0c101c02d01100103417010081131408607180319003855000e141d00002822040081111b40d10082c00c002c8a455954009505640304c1408100780100280d58165 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 440430269 1250 440429019 440429051
    0x5130e0c0a031509062c10110a08130b010803040e0610120915020a050a1b0b01051212030709031104060b09011803021c0c09140a02030a1d01 62
    0x1040300044481c1c0101e10310755200d2121688005204002e040e03500e04001c800c0050613440035040ca1001001e04900c140380c011042c3d00f003e9040e03800f45080c09840900d80c180f000900c940b010800040b0b480303508081c03c100b0b044903100c43c02049141034a07110b850000104140c0c5034018020101480150f175544d0510041c405010030144c4440e0050564000c10110345800c00400402e803013074102c002072172600500344007101d030318034941aa400302c0c0700043c1940c18030740c064014140c0640d961105540090361400e981d17440504800003500c008005c20041c021ba1a0040c008943c529103001111101c90440d8500841640252012404510000d1007001085122621400c90341012201008510300c0c1c11180320040c41440007150401000d20b0745c3e1941200c3c048091400f654001d8040c2c00a01d10300c8501c081656000401501e020004601c0044c0d06900c0d40221485850503428100007600d450010300042d4101810024000342ca440598400341035042c41000303004510000131a80c40c542c0381060b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 440431519 1250 440430269 440430283
    0x8040501020f0a031d03030d09080a091d04080a1107060e18040c0b130e0406150b07051b0f040c090e07050c03030123090c070606121a1005130e 63
    0x10000d41258540c40f0100c2e811100400c07005422103964481c0d0f6078040006420b61040071200a0030303034500f101c40024000c050700039081c840501d4807050740068540b800354200018081030611b20200c1140010001168035029114140c0241014a02e100c102c64050382411540d82203000002d00b080440182441e1a0b04140c0403c00164000304190070f040d200c04406906500a0f502800c400042c1d107130351041d020803140b000300500b240d6100300b81420b00e8148003400c00b480010900c00c2c60500f0108034840d50368100e9804070b902a00902c803040a05181102150071044032580c0700404035148011512a8003a003103000a4a03a0b9203022142401220213006401925800801030284420020440d0010882e07040d602c42e0781c800780000084444080500084200041c0c2021020052051000004000e01580d9108503030a00ca001d8491078822600b00c0d0094000d0704460341191425014048408555040b603450200d452070306031a200450652601c24a1000e4a15a2202000b41ca0a002c1c8100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 440432769 1250 440431519 440431543
    0x7030201380f0307090f0c020c030703060b040209130902040f0e2d010c0c030e0105070f061a03010c020322050901030209220c08150708010911040e040804050102 71
    0x100103428460980c1c00441190604500304800c8010704802d5403442c01d01c415881008003280c2c08071741c0724074900000d849843e610341c92044c00d154034401c0301400424016410103014004141c0640785803100d001410861f21040d40041d0300b0405009107407105da0950001d00190600070807203204d5407052008480f01003010040c4549060300350111b0407800324050305004036450340d10341100304490316a4140c1c072920782c450b001d0f50b1074940b80002c00f680000700141114080c3d10340341c20181e8071000540f81442400c00040c200803500c0754040005086902c501e041e05d144043c810042441c1402003801c5903185080340e40581d0001c104401003051680303107540906040c1e290b40203001d10300300c08144000c01c1800000d2003180d06000080c0d074010390352102a48030f03000c0c400d000c400451604013039240401c54000c0c0d40c5a805100c450032440340b074030328919014265683d2070407443d82c42c04445000902a01d0514110400c1c05c010006541c00c2c0002a03c0c002e9010b042d20f10390f500c0c84c007000645000d12032090 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 440434019 1250 440432769 440432801
    0x60504180210030b310501060c031701060504170f06010b18030c060a270f030c080c030606120312010f08010c0c150f0e030d0e07060e030c0f01090f080307030201 71
    0x13694010b44601814000201080e0074440c0c89513000480308125910b4040001503540c075040001940560100b85512047d0003a280c004c0c011401c0c1031003001c260424042c07000403c200b000200440400c40c8009050791440707900384c41504440104139401e102c1e00781d010310301100b40850b880e4039008600240c002e0507201200107200324100c08010421170f004007450034052000290602140c80c4e516000d211442c00c031001c04e100040c0e15400d240c088505903000c1a61a01e854082c04140f006000075020710200d401401000309585080801000d052500740c108064042404110380054903d420540a4601407080c8840381c3c0c2800b14050031102c9507210b52007000b13011642500032900112512038032900c2c150307002c141a4018106100500840e00fa084142d2100140a40741c03e9000e91011034085a05002d441e0510b50307035201200d040b50610205035054001000c18091441c2100e10010b44041c181000150f8555814031500400b0075903100c000d080e00006608020160f0a2281d403802040a080c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 440435269 1250 440434019 440434031
    0x1080c030a0c051c05070608071808061305030f0d0e0f01020909010603020f19020c0307060201050702030901030203150d0c031a100308030402010309080d320f0a06050418021003 78
    0x20740d042402424458a400341c55132180c101240252580900016030700842140e040380d40d07803903004152300000c0710b8140000300090b41c402d41c40314015007080121452000184640d403518400c04880250b0ba0a04541c00e1004000c4031102d8900c02004c1c0004544065000a12802807000542410b200031604013036a48100a400503d0740c480e60043d054038507034680140c842400982d06140d9100c3d4205011078010b0849034a048150b0000e40d410303201809400340c3c1c44440d038a41080c1e0a0f00c03820b440800140e0428400c1300b6041d4841c3e40034580c4010701c3e031001e48500030f603240820030000703c044051b42c0400f20101c0c207200b441501403e12854103100c0300141e4144c03502d02c2e1185c00303950350f07404010f0000100002040941e842500702800706604440180d0361074000410500007090140c148140c1c0050301c00300c0418801c8007000802c43c1201c54847c180c2c4503607814001240802000b4070008550360f55040c04a400c0d02c0d144640865100e03c00170f4948481d500b40100800c84000003040700406003000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 440436519 1250 440435269 440435273
    0x215071709070f060f020106031e020f042a0512270c0a06050a030b040c0e180c0a0e0109080a0501050a0b0613030605130609200603071704020a0306021201080c030a 72
    0x86207070004ca904600d0060380c800c4080e0b00407805010994000341074500c8c0313482000382d0107041c0c50b428580c051003182c02030000c44403003051000790f0f0380350b005141d0824400c500c1d14009842c8000918840c030034900e8251321b040d04040c40041c15000583e40010764840d0b400050840700700810748080440150300003031500b000100002826030b50b403400352104100c004100400d01c28007a400101403420010300c01d020400d201c242c0100b400300b120070400d11400341c440d2030010300c040e00028039001e10481025585800490901a2050728070000c0b11810407140003c000b45c4088144401c0119604c00c000108a0703081520300d60094615039440c562140004006101d0000248103204c002c41b9070085000c20583d84004003400c2c4030304100340142445041103110700030030108801c1d4044060021030b056100b15080000e120550004a4a01d03000c80c00c521512003c1058650400398454402007050840c0c5403a81d03920300503030300f06101007035020f4100f0005228103d0f0900401c440c1c0c03e0194010016001c540d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 440437769 1250 440436519 440436539
    0x6030d0c05190204060b030a0e01060506070c050405130507030530092119020306010605031b070f060e010b0a081f110d0c050a030c0c08071101021507170907 69
    0x7005644844542c21682038115141c0e500302c50002c006441303071a916031030038442880203042c120100c40515441c19402281604e880c00589002941115070104403508240a0000414028200d1580800c5021103100004c40810242020310b108002914a848031404004001c000078140084084803d110982981280100355040340c84200e030815104450301c854441180d8465410380d44600900c1c042e25560045c9100f43d41c2d10510940840c1e505a0f0307501d204413000d000c240c889410b1001000c501072041e0030700d20302400302c0c6402890210545021961045d0488244041d4903031165140c01d980754503803a16541c5400202070185c041c00144080304a007410786203048a018a805569070341d8400c200c24140c05642e000226000d0801c61113507010030240c01608850740700c0c03000a0502c80c06482c032503c40c405606006030702c008400e0070401c095031102588400211148e0440c13041144000b88811a20720950140f101d80d00c0b010f010302400c5c0d04e4580340c070070024402c00003a448814100610452 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 440439019 1250 440437769 440437783
    0x1020c19030306120b0a09020f0415032a1211041401031103010c0819110403061b14090103020a17010308130603091208070504030c0303020303060a05040c0e0f040204080a0b06030d0c05 81
    0x42164005287c04a03480028a015030007104c2c01d411901d4000050740e04110510604166400b1b0075034920000d038041140124441024080e0130049000407040083c1843c80160711406446018924100811800407900f02e4a0b2110008004180040100140042c0c0c0c0d010700041d210640c000d100b00d95050502130f140075405040641c0001100705c00c0380d000c81180d8420355400403032640392569281d40c6d05041c07010b042003071003084c85a161589a542d00c280503124280b5141e82450402c1c0c144126030005400035000707041e20206100503122486101d48003003c80501031849a0296071300e40041055050b013005558000e1414589000c80000110310203114503900c85482e480e050b225950f8007842250240980e9000505159060202208040c0c0120180d841000c0541d18400400e90310300400050b0307120010b21001041d000c011035009070402c01c0c11080c1000c00076101602e05540e40404600e00705009400f621a814100240710040c6020b115240303842800c5c0c58800100c8003203440c0d098079101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 440440269 1250 440439019 440439031
    0xf0b10080f13140f0c010912080a050906070c080705030705060301030609030905090f06040c1b0303050603120403030504030b130203071710060311090f07020c04020c01020c19030306120b 82
    0x4400091102d20002070103a031516840044100c2039561100756a41c4d6860000c01c15032607004088182c0100e5110f4450041207900c0380740c190450690343c0e1541e11070350f402540050100038041150580c1c036100c800007000c0c880e06c288031340c580a51924220f5824401c9a0300128400d42041030300f00210340e10b10007502d0640b83c0242700014221450b14003510800110352050360090301c0700707003004207031030701660a40e1156005980500c500c0e002c0107021202c400707030300e10f20040d1031080c1412100442e210780d214590000010b011910340a40d00d40d1070b0707100b580003507000318001000040d040c4100701210804580200d40500c60906c0000560b00082e1550340d14054542d00c0c000112511422510030800074440324800c101c00c005654803070500032440103002c072005010300241d030003041c415400c811140344240d01c1036004d818203000c408100000ba5001007005066036409002c1c69040d8141401461846003980346503071842c0080d458090b007901c81030f92245290300741e08000c0a010a40e0929510380c018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 440441519 1250 440440269 440440291
    0x2101e050301080c0111191b0801060b0304140c0a0801020723030919050405010b0c010b0d030e0d17030108070e07020d0f050a12050408180d260c100f0b1008 69
    0x140b0f41d066a071034001060403a40590481d20007d01c2030000b0711001c51500d400c804841d02ca2143c035100d4090982d60b0350b10580e1861481000020041000300d0481000d041c01d03002910018024480010004506908080c10340d940c005010350401920314415070011400001644a54420310f01c0d0a46078069222041e00484610015419012003c00e5680203404018010469541c444180c9001d64004a2044003198a8181010164a446604194055419950700c010b04540c8801e114600c1c0003080101da029200d080000070b08485280a54040c092460040458610f0204161003a22010f0000300541d040002c0074044242d1140e1003100c218042c0c180550364189000040300c1801036420003409851501d0144030400c414038004207103444180040d20111071801c0200b040300d4090210003040700000200407803003a40c4590890903401e445000243c2000d00700180303a420003401a47c0300c0149566826080c003107040511071508140300035a40c03004032503500900030b8400140039003141005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 440442769 1250 440441519 440441537
    0x250303140c03071a0916140103020918060103060b16170405120f01051b0d05090309130507120207150510090207050102040311040506030303010b031302101e050301080c01 75
    0x30031045007111480d140c2841281c0d0365002c14148511600322821003820305942031000b1071380c0070200184800c00000c0c12041102c44904c1c04948403040d0740c98031640303814150280716a64080e5201c00d80307005030a001c00b07851001d6140080c0014100d88441e0402c0c5101002884041070b1003000c612000e08032540200d0b904070280e00001018524081c1d0343c40243d000c0001e800c24080300401050845a81c0c1c41c01e0001c1c0141d0311900d40001c10100d0001355400303e2181408992181031080d0080340e0004580810f8034680708851300801e007941942c3d001d030660652140c0c14040460351040008603912400c1c80d045040045623a56000d9102c000e000042d062034490020403980d04400c14250001d14084408650b140c0051070514041d4002e48002e5800d40b0302c4000304c00b01e41c1440d009141c130440004002d117146a0801034a0300c600d0700058804589075030b005021200603100c0010400750070800392200c00031440c0c0032669805c60448543c242007040340c1440100b0100c1e40000310005000000d08100401d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 440444019 1250 440442769 440442797
    0x90c031115030703020d270c09060b09090a0f0212010f0501050f0304060b0a09060621020a21090804031a07021501060e1909021e0307050a0e12010c0203090102250303 73
    0x180100c0e48801e19403c80c500003440c0701f080c111003c110400d200d084d00d6a02150340e04d030114100c0b10181300301030300b803070f01001440c13080d140440c00d00d90700080710040041c08500b0881100c08076001808062100881c520051100400015a0383e00424091038003a19103131246404403418000944000c1c122601c81d00340c40c1096a40c0e020140160034078003c10003070710b40c0d1100010035280310450754100e034000c0001c000000580c0f40c0215901d000460f15000041101001100400e818250305400c200da03a03142a103001034181c00043c002075000c1d010f4429040c86d40c1c0c5030786844540181403001590711400c0c5113600c40600c9540c0d01d046031114201141c0484450011800c00c241e4400000701050b4981c0d0040703034020950b8040d00510101c451a4082c004113502c802c03032540300c1a505a40810400c1c046030b10340912030321000403620340142a03da8845030000956003954000c20284001d60000b0031101c1d481e582c10844031030981100c0c01e101e403540c0380b03520307900d4402c854500014040090001004103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 440445269 1250 440444019 440444021
    0x130f0e131e0f0606090b0609150306060403060608032a0a03050a17041a011211060d0615020703110402180613080a050606210d0c02030f01090c031115030703020d 71
    0x4442504541064000301c00352510340c004007200c0c041c17a20010300c0d1014007030b40f509120007500d00003080a400030310807208000042d00a80c10007404107502a40402010001501c1c0c0e01410b00180000d400079a103c01c5d414a850801441d0702c1c1b5490701100f0880c0800352202c00020321601d14940604040d40d0381c1c1400c20382203620400e81c15504400001800a100070000b1044040032800550803040003645d0300c1d00e0446e403445401c01d0000d803c0c003410914903400d524280c0c0c001d003481500e02000081143e81c80068104003058003400901582050b02e0810a100c04407080342c640724401c540c110b250000704041d94080b0b02d801c100180c00b0740c1b030101c2c425042c6542c0c99041c3c0081d00c0303094100c42d07100c1013515203507a03205400c45403e0700400314190700d0100803082c024030710505481400582002000e039801213076804d54440050b42e00d8800c6640a141d000740a1007101c0e02d0074020005442d2590460924001c1c00b841c807802c00d405020480380008494000c1c2e82503a80194180c81d001d070b40c0e003440341d601078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 440446519 1250 440445269 440445323
    0x106060c031e091d06040606020d020d0807051303080903010e010204050618060d1b030b03060421090e09010903110d05030f09011407030903030c020a03020601151103130f0e13 77
    0x31500d4090007032008104002c0100340c405c10080300d041c8215174445004076100c07500800580c0c090b81c412083c81925900407509140e1000003498243d0a00240c0702c0348044c0c40d09180d00548107641c00044c01c140c4d0381001e000301050b1001781c030000e519062900340031404078403a06803105103070122500303200c0941c0d6480c1e0484500160300c1500388020b81844101c0c000c0348589064400100380350240c00c810609010030701e07510840e04209001c0980140354002009407039807800d55810462020000308981e020f1280440c0680d001c94000141d0386002d180c0900f040320760a0024449134001c4c1044410181d101c3d040703d80c0040410072101c001d072150884a130143c0b0101c2a1020032594030f204010300c4a42c568007220566009590600c465030a400301aa124000068003900682205c4e0041c40400c0da515146a0b00c0c10302854040c07401d881e050901410768000070103441d461484540104165811050b08030301070074105580301e103241020b400080f44034031180f00080102c418001c1e26032001d01410840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 440447769 1250 440446519 440446529
    0x2030f0d08190e0f06010e01120b06010e04021b160512071a04090c08100b0c10020c072705010b0f0a0c030c0f1112030903370606080106060c031e09 65
    0x1213184820896406403039010900800c511507070418000129150b002c1840c01085e5003283c1d1010854030340c2401150208605240c994020703408000342e200500c9582031140c00c1c001104050305680b2110076001c40c0c1c001882d84142d01c00c400f084c20f202d25880020401000300d80d01c1d500c0e00030031828950f912400c24000c82c1e00c6040c0c80c0d80b420907480411904208030911444586441c0f0b0001d640b501e008500034022400044040e0f03001c050000c06c1d074001a8001c080d2602d5800840e005140d0381c1000c2c07056051540e4880d00071143d001c1c41900c0d045460b008280c0508502c500050801e00030752031450241c0640300e0300c0700400c01c45104560506000f4950003003229004003001c1410050340c00c0110840d581420403d003c1d9454150175282040040191a02c0c148020081d08031500307039250f5005050744102110a0204040d000c0741d80c0c211800c422a82150b100d203101150b094503207580a800c42d6001d0380700d00148800910100d0000340d01c04040522418018080350003802e01078012210f011a40c1c000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 440449019 1250 440447769 440447773
    0x20a170c040b03070e1005010f090b03073209040b09070c080d02070605010602160b04050a0311150a020604052e0507140c0106090e0a02062a03130302030f0d08190e 72
    0x81c4903010346e542c0c20b103105a410130b803280c00b6001ca29000c11917844040b4070a00005000a00209038003e20070300942030301420b0b50f080002412807907841f00080c0c91001c001c54210b4140000c50240c2070400d03000340c000480084030b40c00c580f40b400b010060010090300a001301184000501c0741c055080590580d104d15070484002c01c02980c681d44082d684014108050310140c58a040000701d40c0c101408585c2543c0c4041d0650b0702c41451580c031207152011414096034014424204050f02c0b40100021306080e08082d80140902d05143c20100d060041150350801000e540e000b000244421864130500103144001c00007031682e80700b00e000c46e0145200b50107480c04410000b039a91100c401500120b0540d442494104000302c1c0c101e520310754031240d03d00004c0d0002c009002c00c51014141807595060380742c1e200c10010080031740c41112410b603408856001d086070700400051003941001c01c0307040341c0101c031000240341d00d1000d0f00e13018049000060403060103000e0030001c3d0040403e0358201805400786182 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 440450269 1250 440449019 440449021
    0x60807020a0501180318060e040b01030f090f0c0b07020109140f0301091b0b120a0902060415031a060703170919080a030c08010b04030f110913020a170c040b03070e 72
    0xa41340410702c4001c9802e40018852004144401c01c8400c070700307002c1300d40e0307a115a200703000603105210140041040003410306586428001d50b0100798003510201d81d220740a88003e03018546444c5e441c983c0aa042442c1c9001c0a1050030010303600710b00c0000a840344400340c04014400c560004200d01e034501115a0954240b50000d41003041c101c0241224150b5082c400c000700307840b04020023030b0340150001001505030348008298880d03200d80c06800c46900281c0a2441c15840c1d26195030301c0002d003c81040003075680c0c004440310314883c07058044082d1041710f900d0b24062240c0c5000301580e1442e0b2088040c51b000e103003c50706161007049050139480e03003c10311456031245070514032041d0300039a9010000c00d06042c42440014800c4c054641a6403400c00c40c282090700359281c2044500d041c0c10f0460f02c402144400e1445940d4503225140f2841101980068028481c41800510201a48404200c81040501d406c0148020603403c802d00025180041d001d212000080e141c0225548a5111031141c08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 440451519 1250 440450269 440450291
    0x406060306020703170601111c0c081c0c050c1b0f1c1a0103020109170c090a3e090303090d030f0207080c2209050d0c03080f060901060807020a0501 65
    0x81e03c4917540c4c08814804242e0740310801134500c0b040858504003181c22401c1700d00403411701c4000388400c6d000b180c03400840341c05145c1e0b180001a80126400c401e00448640000c0c0080d445000b900406002c46ca8100d00300702e59000c206950340c500a003410168240800360800300e40b6040c16807550340c04000c100e0003050005030100c01c40780b44400c2c81540c080c0c0c2c1070089001242402e40c00e81d8101da034103a451040307807031800301c200090b2042e8681d030781001d004071035000340340c1d030b071640d00031400780880b0b00002802241c00071203003800101e409048400d20188100c0a108910b4a81d4460f007141c2c84d81c1d01182c1e4030580c1d000080c4c11403280d00001075010046101c2c00c810b0541c41706405100d14032640884601580314014150b44240344510b031030b406868402c0c80324040404040b01f01100d004508003144211441e541c80382801c502211100014022801e041d013810703802070085030041056107110318942841c40100c0d520071340c140108001d101c2c40c100403442e0342d032007080324418040e0448020414074a0711 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 440452769 1250 440451519 440451527
    0xb0d2307120609020705070b0c0a050d0e100e0a06050c01060f0f0305060a0209060d181401150e1b070c0e0405060618090c0f0a08030d020325090e0406060306020703 72
    0x180901c40026031409101080501440c0300b1203441d550010001e04000b0b281c031900407107550011a41c80070074054900c0001c001001002108041e82e02502c84880c501107580a01c1000d007400c5d40701900708580c90300b031001c60380c0782d800d0264184d6015103421562050780c608914058811a40205291103e00e840015903000002340301040e05e1080041d9a0075803510301180702a030081001c0360740d1081040040d1041112103a10003060849005414140312441e912460007601d100355188803180d46075642090200c10340a45a409414440150000e074241043c503c084181c2c81e580b96280d241000504400b800003541e130140080c500b4008006172031401b0301c0d10a4a4000076550103008a21484448074440c200080d0039228174503404c000c002078214002040340500600b42c1c15074201d260f01d04041590701d020b000925800401210159990800d81046503007a0380b18407003102d1560500c2000c542090b0701c24800c20484106113082e10040e125814800000c0c28541e100030300291001848008060308 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 440454019 1250 440452769 440452787
    0x603140c010221030f0618130507120503040b031005090c0a0e0d11040c110a0305120603030f0a080a3305060f0403030c0f0b0106090806060a0b0d2307 66
    0x282e003a54a14025042421001032604007580003955040c00007030600c0b1801700f8003030740c0510024400d006100c10400381c018410000e1b144000300212001c1c081c0d06202d8100b0644000300748107242800040000e03200daa03124043c50248019203000080070070a4100b504403040054000107140030402c0c00c040340110100c0d40b001e1007140204903040550a9646800341d2000b076115000311050140d00054800c11004121210685003804800716540644540c10486454814803e84410360303101e02680403141007040050400e8441d42c420405c0066038806402940e0703140c2c14609203521b0903120305d0044009445048810011042483c0918143c0c980c60400045809003540503508456150b50038040e841c0b050703e142e180c034184200410800a841034141d40745d10790050980426800040c0d44284102c0b1080e03202c1d00002d02135407824003000c04280012174100c441120800e01ca18a4225011000d01030f1000407640c0c1583e802407a240301030308800100000000d52000c10f90b0f803030440c0000d468500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 440455269 1250 440454019 440454043
    0x21203030901060e0708131403030112060e0304030302030708250c17010c1e030f0e010203100905130201140d090503130b0403020a030602131a040e090d0f050d060314 73
    0x3c00c28200107a0b40500060b00760003185103175074880c0e440c1d0319103840c0e0480c030990703071400c0b113036400381d500b420003220350610107103010700005040c3d814a1a054145a019100c50043c0b61007190001c002c100002034000080301c10050303010581e1915100d070030720343c8100c0b0412480103603091180010518200610890090151940414008600111442c4c5039080743c061181590118071030484e84a5091044402000d00c03070180c1c070b0007048004d201c1c10300c0d60603610502d0b4100140d030340210512203a0342220725004003800c45001c00f00102e191202c5910304009106102a052250704140c8900076a40302048451f16441420203000b00e06991906076503aa0103411651000c128040010804002440803201100e400400c509a09030654940b00b00961007284489903000c0031180c001030384000b61040c6440328418036400b94441d450b000d41031610b00340007400040560401040800c0b5180c011a0791329107803002d8030b0119215281c0c104141c005140581010b0329416075074403010380c070031400149030003910 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 440456519 1250 440455269 440455271
    0x603061d06041a09160909030809030f120a02040b031627090f180b0105030d03020301150f02120d050603070f06020303010605130e07120605030309012307021203030901 74
    0x9109020154482030240c41c02072060f08041450340180d00d5000300729070070100394810340c5c040440c684203414400c885a800480c034036444004107410315400c200301540c08201400910301d840803060b142031480c810b10040e1486a540d420100e8000411981920081e00803c44c50f5503990809000305c400ea444041b112900049900c1c84502c610061820703990300100a5222800045040501440c003920038941f1031440c0643d04c2d07003690307100c14107054500d4042c0e005920016065041c0700600d4203100700d5035905400e0500400c01000b42c450000c25400c924a0280703004001d64004040032414035200a1007580c9022000c242d4460b160038650105004000c110102d50b09035035074407004d5990700018400e205c090b80061004210703040c003510051004070400c01020f0a0309803107049040e01c0c45000c0d6220b0001600c00240f16000700f4040c424200606001c800840c18000e800700020608012064184c0d00840e062819074411504601560300319039004041030722045a40280942d0303500220796810040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 440457769 1250 440456519 440456561
    0x4020423060a0210090204090209070f03061215180204021c060801182d1128050d0807060507080708130f0308060d060c050307020706020304120f02060409060306 71
    0x7450300c94102c40d038841c0070382c01811601184886071030007040c00d8070090341c01c60b0301c421100006983d0a0300103072240c0001c0c3c0b1a00d04002200c03000404641c9150481020306900c0007800c0c0105048094500603401c03041300c00b06040c0d4050354140704915103001c0080d00140007003200d030354051507000c99840410102e60b02b0001a036440c00c016081c2c0d0b49604035106403c44840100002c180c0303000031814401d9000001414201d0000c000d90b0316086501350035180c20100000d2000c175407030125030f003d40d007820b07684100751105e02c0205190740900c098881c0c10f00c02d030313200542002004003080560b2000c42c5c11103001c11a914154202401d01001201c21400003810040000e040a003900005803d054204003270b0000400c0645e410390300c03800064030030341d808403100d26074a00007501340c0030700c007004c20640d529103440e8201031f48040d141003100d0f001101903400501c0140010b01c0001001009250090a001c44194050000ca03540344110b0b0000ea09080c10301c00c0110900140b904031443d4044000c0003d554 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 440459019 1250 440457769 440457839
    0x130c030b041b0312030b040b090c03060a0b070f170703080c0c0709020f04030201030b011704030c1509240207110609060403080c0318040c0503070e0102071d1f05060720040204 77
    0x1111000031006500c5401d00000c0f03000120203a01542d404070001c0d110710101a1030380343da06c2130307073f002000112200c4c00305000a404200342c16031000610082445001c1c20306a803550040c1a50b08020040008000b010440c1c28003640c081000b40001c0c10103240455641d403401a840d80d060b4800d00041e0b02087c00d2403518071007035101b60110b03148040e54281c00384590300c0700e581c2281c2e1400d450340156801c404844003030341320401603c204c854070351264406106800d540135020600f5030703610b0316044000d0700c10b0050b00c010500c1464031424065048502c0b5941341c00c4c071400140540038907000540361101c04a12507102100c004001c2c11001111294011112816030420044e1050610803800042e01480800c1c0064001c503504841d070740050041d514040c1e03c980060318107020005d00c29840a0784035080c403082d104868542500220424070801015080c0400b058042c483c01e2402001c4040b08803800080750307030846003400e484e00d00620565955a885040c0440c01241e503800c9142c0000c04911091 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 440460269 1250 440459019 440459021
    0x1f1d0108011203050a20030703021b010c03180b0a08011701060f0e250e090a0b03190c1a04030203100c0207170c030102071208130c030b041b0312030b04 67
    0x8100c2d514003031203a41044103541d0898841c0c002041600034000b4030b48068002c802c1022414840c1c010359002192a046182402403400d52510900084940c174050200907603640001c0590106070141056201e42140e17141c940c1e072004081e40a102d07402004540800c103541c2c001c100f035048491030414540b068148401c02d07802c1303800e0740c8200d52410845010030410360314220f5039140d00880c080075501c400e030b580d501c1c20340281b0008114040014204a00c4120501d40565990342024603104204500c07440b402c0402d61302d80e00900c92690510a0100032010890900090400f80c43e944401070000c8070600501150350304603000880c803a01036042060b481605c00c1c81140704141c0076600400c02c4616141e1018412098000850910700840c03001850a4500340010710702140b240700001402e40203080000e21803038000d0308800d80070011355001c00115041580e2002600e0b00405000015144c2d1300d0803540f800c4030070510b40e944143e03c20b00002030000e071040405640c58a6103090113501c01000c1084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 440461519 1250 440460269 440460271
    0x903030609011a0d0908041d190e0f0d030b010806010201021305060d0e011503110d05030f030a020d0c02060f090f0712020d0203030301030605090111271f1d0108 71
    0x25000410900104410260450001401c0010f000180e02c0d00c480121000c3c02d503030300104182c1c1c204000240801802890f01c1c0041c14600c802031140b2420b0404014011083c1c003e0440325800f103440324652511014244100c812018012044610040300c910000d005440310b110642e0103d401080011080d500600844110020400c00590400d0400d82001240c1e007040f040c06844a45d503290820744040c00344039403004083c050302e01030384061031481d100480002c0b8107402401400351244110024800101391256207458080c0c0315140d41e91003601c000280600b4524501c401e040210002c03002d6004100c41d40640c0c02c2e201103048554641d6003255840c071511683c1c40007070780100c03000c0040020031411482002e100400c091100005600020700e03681080e0410742d00141c2d1403040c404500400d100300c0900d20007088555007007102d03480b803550f4282c40328020301030312400c1112244819a074400038500391041c94250204500740b1024000c003601509001401c03948030b544a800e4481d0f018521403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 440462769 1250 440461519 440461531
    0x4140a271d0a321b010c0302032b0504060506030d030b30070f0609081203063a150506060304080714010204060f020c01080f0a15090507020102070506090303 69
    0x203141248007070303580381ea43c902c80ea90701c864000c0b100041034407000340c03c2c03900350f040d801c842c001003d61458810302c07112083c100500a505000028083c0707030020f5004020344058060015080059801d40c1d05070301402c4115a00c4d0100051400042004002c0c41d40e01003401200c0c258111601c0801001c000d50850f00c40c45032607640903403c901100702c01c102810f8100d040c545540c40b0350340f4003100c40800d1840c004181e006030400100b500e606000d0b5030f0348414000020a00700002b420100d0150f10000300c28030000d40310354011064070183d680201402148200c03a600c481d841c1c42000380b40200d50014071080707184100c500421012556071610322a008003070180c08000c1540d40782d92075a80e5007102c030340e122000c12501d0321201d04070360030010400c2c4042c00c0100105c0d00c0b40220408100c9000341800092840e09040c05002c41c10f000c1107144245407603a108449003400a003012404000706454400380c1d001015442c204010480c0709603064024101c0c0034451021200300391900ea0026889010455030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 440464019 1250 440462769 440462773
    0x708040e0f061909110910030507020f0d08010e04031b03020105061302090609010c0c0e100f1e143606011b03080601030902030d0309150207030504140a271d 69
    0xc0c05803215035400b51a0020300170b016079240c0740d2103d010804225000b41e9030004240da03a400c100040d40c040c0300b42216405908041c4c8020107001c0e201605500d0107000b888d1801036000c000608046c0201880304003001c030304a18201d000c03101e19009000c1c2004807a0395001e000e01c8440c0e011422014001c0d00c02c11030b0b000300003600301880356004540c01d1514410984100da5241c600180d0124561000390161600700c0f1500d035018101741c050080705d40d80d5072140c00755007103200300c1450ad00800d15080003500d810300d00440d0100d04450010304a109500c4198402c4803001d07010341844040c00c1e44c0081004901009040c0130f42d01c003c0196001c035004982c18140a580610560000c0d1051007415070000341414000358020207500800e10341529102440d000c0790380d80c441c02050100740d11081071214003201c401d51a0010683e4004c040c3d0155205560341203494010500380ca0b5a8011201d004d4996501c1e100b448c3c40e0365001200412641c040c0d403480e882c0c50891820150a0443e00c5d0302206c143d4080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 440465269 1250 440464019 440464069
    0xd0519020c0309040507090510081501080f040b060102161707080601060804060e070f06080405010e010c050a050f0c160e0604020906040b0c070816090b030a020a0b0a03020708040e0f06 81
    0x144805010001d044100b0806000d1000c5500d640f41584242703242250368542d40c03070b441c0c010200c0320018011120a0b0522400c0010420b8105039054600d510a610046500c1c0548940340180d1503c021203903008510a0703040004104015449440309400c40c202e01112030b8266100e0142c0d84546007030059900085140e400900824003036000100c8408001d0125501150b4440018000f500f49821543c0001c2e1880c003408140002406016651558580204000e201c9008080d203d4414884440c0c244030003c01c00f20011071000042d500d101e0103540030744400c1403401a00317100f0712409000c0c0710f05868080020450070f080c64429070760f1803200a069a8549410a99081000d42000c491013095120f0101c0214103002d0502003038035030200c854424112a0304200d00d000699011000c014025840b00c214403016986da5012035086881c811061030b91070300d601100300d010748034010713010b042c10400140c0003411000c014a103070300c2100c1003021040c090315a130040042207000f007240251003c003c05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 440466519 1250 440465269 440465287
    0x6110c1009150c0804091409060105010e0d05211c06050102061302060c0106180606050906160533010902091003050c160812070f0504091806020d0519020c03 69
    0x410800c08070010f040c580f0301804a80c1c2c1d899000c0e80160400000d0541311410307010348244194005400000c0f01e4040e01c00c6604004c00200742240c4900080d105065103000c10003401414481d0141c108400301071107620440d0003c2c0d451240d4401c880c0e030150100c15401000c2040360300d02c9048280c0343c0581c050700c071a49514415100c2d0b20002101640d0040d001c100ba03c501460910440000304028508181c54100030100d5104031001e40e0302c20403d00c1010000c641c1541d070f40c1400c603a02c084910401030084012030404a03d055100d504402c03881c242203621030010180d11281d07104046241200c1061a80c03500008003d0b40180c04426800400188104100f0f9001c0d0308a1a444900035007424204020b80d54034041c502003510081d07403403080000c5c04c44607a009080c8125441891402d21b90703c10580c540004007c0c0c407a500c2080c00e0959139022a03071200104424850701140c000c5815501c0740298016000201015a03596141044140443c02907000500951f0300c4044404059410300c3e07542 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 440467625 1106 440466519 440466539
    0x11181302040b0d0201140d0603050a030203070b06042a110709020d0f0c230d02030c090907091505131e0e0f060f010509010e06030106110c1009 63
    0x80c80f01d80740981d030424441c150f16402e503110035a441461f403046030001d003016000285140031304d90520b070a02d40d001024003c0240220380022840c0c4aa604201c22034481070340e410b0038101550a1841c003a10401c83c00300d0314940390f0800e810311a6000c1c846504081c0150000208a036002c01d00c6a000c1c0c02511030402d98031403448003003080408104000e000c0d03244000b8291240e034010304848101060300d0301030380d00b0140340d440255100d0a144550402c140c00c8008542d014499103c0003c6d0202d204050200444803241c60741c04080328156400c44407903100541008442902103030004030015a000d00c900e048100c020001c07242c0d41014280c0d07403400070190000350064044810700c240b42d600c08840c0a0342110900b00655a0303001400141c2c0c440c2c1c01d0280c030710b0344058080000500a9001144120315804c408240d0702d41c1c1544004006d0704015181c0303503500041440d14180012101c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 440287769 440467625 := by
  have h0 := BRFrame.cov_init 440287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 440287769 ≤ n) (h2 : n < 440467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
