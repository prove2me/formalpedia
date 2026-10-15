-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4533
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:12.521985+00:00
-- url     : https://prove2.me/submissions/3fefb05b-c881-498e-b3d3-9cd342fda88b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 815107913 ≤ n < 815287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 815109163 1250 815107913 815107919
    0x20303160e0a03120f090302031b130603060506031506090601112a040c1b0303020708070506011818170d020f0c07150804110112060302031b0102010506041e020a02070807 75
    0x2c1e999034040c104050307107178403180c021206020342e8282c1003480041d40c56009030b01564040c00600e5050030000c0c0008113817100313002a0b070710b200d03007103c1281d0015100e140d0780d4020400f881c10100855406020800c01700e4074940b0707243d400168041c0000301001c3c1004115402d5a0f107030700c2d0801501d4480311710b04c941c424002c0f09903030b500d1031009080001144180c1c20043c0b10f5842e180640c900c051403159042c0d1542612400c1d44003600a0341c4201004c43c3d04020800c050400704006000e002d0103000300400b01100d50035540020b9041d55003c5944202001030750250f080040c41b01601c0100c00041410150b84448001c51842c0003802422540e5100b000005050703511110046140000d80c1c0095800f406e00b0b804220045a04090480b402030013071440d070b1040541580689030840d4a0792200e800030600719221f03804207040041c80c941c2007612200103245810f840d030702130150b954003001c140c40401500c03c040020700c2404440810103200203a0009450035414403d00085000d0040b100880d81d810b40c2e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 815110413 1250 815109163 815109173
    0x60f1204020f1c060203090a0f08040905151c02042910030c0f110a080a05032a0403020d080903061305070b0f0706020d0906150e0c0307020303160e0a03 67
    0x102110124490894041440b8451801e0450556801140c4070070103548001562200000d52002d4100c8034544110040b00b80017801a5039000380442c821040152528901245070040c0d03032024003801505418050311401a0300c50725101c054078084890031001b20102e40c000301d001020f1031a0710b20110203d0f0414001c05003080c1da01c0c07a010507000d40d802d5041c0d00c0d04e50300c12400c45074041012400200707001f5100300c49e0707031054002c3d50503491580c041c2e07601a612503445400580c800611800410f202100704502000000c0c0c11003810761310702494a003800c07800f0051520a2080e404000e218068990b05001842011004d69400f102c0150450300c80741020507102040b0040040d044525200302035000c103008200c441603500707402903201104c0c01c02c1c92a40e121000703034000e4030041d403006d9950503490001c60b0403401561510b00050100e84c2486003030611401c0740b05401480502248020424020003e0f0300000303c82e80008000c40c1c049010807000170803204000f072421500d500c0403031400f012007408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 815111663 1250 815110413 815110447
    0x10621230106060206010816060f0905220c030c0813060212010e010317070c2c0a05060301150302060406050306060f191706010801030803090309090915130f11060f 72
    0x180241c0c080b96002c0c7c0ea42e041d0155100082100c080403103007a1081088150b006410401c5450441d08201c003000b0380790030200c2c07510101d01003100c441c0c41ca00703000e250008010b44542101d0080c5458240b0215044206c080d0103094041c2485c901008d00322241001d101080c3d0540d80b4120344010350a1007540d4070521017881140030f000c04e4501031105601c500d202c2c1c801070100c40c001648401c40c01300841c43e2100724008100003100c07100030341c020160242c3c44034001c0c004880c4070340107a840c00a0542003c4050500f105c865160711548a0f644040901c050f030380b000161000c039007c901c0c01036680e50700d40f001700703400f4020000c02c44e480385000308108242840c8099071401c50807082d550642900c0113802540c074101000c0d601e072408644a01d0042c40400c2c0040011940840141d003200e00c2c280c203400204c1d41d81d4074115120700603a0000c07800940302c07603440c00042c1d4205400e9001c400c40400700c0d842d10281003084900c002c103084251144e0f40d0650315050281c035208a440e20324161980554170000500e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 815112913 1250 815111663 815111669
    0x80c0a02040f0f0c05270f030105130302060117031608040b16031202030f0f0403090f1d0108030a0210020a0905150d141b0c1501080a05060108010621230106 69
    0x200341000100e02c0b070070340f142e4240c2c0c1040d440030301b005001c0d02c030700150100007003d091020360f042400c8140300519603e09000722400327030000c00700308468600301d82402030034500180c2090600100d00a04540d40c4000001620072102d21035540d0340d0403040368684142c5902c11075110224182c804507003243d040c202800c2080c00c50f402900d400b12481c80303036114070040348030440b00a03e10043d041c000c0341c3c08005039a00e00342e00c14440c1c10181c450b25140d078039001c0c0440390380d80722962081c0f1602c501e00d82d078402c5000a50040580000640c2019201c04001e51030b0600900d6a00b807855022500e03850052207100024000e00015003a29024106104000344940c01505146061810140d5440e50740d003140c1103103840f440322501d094020880081034154a9840400b803601d992182c8034807400c0d403c056507000d038002c0040d00700900c01e07400c80b880d02505101d8141d01c0a030190745080342c01c01c02ca0741c51500300d545e502c13044940455a0b04040c50010401294182c0040048401c00071301d2003122015440f80c001d07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 815114163 1250 815112913 815112941
    0x1908060319171306050a0216051f09080313082a010c050a0c0609080f0a0b060f0402040510020606191401030c02031c0c11011e15091415100c080c0a02040f 68
    0x2002e20040c0080900e0300e45101d86500301d1610342c100440d212b80c400c4211400240d1b03180494405564250711465a00700301c501f0300c0c2d20005031500b0006101d00308000c10300c1e020300128485c00f04505983d40082d007038021000c24144505800704508010092001c08a8243e225005450040d00c45c200103002c107640c0c1c065001140318410308418480c0000501926040e400001c6a0465070b84a05100e101c000701e000a0350801c1c2c00740300100d5540c0c4c0d20013014105492980c01000146401001c001d001010580f4114102407010700c2802500031002d02542080c03001e0030040340300c0b02c20301001c03441e502c1402180b807144509510020740503a403582103000c440c00650348441244100b60041422504c513a0750107480600c0003c0213034031601d841e8002c00d219040108802c2d41403175031004ea40e0180d5120f4400c04032008500c1003000503000000c8108020b61405035078046a11100c47c2014208800e04071002e028042c022988070501803003003011404255010784140114130741d101072200a0140c180f20711507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 815115413 1250 815114163 815114173
    0x203010602060106201b0609040906021e070503191704030f110111030112030203091c210c0303050a06050d0602040305011b2c061908060319171306050a02 68
    0xb00c10b18045c01101c101c442d0101034100e000112441c00d290320481c80203250082004d000c10030031035403103114210402d40a10800751340c80440481d41d170b5141c000e082108981440070301019005c40c0c0f0001c03c1e2000b000c002c02d100400403103081c10030b80c0c841c81d000315262002d54922040008155104000f62a01ca0b03054494403880300300c400302c2d0760a03038243d44c40d181c00c04a02880100031129092602035095030003030040e28540286840410807026000300001d2030110360b000c0d540c0400140d41c005244107103140c0b04c22980e120b0402001024010076a8001d4100760b141c00200785844d42c40d601074402480c00410f07200c2008954900400039400505c0281d40e203510b42414052503500b40031002c4d0039500c1c103580d545407080480c00e0040d04100c00300e80d08058040c00d03250390300d0b0a4070b600c001070402503c0e5040340664662034200040c10f5040c014400c038000c0d008079a1040b4440c031045102038549912046400b49103800c4022552180559a4501c2c0a007070040000070340d164104000300090b051540c00e0754 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 815116663 1250 815115413 815115437
    0x912020a18241a0304020409170a120b0a1806080709150806040c0513180f02191a0f09041404051b010507200d11040b010c020a03020d080d0203010602060106 69
    0x30000c0349180c031443d154200ca00350a190880e052400550b44039100a000007516602601c030044040303540c001c041a00f41c0006400d40130a0b03080301103680c00aa0301c2d9014041c1440000100308103001e28859901c84005070300d00980c1c0c21a5507085803014020800485142c0f55a50711010040c1948004c5550038144684004c219140c0c04611644195000340100c44140d1410b408e002e4100c02d00c000161210750313a2040d03a212294440c800c0d203c0031340644044581040540104040c601d02d9685c060320940c0281810400c40030601d180c031200005020300755031140c208200e0a010341c03198004860b8030529254404550100c0480703c03030b001c1c5024404072000604940380c54911030341c8090401d13000c100705100d01d40010315404070405400b8041c2c03000d25402d90031039005c01c180340e104401c219000b01042d10311a00782d051501c18011075400918160b04200425004182e455510b80000b0307014885504004003400180d00494001140d004402c540d00d680d5604000d41f11b400a002d164002020160340c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 815117913 1250 815116663 815116721
    0x1b050406030e1c0e01050d09081b03190e0f0406030c03050d0c050c0f0a03021008070305060301060f090b031e031e07020108160908030d05090f0d0912020a18 69
    0x22540f03540c00d000c038028209210b403800380c80360500111000d0410804002035907004e04c49005c0c61841c00d105504e081c0d00c681c50142c420300f100d0401c03613a504003a03105003c0d1000f94812028604294546807e11420343d040d64001300701ca60b60303807400c030580060615400204115581c00414100d038058070980710b108001001c03ca03000f0981600140c81540318445164442c607200c41d0b21108084000c08420081d40c1d07032b0b0b0124200d80d00740103081000c036003040104015260140182c95004c6001c50080060b142040c00504030048035000c0e09074035982c0c4109043d01c030784080100341c1000710b1040c11010032010380560159654018400b045230308981c000800c0340351506005580400e60b050f11841459038499440700710410000c0c001e10304118801500180640c0144001d003481d0f22000e0003c07030030749088000680f07060001c24004006a0110002c4e200081c0e06c0034583c000d880440e074064004000e280005a0b22280e0b07600700f4050b61100702007008400040d0b034000404040d043e4030740e6003050144482 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 815119163 1250 815117913 815117923
    0x708250f03030f0e270a140c0d11041e0f0605030606030406050603070519050a0509060303070b0a0b06160b07180909140703030e18190902041b050406030e 68
    0x100502007800c2c01000505603024110038820814080c1c05000b0791142c212009142d4005e00301d040340000112000e1200d0b440c1d050040859010024030b9035441341c01c1a0043c410188071748111010a19545e5045003a0b00344080d0485004002501003100307404510000e001e4040a184a0320030920700c0d050380024914007d00c141c0e407160070000c0405055030340b43d4650707201134400144601d5150041400224941d6200d04076120714070120a00184642d0801c0244105ca68403600040c0c0304032414001c00c4001d44e40002140c403403507030003c881012a100d03240c0d00c001901c90340d0300c016400400455007081c006c01004227800518020294074044d40c4682600b9540b403c684000b005001901e21001c1c003110499400001c040c5e0311032140c1d003044420a1101c1030400c40640c0003207000842880c501015031070483c90b0700030b11440c0494000a1400c00c200e40300d5100408158441d0744d5a20b8110207000d6545a9010301141c2030074400300795070380d104610010030170792080c002c0b40086468481d8880b0361b0940003030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 815120413 1250 815119163 815119169
    0xc051b1507082401030f29010e0f040c0908070b0310090203160f1701030510061502060412050c0609010f230a05220b0108100b0f10020708250f 63
    0x140c038403510700d80d0501002c83d1180d506005414503484000403a0400701ca881744045200801c0004490b0124141e030780141c0714800f00d40c8034100035501c490908907130b4912004404000044800160f0403007032040548480b281c43c0d00604003400380440c0040c40b41c4201d0b000b144990b10f403200d940c82103502c1d81c4414040b8041030700c04401c1c404210503583c2a0070301070010182e0520f51420030345000d00100c40140c0c0e45e41c200f60411165504078030240007244085015043c060154019406820720321402c0c001d68031a130082010b0b0802c0d80c01d0102003c11030065003240e030310481030341c02d540f543c0c60b0030340390305020b044c0500680500c0d41ca0000042e00210034504011144040c1d01250009511201740650141c80050403881909200c40180c07140031403000b20486507503204111002d102e6141040c51401d02502003500c4004a06002d0300414659907609a00100318007101d42903020b51104508034503102c0e80741c00414451160807050942004000140e46a00c66108407a4140075201ea1001c82035400501c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 815121663 1250 815120413 815120431
    0xc0f0a230102060f0405030702210a08040f0501020705150a1b0b0f0906012303010e0307050706090e01030b040308070215070225060f08130219060e1002060106030c051b150708 77
    0x10123075400516107808096010248102420170003002040d41c40c3c185841280100c0d000280000e04000700e10440504100411090024001c26460040806c041440100c0c0490482750001a4030710514040d02c03c02d280740c00220b0203507011540b1490001403000041e1808034000d05480005581e8101c00107446042e02c0c04a855184035000640b00c443d00541483c110b20791554a5240d05040c11208101910200740140000c00e84a03180400242404000384c0000c12152115001840810410a030141c1c00613854070300b5580d290750b11501242071045d8203803941c10041d800000d001690744c2c002660700e80841d40d0824a003284a03400b0f030345107005190b0701c2440c022950040540014034055100c01d0751003030160285c0002d440b0f80b035001035142c1c143e00840a1100324104400c1c08000d6111741c00a40741c010507954103403d410721210207550755605115a104041d1035522200c6d80d40d104c0c2c015180f002480c1e0580e8074440000c1d89655844240a182c038550445a400014082074810311109015207184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 815122913 1250 815121663 815121667
    0x110f030109110d02010e030322140f13090204060b042610050c0c01090b01150e0a030b0a0e0318040b03190809010302120703150503010c020c0f0a230102060f040503 72
    0x8400c3c44104003042c0c0003a41400102c414102d1907032002d100a0592050f4008010302c0702c00c40c03d03c2000d400b1a69048040a0080c1c520404003585032440300c4826010100d6003101e280000c042d04901031300c22a600207400030308210002800b283c403040500180c513104075020705414040c1d90910a042c203894211160380c1d020701845251a105644015000a070314004c1c0c0d844e02500310103090a41d20455421624561824010416213819012041034000c071481e000800c90100400034000303090502020f0008016000030a00d1074840342d0094031081e008805807030300d0362031403030820840e0a4002c4d541030107241404e9440009160124981c40c1401c213081e000303a40c0b68120348401980c0e070410441203052680c2000780d80440e9080c1034415100e43d0041d50003240441d4544502074000c442c07030703100e240681e052941d0311400ca5000714501c1001102500c12400b44415200022810711040d0f03c054460001610028040045040103c5081c0401e17001c84044d903e910f0b0304610806000c55024000b9001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 815124163 1250 815122913 815122943
    0xc030f0e0d0903020f0a1a45030f070305070504060b2a01020d0629130e04020d0209090d092108030612010608100f0b0a150c0f110f030109 61
    0x80d1504002c0c8081c05020000e00c00d0312041032885480312001e4140d0211004101c030700c001100d00f02c1c01c481d0340c034504801b407011440d81902d030704230407070009074602502490b5612510130762410002c2c1e081c2400040104c8881316070324242075031140503d000c1d190003282014004a003001c1400b0031039002042c85000c802c4031850b002e01d070284d08010b030056010555000c0007204e81c03240e02401100060842601c0e003000094803200650b0034098075440d9422920002d000924524145a508104071104040c1010303e42e0fa82d40300050340455200c00080d0b200c2e00b00000c1c809a620300282030f40c00d0500c640c80e000b05568440f00c01c018543c9507002e0176000c4160300d041c03000029207510095500b00a0142804014070082c1c00401d09643d62900104200d5200c0c4080e1340d1070900c54003480c0e691844900080040442c11700c0031a00b107010b00d00552403600c0308244d00b03640652241c152403c2c07554100c1101c1520040c545040b01350300991607481c5200d800c00c0011200a46410b1051403546a8000c25003402066 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 815125413 1250 815124163 815124169
    0x30c14101101060e01031101111204050d080904020c0304080f190809040209040c0509010e06040f03032f0102030601030c1701090b0d05120c0609150606030a0f0c030f0e0d090302 78
    0x20101c02084955403285400100b249806584901071442424514a0400c4183c0014183c04800c0080c0c54a58095000e032050009030004a038242d82055400c640c1c0148141031041e4031740b14020720544c11034800201c0f41d86211000c005070081c0c1d00d074001507032515420321003001e507502c10038030161030024020381e61803000500781c1001340080040a8400340c105090340d40090101c402c1c0c0c03051304000c43c070002050706666034032040b8003a280c3e40807110f03181064203101e40c0c0141e1000c940401010701a46001c2595020030103007000c10700a450014030b6441003104a00140070750002d5480b41c0c080790901964040340707030050346603035102504036004802c40da190503105d001410384203101c260804a001e02e44008542c2c1400b1190400000000c160750302d441000700076240c800010003288540e004030148004d089101240740b50050012510303a0b8480e11800407000007851502d1040424604c1c240d0a0b000e280d4064105040c010316900c400c000304040101c0d243c2e2103180c4550441c001840140301400189 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 815126663 1250 815125413 815125427
    0x5150a0f050a30090c09110f03060f0d020306010305011b170621030a0804110405040804090507021e0a0b01060206011505160813080106052715060a09030c1410 70
    0x103c440307550303485030507844549801202c0302140c0c10340d88079214981c01c0c8102d81e054028621148040481d09240c00f140001200590101074240d038460315805003265030303a546508111101903002000e8919550303403454a503000700500c25400c001c448612a4108c403a60090030f6514a0010f500d42c40b1641d60390b490208003034600c00c08001441c1c0445020a4094484204040c10b84441103480340341e80e80c01d05040824003000d4400751984507038102010080001c0c45034090700c003280c0c0d100001040b10348402c0e5060f400c1c010301000320449407509240c0c60a01140015a17690040d0181c01c64024590300c1f040200e0312190240a29080394001440c074042e900e115100038040c1d10f00f03010a01a5102c096038800d005079118a0380c695104100590900080d01c027840380302c0c002c0108498040c8641e041c006124118500001e40828841c0d003e40051198065099120003c08000b00f80c96560600c00e000030346948898001980c801e14043c401091184100c0441d40400c00005c21204100003e244116802c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 815127913 1250 815126663 815126717
    0x804091e020d0f0b0406030c033f0e030c150a111618020a213b0f030412031b08071401050f150a05150a0f050a 49
    0x40e109403000d864042690301c0606407a010300007001c1101200b0004803010750303040d120344034415441c0680170070016014004000c1166400800e500e0010b1042c2e105401d85228007200d0103180c2444040c0e00c2d000206400c0f52140e0113107589555101101c400103041e82c52000201e03031038001c1c0f10380309203108074002040502620700c4945842a81091050702c218184081d5412121036664045000d10000c010159a0244941080303811400c0c000540b034014541040600c0302e8400c4c1d8000b08810b00c6101480d00324001d8840c0c1039051040c80c40fa260113040100074401c020412401a0039506940c003c2c020511411140c002001142860f09001207403c52000e2900100c1c00c0c00072820040100100030700b5281c520364000c0042c56268181400c003007620801b01100810503916040401c07140c40b444600c0d050b0001c90719110035882072240c001062401a01c1d8212617440708103040a94404200507005003410f070120354a8561030344000c001a6003074000d11481c2404260b0440759070500040400d580855 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 815129163 1250 815127913 815127941
    0xa05091b030f0307060501060e0105030f011509050405270c030c120c100203040e0f130609060e150105040b030a0312020c0a0804092414090408070623070507080409 72
    0x299242c0344558520356031250100f2a01240c03150300420000c0e4200d45031268001c0c0a0070083d182d80340001c88411080b070140507411929143c100c0040007184a640b0442c05884041c0c801c00c800d00b8040030061110542c0e46042a48699090b00085480c002240c00c4110580c09001404680601c000f0031001000f190511400c81c1304508200c0040c1d560004480200c0c04950059981c550504c110707843c00d01c02c0144040104081e54007401244045800d500760880d40003080002d80362850310f89040174040d8180c0600070b0344100d0b91283d803100d070300c1c8944904a45040f54204403816801c0103042d00c3d500c85001c0a404500e29102c407540680050700101079183c07000c4195444124699617000c503682154000941d40341d510000d5100c00c030754481c0d214610f0384a214100781018502818103038141d00010807a4000c102c204041800c220850081d60314981c0c1c01031041c440c5007078504804008011680c000e420400010020602140c0a00f04842c052600035403080e2a00742020021009030140c40d840002d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 815130413 1250 815129163 815129173
    0x20c1014092202030408181801060c0507080303010618080a020d0206031302130207060f05010b0d09031806051909061d24180307081011040f0303170a05091b03 70
    0x4800003203200139841107202d161105d480702c5610340004011803a18403158060300120020900c1500882e03a6103044031142c1c90406242c0c00a446c0250a25140754082d0000744804000032a0040d08000140d246080e5011700c0c2c1c0311181c2e0341280c1a641c0c040e0400294004601c02580310150500c90000e580c00380c118004060003051a03404201c00002c200b0103800400e0707000c654007041100030f00408408a02050090169504243d031081540c49070b030100a00d219034900c4a101014003410010944100042c2c03240d0744203960300005032040c0d000585070403c8101c60004d11840c54002c2010000b5241c4540d50504000140040d025101c0c0c50280d00c258082c0d0858480051001c00595101c0100f0880c08a65100d03900a04070000f001040ca0046209810180781440701c0c0c1c100207241c00c2c3c0651216004144181c0801d071100c131520494208540001da00c10000c400d158100701800c00c0c8552840300d0140c90350718014060100c620a442c00740c41342e00b00480400c001c0600d42001c901410000702615 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 815131663 1250 815130413 815130469
    0x3010e1303110d03140609040209012d120507060f0e040b04090602070615060309021c11030a080c07050d0f03080603010b060705010510080d053403020c101409 70
    0xf850200c941044000080e00d403181800c1c40b01d02000419044413094502e403009081640c0010401d000500079a06440b000c0d4407902e008003200c41d540c00d0304102d016007100d45140c84101000e0b00003003490055071107204956000400512450302c0362a501510b40d9110504c0004800f0800600030341140d5907800b0b40c444034000c0100f00c17284010b00d8200e1042400083e280001e540e410002421a4883d03002d1510389492034000d80c84a0080041201a03c1c08030b8481403000c0c40c00103e07542d0a118965011f1003403035a0b080401c980d440040100540b00c0040700c81c056550710401450b030140e01001041c01c1102d000710310010303029030707440d6400c144000c0c008901c020340800803944903004548245ca1983d1110148107a28641c451904003400001000e01000e84803010301425600c00c0181c0c01c034007182c003401d00c02d844000c8900c013440551005c1e040000031014500300255503a100c0d1484034828242807078000c80b2a40030b0f003441032864030010802e6049c401044c0812171046161440200042183c90b00c203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 815132913 1250 815131663 815131697
    0x311030f0414040b0f0a060813120807030f0c120c1106130209010806221104090c1509030b151203040306020a1202031e0603030c0a060606020c040203010e1303 70
    0xd070000d40035082406103000c41c0d001c00c1105840582c1c2085004003900100941952240440d06040c1c0c1d00340d00b010403068071208aa62102541c006014007288800c074444041e81c1da002d1045401401c50780c0e000e11100305400c1d0400100c5007445074001c08100d83d04108440c00003150407030b0150312044e040086000d1440f200c80b5041400c201d8003403084600014401003189020b404050241424070b004001c585000c100c5000910040bd018000da01c420f60700400070803c0d800168004058007410500c1410814034101540e02e00d68010201c0d040000b10007580b81e18814030689049035000303860003c598440071030342d540212007a20016048910188154605441000100019845100c0041c2ea0307281105c001404010074101920781cad01d004205100041c401001038170194075081a91594a4684100007031840c40303002d0118060780101e83c0c20000380318065200500302d0b03600740c080c1c8142520060400040344001d0180800c030062100202d0401c0102156031080d0310300c01e0030403c121441c0c1d1681 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 815134163 1250 815132913 815132917
    0x7020109050a03020c1003050f0606131805040c0648080304030215071d0414042d05031803030c030409060603150803120c1b0109120c0c030311030f 65
    0x540140c4c1c40710102c00170906099a0368032500080b440d0400190910801f80c42846ca4041c140c2c40c402c8101041e80300058564a4014001f00080300c514038002281c2c04003800a044111401d0741e264020f020001003d500820202c5074070f4032415080c401d8035080900c8820100d10302181c5140c05900419641e2402420030b21605045001d00b020b10344a14140c94000e10b082c503485100340e00d2545600c00c0c0a24a41c0100c0c880402e40c801002d02120022800c011600509415589581720b8200070140810300c0a103460304001001c443c844d056048401c10071180304966900001000c0d5030040118200016040c4204155401c004060380e1a00c040c082c92280b5541280d0000500710342c2c4c811041042da50540710b6100c0d0a040b20800702c1100d407815031415100d01820f0810004a94000005482d009201d0200c864010301524840b48c1d0540e501425402041c00042c00c850001b165681085901c2c00742922000c52944200c140000a040d50b908441c000281c0c2c01403c1c503840184030031803010600c040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 815135413 1250 815134163 815134183
    0x402070302031902150406020703210b042d1a0405090d081003031707140f07020f04061a0c010b1e1003060e01121406090105060909070b0405090702010905 68
    0x2004603261008000d9005034203901a01503c1550b00100c0b80c2d80d2401c0600010950040d002500180c035100b5500341644c0c1c044400c2d541800d19a0720611940300b2a0ba1039111000c2e400d03054800b0404205103400e2030744c82110101c421603040e039070441c00c2983e1180540003d04200e00e180002110140e0320800324041d20019203e540d0607800001002c241030354010703d07056210b144144240f07800c0d45181c034007604000c80ea81c00262524166800180f019001f90b0b0007941580d01c18420980e180b1000c01408802d07000304100728810102c05664905034600780c050b1a05032030651000000100204500580c0da5102c0840f8a0040d5281c45d240c2e1096070300c084110250148498071041d11700000009c0028901d410302e0002c00381071600030180100c2c140e903403c0c541501c0c50a04c0480c0466500d05044a00a885000c14003440c403c080406c03003251b8040d00180c1c0a10000c3e245c1c01c0c540d032110007a0701d07200c0c5018006c1e6285450240700c10003d910b8503a040d550040030034000043c2c03480e40c3d521510b044c000070340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 815136663 1250 815135413 815135417
    0x30609021b1b0d1514010620030f0d0507260a06050301020711090c0c030712020606060406050a03111603030c081602071401050c0d021f1803030f0b04020703 69
    0x550030921000090148014407260340342180c418000b101d000a12010380d06001402048403801155003180c41a401924910302c402841055503175142d00041c4080c031200540b222a50284c904034040410001c1955409440c5103001d40c242414020550300a0400400800800c140b040160390ba143d02024500400e0f20403002102d420b03d800d25140050f540301d980007034001c0c0e20410014000c2400c1e125618400f03041103d620b00c86884a0710034462a0068a4010030f4038000080c401c0c08000310801201147e071030503002e68a155507200200603c0d4040d070301c00e41000c10701c10000340c0d04240c406d603c1280d10104800405050041c40d08500c90231111196003200426038a080100e806a00640c040d68030820701e2481050030300400b40c009480b403d0380d00c180780045c00041000c100e580e003e001550410001c0004464101241800081d0b85d1000e8611704446141f2440c8036407680c0c0054002c02105282d82440ca075030304041340da0114010b20005892001a40c0d0341d000c1005d141e56180020088140a030f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 815137913 1250 815136663 815136697
    0x204050a0b09010219020d020d260904060501110604110105040312020102030603070b1c02032d01170a110603041103030c070306150e07050f040515071505010b03060f0103060902 78
    0x200d4006440d0103402420b4100b60031740030a80000598130903c043c4100c940c19614076500d222140f034401017103800e0024500c8900607510002e85540f1000010304410a000c440c14410580c0c2c680055620100d1704103854040c3d00f0910000b40460724102e006840000c3c10324101c0c0c6000d82d81d8485600d4241d07040d07043c000503500001800030364078080240c10060031030000882c0c686500c03160a00c00ca000710084d4203001a4010002800d000700200c0019442c0010b145035003211782011003000f94040b424007491107042000706c040e5591340d00001e01c00c0c0700190b12a410546581c0a8410440140c000070411610100041417103c484c1d01c05001500b40300d004030000703000090130740c40c000c82582c00240707001c5600c4107020001c018042c0f111440541244403410442c0d41d03056449005030030351045401880d001110110b0b84901843d501000b8418540241c15024080c02c03240e8119040c1d0394284180c10321220140f01290403850400350104894205040016949941d030301104240d030814942007401c0310071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 815139163 1250 815137913 815137927
    0x50309150c04240f030905010902130903020d1d0904020f0a030303050702100b10051e0307020307021201022b020c070e0709050a060c0f0f080d1a0d0f06020d0204050a0b 74
    0x1070f81110100a09038203030075420301075451800403c0c0c501409140010152505280028010294410070f82035802414040b0b03218a480c2d8031102408441c4403c9005208503103001c406a40700700300780414a10290080c10108119000300440840041c01c244c0e40468081700803405541d4159003180158401d450105203850515406400c0000c98040c2c2c466013400d003000d00c02c0035a03820b100b990b402045400c2660f2107c12410710f02046503a44581074081a1002091240c0942c0002c080c2054601c00c60f074041c05841002002802e034004c0d40c500350400c41404085c0501d07850040740f420790182d884400181090300c600c081c2441d00c0b01e17607407000307400300c4e40c03034082c051229444500310010788010b4034132400440c6003120040c103815074800080c01c65991407502008000440c840c69070016004038089845030100340d001802410081c00d00e080120402c40c011089042134000c584005402c81c044c1d28032a412512220701a600c2026141d032000c0e82000042819910340266101406616082585901c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 815140413 1250 815139163 815139179
    0xf14090a051c021c05040b0d0209040f06080d0f020c1003150609291314090f09070302040905030c0a080301030605071b02271503070e06030a0201050309150c04 70
    0xb40082c0071800c0511001c402c08040e000102c5071018100c0500c01215101070b18011282da0095800c04014248009281c4100366856000f82480e100308a900f04080c10302000c0b070310202c071139070f118680c20f80d00030509909003140500f00902d030400290040d5800c0600b0a00051000201d1403402c40c0820b0b0340f00140e80e000354017031060308050102810315101c0c2d58105004094030f45a03841841e003244085c0c00320010b5114180d01a941501c42159084030520b0701c4800409680300d0020159010307040a400081e000c00342c4441941c01000e02c0d1000c0d00440e400c60702440054140c10805540da44001c102c075840d1188100081400c260068204988075410742c0b40c01801d41d81d000c3c01980070403241081e8aa00c8224425240829590455080201c0381004202c04040044445142d40480e50f43c0b040012038400f8039425158906c044081d40c081980fa000380c000d4140c000d880c0140c0583c03001b01c1072001075000384000d41d0080b03d5801202c110350361502d02c1300b0302e40004032080401d800000c83c042000074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 815141663 1250 815140413 815140423
    0x9150d09060f0c052b02031e090d0905211c1d0a050621091c0207081e151f092310051c120801060e040f14090a05 50
    0x119040c030074041e0280d004401006400382081040c1d80032085c0080900e6500183d00ca0001141000019907c070310300180c1000011400c040140700b44a0080001080d00c040410007400301d945544400d04c541e030a000034001300d038006d02c1002d6030509003140500c4414104009102414000c0c80341d6000005403000010300451404e400300b400c1503440d00c42d120040e9520340c0d0780310656000b0f5450701d44038074501408520000a200591110304c81c441c0a1154204000c200e40410340460110000807000301c0170126502c0c5018460289150012003030910480c05041e0410b403120070b10021205c5400360078103503003442c1c8801d407400041c01451340320000c0c028001c0b80f26107004040f002d03403c01c1040e05048890488040d042d85044142c2d6503240098440e003581d210381c00c0545400303004c11024030b040400c0392510711010401680d00f116543c080c207411511448840c0e050300c00f1940c45140c0d240039074041c40064170704c1d0400003103c0c13030300c4515106407004854506031050113020001c0081e08800d0900034100303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 815142913 1250 815141663 815141681
    0x90b090705061303290403090f0b13051e03160e060603160804140f061801020a091226070b0106020c03150a0e1e060a0501030f02040209150d0906 64
    0x25200c1880600b5038003480300d83d0b0804490700403071843c01c2c41c800d039601154003181d90032040c2c0041650006010605034481d01c60804d540034140603020181d22082600390780d008810440d95407035000740d418401030500c4400c020300c1c80041d0304030341004140600002e060001c3d0400e100654503e0110030014800c0c0e14441d40d422080a03503c2610f142001804405404c8002e04520180042000840e040103003481251030302058040541d160345251907447c544801003076944401030307000720001c10141003042c400c481700070003a5101c03002c1c074134600f081840b4a02a80b40042c1c60004201c58130b0784000200c04940084006021200c640d0b0b0001890142841030741178001070115482214965010740b80010386401803660580e5140180c0e80b40401c2901501c80c0f220041398900846c0c61013034039600703605031f40a4040458001e549031a43c84050584c11104240b101a01da10754041c14000541441e5005109104025017500b0b081c1e038280560101d90350000118000711550350212409103d01ca120300c00e11303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 815144163 1250 815142913 815142919
    0xb030f370911060f30040809150a03020c061005011707091d0718080628060b07050d0f091203200c0103061202060306041d0a1506080307170c0106050301090b090705 72
    0x410032080c2221179074804000d100524440e070005503d88a683e0b114200700300b01c403500700025500c00c50480010082e40252085a1141c4180400310301c103080740b020b00400707031031060b503440c4402502c080e42403120040c00740c0300c0402c7c48507220001c00c1d101400c02c103d400c40151144121110704180c40700404003c00310382403918100a01d2400d204000d004507480c0e400c001d10070014051390511061449505241003c1800c070b240c50107800003038480d041006894058002c1c41074490354090300b08160b503c00c400c40c2c0c0c07040020f0071b0407000b80803155480a600095078001d20348095103a03507058803d030401d90010110070f415030080c0300c1c00c20a5039141c015039000d03115400340d007003031401c540d40401c101e4080038111900c11a110402c000c000d00381c48408a1100c88004101d0b20070071000e0030300040d880c0d041d0710142010340c144407000c0b9540c0000401c0342c50540d482030003a520241001c0c0c1e203a046400c008031380f0082d5500d07243c0004007070b81e00b4004e041c04a40225002851410003040a51900d0a20341c48a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 815145413 1250 815144163 815144227
    0x90c0906030616030b0604050603040524010f0302010302030406061d011e0e0c0703030b060703030e1c08040609062c010b0d02150f040b030f370911060f 67
    0x40c3c0ca81c00030034215084003a080118060511700001865030295401950b00b0030400700c10081401400100c1011032100c01030301200040440780c4540303c088090280c00810880b2120400040d4800d5009580c800e0003843e000600700e4a56000c411180001d0211705807038500003005020540c0300107490001c9100f200c1500c40d40c06d190a6070b440105074002e0460b000c0c0800803c41c2011f05009805c07900030b07100014040c1e503854200340b60190041c4282c89010202d8441c00c81c154114800082c000e104031a600d8a410b02103035560356035000030380710001c402c803040380e11041e030350b0400500304450403000745c1485050040d8011100c01c032401c4410001c1a5445002030251100144e00c03003103105d90501d0b2003104059035a0b841103103240910721640c1c0c0045001170b400410442c6c2c90000d031040d14040c0b446038158803c017254140d2a0341d0f1040030181a850050000d40100031004080e9100c0d401151064095000045000c000103103143c0000d0074038a0755101c0020840f000000900201d100003011055080c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 815146663 1250 815145413 815145421
    0xb041b121208010f0e0405030c190516030b01031e06020a0509090f01050a2303100b0103050915270d020a12081306050c0d060b221a1b06090c09060306 66
    0x41c0c141c191361161040c018001030106044c85800e0040398201232099040b190707499541c110125443c52003040c20340d83d0b4003a0390039142462800d40c034801c040341e400080d0701c83c0c241d0850711240301c0c0da50f00400c0902618280d03044400040c0450001e800482045c6d00d409890f0b44000341480b00f418401464010580104801485641d803200d0a420666140320040380f0b2500749503000c0795001f00c03244c44465140c8184202800c0207440768116002e0000c081e42d083c4420b4441c1c07051140d5409003483ca184a0503040c90000e162070329104496041c14101604102c88006031480050030030401c0c120403070050300844525024842e0000074081c04400510b8100d0741490008003582207013840f4000100300d69100c6000c41d55000c070000580e40030f480140c40400105030b490342c0e40704c1c007580108200158141e05662260b5016000000c1c42c080710072204044141c1400b03001600400d92040c501300003070b03100d03904008911034410441d00c0c0c42980c01000911045c05075501300f16481c403000b0025031003503100c04100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 815147913 1250 815146663 815146679
    0x409050a0602090d202e0f02030d29031203071b05060a0510060c0c05090406061e03030e0f1e011b03031a030c0604030b041b12120801 59
    0x5200d040303030016030040c2c64610000009195941064020b00b007840403034601407020600084001540310308540d40c00786001104411035000c508440804004075050428800144c001c58000302c0349403481c41643e15240b84030000c04120350804031039410328141020412117450340d80448a0795030000b00c00801c000595910400c5461100a0002d020080107810704030460541200d6400055071000c19101c1c80c1c60208907100041404030f03070140c88001407017000640b01d4064050381007000e0b0041040d5a80609002c2031240c1d0720009481155107950755000001d0309040301d90343d103003c0c2116000e055811441c1d81801820003010b1703e0401d11400003000721000700d617138400c000707131640032511030202041902000680341c0ca8589004824031030b4940340c07070700100740d4560300c048020001e6a6102000c01d0300c0f102450f980b1600d07103c0c3d20350054130410051000c2008010484e070300c01e20034070410702e1400c4180c0c2d0b4040d8180b8036601c40459505601303c250100720300c102c00c0c10055a0780d40f5060f5050740c500b07000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 815149163 1250 815147913 815147923
    0xf0d0203190e2e0e090717040c080f03070611091c0312020c0c031903091806032009150609040902060903030a0228170f07022d040905 59
    0x4007800304a141d24501d64540303012400c480b0070382c4050f100d100e042e481c10404809600000840c0040c110084414507454240c80d20b601905455440d02c00710428110012038214003d84103640203039600c0000240300324100505066042c040001d1a1214941c0c6080805d47c2c10f4240300c0c00300601d0600c01c50700da82c0c440c09241801a40380e01d207078459107a043e00b4196085410301e0320815456000180c0d04083c5500011305800164050341110265120b43d403c01d07070019150341006001034040f28041100904e0041d09461340c0d244800c0c0014456907030340c0d0b06131811030302070030710070050390348060071206860a140101d0f40680c2038403032140e00b070301c1e11070019200b0b2091000aa00ca1580c0346c400b81c040d500e031001500c20248020b800c8030307520100c9205c065900d2000e561415402d191140349689200d20207200031202030391004007000c0d00340100b0361125840c0c004001c80190f440d0240905409a07454449843c090280030741e0f0b854100311481e0a64000308458a40c880c01141440030f104001840007039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 815150413 1250 815149163 815149207
    0xc01090902160f110414010f080102041a0c070e0a05011d28090b01181b1b150f320c09010c0f06060503010c08092515020f0d0203 57
    0x4074400801c04649805030413404e00b003090940040c50f02d18419400d050458546069071810f071145c10816030b84855041c04d038440e034000c020701d41c280130415503451448000a041c0c1ba02d00d91040c0c0c2c850031b840d04060b5104000c12190f0025503503e5400404c00700783c0c10345445a02450391080b045181c0340201034001520b54000c5038401031484105001d91200b51036210700c60603940034044000c07550b91103003842c0c840d80729003e0a01e4018035145022100c100c000e520a03881e0b0b6801e8849004000200900340d5401241001c140e44044c042d100c61103030990a44a8000c4500044d9400101010700c0e0514040c5035100303011070440301e06004440c080710480e282d156a44010b030b54554030380c0c0e0426400101c0b41034100035402410359141290700c0d4100849500400b00780c4405400802407980b04041c12a8000010354030600c26070404100491102c0c142045008400382070551031000d5076840300d00400b0100f560780d40c400140c024400b101c904580610a0950401e810710080d4106149213203113003038400401d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 815151663 1250 815150413 815150423
    0x7121b051b01022505100b090f1b1c0e030a0c1e08210606090a0e06030c1216050315070c0f0b040c1403150a020f04030f050c0109090216 60
    0x704840d15202800d404468400440e91203059801c242d000680603140e020000c21942c0703018071039100e50308580ca0712030555002c8004008614588904102c4c4400002c082c100c8080f00030300106a00ca0b5000c030800074000c0311802c3c007801c2801c03a66450304208480d0f00c940030418a80041140c6440385900041c0c000340c540d08003507440c84c1c0544407110b107494816841d2005052900200d0a013400b03012181d0303a80311000e1213440c003601c07071383e1941d0401555210700c00c0002c1d4421403010040c002e0301c8084184940c80354014044a811440c5d40300000e031401e2b090345c0c007120f150380038108001220343c4040000300104020760081401201c40001b85400500041c0740c8402c0003081101c8106103e80804610f0203d90410880f1020b420207081024105032940100801105440000e42c21420f000600c010403244103c000d08079a20385040040c041c2d4010850780001d101d0521000c00450315040f5080c0c1082d120741d0017450070100c0d00001612003030095002c0741e4490b2051080c951720281c540701c0c1d07140241c0c2c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 815152913 1250 815151663 815151697
    0x906010305100f140f010314030a09060302370e040b03060402090403050d090302030d0c0f0e0402090a0f0f0801110408060408070606080616112103041a07121b05 71
    0x1100e410f0060103000c02c2aa800d12102050111000f401d00d00b0505070380c05a0b000c94901604500070b25600d220301c00031741c4001196110304020603442070303000d00b4a001914100e00001081d14481032001e00c9400c94091140c60480711074021541c100c1c509200c1600240c0d400d01c00707021440c000980303800d002400071307015840000c0041d0415110f0320864101c81e40d116400c008e45291400d009580360000113402180d185080c4a4070206401031030b40720801012036941c901c880740c070a410f00010350015003060390031004041c00411200e0010b01507102415034103001e0280c0d149410511425a0100740d10380c000100108810703c5051000b280c1303242d000d5008948642d50700242d10f046001070055500001080c02520144020401404c0581705103120f995201c40160210038140c2c0c0d21005a000e100c60040729460000b012031080d207014660107401242c840480155044a02031091011074038100001d4240c014494080503611560305040489103280200c15240040034200c0e100b0b404400c2d402c2021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 815154163 1250 815152913 815152931
    0x40308070305070b040b06030601060e1f030f0204181802030a0b042108090c0909191401112503050a0e040b1e0414090601061b020a0e010e090601030510 67
    0x2e90304480600e075100d12641003030b241500340a50426429150140b082c0039071000010118841e1100b09240c0c40c00038956408407030a400c208405003244c1e04110306160311400c1c0414203c1c0c031440a00000c0550075912143e06100480c164100c9201c00145094080e0f140c6c0e190002d80c84c001411030b00c60b03500039076502c0103442d10305007400706a004245001c8070103007500d0181000d90748403001c00e009103500c0c0215034011520408101d0244030440e200c5600c0d51240c49000620211640118039841c000e0021a00e8640c404c2001c1e030070744844030310030203002344001070000318070b20050001c8142c500881c0c80c040c3d60f40501c0c0d034000c08601c078092010040087c146034684030b541d03966204620500c002448245240ba090700e15216030450074072a28816481c100306415500350700c85082e03116030b8508000d441d043e824490300340d5284151a01e100418ae8501800c1c04c0141c5490320143c001d40314101840d1901c0d072400b6400070200310010505144c03900b00c40e004000040c0c001540358100c4400c0007012440c484 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 815155413 1250 815154163 815154167
    0xf03030c07241b1b030e01030c05210609010603060803030c03061c1203111e130b04060302300402011b050102180306070809070509151009060e03070b0403080703 71
    0x4107181d00c541000c0c548904496030a42141020345104410313251480115a050090208005008406000301713400380000c909030340c4a40c0c081c0010b000c9a0074068145114802c60340c082042500313031280d8000f0360009020048c5044044140140701c24a01840b4140c1040d81c030740d459000181100540c9a00840412801d60380c00c406240c07040305d0b0892000702002c642c14000c40301e604540d242008a40740c0402c04c85007892840c22a444a04020404c828400b8815540c1149602c070148a0789542c1c0d041c3d101281e054100b03002800180060784d40580c9030b0744500e00c901840605020324030421640e903020300c5414086020040d074000e40908003000100c50142c0c41c01050700306038600808551001845a64143d501d10034800c10540c1a002c0f40c0003075958135002e88001c44260303501c600c281e000c2c902c00c01031860700f403403071960000c20742c070f02c013034000326607030041824982601901c1d00428900d000611a07140d20107034607281d00104400410406241c50090a03e6124a01000d00044c00015030310003458 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 815156663 1250 815155413 815155463
    0x506310b13120e010e0a030b010b0306031e07030c0f0305060a0b04020408030d061d0f04060203040305090a03153e04030503030726011406071703090a050f03030c07 72
    0x680100c402c810300a40c0e818020b01d20484a60b00d240401d080b050100b4541c10208000000d4950001c400c002036428440300b1845c64100a00360b81d418420801c1c061400c020032103a902da4500c1020081c1078440c19840c10f10591112504001c50503182d41a00300041000000c02d142c1123a00c01c24001540515240401c019110707079003240000d48000203203a4a401680c0d40100216501c12402d14801405455802c1c44841d068610138509030481010078049a21580250307003080c42410014500b99005020840b8860139900540b65014802d0801c2009805409071000d0114001c41c201882c1d800b084010314003038455183c100c0034000f0000ca031041901108111009075400001700c0340c880c5803081c1d000300000400c000704c2252100310400310280010890036981030790014018012602000400c0c040030740c0040d1070548040111102c0280e84004500003540207000c01c1c0040c03c014000c6040c090b01e032640b50f00352040c3c650b004204200e41152260b09443c842030b4040086510340a002d0500d148070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 815157913 1250 815156663 815156701
    0x13172802030c040e2a01020a17040f0e0405010f090c0b070302010603200a0801050402311d010c17130302120a0906030501140a0b091c0506310b 63
    0x2c10300c0c144000382c607080c00241c4e5005210071441e24605098506075070817004486242d600340560720038602c040c00100030000e00d0070014920303102e07a4103050395200320310074104c0c06078007102a00d42640300b4802409401c1c001d1940300d115802c004d019580342950b03242101d034003d101d09804100d0200341a002c061003034102d03100464220b6258100301e0200c2c1c802c415113041c000e4659119102000c8001307411581805a148144d40060460403100f051021828940c504070300507640c1e03000d60401c404d040708914842d51541401c54104807299110702c9124900311400d6285d80014018416441480980c1301070440398004c04554982106000d00c0c50142d290000011121941442c041141880c0c1548a000402142d0491f50700f0300890b40e8600c08520b400d0b41c0c100c000307900420110014010342e000b10008000c01400903007481d410180f41040c42460748a140b0044401b60480c1007440281d080c081c003480c100341003400e00e0310315020b101c141881c440581e803000101706a5000001a01c0350344130451066074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 815159163 1250 815157913 815157919
    0x131a1e040b090f07210c05040c020a06060f0e0604090303091406090d050901050a0e0a050a0f030c0602060c0a0f020c0a090903120e0a1502040b13172802030c 69
    0x200e0800e880c001d01641c1007103981c80800c0c0310b021488402c0ca040001c03000219101a01c210180c0300420b0410824110140301c242d4040712103110010307042d202e902c50b858064880b90f0140000d60070a29059007507804c654801d010f050749560003130107003c010300f8070f854005504a0f000a080002850181c0241035260400360070550a0800b000110402141091003480e000c0c0960700f0103403100b10b096400340640420b550000b10700380002e02d4600c0c014022010003500c010704011200d90b0b41d00000d00c0c0c01580e60085d4400d003078030480c1042080b0120702c000c00507140c3c90001e003813980744c00d96a680d910f014204110080000700c8280341c1c800e6000b400b0041d241c2d40d02a00389840c1948a054402c040c0500c00f03001c07000540e2601c000c26802409104088940c01d2007409490441140c0d00c1c0c1c1120103213984074101e4000d60030800006c00030f440d6002860000088166404114031b00504002d002c100940e05510719000010302030b0740301030f801c0c00c559030300c0c03c5000f04800d2a4000d8000f091a01010100b4560 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 815160413 1250 815159163 815159221
    0x100f1104092013060305060d0f0212071a0405030c0402072a1d19140a0e0f031801080907060816021e060114010c0b01140d060c08010e131a 61
    0xd03c0280b9078150700166a0f042e1800c0c065030700c0390303410b0000440026001030031002c5805084001407400707040e500d00e240c0c599011030380d07403d481d80314403401e500c80411454565540002d040150382800d1000451301e45080b142103051100c076445003900d00ea00014080544100141819070418410110130040d00c0c004280040142c80c2101c04440e8010a0b10540480d50ba2030360218818203050040c50b07201341442e0028001622070f00e0b5040d002d00100308500e4118010b100802483c004204050912601c8030fa00d410700c00000c0d040050441c01002c0e06440309c0380c0000c1c80c20310149030402909a0411350800381180d410b180350f20128201200b06260842403010b010f185030080800050035030590f031460401400704000c0800566580546140013044100c12100400c04003c00c100c80704414070000e0f250313945c1070400eaa115001c5409084081d004582450018000d0200b0900c07015403010501141c680302403900d8a80d00c9a0145042c4401d113019000c0e00029045100342c44403d40401010303c00d54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 815161663 1250 815160413 815160427
    0x90503070b09060105120109050a0803100905100f06080c0f09010c0812010306180b060409050a051504030206060108090a020f031906020d0c1707081b0c100f11040920 73
    0x140c80f507400703101e2644100d02d1008072465600c4103114003004280e1080052041403299070f188442d5400040c69040f00100e03002002031003890b1030061611502034072590382c1c80c0500701080300b0b88100403904804d0400084504000301e40400c3c80c11203400c52110712855445241e09001290720001148008003422008503400405091b0300180e14166880348905102105244070400c220300c86508001e01a0850900865005e05281d4000c50700130340a4002e40d00c0c201d032251074280c64007044000d0f001902c5d10380700802041c150b0500a481c0c01c02001d182c45103c07401c00042140e600c2100c04c030040d1103002e000c2800d1205a6007001610b5007220a00c3c0c80c003000d90080e0034408001e41000e81c54950031810203aa442019104040c044001c10100ca005002612030300801ca40442d002444200703034a0300c50802901400d1b01802508518003044014130228513208440d1080d81c04947d40c00c0707195814100300c886500b00b85400c2e82d0585002c0d040026103420071501d0f0600d5110455110140000000717142c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 815162913 1250 815161663 815161681
    0x203010603140c100e0d0213090b0103210e090a0f0f0612060b191503020c03180f12030f13051203071205040e06040b0301090b0a0c09060206010b0a03090503070b 71
    0x1c652600c50880381500104d121083c02e03102c030907001d2026544034144400c03103001850440310400044040b008001440700c101d0703860520202c42030308203441c0e40c0440c03c5001881d0711b240c0380341c601b5561141380020008007810003080c2c2c1c2903800b802c45e640340e9071602d42e5031aa06516a10104100c0e550b4072007840a00c3e500d9442240488089a0542da02c9080409081e03807030420b0921507032481100b047c003100345803515261808548a1090320300401d50208010419081c0400190403c00059108058080901d2041291200c0d80500c000d01030000394000c0d02c1d024401000b502c4070005103008041e501c0001c0c0502c91007c00064000542c041d1002d07103102e0b100300002001c1c2c50018815802010030740d111650942e468011441403081d003210820014905042079040344040c014040c0021615110396500c080d0f12000456030240051b40c0e0314108010603611140c0a8010407850014008c1795040c14815040c0d031082480c01024152604080810030008100701c5040d2078124800d014107003030103611 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 815164163 1250 815162913 815162923
    0x21e0a0611030a0e011503170f0a090e06091e070207050d0c06030e07140409020f060c010f0b040b010203040504050c130e010e16050901030b151201030b13051207020301060314 77
    0x7444a5681c80c00180804d105014851800f51500e942034040e02c2d03510356035401e01c42220a46495424480c244620300b180c12030b40c009803041d422140c5074814507070704120011640c07000003814203101c2c900c41000e00a14200380c1c100c081801c658000c0c510f04e0b5a4071410283e01e054401da00c142e4204850014020920059050200a80d611a50103100c003010451405586041e0707800340d00344850102d500306072a840c069010000107031014103486025422440024643d4002940704c07a203d075100c4032000d001e96035612a00c0b1804408841c10003070b04156600003907880c0114080c40e8000d540d0ba001041c000d1820f641a0b540b05404c0081070000d031340c0c6a260384200141d0a100300c0710300c4180c22000c81d052540d80c1c142d0f81e010300d40c40e594190602200b500110064110242d146401c8148080600d400240310380082c42207030410b4101c60903c4d45113161090003c5801810074000508600704200050401701b0a1070030003050f20010707034480c82d081c00040d0060030302c0d030300040580d09022100b02d1b107002c020078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 815165413 1250 815164163 815164171
    0x60f120605090a1a100b0315090a111e0d02070f0b011a0d0507090305100c09050f0f0618100908101e0e211315021e0a061103 55
    0x30188140d8842150030356403224000f01c000c000749094100d181a5110218000c2e5000c4511a280c42c015a40e5240d4115203034401d81c0c170521542d1a0500ea01018145000403030380250410360200300076564080b090b1064000c2e5808030601041002211a841002c03900f65209400000400c41d80c45425103400e10032084011000c550b843e45407000000c0b545c48460f411801c607103079100428a00b90f1181d03002001004003d01010502a800c5004070101e58108041328003040516070000d0018221a0302420401c1c0a502c41c61080d42c1d034442e21451a201d0394001c203a410000d981d100e403280f80b03803038500b845400c10607206500964190b0801c0030b602e030300c12024030440d4840002e80b00341c455881c002d5001e0398250070780f00c0403400c42e030b4514017604200396001c500d1495114040d120a540745110b213418030000d04014541869011070b60f483c42c0000019104010301551450700c0320300410180103919106007a15006001c5080d50051103041028410022038070742c44401004808104450107401e90000c2e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 815166663 1250 815165413 815165423
    0x31902090a050603060402011b0f05030a02010e010207020d0210120e010903090e0603150c070209041211160e04030c0501020a120b0307030506130c210312050f0415060f12 75
    0x30000c076010207103511035075000d518080c0c042c040f207561795001924a908119409080300b0780d0141000e01082c071007100700402e2489900a15911900306c00000e09540850781c00b044181d104204c40e1005940b48010740010541c103a501010385480e100082d10914000e0345a0890141040d280c180d0040045d40b001a44500c6511007030081900c60041079a80caa08a80b219010380c081944244402e22a00480343d0101f4074940305803500c0c4450340803524020b001c0e00d088402c001038030083e03030240342c002c0910208203001070020100d0502d00d020310402401c4c0e03442400380082d283c2010805242c800d41c1200e8229030070800075582c8441c604401440d07014404640014646040081d02082c500401e0040840f608200200041e0b100c4240c070b03006200e0064004c6601d0401c0d040d00080ca0a054601410300b460358001c9900784070510300340544140d0849080390505890141040039003568050480c3d0002e4110f41d91f0904152072818400c010641c50700640440101d0110000d150603040d100058854410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 815167913 1250 815166663 815166679
    0xb092a01090608041e022121030c1b0304050d030809060c031605160218090d0206220c0506030a240602060c03220b04051501060912020f031902 63
    0x780c0701c1200e00f00b01c207840061101501d19a00c00010030f50316525440702d03000a103a0280c012072903000c006685000c100802c42900500303003440396841400740300b035900100a4011485c62400407010440346c451b002c042d44482881b50b103a1000c0610030401d80d03000c0c0c4400381410540c10894103000d070101c24101c070000c1c0980701e242c000030440d202050071359001d66035410644e106400591016106600100e00c000d015500340340e5090090383e039400c0740c0041e10f00303950b101c1c0318503003001c62226040c04908102e4800750362208080c0105481f0a8048048845441103071b0f000c2c45040b0701e00b20318007070180d40c4441e81c8503a0100500910ba002c950001c1182a1342c00e010706044071848400417000c00b6070303200e000017603001680043c51104032000219032004003010600319180c4208803500030200e0800056481d08901001c1001700032007081710401d40105000190800e43c58000014032000b0755004030207044d810306640b40119110300341036964420b8000c060354418020703000008103041c0c003d44203a02c50620 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 815169163 1250 815167913 815167919
    0x408031215221b050a0c020d0c0b070c0b0a1b0503071209081e0d080402011215030b1509010626090607031103090c040506060702030a06051807050307030b092a0109 72
    0x110401c54003503e07500d44070309100c1c52840c01d81d05080c0085060b07800132090112074000400c08007601016107030300c0762003903181c00550800903402350341908280d50320300c410402c5841581d04000d05083c0300300000c0340718140c1c100c60b00d400d508500a00400030089101510008191908150700009640c1d49404484000c94149994107180d0401c00072034101da0400700c80220070b01e12408509500c0790042c10140303200807243c1014030894509508219000c0c421400510070004041800c5030045500000940000d044800066804e001131040c02c003400010110361241c504074403000c0c40c0344d90310310300ca802d1545000307000d0b5600c0740b504a40a90020386494550b4003032105107030a40e0b01540042e001001403401440c14131009150141c12950311401c10301081c00141e90401c8040350040c401c0002244d503040c200d000401044450b03903c0300031604039030402e002540340019002d0131203030842136401d01500c900040780d08120402d841c8020340d684200070302d268040a0f01e00c0806002007030303860f07104ea50341e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 815170413 1250 815169163 815169191
    0x1c120b0604030b0a0c1803020901290a03050f010b09030316050f0f011b020304030c0b03100e0a140f190b0f0a030308010303120203010608012d29040803121522 70
    0x11b40c80c00000c0d40040b03548014031240400e40c2c42e403044038406c8a102e0322900b861819018080e004203514400094075241045801661501050b006103210302c00341f0706000c01300000903182d00400301401f019200030500340c01800010080f95840c41c041d541a28840000d000c1850701922040300920518090130300540141403000003264110703a0041034007900300e801c0c2a030030311041d84040d0000b000740a402e0b1700411080c1241000c203008205c1c070b4038001080b03200300c400b90421b4103004140b51610b00750f04d420081c41d03000c1c48401c148841700341d440c0001d400d0442070000c0d4047e1516081c150f007011241d10048205900b156000341138074001d440751841d500f22071140c641a0b2000340a40d000103041030340100030424002241c0311085409154006030104521402036034121560b10001c0c0c4104042800b002c00f90041054601c10781d544605549428280310b81b140d903900c200000101007c44c00e20000d400d008880c0000741ea220b0b0003d1040068644103030f58011449100081e6050b218509000708200c00d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 815171663 1250 815170413 815170457
    0x302041803020a14030903060f0702011a010f21050403030b010216050d030c0f060e03091002010905030315060d09050a060506041e0e010204090e0f1c120b0604030b0a0c 74
    0xc1d50660082446482654801a0030074a018030801c3c0c62000b0301201c0110354003072001c5032185a409044a80318500781c500203094404012010203040c82410030000d042e6030040b240c14101110f410b0030303044100c001c4001b0306070625145400c0c07021440d01c02071204050b815005031880d554240d007200c083c0f4104100c0403004244a1140c2d56000030301000c42c500107800303101c80c1c1c00254011300f9181c00444a1383c581e0b006640d048040e128550300006900e0001d07190200301e4402901442c4008c210140c0b550765915500d2002402c805140010f0048035007260f1303a0103007140c440c514041c10500000d010340c40e06c3e40d81c2e09000101202c205007864001005170409210b903188403103810301d6600c065481c86071894010b005480043c0a555020400400c0303c400c9401094000c2408100500c2c1480001000300e081181e0800c0105554661300d07034025007268044003440c208113403680001801240d00300011424891680010710960046003000440d0001c4d500681c8400001d484c0c64038100c4584d24030740564 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 815172913 1250 815171663 815171711
    0x30e0f0a0b012903040209060d080c06011511060a0b220903030501120f030f03230405120c10020a05070f03170a052202040902031f0b06070f03081519030204 69
    0xf0740b0600c0040c000d8607045c66034540280005c0d02810044143d5110b203036140e8054580000c00d0380c040b00040000700d41d44188614043c0041c6006c02020000c26410b58031540040c0c160881c0b15180c6c0b44150756683c0b04140301040703414000300b240340b8400049045014105440055000c02d2800c800054600000c0c0c01c101d01d500e40c40700d441400c0e00c01a84d41582c8407030801410104040d643e0448105024462004840d07101488a1070b10040c40c152410385c3c0303002201810008010701c00c0c4203503001004000345100f1030f03002410b009626080c101c6421940ea01032400301424102d5403150f158149078010003072a08000300f0303450300d0846540f80100c400a8030420764900055003100c40740d4429084084403c083c8483c8010b1020030300c03080c281c0000f03250070250000d4989038246070b414044010072a105003444248190b83d15418403000752140c2d015410f01c10740c05410700078110001074804442c400c007806d00140040101700c040b0f1245460f408104407070700049010350303e040c4202c0f042280c10103000c1d040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 815174163 1250 815172913 815172989
    0x1a06071208150d12180f171603240f02071209031104022503033213063306080c0f09150c010f0c080412030e0f0a0b01 52
    0x902d65250b41d0802e5409000e92a80c1c00c20250401140000704003001c2e01008015540c004000141401031008000156655840da55442441550203041c2a040c00e08c0840b0340000002d0114440585c151000303040b80324080308040c2c90f09450114000d0740da0701030811a8024154000040000001501e10383d0103400040d000c010040e841d01186e15140e0000c002c85450074450109a048006041380d440e014208100d01282c1c481801a030149080600005412030007002018031420300d80c2c0300c54601304007170520108280c0c0329400d032051114540103003040350f203088884e00c901440d11a4508001d0110505000ee0440c00b460001c0e040d8880d0714128002c1e4150300c01580b030000e00c0040d0300841d034024025141c01507020621388900056081c0a0726542821000200b000e8648040071011125000d807840c0911040100b480301055403404e0003880d284560034001854660000304902c0c0110b0380b901400ca0b0b1007007134440001c200050070720504803141c00c00304000c6540400c2c942c03a00b0004103011004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 815175413 1250 815174163 815174179
    0xf0f120c05060a030f0908032505090607022e0f170a09030215070c020a090615080603010b060a02030c0c091603050606251518061a0607120815 63
    0x10b468040020b00c040842400c0000e81c0100d11001c520070380740848001d45a41d100801000807104000d800c2c04c00c14a041c206038003c9958030704020f00035005002100b0f0060401240000031511824802e020380c0100013008283d0300004003142e41109681c3d0b4400001400003400481210301400000f003c0c40c001100151803a44c540c0e00039001803040280540841c070a0018640c0361000149585000d200159034400481000340140008652a0ba0140000c0c2c1e20709071042154a48100d1000410503c51400c082c030341c0c45800010303014000351081140d0114002695a03403450700000100410070503201607030440d641703007010000702c8042102c50803144000410f840000c240f0980c0042c0e800000140b0311410004403c1a8900c40a07102c203d40805070545141d207002d001c214110000401e0010300f007030003504140c0801c0c030010502008020a0705440705199290785e028604502c490540203009180c80e5141400d0200e900040d9159070404202e510002c50031111200c80300320301101780a00411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 815176663 1250 815175413 815175419
    0x9060207060c0f08160618031b020415120204050a050112021201110a090905060a141002070513060618121205190302040f0504180303020f0f040f0f120c 67
    0x307501d100c40b54404442c8494000c40a1001850000282011004546206003e51744900d0b2100407030b0546e0b00c0c004c100c14282c0d580240020b602200704110310b01ca107428800c10301a28400f103005030144400c0c9082845400e5400b08003a8018903150b4001402260705010a41369803a6610448501303004264031314104070040c10141c2800b40010204c001c1071000007a604450010650040d0006080800000c03e8500c0030400703d10b5500400e070b0002030890310950741d2460100ca1102103c912000d82e0701401140f402c1e8a135440c028885130380180006000011095141013214008241c540941c01c00b00b40c61508842c2a1701903d0320010545038013101d580d058149075107c10100c072100e1120801002403c0000d4012403041030103408148c5041d440141c0ca0707a082102c0301440c1d014a40180d4090b82c80c107903d81e0130302e208260740000c01c15050700700160740e10039080301e43c0403911400b000c138020710b600001d0002c1ca01c45601c0e0702004540400702d04000850b10b42d840c0080c6840003141c040e00030125a0400c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 815177913 1250 815176663 815176667
    0x6090a0e09031207051b0c030a0201031e15260c0f0a051003050108060106110304091a0604030b091507050702011d0a03030221070305030c0a0e18160906020706 70
    0x640d4104810030300b00c0e810140c03444100c07030741c1000c00c0b0b81d0b441c0000c50100b0710107454604080301c2075001112401502e26900604042640c0c1c40100d10064105511060003030010350300c1c4a06080e254281320818030014185282d650035420301c5200390503c50740c0012020b487c00c031400300c55580600c0c0d035202030031058603c0410009003411200c80182d00aaa109001071143d484510040c0d007910b0980b004501e039072411410f141803200c16480b4900340324082c070f0850707001e2070084200d9040e600701c0c003800181d071000e26290800000c2403d0045400c420000307000f2041c4011408028410304801c412070b070070740840c098414400207040c0c4240000c91001e2240c0c000540c080d944110300c44259002e402c03a0f16403210001012000b0b95401500541c1120a09162a01682110038048180d43c103999223040090ba9004026100003494080507500205614100901c501e03800c5100800041c4a941c040c0068030742c4040301d51007600c10541240707910421400c914082c80d100c108494183c0c0113042568130304031003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 815179163 1250 815177913 815177939
    0x608011208090d0506163e0d0c0b01080307021e03010f0f02041707062a0507090b010201050a060506030a1d0d02010504020a1d070338010e06090a 64
    0x4844400003400b548000d038880140c169500da001e040100013508040301d05c98600100018540d00708882500540017064a80050040e07501ca450045030880042880e40084212150b8601d500c038081c01000700c08241c0d003c00c030b88244a025000896a507641c8189456982c45181c1009400880c034191051283d504e034200580041c10142c0040760095421070540222094515100382c82e6070b020034203004a061282403080c0301e0007000c0041107441c1c200384014060310407007880545800d40c82200d008241e268520544405507201040300d4000d9100c0c42040d01408100640078011340ca40340004405510324018070048602c05003505265884490718076000d8520540c40c6808215103e440c804d0f010400c1081000c20754481e0700010740d5003080e2040002c1c0c0500c6a100d50301c1d89203c050080c060715000c0c03501e5500400d00307080c0020440451070b440c184504e00d00c03518041903244c00c07110341b040009045524010720026a00d286030600c0701e408011003800340c0d40485070030081700d400a026401e0b08400f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 815180413 1250 815179163 815179199
    0xf030612081b2a0a14120a0c060503070f0503040323070206070f061103092a2805030723150a02010f0c1b030e04060f0602031308030301060801 63
    0x289500300c10044400e01c0b854507500004540d01d840d5140030b83d4070084050160307030001c500100d41d103251413454042c0d0741c2c0440040008451140160312654641280d040112403100c81d0b0001c005541984d440d20b0140c200e8004a554402007002c48007030504d414428012240b007140d050302e500d07001040e5080c9115842090403d00160042c040040102507566030026080301e07440380355000c020381000c0c0341003403d8402051515044031014820b0042d092400303d02a0103001410000300c148006148214403151003a64175160000c0341d07180c000c0b0105152041081e1001210424415056580c909040d600e00c564442c1750190b10080d090149203514840c94601c0701c05005061620b0492400304002c0c0f9984030403880c01c0075030b5699528290f03140d10342c09440030310042418403008039010082d20902c40b03e86014018100300c1088003680c00c940d82c41e4070500103004440c56103288c1c65141e44029690360b000d21204c0c0385100704054006510400002224145e850a6031440001e0340381800744000030503520 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 815181663 1250 815180413 815180437
    0xf060a060609083f090f06040b040e04080d020a0513321201151503061406030910180515250e0409060c1205010609060e210d0f03061208 60
    0x766844d00c0d10154902d90192075040154426900c601c0f0341d0030030190850900e00540100000d0004103c020400000d4030101d40e9000580c80301540c5501d00000248100d20940c1d8007244045040b09201d40d1200c090403404501c0c041560043d0b40f1582c201d140c039442c4ca1040500c0142a0b08c41124130301d045501c141403000301520030990b00d50000c1496094558688019100440da01000c01045903501d000c0140090300d81010021030707040021100ca150002d454541c040c032700c004003041e100d410400c0007505210300d20704100319108000da25040142c410300015070356882506042d12404a643ca12070b401032813001d01c00b00380c41c0500085c010981c3d43d181c42520911101c401e51486544590040480c0c0740d1003100300140c11403580b08054801c21b00310b0b08d0400032518000051081c941c011000a041d568181000600ca100c1c041c00207100c40034160020702c0c0c0000103041d041c480b04001644502800064a5a1034034466022040342180e00038443c1d06c241c001c0720349510b80417516400040810303200c25 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 815182913 1250 815181663 815181733
    0x2090418060c080109052208070b0103060b0a06030e1e0307120302120a180308060609060f0915030405120307051207090603060801150b0f0c0f060a06060908 69
    0x140180068014110001d5820030380700c02c41c200d07055510428203800750462040402590034010074a4007490714040c0000800f611445041d8280301c2c406056030441c0e0390000e02c01c00c2c103607141e2403c0c101816000302c0050191400c0100031038558002e004481c822505080280495080900e07006130074443e0f1105001d0a000c00c0181c2e4001c9540e07001d0569020405840140e9034080f000b1511080540003001c00b09402d03d00402141c00202d25001c40001c950149400784d8581c960400195051180d80b04a660000000403001c0540e04010b000c4c009039407007100c45c680856400300c4504d550b88030486004056400c114400d0b10016030300400b45410002d1841c01c24102500b2648940c245542a2507042c00701c3d4181c00100304e4280d060103900007070f183e10390003400f90600b41556092241e03034502500d803040340045000301c101900541507034008140c1c0380031150000074407044140c8481069441c003060300e041c81004580c05010351000c50450365901c00800440c42641e814000d00e02c0c0c1c1036100c600d00202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 815184163 1250 815182913 815182931
    0x6100605270d14161d180d090f06030615030207080912150c04080c011d06030c04060e0f0a1e030203060118050907080618030702030102120609060a18020904 69
    0x80c2e01c52050324030711a607040a42440d0075280c0900d06011415194502c4400300003c0c40210290203a0440722100003102c2c0e10325449065a62000418032100c130b0003544100d84518504642c0205040200d4410a210040d099201e0504a0075112940a01e001d5038110410351010386109034001e00359507018844440c10300d04442c0c0041c111016000b810301075a841801c600711848020030300d19070811b4400c0700c0145040d15001720f49456140f04100c3c103050099000c2001142c0d1704404041810f18801801d0b02d0740c0c0c1c9462201484660070601419001450340c44030025203081c00c1142e40d00e00003000341042030079803600c501e1023600f81c0115000129141c06990001c0140c4040040c2c40c082d10b400804424050031100c182c070300300c1b00010003c9885a11080307003002600404600b43d6049003840c0c0d2400c03103180c0503010b07192440c412064020340561001a12042c4030b80f44460351805188220b40d103102d2501ca49081101c06e50590140d4050602d0200954040241c01c2d07005080b0341001501c04240424 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 815185413 1250 815184163 815184169
    0xc0f0405100201090f0f1101080405071e03050f460813090c021b09010b0a050c030309010b010f030507120203060f040504060218150904050c040b0a020f0610060527 72
    0x41345d204101c030312140015196081001c501e524640300381c021700e0302ca0076a00e42510303039603038840b000e10583c40c10791624400c2c490710203a0401d180c4003858200c8115103804070805840c0d41e444a1000505004101c0d00030f4003000c042840c5112044a14480d0104203101c016a101e612000e07601c2c00112860001003009000202c0e401c10228020700e020381000440041c5280b01a007002c3c1034400305100400740040100b1641d40e540b4100e415215026000c540340c85600388240c5440c42159241000c071321000c0304002402c80c054001c008400c0082e40c27601c03612400d004055054890507036894001c2140c40e4154200686654040c42e0700000041c40251801c0c1041e000c81c003100d100341d80a58075180c00040e440042900520400458041034075800300055000511240314002c0313104a0b442503031140b002ca2002005c920507540608510ba01940d520f601d40580030b03558101e20980f00901e40a00400244510300c03000c00241122416120203103000036a03c0314080c202c03400c036010003080b1140401c40146d0b031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 815186663 1250 815185413 815185433
    0x7050a0914132412170c01020f0309010e070f0602060a0b03011b0c02090c070309060503070309170a02120f0702190801021209010b1f03020306150d140c0f040510020109 74
    0x70403c60300010490101c0c08203c1c080c2801c1da04200021100c8108a03c0001c0c045c0c820314034010f40760040e0980340c11075503020a029107d02411030903554804001e02500c1e90040d80303e40c00d140d6000041705e885641d501618600940d00f40b00384005a088140090300041681c0c001c140700b454014000074100440891400d01000c0d401c00020002e40c1d90b9182d0011800c2c41011243c2004080722074506003c00c80d500142031442500841d0704001c0040702040409009412402c0030036031100700c24828900d804114940758000300705900051244266462403400d5120440320002d50030b0000c980303042010307000e0014204082c568a5006002c0d0b010001303541d0000c5c8050010100351302d4010405040540c4020300390390381c001d2028410304030046e00161112200c0210700d155061424056107036992403001a54000d0900d040c80b140c2c0e0340004411030280c9003940a0003031048088800f220645407100d00138468007403012040410030040000380680e1422104503a84501d2a10000c00c0c02d4201e50f440300c8040e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 815187913 1250 815186663 815186681
    0x20f060a0b0111030702062506050c0a03050a0c140a1202030c030106090603140109110c071410031b08041b03110109120312020a030228030507050a091413 68
    0x9180e8900315007505690040504810410300c6000398107106136500060954072490758400c000090b04201001140f65109075010340503044401001503151088140341c9a03400002c410b00000d1600b000544008480d1281e12840c40e455550303005060014201020250b11100d030040c188403c1014004d292012070004604c0340b840f00560507125450904060b004e1701c0c66801c400141414402c80030260400009403074110794428101003420302c0315000c50340051040303201115903400ba429021800081c21100950f07424030654040050602c118812422540214441c145400260314030482181c400c6011a4000d405028007a060000019004602080b0340d8000c4480e241c441244414542c2c000c501040100b45620401da0014035903980207041d10907064888020300d42c013103031301da103000c1c800d0307050724100825401895002030302c0080202c480541c4501510009090100083c44203100300c0940750940003545520795802c0c102030032074030f0b81c0350800d1005da084000d020002e00e40c0c082d01d004910358 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 815189163 1250 815187913 815187931
    0x2030709091b03080f030a0b03030c07140303120103020d02011b0c150806060d090c090f020904050106030c201212090d02070f0902130f170d030c1b03020f06 69
    0x328449031510700324000303403408901c850500c100820008140101308503030540203484d1107184c0d2a0740341108a4014003101c4011605440003180f03410362120002080b0042c0c5004500102c813500d0400101f59907846410224031262290300010001818807900105603148141400f10031041c074004901d000c0c100c11a010364840400d05020004290b00400700c039208041c0e868031031031030300d00040440c0341d030f108611200e8a40f0340d41e115000c050103821040c0a0107400918001e0100c00600503543d0007a41110400768444c03494034000290040c0244181d48040794182c403080006811801c1c94201d0705801c1120100c2402107014500e505050600141103030b40c001a41c02c1050300f804141280341042c0340d060101558003100040c071810b40203611010889501b0b82015944103640c0d0404400008641e0201c41004e01100021882c07c48d00c3c011500c5c070450b184111056a02c400c1e81c120242d80492042402051485082c0e0701d5602a003204d0b40080350181c0129001130710084a9549050021291808 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 815190413 1250 815189163 815189171
    0x20906032701020a1d01170c04050f060301030515040f12050703170108102301090c1b0f080f070210120b0a0b0a110f1002040e0105010810030305090d02030709 70
    0xa01d00ca407140300500d9400c40402181400c11840016200081d81710807181400440144031100d41c0c880c003080c01e200e40d401c0408812600300400c2c07107491900070740031f418030030f10b1076628071042420702905490403240c20170000c11240024036901e840c2c000f0041d105440144801480c8004039a01e0601e00011248031f584080c1d40e9486400c0060007035600c25100104030301d80c075004020007003000551300001d0000a400051003c41d0070030000100d0700c004072504020403114000141440710358442d07082d51140d519014584200800c0100300410206001421400c80080000208500801034141d031140740105a03e840c030f84c1d400090390403409440c41800190b880420508810031401040140d46080c2c0348005440d04000603c01c07940036a41c0ea05081119420302440310070000c10800174017081130400c0e243c1d000f503003c0b120400795129029045080c0b030300800004a035441101c415204d080900d90103061a401c598049580d07074801c50606a00980c0d00340358902680d020700c21103000303014024000cd = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 815191663 1250 815190413 815190451
    0x1260a0809040f0b0d02300606010906080c160f1a0a060605070302120d150906090b0a051804081b030d0b1804030c020d0f05030315041802010e0402090603 68
    0x6032051074074500b60060800700048030ba501c4400078060754a5045603503140001d01c40654a60000c651003101c01564039840c280c80380c0b42e5001c108d0f140180c0c0203a850054003a200d480a542340701056449100c1c100b810043e41c08408035000b0746140780d87c030400e2512619503036030300c4540744012861059100d0510b91000c2c0316040d8040c0c03054200404073f50400070b0810880d03441c041c3d111145100640503625002030094400c92007035000f240200f504050416400c1e0716800c4c88802002c5da40110041180391101100141c501041040101d0b40010084000d240d0083c00c2c00c582958041d0040750110003c1c8202c1c2140400191441101c1c0c40c468002e41d1500810071041c010b0390484041f0074021050003604810b06c0032102d000070b03846501400e045242500d6071011814140320140050003030b0207841c43e44410001c0210055005d801c0741040c50035050750a0b420003089682c0020014209503184080034019402143d032004c400c0002003005003000c0c0c010000c16400e40c002ca80300304045400c0d042c20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 815192913 1250 815191663 815191669
    0xf07020d0c030504180507020c0f130b0409050f0a0606050301140c07150f020a08060d080909090f060c04030b090c091b04030c0e0708010906120201030b060c0703120f020f0601260a0809 81
    0x274003404003151707034000000d09130300450910032001181d0b8041940b241030004c0d01b47c0340c507000f00c001c4550103800c41e41302c1d00c40c40301d03030640764030104004445890402000013814075050288a46090034595040c085407a00150f010301603201d40400c40311069111a460311481e460b21031002140000c101c0944e80f140700ca50300a1a055000b48804d11030f52a50700032001144103407040e598102d400f035804803026111510302910380041e031850390005120349000c0003a101c8589003d042142c4c490100680715840d000d40e07090701c580402d060660040e80701e80002ea03042103060300086084003c0002d0914164403900d400c250140d06400600c840c18050081c41a0030b07601c02000741c01081d000340c1c108030441c109640d840100c0d01d1003038081e04142e1152206200d9990b04001c6840101c1d0301811110072558a241040780703112581640c0012070710591040304098004900400d1202020001e0f000301ea0800b2408582002d180b460070710b0100000c1c08061410304100152340030707140a03400c0161140112810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 815194163 1250 815192913 815192923
    0x40606020105091c11070b070b0703020304050c041503021818060c1804021c09061b021903022a03191101030b1c0311060f07020d0c03050418050702 65
    0x51045a1610040200c01c80c2c010600701c541380c03001035078070400d0f80b85610203c855002580390710300c040c0110040011800402d00c000c1c942c00c2d2103500880301980d60700c403096003240800c990150694128100d8819186400c0c0d10039160441030100c03140000781c0381c2d004905040d84111500c07005601240901c00b4a6414061400ca911011002070405180c000300d50b00e1940150b00c080708060547c4c285414403661140c05803840c44051452802c09140390343d4480c006494000d1040c0c48803468406440c5400c50398403401c144110f5260000c00880281214202e035581003000c0960441c0200c115545120b14204005041003080584841600e0030020400d42031125010a1710700c04919865210000340c01404452424a001d007800510f415004005c1144044071412298002000d03c84c29000c068001c030540003601d001408032045592494185030140006581c3d034400b50b40305c20504c0c46418410b2030300e00c2c80a48289030060800750703900340c0c100102c2c00c00400040c0c07045c2c4400400103442d60402c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 815195413 1250 815194163 815194169
    0x90b1e15160b0f1609060f0504051e0a1a04050904050705090c0a03050702030703170709080d210203220602120f090f011a010c05010204030b010f031502091e01030e010501030506060406 81
    0xf580c3e50440b40444e000d4040b10b0300c1c1c828142403000c24040c0740002c1e405a000d03a4005c00b00902040301002a030000d0400c4410140d503128483c03a591940814000c08043c05509400d0540c503003d40313058200000c00900042c010801c0b90309104100000c54aa112002080c0c0115000b5002030f03283da101b2034000e000c0e120010121011940107220410110761703c032900071404180e555080007941c682e80000c4408443c640c010400314440c1031005141c0700e03408025840c0c6400c3c4658080705207408076402e1800c0e84002e8503c4003807542c944070f2406104440240300c20040d4460400145000d0540721140072258044400042407041007003000700da100103120011000f14140003c0101e9000c20a40c241c001744084192410080400da100381044808d604803400346400011012407580c0d02c000c05182c40645001c1240c507402d03001400840f030070b4180280c0e4040344008103003911503190046c40121641c0079455142c1095243ca0040c0d00390705085c42694080c5000d41d004e450350f0320300780041c07005681c2c85d0f82c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 815196663 1250 815195413 815195431
    0x709050601050d09061803270f0608070c0b0411010933020f150720060705070c05040c080403020f07030f0b130b07030501090b1e15160b0f 61
    0xc012440c1e07404411204106040080020720844508124004100c0300c400401c1c20000b0880785414982c01012007844071078684005074407004405611f13292425940314080b101c2001007014449a406a80440d5001c1a6440c0092040b4004e44450038a40342c19507050700d140c03140068000c0d00d96031040c0361201920414070310018600400354184c000803450420080c00042c00500d41c4c490920901c01c1008040c00c9500b15844280c060450039000c500685504000c244002c0340c1074036802c0007181c882c0c5881c02c0c0c040940001d5032606020b8907140e0040a0465101e424404041030036030b0b4a200d811447d015a680b6509607107014600640b070144444070803929940100c1c420000260f501611401d0643e1001801400d0b4079040703007080c82c1d0104035100030a5100d041080100c02c0e0382c158019412100c080c0340621814565000303000d04404805c800c50040042040400c0c2a400c0202071484a41900d02c0552301d80740031704940440c14580d08100301d40c084042020b02c00860014420f154103d107500f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 815197913 1250 815196663 815196671
    0x2030d05030606030604090201020c1305011e03080a030b01090308040801150b0f07030e15031f0e0c040509070e031009060f021204120c0c181a01020303060f0604030f0f050709 77
    0x2d90008009010040003140310301e0300d0761241d10859100380304850b0160307800b4040034841c56032803101d440900302c24003d8000c200346c002d03021000c000d2a1504141100d03000104c0c20701e0701094120490282410750119070511403000000000900004024001400c56200010300c882000301200b00456041d4451000c088042c00303c6051110544112510341c0d5141c10606210020320340414403401000d080f0044020001c0204aa1032441000c00c503134003079400b112078141589504940148a1094441080d00441440b00388410300700100b401d60002c400381000600001e083c00002d203410b0104003150402619000040c0800000307004c0d0412458030f0301030a5040001d4440341091584006002410007010101181e501d203000b01041a50b4641100740f407503115898070340d0207079550b04070000b020407517213800601c42c0c05040200344070842c0b02c0142d02441c51611032004000365400e06e41c03e9a68003581c20400000021108030425204612416403510f42140c01c0c241141050340c3c80e03101e01d80385414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 815199163 1250 815197913 815197921
    0x6021902030c01030f0f0f0e06130804061b02040e01020c070504230c041a190c020919290a050d11090a090f060914072103230702030d0503 61
    0x31075003100b000020729000071140200e0b2116000782c68180c40c144011441d004450059461580250706081d914a003154959200c603500e103c00c007e13610b0000b400c681000c0c0400d0003694822410803a068402900d10903150300320b60001800c40d019822061001d80d17001401107402c02080c000c0340c0c020002114200003055031542030141d0b05aa0030b101503c100501c030005124825501c0c1610094240101e6518201d525221014115800000c0342e034403000d4004241411144908001d81100342d014055000302d444041601c10381c0300e0345114100d02e0544882c1d1654404122a482c081502024500c1a04245003401800010006900013074006d60406400601040c0301491406100000b0b8822b041c5e0f954402c1000c1000b4205180f000f00b4140070b1a050405100d00354120b062000c0c001c0c05c0e88641c0c003c01148182d5919443d100c1c0642d003020b1414502038400c052048121034074043e0908a400c40e200e107100651010000000c90000800820b542c0d080d4282000980704040c3d407410304d90300d1400c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 815200413 1250 815199163 815199169
    0x60a1713051b0a081203040317010503100905030c0a060b090c0720040908070305070201110105100b03040f120206010603110313020d1a2d0f07081015080106021902 72
    0x1640340d800884803410140c0b01001529140207841c0202004010748a0310018140380308001d520a07142540004c0d88116104003a03400420754504136031000340140280003615041601070194500306540314041442903841042c011700c5403040c454890031000840d548410100301c4010009001c16170702c01014080c40002910110700c9143c80307610034060038031040300d200014010b4031540381c3c010000e02011440074100354002c000717413030b9142c800d8036403101c5400903004e154200c94045030000c0010707038015010040000c22400454005004521080c90b060850312850a201c071500d1b101401a440b040c01081116032521411051000384802c071407540c1404c81540580c51074244019214074110201d00003000f454880c0e8a4000f03800d15000c89417481c00c0d1004448000300750454151854450500c2110010051105485100240202c03809519101c0c41100c44030701c001c003240010324030080c02180d02c94203019078140819459451142c0c0e507040580003818501044004841103501803003207001a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 815201663 1250 815200413 815200423
    0x40e0604020f0d1104020703050316020f0606010c020a030f081e07023601080708010c0203090a09110705030d0c0e0108090a0b0a020f0f0a020106050a0b04091a060a171305 75
    0x30b800c6502c08030f450b0a138141071107402c00d45007501e54042e20005911042540000181d407043c0400c03603000195803042913042c2c0e22000d0202d40c1c400a0742003040000e8556026100c2c0f1900d450016101240c520744940e08c8181e001c406e00c4003601c81c003101265080703206d826072049000010092a056050418541c007140c900b4910a0012031620300300d82c036191440b2403110601e0212907507540c40300d4541d41d44043e01912607086019944580d402d0039080d481076400081200c0200c00e0207401d14440340d140800c90320040c0100400c1c09240c0604200041c0401c1040024101d40d403c11140001c1c03600c0000c101521082d000c0c5265414817280d0810000c9003400854114040340e0494a1000c80e5540d40032210000d1099000a8103917a4003c1903503100c54008001600c2e0258090300200192a20740c0d040044810451081488030401000207006030265504075030700351403c018044240003040e000254143c0c00c07082250001504442882c0815999000c403190000300b011400000c800181c0c413040c2e110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 815202913 1250 815201663 815201689
    0xc0f090406080114071103180d021804030807020109030819091b0e06041b03110c010606050c0105010608010b030420061c060608010b070b100f0e040b010504020301121101030906060f0302040e060402 87
    0x101444423240440ca0b101e400051111950091911444018503410044080030607038040c0c002030104000602050b005111325440c9a401d13481e00d06c80c80d513540c48100025440e1540075480e00f5107030710026000070b0b4004a00300801c3d2135140400c1006043c2400d044141e1001440303240b156003042c005400d087c0703001810004020b40c9103808949030035001c0b030000042c8103907480440550701e404000034905070302038090300d00c0c01e403d400203100990342d0701000c43d855442801400d042c41000c1000c00d0001710f42881d441014124000005420110007002411981081c031545100c1d00d1800d008074011082e41c419000503080a05201d5215410b06280340054052440c008085209840c049007031104403404000051201080510002c1e072200070506030302c001510210f414810f41400442c03075147c14002c1e641030340c1d0201d8203601716491684030351065030140c0c6801410301d55128898404100c50b405000050142695544011481d41c03040c0012540c110050a0490b00440140070041c2c2c1d820300030ba804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815204163 1250 815202913 815202937
    0xa08092b0905120705010206090c0a0b0a090b0a0302090f030607020d0c0c0906080102090307080607080a0c030b122113050f0a1d0703050f07080c0f090406080114071103 74
    0x1540403403401500c2295498111a078090410105003400f0030000951109460b420382c2a01e6240c3c61b141501c0c1d6407102d041c0c0200d940040303d0401407007030780500d2001e4210f66019141c91800c0342c1e0f8405a0301e1003a0302140405001a400042000080c14045200756140c8030a80017015a807510702c90003074035803100c0300d807100030495100300c0d60b8140f02100d2841c9004c2c1905800400c00c0c4d580e6162841e00075031005103001c0c000e0188400004111401041d0b1910918080e00da885240c0c0c0e403140c6400060280325049810b02d680c881e0f412081d600c610703240008d81d0302c401000382941400f000c0e420325648106040035501142c2040701a030b41c0440501c40704100c44098590000c07854040001440781c4100f600f1010107420b00c40c5903c0080740041070a540260415102041a40c03100c41c50b90340c600c1d808403802c0012035140008503007000d042000a04030300e4854040f250519031602c0000d03041d1111907220084a07074407000d0810205000745002500040329040500c8804144c03c40c013a1603000704001502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 815205413 1250 815204163 815204233
    0x110a0803070b150103020417102a0f030e010516120e1e01021c02030f060108130f050f0d080103120504080a0b13080f1306030b0639030a0809 62
    0x12a902030b0b01502c008e09413a21b000b0303412050320310450f0703a103144813080502550f0038880c43c0380803d200c102c1400461300c281c4c1940d90014426a030241da000c9810039103401016650030400c207920b02c0070b2041900a05410941c9004910420001404c0c40f2174030042c1c0720310031f250a400d9410420000740c44212103071031a0031f486c1c1030b02d100c400e0180203006a0701040c20000f0485d2961815842ca40d00031032080342030a4805032552268001101c0d2110229130103c000141c024146c804a240030103943d220038402c504840b4403012070349006007003d040300240c10108101c10014410000000c07c0714049280c2444c0040c1403a191000b140c1d07807400b289030301400740c41110011884012030741d040f203c18181c00c000480d507101e942104444956002402d880c1c00800c2c00076011440c28440c0c081d2024522004001c1814251100ca81c28901131000707107002201000c0035070100b000e9142ca002002211007800c003075500c51141d003178041c007400c40007060806a6044604401d9980d2040c00e40e0010310300340704050b29 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 815206663 1250 815205413 815205451
    0x1905010f050f0316081e010c050405060c07030204020a0e090619030210030e0303010b1213020a180e0f0304030512030417160c0f080d08150f030a0807110a0803070b 72
    0x107404d203180719020283c9030800c0711303020546107400218443c0414290003040140466044840d0072901407140c04000142e040004204c00c2c0703045000b90a508000030255501240e6960000d4126808001170b103005ca50704d004003201c10f1402c07160440d845402551146031180c9000d4030003c2c900220b000007881080d040c5940b40800e40300c2c0d400341e21482c030850b0489540e035031590051f280d9034004419030b25940440d1800115542c0a05900740380d001d40c00703840c1001c542c0c28050020440303c1d02e405840070181d500c0c800d0514000003081004c80b4150b050003d565281d0541c06e20a0a001e0385007603520801c0300030400d02000854900864002e94030005090b610345080d25085042041e10841c0585546150340c404070746114412080811aa44a4100c4e440100051411365450100315402c2481514503400040d05040c0402440c158034401020341d124a03456580385603164004001c25185492694005c4500d418611421400307441c03080010341c14107900366200c0c0f0303558030300810200c50840d190b0310030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 815207913 1250 815206663 815206669
    0x7090b1e191a04090518062d010f170f0d031a0d060c02011a010c020f010e0d06060501021b030a11120a083a05130f0602031905010f050f 60
    0x2480191401c0c186807001e010785003184070b40580060003501c10341458103011801001410038035002c1c54100c10050000e41d52103040c0603c0e4590804a001d0311840340050060100a00209070741c003820214510181d42810590700102c0c0521284044800d5404003080700003507603000801c5032010302c8519010500c1c0c0c80c15a944d9403a41c0d0000718068201c003d031b005e50030810000f0341282d50b01131115030007048504940300b200301c0d9107103400802030f010075001d141c01805401d11951145031440c040c10440e503442a0741c40843e034040e104540603502c550b603076001441150307414044820280300c14001c08113042e00006c00207448640d008002442055002800b801b641c4a134002c401071501004140d4214541505118006030701c03a80030185980c84003101d4540c0c0201070b2040160300003008968040d5070b080c1d0300100c00201809005510f5401c41c0e0300300c0000041c40c40320b030350040030b01c914030140e164100040416844090b140c8692040c40c18170006005503059086000c080b904111041c1008032440004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 815209163 1250 815207913 815207959
    0x2060403140c09040609020108060108070903023a030f020a08030c1b0102131406040e0f090f01090c051305010305030a0e0402070618150207051b040b04090507090b1e 73
    0x710740c0c020300f8030002c00042c8581d540c442c4050714000c1c0c130b42c11255602d8400446020740d0440d01d9501044000c54280003605120802c1c070303d0300d203640d980b09030340d0b101020703da00c1d458200000c82c401003040318003041c04056102400c040312113518002018421130603902c6014601001b06a003115002c040381058180c0b04690149800c0200e0740021503542c41080d9071464003040741e010710b1130091485000c003c11818030008480481f02c5244019500c5d0b1100c2010307020000000e80700700414483c3c07011902400400703104600070035206441041081e4649400d104143c26850f14440385149804010404103102101f2501c04200c0c615042c00490b60307850000d0300a000c5c4e800060000381ca0700c0e00002c0503c1111601b0120f90340030b05175082c0c040c408452820140d2103030b0b85000300103030000717130a070304071010801c54a40c0048001040862211103403070109049031451002520b240d40145010042054148144907624000f556050204550a90b010a55001251901e0700504040800d4030b405000700d0f607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 815210413 1250 815209163 815209183
    0x90b1003090203190804080f1903032f071202010b24070f060b03010506060c1c0903120e0901050a0b0f071a0705030912032e08010c090807120206040314 67
    0x5041041395181464180b5420034044c14505205203013840800000024170003480038440347c00a40000142d95080b00600352100c4490700441914454a03201c003004400c0c3c045580034030300816140d040506040c02c042168010031419645051041800d175210072243e0440ba650030040b420070110400c281e002d09104015002d400c540ea160784040c00c000c1c0b00c0c0c002402c2d241044000340183c2d181e003000c01443c0d00c2842c075401ca00e9403042a803d103104010811005e82480b10781020600b140e96512a59000c285060001c40020910007628019240c06903055014100c1a1203210f0080d007080040b0506200d844103035001c00c280810b9120411500030800103a2212103501c000c4c05042900c005080b07a002560b6120140c090004010300c3c0000f0507082c2ca100700c0c401c00079840f1485184029606164000f251120510090350010404040900407511010888d0751402a02480c00c020300b420030146403c43c1d4141126200101c1c00741c2d43d0b1a05480642c4c0c3c000c07094010381100340311141d2a00171141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 815211663 1250 815210413 815210443
    0xc0201230405150c0708150a0b0f06180a151d0418050d0f0e100813020603130506060402210709080601060807111f0b01050c0106080d09090b1003090203 67
    0x30f290740003c0440d00000e040840c44620894084684034642d0075107030070340f420400008582070000200342e40220780111840c104e0291105003400380100200301e07035500c40e10a80d1000b4034002c00e8000141428054a130040c000980e03a03031040e0301956001025044000c2c0242c2000d141001d820586076502d074400740c10680e052050040c030080030300e01a0344806401c458180403a40c208840c0401c1c0d030203202c000c0e075185002020515030529111050b0342c40c5002401076030407004e00804000050711000e00442c000d5007a1440c6240800052901500d4490002d00302c030b000d54014000010308000400c0d1240060100212648050385c89150807604020301e68415100c602c02c3c0c000025500e60019401801751300c1c02e64659407d48203503008207a030f0f280007113450318003004041a4803c00340c0f05580208036903441403404d18030701000003400303070700f03541c610b8100314010380215103440071032600140d80078000c10881c10180005110300e070010701540154030744003040c03548500b00d4404642e0144090031307003c0691 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 815212913 1250 815211663 815211679
    0x3060501022d03130e07020607020c012708010209040e0115030204180f11010f0e0321070c0b03011401020a030c0b0c04092d02072301061d160c0201230405 68
    0x80401c2e0715600d014411040b500c017241d00402c80c881d02c08035400f0b10582c0c460b0010545510a8001150b0800305078a9034408c4007400441e00e9921010915034900a1185030b00160312040340008200880300c0384495080943e140c9010100d0f0107034601a00012070350110740004000c10101c2c0e40c0c00070380d40580d800920720f45c44500b242040206990241004640a03a142001c81441c403600352002c003a0b0341405985a84144902050786001486080301da8070414002400e0107201c0c2e0340d150142e08690000703596400c0c084014801140a1114a40102e80910082040d60b0306130302c02600300381403800701400b501001c10009002020460480c2c00a1000c80001c200c05a50303d110301580c4a0041e402080c04180181d6940200c2110b000761100c094005d42c83c81041011469010820444403500807995522100000741c40015420f2258280686c400540228607107060031010300035402e0792540074003050001440250340e000310a00720400c81c1c03023440c030016080c15811000c14001c950200b0b41c0b210f00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 815214163 1250 815212913 815212927
    0x120512040c1a0301031a150d0302060a0c0813030c030e0a080f0d030501080309010e030109290a060b040b031003050f1e12220519080d03060501022d03 66
    0x109040341d400c403101000450510000001c55400c80d200c20300c00035084800740e580a04004104a19003500700265129158074064220041023a00903060310681c0075030000400c000ba003414070701558a008007903280c041010300c2c0c008210340600c20b64000180030441420707110303010580641602040381f00300808142031142d030f9a01142c8d98070345400003132419004500d000000c25001c1c2c00384905840d0b03260061828100d030701c00110b0b01c0007440130620b0340c0742d904d54241c100801c00c81013400001101c40019040403140b03c8944070241d00c0b014060b03240f01c0b841c10b4001c04c00e0400582c15241030f990500100ca075a030302d812024803c10714541d0405421400f80c050002c0422000141d100c000005410b10341e6445607031012803603111034400c446016403501c10401301c09805085165800d080702c13961028445951260003003031014019844141d244800d00205104e04241040a01d0200b800c6d803805110503070401e40000c3d200c1101c06440c03103025001c400128039010280c400c90030b0140c0b43d0400c6948440d0b0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 815215413 1250 815214163 815214173
    0x31419171c06031202060f01090b0d02060304060c0f0504050d02060d14090705030d02030c12070305120112150504020a170102090303190905030d0905010c0816050109110d0b0412051204 81
    0x2d15100460b0f1104202c510309005038000b049152080d0550740c0c021003140e10b000000c0010700151440c85a010309003102540050340c1e190095805180908000510807048800113131400707030f40074662818000700b0711042255a81303003451443c010b40d054a81d540c0344e4908910702d1001d01240c035892034084002c401004020340c000030300780c01142c41c00c50407038414194052040e41c0343d1080e60084062034006846070070301c41c20658000c250152013860114604007000300c141e02d6240b003e07006061004292007000090029501030300095040c1a601040603082c15030000310700c80c140e4410190f0318611852280c1ca4000d080d4141c0742c02c54005000c1e0ba54031000003084400c44101c1000042c080740ba0164041040d040000da8082d042856480f6241854201401503d0032a81408210b5401008100c84101204045e0508400170310440000c03803001c0e214075155504000b11452540515005075520000c602000314503034000d6000544000c6c1c4070301140381102c82d44541c005c0400345600704024082080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 815216663 1250 815215413 815215421
    0xc18020f0726090607020402070215070501141e06010e03010e0102040b120903040302152d030709091a0d14010c050c010b0603010e070f2304031419171c 67
    0x416140320040b10400704a1040d403490041100e441d402c050288200001818998010084240001c100700148036a038542d008081d8414001151165128a1110442e49069000d5504480c1c000004c071f400880111440303290100040c45103040152401212005450a50000ca000100e00009641d140e07110034020002c3e0744943c005018546a500020345160404000d490a40f50300924030b204c598000d602e8128182c2000b00c803540300507001001c4d040710171001000240c1e56109000c40b40e490b85888907015019800c40e070f00c40501d16007081e01c0f0a0310744071407070040309030503104031500b9259582a041902f680d1035103504402d0150310704111105041d0b0080054054110428021f03c030800c413070f03014044140828840d110a4502c000081202e00b03024401c040800142d40c90a205034000230b02d1600d2007450245c1c80d4890340080010b0500c184038403030744140c0c008071800005090503404203c001c150144031610140842e851002840100c2c000d02003243e8043c0c140360f22080a400d52000d42200038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 815217913 1250 815216663 815216693
    0x40812042f0108011d040206071506060818010924091403070c0f0b0403020f060c10020309010c02070518190504150b01020a020f0603070507290609040c18020f07 71
    0x4125028000110350070b82c00d07179105d000e02011049061380c2d00c481e805c0c0055074001040807620406c041e901d10220300d91902c103580c0140010b507900c02841c00d10039011a103c150565545085904082c003c8001c100242a000f010b2122041810a0940014201c40042500310b00040ac0720515541c0c0300101100040a816558000c80e21410203d54984569584c0c1c00d1922814220000a1104001604d044103040b5424840502030910f001c401000c814204000003418101c402d0303000c07040c801c940d0005d10030454400340e580000c00049007454002807040c0c400d004100590800c4400040e100c2d9000d40031011211003107002849a810f09140c010300b44400e0a60707164030f1600d001c4c0c1e800025031000419110943e00030303100303080c82118031042c02161381c0001c0450060020400c5030200140f03072641618046002002625620103081700705540107840a441103100f081d040c0309110210750042d0058045400640c4c0f81301c1007007880d25070f24003e406184000b540c0010003003209401c1c001d45002c40000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 815219163 1250 815217913 815217917
    0xc07020607111c031e1713060b0406081504020102150403080402090f13170f040605120603010c021005040203011b3c0320040b040311010206040812042f01 68
    0x103c03820340001810703001c1488406000a4419801040741c3d4170101e07415103500c80c00e480c15800e10164014403a114640540700b070a10140444512814000d06220f141500c40049405200c580e07d040d0115558069120102e031481d642c1c00701207003c581c0200015042c40c1e03c03507075004079980b52504001c0d055200c11602030b03003d0001c0758005060a107880c1c45052194000800c40f4406d109141c6501d07040000143c201010401c04101078a1801d64520183c0010450796540942e94600c2000a04d044030002d800d441c001c1c3e040c407010600c680c2d004545658806154400020710b95284d000185c09416000c204030480c0000c12100380d2003a500420f031411911480b14105250300250b0340f460404206080d019200340c0d50240c0040301c1e14401d0300110841c0e94040c00194442d81009664803080d84036a102c015003940000f000c00410941c03822202001c6ca00340050540e500d440d0715071084902c00c2041241c10f4040d1a80083c0c1048181300e440100300524004140d080e01f401d08001041950701d03e84140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 815220413 1250 815219163 815219179
    0x106020d0f0f0c05161e120515100504020d1b02211b12120a0b060421060c020c12070b040611120a082202030d05030c0702060711 57
    0x101050268120050055159a80444210041e24112107030fa111a030200d605004e04094013680c0c1c0e00c12607050b07004d0001c008131007034840d854081c82c0c07401550983c0183c85640308030380e9000c04a1004100080c80321b001d00072400340765444500d40d50849072642c00c401e5100d03202060030749002d0002c1c2c0c4500c0026445032818421305c0184070042e84c0d10881440c50080e8050041801040080280050904858603840091095401e10707a2070781017180701a01880d950f000420b0101e01d02c4009401d00750408c0c004001008a0200e02c400301c0d030103100f507000d207001c1c00e07004a454180c4072000310803080c0d450742c022508000d0407522100c0251602c46900100d4860005000031081304030012071200c04075006036410700d10b09450050262a258091400c540c140e01034000c0b4006000701c1e41004004d1031002c2c0d40d03040b81d0381c54404c41d905002e0200d0700244480b0a403d4880d20016180040d030079a42420908040340c0300ea031881c041c04c9851080c0e002c0203400c82d8001c03440c41c0802c00c03800151016000c046039080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 815221663 1250 815220413 815220433
    0x3070804140d080a2f0d0b0901120c06110d0c0206091c02030609030a0c020f19290a0f032d05091203061305060f120c0f0a06120b130e06010602 63
    0x170a01c81c8100c180f203110580316080ca9041c12004002030014007404100031902e01000800108802c000341d0012403001c41400f8041c04205580090001405042c01c0c00c1c607003c2900300d11300c2d50340c4602c02c0c09041407005d580603017425951220195044c2010040c80003e10741d03180303085203080c0038414108030b01a20543d4049650b03100c010064861558155440d540d0403d030540810000604401099410483e41c0da0015400003040c00404003408403201140082e03d64000c03010030b401d0300061400f4044105020850106a00c03002d207407107494040c900850174824102400c02c0310034103407458a03415002281003038100c01c110380240d48200c40403410380310100003480320700d81c81d40f0049a485a02a02c1035070010003d86082c0d11440e006403026050140c030083c0300c0c0100b0003450000300c01c00503540c00440c40111501e048452114410303403d4035600a024a44000a450144480343e03501c0e6547c0c0703590280d007240d1070b140d545a1141c01c48410901c07409000c03074486605d8000a015840040c05090400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 815222913 1250 815221663 815221691
    0x6060b0d0f06060f08100e1e09010c080105040917040f0f080606010804021e0d0c05040c09050604091107020607080405090c400f2903070804140d080a 66
    0x2c40c08680c02900c403070107554210311085520810060407406900805800803030640504d00e500c62150405000b505180080792100c1c81c0c50290040c00d0341d0050303041000400280f9030004640307044560aa03400b00e035100c0a0325000302080c00d04841c44007074a001040c0050204520b000314012500d00007030700c10303620b074440c514603884001c21a4814042240c242c08100141843c40f0031481215a034803001c24000c00240000310008034010040d60400003401d824051850640300c0e00c2c28004032030511100540c5000f020034003074040ea100b0f02180c01d586078403540e8119401401c035040598002c0000e644e8844520301110960401d0050740d0080a0010000e600315150320121a039255800103000c6221058104155506e5800e9140c4041c0d440304400750903060f5030750700c0400b029203a2040b002200f44d040c80b120150750100841e145c10801d02161050b541d03001a502200d410200d2441e202c102540c4a0410207405000c0380740d40182841103c4000070800c0e1b021440c00d000b008215803d00806100381c202c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 815224163 1250 815222913 815222921
    0x5031e040e0127320402030606040b0d05190b06060406022a120d02060c0f04140a08060702010e060703110d0f0f060306050405010e03031b130306060b0d0f 68
    0x40d2121118034000500c41c404040010746081584030f209900050a421030340010b4809510141c074082d0b208000c0c0140c0c008090344040b07008801c142c400c071240d00d0b00342c0009a40702d0000d40040e009981d40c55030300d00366440302d1100e8203034142c01c031080700c1050040c0c00d41124604644001920304441040104400713180102c1140c0480350668014800034001d030040d00202c28080940e20510b05551803120a26201c0c410702c02124130190001d001d005d44074010190410300020039020303465000b0802040b82c003071450140d800b9101e41c044070401003415540031407031443c1c16030004001803081600b00300c1010780c15041400d040f071104042d43d0061310707548802c3c2e007aa046d0381e01d40014001d0030322032807948120b60782c0005001390340e9140200361280d640c2a1041200e0094000340c4a4030340f02e00411007401024010a55180070b0b02d0010f41c41c51900410480e4000710b202072100c0140c8001401780106041440300f1000b541c2c010108105140c0d50348006100381e413204010100c1d203420302d01d480e80c0038601842 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 815225413 1250 815224163 815224169
    0x121406061008010b030723120a020405011706030106090905070312021507030f0b040c123603020a020301020a030606020c1912050a05061003031d0a09050a140405031e04 74
    0x2102c0c5a541d0070680a080f25400041a0300200454580d1020b4250f07000d50b098003100754522401d40c0c1e03d9640ca9900803203440001e15009c0005d004000401c10703a680000c81e803105205108040c1c00903140c0000013805800c0d10380c424401e07142004400c109008010850100301d9100700d522101001c005041641c032203c004c04480b429410480c0020030381c900075045084410071b41c49001910000410010b011604180d92040024081001c0300410b0720040c8107c1103d00e049222440461128803199080c440c43e2050840030311942c90702010405000704441e0f095280e00800a41d124030342c0e0704004000709640c0c40b84000520585c5039035401d41c00e0580b640315103a00000c0101207058100541c8102003c10b22008480071300c122801e51010810a000c41809050003c01400d4000d155080c020220200200d8401c544007820703241c1500755460700c1040301116581c0b000400c907540c52052250042c80244420349000c1c00c40400c1104100c07000c03000b07104010090102d18210a0700010320f00171400b03140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 815226663 1250 815225413 815225417
    0x210c0509040e011b02030c100209060d020708040b03160305130309061b060f0f05010501090b16080c150103061a0a0509061f02010e1e06041502041214060610 69
    0x444000d05040c00d801155042c0c07003010012a003074410300c0014921016030003045005030070104c0c1070750300880e092188551140f5035480540c10312440c1c0000071218440c0c010000c00e480c0e03002801030100540001a0740082440303424554072071619103005081c50032040b0a1100082c500350000c1c0d2b07000e120340c60302e5502d142c1642d07620304640e081000564509000700c104601c0300142c00d01c0344002132040d01402d008a43c0050001c80d01103c11341d96407007560810b81002d418088014024031840e041c1009a1320701d1320002860b620080c1d558244060343d03100310104141c660040402e4007102c101040d055074101c9208040420151107864440340252059414160b030000e04c407c41041180380010302c10360001002030450b544500c401002000c0007201c9100388016035180c00000c06c51400900410800007410720982d1021206d4500d480d0b203844002300001c10301c00c000e2440c032000108660503a405008001c41c3c42d204650542007410314a01e4916121600c0e01c501000640d650030700241c5040d1010b440c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 815227913 1250 815226663 815226667
    0x40e1e040f050c060a030b0f03030715020a12320115140d090c15140a0f09030606060509040612050c101b0b24151b010507210c05 57
    0x2680d01c02154103000c1d001903074148920365505803580d030380350700408008010352000038110b500c0c2410300401061844405d4480c0d00b0500c040c0e0040380840303501181c1100e246800598903d0040ccc401c1c0d1310b040c031070861580300e04d10785020001880c00c051803001e0350319070364082128680040c141c6030f80518824004c111110402d480d40d1071489000d0605a201030700d4005460b400c00d0341c169260f1040303414641068606010881c800c003c404000e02c000c031002c001d80d1620003444504407660f40c880c1d1044c01200810001580101c017a183c0c03095106d240550351142e8180451650350000501c990040380116114919200b00042e41244007110030500303da208000e000385014250030081c20501c688601010300004688101032604547c4409218501c25807080c0303003d06144801040c500b550348016886110201024282565080c02420006c01080420f035078400402c0ca02c1c170b03202004443c804c1329a6081031b0a2285d003d8101461b02100720161982c00a10980490400140c0b000608000023060342 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 815229163 1250 815227913 815227921
    0x309031401062306040506031018050c04060c050f101a06130308071e0803041703060906060307260417031b09040603050f0f06060d03080c0c07150203040e1e 69
    0x5140d000040c1c515000b040300307045c01e03555030205810b90b000300c0741010390603801001400303540c0740e5038035500140f040d04804000710724210384681d64034421800b8450a22644500c0718080003c20885105142c41e403105480b586a108240b24010f801450f00103c4070302220214813040d81031810a50701840e050f070401d515110710315140c5239070a41c0910400d031042c80c6003d90369954a5152401442ca15109084095032031409081220035900001a100d01c1d66104005000381c5584540daa6500314404403000c640d83d8544660a0710505040b0425200d104180c4540c2c40300400c1c81603c0d00d11440c049d2001400210341a02c00d0043c601c0115240504070480009903685407c896015010800003e4000a100380e2291103044c5081403000c40c0040d02d234040041d10000901c2030000c240c00000980d07810312101c0f06607902503c4120014000e402c00300e000b0420600010080060703000400c00001814103c00300740c01c1c020748960281c010304a00b03000341008140c4008024040616040305414030000c6e50311 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 815230413 1250 815229163 815229209
    0x20303041704080f030c010605010c0803070f0516050a020a1a030705180d110a0f18020d06090608070807140603040204090302070323010b0301020f0a050c0712030903140106 76
    0x41c01e0740320315030110010700012074410001c00c078180148180800039078840210705800b6003980c1203034200a04005a4402001c0002e6032042665003251950a2a00308a000500101c60f54081e800300329255013001c00e00302042c860081910300201d402a18110085030701c0e4a40c034510303140c1c4001880e00f550020000500c1c0c142c130036005401329810803070742d03007802150200000e0341202d076945041d42d1140b5040006111450310158103c010110382200500386480c09001e1124441d00ba00607017400e0f9000241103502c1e800316808a80503003031690003005441d46a007801590385a541c052181144240000401c022840484040d00b0307090041c1400e146540355401e000180c000004120154812003001100180181c40b142c80b981d10403100001c1030380c02da00700b0702d0b0944516051580c007a910422400390401074550807a03031400301ca410303c0d0384e0724031a4000c000e00d40300c00350384a21400750741c0089030780c04c0551143c00c200031240242d0390807c0620b0451000c03401c94015201d00b15502038040c0b04003400310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 815231663 1250 815230413 815230433
    0x503091f0c08062704031b12081003020306010605130506030c03041707050c100302120916090e0d03090212011404020f1002070611030409060b0a0929070c15080402010801060f02030304 81
    0x4e10074a011241a145040100740121f0400d004039803250b0141e0640704400c3c1c1c001241030f4841d110304801d000c50b82c590f401103a1640c0042c00b41908000d0005000101c079989206244000c20010344020703a0b030311f4800603903c0580c00c107460440c0d850548052401c204802182a949810b41040c0500032520f04a010400102c0c56008258181602030003051090002812860b00c910705500c081e01e000c40c60394910005055480d081420500c0c1b4003040707951013500008032010300401d40c0c02e00007401055070000880b20304000141e03503403641c20134016401c000050780c40c80d07015620990b030211014580d0703010460f04645c000065001030744105010061584250032103c0c41060030000d0380d16064807000c101d419a0081c3d0000030ba411320001d40b03ca04a0f501c800080c006001001c3c6651901a1040d0708520003411035000c4010b000300429020f046c080102c03140350007451013500d4803502a02c1b0480141000303030204c03426408942080000601c2d6401a02c15180d101c82030350241d0b04e503aa07507940301e0000c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 815232913 1250 815231663 815231671
    0x12040806010e1e161107080316061b03060311120307231501031502190f050f1c1512080309011808030a050a0c0905010503091f0c080627 60
    0x40110b0280310302c03003504180c410390003204001e4140960312280900505450340c0356402c08501c0c1d110006c00c2084602c04000da5a848000d80000352844040c0e00b08900900710600301f0200000d480c5d030715102125050b074440c0d800c0b04d100d841c02c045040030b05c80c1040302e912581d03500031041e50020406000000c840100d040944c2907469460b040641000b041a072921504824510349102200014000d000404801d00c2e400142c0e520150b02c0c02880b08000550164030484130024400c100d20f644154034000c0055508546001051944a800750642e06060b00b036215040d0240c03614084442e452087c40700c008100b5140c0000580b014044140e0b202c00c00c50740003c00388520f0b5580ca0102d5035450609018000381da07401001708030b40720704048030ba2504a8402524071600d651a2000040147c1d82017940c28080b12024240300c0d0f10313561400c005038202607594117503440c0503240143c040320882050344100300541d000d5899403100e545030010b208000e41248034002d0300303040030440c038185030400303030421544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 815234163 1250 815232913 815232931
    0x90b040312090b0a020901030506090603190309150305060f03150601050d020c06070e1c03080403140d0f0f0b09041e02060c060a051803031608220b070212040806010e 73
    0xc415a5440f200c203c03403c151041e488a0b900011055615a818080d1075041102103030482010f080220009030340c0e810302c19251159203510600081410300444143e4024400244828501114008010001c0c5800c59809216108000e01046c050500180d1200d00414942d4050080d403100340064803035400c1818540d10f41a020400400301c090f050008602074130040d2100701200000d482001000800d01813101d48144082040101095200840e0b0340c104d038050600180d2000714200d0b581c424400c80b000c600000d03003801480c40003281940c1c441c8400f4000041e00b0001c0d035903000f042250400c015140609090900d0b281c00d00d1038074480182181e000c0c40105401e103400f958074a039505000040321030001c82940e480410491000d044000050f62554002451035031a0a5001d040c1030380ba2016140100244480090072440002c1c00c041c0c00d1641d665108140100c2c80d1030840803041003200e0000060251a010410000c0400300f560151070100002e40416030812041c032815480040c03948078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 815235413 1250 815234163 815234171
    0x3160524043504090501030b0f241f0c12031517010213091401150f0810080703060e07060c0f0807050c0d0503030907060e0a03020f0a090e0d080a090b040312 69
    0x42d1050b0500024001000251008030b810b43c90b5003820161408001d00b1084d20361003200410070844000e498007509005810311041c507a03019031002c14004501c25040d4001c14462690740c40980d034001c9400c25280d40f1a00311140c04d0310a1407411000e82d0300700742c01d08004a01000050040b5103924900c60700c0c900101c4001030038952003610760070482c1d00a03070085000c00e03a80d00c110241d0207900d9150b14094060171482c9141004950380040c41c070138041c140c02d0308200b001000706191a90f143c06050060883c403003241c48241d1a814601d00600302e0400c0304071544580c141c001a0640210f0350070000a07040300307600c041e007003094890f0404d130350082c1e03001c0f9018040e42605030f92955501401989480c000c4000710b81701d01d407034181c4a1420815800c81d1042c400c45c07590844450303030b400300b0740b0003500e6040e100c0309150f511160204240203620b8000701c1da964102000d0b040600000122481c081a00e81d8070010b068484440c040212556080040c02c2800814001000300f80200c1c049074482e00603401c009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 815236663 1250 815235413 815235503
    0x60c050a170d060f0b0a0503090703021e190501050a050a021203011202040e01050f19020415030510150c0b1f0b18090112140316052404 60
    0x79035840204065101101d50202d0350911011451040002a0140c14200b807139080c02c1031000402400b13030803039903010030400100040902d48148a003100469000c3c0c07260890388810114040701c0ca001880c83c034000e044000594050301440d040700400c8074010f843e050b20380358404074111441d030b201420080943c810100b401622440341c40007103000740140c2d880307020101064410441520000056911540e0501080c40b01c07211600c2000c40d00424038448003c60401060180340c064011544403011540740d40c14400c0180f509908114450384800343e0115420f512400108190031a440c400c1c40019908406040050202c510658114446da51000d41c1940200c0c44003200f683e40381c00c560300311a0b01007160300b00850503100c5204481d40c100c800594a6040c010b5441c1d00e03030310110001d08800d542191030866000207000712101407004071060308540041d42070480c1c0d600c264020040610f01c42c20703141003084818403200d50295a000741c07640c07100b10583c002c240074180d880140e91812503800c0c03418 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 815237913 1250 815236663 815236673
    0x50c070b0705030a0606171603090c0b0d0b030a05060f250c1e080f0d060e09070f09050c0a030b01050d02120609060a210c0b0c010f05060316060c050a 66
    0x1151081065690b02581c910744034401c2002c1d200c203a4070580502101000710340100c4d6003208415401040100c0001ca110301e0184105c001d8045e01401801d01a041040440c0c1d0701d000c00028602e141440074284a13841944c0c00b41603036520940e50140550b00000007254124000d4440e264006040c05030340c01502c44820306402c4d5001404c10a90003248440343c1038010401e12810b800e10a4492007401c0e0581d401395110450144038642008072601030008a0000850569218001810711342981203882d1401c003155580d10480ca0003001649051840c2c001001c82640c040c50713200d00304003843c0700c2c186107101509501800c6030580c9503060200c10b010b02c01003001c007480a4441071407065540359882c2007000c1032145003100a40214041c240d401418400c1c8010500740030300d01c40c49001400020042e41c242140d10800355044200e10307100c0003402c1070200034150003a0021644040d0204403517102c007800c0694840d00705200c0f42510900c4081009540c0c060320300b949400f4024010380740c000025580e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 815239163 1250 815237913 815237933
    0x160b210108011e05011512060b0c030409200f070f060c0f1103040b0703051602130b19080c1314070201150602010501240e030703110f04020f030a050c07 67
    0x3001d403180e0740d900e11807070101c14900704080d05a0303240c21040040d94100380040c81c070418400185018090a003101400d031005540c007960003171450403a0700382c60f6501d40c10500e450b94030900c03568104074200400c0c8501880021090300704c980b400241c0d2441e10412180c002c009820054040e40c0e00c44058882c00085003c600500114001c50f64030309101102d60b46024210412040307406545910620042c49103244180c2180c501e90b030035041c401d40380c05a45030402c41040000100a4110701c1242520316041d4040c1c0016941420442e42c0000d224010a2440c000700b22510600903140d0222a8006203410301600c0602c912600d07000121f005a800c0a5090001304c040d110100148c1d541c24524000641400d040c1001c0c05191000b48025490720f0003514001e07503619464501c04110035980360003a030080e50194100348002d0152081540e80e824100400054603642a00032810b036001c62880f441e051007140c1760b4113042840306055840740c0c14840010080204bc000ea1070034200019000724100c415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 815240413 1250 815239163 815239169
    0x201110a0501150f170a032d0801060e010c020d0b0c04030602070c090b1207060f17072a02010507080a050c030301030606030213060302030c10051e0714160b2101 71
    0x241c110510b25108000c2c213100d2255104051a80c0188801e2020050114200c0c5800341c0502e40b1000d460f6400e901d8500d803480c00300d500c407a0b00c4401340341c40c038526400480980c1210001e0310741042102d81e420040d2507900c0741c0d02000b907010700742c4d0003480005071030189003e4111141e400e11508040c0c0701c1d5680d4003203a2100c2c00a40d007404c54000200070072a4540035040d00d1180540309a100d4500c80e45e4865a076000c18010001400380e8020048951840760300310a01558031741000002504010601810406800c0f280b0703040300c2106040030022900c001d150545199060355098a00740454607400e003203403c1181104200001041044200042003024501170740c011f440008002d807551040000b400c0260110340565401c09100300003590340401c919125072019264010f10b100d180a08070307414130403615882401c18420307610b26030f14544080901b5061380300351a10344500e40d0340c00320325994641d00010102c4031079034a18280046800007010f0b000c10201c0500d1a20008607156020b5150b481c00d0b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 815241663 1250 815240413 815240441
    0x20c04020c07140103090f0b1b070b070917120306040f2a0305062b140705030c090f0c0c01060801051620120702030f011401031505010b04030201110a0501 68
    0x1c03e000740007004500080081090030704018419040c0d4a0b02c001c2c0703071001c0014154134030b2400042d41050500600040c03002036410803580c0e0f0000c502d0034000760001a601e07400014042d140100d9985006c501c805104050180207080c82c8684441110440d80001c00c25034000f5143c0c178492082500d64001c0401030a50103000d6010420300181112840441581140800d414281444080e444000c0e0140c0b4143c0c00400058121243d030020b0000d82c5040d11004284c012030b0b90074a450504041410300076908220f09030349058400c0000c021050701c0946400b502038401e0004504000d00c00401003240c0c00d982c8001249036a65089403c0c02c40e541140d2450000320308000000035580d1010000080c1d42e4000c0f04400b41543c0c02c440569142210417996440e1070740091510299941000811455134045000788000580c031100c05684041c20301c070899410402c1010305d48072900c03e00860b81656903090149081030b1643e001142d5410700c5508102d19070060100843c040380003801600b03c544080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 815242913 1250 815241663 815241673
    0x110f1b030f071b0609051c0b160905030c1c050f0f01060609050301020a080c1b010905030c0114070f0c0f0b100f1401090e0a060e040b0f0a09080a0f020c04020c 70
    0x58240b090f03070b54040581c20070500049682c280b04083e000b9a256007515070540e520000d080c5200010701c00c0e186004c6c4050800b040e180d0410000c2c0b46c0d198101841c0304116959111001d07a500d042c159281440120507601402d1016225043c4294158264405004808581400300c141c1001800c00b00d407589083c00c165107441040c050960020302ca00010b140c10f41c000c40ca4000310701d9000f000d140014144400322040040e400c9150090002c90088580740341d0020001d044c281d29003580c1e80e03840910100d01c254208001d5940202001161502c1240e090b01c1b03a06160070f01d04400c44aa610b40303e81250801e50134010b05000c0340054030250f10400030b942e405080113042180008100e480c0d6800360840b941900740440c40e50b64085038181c100d03040138201e0f213040d0b1a0480080301a082a030000e144a1000c1000c21003400f581d00000c2c0d000342080000c9038a252a04510001624400c8a025144400030403081e8042e40c4140e40c21110a0701e00c1c810381e500190124001010780e8070050503905142d00c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 815244163 1250 815242913 815242927
    0x221120907030f05070f0501110a110a05031e0d05120f0402040f0906050714030108070b090d0206160b010803120c09040e16050a0b09010813031403010905010315110f1b030f 76
    0xc0d1b401118042c11003400d00311400507114000e0b5a440e480c0341401402505012400a50343d192848a20043c0034010140c45075180d03031052000f10f151004107112039900c03039408000030003070140c41101e00003405014000754603a148041e500101e04d024004982081c1d4400e4010b0440c091031240200403445050b01003100c0c1400d950042102000184c1e064101200b0001003005000010700003007103812000702c0079103810001d1300040512422080c0690018070004035588103840f00c161005a07a41314907000003180c0d0301c60240c140c0c1c0c0d01540c6100c40d01e2078a1000400c050049500c098079121100820125044040300407250601b2403519405014017207040c0c0900031482c050601c42c0c054900e0350700043c02d02d40040c000074483c0707070060300c00804074030740040d0703c01414460000b60903462565201103580b540c2d558800c1c0001c041c03d20047d1000c420041d96042e0340c03001d80c0640d0032001080d50220382801880350b01142150b102d120f191040e500e0740081410701e09001d10203802601300242c80d460301c03106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 815245413 1250 815244163 815244179
    0x60903080601030e0607200a060203010f0909030207260106030b0105040c18060509030f0d0f0e01110709150e090a03020d0f17071b11010221120907030f0507 69
    0x260215051500b400079060180d80d000450f50f5101c1d80f1b03454000c0040d4014420300c002c1e041f0201c0c00389814001c4003107160070302c846500254100c424001c8404081941c820300042141e00514008006804c4440c08014590402820903403140c188d108503090704000b0010a03003102c0e40d5601c210380400c2c0000042141340b800b48103400090819052800140c83e2140345200b02c600c0303d000745028088081501a540d0302c0030000044512942c80c2100c280c407241d960041e05070480c1c0185000040c2095010320107a52084081c1c3c2c041100c410000c00d001400c1008543c081d0006540c1800ca440780c4030300005d0341d82901c46c50315004000800181c580050141030080c00c2c004461046020f2240c4910030341e403400c0c0c0c80340407083d048220014840203a01c40c0c1c181181e946514028003003902d0420440c5c0c0d4244180714035080001c003400d80031500702500214004e03425a6080040008898040c82142d200c4a160900c03d90720121090030744500c1c40d10fa6407a441718000780036094655074801314040c06000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 815246663 1250 815245413 815245427
    0x120308040b0105010309020a03021302090307061805060414130b0a030602121e07030b21150108010c12090507031208011505490c02010b10050a050c03070f060903 71
    0x4002868113006e02c1c580c5402003000030003684002401404540c00318007114007260305440007080e000b000c0ea6049696410014240680300140d00c1012155000008072031500354100c0742150400c049615100100c9c0f020000c07040c40700030003c50b0315a140c14801e8919a41d1440d035030065445001f0050f200c0710424550246260004c01656841790320300003654a00d40c000d0483e0707034840c65518010680f904810b0110301d1004d960326000c00c5030300c0000c007241d220020100e40341001010460348100240c3e681c0e000c8501765040304c500720f00458001c40e000d560a03001070300110056401401164a0295603540380b5000d80c0c2103d1110340058039420040c80071640700300c1c02d280120340303504c1d0842c201032510303100d8107003040000241c564903042074041c5244840002580f20b1840ca4128030120407101c40b82106000d882c10340403001c010351038034150704424604002e40d80000402555001d040c1050802c0680b0190700c4054883d07110305c4240b0403c0c2c0040c280d081c00081c01c91003002c0200b01580d03540b402500e01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 815247913 1250 815246663 815246669
    0x7080105120f121305040c020a2a0b1c050402101b0c0803040303170402010f0c1a0405010c0318110405040305040e04060b011403060d0b06040e0303180d2303070504120308040b01 78
    0x29402e05403419620795000510007441502b2000813204590b4031310070920350105110a40c100210004400a0000340c6280030b01003c038059039a403110b441010444108445d01103030020350141007502d80e060070341e110703040d444041030804d511000c291642d07071205004580650310000302c80d4000501402016880100c0c401e070108202c801111508081e80040c1220422105260403c035041190340244400ca010228109100b009011164181401d006020b000d003922118086403c1c001c1070f4101c09210710180c003215070000303080710440b442801080f010f80406042602049414080400c2042c840104503000360300c00d1070006102d4041070009040812903c2200b41550340500c00c1050300c2d1180b040400d90194859020422940c644002400614054600110302d10003c070800c00705042210b1005100007955040740c03001c0d001c0c0a0200c422440b00d12443c402000780601e012280c60220300995000728150a0141c107180d120b0100c1e120005c06104150300113243c5a0620090124650910f809 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 815249163 1250 815247913 815247919
    0xf050f090f0a03020c01051e0c0a11030d080c0309070324110a05031801151403070b03071407020102150a050f060111030f1c02030c0c010e030307080105120f121305 72
    0x46004a460294580e945c50044c14113010000414601c4100c5d0200d0400f144504c000c0c41d00c0d15641403030405592254000411100d05d200c9603014a1180380000d189490140302c3e9032074000315074400c4203a841da40c0014200c104a0300c42c0210200009070410b5030800124030065440f000410860058401d07540b10746050302c03a03a20308100e203601e49503008040320340c45901c042c03030082601c508079071103801082c4501000c1c0c0c65080c44400801d2100e4000b0840040d00021004c941704a901c880b40075910348010389004000c903107a03500e48a0080000005010b03038a0050043d5080455159890711801004031440388500d680c0b40e08001010503400d4509400641c20b28000030800c2600e1080c95603803040e4034061811081c081416414454590140701400e00104002d40d202d08050080318040d4104040004255003402150700114070000113880c894500c954904082d03910340010b001a402c0864582d480314042c1c00003031100607808100900c0c0b090b0310000965a1000b554040c0500c18100d40c2000d84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 815250413 1250 815249163 815249173
    0x909010e072a1415240307060903020d05100c0309061503020f120f031902190c0306020708370903201306060509010f1b1103010f050f090f 61
    0x4807201c0a051102841d44581403110000c03000d80c00ca843c043c8207649045012101c0420003007484800300d440741000039511340407518982c1017810113072102114095000001d00805040016240c0864176144950264096500450011385200199804500c2c010b0220751600d0203081040301d54800d0400c00d12030f126440202a007940d0008140928119005100703800d10700c02140083e0041c00b041403400380c250102d0303940713141c482e4421186450b907890784409400303a5005001101e84001c0f1180d40213130302103040342d40541142c5c2c2c0d5000a40141006882d922000e000300301c0290a00d421700c050703281c00c008690303042c600c00c900e0b000610103019031801c0030002d089404200141c00100c826842d0484403000c00e0002410b0b4010640c2c840d041c9441407070f91414400b002540c180c101005082031007007a61802d0b000b814421040d6101550b00c40d4603540e0b0110142040c0c0450b0b11034030114102440200085418a8000c1d00d050990380180c0e090b0400304004d0040c0a41040100032042c3e2903800000135003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 815251663 1250 815250413 815250467
    0x50a0c1205060a0603150f0807030b01080f03030606070602161b050303070f06090f12050a0f0518040b0a0512010608010f0912031107150f06050f0a1404020909010e07 73
    0x1510f942c00300c0c8105000d15855821280c0c400180080c640c01800074840482c03903a0390b50b42e1105039a042c4501c0b06840165169001240d1441c0200c0c900d140740b0920b1000314a1903c44406011a5502040c01682c04580c24441441094440c0c050074514600810046030004c030050b04203c0f0a44555000d54400d60081180d44006244c2540109002c1d070020780c00501c2d03a0123421302512034603444100801d510061000d40d0328280d040b04c0501014040c9a84000012104070800e446034031541c503a006072200807402094003071405d0380120051000c0a0f219844aa0f61030000c590f02020003c2007140c10394560380c044c02070046c24401d00c0c070b0701e4403181824410a01c4a40b5071441500c5040242c00800d500ca44150903401c4801c000c8030180c40c0d00c1040100d0b04000ca1017040010508442641241c03030401c40300160b981380014414040d82c40050401d02d05a07e044100b0064015409074a40c010740c080c402d11281d80d64a0004a00030951007415800506d410040102050004403444585901d282c05103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 815252913 1250 815251663 815251669
    0x50f07030f0c0e0904110a0b0c19020609040518010c031e05060a0b0313120c0b070903080d0e0109080417060a2a030b030f010c11071404090312050a0c120506 69
    0xa0342c50f69051303898907a0b9443c2d0341041010030000c403903d00d03005490034500040020281009282031100c0c0d41c2514159085406110280a20741ca4082d50000c07040c801102c843c0341031742c80300ea0070a4501d055014021078840341030342940d80070414a40465510607003003224074510909151070603800502004586000c80000300e203101c450144080060001c0000f810001c0144ca218254540040041c000201003500c0203020000d6180c00300c86104401001c19591801642008150399000344c80d1804c150507000014010702002c500000c00350340b01c0369660040380410300244003610041456031300703141c402c020003454404007400c00301101c0d1400c080012007a1108a250400442840550420092a680460241c61000c900c5039141c019101c03001d00c0418154401500a0b40a80b2034000300c29860308001e44424440c80b48288081d000340311800c0a1401d5031080b40c0310751107410040103035148682030b02c084550440d40306c100c0f1690b590b0700d007080315005400c402c1c6510a40c4414030082c40c00d0303008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 815254163 1250 815252913 815252927
    0x5040c030522020d1a10090203060f04020d14160f110309040515060c060103060b030c090411011b06020c060a11070f031b0f0210020616140409050f07030f0c 69
    0x3030b94180140b4a85400071941c541d40905103198100b4000d03c0621100210440c0b0240309403500141c0310410280041ea804145c000c0d24450341c402491440c02842030014880a540300c9400203603044e43c1c038a403080030052101e5882c0d0044c00d441a00030701203c94014054090041100d02409009001140e1410000004101d07012000b007a2000701300707610b8110034100c2c00c0345405403050344044d0110300002d1101e00000c05c3c50480b80903000074010100724205041e294001a1000750f00841120002400314161369680d0500d0752040c501800d40d10020b41a0540f0381d1240c500484035281c0005000030390030401c000c80c5403c042410810080310204459900c0c1c148034180c0b0051039540d030b83c00c61070140350050080454040400c2d105660108581c0b900000081000300201c2c4074404903460308001c2440007805074031529107944100c800c1d10b0305e200c00b83d56040200c41c0a04010b8410040414103c0030f600030340d4014459000c215805003011207000e82640d44840440942c9803a00c45d5106040394132600c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 815255413 1250 815254163 815254201
    0x1090b0a09090c050418110402030601270306050405070305161d06040905120904150302100c062c1c120902011b0308101212030f09060603080405040c0305 68
    0x8000600030141d29043d2001a000d034007207540140307000946d03464070800002c410b100c14403d4a185400d070903080200022408140d032060700140d4041030204800042500c14034140301d245113010312907562a0765500a1740c00844003120300303400c00142001002010040202d00d00440045803561a0900c41070f1030362040e210962008002d600004602e2030b4490741d111458550b040025503c90041c3c048c960310b040d030301401e00306009910341803600b413018110400d2281620790003401a40d00c034000101c1141e000c2160402514225074415807550404406200d043c1c80d1492034100c100c007a480c0405040c10440c00c0c580c000d1201c003400d150140041d82c08810f0404051a1040018801d01d103800101c030704464a410040c4d07500740380c5c01d5081c1815000031181c0c0c03140101c101d040c59021b469980310b441d9400c44040051030f00c1c0803517180198060081e00100e07600e80e06001d000070030b01c0043d180d07401540d0441d13101703071791180d40000c0030720807824580581d003000381c200d0405020300d08000d0440103007408040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 815256663 1250 815255413 815255429
    0xa03020a0b150904140c030f0a081c0203090a02010e010e09011703040305060103111009032d120306260c06091909050618040f1b0f031103010501090b0a 67
    0x40015000500da1204004090b40586185014605031400c1c039810841000c9000e80c91040d00500503c0b40340008144402c440000d0261080300362581d200f141c280c00040e412110303411081c5681000000c6840550f00c6681c009004100099403800090310407a0456009410020a150300340e005840700541d2504640071842000864100071a41900303502a64100a11901981000000f401200c002e084da26405c111103140101803420000c1e2140d014500c0002c1a01407807481c06800d12a100c00d0f0b00d0078070540c0115017042c10781c681e0b0b01c03c00140c400e80039100220f5694102844900700c548080042650411910301e103180741700c204030fa41e4103141d400c414401c1a000401501640340c10701820712074030f0320b0f6107079004294a03441940080c081c1210300301d0190000701d08000e26140386040c06400380da04206034903da4907032a211040303c120722030410001a16130300f100180069200c11040001c43c0940110420241c4107030800d800d441c1c5c1a8451503289041004c807114591b22600303007c040300c000c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 815257913 1250 815256663 815256683
    0x90609090a1805210c0d030f0915051005240d0b0d0f14070609060e150301082416050c0c0306040b0402030f060106050301120201030605210f0a03020a 66
    0x1101c00c1202526880220b82c080d40c220810360420010000303071040390b14040c01500c2c4184031142107464001d0042035030748001d551050015880701802940560b91051400001060840050301c0d40908541b0b0070ba100e401d400d541c1d50810040a04c0c0c003001401501048070a03003035081d030303034079403141400c0002c052541e105c0310009580e50411903d40c03221140f1364019042d00d030500c0c114144000501d0740c211060715510100c1c0503808100c5404210101030300e11503182c000640d41400300c01c445403d003a038405a001009034120808928414000e0b60081002d8030080c001004450722903c80407106403000401030035060140145141d0201025a51150b10300d000e03515454810841480c0032406151241c05004400034070003805011252070788168001d800b1910440301c0e4013030880c0d480034244148400a801403005114100c002491405000d005140100701181c658000800754050348004101070464592001070611081c0010400c0d040e1960103810910b44644007c1d481d0a14064014264121 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 815259163 1250 815257913 815257921
    0x201050615090d020406080c090a02070224090d1112010603080301090513121218031e02010e030d0204051903030507080d0e10240612091a090109060605040209060909 73
    0x82c0d43ca60303003c07a0350001d00c00d002c407603510341c0384d02d44810071004154001c0f184003002171440080c40c000c03140d9541d0702070090f900b03094440c451510204000107612140c01020010380c80f0741c0c0e494010f8021040d000361010064843c0003030802c40ca10103200240c116690401d04100b0204a41e03100352411501c00c0c4ca00802c2c6561010303105030042c9410000181540d8468904281c601e40c031000014042660107020031007101c0d0201448400900c041d00140015010000341c82c480700707100c00006c80034076103000200300c042c0505200741c04c64100118210710f4a84c045020090742c41e10044068a0381d044039401d601103421034400a04511a90401038913140c00080e40e000e005007e03510450300e40d5081001d035100160b0610004018114442501c0c18203400842107503007000100222204031011600ea4603690b00740740700c0c03d0300507008805060341d81c01e801240301180c03400d608401d00e1280d4440400002c000c00249031100403121203070040d80c0603e20500800e0080d450700801c40d40c01c0c4208596118880e92 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 815260413 1250 815259163 815259169
    0x120f0d090203030a0512010603180303090318030f0b100b040b030603031b061005031b01031112010f0609080d05070609020d120c0213050603031b010b0603010b030115020105061509 79
    0x81803040003505440002002c84a440d0b029000e050301c42d600221400032641d82c2c40049080c3c0e84841c0c603a00c080d100e05a16540003038002da2281c81d050b442070a0290002c00710450b21000c9210325401a924000004200710400003c41c00040e40840095186c2c3e040034140410312220b400750780100d0092140000104000390760030429100c0074600d1421100003d6103d908c09600c600043d11980d0b00f44100b0100860345103408500c9a01030441c008594500000c0500114040c00c1403814100c240c4400b0082d44040480b06281e080c041d00207200b40c05001c0d8030785170004010445030342c00840c0da9000f1301d0811100c203500c8070403521a60b41040c0c0104940005000144038500318243c02803001d00d0728009280000c5d0400a4248002c0c0201c1380c0b070503484034810104064503000c8840c20352503001000344410504203400307916110101c0b40b0000880346ca610011601c00c2d4000e1300100e0f21120080010015030702d00032041c8030490f609200900940c180200425150710807140d841035038584c040380019050b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 815261663 1250 815260413 815260421
    0x7020304091104170c0906100c120207081203091b01170708090d081501030e070f14100f120f0f06180c050a210b09091608120f0d 57
    0x200d03200104400c400341403102c1c4007540715110350a0381c500c07698a0b0f04510b0f1808582c2412510000d0321040d2030742d0b0350781e0401c1400301d0303c01c401205120003000c04402007020f0041d014a1911542c0092102c00c0c101503640340ba00340e0003031740308056901c01c10402c885480d000c00c5100d010523041000030a1f00e6445001a00c152081c5041c08101ca00088104100d8591104056015040e10816260402d40200003107a418008945203842204240414086941310340c0c801c40d05150940181d4940301d4440c08401d442d02c0c0c4030741c00811110100701c1609e03a54909510b030484419143d04000c42c040300d000b01c000e80402c015400e11006035507140b403010041c05044d004046401e0310300004005481d1210703103034900700315440d8170b04100a2402b103280680d240900c085411110741919403100769100e0a505200400d0307040243c1d940c43da05c07540010b40c1d40e00c5207920030380580e8040700985022106a1180340c02c81055511064159000fa603c081540f55502e045900000c0700040c260b6540d00741d0322850010f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 815262913 1250 815261663 815261669
    0x501020d290927011b020d200a0b01060507030e18130309120507031511160f02060403080c0c03070501050d0b0d02032a01080c1b0a081b0c090f04020907020304 70
    0x990f40340c034201ca40340310f019405030200e030b0380780d88a14007481401c503001c03660783c81460084804a1029503411509000da070150080c4446500300b21180f00d807040d87c6103600840280e204a0201f0b202003181c108158002d05803e02904044d98044200e00041700b4804440d040580290b038904075242001013498441d00c261006003021540380341c000c01c0103182180c1e640760148000d40c0ea07045450b100025054040c002d04550307144100540d400c4c520f2811941d80b0b000700d03605040b01c020002c0c00040c0016103403000070f000194000c4564545550503881054201006484210b00c40e82003517805000300da8200d400d451210904000000e40b03464054046079003503460307040c00f130340c54821052900140c920f80e0500d103510400c464028000225448010b4a0101c030a40d80e03001e441328184041d0b24031980d118041c4000d034070300c1c808461000045c0e03241d04486610680c0b101091050600ca143c8500004001507400c94200b0350b4400b005107010541d50540e5140900028800c010280210306103030320810654001d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 815264163 1250 815262913 815262961
    0x3022101020c0a06050a02040e01170322080c030106080d050c0c090421170a1a04060308040603111303082107030204050a050d0b010e0601030603050a0501020d2909 72
    0x740ba140304803525501c601d460b01c100c848170b00b40000202d90600500070341d002c80d00300c00410300d52a42010800c680c0103010b40e6005c1002e100074403001c00c5824000e44000c1c40700111201940d509400c00007064180007010710b159000e40e06000d000c21841000064000b6100c00d01e02c1e08170344403500355140500344120081100d80c0514000d0034001402000440410034003240e08440c8880042e0704019140c00f14401243c4001c10500b5000405007541078002d10401e15210750144004202d800001e002c0740c189410694102c0c00224040c45029018840d2001011090346c0c40e0b820040c91209800000b5124000201052004a900c401071180b102d0360764804000210919860b151020008009412601c01e50307203e841904000901802d002d8201444c440e007182e0303891203d80c00d24692010982c0003500081c1019504c040c000040f540c140000c00c1140e203d00c0c00036964140c0c008a0310b00359410780c135104509021200c6500c08441300c40710fa030000f06c01e01342d48640d45030342c84500303200a4015014842e02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 815265413 1250 815264163 815264167
    0x91b0f031e0321101203120509060f07091214030408190203060c09010203120402030c220605030303091009060b060409020306040c0e0d0b04050f0f06090105010b0a090302210102 78
    0x25125012001d030103041500d1100d2a1840146500b4108116003914140401030842ca000e01001c21105d0490342041e00a003064401410b0302040c2c2030881c0c40c00c03139030100304d03422032414071010060401046401c190249000043c040c1001b410b01e482051136580101142c003c054410090002842981d008000800548559841d540c4000b581c3d05080e079400c030320900a0400042c4d004130400c056502c1008182e00450030801b40319040303035612034007410603a07141c4215041b800c01c50b5520900315070881d5102400072440b0080d011000c0030307208a030300407a10a41051040044001d40012001200280c400e030106410002d8213200e4018507170140d00c1c680040000401280100300340d00194010081035800f048042400142180c0501e01943c0e13060703219803d04004800b05c0c0141003201d40181c09203045d2404101e400e90814600b03000c40071001c0e256044002000b52604c000c1c81500e0040048044862038600420001000c203140750000030311803020100554010500c4000c180070444100b80215 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 815266663 1250 815265413 815265463
    0xb0903070606090c0e06130806070e1201050106020d051b01050103030c0b100e0105040c0e060c0604030f020f0d0f020a0f2a05100807050c010f050609091b0f03 70
    0x685951182409540541c10b00750002840c500a1040406850003582c0d140d5254031480e003002096407100440303803017010441d900485c40040600189005038410349070000e003d602d00040c0034081300740d072010a8203649000d00422204d0380100340c1d0000e050701c80c03900680d104401441d501503c002115416655880c02d0008070406401c000d0021030603000e500c1c40e6010b1b581d41d400342021102c1d01d0160035143c251b540d004100c141016000007440c0c94107410100303242540c0f41d010490507000300081d004554000030030320050503045516103403a002ea501c06011506420205aa502e0741c140d2410001c101da85c02d412115a403003807000c1000c8951003808a00c83c4041400c00d0001d98000c0108454802c0b554203482140f142441808411a2000b0f407006000804145064400410040c035003018480108444200e07003c081c440e1320f040490182d4000340030b0805400707201e41800014000c401c02e03401001c0884580103201301d87c2c80e11070011200d040c905144140400c0c209000340945c0004a00110800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 815267913 1250 815266663 815266681
    0x9201e0f0907120c0941031f0b0414010b18120a050607080604060807050402250f050d0815090c040b0a050316090302010c1e15091101020f0c0f0d0b 65
    0xa40225070300541941601b450f00c5403d82440c442c180001d91000d1440c600c0f0700489500841c5c91044002c0080580310f0001c05909400042417000c11030900031690f07a010000c803458540328218018005000701b01183d8100701c08800d00d40f01d0440c540700403641e460380c52000c1d5504d5220016038003004c07000b903401c0c03d1518a406643c0b80e0003903c4602c013042d58407000072000e041500ca03280c202c840203c000d140700c0b031410040c0002580316150f12161004c080c000b4079405116101250505842040e071644500e8007800c00c0d6080440380118202080740d40f4007841b41d0300f810881c14410b43c510480d08a00c1d075407200740285546105550015207041000b05001032001d03007181c05140728002c460680280020800c0701241c0d5074846000080c0801c141c00d1104000c24580e0702c00300510405480b60160051103503c80c041c40503803041403801c207691526604410081d0b24443d2b25001602030000b0910b260411001d5a20b42c50f41814083c040d15407803000960952301c2c0d500340e042180e04522050f103181420045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 815269163 1250 815267913 815267927
    0x1e06021c1b08060a1a0d050709140a050f0f03010603170c0106050d050a120c020301020f040602011a030d05090102010b060c0c01080c0a08011401020109201e0f0907120c 74
    0x6220340d0201c0c22aa0744035458098036142c0e00c82c0328000c0000a0f4141045c114680d80d0000081084482c4c10070b025183c400fa540d03215190003010140c950921044c031748074480089a1400000a0184d03020501c104440c1e1580402d900f10414101d03003034095a0b150030040323801400c05520144c9a60500e000500880c481107006054200d03401d0000e106540d04d54043c8404d003902d13a54020402e82c00502c0300c1c4042030020794041000c00c0c4925102d8a64441600081c0c01d98101c9039941c030b084000001c04000f5a0340900c14494410703500c0040782c603202c0f5401c001030740b101030000c3d40c0303414071070001950301711a0720030b50000c031800d00f000300b40540b20394001e10310594410346c40036902d001c62052004600312103104010b4816000c001c3d5a0b0040c41ea003003038200440548242c03492030640d034031100c080b0005031b01e9525001c5581e01100c08100004101420420b418041e2103048000540f44c0031a4000c03520340d140e02417880c1d00300392240c0900e911390340000c0702c160100071010b904103450700d48044096680304030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 815270413 1250 815269163 815269181
    0x501060e150405010e1f0806010603060e01171005060114030423030f03011e0312120b0604030b130311070b07050114010531020a020f010c08041e06021c 67
    0x30074050000515014002226005e001d0400d11101c42c00010700c25481c4041c003420120081e83c000724045070783e410910300e080070070380150010a4a0304030501040c204481d4039030041c08682c109030b030300400c0000616110610001d0080486840b000052075590041c403034003501e840302801c1203550b40f4060030315510321100103404414803842c074410304500e480c0000c00c0c0d4000b0003203d00a5441c40e4030703010600000f0451070b03040c1c05003030495050001c0881c103202054000b02034039848211107511800300c0241200d082c02d20641c483e01040c042400814031803841c9a901c1081c1c005c00c520024003500303050303a100003515404880e074812244c0c08074090818034041d1000603c100000d0050070140020b22076010700c00d0003807507000721039030040d281c0d504280440020013420340b49584001c41c0398a80c90340b09aa011010110142c1d0007030750419030fa40b200340318034000d041880c90000c640d0b04103079075104003844020b0100005c032024150344d642030210907412503500c11368451071583c0c101d2a0740e140d80007420342d2007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 815271663 1250 815270413 815270431
    0x301050108061e09100c0c0212060129090303041710021602090403110304120308010b07050705121f0c03050a1401170a021008040b1005012a0501060e 66
    0x1400001c2155000402501842c8503e0620b000078100c400d000700503100041c603207a540d00c5000f01100c00343e41c60f481462a1001d0f1551820b00a079071b940144810000d0303c04c40c01900754021401002070710340038025243c489844110b170180e503004640300310340309000300c0c1c1036164907020020f4002202e440b40070061160b561400705840611120000304c5049000d1100c441c040303000c5442d0310200510340031907107550292081c2885d64281041c10303505803458009402a4880340c0c8001102c509054015900c180100500c0400e04d01c0c184841c0e403515112121840703464002d4800d4021000340d5001803014855210b100e4050700c1d10101114020030140040700380c0407002c20b1402003c01d0902c0703081d003c2c00c80d0b800482c030f20410303e41c0d282c007130f44441d1115007194551040c011016030f500117036114904d030351652060f650740000608040c00c0142503100d0160001028601c1c0c0003040021b039810842002d11000305101d401107105504020f0361800340c821b13000038101d5207065004150702540c9211140540101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 815272913 1250 815271663 815271671
    0x1603050609010b10080c31080a08070204110c011103100b1305212a0105180907030905061008010608031e0f0f040311040507031a040f0605100c020301 66
    0x2454282214901c8040f6500031043d00c00b84401d80d406000b4882e00583c5010f109494034280c5800d000300749400c5c1e0702182d10030b1450000707111503826440341c1d00b01400c9400e001d0074140d2003a03035070b01c0c0c0d0364440c10034001c3c0119160009000300e480c00c030041e500c03821701c440b00920009020403507117250355100b100c1e540c0701d140884402103022401c0c01d05582c94103002411140106080400304010585803180200707080313a0001c82e03040121020b204c2d6844044000c21203042c0440328026006040740750b2144241001814404d881d1044030705480070b03080c03e07401e80c1c0d2005aa203c40790200d0140081340c00280452040d80305006c2454203407131000d011950403100030050207454420250b10b0344685044201d2400e680040c01003c424024000c158502185a56526000200070303113031490b8100345d00a803002e00340070702c000c83c036400c090042c581d2101052030100338142101e0404c0041d18440c02c1c80c2405569202804022070a642c1d00610140c00010031500030700e08800d200420501c08031100b24029420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 815274163 1250 815272913 815272921
    0xe1305060114030a171e0910110604140118050606190803040501262d010b070f061d0a150c021207030309020d0305070204140402150c0a0516030506 65
    0x40e0b140310180d40002006032401041e16101c2114040e44101c403203040910400c28682002401c1d442440d81440c0108110380b2459174201f000545000e82e81c4010030700030340081e491407c20780400c0750f0750b01c10792080983c40300841002140340184400d607006100d40d5404c00c00c01c01030141c006042440b800085407854410300c95442c0050546203548613481140e4004e11051101750b00840c1c280c495030040030503584100c851300d042d40c5035489007a6120f11305410094031030750312041200c0740c3ca210700e0305850342810b107540750007110480c6205802e005000040b8120200c1c040000039049034280c1401c0c5200000481220060b0325242c032406801100c0c8251441c1d0f2081e02c041c1c0c0c50041e80c19528407078001d00510086c845c96a003d81e44145400c81c20580e035000c4050040ea5080401035089019a03207080d11615980b0501044454440124518004200c100401030343c1d04140c1d000c0303d030152120300e42c84111382d00080385850381c031070b030020814010000c98401013824002c0180849010358225203064075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 815275413 1250 815274163 815274179
    0x130e09150106030903110d030501080d0201091e0809040e0106090e071401050c10060905060a080c0a05121f0203060a051e0108282a120b0a0e13050601 66
    0x215400c80c11051840300c0010041140658046a1403d0080c1003820b040181c1ea00740c541032540f030307684010200c0d81d01c0d001441025002c0203181c0d4806c1542c0001c00202107a0b848401004590b81807104100200041420410a00c0c200303440c2240ca01400030701c010106500e41310f000e4191030080e0b100c0c00c0d260005100d600900011400200c400d64840c5a01d28010400119201d5000360031200715807207411004004003c0600c900c00040c01d0740307031000507142012070411041403080e030b000e46000d910951b064065903131802d000d40c003105e00403560043c022001000007410200da48641200c05043d020700044400029001540308060859801040c5511001003003140c240c3c0b55050000034400040710507155002e02070180c0c000382401c04c0f041d020a820355401c070071114941d0401803603588504405141c44802c54803040b160441c1c0c14582e65101070014000c0000c1c03442d00d28908441d4031105100c1c040d0b2691400390000c0d062104108d8154078041e1062114404a01d10843e254401c0c03000010b440c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 815276663 1250 815275413 815275423
    0x204090f0323041514071407050108150d141005040b0112050607032a050d05100803160602040305011d07060206040b07030207030e09100618051008070212130e09 71
    0xc1c081603074203141c205130000640c039080700c3e0200c00388846294100740030441800500100c078800c0c003400b01000c130061710203410800c0c1544014148650030040c04001d8a4564030a481c8850940b0f401201d040306003030440c030300f03211350130a00d5280c010140f400c11600042d4118902c1140160142c000b6640c0e079080d0200003035500e01000d01940c11000104059510980081400b03420045408224542036a150504560a01c104002185000440100300160341c0a20760740302d100c5461a0a01d0f43c0b070201d180b5224840c980a4084803050100040c04014080d07060354081c3d60070000821100e4071100c10600400d41c1007854801c2403265542c00165207200103042c038800c0350301148103c200d4a519009502a400c083c40403030501c0700c0a01c201e0125150001c1c41c6118202c41c0d043c000c0b506103418406002d02210b900e092202000c0b0410900035500c56555450280b5407e00d00100c060780c80e0b000880c14415007108111516400081d8017031071006128101b419900700c2040302c3c5050315100d4007a641d41d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 815277913 1250 815276663 815276717
    0xc030b0d0506060d060b0a0f080105060132040810050105130603080f1602090a0506040c03060e070c030212040308120702010216080c011d06041211070915030204090f03 74
    0x542c0c4054005000c40c2016240483e8862103048041146020302000582d0031003550060f480035031555808000002090040c903070020300a080a41070901d000105804100c0701901000300e5030742c0c003000440c2c40c8003110300b1a4000c1c003003002030b2000114800c02c0013010b0f110a2040d02d10910b95400001001d250603c00e034400c880c0d0010501d403800040c0c00c04200c20342c0206010380e100080320340008001d6150403005910513564824000752903e00031041004484104000800309803600900f401082c50204044c0c0d0004041d0403c588040e0407403400300d181010b104c0300c003807102d400442c1c00010440c0050141903110100d03000d24405940d8034004034202c1c001d002161602d44080003496002c07421000040214004407400400c1002243c0c002c1058000a0172101c81c0270740c0108100010300108660038002c0c8011850a0171800b80712004032075440d0114041e0100700c40d43d84002e0296843c0b00a2240021a8082c105014524050411100e0900036400640100d10000505080400440c040400b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 815279163 1250 815277913 815277923
    0xa110612070e0f100801060306081f020d0b0a12061a1e0303040911030a0e0a03080a2415090902030c0d05220507030c050603040803010e280c030b0d 65
    0x400c1d40d4104080b0758800c0c0c2c044045030400f800c1801d411a030b450f5003c0142eaa90101d0f2101041949080d00090488041e070b40450650f030400310641c0d495040f9003105010b882680a40561110280c40348100108030565a00da030101f5070190001d04884031607010004140128410064031012180e8090f5040d803840406501c1040344200c00828403000040b81108507001e03048905040c1c98a20303100448a512801d40802030b8040200000c9003101d01903c4c01804c0d540303000d4041000d0b141c4e4040c080c49130181480c08803646500d1a410003002c0139000003024810040c2c1460240c1d034a41c00002e4040f1110380d00700c00280d010700b0200e0650a0f0340200c038040d1803072103006441c00c1e0f0b203079450300b00409018004c20642da000c6240b51b25264150f9038040c135158001e0000c0c00c4183d1031460070101e015041d600140c0103c1e420f02c20007000c550b030001924111162810507520f2551609541c403004802927404140c115500c4192080e1110668028420305046840c104841d40e0503c080040c03030400c0b1500100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 815280413 1250 815279163 815279197
    0xf02120105130f0e03070c050406030203062206020a050309010b0a05010e060c16030503040509010602150a0228030204061706030307140a051902090a1a010f18080a1106 74
    0x101e41007502094a11003050b81001070005400048002540e102a0001141e580045418028002549120002020b007290104200303865903001c83d4403074070014008854030030303040c802da0340700000c50418002d4194020021581c840075507a0107040b80c0c0059034603901070340ca48040b201903810401c41440540e00140c5601c18109101d10401c54142d0000032049100c3c00b038400032259074001c04200710043c610800255441d64104803d0100a4105078003410865000c1d0400791140d0b03071045603164218450707881c090b03a52025010f2043c80108040c1390741c86103456119001d850554964080e005171950344d547c4403101590725100d0f4100c2c890550301c0c41d0b80b6070803c1201c10006031913912100d000c0c940702400d0b02ca170312065440c0c5038240100300441503410992940030400f1440c1000007180d003c420403800b081a00340e40c07100c1202c2c840c02602c000d4140001c0c104030200b05402250101400a070440255540350b860749415925415082e038100c4002c045841b00440e1440c019050300d035010401e1340344803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 815281663 1250 815280413 815280419
    0x60e0301230601020304030203070803030702160b0706180b04030e0406080706140306041103070c11121515060403050708060c030f070f09030b070807091a040302190902030f0702010f021201 83
    0x3401e81010308464103610040000200503101400000001c00c40c0b08051500d914040304040e00781044a402e0b00d81d101a183d100b800b07051041020703156542e80020f27001640240000c01e107003103142862806841865200208010142e0110001c8064441902c051090b541c1d11601e01781e40c0c0b1482e0041d680480c1294016070444084280510361260000300701040703011104541c2590350744262107003400140000b11890034040e1018055180c59410b41c1c421091011600c10700341c80381418540048a0b25408001c60b0340e1494071580c1110100300140007541d115564905113a50f08030620980c131030740c00f40c6c0000030481001501564401c000c0d01075140e40719a6685021600002000310210501001c60b0f4040086000004454400c0754281c441007050300384044080c012020035807041018009400f144008503004005641c01c60791b0544210041829010042c2c8540d000c1390001383c4c0c42c901c08010040e000405c03942c0c0e107014841540082011500d00030780c0d842a0702c01c2004283c4211780c820010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 815282913 1250 815281663 815281721
    0x5040207051501080a0506011413021308100917031e04080f0f0714070530030a0216060c1a0c09100e12061006140708070804060e0301 59
    0xc000ca144a90240c0d59498084402811141d034282c1040d4640c0e03008001600422000700f00b000d0150541c1d2107032800c40702040300051521880d5401d22060a9008101282c00000440c00700700600500340035500941048a824002050b500030309485010140c51035120040307514040324040c900941e441d50310740d901d03500c552341c280c5400b0300f084901030000c0150b00544140c4001400c1034200c54240940e8075201750410740390814200041c80c5007604080020800e1307540c0c3c83d4064043c09090942d202680c003640000c0300110710300c00d600e0203141c000014400500703680030800143c8046900d840301c04c02da0700c4440803100100d2401c4010043c060507800820811074598450368003c2d000c009440c9020340d51400310703458030141b009035008565020350404040c500749030340300609203c200c010540d5290042001d55294800e104075070500000416030548030034000d08403004a500042d5469030784400c2e00e800880342d445882000c1c0090500600c2154038131301801000c001c403a074014019400441c440c46 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 815284163 1250 815282913 815282917
    0x12020f030c0409121416080c150f0a050a14160c0c170f0706020c01080429061509130e0c0d0b0f1503032713020c0f0a051b0406090f050a060806090304050402 69
    0x1080b18030301c9200c6120404030240980030b4400e0707460360341c032b521203091090038142500e8024211102050a1090701107020a049900c2d03a8811804c211600d240c2c6550f05040d5841500e00c98040c0010000c1038010034a5a00c00783c04100081d40070302202c480c40d2860100c19201c40c1503019150050b045005002e00fa5031140c0a0541c100b405042c41640072010000d40c0e80e03820702550f92260081e19280b0801c902c62800b558540b04040340c5406c1c40f454100c41c1800200c8162124050740b10a40d070706d032010305128a0070000e49007914400b4100b82e40b0030741941050304482100711a80030342466030000040170b002428031003100d14030002c1c0044d820441c4a407046003400003140760b013030502101003040340e405a65503001c0c940344030a0200011707a140e1420040b181000325450b440083e96006141280000c0c000254516459416141d0380c03c0700000c0c0c4000038041e210a611002c190342c20104e0446003440d80750700660294640c000c08008041c1c0c0c3c0e0035000c1d1100c0088411a0b03064000740000c01481c1000d0300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 815285413 1250 815284163 815284177
    0x10c120522030f0305010501080c041a040806040b01091b09090209130204060c03120e1e0a120305161713020d05010207030905150412020f030c040912141608 69
    0x71038035074410503000341e03035440503032181900001c220070000d104881d0181704080c003406080c0781010f064034060011503414400d5100c1c403c4041d03046000110503403540c100381c8010309043d8064402908050608aa06040a0145803406403070815245020705044d110070144111503155450814503102460b80250806070750355821542041590766014024802000641845e032140e1603104014200200480e5401d01c501c0500340c9400c3c1401c50a1400045200300c0e151a4400c0c00301c180203600c1c0d84c0c2d050540c0c1c0f840041130201640c035444440c0f505a041140301e010380c907441c0d82c0d0603010039104030b400140c0104a00c08440542011450080107581d4103110140043c02c10164010280d07581030880e4403080b016000102000c4e018080352a24243d07460042000f01042401d1a0130100200b4103400d03600c43c024450a000001d11243e9103080c081c1c2020940d0040c010841010203080003200e0f0b242c04803d0a00091003403004c24440b0201200366203402840400750340c070300d00b02a1745034481a44005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 815286663 1250 815285413 815285431
    0x210e09040618061a0301180209040206040e010906031a1314030c060103150c050c0601120201171003060b06310f1401020d050c100b061b010b12010c1205 67
    0x100d00c035640b140b0300c4081c240000d01c0740c02c0004400e46094002504a4180d40126100340d0500105900d082001d51041440940403034400301141c480f07100003403841c4034035440303c1d40d801c012100000340b011307045d8809000c80f40907a0500c4440b0004e081c0001c6080002c4401c461050b0b403072100c40021554565054442411040441c1d05e80b01354405400d18142090f8411102d20811542c450b50300c131014001c140951016003801804c02c003e030300e0741e03c0d15403005008001f080c0100c06102400d41e846109034031281110942140b4260500f0b15032040132400038001510254281900350303601d81030500c201e541c810313641100459005252406181e03072201d80001401500391045021601d54042100007006010502d0b40b144050305035400a410011100030b00350a0140a11050101542c04104541c00d1060701c60009091060780001a03068000d401c4107442c02070b08500751440e95841580300c1041001c04035928141030260b6245030342a22140c44c01180020007145008990b00e01c0354014940001c041d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 815287769 1106 815286663 815286671
    0x322060903120201090807060e120f04120f050303240a0303050f0c011407020a031409010c0803070504053f06010605130504051003210e090406 63
    0x39110140c029803607407100d010341500c00e44c003404405070f0180c8865112001c5041000c0108190120b0003450311440300c001d94403506900c1500c0f07201c1e140d40a524641401c012074440081d000101c216641c0341c04018000c0002c00601c003452148108101c00c1c40144003162150400c0d403c02913505014103884207043c4042903104040b20034a15550110307654610006240034018a401e181c0b00e0304400150341030115440d400700344110780d14040d50f01d200b41004e045800d04142c0c0308010301e07e4049190b04100e400000da0400146910200701e0038a2401d050313407200441c1c110701442e0005c80d4070422400c11200300c4504002e8030300342101c0e0b42a8120254060020760380c1ea44030180240f0307041c4500400d1349407425560b222030743c0c042e000247c014401410302c240202da00e080c042c0400c552181d40341640e00344018200811040c062015980c0389151130030a17040c020800006030041c3e95490312 = true := by decide +kernel

theorem cover : BRFrame.Cov 815107913 815287769 := by
  have h0 := BRFrame.cov_init 815107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 815107913 ≤ n) (h2 : n < 815287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
